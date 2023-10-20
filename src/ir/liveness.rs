//! Determine what span of the code each SSA needs to be saved for.
//! This will allow efficiently allocating registers in the aarch64 backend.

use crate::ir::{Function, Label, Op, Ssa};
use crate::log;
use crate::util::imap::IndexMap;
use std::ops::RangeInclusive;

pub struct SsaLiveness<'ir> {
    pub block_start_index: IndexMap<Label, usize>,
    pub range: IndexMap<Ssa, RangeInclusive<usize>>,
    // Floats and Ints are tracked separately (these numbers will be hit at different points in the program)
    // These don't count those that are held across function calls! TODO: change this if i stop just putting those on the stack.
    pub max_floats_alive: usize,
    pub max_ints_alive: usize,
    pub held_across_call: IndexMap<Ssa, bool>,
    pub has_any_calls: bool,

    // Private fields used for computing the live-ness.
    usage_count: IndexMap<Ssa, usize>,
    first_write: IndexMap<Ssa, usize>,
    last_read: IndexMap<Ssa, usize>,
    first_read: IndexMap<Ssa, usize>,
    op_index: usize,
    ir: &'ir Function,
    current_block: usize,
    read_blocks: IndexMap<Ssa, IndexMap<usize, bool>>, // [ssa][label+1] = did we read here?
}

// TODO: the idea is to use usages to prioritise who gets a register but this is lexical count. It needs to consider tightness of loops, etc.
//       backend should sort by size of range so the ones that span the most code go on the stack
//       or ones that are used the most go in registers. being held across a function call pushes towards storing on the stack?
//       inline is great if you have enough extra registers because it means the callee can use your extras instead of you saving them on the stack
//       should store all usage positions so you know whether to load it off the stack after a function call or wait until the next
//       calculate which position as function arg each is so it can prioritise getting the right register when possible.

pub fn compute_liveness(ir: &Function) -> SsaLiveness {
    log!("{:?}", ir.signature);
    let mut liveness = SsaLiveness::new(ir);
    liveness.walk_all_ops();
    log!("-----");
    liveness.calc_ssa_lifetimes();
    liveness.calc_held_across_call();
    liveness.calc_max_alive();

    for (i, range) in liveness.range.iter() {
        let held = liveness.held_across_call[i];
        log!(
            "{}: [{}] -> [{}] {}",
            liveness.ir.name_ty(&i),
            range.start(),
            range.end(),
            if held { "held" } else { "" }
        );
    }

    log!(
        "Max Alive: ({}I, {}F) / {}T",
        liveness.max_ints_alive,
        liveness.max_floats_alive,
        liveness.range.len()
    );

    log!(
        "{}/{} held across calls",
        liveness.held_across_call.values().filter(|b| **b).count(),
        liveness.held_across_call.len()
    );

    for (ssa, data) in liveness.read_blocks.iter() {
        let mut s = format!("{:2?} ", ssa);
        for (block, used) in data.iter() {
            s.push_str(if *used { "X" } else { "_" });
        }
        log!("{}", s);
    }

    liveness
}

impl<'ir> SsaLiveness<'ir> {
    fn new(ir: &'ir Function) -> SsaLiveness<'ir> {
        let count = ir.register_types.len();
        let mut liveness = SsaLiveness {
            first_write: IndexMap::init(usize::MAX, count),
            last_read: IndexMap::init(0, count),
            first_read: IndexMap::init(usize::MAX, count),
            block_start_index: IndexMap::with_capacity(count),
            range: IndexMap::with_capacity(count),
            usage_count: IndexMap::init(0, count),
            op_index: 0,
            ir,
            current_block: 0,
            max_floats_alive: 0,
            max_ints_alive: 0,
            held_across_call: IndexMap::init(false, count),
            has_any_calls: false,
            read_blocks: Default::default(),
        };

        for ssa in &ir.arg_registers {
            liveness.first_write.insert(*ssa, 0);
        }

        let mut opi = 0;
        for (i, block) in ir.blocks.iter().enumerate() {
            liveness.block_start_index.insert(Label(i), opi);
            if let Some(block) = block {
                opi += block.len();
            }
        }

        liveness
    }

    fn calc_ssa_lifetimes(&mut self) {
        for i in 0..self.ir.register_types.len() {
            let i = Ssa(i);
            let first_write = self.first_write[i];
            let first_read = self.first_read[i];
            let last_read = self.last_read[i];
            let uses = self.usage_count[i];

            // TODO: this isn't enough
            // if the last_read block branches somewhere above any read, need to only drop it after it gets out of that loop.
            // where above might not be lexical (can't just compare ).
            // not just above first write because pointers are mutable?
            let mut start = first_write;
            if first_write > first_read {
                // TODO: this is not optimal
                // Hack to fix loops that set in the body then jump back up to a phi that reads.
                // We want the same register allocated for the whole interval [phi_read -> body_set -> loop_back].
                start = self.first_read[i];
            }
            let mut end = last_read;
            if end == 0 {
                assert_eq!(first_read, usize::MAX);
                if uses == 0 {
                    // Unused argument
                    end = 1;
                } else if uses == 1 {
                    // write but no read.
                    end = start;
                } else {
                    unreachable!()
                }
            } else {
                assert!(first_read <= last_read);
            }

            self.range.insert(i, start..=end);
            assert!(start <= end);
            if uses == 1 {
                assert!(
                    (first_read == usize::MAX && last_read == 0)
                        || self.ir.arg_registers.contains(&i),
                    "reads + writes so one usage means there are no reads OR it is an argument."
                );
            }
        }
    }

    fn calc_held_across_call(&mut self) {
        if !self.has_any_calls {
            return;
        }
        let mut opi = 0;
        for block in &self.ir.blocks {
            if let Some(block) = block {
                for op in block {
                    opi += 1;

                    if let Op::Call { .. } = op {
                        for (ssa, live_range) in self.range.iter() {
                            // for args end==opi, for returns start==opi
                            if *live_range.start() < opi && *live_range.end() > opi {
                                self.held_across_call.insert(ssa, true);
                            }
                        }
                    }
                }
            }
        }
    }

    fn calc_max_alive(&mut self) {
        for op_i in 0..self.op_index {
            let mut floats = 0;
            let mut ints = 0;
            for (ssa, ty) in self.ir.register_types.iter() {
                // NOTE: not counting those held across calls because i'll just put those on the stack for now.
                if self.held_across_call[ssa] {
                    continue;
                }

                if !self.range[ssa].contains(&op_i) {
                    continue;
                }

                if ty.is_ptr() || ty.is_raw_int() || ty.is_raw_bool() {
                    ints += 1;
                } else if ty.is_raw_float() {
                    floats += 1;
                } else {
                    unreachable!();
                }
            }
            if floats > self.max_floats_alive {
                self.max_floats_alive = floats;
            }
            if ints > self.max_ints_alive {
                self.max_ints_alive = ints;
            }
        }
    }

    fn walk_all_ops(&mut self) {
        for (i, block) in self.ir.blocks.iter().enumerate() {
            log!("[Label({})]", i);
            self.current_block += 1;
            if let Some(block) = block {
                for op in block {
                    self.op_index += 1;
                    log!("[{}]: {}", self.op_index, self.ir.print(op));
                    self.walk_op(op);
                }
            }
        }
        assert!(
            !self.first_write.values().any(|i| *i == usize::MAX),
            "Must have an entry for each ssa."
        );
    }

    fn walk_op(&mut self, op: &Op) {
        match op {
            Op::ConstValue { dest, .. } => {
                self.write(dest);
            }
            Op::Binary { dest, a, b, .. } => {
                self.read(a);
                self.read(b);
                self.write(dest);
            }
            Op::LoadFromPtr { value_dest, addr } => {
                self.read(addr);
                self.write(value_dest);
            }
            Op::StoreToPtr { addr, value_source } => {
                self.read(addr);
                self.read(value_source);
            }
            Op::Jump { condition, .. } => {
                self.read(condition);
            }
            Op::AlwaysJump(_) => {
                // TODO: does this affect anything? I think the special case is handled by phi nodes.
            }
            Op::Phi { dest, a, b } => self.phi(dest, a, b),
            Op::Return(val) => {
                if let Some(val) = val {
                    self.read(val);
                }
            }
            Op::StackAlloc { dest, .. } => {
                self.write(dest);
            }
            Op::Call {
                args,
                return_value_dest,
                ..
            } => {
                self.has_any_calls = true;
                args.iter().for_each(|a| self.read(a));
                if let Some(val) = return_value_dest {
                    self.write(val);
                }
            }
            Op::GetFieldAddr {
                dest, object_addr, ..
            } => {
                self.read(object_addr);
                self.write(dest);
            }
            Op::Cast { input, output, .. } => {
                self.read(input);
                self.write(output)
            }
        }
    }

    fn phi(&mut self, dest: &Ssa, a: &(Label, Ssa), b: &(Label, Ssa)) {
        // Assuming that the first one is always the parent block of loops.
        assert!(a.0.index() < b.0.index() && a.0.index() < self.current_block);
        self.write(dest);
        self.read(&a.1);
        if b.0.index() < self.current_block {
            // We're not jumping backwards (this is an if not a loop) so treat this as a normal read.
            self.read(&b.1);
        } else {
            // We jumped backwards. The value must live for the whole loop.
            // Treat this as a read after the block we came from so it gets dropped when we escape the loop.

            // Set first_read to here.
            self.read(&b.1);

            // Extend lifetime down to the end of the loop.
            let ssa_i = b.1;
            let block_i = b.0.index() + 1;
            let read_i = self.block_start_index[Label(block_i)];
            let prev_best = self.last_read[ssa_i];
            if read_i > prev_best {
                self.last_read.insert(ssa_i, read_i);
            }
            assert!(read_i > self.op_index);
        }
    }

    fn read(&mut self, ssa: &Ssa) {
        let prev_best = self.last_read[ssa];
        if self.op_index > prev_best {
            self.last_read.insert(*ssa, self.op_index);
        }
        let prev_best = self.first_read[ssa];
        if self.op_index < prev_best {
            assert_eq!(
                prev_best,
                usize::MAX,
                "first read we see should be the first read."
            );
            self.first_read.insert(*ssa, self.op_index);
        }
        self.usage_count[ssa] += 1;
        if !self.read_blocks.contains(ssa) {
            self.read_blocks
                .insert(*ssa, IndexMap::init(false, self.ir.blocks.len() + 1));
        }
        self.read_blocks[ssa][self.current_block] = true;
    }

    fn write(&mut self, ssa: &Ssa) {
        let prev_best = self.first_write[ssa];
        assert_eq!(prev_best, usize::MAX, "Expected SSA form.");
        self.first_write.insert(*ssa, self.op_index);
        self.usage_count[ssa] += 1;
    }
}
