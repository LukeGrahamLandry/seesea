//! Determine what span of the code each SSA needs to be saved for.
//! This will allow efficiently allocating registers in the aarch64 backend.

use crate::ir::{Function, Label, Op, Ssa};
use crate::log;
use std::ops::RangeInclusive;

pub struct SsaLiveness<'ir> {
    pub block_start_index: Vec<usize>,
    pub range: Vec<RangeInclusive<usize>>,
    // Floats and Ints are tracked separately (these numbers will be hit at different points in the program)
    pub max_floats_alive: usize,
    pub max_ints_alive: usize,
    pub usage_count: Vec<usize>,

    // Private fields used for computing the live-ness.
    first_write: Vec<usize>,
    last_read: Vec<usize>,
    first_read: Vec<usize>,
    op_index: usize,
    ir: &'ir Function,
    current_block: usize,
}

// TODO: the idea is to use usages to prioritise who gets a register but this is lexical count. It needs to consider tightness of loops, etc.
//       backend should sort by size of range so the ones that span the most code go on the stack
//       or ones that are used the most go in registers. being held across a function call pushes towards storing on the stack?
//       inline is great if you have enough extra registers because it means the callee can use your extras instead of you saving them on the stack
//       should store all usage positions so you know whether to load it off the stack after a function call or wait until the next

pub fn compute_liveness(ir: &Function) -> SsaLiveness {
    let mut liveness = SsaLiveness::new(ir);
    liveness.walk_all_ops();
    log!("-----");
    liveness.calc_ssa_lifetimes();
    liveness.calc_max_alive();

    log!(
        "Max Alive: ({}I, {}F) / {}T",
        liveness.max_ints_alive,
        liveness.max_floats_alive,
        liveness.range.len()
    );

    liveness
}

impl<'ir> SsaLiveness<'ir> {
    fn new(ir: &'ir Function) -> SsaLiveness<'ir> {
        let mut liveness = SsaLiveness {
            first_write: vec![usize::MAX; ir.register_types.len()],
            last_read: vec![0; ir.register_types.len()],
            first_read: vec![usize::MAX; ir.register_types.len()],
            block_start_index: vec![],
            range: vec![],
            usage_count: vec![0; ir.register_types.len()],
            op_index: 0,
            ir,
            current_block: 0,
            max_floats_alive: 0,
            max_ints_alive: 0,
        };

        for ssa in &ir.arg_registers {
            liveness.first_write[ssa.index()] = 0;
        }

        let mut opi = 0;
        for block in &ir.blocks {
            liveness.block_start_index.push(opi);
            if let Some(block) = block {
                opi += block.len();
            }
        }

        liveness
    }

    fn calc_ssa_lifetimes(&mut self) {
        for i in 0..self.ir.register_types.len() {
            let first_write = self.first_write[i];
            let first_read = self.first_read[i];
            let last_read = self.last_read[i];
            let uses = self.usage_count[i];

            let mut start = first_write;
            if first_write > first_read {
                // TODO: this is not optimal
                // Hack to fix loops that set in the body then jump back up to a phi that reads.
                // We want the same register allocated for the whole interval [phi_read -> body_set -> loop_back].
                start = self.first_read[i];
            }
            let mut end = last_read;
            if end == 0 {
                // No reads
                assert_eq!(first_read, usize::MAX);
                assert_eq!(uses, 1);
                end = start;
            } else {
                assert!(first_read <= last_read);
            }

            self.range.push(start..=end);
            log!(
                "{}: [{}] -> [{}] ({} uses)",
                self.ir.name_ty(&Ssa(i)),
                start,
                end,
                uses
            );
            assert!(start <= end);
            if uses == 1 {
                assert!(
                    (first_read == usize::MAX && last_read == 0)
                        || self.ir.arg_registers.contains(&Ssa(i)),
                    "reads + writes so one usage means there are no reads OR it is an argument."
                );
            }
        }
    }

    fn calc_max_alive(&mut self) {
        for op_i in 0..self.op_index {
            let mut floats = 0;
            let mut ints = 0;
            for (ssa, ty) in &self.ir.register_types {
                if !self.range[ssa.index()].contains(&op_i) {
                    continue;
                }

                if ty.is_ptr() || ty.is_raw_int() {
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
            !self.first_write.iter().any(|i| *i == usize::MAX),
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
            let ssa_i = b.1.index();
            let block_i = b.0.index() + 1;
            let read_i = self.block_start_index[block_i];
            let prev_best = self.last_read[ssa_i];
            if read_i > prev_best {
                self.last_read[ssa_i] = read_i;
            }
            assert!(read_i > self.op_index);
        }
    }

    fn read(&mut self, ssa: &Ssa) {
        let prev_best = self.last_read[ssa.index()];
        if self.op_index > prev_best {
            self.last_read[ssa.index()] = self.op_index;
        }
        let prev_best = self.first_read[ssa.index()];
        if self.op_index < prev_best {
            assert_eq!(
                prev_best,
                usize::MAX,
                "first read we see should be the first read."
            );
            self.first_read[ssa.index()] = self.op_index;
        }
        self.usage_count[ssa.index()] += 1;
    }

    fn write(&mut self, ssa: &Ssa) {
        let prev_best = self.first_write[ssa.index()];
        assert_eq!(prev_best, usize::MAX, "Expected SSA form.");
        self.first_write[ssa.index()] = self.op_index;
        self.usage_count[ssa.index()] += 1;
    }
}
