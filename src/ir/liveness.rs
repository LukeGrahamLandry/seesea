use crate::ir::{Function, Op, Ssa};
use crate::log;

pub struct SsaLiveness<'ir> {
    first_write: Vec<usize>,
    last_read: Vec<usize>,
    block_start_index: Vec<usize>,
    op_index: usize,
    ir: &'ir Function,
    current_block: usize,
}

pub fn compute_liveness(ir: &Function) -> SsaLiveness {
    let mut liveness = SsaLiveness {
        first_write: vec![usize::MAX; ir.register_types.len()],
        last_read: vec![0; ir.register_types.len()],
        block_start_index: vec![],
        op_index: 0,
        ir,
        current_block: 0,
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

    for (i, block) in ir.blocks.iter().enumerate() {
        log!("[Label({})]", i);
        liveness.current_block += 1;
        if let Some(block) = block {
            for op in block {
                liveness.op_index += 1;
                log!("[{}]: {}", liveness.op_index, ir.print(op));
                liveness.walk_op(op);
            }
        }
    }

    log!("-----");
    for i in 0..ir.register_types.len() {
        log!(
            "{}: [{}] -> [{}]",
            ir.name_ty(&Ssa(i)),
            liveness.first_write[i],
            liveness.last_read[i]
        );
    }

    // Must have an entry for each ssa.
    assert!(!liveness.first_write.iter().any(|i| *i == usize::MAX));
    // 0 means no reads.
    // assert!(!liveness.last_read.iter().any(|i| *i == 0));

    liveness
}

// TODO: vm panic if you try to use an ssa when it shouldn't be live. 
impl<'ir> SsaLiveness<'ir> {
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
            Op::Phi { dest, a, b } => {
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
                    let ssa_i = b.1.index();
                    let block_i = b.0.index() + 1;
                    let read_i = self.block_start_index[block_i];
                    let prev_best = self.last_read[ssa_i];
                    if read_i > prev_best {
                        self.last_read[ssa_i] = read_i;
                    }
                    println!("{} {}", read_i, self.op_index);
                    assert!(read_i > self.op_index);
                }
            }
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

    fn read(&mut self, ssa: &Ssa) {
        let prev_best = self.last_read[ssa.index()];
        if self.op_index > prev_best {
            self.last_read[ssa.index()] = self.op_index;
        }
    }

    fn write(&mut self, ssa: &Ssa) {
        let prev_best = self.first_write[ssa.index()];
        assert_eq!(prev_best, usize::MAX, "Expected SSA form.");
        self.first_write[ssa.index()] = self.op_index;
    }
}
