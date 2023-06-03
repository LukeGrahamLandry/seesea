use crate::asm::aarch64_out::EmitAarch64;

struct IrToAarch64<Emitter: EmitAarch64> {
    emitter: Emitter,
}

impl<Emitter: EmitAarch64> IrToAarch64<Emitter> {}
