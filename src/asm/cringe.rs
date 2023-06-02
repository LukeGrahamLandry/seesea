use crate::asm::llvm::LlvmFuncGen;
use crate::ast::CType;
use inkwell::types::BasicTypeEnum;
use inkwell::values::{BasicValueEnum, IntValue, PointerValue};

// TODO: CLion can't cope with features and thinks there's an error here even though it compiles fine.
//       For now, these are just in another file so i don't get distracted by the red squiggles.
impl<'ctx: 'module, 'module> LlvmFuncGen<'ctx, 'module> {
    pub(crate) fn build_load(
        &self,
        pointee_type: BasicTypeEnum<'ctx>,
        pointer_value: PointerValue<'ctx>,
        name: &str,
    ) -> BasicValueEnum<'ctx> {
        self.builder.build_load(pointee_type, pointer_value, name)
    }

    pub(crate) fn const_gep(
        &self,
        struct_ptr: PointerValue<'ctx>,
        struct_type: CType,
        ordered_indexes: &[IntValue<'ctx>],
    ) -> PointerValue<'ctx> {
        // TODO: this is clearly not safe but idk why
        unsafe { struct_ptr.const_gep(self.llvm_type(struct_type), ordered_indexes) }
    }
}
