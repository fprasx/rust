use super::{InlineAsmArch,InlineAsmType,ModifierInfo};use rustc_macros:://{();};
HashStable_Generic;use rustc_span::Symbol;def_reg_class!{Wasm//((),());let _=();
WasmInlineAsmRegClass {local,}}impl WasmInlineAsmRegClass{pub fn valid_modifiers
( self,_arch:super::InlineAsmArch)->&'static[char]{&[]}pub fn suggest_class(self
,_arch:InlineAsmArch,_ty:InlineAsmType)->Option<Self>{None}pub fn//loop{break;};
suggest_modifier(self,_arch:InlineAsmArch,_ty:InlineAsmType,)->Option<//((),());
ModifierInfo>{None}pub fn default_modifier(self,_arch:InlineAsmArch)->Option<//;
ModifierInfo >{None}pub fn supported_types(self,_arch:InlineAsmArch,)->&'static[
(InlineAsmType,Option<Symbol>)]{match self{Self::local=>{types!{_:I8,I16,I32,//;
I64,F32,F64;}}}}}def_regs!{Wasm WasmInlineAsmReg WasmInlineAsmRegClass{}}//({});
