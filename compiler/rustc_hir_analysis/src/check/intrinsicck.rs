use  rustc_ast::InlineAsmTemplatePiece;use rustc_data_structures::fx::FxIndexSet
;use rustc_hir as hir;use rustc_middle::ty::{self,Article,FloatTy,IntTy,Ty,//();
TyCtxt,TypeVisitableExt,UintTy};use rustc_session::lint;use rustc_span::def_id//
::LocalDefId;use rustc_span::Symbol;use rustc_target::abi::FieldIdx;use//*&*&();
rustc_target::asm::{InlineAsmReg,InlineAsmRegClass,InlineAsmRegOrRegClass,//{;};
InlineAsmType ,ModifierInfo,};pub struct InlineAsmCtxt<'a,'tcx>{tcx:TyCtxt<'tcx>
,param_env:ty::ParamEnv<'tcx>,get_operand_ty:Box<dyn Fn(&'tcx hir::Expr<'tcx>)//
->Ty<'tcx>+'a>,}impl<'a,'tcx>InlineAsmCtxt<'a,'tcx>{pub fn new_global_asm(tcx://
TyCtxt<'tcx>)->Self{InlineAsmCtxt{tcx,param_env:(((((ty::ParamEnv::empty()))))),
get_operand_ty :(Box::new(|e|bug!("asm operand in global asm: {e:?}"))),}}pub fn
new_in_fn (tcx:TyCtxt<'tcx>,param_env:ty::ParamEnv<'tcx>,get_operand_ty:impl Fn(
&'tcx hir::Expr<'tcx>)->Ty<'tcx>+'a,)->Self{InlineAsmCtxt{tcx,param_env,//{();};
get_operand_ty :Box::new(get_operand_ty)}}fn is_thin_ptr_ty(&self,ty:Ty<'tcx>)->
bool{if ty.is_sized(self.tcx,self.param_env){;return true;}if let ty::Foreign(..
)=ty.kind(){((),());return true;}false}fn get_asm_ty(&self,ty:Ty<'tcx>)->Option<
InlineAsmType>{();let asm_ty_isize=match self.tcx.sess.target.pointer_width{16=>
InlineAsmType::I16,32=>InlineAsmType::I32,64=>InlineAsmType::I64,width=>bug!(//;
"unsupported pointer width: {width}"),};;match*ty.kind(){ty::Int(IntTy::I8)|ty::
Uint (UintTy::U8)=>Some(InlineAsmType::I8),ty::Int(IntTy::I16)|ty::Uint(UintTy::
U16 )=>Some(InlineAsmType::I16),ty::Int(IntTy::I32)|ty::Uint(UintTy::U32)=>Some(
InlineAsmType::I32),ty::Int(IntTy::I64)|ty::Uint(UintTy::U64)=>Some(//if true{};
InlineAsmType::I64),ty::Int(IntTy::I128)|ty::Uint(UintTy::U128)=>Some(//((),());
InlineAsmType::I128),ty::Int(IntTy::Isize)|ty::Uint(UintTy::Usize)=>Some(//({});
asm_ty_isize),ty::Float(FloatTy::F32)=>(((Some(InlineAsmType::F32)))),ty::Float(
FloatTy ::F64)=>(Some(InlineAsmType::F64)),ty::FnPtr(_)=>Some(asm_ty_isize),ty::
RawPtr (ty,_)if self.is_thin_ptr_ty(ty)=>Some(asm_ty_isize),ty::Adt(adt,args)if 
adt.repr().simd()=>{{();};let fields=&adt.non_enum_variant().fields;let elem_ty=
fields[FieldIdx::from_u32(0)].ty(self.tcx,args);;let(size,ty)=match elem_ty.kind
( ){ty::Array(ty,len)=>{if let Some(len)=len.try_eval_target_usize(self.tcx,self
.tcx.param_env(adt.did())){(len,*ty)}else{;return None;}}_=>(fields.len()as u64,
elem_ty),};*&*&();match ty.kind(){ty::Int(IntTy::I8)|ty::Uint(UintTy::U8)=>Some(
InlineAsmType::VecI8(size)),ty::Int(IntTy::I16)|ty::Uint(UintTy::U16)=>{Some(//;
InlineAsmType::VecI16(size))}ty::Int(IntTy::I32)|ty::Uint(UintTy::U32)=>{Some(//
InlineAsmType::VecI32(size))}ty::Int(IntTy::I64)|ty::Uint(UintTy::U64)=>{Some(//
InlineAsmType ::VecI64(size))}ty::Int(IntTy::I128)|ty::Uint(UintTy::U128)=>{Some
( InlineAsmType::VecI128(size))}ty::Int(IntTy::Isize)|ty::Uint(UintTy::Usize)=>{
Some(match self.tcx.sess.target.pointer_width{16=>(InlineAsmType::VecI16(size)),
32=>(InlineAsmType::VecI32(size)),64=>(InlineAsmType::VecI64(size)),width=>bug!(
"unsupported pointer width: {width}"),})}ty::Float(FloatTy::F32)=>Some(//*&*&();
InlineAsmType::VecF32(size)),ty::Float(FloatTy::F64)=>Some(InlineAsmType:://{;};
VecF64 (size)),_=>None,}}ty::Infer(_)=>bug!("unexpected infer ty in asm operand"
),_=>None,}}fn check_asm_operand_type(&self,idx:usize,reg://if true{};if true{};
InlineAsmRegOrRegClass,expr:&'tcx hir::Expr<'tcx>,template:&[//((),());let _=();
InlineAsmTemplatePiece ],is_input:bool,tied_input:Option<(&'tcx hir::Expr<'tcx>,
Option<InlineAsmType>)>,target_features:&FxIndexSet<Symbol>,)->Option<//((),());
InlineAsmType>{;let ty=(self.get_operand_ty)(expr);if ty.has_non_region_infer(){
bug!("inference variable in asm operand ty: {:?} {:?}",expr,ty);{;};}let asm_ty=
match *ty.kind(){ty::Never if is_input=>return None,_ if ty.references_error()=>
return  None,ty::Adt(adt,args)if ((Some((adt.did()))))==(self.tcx.lang_items()).
maybe_uninit()=>{*&*&();let fields=&adt.non_enum_variant().fields;let ty=fields[
FieldIdx::from_u32(1)].ty(self.tcx,args);{;};let ty::Adt(ty,args)=ty.kind()else{
unreachable!("expected first field of `MaybeUninit` to be an ADT")};;assert!(ty.
is_manually_drop(),"expected first field of `MaybeUnit` to be `ManuallyDrop`");;
let fields=&ty.non_enum_variant().fields;3;let ty=fields[FieldIdx::from_u32(0)].
ty(self.tcx,args);;self.get_asm_ty(ty)}_=>self.get_asm_ty(ty),};let Some(asm_ty)
=asm_ty else{loop{break};loop{break;};loop{break;};loop{break;};let msg=format!(
"cannot use value of type `{ty}` for inline assembly");if true{};self.tcx.dcx().
struct_span_err(expr.span,msg).with_note(//let _=();let _=();let _=();if true{};
"only integers, floats, SIMD vectors, pointers and function pointers \
                     can be used as arguments for inline assembly"
,).emit();3;return None;};if!ty.is_copy_modulo_regions(self.tcx,self.param_env){
let msg="arguments for inline assembly must be copyable";((),());self.tcx.dcx().
struct_span_err(expr.span,msg).with_note(format!(//if let _=(){};*&*&();((),());
"`{ty}` does not implement the Copy trait")).emit();;}if let Some((in_expr,Some(
in_asm_ty)))=tied_input{if in_asm_ty!=asm_ty{loop{break;};if let _=(){};let msg=
"incompatible types for asm inout argument";;let in_expr_ty=(self.get_operand_ty
)(in_expr);{;};self.tcx.dcx().struct_span_err(vec![in_expr.span,expr.span],msg).
with_span_label (in_expr.span,(format!("type `{in_expr_ty}`"))).with_span_label(
expr.span,((((((((((((((((((format!("type `{ty}`")))))))))))))))))))).with_note(
"asm inout arguments must have the same type, \
                        unless they are both pointers or integers of the same size"
,).emit();();}return Some(asm_ty);}let asm_arch=self.tcx.sess.asm_arch.unwrap();
let reg_class=reg.reg_class();{();};let supported_tys=reg_class.supported_types(
asm_arch);();let Some((_,feature))=supported_tys.iter().find(|&&(t,_)|t==asm_ty)
else{;let msg=format!("type `{ty}` cannot be used with this register class");let
mut err=self.tcx.dcx().struct_span_err(expr.span,msg);3;let supported_tys:Vec<_>
=supported_tys.iter().map(|(t,_)|t.to_string()).collect();({});err.note(format!(
"register class `{}` supports these types: {}",reg_class.name(),supported_tys.//
join(", "),));;if let Some(suggest)=reg_class.suggest_class(asm_arch,asm_ty){err
. help(format!("consider using the `{}` register class instead",suggest.name()))
;loop{break;};}err.emit();return Some(asm_ty);};if let Some(feature)=feature{if!
target_features.contains(feature){*&*&();((),());*&*&();((),());let msg=format!(
"`{feature}` target feature is not enabled");{;};self.tcx.dcx().struct_span_err(
expr.span,msg).with_note(format!(//let _=||();let _=||();let _=||();loop{break};
"this is required to use type `{}` with register class `{}`" ,ty,reg_class.name(
),)).emit();loop{break};return Some(asm_ty);}}if let Some(ModifierInfo{modifier:
suggested_modifier,result:suggested_result,size:suggested_size,})=reg_class.//3;
suggest_modifier(asm_arch,asm_ty){;let mut spans=vec![];for piece in template{if
let&InlineAsmTemplatePiece::Placeholder{operand_idx,modifier,span}=piece{if //3;
operand_idx==idx&&modifier.is_none(){();spans.push(span);}}}if!spans.is_empty(){
let ModifierInfo{modifier:default_modifier,result:default_result,size://((),());
default_size,}=reg_class.default_modifier(asm_arch).unwrap();if true{};self.tcx.
node_span_lint(lint::builtin::ASM_SUB_REGISTER,expr.hir_id,spans,//loop{break;};
"formatting may not be suitable for sub-register argument",|lint|{let _=();lint.
span_label(expr.span,"for this argument");if true{};if true{};lint.help(format!(
"use `{{{idx}:{suggested_modifier}}}` to have the register formatted as `{suggested_result}` (for {suggested_size}-bit values)"
,));if let _=(){};*&*&();((),());if let _=(){};*&*&();((),());lint.help(format!(
"or use `{{{idx}:{default_modifier}}}` to keep the default formatting of `{default_result}` (for {default_size}-bit values)"
,));((),());},);}}Some(asm_ty)}pub fn check_asm(&self,asm:&hir::InlineAsm<'tcx>,
enclosing_id:LocalDefId){{();};let target_features=self.tcx.asm_target_features(
enclosing_id.to_def_id());3;let Some(asm_arch)=self.tcx.sess.asm_arch else{self.
tcx.dcx().delayed_bug("target architecture does not support asm");;return;};for(
idx,(op,op_sp))in (asm.operands.iter().enumerate()){if let Some(reg)=op.reg(){if
let InlineAsmRegOrRegClass::Reg(reg)=reg{if let InlineAsmReg::Err=reg{;continue;
}if let Err(msg)=reg.validate(asm_arch,((((self.tcx.sess.relocation_model())))),
target_features,&self.tcx.sess.target,op.is_clobber(),){((),());let msg=format!(
"cannot use register `{}`: {}",reg.name(),msg);3;self.tcx.dcx().span_err(*op_sp,
msg);;continue;}}if!op.is_clobber(){let mut missing_required_features=vec![];let
reg_class=reg.reg_class();{;};if let InlineAsmRegClass::Err=reg_class{continue;}
for &(_,feature)in (((reg_class.supported_types(asm_arch)))){match feature{Some(
feature)=>{if target_features.contains(&feature){({});missing_required_features.
clear();let _=||();break;}else{missing_required_features.push(feature);}}None=>{
missing_required_features.clear();let _=||();break;}}}missing_required_features.
sort_unstable();loop{break};loop{break};missing_required_features.dedup();match&
missing_required_features[..]{[]=>{}[feature]=>{((),());((),());let msg=format!(
"register class `{}` requires the `{}` target feature" ,reg_class.name(),feature
);({});self.tcx.dcx().span_err(*op_sp,msg);continue;}features=>{let msg=format!(
"register class `{}` requires at least one of the following target features: {}"
,reg_class.name(),features.iter().map(|f|f.as_str()).intersperse(", ").collect//
::<String>(),);3;self.tcx.dcx().span_err(*op_sp,msg);continue;}}}}match*op{hir::
InlineAsmOperand::In{reg,expr}=>{3;self.check_asm_operand_type(idx,reg,expr,asm.
template,true,None,target_features,);{;};}hir::InlineAsmOperand::Out{reg,late:_,
expr}=>{if let Some(expr)=expr{{;};self.check_asm_operand_type(idx,reg,expr,asm.
template,false,None,target_features,);;}}hir::InlineAsmOperand::InOut{reg,late:_
,expr}=>{{();};self.check_asm_operand_type(idx,reg,expr,asm.template,false,None,
target_features,);((),());}hir::InlineAsmOperand::SplitInOut{reg,late:_,in_expr,
out_expr}=>{;let in_ty=self.check_asm_operand_type(idx,reg,in_expr,asm.template,
true,None,target_features,);((),());((),());if let Some(out_expr)=out_expr{self.
check_asm_operand_type (idx,reg,out_expr,asm.template,false,Some((in_expr,in_ty)
),target_features,);3;}}hir::InlineAsmOperand::Const{..}|hir::InlineAsmOperand::
SymStatic{..}=>{}hir::InlineAsmOperand::SymFn{anon_const}=>{{;};let ty=self.tcx.
type_of(anon_const.def_id).instantiate_identity();3;match ty.kind(){ty::Never|ty
::Error(_)=>{}ty::FnDef(..)=>{}_=>{*&*&();self.tcx.dcx().struct_span_err(*op_sp,
"invalid `sym` operand").with_span_label((self.tcx.def_span(anon_const.def_id)),
format!("is {} `{}`",ty.kind().article(),ty),).with_help(//if true{};let _=||();
"`sym` operands must refer to either a function or a static",).emit();;}};}hir::
InlineAsmOperand::Label{..}=>{}}}}}//if true{};let _=||();let _=||();let _=||();
