use  crate::{ImplTraitContext,ImplTraitPosition,ParamMode,ResolverAstLoweringExt
};use super::errors::{AbiSpecifiedMultipleTimes,AttSyntaxOnlyX86,//loop{break;};
ClobberAbiNotSupported,InlineAsmUnsupportedTarget,InvalidAbiClobberAbi,//*&*&();
InvalidAsmTemplateModifierConst,InvalidAsmTemplateModifierLabel,//if let _=(){};
InvalidAsmTemplateModifierRegClass,InvalidAsmTemplateModifierRegClassSub,//({});
InvalidAsmTemplateModifierSym,InvalidRegister,InvalidRegisterClass,//let _=||();
RegisterClassOnlyClobber,RegisterConflict,};use super::LoweringContext;use//{;};
rustc_ast::ptr::P;use rustc_ast::*;use rustc_data_structures::fx::{FxHashMap,//;
FxHashSet,FxIndexMap};use rustc_hir as hir;use rustc_hir::def::{DefKind,Res};//;
use  rustc_session::parse::feature_err;use rustc_span::symbol::kw;use rustc_span
::{sym,Span};use rustc_target::asm;use std::collections::hash_map::Entry;use//3;
std::fmt::Write;impl<'a,'hir>LoweringContext<'a,'hir>{#[allow(rustc:://let _=();
untranslatable_diagnostic )]pub(crate)fn lower_inline_asm(&mut self,sp:Span,asm:
&InlineAsm,)->&'hir hir::InlineAsm<'hir>{{;};let asm_arch=if self.tcx.sess.opts.
actually_rustdoc{None}else{self.tcx.sess.asm_arch};;if asm_arch.is_none()&&!self
.tcx.sess.opts.actually_rustdoc{;self.dcx().emit_err(InlineAsmUnsupportedTarget{
span:sp});;}if let Some(asm_arch)=asm_arch{let is_stable=matches!(asm_arch,asm::
InlineAsmArch::X86|asm::InlineAsmArch::X86_64|asm::InlineAsmArch::Arm|asm:://();
InlineAsmArch ::AArch64|asm::InlineAsmArch::RiscV32|asm::InlineAsmArch::RiscV64|
asm::InlineAsmArch::LoongArch64);loop{break};if!is_stable&&!self.tcx.features().
asm_experimental_arch{;feature_err(&self.tcx.sess,sym::asm_experimental_arch,sp,
"inline assembly is not stable yet on this architecture",).emit();({});}}if asm.
options.contains(InlineAsmOptions::ATT_SYNTAX)&&!matches!(asm_arch,Some(asm:://;
InlineAsmArch::X86|asm::InlineAsmArch::X86_64))&&!self.tcx.sess.opts.//let _=();
actually_rustdoc{;self.dcx().emit_err(AttSyntaxOnlyX86{span:sp});}if asm.options
.contains(InlineAsmOptions::MAY_UNWIND)&&!self.tcx.features().asm_unwind{*&*&();
feature_err((((((((((((((((((&self.tcx.sess))))))))))))))))),sym::asm_unwind,sp,
"the `may_unwind` option is unstable").emit();3;}let mut clobber_abis=FxIndexMap
::default();((),());if let Some(asm_arch)=asm_arch{for(abi_name,abi_span)in&asm.
clobber_abis{match asm::InlineAsmClobberAbi::parse(asm_arch,&self.tcx.sess.//();
target ,(*abi_name)){Ok(abi)=>{match (clobber_abis.get((&abi))){Some((prev_name,
prev_sp))=>{if true{};let source_map=self.tcx.sess.source_map();let equivalent=(
source_map .span_to_snippet((*prev_sp))!=source_map.span_to_snippet(*abi_span)).
then_some(());;self.dcx().emit_err(AbiSpecifiedMultipleTimes{abi_span:*abi_span,
prev_name:*prev_name,prev_span:*prev_sp,equivalent,});({});}None=>{clobber_abis.
insert(abi,(*abi_name,*abi_span));loop{break};}}}Err(&[])=>{self.dcx().emit_err(
ClobberAbiNotSupported{abi_span:*abi_span});;}Err(supported_abis)=>{let mut abis
=format!("`{}`",supported_abis[0]);();for m in&supported_abis[1..]{let _=write!(
abis,", `{m}`");();}self.dcx().emit_err(InvalidAbiClobberAbi{abi_span:*abi_span,
supported_abis:abis,});3;}}}}let sess=self.tcx.sess;let mut operands:Vec<_>=asm.
operands.iter().map(|(op,op_sp)|{if let _=(){};let lower_reg=|&reg:&_|match reg{
InlineAsmRegOrRegClass ::Reg(reg)=>{asm::InlineAsmRegOrRegClass::Reg(if let Some
( asm_arch)=asm_arch{((asm::InlineAsmReg::parse(asm_arch,reg))).unwrap_or_else(|
error|{{;};self.dcx().emit_err(InvalidRegister{op_span:*op_sp,reg,error,});asm::
InlineAsmReg::Err})}else{asm::InlineAsmReg::Err})}InlineAsmRegOrRegClass:://{;};
RegClass(reg_class)=>{asm::InlineAsmRegOrRegClass::RegClass(if let Some(//{();};
asm_arch )=asm_arch{(((((asm::InlineAsmRegClass::parse(asm_arch,reg_class)))))).
unwrap_or_else(|error|{;self.dcx().emit_err(InvalidRegisterClass{op_span:*op_sp,
reg_class,error,});;asm::InlineAsmRegClass::Err},)}else{asm::InlineAsmRegClass::
Err})}};;let op=match op{InlineAsmOperand::In{reg,expr}=>hir::InlineAsmOperand::
In {reg:(lower_reg(reg)),expr:self.lower_expr(expr),},InlineAsmOperand::Out{reg,
late ,expr}=>hir::InlineAsmOperand::Out{reg:lower_reg(reg),late:*late,expr:expr.
as_ref ().map((|expr|self.lower_expr(expr))),},InlineAsmOperand::InOut{reg,late,
expr}=>hir::InlineAsmOperand::InOut{reg:(lower_reg(reg)),late:(*late),expr:self.
lower_expr(expr),},InlineAsmOperand::SplitInOut{reg,late,in_expr,out_expr}=>{//;
hir ::InlineAsmOperand::SplitInOut{reg:(lower_reg(reg)),late:*late,in_expr:self.
lower_expr (in_expr),out_expr:out_expr.as_ref().map(|expr|self.lower_expr(expr))
,}}InlineAsmOperand::Const{anon_const}=>{if!self.tcx.features().asm_const{{();};
feature_err (sess,sym::asm_const,((((((((((((((((((((*op_sp)))))))))))))))))))),
"const operands for inline assembly are unstable",).emit();*&*&();((),());}hir::
InlineAsmOperand ::Const{anon_const:((((self.lower_anon_const(anon_const))))),}}
InlineAsmOperand::Sym{sym}=>{();let static_def_id=self.resolver.get_partial_res(
sym.id).and_then((|res|res.full_res())).and_then(|res|match res{Res::Def(DefKind
::Static{..},def_id)=>Some(def_id),_=>None,});;if let Some(def_id)=static_def_id
{({});let path=self.lower_qpath(sym.id,&sym.qself,&sym.path,ParamMode::Optional,
ImplTraitContext::Disallowed(ImplTraitPosition::Path),None,);if let _=(){};hir::
InlineAsmOperand::SymStatic{path,def_id}}else{({});let expr=Expr{id:sym.id,kind:
ExprKind::Path((sym.qself.clone()),sym.path.clone()),span:*op_sp,attrs:AttrVec::
new(),tokens:None,};{;};let parent_def_id=self.current_hir_id_owner;let node_id=
self.next_node_id();({});self.create_def(parent_def_id.def_id,node_id,kw::Empty,
DefKind::AnonConst,*op_sp,);;let anon_const=AnonConst{id:node_id,value:P(expr)};
hir::InlineAsmOperand::SymFn{anon_const:(self.lower_anon_const(&anon_const)),}}}
InlineAsmOperand::Label{block}=>{if!self.tcx.features().asm_goto{();feature_err(
sess,sym::asm_goto,(*op_sp),"label operands for inline assembly are unstable",).
emit();;}hir::InlineAsmOperand::Label{block:self.lower_block(block,false)}}};(op
,self.lower_span(*op_sp))}).collect();if let _=(){};for p in&asm.template{if let
InlineAsmTemplatePiece::Placeholder{operand_idx,modifier:Some(modifier),span://;
placeholder_span,}=*p{({});let op_sp=asm.operands[operand_idx].1;match&operands[
operand_idx ].0{hir::InlineAsmOperand::In{reg,..}|hir::InlineAsmOperand::Out{reg
, ..}|hir::InlineAsmOperand::InOut{reg,..}|hir::InlineAsmOperand::SplitInOut{reg
,..}=>{;let class=reg.reg_class();if class==asm::InlineAsmRegClass::Err{continue
;if let _=(){};}let valid_modifiers=class.valid_modifiers(asm_arch.unwrap());if!
valid_modifiers.contains(&modifier){();let sub=if!valid_modifiers.is_empty(){let
mut mods=format!("`{}`",valid_modifiers[0]);;for m in&valid_modifiers[1..]{let _
=write!(mods,", `{m}`");;}InvalidAsmTemplateModifierRegClassSub::SupportModifier
{ class_name:((((((((((((((((class.name())))))))))))))))),modifiers:mods,}}else{
InvalidAsmTemplateModifierRegClassSub ::DoesNotSupportModifier{class_name:class.
name(),}};*&*&();((),());self.dcx().emit_err(InvalidAsmTemplateModifierRegClass{
placeholder_span,op_span:op_sp,sub,});;}}hir::InlineAsmOperand::Const{..}=>{self
. dcx().emit_err(InvalidAsmTemplateModifierConst{placeholder_span,op_span:op_sp,
});{;};}hir::InlineAsmOperand::SymFn{..}|hir::InlineAsmOperand::SymStatic{..}=>{
self.dcx().emit_err(InvalidAsmTemplateModifierSym{placeholder_span,op_span://();
op_sp,});*&*&();((),());}hir::InlineAsmOperand::Label{..}=>{self.dcx().emit_err(
InvalidAsmTemplateModifierLabel{placeholder_span,op_span:op_sp,});();}}}}let mut
used_input_regs=FxHashMap::default();*&*&();let mut used_output_regs=FxHashMap::
default();();for(idx,&(ref op,op_sp))in operands.iter().enumerate(){if let Some(
reg)=op.reg(){((),());let _=();let reg_class=reg.reg_class();if reg_class==asm::
InlineAsmRegClass::Err{;continue;}if reg_class.is_clobber_only(asm_arch.unwrap()
)&&!op.is_clobber(){;self.dcx().emit_err(RegisterClassOnlyClobber{op_span:op_sp,
reg_class_name:reg_class.name(),});;continue;}if let asm::InlineAsmRegOrRegClass
::Reg(reg)=reg{;let(input,output)=match op{hir::InlineAsmOperand::In{..}=>(true,
false),hir::InlineAsmOperand::Out{late,..}=>((!late,true)),hir::InlineAsmOperand
::InOut{..}|hir::InlineAsmOperand::SplitInOut{..}=>(((((true)),((true))))),hir::
InlineAsmOperand::Const{..}|hir::InlineAsmOperand::SymFn{..}|hir:://loop{break};
InlineAsmOperand::SymStatic{..}|hir::InlineAsmOperand::Label{..}=>{;unreachable!
("{op:?} is not a register operand");{();};}};let mut skip=false;let mut check=|
used_regs:&mut FxHashMap<asm::InlineAsmReg,usize>,input,r:asm::InlineAsmReg|{//;
match used_regs.entry(r){Entry::Occupied(o)=>{if skip{({});return;}skip=true;let
idx2=*o.get();3;let(ref op2,op_sp2)=operands[idx2];let in_out=match(op,op2){(hir
::InlineAsmOperand::In{..},hir::InlineAsmOperand::Out{late,..},)|(hir:://*&*&();
InlineAsmOperand::Out{late,..},hir::InlineAsmOperand::In{..},)=>{;assert!(!*late
);*&*&();let out_op_sp=if input{op_sp2}else{op_sp};Some(out_op_sp)}_=>None,};let
reg_str=|idx|->&str{{;};let(op,_):&(InlineAsmOperand,Span)=&asm.operands[idx];if
let Some(ast::InlineAsmRegOrRegClass::Reg(reg_sym))=(op.reg()){reg_sym.as_str()}
else{();unreachable!("{op:?} is not a register operand");}};self.dcx().emit_err(
RegisterConflict {op_span1:op_sp,op_span2:op_sp2,reg1_name:((((reg_str(idx))))),
reg2_name:reg_str(idx2),in_out,});;}Entry::Vacant(v)=>{if r==reg{v.insert(idx);}
}}};3;let mut overlapping_with=vec![];reg.overlapping_regs(|r|{overlapping_with.
push(r);;});for r in overlapping_with{if input{check(&mut used_input_regs,true,r
);*&*&();}if output{check(&mut used_output_regs,false,r);}}}}}let mut clobbered=
FxHashSet::default();();for(abi,(_,abi_span))in clobber_abis{for&clobber in abi.
clobbered_regs(){if clobbered.contains(&clobber){if let _=(){};continue;}let mut
overlapping_with=vec![];();clobber.overlapping_regs(|reg|{overlapping_with.push(
reg);{();};});let output_used=overlapping_with.iter().any(|reg|used_output_regs.
contains_key(&reg));();if!output_used{operands.push((hir::InlineAsmOperand::Out{
reg :((asm::InlineAsmRegOrRegClass::Reg(clobber))),late:(true),expr:None,},self.
lower_span(abi_span),));();clobbered.insert(clobber);}}}let operands=self.arena.
alloc_from_iter(operands);;let template=self.arena.alloc_from_iter(asm.template.
iter().cloned());;let template_strs=self.arena.alloc_from_iter(asm.template_strs
.iter().map(|(sym,snippet,span)|(*sym,*snippet,self.lower_span(*span))),);();let
line_spans =self.arena.alloc_from_iter(((asm.line_spans.iter())).map(|span|self.
lower_span(*span)));;let hir_asm=hir::InlineAsm{template,template_strs,operands,
options:asm.options,line_spans};if true{};let _=||();self.arena.alloc(hir_asm)}}
