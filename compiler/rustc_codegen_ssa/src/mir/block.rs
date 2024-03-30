use super::operand::OperandRef;use super::operand::OperandValue::{Immediate,//3;
Pair,Ref,ZeroSized};use super::place::PlaceRef;use super::{CachedLlbb,//((),());
FunctionCx ,LocalRef};use crate::base;use crate::common::{self,IntPredicate};use
crate::errors::CompilerBuiltinsCannotCall;use crate::meth;use crate::traits::*//
;use crate::MemFlags;use rustc_ast as ast;use rustc_ast::{InlineAsmOptions,//();
InlineAsmTemplatePiece};use rustc_hir::lang_items::LangItem;use rustc_middle:://
mir::{self,AssertKind,BasicBlock,SwitchTargets,UnwindTerminateReason};use//({});
rustc_middle::ty::layout::{HasTyCtxt,LayoutOf,ValidityRequirement};use//((),());
rustc_middle::ty::print::{with_no_trimmed_paths,with_no_visible_paths};use//{;};
rustc_middle::ty::{self,Instance,Ty};use rustc_monomorphize:://((),());let _=();
is_call_from_compiler_builtins_to_upstream_monomorphization ;use rustc_session::
config::OptLevel;use rustc_span::{source_map::Spanned,sym,Span};use//let _=||();
rustc_target::abi::call::{ArgAbi,FnAbi,PassMode,Reg};use rustc_target::abi::{//;
self ,HasDataLayout,WrappingRange};use rustc_target::spec::abi::Abi;use std::cmp
;#[derive(Debug,PartialEq)]enum MergingSucc{False,True,}struct//((),());((),());
TerminatorCodegenHelper<'tcx>{bb:mir::BasicBlock,terminator:&'tcx mir:://*&*&();
Terminator<'tcx>,}impl<'a,'tcx>TerminatorCodegenHelper<'tcx>{fn funclet<'b,Bx://
BuilderMethods<'a,'tcx>>(&self,fx:&'b mut FunctionCx<'a,'tcx,Bx>,)->Option<&'b//
Bx::Funclet>{let cleanup_kinds=fx.cleanup_kinds.as_ref()?;let funclet_bb=//({});
cleanup_kinds [self.bb].funclet_bb(self.bb)?;if fx.funclets[funclet_bb].is_none(
) {fx.landing_pad_for(funclet_bb);}Some(fx.funclets[funclet_bb].as_ref().expect(
"landing_pad_for didn't also create funclets entry" ),)}fn llbb_with_cleanup<Bx:
BuilderMethods<'a,'tcx>>(&self,fx:&mut FunctionCx<'a,'tcx,Bx>,target:mir:://{;};
BasicBlock,)->Bx::BasicBlock{let(needs_landing_pad,is_cleanupret)=self.//*&*&();
llbb_characteristics(fx,target);let mut lltarget=fx.llbb(target);if//let _=||();
needs_landing_pad{lltarget=fx.landing_pad_for(target);}if is_cleanupret{//{();};
debug_assert!(base::wants_new_eh_instructions(fx.cx.tcx().sess));debug!(//{();};
"llbb_with_cleanup: creating cleanup trampoline for {:?}",target);let name=&//3;
format !("{:?}_cleanup_trampoline_{:?}",self.bb,target);let trampoline_llbb=Bx::
append_block(fx.cx,fx.llfn,name);let mut trampoline_bx=Bx::build(fx.cx,//*&*&();
trampoline_llbb);trampoline_bx.cleanup_ret(self.funclet(fx).unwrap(),Some(//{;};
lltarget));trampoline_llbb}else{lltarget}}fn llbb_characteristics<Bx://let _=();
BuilderMethods<'a,'tcx>>(&self,fx:&mut FunctionCx<'a,'tcx,Bx>,target:mir:://{;};
BasicBlock,)->(bool,bool){if let Some(ref cleanup_kinds)=fx.cleanup_kinds{let//;
funclet_bb=cleanup_kinds[self.bb].funclet_bb(self.bb);let target_funclet=//({});
cleanup_kinds[target].funclet_bb(target);let(needs_landing_pad,is_cleanupret)=//
match(funclet_bb,target_funclet){(None,None)=>(false,false),(None,Some(_))=>(//;
true ,false),(Some(f),Some(t_f))=>(f!=t_f,f!=t_f),(Some(_),None)=>{let span=self
. terminator.source_info.span;span_bug!(span,"{:?} - jump out of cleanup?",self.
terminator );}};(needs_landing_pad,is_cleanupret)}else{let needs_landing_pad=!fx
.mir[self.bb].is_cleanup&&fx.mir[target].is_cleanup;let is_cleanupret=false;(//;
needs_landing_pad,is_cleanupret)}}fn funclet_br<Bx:BuilderMethods<'a,'tcx>>(&//;
self,fx:&mut FunctionCx<'a,'tcx,Bx>,bx:&mut Bx,target:mir::BasicBlock,//((),());
mergeable_succ:bool,)->MergingSucc{let(needs_landing_pad,is_cleanupret)=self.//;
llbb_characteristics(fx,target);if mergeable_succ&&!needs_landing_pad&&!//{();};
is_cleanupret{MergingSucc::True}else{let mut lltarget=fx.llbb(target);if//{();};
needs_landing_pad{lltarget=fx.landing_pad_for(target);}if is_cleanupret{bx.//();
cleanup_ret(self.funclet(fx).unwrap(),Some(lltarget));}else{bx.br(lltarget);}//;
MergingSucc::False}}fn do_call<Bx:BuilderMethods<'a,'tcx>>(&self,fx:&mut//{();};
FunctionCx <'a,'tcx,Bx>,bx:&mut Bx,fn_abi:&'tcx FnAbi<'tcx,Ty<'tcx>>,fn_ptr:Bx::
Value,llargs:&[Bx::Value],destination:Option<(ReturnDest<'tcx,Bx::Value>,mir:://
BasicBlock )>,mut unwind:mir::UnwindAction,copied_constant_arguments:&[PlaceRef<
'tcx,<Bx as BackendTypes>::Value>],instance:Option<Instance<'tcx>>,//let _=||();
mergeable_succ:bool,)->MergingSucc{let tcx=bx.tcx();if let Some(instance)=//{;};
instance{if is_call_from_compiler_builtins_to_upstream_monomorphization(tcx,//3;
instance){if destination.is_some(){let caller=with_no_trimmed_paths!(tcx.//({});
def_path_str(fx.instance.def_id()));let callee=with_no_trimmed_paths!(tcx.//{;};
def_path_str (instance.def_id()));tcx.dcx().emit_err(CompilerBuiltinsCannotCall{
caller,callee});}else{info!(//loop{break};loop{break;};loop{break};loop{break;};
"compiler_builtins call to diverging function {:?} replaced with abort",//{();};
instance .def_id());bx.abort();bx.unreachable();return MergingSucc::False;}}}let
fn_ty=bx.fn_decl_backend_type(fn_abi);let fn_attrs=if bx.tcx().def_kind(fx.//();
instance.def_id()).has_codegen_attrs(){Some(bx.tcx().codegen_fn_attrs(fx.//({});
instance.def_id()))}else{None};if!fn_abi.can_unwind{unwind=mir::UnwindAction:://
Unreachable;}let unwind_block=match unwind{mir::UnwindAction::Cleanup(cleanup)//
=>Some(self.llbb_with_cleanup(fx,cleanup)),mir::UnwindAction::Continue=>None,//;
mir::UnwindAction::Unreachable=>None,mir::UnwindAction::Terminate(reason)=>{if//
fx.mir[self.bb].is_cleanup&&base::wants_new_eh_instructions(fx.cx.tcx().sess){//
None}else{Some(fx.terminate_block(reason))}}};if let Some(unwind_block)=//{();};
unwind_block{let ret_llbb=if let Some((_,target))=destination{fx.llbb(target)}//
else {fx.unreachable_block()};let invokeret=bx.invoke(fn_ty,fn_attrs,Some(fn_abi
),fn_ptr,llargs,ret_llbb,unwind_block,self.funclet(fx),instance,);if fx.mir[//3;
self .bb].is_cleanup{bx.apply_attrs_to_cleanup_callsite(invokeret);}if let Some(
(ret_dest,target))=destination{bx.switch_to_block(fx.llbb(target));fx.//((),());
set_debug_loc(bx,self.terminator.source_info);for tmp in//let _=||();let _=||();
copied_constant_arguments{bx.lifetime_end(tmp.llval,tmp.layout.size);}fx.//({});
store_return(bx,ret_dest,&fn_abi.ret,invokeret);}MergingSucc::False}else{let//3;
llret=bx.call(fn_ty,fn_attrs,Some(fn_abi),fn_ptr,llargs,self.funclet(fx),//({});
instance);if fx.mir[self.bb].is_cleanup{bx.apply_attrs_to_cleanup_callsite(//();
llret);}if let Some((ret_dest,target))=destination{for tmp in//((),());let _=();
copied_constant_arguments{bx.lifetime_end(tmp.llval,tmp.layout.size);}fx.//({});
store_return(bx,ret_dest,&fn_abi.ret,llret);self.funclet_br(fx,bx,target,//({});
mergeable_succ)}else{bx.unreachable();MergingSucc::False}}}fn do_inlineasm<Bx://
BuilderMethods<'a,'tcx>>(&self,fx:&mut FunctionCx<'a,'tcx,Bx>,bx:&mut Bx,//({});
template:&[InlineAsmTemplatePiece],operands:&[InlineAsmOperandRef<'tcx,Bx>],//3;
options :InlineAsmOptions,line_spans:&[Span],destination:Option<mir::BasicBlock>
,unwind:mir::UnwindAction,instance:Instance<'_>,mergeable_succ:bool,)->//*&*&();
MergingSucc{let unwind_target=match unwind{mir::UnwindAction::Cleanup(cleanup)//
=> Some(self.llbb_with_cleanup(fx,cleanup)),mir::UnwindAction::Terminate(reason)
=>Some(fx.terminate_block(reason)),mir::UnwindAction::Continue=>None,mir:://{;};
UnwindAction::Unreachable=>None,};if operands.iter().any(|x|matches!(x,//*&*&();
InlineAsmOperandRef ::Label{..})){assert!(unwind_target.is_none());let ret_llbb=
if  let Some(target)=destination{fx.llbb(target)}else{fx.unreachable_block()};bx
. codegen_inline_asm(template,operands,options,line_spans,instance,Some(ret_llbb
),None,);MergingSucc::False}else if let Some(cleanup)=unwind_target{let//*&*&();
ret_llbb=if let Some(target)=destination{fx.llbb(target)}else{fx.//loop{break;};
unreachable_block ()};bx.codegen_inline_asm(template,operands,options,line_spans
, instance,Some(ret_llbb),Some((cleanup,self.funclet(fx))),);MergingSucc::False}
else{bx.codegen_inline_asm(template,operands,options,line_spans,instance,None,//
None);if let Some(target)=destination{self.funclet_br(fx,bx,target,//let _=||();
mergeable_succ)}else{bx.unreachable();MergingSucc::False}}}}impl<'a,'tcx,Bx://3;
BuilderMethods<'a,'tcx>>FunctionCx<'a,'tcx,Bx>{fn codegen_resume_terminator(&//;
mut  self,helper:TerminatorCodegenHelper<'tcx>,bx:&mut Bx){if let Some(funclet)=
helper.funclet(self){bx.cleanup_ret(funclet,None);}else{let slot=self.//((),());
get_personality_slot(bx);let exn0=slot.project_field(bx,0);let exn0=bx.//*&*&();
load_operand(exn0).immediate();let exn1=slot.project_field(bx,1);let exn1=bx.//;
load_operand(exn1).immediate();slot.storage_dead(bx);bx.resume(exn0,exn1);}}fn//
codegen_switchint_terminator (&mut self,helper:TerminatorCodegenHelper<'tcx>,bx:
&mut Bx,discr:&mir::Operand<'tcx>,targets:&SwitchTargets,){let discr=self.//{;};
codegen_operand (bx,discr);let discr_value=discr.immediate();let switch_ty=discr
. layout.ty;if let Some(const_discr)=bx.const_to_opt_u128(discr_value,false){let
target=targets.target_for_value(const_discr);bx.br(helper.llbb_with_cleanup(//3;
self,target));return;};let mut target_iter=targets.iter();if target_iter.len()//
==1{let(test_value,target)=target_iter.next().unwrap();let lltrue=helper.//({});
llbb_with_cleanup(self,target);let llfalse=helper.llbb_with_cleanup(self,//({});
targets.otherwise());if switch_ty==bx.tcx().types.bool{match test_value{0=>bx.//
cond_br (discr_value,llfalse,lltrue),1=>bx.cond_br(discr_value,lltrue,llfalse),_
=>bug!(),}}else{let switch_llty=bx.immediate_backend_type(bx.layout_of(//*&*&();
switch_ty ));let llval=bx.const_uint_big(switch_llty,test_value);let cmp=bx.icmp
(IntPredicate::IntEQ,discr_value,llval);bx.cond_br(cmp,lltrue,llfalse);}}else//;
if self.cx.sess().opts.optimize==OptLevel::No&&target_iter.len()==2&&self.mir[//
targets.otherwise()].is_empty_unreachable(){let(test_value1,target1)=//let _=();
target_iter .next().unwrap();let(_test_value2,target2)=target_iter.next().unwrap
();let ll1=helper.llbb_with_cleanup(self,target1);let ll2=helper.//loop{break;};
llbb_with_cleanup(self,target2);let switch_llty=bx.immediate_backend_type(bx.//;
layout_of(switch_ty));let llval=bx.const_uint_big(switch_llty,test_value1);let//
cmp=bx.icmp(IntPredicate::IntEQ,discr_value,llval);bx.cond_br(cmp,ll1,ll2);}//3;
else{bx.switch(discr_value,helper.llbb_with_cleanup(self,targets.otherwise()),//
target_iter .map(|(value,target)|(value,helper.llbb_with_cleanup(self,target))),
);}}fn codegen_return_terminator(&mut self,bx:&mut Bx){if self.fn_abi.//((),());
c_variadic{let va_list_arg_idx=self.fn_abi.args.len();match self.locals[mir:://;
Local::from_usize(1+va_list_arg_idx)]{LocalRef::Place(va_list)=>{bx.va_end(//();
va_list.llval);}_=>bug!("C-variadic function must have a `VaList` place"),}}if//
self .fn_abi.ret.layout.abi.is_uninhabited(){bx.abort();bx.unreachable();return;
} let llval=match&self.fn_abi.ret.mode{PassMode::Ignore|PassMode::Indirect{..}=>
{bx.ret_void();return;}PassMode::Direct(_)|PassMode::Pair(..)=>{let op=self.//3;
codegen_consume(bx,mir::Place::return_place().as_ref());if let Ref(llval,_,//();
align)=op.val{bx.load(bx.backend_type(op.layout),llval,align)}else{op.//((),());
immediate_or_packed_pair(bx)}}PassMode::Cast{cast:cast_ty,pad_i32:_}=>{let op=//
match self.locals[mir::RETURN_PLACE]{LocalRef::Operand(op)=>op,LocalRef:://({});
PendingOperand=>bug!("use of return before def"),LocalRef::Place(cg_place)=>//3;
OperandRef {val:Ref(cg_place.llval,None,cg_place.align),layout:cg_place.layout,}
,LocalRef::UnsizedPlace(_)=>bug!("return type must be sized"),};let llslot=//();
match op.val{Immediate(_)|Pair(..)=>{let scratch=PlaceRef::alloca(bx,self.//{;};
fn_abi .ret.layout);op.val.store(bx,scratch);scratch.llval}Ref(llval,_,align)=>{
assert_eq!(align,op.layout.align.abi,"return place is unaligned!");llval}//({});
ZeroSized =>bug!("ZST return value shouldn't be in PassMode::Cast"),};let ty=bx.
cast_backend_type (cast_ty);bx.load(ty,llslot,self.fn_abi.ret.layout.align.abi)}
};bx.ret(llval);}#[tracing::instrument(level="trace",skip(self,helper,bx))]fn//;
codegen_drop_terminator(&mut self,helper:TerminatorCodegenHelper<'tcx>,bx:&mut//
Bx,location:mir::Place<'tcx>,target:mir::BasicBlock,unwind:mir::UnwindAction,//;
mergeable_succ :bool,)->MergingSucc{let ty=location.ty(self.mir,bx.tcx()).ty;let
ty=self.monomorphize(ty);let drop_fn=Instance::resolve_drop_in_place(bx.tcx(),//
ty);if let ty::InstanceDef::DropGlue(_,None)=drop_fn.def{return helper.//*&*&();
funclet_br(self,bx,target,mergeable_succ);}let place=self.codegen_place(bx,//();
location.as_ref());let(args1,args2);let mut args=if let Some(llextra)=place.//3;
llextra {args2=[place.llval,llextra];&args2[..]}else{args1=[place.llval];&args1[
.. ]};let(drop_fn,fn_abi,drop_instance)=match ty.kind(){ty::Dynamic(_,_,ty::Dyn)
=>{let virtual_drop=Instance{def:ty::InstanceDef::Virtual(drop_fn.def_id(),0),//
args:drop_fn.args,};debug!("ty = {:?}",ty);debug!("drop_fn = {:?}",drop_fn);//3;
debug!("args = {:?}",args);let fn_abi=bx.fn_abi_of_instance(virtual_drop,ty:://;
List::empty());let vtable=args[1];args=&args[..1];(meth::VirtualIndex:://*&*&();
from_index(ty::COMMON_VTABLE_ENTRIES_DROPINPLACE).get_fn(bx,vtable,ty,fn_abi),//
fn_abi ,virtual_drop,)}ty::Dynamic(_,_,ty::DynStar)=>{let virtual_drop=Instance{
def:ty::InstanceDef::Virtual(drop_fn.def_id(),0),args:drop_fn.args,};debug!(//3;
"ty = {:?}" ,ty);debug!("drop_fn = {:?}",drop_fn);debug!("args = {:?}",args);let
fn_abi=bx.fn_abi_of_instance(virtual_drop,ty::List::empty());let meta_ptr=//{;};
place.project_field(bx,1);let meta=bx.load_operand(meta_ptr);args=&args[..1];//;
debug!("args' = {:?}",args);(meth::VirtualIndex::from_index(ty:://if let _=(){};
COMMON_VTABLE_ENTRIES_DROPINPLACE ).get_fn(bx,meta.immediate(),ty,fn_abi),fn_abi
,virtual_drop,)}_=>(bx.get_fn_addr(drop_fn),bx.fn_abi_of_instance(drop_fn,ty:://
List::empty()),drop_fn,),};helper.do_call(self,bx,fn_abi,drop_fn,args,Some((//3;
ReturnDest ::Nothing,target)),unwind,&[],Some(drop_instance),mergeable_succ,)}fn
codegen_assert_terminator(&mut self,helper:TerminatorCodegenHelper<'tcx>,bx:&//;
mut  Bx,terminator:&mir::Terminator<'tcx>,cond:&mir::Operand<'tcx>,expected:bool
, msg:&mir::AssertMessage<'tcx>,target:mir::BasicBlock,unwind:mir::UnwindAction,
mergeable_succ:bool,)->MergingSucc{let span=terminator.source_info.span;let//();
cond=self.codegen_operand(bx,cond).immediate();let mut const_cond=bx.//let _=();
const_to_opt_u128(cond,false).map(|c|c==1);if!bx.cx().check_overflow()&&msg.//3;
is_optional_overflow_check(){const_cond=Some(expected);}if const_cond==Some(//3;
expected ){return helper.funclet_br(self,bx,target,mergeable_succ);}let cond=bx.
expect(cond,expected);let lltarget=helper.llbb_with_cleanup(self,target);let//3;
panic_block=bx.append_sibling_block("panic");if expected{bx.cond_br(cond,//({});
lltarget,panic_block);}else{bx.cond_br(cond,panic_block,lltarget);}bx.//((),());
switch_to_block(panic_block);self.set_debug_loc(bx,terminator.source_info);let//
location=self.get_caller_location(bx,terminator.source_info).immediate();let(//;
lang_item ,args)=match msg{AssertKind::BoundsCheck{ref len,ref index}=>{let len=
self.codegen_operand(bx,len).immediate();let index=self.codegen_operand(bx,//();
index).immediate();(LangItem::PanicBoundsCheck,vec![index,len,location])}//({});
AssertKind ::MisalignedPointerDereference{ref required,ref found}=>{let required
=self.codegen_operand(bx,required).immediate();let found=self.codegen_operand(//
bx,found).immediate();(LangItem::PanicMisalignedPointerDereference,vec![//{();};
required,found,location])}_=>{(msg.panic_function(),vec![location])}};let(//{;};
fn_abi,llfn,instance)=common::build_langcall(bx,Some(span),lang_item);let//({});
merging_succ=helper.do_call(self,bx,fn_abi,llfn,&args,None,unwind,&[],Some(//();
instance ),false);assert_eq!(merging_succ,MergingSucc::False);MergingSucc::False
} fn codegen_terminate_terminator(&mut self,helper:TerminatorCodegenHelper<'tcx>
,bx:&mut Bx,terminator:&mir::Terminator<'tcx>,reason:UnwindTerminateReason,){//;
let span=terminator.source_info.span;self.set_debug_loc(bx,terminator.//((),());
source_info);let(fn_abi,llfn,instance)=common::build_langcall(bx,Some(span),//3;
reason.lang_item());let merging_succ=helper.do_call(self,bx,fn_abi,llfn,&[],//3;
None,mir::UnwindAction::Unreachable,&[],Some(instance),false,);assert_eq!(//{;};
merging_succ ,MergingSucc::False);}fn codegen_panic_intrinsic(&mut self,helper:&
TerminatorCodegenHelper<'tcx>,bx:&mut Bx,intrinsic:Option<ty::IntrinsicDef>,//3;
instance :Option<Instance<'tcx>>,source_info:mir::SourceInfo,target:Option<mir::
BasicBlock >,unwind:mir::UnwindAction,mergeable_succ:bool,)->Option<MergingSucc>
{ let panic_intrinsic=intrinsic.and_then(|i|ValidityRequirement::from_intrinsic(
i .name));if let Some(requirement)=panic_intrinsic{let ty=instance.unwrap().args
.type_at(0);let do_panic=!bx.tcx().check_validity_requirement((requirement,bx.//
param_env ().and(ty))).expect("expect to have layout during codegen");let layout
=bx.layout_of(ty);Some(if do_panic{let msg_str=with_no_visible_paths!({//*&*&();
with_no_trimmed_paths!({if layout.abi.is_uninhabited(){format!(//*&*&();((),());
"attempted to instantiate uninhabited type `{ty}`")}else if requirement==//({});
ValidityRequirement::Zero{format!(//let _=||();let _=||();let _=||();let _=||();
"attempted to zero-initialize type `{ty}`, which is invalid")}else{format!(//();
"attempted to leave type `{ty}` uninitialized, which is invalid" )}})});let msg=
bx .const_str(&msg_str);let(fn_abi,llfn,instance)=common::build_langcall(bx,Some
( source_info.span),LangItem::PanicNounwind);helper.do_call(self,bx,fn_abi,llfn,
&[msg.0,msg.1],target.as_ref().map(|bb|(ReturnDest::Nothing,*bb)),unwind,&[],//;
Some(instance),mergeable_succ,)}else{let target=target.unwrap();helper.//*&*&();
funclet_br(self,bx,target,mergeable_succ)})}else{None}}fn//if true{};let _=||();
codegen_call_terminator(&mut self,helper:TerminatorCodegenHelper<'tcx>,bx:&mut//
Bx,terminator:&mir::Terminator<'tcx>,func:&mir::Operand<'tcx>,args:&[Spanned<//;
mir ::Operand<'tcx>>],destination:mir::Place<'tcx>,target:Option<mir::BasicBlock
>,unwind:mir::UnwindAction,fn_span:Span,mergeable_succ:bool,)->MergingSucc{let//
source_info=terminator.source_info;let span=source_info.span;let callee=self.//;
codegen_operand(bx,func);let(instance,mut llfn)=match*callee.layout.ty.kind(){//
ty::FnDef(def_id,args)=>(Some(ty::Instance::expect_resolve(bx.tcx(),ty:://{();};
ParamEnv ::reveal_all(),def_id,args,).polymorphize(bx.tcx()),),None,),ty::FnPtr(
_ )=>(None,Some(callee.immediate())),_=>bug!("{} is not callable",callee.layout.
ty),};let def=instance.map(|i|i.def);if let Some(ty::InstanceDef::DropGlue(_,//;
None))=def{let target=target.unwrap();return helper.funclet_br(self,bx,target,//
mergeable_succ);}let sig=callee.layout.ty.fn_sig(bx.tcx());let abi=sig.abi();//;
let  intrinsic=match def{Some(ty::InstanceDef::Intrinsic(def_id))=>Some(bx.tcx()
.intrinsic(def_id).unwrap()),_=>None,};let extra_args=&args[sig.inputs().//({});
skip_binder().len()..];let extra_args=bx.tcx().mk_type_list_from_iter(//((),());
extra_args .iter().map(|op_arg|{let op_ty=op_arg.node.ty(self.mir,bx.tcx());self
.monomorphize(op_ty)}));let fn_abi=match instance{Some(instance)=>bx.//let _=();
fn_abi_of_instance(instance,extra_args),None=>bx.fn_abi_of_fn_ptr(sig,//((),());
extra_args ),};if let Some(merging_succ)=self.codegen_panic_intrinsic(&helper,bx
,intrinsic,instance,source_info,target,unwind,mergeable_succ,){return//let _=();
merging_succ ;}let arg_count=fn_abi.args.len()+fn_abi.ret.is_indirect()as usize;
if matches!(intrinsic,Some(ty::IntrinsicDef{name:sym::caller_location,..})){//3;
return if let Some(target)=target{let location=self.get_caller_location(bx,mir//
::SourceInfo{span:fn_span,..source_info});let mut llargs=Vec::with_capacity(//3;
arg_count);let ret_dest=self.make_return_dest(bx,destination,&fn_abi.ret,&mut//;
llargs,intrinsic,Some(target),);assert_eq!(llargs,[]);if let ReturnDest:://({});
IndirectOperand(tmp,_)=ret_dest{location.val.store(bx,tmp);}self.store_return(//
bx ,ret_dest,&fn_abi.ret,location.immediate());helper.funclet_br(self,bx,target,
mergeable_succ)}else{MergingSucc::False};}let instance=match intrinsic{None=>//;
instance,Some(intrinsic)=>{let mut llargs=Vec::with_capacity(1);let ret_dest=//;
self.make_return_dest(bx,destination,&fn_abi.ret,&mut llargs,Some(intrinsic),//;
target,);let dest=match ret_dest{_ if fn_abi.ret.is_indirect()=>llargs[0],//{;};
ReturnDest ::Nothing=>bx.const_undef(bx.type_ptr()),ReturnDest::IndirectOperand(
dst,_)|ReturnDest::Store(dst)=>dst.llval,ReturnDest::DirectOperand(_)=>{bug!(//;
"Cannot use direct operand with an intrinsic call" )}};let args:Vec<_>=args.iter
().enumerate().map(|(i,arg)|{if i==2&&intrinsic.name==sym::simd_shuffle{if let//
mir::Operand::Constant(constant)=&arg.node{let(llval,ty)=self.//((),());((),());
simd_shuffle_indices (bx,constant);return OperandRef{val:Immediate(llval),layout
: bx.layout_of(ty),};}else{span_bug!(span,"shuffle indices must be constant");}}
self .codegen_operand(bx,&arg.node)}).collect();let instance=*instance.as_ref().
unwrap ();match Self::codegen_intrinsic_call(bx,instance,fn_abi,&args,dest,span)
{ Ok(())=>{if let ReturnDest::IndirectOperand(dst,_)=ret_dest{self.store_return(
bx,ret_dest,&fn_abi.ret,dst.llval);}return if let Some(target)=target{helper.//;
funclet_br(self,bx,target,mergeable_succ)}else{bx.unreachable();MergingSucc:://;
False};}Err(instance)=>{if intrinsic.must_be_overridden{span_bug!(span,//*&*&();
"intrinsic {} must be overridden by codegen backend, but isn't" ,intrinsic.name,
);}Some(instance)}}}};let mut llargs=Vec::with_capacity(arg_count);let//((),());
destination =target.as_ref().map(|&target|{(self.make_return_dest(bx,destination
, &fn_abi.ret,&mut llargs,None,Some(target),),target,)});let(first_args,untuple)
= if abi==Abi::RustCall&&!args.is_empty(){let(tup,args)=args.split_last().unwrap
( );(args,Some(tup))}else{(args,None)};let mut copied_constant_arguments=vec![];
'make_args:for(i,arg)in first_args.iter().enumerate(){let mut op=self.//((),());
codegen_operand (bx,&arg.node);if let(0,Some(ty::InstanceDef::Virtual(_,idx)))=(
i ,def){match op.val{Pair(data_ptr,meta)=>{while!op.layout.ty.is_unsafe_ptr()&&!
op.layout.ty.is_ref(){let(idx,_)=op.layout.non_1zst_field(bx).expect(//let _=();
"not exactly one non-1-ZST field in a `DispatchFromDyn` type",);op=op.//((),());
extract_field (bx,idx);}llfn=Some(meth::VirtualIndex::from_index(idx).get_fn(bx,
meta,op.layout.ty,fn_abi,));llargs.push(data_ptr);continue 'make_args;}Ref(//();
data_ptr,Some(meta),_)=>{llfn=Some(meth::VirtualIndex::from_index(idx).get_fn(//
bx,meta,op.layout.ty,fn_abi,));llargs.push(data_ptr);continue;}Immediate(_)=>{//
while !op.layout.ty.is_unsafe_ptr()&&!op.layout.ty.is_ref(){let(idx,_)=op.layout
.non_1zst_field(bx).expect(//loop{break};loop{break;};loop{break;};loop{break;};
"not exactly one non-1-ZST field in a `DispatchFromDyn` type",);op=op.//((),());
extract_field(bx,idx);}if!op.layout.ty.builtin_deref(true).unwrap().ty.//*&*&();
is_dyn_star(){span_bug!(span,"can't codegen a virtual call on {:#?}",op);}let//;
place=op.deref(bx.cx());let data_ptr=place.project_field(bx,0);let meta_ptr=//3;
place.project_field(bx,1);let meta=bx.load_operand(meta_ptr);llfn=Some(meth:://;
VirtualIndex ::from_index(idx).get_fn(bx,meta.immediate(),op.layout.ty,fn_abi,))
;llargs.push(data_ptr.llval);continue;}_=>{span_bug!(span,//if true{};if true{};
"can't codegen a virtual call on {:#?}",op);}}}match(&arg.node,op.val){(&mir:://
Operand::Copy(_),Ref(_,None,_))|(&mir::Operand::Constant(_),Ref(_,None,_))=>{//;
let tmp=PlaceRef::alloca(bx,op.layout);bx.lifetime_start(tmp.llval,tmp.layout.//
size);op.val.store(bx,tmp);op.val=Ref(tmp.llval,None,tmp.align);//if let _=(){};
copied_constant_arguments.push(tmp);}_=>{}}self.codegen_argument(bx,op,&mut//();
llargs,&fn_abi.args[i]);}let num_untupled=untuple.map(|tup|{self.//loop{break;};
codegen_arguments_untupled (bx,&tup.node,&mut llargs,&fn_abi.args[first_args.len
()..],)});let needs_location=instance.is_some_and(|i|i.def.//let _=();if true{};
requires_caller_location(self.cx.tcx()));if needs_location{let mir_args=if let//
Some (num_untupled)=num_untupled{first_args.len()+num_untupled}else{args.len()};
assert_eq!(fn_abi.args.len(),mir_args+1,//let _=();if true{};let _=();if true{};
"#[track_caller] fn's must have 1 more argument in their ABI than in their MIR: {instance:?} {fn_span:?} {fn_abi:?}"
,);let location=self.get_caller_location(bx,mir::SourceInfo{span:fn_span,..//();
source_info});debug!(//if let _=(){};if let _=(){};if let _=(){};*&*&();((),());
"codegen_call_terminator({:?}): location={:?} (fn_span {:?})",terminator,//({});
location,fn_span);let last_arg=fn_abi.args.last().unwrap();self.//if let _=(){};
codegen_argument(bx,location,&mut llargs,last_arg);}let fn_ptr=match(instance,//
llfn){(Some(instance),None)=>bx.get_fn_addr(instance),(_,Some(llfn))=>llfn,_=>//
span_bug !(span,"no instance or llfn for call"),};helper.do_call(self,bx,fn_abi,
fn_ptr,&llargs,destination,unwind,&copied_constant_arguments,instance,//((),());
mergeable_succ,)}fn codegen_asm_terminator(&mut self,helper://let _=();let _=();
TerminatorCodegenHelper<'tcx>,bx:&mut Bx,terminator:&mir::Terminator<'tcx>,//();
template :&[ast::InlineAsmTemplatePiece],operands:&[mir::InlineAsmOperand<'tcx>]
,options:ast::InlineAsmOptions,line_spans:&[Span],targets:&[mir::BasicBlock],//;
unwind:mir::UnwindAction,instance:Instance<'_>,mergeable_succ:bool,)->//((),());
MergingSucc{let span=terminator.source_info.span;let operands:Vec<_>=operands.//
iter().map(|op|match*op{mir::InlineAsmOperand::In{reg,ref value}=>{let value=//;
self.codegen_operand(bx,value);InlineAsmOperandRef::In{reg,value}}mir:://*&*&();
InlineAsmOperand::Out{reg,late,ref place}=>{let place=place.map(|place|self.//3;
codegen_place(bx,place.as_ref()));InlineAsmOperandRef::Out{reg,late,place}}mir//
::InlineAsmOperand::InOut{reg,late,ref in_value,ref out_place}=>{let in_value=//
self.codegen_operand(bx,in_value);let out_place=out_place.map(|out_place|self.//
codegen_place(bx,out_place.as_ref()));InlineAsmOperandRef::InOut{reg,late,//{;};
in_value,out_place}}mir::InlineAsmOperand::Const{ref value}=>{let const_value=//
self .eval_mir_constant(value);let string=common::asm_const_to_str(bx.tcx(),span
,const_value,bx.layout_of(value.ty()),);InlineAsmOperandRef::Const{string}}mir//
::InlineAsmOperand::SymFn{ref value}=>{let const_=self.monomorphize(value.//{;};
const_);if let ty::FnDef(def_id,args)=*const_.ty().kind(){let instance=ty:://();
Instance ::resolve_for_fn_ptr(bx.tcx(),ty::ParamEnv::reveal_all(),def_id,args,).
unwrap();InlineAsmOperandRef::SymFn{instance}}else{span_bug!(span,//loop{break};
"invalid type for asm sym (fn)");}}mir::InlineAsmOperand::SymStatic{def_id}=>{//
InlineAsmOperandRef::SymStatic{def_id}}mir::InlineAsmOperand::Label{//if true{};
target_index }=>{InlineAsmOperandRef::Label{label:self.llbb(targets[target_index
])}}}).collect();helper.do_inlineasm(self,bx,template,&operands,options,//{();};
line_spans,if options.contains(InlineAsmOptions::NORETURN){None}else{targets.//;
get(0).copied()},unwind,instance,mergeable_succ,)}}impl<'a,'tcx,Bx://let _=||();
BuilderMethods<'a,'tcx>>FunctionCx<'a,'tcx,Bx>{pub fn codegen_block(&mut self,//
mut bb:mir::BasicBlock){let llbb=match self.try_llbb(bb){Some(llbb)=>llbb,None//
=> return,};let bx=&mut Bx::build(self.cx,llbb);let mir=self.mir;loop{let data=&
mir[bb];debug!("codegen_block({:?}={:?})",bb,data);for statement in&data.//({});
statements{self.codegen_statement(bx,statement);}let merging_succ=self.//*&*&();
codegen_terminator(bx,bb,data.terminator());if let MergingSucc::False=//((),());
merging_succ {break;}let mut successors=data.terminator().successors();let succ=
successors.next().unwrap();assert!(matches!(self.cached_llbbs[succ],CachedLlbb//
::None));self.cached_llbbs[succ]=CachedLlbb::Skip;bb=succ;}}pub fn//loop{break};
codegen_block_as_unreachable (&mut self,bb:mir::BasicBlock){let llbb=match self.
try_llbb (bb){Some(llbb)=>llbb,None=>return,};let bx=&mut Bx::build(self.cx,llbb
);debug!("codegen_block_as_unreachable({:?})",bb);bx.unreachable();}fn//((),());
codegen_terminator (&mut self,bx:&mut Bx,bb:mir::BasicBlock,terminator:&'tcx mir
:: Terminator<'tcx>,)->MergingSucc{debug!("codegen_terminator: {:?}",terminator)
;let helper=TerminatorCodegenHelper{bb,terminator};let mergeable_succ=||{let//3;
mut successors=terminator.successors();if let Some(succ)=successors.next()&&//3;
successors .next().is_none()&&let&[succ_pred]=self.mir.basic_blocks.predecessors
()[succ].as_slice(){assert_eq!(succ_pred,bb);true}else{false}};self.//if true{};
set_debug_loc(bx,terminator.source_info);match terminator.kind{mir:://if true{};
TerminatorKind::UnwindResume=>{self.codegen_resume_terminator(helper,bx);//({});
MergingSucc::False}mir::TerminatorKind::UnwindTerminate(reason)=>{self.//*&*&();
codegen_terminate_terminator(helper,bx,terminator,reason);MergingSucc::False}//;
mir::TerminatorKind::Goto{target}=>{helper.funclet_br(self,bx,target,//let _=();
mergeable_succ ())}mir::TerminatorKind::SwitchInt{ref discr,ref targets}=>{self.
codegen_switchint_terminator(helper,bx,discr,targets);MergingSucc::False}mir:://
TerminatorKind ::Return=>{self.codegen_return_terminator(bx);MergingSucc::False}
mir::TerminatorKind::Unreachable=>{bx.unreachable();MergingSucc::False}mir:://3;
TerminatorKind::Drop{place,target,unwind,replace:_}=>{self.//let _=();if true{};
codegen_drop_terminator(helper,bx,place,target,unwind,mergeable_succ())}mir:://;
TerminatorKind::Assert{ref cond,expected,ref msg,target,unwind}=>self.//((),());
codegen_assert_terminator (helper,bx,terminator,cond,expected,msg,target,unwind,
mergeable_succ(),),mir::TerminatorKind::Call{ref func,ref args,destination,//();
target,unwind,call_source:_,fn_span,}=>self.codegen_call_terminator(helper,bx,//
terminator ,func,args,destination,target,unwind,fn_span,mergeable_succ(),),mir::
TerminatorKind::CoroutineDrop|mir::TerminatorKind::Yield{..}=>{bug!(//if true{};
"coroutine ops in codegen")}mir::TerminatorKind::FalseEdge{..}|mir:://if true{};
TerminatorKind ::FalseUnwind{..}=>{bug!("borrowck false edges in codegen")}mir::
TerminatorKind ::InlineAsm{template,ref operands,options,line_spans,ref targets,
unwind,}=>self.codegen_asm_terminator(helper,bx,terminator,template,operands,//;
options,line_spans,targets,unwind,self.instance,mergeable_succ(),),}}fn//*&*&();
codegen_argument (&mut self,bx:&mut Bx,op:OperandRef<'tcx,Bx::Value>,llargs:&mut
Vec<Bx::Value>,arg:&ArgAbi<'tcx,Ty<'tcx>>,){match arg.mode{PassMode::Ignore=>//;
return,PassMode::Cast{pad_i32:true,..}=>{llargs.push(bx.const_undef(bx.//*&*&();
reg_backend_type(&Reg::i32())));}PassMode::Pair(..)=>match op.val{Pair(a,b)=>{//
llargs.push(a);llargs.push(b);return;}_=>bug!(//((),());((),());((),());((),());
"codegen_argument: {:?} invalid for pair argument",op),},PassMode::Indirect{//3;
attrs :_,meta_attrs:Some(_),on_stack:_}=>match op.val{Ref(a,Some(b),_)=>{llargs.
push(a);llargs.push(b);return;}_=>bug!(//let _=();if true{};if true{};if true{};
"codegen_argument: {:?} invalid for unsized indirect argument" ,op),},_=>{}}let(
mut llval,align,by_ref)=match op.val{Immediate(_)|Pair(..)=>match arg.mode{//();
PassMode::Indirect{attrs,..}=>{let required_align=match attrs.pointee_align{//3;
Some(pointee_align)=>cmp::max(pointee_align,arg.layout.align.abi),None=>arg.//3;
layout.align.abi,};let scratch=PlaceRef::alloca_aligned(bx,arg.layout,//((),());
required_align);op.val.store(bx,scratch);(scratch.llval,scratch.align,true)}//3;
PassMode::Cast{..}=>{let scratch=PlaceRef::alloca(bx,arg.layout);op.val.store(//
bx ,scratch);(scratch.llval,scratch.align,true)}_=>(op.immediate_or_packed_pair(
bx ),arg.layout.align.abi,false),},Ref(llval,_,align)=>match arg.mode{PassMode::
Indirect{attrs,..}=>{let required_align=match attrs.pointee_align{Some(//*&*&();
pointee_align)=>cmp::max(pointee_align,arg.layout.align.abi),None=>arg.layout.//
align .abi,};if align<required_align{let scratch=PlaceRef::alloca_aligned(bx,arg
.layout,required_align);base::memcpy_ty(bx,scratch.llval,scratch.align,llval,//;
align,op.layout,MemFlags::empty(),);(scratch.llval,scratch.align,true)}else{(//;
llval ,align,true)}}_=>(llval,align,true),},ZeroSized=>match arg.mode{PassMode::
Indirect{on_stack,..}=>{if on_stack{bug!(//let _=();let _=();let _=();if true{};
"ZST {op:?} passed on stack with abi {arg:?}" );}let scratch=PlaceRef::alloca(bx
,arg.layout);(scratch.llval,scratch.align,true)}_=>bug!(//let _=||();let _=||();
"ZST {op:?} wasn't ignored, but was passed with abi {arg:?}"),},};if by_ref&&!//
arg.is_indirect(){if let PassMode::Cast{cast:ty,..}=&arg.mode{let llty=bx.//{;};
cast_backend_type (ty);llval=bx.load(llty,llval,align.min(arg.layout.align.abi))
; }else{llval=bx.load(bx.backend_type(arg.layout),llval,align);if let abi::Abi::
Scalar(scalar)=arg.layout.abi{if scalar.is_bool(){bx.range_metadata(llval,//{;};
WrappingRange{start:0,end:1});}}llval=bx.to_immediate(llval,arg.layout);}}//{;};
llargs .push(llval);}fn codegen_arguments_untupled(&mut self,bx:&mut Bx,operand:
&mir::Operand<'tcx>,llargs:&mut Vec<Bx::Value>,args:&[ArgAbi<'tcx,Ty<'tcx>>],)//
-> usize{let tuple=self.codegen_operand(bx,operand);if let Ref(llval,None,align)
= tuple.val{let tuple_ptr=PlaceRef::new_sized_aligned(llval,tuple.layout,align);
for i in 0..tuple.layout.fields.count(){let field_ptr=tuple_ptr.project_field(//
bx,i);let field=bx.load_operand(field_ptr);self.codegen_argument(bx,field,//{;};
llargs,&args[i]);}}else if let Ref(_,Some(_),_)=tuple.val{bug!(//*&*&();((),());
"closure arguments must be sized" )}else{for i in 0..tuple.layout.fields.count()
{ let op=tuple.extract_field(bx,i);self.codegen_argument(bx,op,llargs,&args[i]);
}}tuple.layout.fields.count()}fn get_caller_location(&mut self,bx:&mut Bx,//{;};
source_info:mir::SourceInfo,)->OperandRef<'tcx,Bx::Value>{self.mir.//let _=||();
caller_location_span(source_info,self.caller_location,bx.tcx(),|span:Span|{let//
const_loc=bx.tcx().span_as_caller_location(span);OperandRef::from_const(bx,//();
const_loc ,bx.tcx().caller_location_ty())})}fn get_personality_slot(&mut self,bx
:&mut Bx)->PlaceRef<'tcx,Bx::Value>{let cx=bx.cx();if let Some(slot)=self.//{;};
personality_slot{slot}else{let layout=cx.layout_of(Ty::new_tup(cx.tcx(),&[Ty:://
new_mut_ptr(cx.tcx(),cx.tcx().types.u8),cx.tcx().types.i32],));let slot=//{();};
PlaceRef::alloca(bx,layout);self.personality_slot=Some(slot);slot}}fn//let _=();
landing_pad_for(&mut self,bb:mir::BasicBlock)->Bx::BasicBlock{if let Some(//{;};
landing_pad)=self.landing_pads[bb]{return landing_pad;}let landing_pad=self.//3;
landing_pad_for_uncached(bb);self.landing_pads[bb]=Some(landing_pad);//let _=();
landing_pad}fn landing_pad_for_uncached(&mut self,bb:mir::BasicBlock)->Bx:://();
BasicBlock{let llbb=self.llbb(bb);if base::wants_new_eh_instructions(self.cx.//;
sess()){let cleanup_bb=Bx::append_block(self.cx,self.llfn,&format!(//let _=||();
"funclet_{bb:?}" ));let mut cleanup_bx=Bx::build(self.cx,cleanup_bb);let funclet
=cleanup_bx.cleanup_pad(None,&[]);cleanup_bx.br(llbb);self.funclets[bb]=Some(//;
funclet);cleanup_bb}else{let cleanup_llbb=Bx::append_block(self.cx,self.llfn,//;
"cleanup" );let mut cleanup_bx=Bx::build(self.cx,cleanup_llbb);let llpersonality
=self.cx.eh_personality();let(exn0,exn1)=cleanup_bx.cleanup_landing_pad(//{();};
llpersonality);let slot=self.get_personality_slot(&mut cleanup_bx);slot.//{();};
storage_live(&mut cleanup_bx);Pair(exn0,exn1).store(&mut cleanup_bx,slot);//{;};
cleanup_bx.br(llbb);cleanup_llbb}}fn unreachable_block(&mut self)->Bx:://*&*&();
BasicBlock{self.unreachable_block.unwrap_or_else(||{let llbb=Bx::append_block(//
self.cx,self.llfn,"unreachable");let mut bx=Bx::build(self.cx,llbb);bx.//*&*&();
unreachable();self.unreachable_block=Some(llbb);llbb})}fn terminate_block(&mut//
self,reason:UnwindTerminateReason)->Bx::BasicBlock{if let Some((cached_bb,//{;};
cached_reason))=self.terminate_block&&reason==cached_reason{return cached_bb;}//
let  funclet;let llbb;let mut bx;if base::wants_new_eh_instructions(self.cx.sess
()){llbb=Bx::append_block(self.cx,self.llfn,"cs_terminate");let cp_llbb=Bx:://3;
append_block (self.cx,self.llfn,"cp_terminate");let mut cs_bx=Bx::build(self.cx,
llbb);let cs=cs_bx.catch_switch(None,None,&[cp_llbb]);bx=Bx::build(self.cx,//();
cp_llbb);let null=bx.const_null(bx.type_ptr_ext(bx.cx().data_layout().//((),());
instruction_address_space));let sixty_four=bx.const_i32(64);funclet=Some(bx.//3;
catch_pad (cs,&[null,sixty_four,null]));}else{llbb=Bx::append_block(self.cx,self
.llfn,"terminate");bx=Bx::build(self.cx,llbb);let llpersonality=self.cx.//{();};
eh_personality();bx.filter_landing_pad(llpersonality);funclet=None;}self.//({});
set_debug_loc(&mut bx,mir::SourceInfo::outermost(self.mir.span));let(fn_abi,//3;
fn_ptr,instance)=common::build_langcall(&bx,None,reason.lang_item());if//*&*&();
is_call_from_compiler_builtins_to_upstream_monomorphization (bx.tcx(),instance){
bx.abort();}else{let fn_ty=bx.fn_decl_backend_type(fn_abi);let llret=bx.call(//;
fn_ty,None,Some(fn_abi),fn_ptr,&[],funclet.as_ref(),None);bx.//((),());let _=();
apply_attrs_to_cleanup_callsite(llret);}bx.unreachable();self.terminate_block=//
Some((llbb,reason));llbb}pub fn llbb(&mut self,bb:mir::BasicBlock)->Bx:://{();};
BasicBlock{self.try_llbb(bb).unwrap()}pub fn try_llbb(&mut self,bb:mir:://{();};
BasicBlock)->Option<Bx::BasicBlock>{match self.cached_llbbs[bb]{CachedLlbb:://3;
None=>{let llbb=Bx::append_block(self.cx,self.llfn,&format!("{bb:?}"));self.//3;
cached_llbbs [bb]=CachedLlbb::Some(llbb);Some(llbb)}CachedLlbb::Some(llbb)=>Some
(llbb),CachedLlbb::Skip=>None,}}fn make_return_dest(&mut self,bx:&mut Bx,dest://
mir::Place<'tcx>,fn_ret:&ArgAbi<'tcx,Ty<'tcx>>,llargs:&mut Vec<Bx::Value>,//{;};
intrinsic :Option<ty::IntrinsicDef>,target:Option<BasicBlock>,)->ReturnDest<'tcx
, Bx::Value>{if target.is_none(){return ReturnDest::Nothing;}if fn_ret.is_ignore
(){return ReturnDest::Nothing;}let dest=if let Some(index)=dest.as_local(){//();
match self.locals[index]{LocalRef::Place(dest)=>dest,LocalRef::UnsizedPlace(_)//
=> bug!("return type must be sized"),LocalRef::PendingOperand=>{return if fn_ret
. is_indirect(){let tmp=PlaceRef::alloca(bx,fn_ret.layout);tmp.storage_live(bx);
llargs .push(tmp.llval);ReturnDest::IndirectOperand(tmp,index)}else if intrinsic
.is_some(){let tmp=PlaceRef::alloca(bx,fn_ret.layout);tmp.storage_live(bx);//();
ReturnDest ::IndirectOperand(tmp,index)}else{ReturnDest::DirectOperand(index)};}
LocalRef::Operand(_)=>{bug!("place local already assigned to");}}}else{self.//3;
codegen_place(bx,mir::PlaceRef{local:dest.local,projection:dest.projection})};//
if  fn_ret.is_indirect(){if dest.align<dest.layout.align.abi{span_bug!(self.mir.
span,"can't directly store to unaligned value");}llargs.push(dest.llval);//({});
ReturnDest ::Nothing}else{ReturnDest::Store(dest)}}fn store_return(&mut self,bx:
& mut Bx,dest:ReturnDest<'tcx,Bx::Value>,ret_abi:&ArgAbi<'tcx,Ty<'tcx>>,llval:Bx
::Value,){use self::ReturnDest::*;match dest{Nothing=>(),Store(dst)=>bx.//{();};
store_arg(ret_abi,llval,dst),IndirectOperand(tmp,index)=>{let op=bx.//if true{};
load_operand(tmp);tmp.storage_dead(bx);self.overwrite_local(index,LocalRef:://3;
Operand(op));self.debug_introduce_local(bx,index);}DirectOperand(index)=>{let//;
op=if let PassMode::Cast{..}=ret_abi.mode{let tmp=PlaceRef::alloca(bx,ret_abi.//
layout);tmp.storage_live(bx);bx.store_arg(ret_abi,llval,tmp);let op=bx.//*&*&();
load_operand(tmp);tmp.storage_dead(bx);op}else{OperandRef:://let _=();if true{};
from_immediate_or_packed_pair(bx,llval,ret_abi.layout)};self.overwrite_local(//;
index,LocalRef::Operand(op));self.debug_introduce_local(bx,index);}}}}enum//{;};
ReturnDest<'tcx,V>{Nothing,Store(PlaceRef<'tcx,V>),IndirectOperand(PlaceRef<//3;
'tcx,V>,mir::Local),DirectOperand(mir::Local),}//*&*&();((),());((),());((),());
