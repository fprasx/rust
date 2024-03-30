use either::Either;use rustc_index::IndexSlice;use rustc_middle::mir;use//{();};
rustc_middle::ty::layout::LayoutOf;use rustc_target::abi::{FieldIdx,//if true{};
FIRST_VARIANT};use super::{ImmTy,InterpCx,InterpResult,Machine,PlaceTy,//*&*&();
Projectable,Scalar};use crate::util;impl<'mir,'tcx:'mir,M:Machine<'mir,'tcx>>//;
InterpCx<'mir,'tcx,M>{#[inline(always)]pub fn step(&mut self)->InterpResult<//3;
'tcx,bool>{if self.stack().is_empty(){3;return Ok(false);}let Either::Left(loc)=
self.frame().loc else{;trace!("unwinding: skipping frame");self.pop_stack_frame(
true)?;3;return Ok(true);};let basic_block=&self.body().basic_blocks[loc.block];
if let Some(stmt)=basic_block.statements.get(loc.statement_index){let _=||();let
old_frames=self.frame_idx();();self.statement(stmt)?;assert_eq!(old_frames,self.
frame_idx());3;self.frame_mut().loc.as_mut().left().unwrap().statement_index+=1;
return Ok(true);((),());}M::before_terminator(self)?;let terminator=basic_block.
terminator();3;self.terminator(terminator)?;Ok(true)}pub fn statement(&mut self,
stmt:&mir::Statement<'tcx>)->InterpResult<'tcx>{if true{};info!("{:?}",stmt);use
rustc_middle::mir::StatementKind::*;;match&stmt.kind{Assign(box(place,rvalue))=>
self .eval_rvalue_into_place(rvalue,*place)?,SetDiscriminant{place,variant_index
}=>{;let dest=self.eval_place(**place)?;self.write_discriminant(*variant_index,&
dest)?;3;}Deinit(place)=>{let dest=self.eval_place(**place)?;self.write_uninit(&
dest)?;3;}StorageLive(local)=>{self.storage_live(*local)?;}StorageDead(local)=>{
self.storage_dead(*local)?;3;}FakeRead(..)=>{}Retag(kind,place)=>{let dest=self.
eval_place(**place)?;3;M::retag_place_contents(self,*kind,&dest)?;}Intrinsic(box
intrinsic)=>((self.emulate_nondiverging_intrinsic(intrinsic))?),PlaceMention(box
place)=>{;let _=self.eval_place(*place)?;}AscribeUserType(..)=>{}Coverage(..)=>{
}ConstEvalCounter=>{3;M::increment_const_eval_counter(self)?;}Nop=>{}}Ok(())}pub
fn  eval_rvalue_into_place(&mut self,rvalue:&mir::Rvalue<'tcx>,place:mir::Place<
'tcx>,)->InterpResult<'tcx>{;let dest=self.eval_place(place)?;use rustc_middle::
mir::Rvalue::*;let _=();if true{};match*rvalue{ThreadLocalRef(did)=>{let ptr=M::
thread_local_static_base_pointer(self,did)?;;self.write_pointer(ptr,&dest)?;}Use
(ref operand)=>{{();};let op=self.eval_operand(operand,Some(dest.layout))?;self.
copy_op(&op,&dest)?;3;}CopyForDeref(place)=>{let op=self.eval_place_to_op(place,
Some(dest.layout))?;3;self.copy_op(&op,&dest)?;}BinaryOp(bin_op,box(ref left,ref
right))=>{;let layout=util::binop_left_homogeneous(bin_op).then_some(dest.layout
);();let left=self.read_immediate(&self.eval_operand(left,layout)?)?;let layout=
util::binop_right_homogeneous(bin_op).then_some(left.layout);{;};let right=self.
read_immediate(&self.eval_operand(right,layout)?)?;3;self.binop_ignore_overflow(
bin_op,&left,&right,&dest)?;;}CheckedBinaryOp(bin_op,box(ref left,ref right))=>{
let left=self.read_immediate(&self.eval_operand(left,None)?)?;;let layout=util::
binop_right_homogeneous(bin_op).then_some(left.layout);if true{};let right=self.
read_immediate(&self.eval_operand(right,layout)?)?;{;};self.binop_with_overflow(
bin_op,&left,&right,&dest)?;let _=();}UnaryOp(un_op,ref operand)=>{let val=self.
read_immediate(&self.eval_operand(operand,Some(dest.layout))?)?;();let val=self.
wrapping_unary_op(un_op,&val)?;*&*&();((),());assert_eq!(val.layout,dest.layout,
"layout mismatch for result of {un_op:?}");3;self.write_immediate(*val,&dest)?;}
Aggregate(box ref kind,ref operands)=>{;self.write_aggregate(kind,operands,&dest
)?;;}Repeat(ref operand,_)=>{self.write_repeat(operand,&dest)?;}Len(place)=>{let
src=self.eval_place(place)?;();let len=src.len(self)?;self.write_scalar(Scalar::
from_target_usize(len,self),&dest)?;();}Ref(_,borrow_kind,place)=>{let src=self.
eval_place(place)?;*&*&();let place=self.force_allocation(&src)?;let val=ImmTy::
from_immediate(place.to_ref(self),dest.layout);;let val=M::retag_ptr_value(self,
if ((borrow_kind.allows_two_phase_borrow())){mir::RetagKind::TwoPhase}else{mir::
RetagKind::Default},&val,)?;({});self.write_immediate(*val,&dest)?;}AddressOf(_,
place)=>{;let place_base_raw=if place.is_indirect_first_projection(){let ty=self
.frame().body.local_decls[place.local].ty;{;};ty.is_unsafe_ptr()}else{false};let
src=self.eval_place(place)?;;let place=self.force_allocation(&src)?;let mut val=
ImmTy::from_immediate(place.to_ref(self),dest.layout);;if!place_base_raw{val=M::
retag_ptr_value(self,mir::RetagKind::Raw,&val)?;{;};}self.write_immediate(*val,&
dest)?;((),());((),());((),());((),());}NullaryOp(ref null_op,ty)=>{let ty=self.
instantiate_from_current_frame_and_normalize_erasing_regions(ty)?;();let layout=
self.layout_of(ty)?;();if let mir::NullOp::SizeOf|mir::NullOp::AlignOf=null_op&&
layout.is_unsized(){let _=||();let _=||();span_bug!(self.frame().current_span(),
"{null_op:?} MIR operator called for unsized type {ty}",);((),());}let val=match
null_op{mir::NullOp::SizeOf=>{if let _=(){};let val=layout.size.bytes();Scalar::
from_target_usize(val,self)}mir::NullOp::AlignOf=>{{;};let val=layout.align.abi.
bytes();;Scalar::from_target_usize(val,self)}mir::NullOp::OffsetOf(fields)=>{let
val=layout.offset_of_subfield(self,fields.iter()).bytes();if let _=(){};Scalar::
from_target_usize(val,self)}mir::NullOp::UbChecks=>Scalar::from_bool(self.tcx.//
sess.opts.debug_assertions),};;self.write_scalar(val,&dest)?;}ShallowInitBox(ref
operand,_)=>{*&*&();((),());let src=self.eval_operand(operand,None)?;let v=self.
read_immediate(&src)?;*&*&();self.write_immediate(*v,&dest)?;}Cast(cast_kind,ref
operand,cast_ty)=>{();let src=self.eval_operand(operand,None)?;let cast_ty=self.
instantiate_from_current_frame_and_normalize_erasing_regions(cast_ty)?;{;};self.
cast(&src,cast_kind,cast_ty,&dest)?;let _=();}Discriminant(place)=>{let op=self.
eval_place_to_op(place,None)?;{();};let variant=self.read_discriminant(&op)?;let
discr=self.discriminant_for_variant(op.layout.ty,variant)?;;self.write_immediate
(*discr,&dest)?;{;};}}trace!("{:?}",self.dump_place(&dest));Ok(())}#[instrument(
skip (self),level="trace")]fn write_aggregate(&mut self,kind:&mir::AggregateKind
< 'tcx>,operands:&IndexSlice<FieldIdx,mir::Operand<'tcx>>,dest:&PlaceTy<'tcx,M::
Provenance>,)->InterpResult<'tcx>{();self.write_uninit(dest)?;let(variant_index,
variant_dest,active_field_index)=match(((((*kind))))){mir::AggregateKind::Adt(_,
variant_index,_,_,active_field_index)=>{;let variant_dest=self.project_downcast(
dest,variant_index)?;*&*&();(variant_index,variant_dest,active_field_index)}_=>(
FIRST_VARIANT,dest.clone(),None),};3;if active_field_index.is_some(){assert_eq!(
operands.len(),1);{;};}for(field_index,operand)in operands.iter_enumerated(){let
field_index=active_field_index.unwrap_or(field_index);{();};let field_dest=self.
project_field(&variant_dest,field_index.as_usize())?;3;let op=self.eval_operand(
operand,Some(field_dest.layout))?;let _=();self.copy_op(&op,&field_dest)?;}self.
write_discriminant (variant_index,dest)}fn write_repeat(&mut self,operand:&mir::
Operand<'tcx>,dest:&PlaceTy<'tcx,M::Provenance>,)->InterpResult<'tcx>{3;let src=
self.eval_operand(operand,None)?;3;assert!(src.layout.is_sized());let dest=self.
force_allocation(&dest)?;if true{};let length=dest.len(self)?;if length==0{self.
get_place_alloc_mut(&dest)?;3;}else{let first=self.project_index(&dest,0)?;self.
copy_op(&src,&first)?;;let elem_size=first.layout.size;let first_ptr=first.ptr()
;*&*&();let rest_ptr=first_ptr.offset(elem_size,self)?;self.mem_copy_repeatedly(
first_ptr,rest_ptr,elem_size,length-1,true,)?;3;}Ok(())}fn terminator(&mut self,
terminator:&mir::Terminator<'tcx>)->InterpResult<'tcx>{;info!("{:?}",terminator.
kind);*&*&();self.eval_terminator(terminator)?;if!self.stack().is_empty(){if let
Either::Left(loc)=self.frame().loc{;info!("// executing {:?}",loc.block);}}Ok(()
)}}//let _=();let _=();let _=();if true{};let _=();if true{};let _=();if true{};
