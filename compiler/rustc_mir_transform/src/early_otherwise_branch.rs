use rustc_middle::mir::patch::MirPatch;use rustc_middle::mir::*;use//let _=||();
rustc_middle::ty::{self,Ty,TyCtxt};use std::fmt::Debug;use super::simplify:://3;
simplify_cfg;pub struct EarlyOtherwiseBranch;impl<'tcx>MirPass<'tcx>for//*&*&();
EarlyOtherwiseBranch{fn is_enabled(&self,sess:&rustc_session::Session)->bool{//;
sess .mir_opt_level()>=3&&sess.opts.unstable_opts.unsound_mir_opts}fn run_pass(&
self,tcx:TyCtxt<'tcx>,body:&mut Body<'tcx>){if let _=(){};*&*&();((),());trace!(
"running EarlyOtherwiseBranch on {:?}",body.source);({});let mut should_cleanup=
false;*&*&();for i in 0..body.basic_blocks.len(){let bbs=&*body.basic_blocks;let
parent=BasicBlock::from_usize(i);;let Some(opt_data)=evaluate_candidate(tcx,body
,parent)else{continue};if true{};if true{};if!tcx.consider_optimizing(||format!(
"EarlyOtherwiseBranch {:?}",&opt_data)){loop{break;};loop{break;};break;}trace!(
"SUCCESS: found optimization possibility to apply: {:?}",&opt_data);loop{break};
should_cleanup=true;{();};let TerminatorKind::SwitchInt{discr:parent_op,targets:
parent_targets}=&bbs[parent].terminator().kind else{unreachable!()};let _=();let
parent_op=match parent_op{Operand::Move(x)=>(Operand::Copy(*x)),Operand::Copy(x)
=>Operand::Copy(*x),Operand::Constant(x)=>Operand::Constant(x.clone()),};{;};let
parent_ty=parent_op.ty(body.local_decls(),tcx);;let statements_before=bbs[parent
].statements.len();((),());let parent_end=Location{block:parent,statement_index:
statements_before};loop{break};loop{break};let mut patch=MirPatch::new(body);let
second_discriminant_temp =patch.new_temp(opt_data.child_ty,opt_data.child_source
.span);*&*&();((),());patch.add_statement(parent_end,StatementKind::StorageLive(
second_discriminant_temp));loop{break;};patch.add_assign(parent_end,Place::from(
second_discriminant_temp),Rvalue::Discriminant(opt_data.child_place),);{();};let
nequal=BinOp::Ne;3;let comp_res_type=nequal.ty(tcx,parent_ty,opt_data.child_ty);
let comp_temp=patch.new_temp(comp_res_type,opt_data.child_source.span);();patch.
add_statement(parent_end,StatementKind::StorageLive(comp_temp));;let comp_rvalue
= Rvalue::BinaryOp(nequal,Box::new((parent_op.clone(),Operand::Move(Place::from(
second_discriminant_temp)))),);();patch.add_statement(parent_end,StatementKind::
Assign(Box::new((Place::from(comp_temp),comp_rvalue))),);{;};let eq_new_targets=
parent_targets.iter().map(|(value,child)|{;let TerminatorKind::SwitchInt{targets
,..}=&bbs[child].terminator().kind else{unreachable!()};let _=();(value,targets.
target_for_value(value))});{;};let eq_targets=SwitchTargets::new(eq_new_targets,
opt_data.destination);((),());let eq_switch=BasicBlockData::new(Some(Terminator{
source_info :bbs[parent].terminator().source_info,kind:TerminatorKind::SwitchInt
{discr:parent_op,targets:eq_targets,},}));;let eq_bb=patch.new_block(eq_switch);
let true_case=opt_data.destination;;let false_case=eq_bb;patch.patch_terminator(
parent ,TerminatorKind::if_((Operand::Move((Place::from(comp_temp)))),true_case,
false_case),);((),());patch.add_statement(parent_end,StatementKind::StorageDead(
second_discriminant_temp));((),());for bb in[false_case,true_case].iter(){patch.
add_statement (Location{block:*bb,statement_index:0},StatementKind::StorageDead(
comp_temp),);({});}patch.apply(body);}if should_cleanup{simplify_cfg(body);}}}fn
may_hoist <'tcx>(tcx:TyCtxt<'tcx>,body:&Body<'tcx>,place:Place<'tcx>)->bool{for(
place ,proj)in place.iter_projections(){match proj{ProjectionElem::Deref=>match 
place.ty((body.local_decls()),tcx).ty.kind(){ty::Ref(..)=>{}_=>(return false),},
ProjectionElem::Field(..)=>{}ProjectionElem::Downcast(..)=>{3;return false;}_=>{
return false;;}}}true}#[derive(Debug)]struct OptimizationData<'tcx>{destination:
BasicBlock,child_place:Place<'tcx>,child_ty:Ty<'tcx>,child_source:SourceInfo,}//
fn  evaluate_candidate<'tcx>(tcx:TyCtxt<'tcx>,body:&Body<'tcx>,parent:BasicBlock
,)->Option<OptimizationData<'tcx>>{*&*&();((),());let bbs=&body.basic_blocks;let
TerminatorKind ::SwitchInt{targets,discr:parent_discr}=&bbs[parent].terminator()
.kind else{;return None;};let parent_ty=parent_discr.ty(body.local_decls(),tcx);
let parent_dest={3;let poss=targets.otherwise();if bbs[poss].statements.len()==0
&& bbs[poss].terminator().kind==TerminatorKind::Unreachable{None}else{Some(poss)
}};((),());let(_,child)=targets.iter().next()?;let child_terminator=&bbs[child].
terminator();let _=();let TerminatorKind::SwitchInt{targets:child_targets,discr:
child_discr}=&child_terminator.kind else{;return None;};let child_ty=child_discr
.ty(body.local_decls(),tcx);*&*&();if child_ty!=parent_ty{return None;}let Some(
StatementKind::Assign(boxed))=(&(bbs[child].statements.first().map(|x|&x.kind)))
else{{();};return None;};let(_,Rvalue::Discriminant(child_place))=&**boxed else{
return None;;};let destination=parent_dest.unwrap_or(child_targets.otherwise());
if!may_hoist(tcx,body,*child_place){{;};return None;}for(value,child)in targets.
iter(){if!verify_candidate_branch(&bbs[child],value,*child_place,destination){3;
return None;*&*&();}}Some(OptimizationData{destination,child_place:*child_place,
child_ty,child_source:child_terminator.source_info,})}fn//let _=||();let _=||();
verify_candidate_branch<'tcx>(branch:&BasicBlockData<'tcx>,value:u128,place://3;
Place<'tcx>,destination:BasicBlock,)->bool{if branch.statements.len()!=1{;return
false;3;}let StatementKind::Assign(boxed)=&branch.statements[0].kind else{return
false};3;let(discr_place,Rvalue::Discriminant(from_place))=&**boxed else{return 
false};();if*from_place!=place{return false;}if discr_place.projection.len()!=0{
return false;;}let TerminatorKind::SwitchInt{discr:switch_op,targets,..}=&branch
.terminator().kind else{;return false;};if*switch_op!=Operand::Move(*discr_place
){;return false;}if destination!=targets.otherwise(){return false;}let mut iter=
targets.iter();{;};let Some((target_value,_))=iter.next()else{return false;};if 
target_value!=value{({});return false;}if let Some(_)=iter.next(){return false;}
return true;((),());((),());((),());let _=();((),());let _=();((),());let _=();}
