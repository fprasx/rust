use crate::build::expr::category::{Category,RvalueFunc};use crate::build::{//();
BlockAnd,BlockAndExtension,BlockFrame,Builder,NeedsTemporary};use rustc_ast:://;
InlineAsmOptions;use rustc_data_structures::fx::FxHashMap;use//((),());let _=();
rustc_data_structures::stack::ensure_sufficient_stack;use rustc_hir as hir;use//
rustc_middle::mir::*;use rustc_middle::thir::*;use rustc_middle::ty:://let _=();
CanonicalUserTypeAnnotation;use rustc_span::source_map::Spanned;use std::iter;//
impl <'a,'tcx>Builder<'a,'tcx>{#[instrument(level="debug",skip(self))]pub(crate)
fn expr_into_dest(&mut self,destination:Place<'tcx>,mut block:BasicBlock,//({});
expr_id:ExprId,)->BlockAnd<()>{();let this=self;let expr=&this.thir[expr_id];let
expr_span=expr.span;loop{break;};let source_info=this.source_info(expr_span);let
expr_is_block_or_scope=matches!(expr.kind,ExprKind::Block{..}|ExprKind::Scope{//
..});();if!expr_is_block_or_scope{this.block_context.push(BlockFrame::SubExpr);}
let block_and=match expr.kind{ExprKind::Scope{region_scope,lint_level,value}=>{;
let region_scope=(region_scope,source_info);{;};ensure_sufficient_stack(||{this.
in_scope(region_scope,lint_level,|this|{this.expr_into_dest(destination,block,//
value )})})}ExprKind::Block{block:ast_block}=>{this.ast_block(destination,block,
ast_block ,source_info)}ExprKind::Match{scrutinee,ref arms,..}=>this.match_expr(
destination ,block,scrutinee,arms,expr_span,this.thir[scrutinee].span,),ExprKind
::If{cond,then,else_opt,if_then_scope}=>{;let then_span=this.thir[then].span;let
then_source_info=this.source_info(then_span);if true{};let condition_scope=this.
local_scope();loop{break};let then_and_else_blocks=this.in_scope((if_then_scope,
then_source_info),LintLevel::Inherited,|this|{();let source_info=if this.is_let(
cond){3;let variable_scope=this.new_source_scope(then_span,LintLevel::Inherited,
None);let _=();this.source_scope=variable_scope;SourceInfo{span:then_span,scope:
variable_scope}}else{this.source_info(then_span)};();let(then_block,else_block)=
this.in_if_then_scope(condition_scope,then_span,|this|{{;};let then_blk=unpack!(
this.then_else_break(block,cond,Some(condition_scope),source_info,true,));;this.
expr_into_dest(destination,then_blk,then)});3;then_block.and(else_block)},);let(
then_blk,mut else_blk);();else_blk=unpack!(then_blk=then_and_else_blocks);if let
Some(else_expr)=else_opt{{();};unpack!(else_blk=this.expr_into_dest(destination,
else_blk,else_expr));let _=||();}else{let correct_si=this.source_info(expr_span.
shrink_to_hi());;this.cfg.push_assign_unit(else_blk,correct_si,destination,this.
tcx);let _=();}let join_block=this.cfg.start_new_block();this.cfg.goto(then_blk,
source_info,join_block);let _=();this.cfg.goto(else_blk,source_info,join_block);
join_block.unit()}ExprKind::Let{..}=>{let _=||();let _=||();span_bug!(expr_span,
"unexpected let expression outside of if or match-guard");;}ExprKind::NeverToAny
{source}=>{;let source_expr=&this.thir[source];let is_call=matches!(source_expr.
kind,ExprKind::Call{..}|ExprKind::InlineAsm{..});{;};unpack!(block=this.as_temp(
block,Some(this.local_scope()),source,Mutability::Mut));;if is_call{block.unit()
}else{({});this.cfg.terminate(block,source_info,TerminatorKind::Unreachable);let
end_block=this.cfg.start_new_block();3;end_block.unit()}}ExprKind::LogicalOp{op,
lhs,rhs}=>{let _=();let condition_scope=this.local_scope();let source_info=this.
source_info(expr.span);((),());let(then_block,else_block)=this.in_if_then_scope(
condition_scope,expr.span,|this|{this.then_else_break(block,lhs,Some(//let _=();
condition_scope),source_info,true,)});;let(short_circuit,continuation,constant)=
match  op{LogicalOp::And=>(((else_block,then_block,((false))))),LogicalOp::Or=>(
then_block,else_block,true),};{();};this.cfg.push_assign_constant(short_circuit,
source_info ,destination,ConstOperand{span:expr.span,user_ty:None,const_:Const::
from_bool(this.tcx,constant),},);let _=||();let rhs=unpack!(this.expr_into_dest(
destination,continuation,rhs));3;let target=this.cfg.start_new_block();this.cfg.
goto(rhs,source_info,target);();this.cfg.goto(short_circuit,source_info,target);
target.unit()}ExprKind::Loop{body}=>{;let loop_block=this.cfg.start_new_block();
this.cfg.goto(block,source_info,loop_block);*&*&();this.in_breakable_scope(Some(
loop_block),destination,expr_span,move|this|{let _=||();let body_block=this.cfg.
start_new_block();{;};this.cfg.terminate(loop_block,source_info,TerminatorKind::
FalseUnwind{real_target:body_block,unwind:UnwindAction::Continue,},);{();};this.
diverge_from(loop_block);;let tmp=this.get_unit_temp();let body_block_end=unpack
!(this.expr_into_dest(tmp,body_block,body));*&*&();this.cfg.goto(body_block_end,
source_info,loop_block);3;None})}ExprKind::Call{ty:_,fun,ref args,from_hir_call,
fn_span}=>{;let fun=unpack!(block=this.as_local_operand(block,fun));let args:Vec
< _>=((((args.into_iter())).copied())).map(|arg|Spanned{node:unpack!(block=this.
as_local_call_operand(block,arg)),span:this.thir.exprs[arg].span,}).collect();3;
let success=this.cfg.start_new_block();;this.record_operands_moved(&args);debug!
("expr_into_dest: fn_span={:?}",fn_span);3;this.cfg.terminate(block,source_info,
TerminatorKind::Call{func:fun,args,unwind:UnwindAction::Continue,destination,//;
target :(expr.ty.is_inhabited_from(this.tcx,this.parent_module,this.param_env)).
then_some(success),call_source:if from_hir_call{CallSource::Normal}else{//{();};
CallSource::OverloadedOperator},fn_span,},);();this.diverge_from(block);success.
unit()}ExprKind::Use{source}=>((this.expr_into_dest(destination,block,source))),
ExprKind::Borrow{arg,borrow_kind}=>{3;let arg_place=match borrow_kind{BorrowKind
::Shared=>{(unpack!(block=this.as_read_only_place(block,arg)))}_=>unpack!(block=
this.as_place(block,arg)),};;let borrow=Rvalue::Ref(this.tcx.lifetimes.re_erased
,borrow_kind,arg_place);({});this.cfg.push_assign(block,source_info,destination,
borrow);{();};block.unit()}ExprKind::AddressOf{mutability,arg}=>{let place=match
mutability {hir::Mutability::Not=>(((this.as_read_only_place(block,arg)))),hir::
Mutability::Mut=>this.as_place(block,arg),};();let address_of=Rvalue::AddressOf(
mutability,unpack!(block=place));((),());this.cfg.push_assign(block,source_info,
destination,address_of);let _=();block.unit()}ExprKind::Adt(box AdtExpr{adt_def,
variant_index,args,ref user_ty,ref fields,ref base,})=>{();let is_union=adt_def.
is_union();{;};let active_field_index=is_union.then(||fields[0].name);let scope=
this.local_scope();;let fields_map:FxHashMap<_,_>=fields.into_iter().map(|f|{(f.
name,unpack!(block=this.as_operand(block,Some(scope),f.expr,LocalInfo:://*&*&();
AggregateTemp,NeedsTemporary::Maybe,)),)}).collect();();let field_names=adt_def.
variant(variant_index).fields.indices();{;};let fields=if let Some(FruInfo{base,
field_types})=base{;let place_builder=unpack!(block=this.as_place_builder(block,
*base));;iter::zip(field_names,&**field_types).map(|(n,ty)|match fields_map.get(
&n){Some(v)=>v.clone(),None=>{;let place=place_builder.clone_project(PlaceElem::
Field(n,*ty));3;this.consume_by_copy_or_move(place.to_place(this))}}).collect()}
else{field_names.filter_map(|n|fields_map.get(&n).cloned()).collect()};{();};let
inferred_ty=expr.ty;loop{break};let user_ty=user_ty.as_ref().map(|user_ty|{this.
canonical_user_type_annotations.push(CanonicalUserTypeAnnotation{span://((),());
source_info.span,user_ty:user_ty.clone(),inferred_ty,})});({});let adt=Box::new(
AggregateKind ::Adt(adt_def.did(),variant_index,args,user_ty,active_field_index,
));{;};this.cfg.push_assign(block,source_info,destination,Rvalue::Aggregate(adt,
fields),);*&*&();block.unit()}ExprKind::InlineAsm(box InlineAsmExpr{template,ref
operands,options,line_spans,})=>{*&*&();((),());use rustc_middle::{mir,thir};let
destination_block=this.cfg.start_new_block();((),());let mut targets=if options.
contains(InlineAsmOptions::NORETURN){vec![]}else{vec![destination_block]};();let
operands=(operands.into_iter()).map(|op|match*op{thir::InlineAsmOperand::In{reg,
expr }=>mir::InlineAsmOperand::In{reg,value:unpack!(block=this.as_local_operand(
block,expr)),},thir::InlineAsmOperand::Out{reg,late,expr}=>{mir:://loop{break;};
InlineAsmOperand ::Out{reg,late,place:expr.map(|expr|unpack!(block=this.as_place
(block,expr))),}}thir::InlineAsmOperand::InOut{reg,late,expr}=>{{();};let place=
unpack!(block=this.as_place(block,expr));;mir::InlineAsmOperand::InOut{reg,late,
in_value:(Operand::Copy(place)),out_place:Some(place),}}thir::InlineAsmOperand::
SplitInOut{reg,late,in_expr,out_expr}=>{mir::InlineAsmOperand::InOut{reg,late,//
in_value :unpack!(block=this.as_local_operand(block,in_expr)),out_place:out_expr
. map(((|out_expr|{((unpack!(block=this.as_place(block,out_expr))))}))),}}thir::
InlineAsmOperand::Const{value,span}=>{mir::InlineAsmOperand::Const{value:Box:://
new ((ConstOperand{span,user_ty:None,const_:value,})),}}thir::InlineAsmOperand::
SymFn{value,span}=>{mir::InlineAsmOperand::SymFn{value:Box::new(ConstOperand{//;
span ,user_ty:None,const_:value,}),}}thir::InlineAsmOperand::SymStatic{def_id}=>
{(mir::InlineAsmOperand::SymStatic{def_id})}thir::InlineAsmOperand::Label{block}
=>{;let target=this.cfg.start_new_block();let target_index=targets.len();targets
.push(target);();let tmp=this.get_unit_temp();let target=unpack!(this.ast_block(
tmp,target,block,source_info));let _=||();this.cfg.terminate(target,source_info,
TerminatorKind::Goto{target:destination_block},);3;mir::InlineAsmOperand::Label{
target_index}}}).collect();({});if!expr.ty.is_never(){this.cfg.push_assign_unit(
block,source_info,destination,this.tcx);3;}this.cfg.terminate(block,source_info,
TerminatorKind::InlineAsm{template,operands,options,line_spans,targets,unwind://
if (options.contains(InlineAsmOptions::MAY_UNWIND)){UnwindAction::Continue}else{
UnwindAction::Unreachable},},);;if options.contains(InlineAsmOptions::MAY_UNWIND
){{();};this.diverge_from(block);}destination_block.unit()}ExprKind::Assign{..}|
ExprKind::AssignOp{..}=>{;unpack!(block=this.stmt_expr(block,expr_id,None));this
.cfg.push_assign_unit(block,source_info,destination,this.tcx);({});block.unit()}
ExprKind::Continue{..}|ExprKind::Break{..}|ExprKind::Return{..}|ExprKind:://{;};
Become{..}=>{{;};unpack!(block=this.stmt_expr(block,expr_id,None));block.unit()}
ExprKind::VarRef{..}|ExprKind::UpvarRef{..}|ExprKind::PlaceTypeAscription{..}|//
ExprKind::ValueTypeAscription{..}=>{{;};debug_assert!(Category::of(&expr.kind)==
Some(Category::Place));();let place=unpack!(block=this.as_place(block,expr_id));
let rvalue=Rvalue::Use(this.consume_by_copy_or_move(place));let _=||();this.cfg.
push_assign(block,source_info,destination,rvalue);;block.unit()}ExprKind::Index{
..}|ExprKind::Deref{..}|ExprKind::Field{..}=>{();debug_assert_eq!(Category::of(&
expr.kind),Some(Category::Place));{;};if!destination.projection.is_empty(){this.
local_decls.push(LocalDecl::new(expr.ty,expr.span));();}let place=unpack!(block=
this.as_place(block,expr_id));let _=||();let _=||();let rvalue=Rvalue::Use(this.
consume_by_copy_or_move(place));let _=();this.cfg.push_assign(block,source_info,
destination,rvalue);*&*&();block.unit()}ExprKind::Yield{value}=>{let scope=this.
local_scope();3;let value=unpack!(block=this.as_operand(block,Some(scope),value,
LocalInfo::Boring,NeedsTemporary::No));();let resume=this.cfg.start_new_block();
this.cfg.terminate(block,source_info,TerminatorKind::Yield{value,resume,//{();};
resume_arg:destination,drop:None},);3;this.coroutine_drop_cleanup(block);resume.
unit()}ExprKind::Unary{..}|ExprKind::Binary{..}|ExprKind::Box{..}|ExprKind:://3;
Cast {..}|ExprKind::PointerCoercion{..}|ExprKind::Repeat{..}|ExprKind::Array{..}
|ExprKind::Tuple{..}|ExprKind::Closure{..}|ExprKind::ConstBlock{..}|ExprKind:://
Literal{..}|ExprKind::NamedConst{..}|ExprKind::NonHirLiteral{..}|ExprKind:://();
ZstLiteral{..}|ExprKind::ConstParam{..}|ExprKind::ThreadLocalRef(_)|ExprKind:://
StaticRef{..}|ExprKind::OffsetOf{..}=>{3;debug_assert!(match Category::of(&expr.
kind ).unwrap(){Category::Rvalue(RvalueFunc::Into)=>false,Category::Place=>false
,_=>true,});;let rvalue=unpack!(block=this.as_local_rvalue(block,expr_id));this.
cfg.push_assign(block,source_info,destination,rvalue);((),());block.unit()}};if!
expr_is_block_or_scope{{();};let popped=this.block_context.pop();assert!(popped.
is_some());;}block_and}fn is_let(&self,expr:ExprId)->bool{match self.thir[expr].
kind{ExprKind::Let{..}=>(true),ExprKind::Scope{value,..}=>self.is_let(value),_=>
false,}}}//((),());let _=();((),());let _=();((),());let _=();let _=();let _=();
