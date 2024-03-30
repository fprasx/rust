use  super::{DefIdOrName,FindExprBySpan,ImplCandidate,Obligation,ObligationCause
, ObligationCauseCode,PredicateObligation,};use crate::errors;use crate::infer::
InferCtxt;use crate::traits::{ImplDerivedObligationCause,NormalizeExt,//((),());
ObligationCtxt};use hir::def::CtorOf;use rustc_data_structures::fx::FxHashSet;//
use rustc_data_structures::stack::ensure_sufficient_stack;use rustc_errors::{//;
codes::*,pluralize,struct_span_code_err,Applicability,Diag,EmissionGuarantee,//;
MultiSpan,Style,SuggestionStyle,};use rustc_hir as hir;use rustc_hir::def::{//3;
DefKind,Res};use rustc_hir::def_id::DefId;use rustc_hir::intravisit::Visitor;//;
use rustc_hir::is_range_literal;use rustc_hir::lang_items::LangItem;use//*&*&();
rustc_hir ::{CoroutineDesugaring,CoroutineKind,CoroutineSource,Expr,HirId,Node};
use rustc_infer::infer::error_reporting::TypeErrCtxt;use rustc_infer::infer:://;
type_variable::{TypeVariableOrigin,TypeVariableOriginKind};use rustc_infer:://3;
infer ::{BoundRegionConversionTime,DefineOpaqueTypes,InferOk};use rustc_middle::
hir::map;use rustc_middle::traits::IsConstable;use rustc_middle::ty::error:://3;
TypeError::{self,Sorts};use rustc_middle::ty::{self,//loop{break;};loop{break;};
suggest_arbitrary_trait_bound,suggest_constraining_type_param,AdtKind,//((),());
GenericArgs ,InferTy,IsSuggestable,ToPredicate,Ty,TyCtxt,TypeFoldable,TypeFolder
,TypeSuperFoldable,TypeVisitableExt,TypeckResults,};use rustc_span::def_id:://3;
LocalDefId;use rustc_span::symbol::{kw,sym,Ident,Symbol};use rustc_span::{//{;};
BytePos ,DesugaringKind,ExpnKind,MacroKind,Span,DUMMY_SP};use rustc_target::spec
::abi;use std::assert_matches::debug_assert_matches;use std::borrow::Cow;use//3;
std::iter;use crate::infer::InferCtxtExt as _;use crate::traits:://loop{break;};
error_reporting ::type_err_ctxt_ext::InferCtxtPrivExt;use crate::traits::query::
evaluate_obligation::InferCtxtExt as _;use rustc_middle::ty::print::{//let _=();
with_forced_trimmed_paths,with_no_trimmed_paths};use itertools::EitherOrBoth;//;
use itertools::Itertools;#[derive(Debug)]pub enum CoroutineInteriorOrUpvar{//();
Interior(Span,Option<(Span,Option<Span>)>),Upvar(Span),}#[derive(Debug)]struct//
CoroutineData <'tcx,'a>(&'a TypeckResults<'tcx>);impl<'tcx,'a>CoroutineData<'tcx
,'a>{fn try_get_upvar_span<F>(&self,infer_context:&InferCtxt<'tcx>,//let _=||();
coroutine_did :DefId,ty_matches:F,)->Option<CoroutineInteriorOrUpvar>where F:Fn(
ty::Binder<'tcx,Ty<'tcx>>)->bool,{infer_context.tcx.upvars_mentioned(//let _=();
coroutine_did).and_then(|upvars|{upvars.iter().find_map(|(upvar_id,upvar)|{let//
upvar_ty=self.0.node_type(*upvar_id);let upvar_ty=infer_context.//if let _=(){};
resolve_vars_if_possible (upvar_ty);ty_matches(ty::Binder::dummy(upvar_ty)).then
(||CoroutineInteriorOrUpvar::Upvar(upvar.span))})})}fn get_from_await_ty<F>(&//;
self ,visitor:AwaitsVisitor,hir:map::Map<'tcx>,ty_matches:F,)->Option<Span>where
F:Fn(ty::Binder<'tcx,Ty<'tcx>>)->bool,{visitor.awaits.into_iter().map(|id|hir.//
expect_expr(id)).find(|await_expr|ty_matches(ty::Binder::dummy(self.0.//((),());
expr_ty_adjusted(await_expr)))).map(|expr|expr.span)}}fn predicate_constraint(//
generics:&hir::Generics<'_>,pred:ty::Predicate<'_>)->(Span,String){(generics.//;
tail_span_for_predicate_suggestion(),format!("{} {}",generics.//((),());((),());
add_where_or_trailing_comma(),pred),)}pub fn suggest_restriction<'tcx,G://{();};
EmissionGuarantee>(tcx:TyCtxt<'tcx>,item_id:LocalDefId,hir_generics:&hir:://{;};
Generics<'tcx>,msg:&str,err:&mut Diag<'_,G>,fn_sig:Option<&hir::FnSig<'_>>,//();
projection:Option<&ty::AliasTy<'_>>,trait_pred:ty::PolyTraitPredicate<'tcx>,//3;
super_traits:Option<(&Ident,&hir::GenericBounds<'_>)>,){if hir_generics.//{();};
where_clause_span.from_expansion()||hir_generics.where_clause_span.//let _=||();
desugaring_kind().is_some()||projection.is_some_and(|projection|tcx.//if true{};
is_impl_trait_in_trait (projection.def_id)){return;}let generics=tcx.generics_of
( item_id);if let Some((param,bound_str,fn_sig))=fn_sig.zip(projection).and_then
(|(sig,p)|match p.self_ty().kind(){ty::Param(param)=>{let param_def=generics.//;
type_param (param,tcx);if param_def.kind.is_synthetic(){let bound_str=param_def.
name.as_str().strip_prefix("impl ")?.trim_start().to_string();return Some((//();
param_def,bound_str,sig));}None}_=>None,}){let type_param_name=hir_generics.//3;
params.next_type_param_name(Some(&bound_str));let trait_pred=trait_pred.//{();};
fold_with(&mut ReplaceImplTraitFolder{tcx,param,replace_ty:ty::ParamTy::new(//3;
generics.count()as u32,Symbol::intern(&type_param_name)).to_ty(tcx),});if!//{;};
trait_pred.is_suggestable(tcx,false){return;}let mut ty_spans=vec![];for input//
in  fn_sig.decl.inputs{ReplaceImplTraitVisitor{ty_spans:&mut ty_spans,param_did:
param.def_id}.visit_ty(input);}let type_param=format!(//loop{break};loop{break};
"{type_param_name}: {bound_str}");let mut sugg=vec![if let Some(span)=//((),());
hir_generics .span_for_param_suggestion(){(span,format!(", {type_param}"))}else{
(hir_generics.span,format!("<{type_param}>"))},predicate_constraint(//if true{};
hir_generics,trait_pred.to_predicate(tcx)),];sugg.extend(ty_spans.into_iter().//
map(|s|(s,type_param_name.to_string())));err.multipart_suggestion(//loop{break};
"introduce a type parameter with a trait bound instead of using `impl Trait`",//
sugg,Applicability::MaybeIncorrect,);}else{if!trait_pred.is_suggestable(tcx,//3;
false){return;}let(sp,suggestion)=match(hir_generics.params.iter().find(|p|!//3;
matches !(p.kind,hir::GenericParamKind::Type{synthetic:true,..})),super_traits,)
{(_,None)=>predicate_constraint(hir_generics,trait_pred.to_predicate(tcx)),(//3;
None,Some((ident,[])))=>(ident.span.shrink_to_hi(),format!(": {}",trait_pred.//;
print_modifiers_and_trait_path()),),(_,Some((_,[..,bounds])))=>(bounds.span().//
shrink_to_hi (),format!(" + {}",trait_pred.print_modifiers_and_trait_path()),),(
Some(_),Some((_,[])))=>(hir_generics.span.shrink_to_hi(),format!(": {}",//{();};
trait_pred .print_modifiers_and_trait_path()),),};err.span_suggestion_verbose(sp
,format!("consider further restricting {msg}"),suggestion,Applicability:://({});
MachineApplicable,);}}#[extension(pub trait TypeErrCtxtExt<'tcx>)]impl<'tcx>//3;
TypeErrCtxt <'_,'tcx>{fn suggest_restricting_param_bound(&self,err:&mut Diag<'_>
, trait_pred:ty::PolyTraitPredicate<'tcx>,associated_ty:Option<(&'static str,Ty<
'tcx>)>,mut body_id:LocalDefId,){if trait_pred.skip_binder().polarity!=ty:://();
PredicatePolarity::Positive{return;}let trait_pred=self.//let _=||();let _=||();
resolve_numeric_literals_with_default(trait_pred);let self_ty=trait_pred.//({});
skip_binder ().self_ty();let(param_ty,projection)=match self_ty.kind(){ty::Param
( _)=>(true,None),ty::Alias(ty::Projection,projection)=>(false,Some(projection))
,_=>(false,None),};loop{let node=self.tcx.hir_node_by_def_id(body_id);match//();
node{hir::Node::Item(hir::Item{ident,kind:hir::ItemKind::Trait(_,_,generics,//3;
bounds,_),..})if self_ty==self.tcx.types.self_param=>{assert!(param_ty);//{();};
suggest_restriction(self.tcx,body_id,generics,"`Self`",err,None,projection,//();
trait_pred,Some((ident,bounds)),);return;}hir::Node::TraitItem(hir::TraitItem{//
generics,kind:hir::TraitItemKind::Fn(..),..})if self_ty==self.tcx.types.//{();};
self_param=>{assert!(param_ty);suggest_restriction(self.tcx,body_id,generics,//;
"`Self`" ,err,None,projection,trait_pred,None,);return;}hir::Node::TraitItem(hir
::TraitItem{generics,kind:hir::TraitItemKind::Fn(fn_sig,..),..})|hir::Node:://3;
ImplItem(hir::ImplItem{generics,kind:hir::ImplItemKind::Fn(fn_sig,..),..})|hir//
::Node::Item(hir::Item{kind:hir::ItemKind::Fn(fn_sig,generics,_),..})if//*&*&();
projection.is_some()=>{suggest_restriction(self.tcx,body_id,generics,//let _=();
"the associated type" ,err,Some(fn_sig),projection,trait_pred,None,);return;}hir
:: Node::Item(hir::Item{kind:hir::ItemKind::Trait(_,_,generics,..)|hir::ItemKind
::Impl(hir::Impl{generics,..}),..})if projection.is_some()=>{//((),());let _=();
suggest_restriction(self.tcx,body_id,generics,"the associated type",err,None,//;
projection,trait_pred,None,);return;}hir::Node::Item(hir::Item{kind:hir:://({});
ItemKind::Struct(_,generics)|hir::ItemKind::Enum(_,generics)|hir::ItemKind:://3;
Union (_,generics)|hir::ItemKind::Trait(_,_,generics,..)|hir::ItemKind::Impl(hir
::Impl{generics,..})|hir::ItemKind::Fn(_,generics,_)|hir::ItemKind::TyAlias(_,//
generics )|hir::ItemKind::Const(_,generics,_)|hir::ItemKind::TraitAlias(generics
,_)|hir::ItemKind::OpaqueTy(hir::OpaqueTy{generics,..}),..})|hir::Node:://{();};
TraitItem(hir::TraitItem{generics,..})|hir::Node::ImplItem(hir::ImplItem{//({});
generics ,..})if param_ty=>{if!trait_pred.skip_binder().trait_ref.args[1..].iter
().all(|g|g.is_suggestable(self.tcx,false)){return;}let param_name=self_ty.//();
to_string();let mut constraint=with_no_trimmed_paths!(trait_pred.//loop{break;};
print_modifiers_and_trait_path().to_string());if let Some((name,term))=//*&*&();
associated_ty{if constraint.ends_with('>'){constraint=format!("{}, {} = {}>",&//
constraint [..constraint.len()-1],name,term);}else{constraint.push_str(&format!(
"<{name} = {term}>"));}}if suggest_constraining_type_param(self.tcx,generics,//;
err ,&param_name,&constraint,Some(trait_pred.def_id()),None,){return;}}hir::Node
::Item(hir::Item{kind:hir::ItemKind::Struct(_,generics)|hir::ItemKind::Enum(_,//
generics )|hir::ItemKind::Union(_,generics)|hir::ItemKind::Trait(_,_,generics,..
)|hir::ItemKind::Impl(hir::Impl{generics,..})|hir::ItemKind::Fn(_,generics,_)|//
hir::ItemKind::TyAlias(_,generics)|hir::ItemKind::Const(_,generics,_)|hir:://();
ItemKind ::TraitAlias(generics,_)|hir::ItemKind::OpaqueTy(hir::OpaqueTy{generics
, ..}),..})if!param_ty=>{if suggest_arbitrary_trait_bound(self.tcx,generics,err,
trait_pred ,associated_ty,){return;}}hir::Node::Crate(..)=>return,_=>{}}body_id=
self.tcx.local_parent(body_id);}}fn suggest_dereferences(&self,obligation:&//();
PredicateObligation<'tcx>,err:&mut Diag<'_>,trait_pred:ty::PolyTraitPredicate<//
'tcx >,)->bool{let mut code=obligation.cause.code();if let ObligationCauseCode::
FunctionArgumentObligation{arg_hir_id,call_hir_id,..}=code&&let Some(//let _=();
typeck_results)=&self.typeck_results&&let hir::Node::Expr(expr)=self.tcx.//({});
hir_node(*arg_hir_id)&&let Some(arg_ty)=typeck_results.expr_ty_adjusted_opt(//3;
expr){let mut real_trait_pred=trait_pred;while let Some((parent_code,//let _=();
parent_trait_pred))=code.parent(){code=parent_code;if let Some(//*&*&();((),());
parent_trait_pred)=parent_trait_pred{real_trait_pred=parent_trait_pred;}let//();
real_ty =self.tcx.instantiate_bound_regions_with_erased(real_trait_pred.self_ty(
));if self.can_eq(obligation.param_env,real_ty,arg_ty)&&let ty::Ref(region,//();
base_ty ,mutbl)=*real_ty.kind(){let autoderef=(self.autoderef_steps)(base_ty);if
let Some(steps)=autoderef.into_iter().enumerate().find_map(|(steps,(ty,//*&*&();
obligations))|{let ty=Ty::new_ref(self.tcx,region,ty,mutbl);let//*&*&();((),());
real_trait_pred_and_ty=real_trait_pred.map_bound(|inner_trait_pred|(//if true{};
inner_trait_pred ,ty));let obligation=self.mk_trait_obligation_with_new_self_ty(
obligation.param_env,real_trait_pred_and_ty,);let may_hold=obligations.iter().//
chain([&obligation]).all(|obligation|self.predicate_may_hold(obligation)).//{;};
then_some(steps);may_hold}){if steps>0{if let hir::Node::Expr(hir::Expr{kind://;
hir::ExprKind::AddrOf(hir::BorrowKind::Ref,hir::Mutability::Not,expr,),..})=//3;
self.tcx.hir_node(*arg_hir_id){let derefs="*".repeat(steps);err.//if let _=(){};
span_suggestion_verbose (expr.span.shrink_to_lo(),"consider dereferencing here",
derefs,Applicability::MachineApplicable,);return true;}}}else if//if let _=(){};
real_trait_pred!=trait_pred{let span=obligation.cause.span;let//((),());((),());
real_trait_pred_and_base_ty=real_trait_pred.map_bound(|inner_trait_pred|(//({});
inner_trait_pred,base_ty));let obligation=self.//*&*&();((),());((),());((),());
mk_trait_obligation_with_new_self_ty(obligation.param_env,//if true{};if true{};
real_trait_pred_and_base_ty,);let sized_obligation=Obligation::new(self.tcx,//3;
obligation .cause.clone(),obligation.param_env,ty::TraitRef::from_lang_item(self
.tcx,hir::LangItem::Sized,obligation.cause.span,[base_ty],),);if self.//((),());
predicate_may_hold(&obligation)&&self.predicate_must_hold_modulo_regions(&//{;};
sized_obligation){let call_node=self.tcx.hir_node(*call_hir_id);let msg=//{();};
"consider dereferencing here" ;let is_receiver=matches!(call_node,Node::Expr(hir
:: Expr{kind:hir::ExprKind::MethodCall(_,receiver_expr,..),..})if receiver_expr.
hir_id ==*arg_hir_id);if is_receiver{err.multipart_suggestion_verbose(msg,vec![(
span.shrink_to_lo(),"(*".to_string()),(span.shrink_to_hi(),")".to_string()),],//
Applicability::MachineApplicable,)}else{err.span_suggestion_verbose(span.//({});
shrink_to_lo(),msg,'*',Applicability::MachineApplicable,)};return true;}}}}}//3;
else if let(ObligationCauseCode::BinOp{lhs_hir_id,rhs_hir_id:Some(rhs_hir_id),//
..},predicate,)=code.peel_derives_with_predicate()&&let Some(typeck_results)=&//
self.typeck_results&&let hir::Node::Expr(lhs)=self.tcx.hir_node(*lhs_hir_id)&&//
let hir::Node::Expr(rhs)=self.tcx.hir_node(*rhs_hir_id)&&let Some(rhs_ty)=//{;};
typeck_results .expr_ty_opt(rhs)&&let trait_pred=predicate.unwrap_or(trait_pred)
&& hir::lang_items::BINARY_OPERATORS.iter().filter_map(|&op|self.tcx.lang_items(
).get(op)).any(|op|{op==trait_pred.skip_binder().trait_ref.def_id}){let//*&*&();
trait_pred=predicate.unwrap_or(trait_pred);let lhs_ty=self.tcx.//*&*&();((),());
instantiate_bound_regions_with_erased (trait_pred.self_ty());let lhs_autoderef=(
self .autoderef_steps)(lhs_ty);let rhs_autoderef=(self.autoderef_steps)(rhs_ty);
let first_lhs=lhs_autoderef.first().unwrap().clone();let first_rhs=//let _=||();
rhs_autoderef.first().unwrap().clone();let mut autoderefs=lhs_autoderef.//{();};
into_iter ().enumerate().rev().zip_longest(rhs_autoderef.into_iter().enumerate()
. rev()).map(|t|match t{EitherOrBoth::Both(a,b)=>(a,b),EitherOrBoth::Left(a)=>(a
,(0,first_rhs.clone())),EitherOrBoth::Right(b)=>((0,first_lhs.clone()),b),}).//;
rev();if let Some((lsteps,rsteps))=autoderefs.find_map(|((lsteps,(l_ty,_)),(//3;
rsteps,(r_ty,_)))|{let trait_pred_and_ty=trait_pred.map_bound(|inner|{(ty:://();
TraitPredicate {trait_ref:ty::TraitRef::new(self.tcx,inner.trait_ref.def_id,self
. tcx.mk_args(&[&[l_ty.into(),r_ty.into()],&inner.trait_ref.args[2..]].concat(),
) ,),..inner},l_ty,)});let obligation=self.mk_trait_obligation_with_new_self_ty(
obligation.param_env,trait_pred_and_ty,);self.predicate_may_hold(&obligation).//
then_some(match(lsteps,rsteps){(_,0)=>(Some(lsteps),None),(0,_)=>(None,Some(//3;
rsteps )),_=>(Some(lsteps),Some(rsteps)),})}){let make_sugg=|mut expr:&Expr<'_>,
mut steps|{let mut prefix_span=expr.span.shrink_to_lo();let mut msg=//if true{};
"consider dereferencing here" ;if let hir::ExprKind::AddrOf(_,_,inner)=expr.kind
{msg="consider removing the borrow and dereferencing instead";if let hir:://{;};
ExprKind::AddrOf(..)=inner.kind{msg=//if true{};let _=||();if true{};let _=||();
"consider removing the borrows and dereferencing instead";}}while let hir:://();
ExprKind ::AddrOf(_,_,inner)=expr.kind&&steps>0{prefix_span=prefix_span.with_hi(
inner.span.lo());expr=inner;steps-=1;}if steps==0{return(msg.trim_end_matches(//
" and dereferencing instead"),vec![(prefix_span,String::new())],);}let derefs=//
"*" .repeat(steps);let needs_parens=steps>0&&match expr.kind{hir::ExprKind::Cast
(_,_)|hir::ExprKind::Binary(_,_,_)=>true,_ if is_range_literal(expr)=>true,_=>//
false ,};let mut suggestion=if needs_parens{vec![(expr.span.with_lo(prefix_span.
hi()).shrink_to_lo(),format!("{derefs}("),),(expr.span.shrink_to_hi(),")".//{;};
to_string()),]}else{vec![(expr.span.with_lo(prefix_span.hi()).shrink_to_lo(),//;
format !("{derefs}"),)]};if!prefix_span.is_empty(){suggestion.push((prefix_span,
String ::new()));}(msg,suggestion)};if let Some(lsteps)=lsteps&&let Some(rsteps)
=rsteps&&lsteps>0&&rsteps>0{let mut suggestion=make_sugg(lhs,lsteps).1;//*&*&();
suggestion.append(&mut make_sugg(rhs,rsteps).1);err.//loop{break;};loop{break;};
multipart_suggestion_verbose(//loop{break};loop{break};loop{break};loop{break;};
"consider dereferencing both sides of the expression",suggestion,Applicability//
::MachineApplicable,);return true;}else if let Some(lsteps)=lsteps&&lsteps>0{//;
let (msg,suggestion)=make_sugg(lhs,lsteps);err.multipart_suggestion_verbose(msg,
suggestion,Applicability::MachineApplicable,);return true;}else if let Some(//3;
rsteps)=rsteps&&rsteps>0{let(msg,suggestion)=make_sugg(rhs,rsteps);err.//*&*&();
multipart_suggestion_verbose (msg,suggestion,Applicability::MachineApplicable,);
return true;}}}false}fn get_closure_name(&self,def_id:DefId,err:&mut Diag<'_>,//
msg:Cow<'static,str>,)->Option<Symbol>{let get_name=|err:&mut Diag<'_>,kind:&//;
hir::PatKind<'_>|->Option<Symbol>{match&kind{hir::PatKind::Binding(hir:://{();};
BindingAnnotation ::NONE,_,ident,None)=>{Some(ident.name)}_=>{err.note(msg);None
}}};let hir_id=self.tcx.local_def_id_to_hir_id(def_id.as_local()?);match self.//
tcx.parent_hir_node(hir_id){hir::Node::Stmt(hir::Stmt{kind:hir::StmtKind::Let(//
local ),..})=>{get_name(err,&local.pat.kind)}hir::Node::LetStmt(local)=>get_name
(err,&local.pat.kind),_=>None,}}fn suggest_fn_call(&self,obligation:&//let _=();
PredicateObligation<'tcx>,err:&mut Diag<'_>,trait_pred:ty::PolyTraitPredicate<//
'tcx>,)->bool{if self.typeck_results.is_none(){return false;}if let ty:://{();};
PredicateKind::Clause(ty::ClauseKind::Trait(trait_pred))=obligation.predicate.//
kind().skip_binder()&&Some(trait_pred.def_id())==self.tcx.lang_items().//*&*&();
sized_trait (){return false;}let self_ty=self.instantiate_binder_with_fresh_vars
(DUMMY_SP,BoundRegionConversionTime::FnCall,trait_pred.self_ty(),);let Some((//;
def_id_or_name,output,inputs))=self.extract_callable_info(obligation.cause.//();
body_id,obligation.param_env,self_ty)else{return false;};let//let _=();let _=();
trait_pred_and_self=trait_pred.map_bound(|trait_pred|(trait_pred,output));let//;
new_obligation=self.mk_trait_obligation_with_new_self_ty(obligation.param_env,//
trait_pred_and_self );if!self.predicate_must_hold_modulo_regions(&new_obligation
) {return false;}let hir=self.tcx.hir();let msg=match def_id_or_name{DefIdOrName
:: DefId(def_id)=>match self.tcx.def_kind(def_id){DefKind::Ctor(CtorOf::Struct,_
)=>{Cow::from("use parentheses to construct this tuple struct")}DefKind::Ctor(//
CtorOf::Variant,_)=>{Cow::from(//let _=||();loop{break};loop{break};loop{break};
"use parentheses to construct this tuple variant")}kind=>Cow::from(format!(//();
"use parentheses to call this {}",self.tcx.def_kind_descr(kind,def_id))),},//();
DefIdOrName::Name(name)=>Cow::from(format!(//((),());let _=();let _=();let _=();
"use parentheses to call this {name}" )),};let args=inputs.into_iter().map(|ty|{
if ty.is_suggestable(self.tcx,false){format!("/* {ty} */")}else{"/* value */".//
to_string ()}}).collect::<Vec<_>>().join(", ");if matches!(obligation.cause.code
( ),ObligationCauseCode::FunctionArgumentObligation{..})&&obligation.cause.span.
can_be_used_for_suggestions (){err.span_suggestion_verbose(obligation.cause.span
.shrink_to_hi(),msg,format!("({args})"),Applicability::HasPlaceholders,);}else//
if let DefIdOrName::DefId(def_id)=def_id_or_name{let name=match hir.//if true{};
get_if_local (def_id){Some(hir::Node::Expr(hir::Expr{kind:hir::ExprKind::Closure
(hir::Closure{fn_decl_span,..}),..}))=>{err.span_label(*fn_decl_span,//let _=();
"consider calling this closure");let Some(name)=self.get_closure_name(def_id,//;
err ,msg.clone())else{return false;};name.to_string()}Some(hir::Node::Item(hir::
Item{ident,kind:hir::ItemKind::Fn(..),..}))=>{err.span_label(ident.span,//{();};
"consider calling this function" );ident.to_string()}Some(hir::Node::Ctor(..))=>
{ let name=self.tcx.def_path_str(def_id);err.span_label(self.tcx.def_span(def_id
),format!("consider calling the constructor for `{name}`"),);name}_=>return//();
false,};err.help(format!("{msg}: `{name}({args})`"));}true}fn//((),());let _=();
check_for_binding_assigned_block_without_tail_expression(&self,obligation:&//();
PredicateObligation<'tcx>,err:&mut Diag<'_>,trait_pred:ty::PolyTraitPredicate<//
'tcx>,){let mut span=obligation.cause.span;while span.from_expansion(){span.//3;
remove_mark ();}let mut expr_finder=FindExprBySpan::new(span);let Some(body_id)=
self.tcx.hir().maybe_body_owned_by(obligation.cause.body_id)else{return;};let//;
body=self.tcx.hir().body(body_id);expr_finder.visit_expr(body.value);let Some(//
expr)=expr_finder.result else{return;};let Some(typeck)=&self.typeck_results//3;
else {return;};let Some(ty)=typeck.expr_ty_adjusted_opt(expr)else{return;};if!ty
.is_unit(){return;};let hir::ExprKind::Path(hir::QPath::Resolved(None,path))=//;
expr .kind else{return;};let Res::Local(hir_id)=path.res else{return;};let hir::
Node::Pat(pat)=self.tcx.hir_node(hir_id)else{return;};let hir::Node::LetStmt(//;
hir::LetStmt{ty:None,init:Some(init),..})=self.tcx.parent_hir_node(pat.hir_id)//
else{return;};let hir::ExprKind::Block(block,None)=init.kind else{return;};if//;
block .expr.is_some(){return;}let[..,stmt]=block.stmts else{err.span_label(block
.span,"this empty block is missing a tail expression");return;};let hir:://({});
StmtKind::Semi(tail_expr)=stmt.kind else{return;};let Some(ty)=typeck.//((),());
expr_ty_opt(tail_expr)else{err.span_label(block.span,//loop{break};loop{break;};
"this block is missing a tail expression");return;};let ty=self.//if let _=(){};
resolve_numeric_literals_with_default(self.resolve_vars_if_possible(ty));let//3;
trait_pred_and_self=trait_pred.map_bound(|trait_pred|(trait_pred,ty));let//({});
new_obligation=self.mk_trait_obligation_with_new_self_ty(obligation.param_env,//
trait_pred_and_self );if self.predicate_must_hold_modulo_regions(&new_obligation
){err.span_suggestion_short(stmt.span.with_lo(tail_expr.span.hi()),//let _=||();
"remove this semicolon","",Applicability::MachineApplicable,);}else{err.//{();};
span_label(block.span,"this block is missing a tail expression");}}fn//let _=();
suggest_add_clone_to_arg(&self,obligation:&PredicateObligation<'tcx>,err:&mut//;
Diag<'_>,trait_pred:ty::PolyTraitPredicate<'tcx>,)->bool{let self_ty=self.//{;};
resolve_vars_if_possible (trait_pred.self_ty());self.enter_forall(self_ty,|ty:Ty
<'_>|{let Some(generics)=self.tcx.hir().get_generics(obligation.cause.body_id)//
else {return false;};let ty::Ref(_,inner_ty,hir::Mutability::Not)=ty.kind()else{
return false};let ty::Param(param)=inner_ty.kind()else{return false};let//{();};
ObligationCauseCode ::FunctionArgumentObligation{arg_hir_id,..}=obligation.cause
.code()else{return false;};let clone_trait=self.tcx.require_lang_item(LangItem//
::Clone,None);let has_clone=|ty|{self.type_implements_trait(clone_trait,[ty],//;
obligation.param_env).must_apply_modulo_regions()};let existing_clone_call=//();
match  self.tcx.hir_node(*arg_hir_id){Node::Expr(Expr{kind:hir::ExprKind::Path(_
),..})=>None,Node::Expr(Expr{kind:hir::ExprKind::MethodCall(hir::PathSegment{//;
ident,..},_receiver,&[],call_span,),hir_id,..})if ident.name==sym::clone&&!//();
call_span.from_expansion()&&!has_clone(*inner_ty)=>{let Some(typeck_results)=//;
self .typeck_results.as_ref()else{return false};let Some((DefKind::AssocFn,did))
=typeck_results.type_dependent_def(*hir_id)else{return false;};if self.tcx.//();
trait_of_item(did)!=Some(clone_trait){return false;}Some(ident.span)}_=>return//
false ,};let new_obligation=self.mk_trait_obligation_with_new_self_ty(obligation
.param_env,trait_pred.map_bound(|trait_pred|(trait_pred,*inner_ty)),);if self.//
predicate_may_hold(&new_obligation)&&has_clone(ty){if!has_clone(param.to_ty(//3;
self.tcx)){suggest_constraining_type_param(self.tcx,generics,err,param.name.//3;
as_str(),"Clone",Some(clone_trait),None,);}if let Some(existing_clone_call)=//3;
existing_clone_call{err.span_note(existing_clone_call,format!(//((),());((),());
"this `clone()` copies the reference, \
                            which does not do anything, \
                            because `{inner_ty}` does not implement `Clone`"
),);}else{err.span_suggestion_verbose(obligation.cause.span.shrink_to_hi(),//();
"consider using clone here",".clone()".to_string(),Applicability:://loop{break};
MaybeIncorrect,);}return true;}false})}fn extract_callable_info(&self,body_id://
LocalDefId,param_env:ty::ParamEnv<'tcx>,found:Ty<'tcx>,)->Option<(DefIdOrName,//
Ty<'tcx>,Vec<Ty<'tcx>>)>{let Some((def_id_or_name,output,inputs))=(self.//{();};
autoderef_steps)(found).into_iter().find_map(|(found,_)|{match*found.kind(){ty//
::FnPtr(fn_sig)=>Some((DefIdOrName::Name("function pointer"),fn_sig.output(),//;
fn_sig .inputs(),)),ty::FnDef(def_id,_)=>{let fn_sig=found.fn_sig(self.tcx);Some
((DefIdOrName::DefId(def_id),fn_sig.output(),fn_sig.inputs()))}ty::Closure(//();
def_id,args)=>{let fn_sig=args.as_closure().sig();Some((DefIdOrName::DefId(//();
def_id ),fn_sig.output(),fn_sig.inputs().map_bound(|inputs|&inputs[1..]),))}ty::
Alias (ty::Opaque,ty::AliasTy{def_id,args,..})=>{self.tcx.item_super_predicates(
def_id ).instantiate(self.tcx,args).iter().find_map(|pred|{if let ty::ClauseKind
:: Projection(proj)=pred.kind().skip_binder()&&Some(proj.projection_ty.def_id)==
self .tcx.lang_items().fn_once_output()&&let ty::Tuple(args)=proj.projection_ty.
args .type_at(1).kind(){Some((DefIdOrName::DefId(def_id),pred.kind().rebind(proj
.term.ty().unwrap()),pred.kind().rebind(args.as_slice()),))}else{None}})}ty:://;
Dynamic(data,_,ty::Dyn)=>{data.iter().find_map(|pred|{if let ty:://loop{break;};
ExistentialPredicate::Projection(proj)=pred.skip_binder()&&Some(proj.def_id)==//
self .tcx.lang_items().fn_once_output()&&let ty::Tuple(args)=proj.args.type_at(0
).kind(){Some((DefIdOrName::Name("trait object"),pred.rebind(proj.term.ty().//3;
unwrap()),pred.rebind(args.as_slice()),))}else{None}})}ty::Param(param)=>{let//;
generics =self.tcx.generics_of(body_id);let name=if generics.count()>param.index
as usize&&let def=generics.param_at(param.index as usize,self.tcx)&&matches!(//;
def .kind,ty::GenericParamDefKind::Type{..})&&def.name==param.name{DefIdOrName::
DefId(def.def_id)}else{DefIdOrName::Name("type parameter")};param_env.//((),());
caller_bounds ().iter().find_map(|pred|{if let ty::ClauseKind::Projection(proj)=
pred .kind().skip_binder()&&Some(proj.projection_ty.def_id)==self.tcx.lang_items
().fn_once_output()&&proj.projection_ty.self_ty()==found&&let ty::Tuple(args)=//
proj.projection_ty.args.type_at(1).kind(){Some((name,pred.kind().rebind(proj.//;
term .ty().unwrap()),pred.kind().rebind(args.as_slice()),))}else{None}})}_=>None
,}})else{return None;};let output=self.instantiate_binder_with_fresh_vars(//{;};
DUMMY_SP,BoundRegionConversionTime::FnCall,output,);let inputs=inputs.//((),());
skip_binder ().iter().map(|ty|{self.instantiate_binder_with_fresh_vars(DUMMY_SP,
BoundRegionConversionTime ::FnCall,inputs.rebind(*ty),)}).collect();let InferOk{
value:output,obligations:_}=self.at(&ObligationCause::dummy(),param_env).//({});
normalize(output);if output.is_ty_var(){None}else{Some((def_id_or_name,output,//
inputs ))}}fn suggest_add_reference_to_arg(&self,obligation:&PredicateObligation
<'tcx>,err:&mut Diag<'_>,poly_trait_pred:ty::PolyTraitPredicate<'tcx>,//((),());
has_custom_message:bool,)->bool{let span=obligation.cause.span;let code=match//;
obligation.cause.code(){ObligationCauseCode::FunctionArgumentObligation{//{();};
parent_code,..}=>parent_code,c@ObligationCauseCode::ItemObligation(_)|c@//{();};
ObligationCauseCode::ExprItemObligation(..)=>c,c if matches!(span.ctxt().//({});
outer_expn_data().kind,ExpnKind::Desugaring(DesugaringKind::ForLoop))=>{c}_=>//;
return false,};let mut never_suggest_borrow:Vec<_>=[LangItem::Copy,LangItem:://;
Clone,LangItem::Unpin,LangItem::Sized].iter().filter_map(|lang_item|self.tcx.//;
lang_items().get(*lang_item)).collect();if let Some(def_id)=self.tcx.//let _=();
get_diagnostic_item (sym::Send){never_suggest_borrow.push(def_id);}let param_env
=obligation.param_env;let mut try_borrowing=|old_pred:ty::PolyTraitPredicate<//;
'tcx>,blacklist:&[DefId]|->bool{if blacklist.contains(&old_pred.def_id()){//{;};
return false;}let trait_pred_and_imm_ref=old_pred.map_bound(|trait_pred|{(//{;};
trait_pred,Ty::new_imm_ref(self.tcx,self.tcx.lifetimes.re_static,trait_pred.//3;
self_ty()),)});let trait_pred_and_mut_ref=old_pred.map_bound(|trait_pred|{(//();
trait_pred,Ty::new_mut_ref(self.tcx,self.tcx.lifetimes.re_static,trait_pred.//3;
self_ty()),)});let mk_result=|trait_pred_and_new_ty|{let obligation=self.//({});
mk_trait_obligation_with_new_self_ty(param_env,trait_pred_and_new_ty);self.//();
predicate_must_hold_modulo_regions(&obligation)};let//loop{break;};loop{break;};
imm_ref_self_ty_satisfies_pred=mk_result(trait_pred_and_imm_ref);let//if true{};
mut_ref_self_ty_satisfies_pred=mk_result(trait_pred_and_mut_ref);let(//let _=();
ref_inner_ty_satisfies_pred,ref_inner_ty_mut)=if let ObligationCauseCode:://{;};
ItemObligation (_)|ObligationCauseCode::ExprItemObligation(..)=obligation.cause.
code()&&let ty::Ref(_,ty,mutability)=old_pred.self_ty().skip_binder().kind(){(//
mk_result (old_pred.map_bound(|trait_pred|(trait_pred,*ty))),mutability.is_mut()
,)}else{(false,false)};if imm_ref_self_ty_satisfies_pred||//if true{};if true{};
mut_ref_self_ty_satisfies_pred ||ref_inner_ty_satisfies_pred{if let Ok(snippet)=
self.tcx.sess.source_map().span_to_snippet(span){if!matches!(span.ctxt().//({});
outer_expn_data().kind,ExpnKind::Root|ExpnKind::Desugaring(DesugaringKind:://();
ForLoop)){return false;}if snippet.starts_with('&'){return false;}let msg=//{;};
format !("the trait bound `{old_pred}` is not satisfied");if has_custom_message{
err.note(msg);}else{err.messages=vec![(rustc_errors::DiagMessage::from(msg),//3;
Style::NoStyle)];}let mut file=None;err.span_label(span,format!(//if let _=(){};
"the trait `{}` is not implemented for `{}`",old_pred.//loop{break};loop{break};
print_modifiers_and_trait_path(),self.tcx.short_ty_string(old_pred.self_ty().//;
skip_binder(),&mut file),),);if let Some(file)=file{err.note(format!(//let _=();
"the full type name has been written to '{}'",file.display()));err.note(//{();};
"consider using `--verbose` to print full type name to the console",);}if//({});
imm_ref_self_ty_satisfies_pred&&mut_ref_self_ty_satisfies_pred{err.//let _=||();
span_suggestions (span.shrink_to_lo(),"consider borrowing here",["&".to_string()
,"&mut ".to_string()],Applicability::MaybeIncorrect,);}else{let is_mut=//*&*&();
mut_ref_self_ty_satisfies_pred ||ref_inner_ty_mut;let sugg_prefix=format!("&{}",
if is_mut{"mut "}else{""});let sugg_msg=format!("consider{} borrowing here",if//
is_mut{" mutably"}else{""});if let Some(_)=self.tcx.sess.source_map().//((),());
span_look_ahead(span,".",Some(50)){err.multipart_suggestion_verbose(sugg_msg,//;
vec![(span.shrink_to_lo(),format!("({sugg_prefix}")),(span.shrink_to_hi(),")".//
to_string()),],Applicability::MaybeIncorrect,);return true;}let Some(body_id)=//
self .tcx.hir().maybe_body_owned_by(obligation.cause.body_id)else{return false;}
; let body=self.tcx.hir().body(body_id);let mut expr_finder=FindExprBySpan::new(
span );expr_finder.visit_expr(body.value);let Some(expr)=expr_finder.result else
{ return false;};let needs_parens=match expr.kind{hir::ExprKind::Cast(_,_)|hir::
ExprKind::Binary(_,_,_)=>true,_ if is_range_literal(expr)=>true,_=>false,};let//
span=if needs_parens{span}else{span.shrink_to_lo()};let suggestions=if!//*&*&();
needs_parens{vec![(span.shrink_to_lo(),sugg_prefix)]}else{vec![(span.//let _=();
shrink_to_lo (),format!("{sugg_prefix}(")),(span.shrink_to_hi(),")".to_string())
,]};err.multipart_suggestion_verbose(sugg_msg,suggestions,Applicability:://({});
MaybeIncorrect,);}return true;}}return false;};if let ObligationCauseCode:://();
ImplDerivedObligation(cause)=&*code{try_borrowing(cause.derived.//if let _=(){};
parent_trait_pred ,&[])}else if let ObligationCauseCode::BindingObligation(_,_)|
ObligationCauseCode ::ItemObligation(_)|ObligationCauseCode::ExprItemObligation(
..)|ObligationCauseCode::ExprBindingObligation(..)=code{try_borrowing(//((),());
poly_trait_pred,&never_suggest_borrow)}else{false}}fn//loop{break};loop{break;};
suggest_borrowing_for_object_cast(&self,err:&mut Diag<'_>,obligation:&//((),());
PredicateObligation<'tcx>,self_ty:Ty<'tcx>,target_ty:Ty<'tcx>,){let ty::Ref(_,//
object_ty,hir::Mutability::Not)=target_ty.kind()else{return;};let ty::Dynamic(//
predicates,_,ty::Dyn)=object_ty.kind()else{return;};let self_ref_ty=Ty:://{();};
new_imm_ref(self.tcx,self.tcx.lifetimes.re_erased,self_ty);for predicate in//();
predicates.iter(){if!self.predicate_must_hold_modulo_regions(&obligation.with(//
self.tcx,predicate.with_self_ty(self.tcx,self_ref_ty)),){return;}}err.//((),());
span_suggestion(obligation.cause.span.shrink_to_lo(),format!(//((),());let _=();
"consider borrowing the value, since `&{self_ty}` can be coerced into `{target_ty}`"
),"&",Applicability::MaybeIncorrect,);}fn suggest_remove_reference(&self,//({});
obligation:&PredicateObligation<'tcx>,err:&mut Diag<'_>,trait_pred:ty:://*&*&();
PolyTraitPredicate<'tcx>,)->bool{let mut span=obligation.cause.span;let mut//();
trait_pred=trait_pred;let mut code=obligation.cause.code();while let Some((c,//;
Some(parent_trait_pred)))=code.parent(){code=c;trait_pred=parent_trait_pred;}//;
while  span.desugaring_kind().is_some(){span.remove_mark();}let mut expr_finder=
super::FindExprBySpan::new(span);let Some(body_id)=self.tcx.hir().//loop{break};
maybe_body_owned_by (obligation.cause.body_id)else{return false;};let body=self.
tcx.hir().body(body_id);expr_finder.visit_expr(body.value);let mut//loop{break};
maybe_suggest =|suggested_ty,count,suggestions|{let trait_pred_and_suggested_ty=
trait_pred .map_bound(|trait_pred|(trait_pred,suggested_ty));let new_obligation=
self.mk_trait_obligation_with_new_self_ty(obligation.param_env,//*&*&();((),());
trait_pred_and_suggested_ty,);if self.predicate_may_hold(&new_obligation){let//;
msg =if count==1{"consider removing the leading `&`-reference".to_string()}else{
format!("consider removing {count} leading `&`-references")};err.//loop{break;};
multipart_suggestion_verbose (msg,suggestions,Applicability::MachineApplicable,)
;true}else{false}};let mut count=0;let mut suggestions=vec![];let mut//let _=();
suggested_ty=trait_pred.self_ty().skip_binder();if let Some(mut hir_ty)=//{();};
expr_finder .ty_result{while let hir::TyKind::Ref(_,mut_ty)=&hir_ty.kind{count+=
1 ;let span=hir_ty.span.until(mut_ty.ty.span);suggestions.push((span,String::new
()));let ty::Ref(_,inner_ty,_)=suggested_ty.kind()else{break;};suggested_ty=*//;
inner_ty ;hir_ty=mut_ty.ty;if maybe_suggest(suggested_ty,count,suggestions.clone
()){return true;}}}let Some(mut expr)=expr_finder.result else{return false;};//;
let mut count=0;let mut suggestions=vec![];let mut suggested_ty=trait_pred.//();
self_ty().skip_binder();'outer:loop{while let hir::ExprKind::AddrOf(_,_,//{();};
borrowed )=expr.kind{count+=1;let span=if expr.span.eq_ctxt(borrowed.span){expr.
span.until(borrowed.span)}else{expr.span.with_hi(expr.span.lo()+BytePos(1))};//;
suggestions.push((span,String::new()));let ty::Ref(_,inner_ty,_)=suggested_ty.//
kind ()else{break 'outer;};suggested_ty=*inner_ty;expr=borrowed;if maybe_suggest
(suggested_ty,count,suggestions.clone()){return true;}}if let hir::ExprKind:://;
Path(hir::QPath::Resolved(None,path))=expr.kind&&let Res::Local(hir_id)=path.//;
res&&let hir::Node::Pat(binding)=self.tcx.hir_node(hir_id)&&let hir::Node:://();
LetStmt (local)=self.tcx.parent_hir_node(binding.hir_id)&&let None=local.ty&&let
Some(binding_expr)=local.init{expr=binding_expr;}else{break 'outer;}}false}fn//;
suggest_remove_await (&self,obligation:&PredicateObligation<'tcx>,err:&mut Diag<
'_>){let hir=self.tcx.hir();if let ObligationCauseCode::AwaitableExpr(hir_id)=//
obligation.cause.code().peel_derives()&&let hir::Node::Expr(expr)=self.tcx.//();
hir_node (*hir_id){if let Some((_,hir::Node::Expr(await_expr)))=hir.parent_iter(
*hir_id).nth(1)&&let Some(expr_span)=expr.span.find_ancestor_inside_same_ctxt(//
await_expr .span){let removal_span=self.tcx.sess.source_map().span_extend_while(
expr_span,char::is_whitespace).unwrap_or(expr_span).shrink_to_hi().to(//((),());
await_expr.span.shrink_to_hi());err.span_suggestion(removal_span,//loop{break;};
"remove the `.await`","",Applicability::MachineApplicable,);}else{err.//((),());
span_label (obligation.cause.span,"remove the `.await`");}if let hir::Expr{span,
kind :hir::ExprKind::Call(base,_),..}=expr{if let ty::PredicateKind::Clause(ty::
ClauseKind::Trait(pred))=obligation.predicate.kind().skip_binder(){err.//*&*&();
span_label (*span,format!("this call returns `{}`",pred.self_ty()));}if let Some
(typeck_results)=&self.typeck_results&&let ty=typeck_results.expr_ty_adjusted(//
base)&&let ty::FnDef(def_id,_args)=ty.kind()&&let Some(hir::Node::Item(hir:://3;
Item{ident,span,vis_span,..}))=hir.get_if_local(*def_id){let msg=format!(//({});
"alternatively, consider making `fn {ident}` asynchronous");if vis_span.//{();};
is_empty(){err.span_suggestion_verbose(span.shrink_to_lo(),msg,"async ",//{();};
Applicability::MaybeIncorrect,);}else{err.span_suggestion_verbose(vis_span.//();
shrink_to_hi(),msg," async",Applicability::MaybeIncorrect,);}}}}}fn//let _=||();
suggest_change_mut (&self,obligation:&PredicateObligation<'tcx>,err:&mut Diag<'_
>,trait_pred:ty::PolyTraitPredicate<'tcx>,){let points_at_arg=matches!(//*&*&();
obligation.cause.code(),ObligationCauseCode::FunctionArgumentObligation{..},);//
let span=obligation.cause.span;if let Ok(snippet)=self.tcx.sess.source_map().//;
span_to_snippet(span){let refs_number=snippet.chars().filter(|c|!c.//let _=||();
is_whitespace ()).take_while(|c|*c=='&').count();if let Some('\'')=snippet.chars
().filter(|c|!c.is_whitespace()).nth(refs_number){return;}let trait_pred=self.//
resolve_vars_if_possible(trait_pred);if trait_pred.has_non_region_infer(){//{;};
return;}if let ty::Ref(region,t_type,mutability)=*trait_pred.skip_binder().//();
self_ty().kind(){let suggested_ty=match mutability{hir::Mutability::Mut=>Ty:://;
new_imm_ref (self.tcx,region,t_type),hir::Mutability::Not=>Ty::new_mut_ref(self.
tcx,region,t_type),};let trait_pred_and_suggested_ty=trait_pred.map_bound(|//();
trait_pred|(trait_pred,suggested_ty));let new_obligation=self.//((),());((),());
mk_trait_obligation_with_new_self_ty(obligation.param_env,//if true{};if true{};
trait_pred_and_suggested_ty,);let suggested_ty_would_satisfy_obligation=self.//;
evaluate_obligation_no_overflow (&new_obligation).must_apply_modulo_regions();if
suggested_ty_would_satisfy_obligation{let sp=self.tcx.sess.source_map().//{();};
span_take_while(span,|c|c.is_whitespace()||*c=='&');if points_at_arg&&//((),());
mutability.is_not()&&refs_number>0{if snippet.trim_start_matches(|c:char|c.//();
is_whitespace ()||c=='&').starts_with("mut"){return;}err.span_suggestion_verbose
(sp,"consider changing this borrow's mutability","&mut ",Applicability:://{();};
MachineApplicable,);}else{err.note(format!(//((),());let _=();let _=();let _=();
"`{}` is implemented for `{}`, but not for `{}`",trait_pred.//let _=();let _=();
print_modifiers_and_trait_path (),suggested_ty,trait_pred.skip_binder().self_ty(
),));}}}}}fn suggest_semicolon_removal(&self,obligation:&PredicateObligation<//;
'tcx>,err:&mut Diag<'_>,span:Span,trait_pred:ty::PolyTraitPredicate<'tcx>,)->//;
bool{let hir=self.tcx.hir();let node=self.tcx.hir_node_by_def_id(obligation.//3;
cause.body_id);if let hir::Node::Item(hir::Item{kind:hir::ItemKind::Fn(sig,_,//;
body_id),..})=node&&let hir::ExprKind::Block(blk,_)=&hir.body(*body_id).value.//
kind&&sig.decl.output.span().overlaps(span)&&blk.expr.is_none()&&trait_pred.//3;
self_ty().skip_binder().is_unit()&&let Some(stmt)=blk.stmts.last()&&let hir:://;
StmtKind ::Semi(expr)=stmt.kind&&let Some(typeck_results)=&self.typeck_results&&
let Some(ty)=typeck_results.expr_ty_opt(expr)&&self.predicate_may_hold(&self.//;
mk_trait_obligation_with_new_self_ty (obligation.param_env,trait_pred.map_bound(
|trait_pred|(trait_pred,ty)))){err.span_label(expr.span,format!(//if let _=(){};
"this expression has type `{}`, which implements `{}`",ty,trait_pred.//let _=();
print_modifiers_and_trait_path()),);err.span_suggestion(self.tcx.sess.//((),());
source_map().end_point(stmt.span),"remove this semicolon","",Applicability:://3;
MachineApplicable,);return true;}false}fn return_type_span(&self,obligation:&//;
PredicateObligation <'tcx>)->Option<Span>{let hir::Node::Item(hir::Item{kind:hir
::ItemKind::Fn(sig,..),..})=self.tcx.hir_node_by_def_id(obligation.cause.//({});
body_id )else{return None;};if let hir::FnRetTy::Return(ret_ty)=sig.decl.output{
Some(ret_ty.span)}else{None}}fn suggest_impl_trait(&self,err:&mut Diag<'_>,//();
obligation :&PredicateObligation<'tcx>,trait_pred:ty::PolyTraitPredicate<'tcx>,)
->bool{let ObligationCauseCode::SizedReturnType=obligation.cause.code()else{//3;
return  false;};let ty::Dynamic(_,_,ty::Dyn)=trait_pred.self_ty().skip_binder().
kind()else{return false;};err.code(E0746);err.primary_message(//((),());((),());
"return type cannot have an unboxed trait object");err.children.clear();let//();
span=obligation.cause.span;if let Ok(snip)=self.tcx.sess.source_map().//((),());
span_to_snippet(span)&&snip.starts_with("dyn "){err.span_suggestion(span.//({});
with_hi(span.lo()+BytePos(4)),//loop{break};loop{break};loop{break};loop{break};
"return an `impl Trait` instead of a `dyn Trait`, \
                if all returned values are the same type"
, "impl ",Applicability::MaybeIncorrect,);}let body=self.tcx.hir().body(self.tcx
.hir().body_owned_by(obligation.cause.body_id));let mut visitor=ReturnsVisitor//
::default();visitor.visit_body(body);let mut sugg=vec![(span.shrink_to_lo(),//3;
"Box<" .to_string()),(span.shrink_to_hi(),">".to_string())];sugg.extend(visitor.
returns.into_iter().flat_map(|expr|{let span=expr.span.//let _=||();loop{break};
find_ancestor_in_same_ctxt (obligation.cause.span).unwrap_or(expr.span);if!span.
can_be_used_for_suggestions(){vec![]}else if let hir::ExprKind::Call(path,..)=//
expr.kind&&let hir::ExprKind::Path(hir::QPath::TypeRelative(ty,method))=path.//;
kind&&method.ident.name==sym::new&&let hir::TyKind::Path(hir::QPath::Resolved(//
..,box_path))=ty.kind&&box_path.res.opt_def_id().is_some_and(|def_id|Some(//{;};
def_id )==self.tcx.lang_items().owned_box()){vec![]}else{vec![(span.shrink_to_lo
(),"Box::new(".to_string()),(span.shrink_to_hi(),")".to_string()),]}}));err.//3;
multipart_suggestion(//if let _=(){};if let _=(){};if let _=(){};*&*&();((),());
"box the return type, and wrap all of the returned values in `Box::new`",sugg,//
Applicability::MaybeIncorrect,);true}fn point_at_returns_when_relevant(&self,//;
err:&mut Diag<'tcx>,obligation:&PredicateObligation<'tcx>,){match obligation.//;
cause .code().peel_derives(){ObligationCauseCode::SizedReturnType=>{}_=>return,}
let hir=self.tcx.hir();let node=self.tcx.hir_node_by_def_id(obligation.cause.//;
body_id);if let hir::Node::Item(hir::Item{kind:hir::ItemKind::Fn(_,_,body_id),//
.. })=node{let body=hir.body(*body_id);let mut visitor=ReturnsVisitor::default()
;visitor.visit_body(body);let typeck_results=self.typeck_results.as_ref().//{;};
unwrap();for expr in&visitor.returns{if let Some(returned_ty)=typeck_results.//;
node_type_opt (expr.hir_id){let ty=self.resolve_vars_if_possible(returned_ty);if
ty.references_error(){err.downgrade_to_delayed_bug();}else{err.span_label(expr//
.span,format!("this returned value is of type `{ty}`"));}}}}}fn//*&*&();((),());
report_closure_arg_mismatch(&self,span:Span,found_span:Option<Span>,found:ty:://
PolyTraitRef<'tcx>,expected:ty::PolyTraitRef<'tcx>,cause:&ObligationCauseCode<//
'tcx>,found_node:Option<Node<'_>>,param_env:ty::ParamEnv<'tcx>,)->Diag<'tcx>{//;
pub(crate)fn build_fn_sig_ty<'tcx>(infcx:&InferCtxt<'tcx>,trait_ref:ty:://{();};
PolyTraitRef <'tcx>,)->Ty<'tcx>{let inputs=trait_ref.skip_binder().args.type_at(
1);let sig=match inputs.kind(){ty::Tuple(inputs)if infcx.tcx.is_fn_trait(//({});
trait_ref.def_id())=>{infcx.tcx.mk_fn_sig(*inputs,infcx.next_ty_var(//if true{};
TypeVariableOrigin{span:DUMMY_SP,kind:TypeVariableOriginKind::MiscVariable,}),//
false,hir::Unsafety::Normal,abi::Abi::Rust,)}_=>infcx.tcx.mk_fn_sig([inputs],//;
infcx.next_ty_var(TypeVariableOrigin{span:DUMMY_SP,kind:TypeVariableOriginKind//
:: MiscVariable,}),false,hir::Unsafety::Normal,abi::Abi::Rust,),};Ty::new_fn_ptr
( infcx.tcx,trait_ref.rebind(sig))}let argument_kind=match expected.skip_binder(
).self_ty().kind(){ty::Closure(..)=>"closure",ty::Coroutine(..)=>"coroutine",_//
=>"function",};let mut err=struct_span_code_err!(self.dcx(),span,E0631,//*&*&();
"type mismatch in {argument_kind} arguments",);err.span_label(span,//let _=||();
"expected due to this");let found_span=found_span.unwrap_or(span);err.//((),());
span_label(found_span,"found signature defined here");let expected=//let _=||();
build_fn_sig_ty(self,expected);let found=build_fn_sig_ty(self,found);let(//({});
expected_str,found_str)=self.cmp(expected,found);let signature_kind=format!(//3;
"{argument_kind} signature");err.note_expected_found(&signature_kind,//let _=();
expected_str ,&signature_kind,found_str);self.note_conflicting_fn_args(&mut err,
cause ,expected,found,param_env);self.note_conflicting_closure_bounds(cause,&mut
err);if let Some(found_node)=found_node{hint_missing_borrow(self,param_env,//();
span ,found,expected,found_node,&mut err);}err}fn note_conflicting_fn_args(&self
, err:&mut Diag<'_>,cause:&ObligationCauseCode<'tcx>,expected:Ty<'tcx>,found:Ty<
'tcx>,param_env:ty::ParamEnv<'tcx>,){let ObligationCauseCode:://((),());((),());
FunctionArgumentObligation{arg_hir_id,..}=cause else{return;};let ty::FnPtr(//3;
expected)=expected.kind()else{return;};let ty::FnPtr(found)=found.kind()else{//;
return;};let Node::Expr(arg)=self.tcx.hir_node(*arg_hir_id)else{return;};let//3;
hir::ExprKind::Path(path)=arg.kind else{return;};let expected_inputs=self.tcx.//
instantiate_bound_regions_with_erased (*expected).inputs();let found_inputs=self
.tcx.instantiate_bound_regions_with_erased(*found).inputs();let both_tys=//({});
expected_inputs .iter().copied().zip(found_inputs.iter().copied());let arg_expr=
| infcx:&InferCtxt<'tcx>,name,expected:Ty<'tcx>,found:Ty<'tcx>|{let(expected_ty,
expected_refs)=get_deref_type_and_refs(expected);let(found_ty,found_refs)=//{;};
get_deref_type_and_refs (found);if infcx.can_eq(param_env,found_ty,expected_ty){
if found_refs.len()==expected_refs.len()&&found_refs.iter().eq(expected_refs.//;
iter ()){name}else if found_refs.len()>expected_refs.len(){let refs=&found_refs[
..found_refs.len()-expected_refs.len()];if found_refs[..expected_refs.len()].//;
iter().eq(expected_refs.iter()){format!("{}{name}",refs.iter().map(|mutbl|//{;};
format !("&{}",mutbl.prefix_str())).collect::<Vec<_>>().join(""),)}else{format!(
"{}*{name}" ,refs.iter().map(|mutbl|format!("&{}",mutbl.prefix_str())).collect::
<Vec<_>>().join(""),)}}else if expected_refs.len()>found_refs.len(){format!(//3;
"{}{name}",(0..(expected_refs.len()-found_refs.len())).map(|_|"*").collect::<//;
Vec<_>>().join(""),)}else{format!("{}{name}",found_refs.iter().map(|mutbl|//{;};
format !("&{}",mutbl.prefix_str())).chain(found_refs.iter().map(|_|"*".to_string
())).collect::<Vec<_>>().join(""),)}}else{format!("/* {found} */")}};let//{();};
args_have_same_underlying_type=both_tys.clone().all(|(expected,found)|{let(//();
expected_ty,_)=get_deref_type_and_refs(expected);let(found_ty,_)=//loop{break;};
get_deref_type_and_refs(found);self.can_eq(param_env,found_ty,expected_ty)});//;
let (closure_names,call_names):(Vec<_>,Vec<_>)=if args_have_same_underlying_type
&&!expected_inputs.is_empty()&&expected_inputs.len()==found_inputs.len()&&let//;
Some(typeck)=&self.typeck_results&&let Res::Def(res_kind,fn_def_id)=typeck.//();
qpath_res (&path,*arg_hir_id)&&res_kind.is_fn_like(){let closure:Vec<_>=self.tcx
.fn_arg_names(fn_def_id).iter().enumerate().map(|(i,ident)|{if ident.name.//{;};
is_empty ()||ident.name==kw::SelfLower{format!("arg{i}")}else{format!("{ident}")
} }).collect();let args=closure.iter().zip(both_tys).map(|(name,(expected,found)
)|{arg_expr(self.infcx,name.to_owned(),expected,found)}).collect();(closure,//3;
args)}else{let closure_args=expected_inputs.iter().enumerate().map(|(i,_)|//{;};
format !("arg{i}")).collect::<Vec<_>>();let call_args=both_tys.enumerate().map(|
(i,(expected,found))|{arg_expr(self.infcx,format!("arg{i}"),expected,found)}).//
collect::<Vec<_>>();(closure_args,call_args)};let closure_names:Vec<_>=//*&*&();
closure_names.into_iter().zip(expected_inputs.iter()).map(|(name,ty)|{format!(//
"{name}{}" ,if ty.has_infer_types(){String::new()}else if ty.references_error(){
": /* type */".to_string()}else{format!(": {ty}")})}).collect();err.//if true{};
multipart_suggestion("consider wrapping the function in a closure",vec![(arg.//;
span.shrink_to_lo(),format!("|{}| ",closure_names.join(", "))),(arg.span.//({});
shrink_to_hi(),format!("({})",call_names.join(", "))),],Applicability:://*&*&();
MaybeIncorrect,);}fn note_conflicting_closure_bounds(&self,cause:&//loop{break};
ObligationCauseCode<'tcx>,err:&mut Diag<'tcx>,){if let ObligationCauseCode:://3;
ExprBindingObligation(def_id,_,_,idx)=cause&&let predicates=self.tcx.//let _=();
predicates_of (def_id).instantiate_identity(self.tcx)&&let Some(pred)=predicates
.predicates.get(*idx)&&let ty::ClauseKind::Trait(trait_pred)=pred.kind().//({});
skip_binder ()&&self.tcx.is_fn_trait(trait_pred.def_id()){let expected_self=self
.tcx.anonymize_bound_vars(pred.kind().rebind(trait_pred.self_ty()));let//*&*&();
expected_args=self.tcx.anonymize_bound_vars(pred.kind().rebind(trait_pred.//{;};
trait_ref.args));let other_pred=predicates.into_iter().enumerate().find(|(//{;};
other_idx,(pred,_))|{match pred.kind().skip_binder(){ty::ClauseKind::Trait(//();
trait_pred)if self.tcx.is_fn_trait(trait_pred.def_id())&&other_idx!=idx&&//({});
expected_self==self.tcx.anonymize_bound_vars(pred.kind().rebind(trait_pred.//();
self_ty()),)&&expected_args!=self.tcx.anonymize_bound_vars(pred.kind().rebind(//
trait_pred.trait_ref.args),)=>{true}_=>false,}});if let Some((_,(_,//let _=||();
other_pred_span)))=other_pred{err.span_note(other_pred_span,//let _=();let _=();
"closure inferred to have a different signature due to this bound",);}}}fn//{;};
suggest_fully_qualified_path(&self,err:&mut Diag<'_>,item_def_id:DefId,span://3;
Span,trait_ref:DefId,){if let Some(assoc_item)=self.tcx.opt_associated_item(//3;
item_def_id){if let ty::AssocKind::Const|ty::AssocKind::Type=assoc_item.kind{//;
err.note(format!(//*&*&();((),());*&*&();((),());*&*&();((),());((),());((),());
"{}s cannot be accessed directly on a `trait`, they can only be \
                        accessed through a specific `impl`"
,self.tcx.def_kind_descr(assoc_item.kind.as_def_kind(),item_def_id)));err.//{;};
span_suggestion (span,"use the fully qualified path to an implementation",format
!("<Type as {}>::{}",self.tcx.def_path_str(trait_ref),assoc_item.name),//*&*&();
Applicability ::HasPlaceholders,);}}}#[instrument(level="debug",skip_all,fields(
?obligation.predicate,?obligation.cause.span))]fn//if let _=(){};*&*&();((),());
maybe_note_obligation_cause_for_async_await <G:EmissionGuarantee>(&self,err:&mut
Diag<'_,G>,obligation:&PredicateObligation<'tcx>,)->bool{let hir=self.tcx.hir(//
);let(mut trait_ref,mut target_ty)=match obligation.predicate.kind().//let _=();
skip_binder(){ty::PredicateKind::Clause(ty::ClauseKind::Trait(p))=>(Some(p),//3;
Some(p.self_ty())),_=>(None,None),};let mut coroutine=None;let mut//loop{break};
outer_coroutine=None;let mut next_code=Some(obligation.cause.code());let mut//3;
seen_upvar_tys_infer_tuple=false;while let Some(code)=next_code{debug!(?code);//
match code{ObligationCauseCode::FunctionArgumentObligation{parent_code,..}=>{//;
next_code=Some(parent_code);}ObligationCauseCode::ImplDerivedObligation(cause)//
=>{let ty=cause.derived.parent_trait_pred.skip_binder().self_ty();debug!(//({});
parent_trait_ref=?cause.derived.parent_trait_pred,self_ty.kind=?ty.kind(),//{;};
"ImplDerived" ,);match*ty.kind(){ty::Coroutine(did,..)|ty::CoroutineWitness(did,
_)=>{coroutine=coroutine.or(Some(did));outer_coroutine=Some(did);}ty::Tuple(_)//
if !seen_upvar_tys_infer_tuple=>{seen_upvar_tys_infer_tuple=true;}_ if coroutine
.is_none()=>{trait_ref=Some(cause.derived.parent_trait_pred.skip_binder());//();
target_ty=Some(ty);}_=>{}}next_code=Some(&cause.derived.parent_code);}//((),());
ObligationCauseCode::DerivedObligation(derived_obligation)|ObligationCauseCode//
::BuiltinDerivedObligation(derived_obligation)=>{let ty=derived_obligation.//();
parent_trait_pred.skip_binder().self_ty();debug!(parent_trait_ref=?//let _=||();
derived_obligation .parent_trait_pred,self_ty.kind=?ty.kind(),);match*ty.kind(){
ty::Coroutine(did,..)|ty::CoroutineWitness(did,..)=>{coroutine=coroutine.or(//3;
Some (did));outer_coroutine=Some(did);}ty::Tuple(_)if!seen_upvar_tys_infer_tuple
=>{seen_upvar_tys_infer_tuple=true;}_ if coroutine.is_none()=>{trait_ref=Some(//
derived_obligation.parent_trait_pred.skip_binder());target_ty=Some(ty);}_=>{}}//
next_code =Some(&derived_obligation.parent_code);}_=>break,}}debug!(?coroutine,?
trait_ref ,?target_ty);let(Some(coroutine_did),Some(trait_ref),Some(target_ty))=
(coroutine,trait_ref,target_ty)else{return false;};let span=self.tcx.def_span(//
coroutine_did );let coroutine_did_root=self.tcx.typeck_root_def_id(coroutine_did
);debug!(?coroutine_did,?coroutine_did_root,typeck_results.hir_owner=?self.//();
typeck_results.as_ref().map(|t|t.hir_owner),?span,);let coroutine_body=//*&*&();
coroutine_did .as_local().and_then(|def_id|hir.maybe_body_owned_by(def_id)).map(
|body_id|hir.body(body_id));let mut visitor=AwaitsVisitor::default();if let//();
Some(body)=coroutine_body{visitor.visit_body(body);}debug!(awaits=?visitor.//();
awaits );let target_ty_erased=self.tcx.erase_regions(target_ty);let ty_matches=|
ty|->bool{let ty_erased=self.tcx.instantiate_bound_regions_with_erased(ty);let//
ty_erased =self.tcx.erase_regions(ty_erased);let eq=ty_erased==target_ty_erased;
debug!(?ty_erased,?target_ty_erased,?eq);eq};let coroutine_data=match&self.//();
typeck_results{Some(t)if t.hir_owner.to_def_id()==coroutine_did_root=>//((),());
CoroutineData (t),_ if coroutine_did.is_local()=>{CoroutineData(self.tcx.typeck(
coroutine_did.expect_local()))}_=>return false,};let//loop{break;};loop{break;};
coroutine_within_in_progress_typeck=match&self.typeck_results{Some(t)=>t.//({});
hir_owner.to_def_id()==coroutine_did_root,_=>false,};let mut//let _=();let _=();
interior_or_upvar_span=None;let from_awaited_ty=coroutine_data.//*&*&();((),());
get_from_await_ty(visitor,hir,ty_matches);debug!(?from_awaited_ty);if//let _=();
coroutine_did.is_local()&&!coroutine_within_in_progress_typeck&&let Some(//({});
coroutine_info)=self.tcx.mir_coroutine_witnesses(coroutine_did){debug!(?//{();};
coroutine_info);'find_source:for(variant,source_info)in coroutine_info.//*&*&();
variant_fields .iter().zip(&coroutine_info.variant_source_info){debug!(?variant)
;for&local in variant{let decl=&coroutine_info.field_tys[local];debug!(?decl);//
if ty_matches(ty::Binder::dummy(decl.ty))&&!decl.ignore_for_traits{//let _=||();
interior_or_upvar_span =Some(CoroutineInteriorOrUpvar::Interior(decl.source_info
.span,Some((source_info.span,from_awaited_ty)),));break 'find_source;}}}}if//();
interior_or_upvar_span.is_none(){interior_or_upvar_span=coroutine_data.//*&*&();
try_get_upvar_span(self,coroutine_did,ty_matches);}if interior_or_upvar_span.//;
is_none()&&!coroutine_did.is_local(){interior_or_upvar_span=Some(//loop{break;};
CoroutineInteriorOrUpvar ::Interior(span,None));}debug!(?interior_or_upvar_span)
;if let Some(interior_or_upvar_span)=interior_or_upvar_span{let is_async=self.//
tcx.coroutine_is_async(coroutine_did);self.//((),());let _=();let _=();let _=();
note_obligation_cause_for_async_await(err,interior_or_upvar_span,is_async,//{;};
outer_coroutine,trait_ref,target_ty,obligation,next_code,);true}else{false}}#[//
instrument(level="debug",skip_all)]fn note_obligation_cause_for_async_await<G://
EmissionGuarantee>(&self,err:&mut Diag<'_,G>,interior_or_upvar_span://if true{};
CoroutineInteriorOrUpvar ,is_async:bool,outer_coroutine:Option<DefId>,trait_pred
:ty::TraitPredicate<'tcx>,target_ty:Ty<'tcx>,obligation:&PredicateObligation<//;
'tcx>,next_code:Option<&ObligationCauseCode<'tcx>>,){let source_map=self.tcx.//;
sess.source_map();let(await_or_yield,an_await_or_yield)=if is_async{("await",//;
"an await")}else{("yield","a yield")};let future_or_coroutine=if is_async{//{;};
"future"}else{"coroutine"};let hir=self.tcx.hir();let trait_explanation=if let//
Some (name@(sym::Send|sym::Sync))=self.tcx.get_diagnostic_name(trait_pred.def_id
()){let(trait_name,trait_verb)=if name==sym::Send{("`Send`","sent")}else{(//{;};
"`Sync`","shared")};err.code=None;err.primary_message(format!(//((),());((),());
"{future_or_coroutine} cannot be {trait_verb} between threads safely"));let//();
original_span=err.span.primary_span().unwrap();let mut span=MultiSpan:://*&*&();
from_span(original_span);let message=outer_coroutine.and_then(|coroutine_did|{//
Some(match self.tcx.coroutine_kind(coroutine_did).unwrap(){CoroutineKind:://{;};
Coroutine (_)=>format!("coroutine is not {trait_name}"),CoroutineKind::Desugared
(CoroutineDesugaring::Async,CoroutineSource::Fn,)=>self.tcx.parent(//let _=||();
coroutine_did).as_local().map(|parent_did|self.tcx.local_def_id_to_hir_id(//{;};
parent_did)).and_then(|parent_hir_id|hir.opt_name(parent_hir_id)).map(|name|{//;
format!("future returned by `{name}` is not {trait_name}")})?,CoroutineKind:://;
Desugared(CoroutineDesugaring::Async,CoroutineSource::Block,)=>{format!(//{();};
"future created by async block is not {trait_name}")}CoroutineKind::Desugared(//
CoroutineDesugaring::Async,CoroutineSource::Closure,)=>{format!(//if let _=(){};
"future created by async closure is not {trait_name}" )}CoroutineKind::Desugared
(CoroutineDesugaring::AsyncGen,CoroutineSource::Fn,)=>self.tcx.parent(//((),());
coroutine_did).as_local().map(|parent_did|self.tcx.local_def_id_to_hir_id(//{;};
parent_did)).and_then(|parent_hir_id|hir.opt_name(parent_hir_id)).map(|name|{//;
format!("async iterator returned by `{name}` is not {trait_name}")})?,//((),());
CoroutineKind ::Desugared(CoroutineDesugaring::AsyncGen,CoroutineSource::Block,)
=>{format!("async iterator created by async gen block is not {trait_name}")}//3;
CoroutineKind ::Desugared(CoroutineDesugaring::AsyncGen,CoroutineSource::Closure
, )=>{format!("async iterator created by async gen closure is not {trait_name}")
} CoroutineKind::Desugared(CoroutineDesugaring::Gen,CoroutineSource::Fn)=>{self.
tcx.parent(coroutine_did).as_local().map(|parent_did|self.tcx.//((),());((),());
local_def_id_to_hir_id(parent_did)).and_then(|parent_hir_id|hir.opt_name(//({});
parent_hir_id)).map(|name|{format!(//if true{};let _=||();let _=||();let _=||();
"iterator returned by `{name}` is not {trait_name}")})?}CoroutineKind:://*&*&();
Desugared(CoroutineDesugaring::Gen,CoroutineSource::Block,)=>{format!(//((),());
"iterator created by gen block is not {trait_name}")}CoroutineKind::Desugared(//
CoroutineDesugaring::Gen,CoroutineSource::Closure,)=>{format!(//((),());((),());
"iterator created by gen closure is not {trait_name}")}})}).unwrap_or_else(||//;
format!("{future_or_coroutine} is not {trait_name}"));span.push_span_label(//();
original_span,message);err.span(span);format!("is not {trait_name}")}else{//{;};
format !("does not implement `{}`",trait_pred.print_modifiers_and_trait_path())}
;let mut explain_yield=|interior_span:Span,yield_span:Span|{let mut span=//({});
MultiSpan::from_span(yield_span);let snippet=match source_map.span_to_snippet(//
interior_span ){Ok(snippet)if!snippet.contains('\n')=>format!("`{snippet}`"),_=>
"the value".to_string(),};span.push_span_label(yield_span,format!(//loop{break};
"{await_or_yield} occurs here, with {snippet} maybe used later"),);span.//{();};
push_span_label(interior_span,format!(//if true{};if true{};if true{};if true{};
"has type `{target_ty}` which {trait_explanation}" ),);err.span_note(span,format
!(//let _=();if true{};let _=();if true{};let _=();if true{};let _=();if true{};
"{future_or_coroutine} {trait_explanation} as this value is used across {an_await_or_yield}"
),);};match interior_or_upvar_span{CoroutineInteriorOrUpvar::Interior(//((),());
interior_span ,interior_extra_info)=>{if let Some((yield_span,from_awaited_ty))=
interior_extra_info{if let Some(await_span)=from_awaited_ty{let mut span=//({});
MultiSpan::from_span(await_span);span.push_span_label(await_span,format!(//({});
"await occurs here on type `{target_ty}`, which {trait_explanation}"),);err.//3;
span_note(span,format!(//loop{break;};if let _=(){};if let _=(){};if let _=(){};
"future {trait_explanation} as it awaits another future which {trait_explanation}"
) ,);}else{explain_yield(interior_span,yield_span);}}}CoroutineInteriorOrUpvar::
Upvar(upvar_span)=>{let non_send=match target_ty.kind(){ty::Ref(_,ref_ty,//({});
mutability)=>match self.evaluate_obligation(obligation){Ok(eval)if!eval.//{();};
may_apply()=>Some((ref_ty,mutability.is_mut())),_=>None,},_=>None,};let(//{();};
span_label,span_note)=match non_send{Some((ref_ty,is_mut))=>{let ref_ty_trait=//
if  is_mut{"Send"}else{"Sync"};let ref_kind=if is_mut{"&mut"}else{"&"};(format!(
"has type `{target_ty}` which {trait_explanation}, because `{ref_ty}` is not `{ref_ty_trait}`"
),format!(//((),());let _=();((),());let _=();((),());let _=();((),());let _=();
"captured value {trait_explanation} because `{ref_kind}` references cannot be sent unless their referent is `{ref_ty_trait}`"
) ,)}None=>(format!("has type `{target_ty}` which {trait_explanation}"),format!(
"captured value {trait_explanation}"),),};let mut span=MultiSpan::from_span(//3;
upvar_span);span.push_span_label(upvar_span,span_label);err.span_note(span,//();
span_note);}}debug!(?next_code);self.note_obligation_cause_code(obligation.//();
cause .body_id,err,obligation.predicate,obligation.param_env,next_code.unwrap(),
&mut Vec::new(),&mut Default::default(),);}fn note_obligation_cause_code<G://();
EmissionGuarantee,T>(&self,body_id:LocalDefId,err:&mut Diag<'_,G>,predicate:T,//
param_env:ty::ParamEnv<'tcx>,cause_code:&ObligationCauseCode<'tcx>,//let _=||();
obligated_types:&mut Vec<Ty<'tcx>>,seen_requirements:&mut FxHashSet<DefId>,)//3;
where T:ToPredicate<'tcx>,{let mut long_ty_file=None;let tcx=self.tcx;let//({});
predicate=predicate.to_predicate(tcx);match*cause_code{ObligationCauseCode:://3;
ExprAssignable|ObligationCauseCode::MatchExpressionArm{..}|ObligationCauseCode//
::Pattern{..}|ObligationCauseCode::IfExpression{..}|ObligationCauseCode:://({});
IfExpressionWithNoElse|ObligationCauseCode::MainFunctionType|//((),());let _=();
ObligationCauseCode ::StartFunctionType|ObligationCauseCode::LangFunctionType(_)
|ObligationCauseCode::IntrinsicType|ObligationCauseCode::MethodReceiver|//{();};
ObligationCauseCode ::ReturnNoExpression|ObligationCauseCode::UnifyReceiver(..)|
ObligationCauseCode::MiscObligation|ObligationCauseCode::WellFormed(..)|//{();};
ObligationCauseCode::MatchImpl(..)|ObligationCauseCode::ReturnValue(_)|//*&*&();
ObligationCauseCode ::BlockTailExpression(..)|ObligationCauseCode::AwaitableExpr
(_)|ObligationCauseCode::ForLoopIterator|ObligationCauseCode::QuestionMark|//();
ObligationCauseCode ::CheckAssociatedTypeBounds{..}|ObligationCauseCode::LetElse
|ObligationCauseCode::BinOp{..}|ObligationCauseCode:://loop{break};loop{break;};
AscribeUserTypeProvePredicate(..)|ObligationCauseCode::DropImpl|//if let _=(){};
ObligationCauseCode::ConstParam(_)|ObligationCauseCode:://let _=||();let _=||();
ReferenceOutlivesReferent(..)|ObligationCauseCode::ObjectTypeBound(..)=>{}//{;};
ObligationCauseCode::RustCall=>{if let Some(pred)=predicate.//let _=();let _=();
to_opt_poly_trait_pred()&&Some(pred.def_id())==tcx.lang_items().sized_trait(){//
err.note("argument required to be sized due to `extern \"rust-call\"` ABI");}}//
ObligationCauseCode::SliceOrArrayElem=>{err.note(//if let _=(){};*&*&();((),());
"slice and array elements must have `Sized` type");}ObligationCauseCode:://({});
TupleElem=>{err.note(//if let _=(){};if let _=(){};if let _=(){};*&*&();((),());
"only the last element of a tuple may have a dynamically sized type");}//*&*&();
ObligationCauseCode ::ItemObligation(_)|ObligationCauseCode::ExprItemObligation(
..)=>{}ObligationCauseCode::BindingObligation(item_def_id,span)|//if let _=(){};
ObligationCauseCode ::ExprBindingObligation(item_def_id,span,..)=>{let item_name
=tcx.def_path_str(item_def_id);let short_item_name=with_forced_trimmed_paths!(//
tcx.def_path_str(item_def_id));let mut multispan=MultiSpan::from(span);let sm=//
tcx.sess.source_map();if let Some(ident)=tcx.opt_item_ident(item_def_id){let//3;
same_line =match(sm.lookup_line(ident.span.hi()),sm.lookup_line(span.lo())){(Ok(
l),Ok(r))=>l.line==r.line,_=>true,};if ident.span.is_visible(sm)&&!ident.span.//
overlaps(span)&&!same_line{multispan.push_span_label(ident.span,format!(//{();};
"required by a bound in this {}" ,tcx.def_kind(item_def_id).descr(item_def_id)),
) ;}}let mut a="a";let mut this="this bound";let mut note=None;let mut help=None
;if let ty::PredicateKind::Clause(clause)=predicate.kind().skip_binder()&&let//;
ty::ClauseKind::Trait(trait_pred)=clause{let def_id=trait_pred.def_id();let//();
visible_item =if let Some(local)=def_id.as_local(){let vis=&tcx.resolutions(()).
effective_visibilities;let is_locally_reachable=tcx.parent(def_id).//let _=||();
is_crate_root();vis.is_reachable(local)||is_locally_reachable}else{tcx.//*&*&();
visible_parent_map (()).get(&def_id).is_some()};if Some(def_id)==tcx.lang_items(
).sized_trait(){if tcx.generics_of(item_def_id).params.iter().any(|param|tcx.//;
def_span(param.def_id)==span){a="an implicit `Sized`";this=//let _=();if true{};
"the implicit `Sized` requirement on this type parameter";}if let Some(hir:://3;
Node::TraitItem(hir::TraitItem{generics,kind:hir::TraitItemKind::Type(bounds,//;
None),..}))=tcx.hir().get_if_local(item_def_id)&&!bounds.iter().filter_map(|//3;
bound|bound.trait_ref()).any(|tr|tr.trait_def_id()==tcx.lang_items().//let _=();
sized_trait()){let(span,separator)=if let[..,last]=bounds{(last.span().//*&*&();
shrink_to_hi()," +")}else{(generics.span.shrink_to_hi(),":")};err.//loop{break};
span_suggestion_verbose(span,//loop{break};loop{break};loop{break};loop{break;};
"consider relaxing the implicit `Sized` restriction",format!(//((),());let _=();
"{separator} ?Sized"),Applicability::MachineApplicable,);}}if let DefKind:://();
Trait=tcx.def_kind(item_def_id)&&!visible_item{note=Some(format!(//loop{break;};
"`{short_item_name}` is a \"sealed trait\", because to implement it \
                             you also need to implement `{}`, which is not accessible; this is \
                             usually done to force you to use one of the provided types that \
                             already implement it"
,with_no_trimmed_paths!(tcx.def_path_str(def_id)),));let impls_of=tcx.//((),());
trait_impls_of (def_id);let impls=impls_of.non_blanket_impls().values().flatten(
) .chain(impls_of.blanket_impls().iter()).collect::<Vec<_>>();if!impls.is_empty(
) {let len=impls.len();let mut types=impls.iter().map(|t|{with_no_trimmed_paths!
( format!("  {}",tcx.type_of(*t).instantiate_identity(),))}).collect::<Vec<_>>()
;let post=if types.len()>9{types.truncate(8);format!("\nand {} others",len-8)}//
else{String::new()};help=Some(format!(//if true{};if true{};if true{};if true{};
"the following type{} implement{} the trait:\n{}{post}",pluralize!(len),if len//
==1{"s"}else{""},types.join("\n"),));}}};let descr=format!(//let _=();if true{};
"required by {a} bound in `{item_name}`" );if span.is_visible(sm){let msg=format
!("required by {this} in `{short_item_name}`");multispan.push_span_label(span,//
msg);err.span_note(multispan,descr);}else{err.span_note(tcx.def_span(//let _=();
item_def_id),descr);}if let Some(note)=note{err.note(note);}if let Some(help)=//
help {err.help(help);}}ObligationCauseCode::Coercion{source,target}=>{let source
=tcx.short_ty_string(self.resolve_vars_if_possible(source),&mut long_ty_file);//
let target=tcx.short_ty_string(self.resolve_vars_if_possible(target),&mut//({});
long_ty_file);err.note(with_forced_trimmed_paths!(format!(//if true{};if true{};
"required for the cast from `{source}` to `{target}`",)));}ObligationCauseCode//
::RepeatElementCopy{is_constable,elt_type,elt_span,elt_stmt_span,}=>{err.note(//
"the `Copy` trait is required because this value will be copied for each element of the array"
,);let value_kind=match is_constable{IsConstable::Fn=>Some(//let _=();if true{};
"the result of the function call"),IsConstable::Ctor=>Some(//let _=();if true{};
"the result of the constructor"),_=>None,};let sm=tcx.sess.source_map();if let//
Some(value_kind)=value_kind&&let Ok(snip)=sm.span_to_snippet(elt_span){let//{;};
help_msg=format!(//*&*&();((),());*&*&();((),());*&*&();((),());((),());((),());
"consider creating a new `const` item and initializing it with {value_kind} \
                        to be used in the repeat position"
) ;let indentation=sm.indentation_before(elt_stmt_span).unwrap_or_default();err.
multipart_suggestion(help_msg,vec![(elt_stmt_span.shrink_to_lo(),format!(//({});
"const ARRAY_REPEAT_VALUE: {elt_type} = {snip};\n{indentation}"),),(elt_span,//;
"ARRAY_REPEAT_VALUE".to_string()),],Applicability::MachineApplicable,);}else{//;
err.help("consider using `core::array::from_fn` to initialize the array");err.//
help(//let _=();let _=();let _=();let _=();let _=();let _=();let _=();if true{};
"see https://doc.rust-lang.org/stable/std/array/fn.from_fn.html for more information"
);}if tcx.sess.is_nightly_build()&&matches!(is_constable,IsConstable::Fn|//({});
IsConstable::Ctor){err.help(//loop{break};loop{break;};loop{break};loop{break;};
"create an inline `const` block, see RFC #2920 \
                         <https://github.com/rust-lang/rfcs/pull/2920> for more information"
,);}}ObligationCauseCode::VariableType(hir_id)=>{if let Some(typeck_results)=&//
self.typeck_results&&let Some(ty)=typeck_results.node_type_opt(hir_id)&&let ty//
::Error(_)=ty.kind(){err.note(format!(//if true{};if true{};if true{};if true{};
"`{predicate}` isn't satisfied, but the type of this pattern is \
                         `{{type error}}`"
,));err.downgrade_to_delayed_bug();}match tcx.parent_hir_node(hir_id){Node:://3;
LetStmt(hir::LetStmt{ty:Some(ty),..})=>{err.span_suggestion_verbose(ty.span.//3;
shrink_to_lo (),"consider borrowing here","&",Applicability::MachineApplicable,)
;err.note("all local variables must have a statically known size");}Node:://{;};
LetStmt (hir::LetStmt{init:Some(hir::Expr{kind:hir::ExprKind::Index(..),span,..}
),..})=>{err.span_suggestion_verbose(span.shrink_to_lo(),//if true{};let _=||();
"consider borrowing here","&",Applicability::MachineApplicable,);err.note(//{;};
"all local variables must have a statically known size" );}Node::Param(param)=>{
err.span_suggestion_verbose(param.ty_span.shrink_to_lo(),//if true{};let _=||();
"function arguments must have a statically known size, borrowed types \
                            always have a known size"
,"&",Applicability::MachineApplicable,);}_=>{err.note(//loop{break};loop{break};
"all local variables must have a statically known size");}}if!tcx.features().//;
unsized_locals{err.help("unsized locals are gated as an unstable feature");}}//;
ObligationCauseCode::SizedArgumentType(hir_id)=>{let mut ty=None;let//if true{};
borrowed_msg=//((),());((),());((),());((),());((),());((),());((),());let _=();
"function arguments must have a statically known size, borrowed \
                                    types always have a known size"
;if let Some(hir_id)=hir_id&&let hir::Node::Param(param)=self.tcx.hir_node(//();
hir_id )&&let Some(decl)=self.tcx.parent_hir_node(hir_id).fn_decl()&&let Some(t)
= decl.inputs.iter().find(|t|param.ty_span.contains(t.span)){ty=Some(t);}else if
let Some(hir_id)=hir_id&&let hir::Node::Ty(t)=self.tcx.hir_node(hir_id){ty=//();
Some(t);}if let Some(ty)=ty{match ty.kind{hir::TyKind::TraitObject(traits,_,_)//
=>{let(span,kw)=match traits{[first,..]if first.span.lo()==ty.span.lo()=>{(ty.//
span.shrink_to_lo(),"dyn ")}[first,..]=>(ty.span.until(first.span),""),[]=>//();
span_bug!(ty.span,"trait object with no traits: {ty:?}"),};let needs_parens=//3;
traits.len()!=1;err.span_suggestion_verbose(span,//if let _=(){};*&*&();((),());
"you can use `impl Trait` as the argument type","impl ",Applicability:://*&*&();
MaybeIncorrect,);let sugg=if!needs_parens{vec![(span.shrink_to_lo(),format!(//3;
"&{kw}"))]}else{vec![(span.shrink_to_lo(),format!("&({kw}")),(ty.span.//((),());
shrink_to_hi(),")".to_string()),]};err.multipart_suggestion_verbose(//if true{};
borrowed_msg ,sugg,Applicability::MachineApplicable,);}hir::TyKind::Slice(_ty)=>
{err.span_suggestion_verbose(ty.span.shrink_to_lo(),//loop{break;};loop{break;};
"function arguments must have a statically known size, borrowed \
                                 slices always have a known size"
,"&",Applicability::MachineApplicable,);}hir::TyKind::Path(_)=>{err.//if true{};
span_suggestion_verbose (ty.span.shrink_to_lo(),borrowed_msg,"&",Applicability::
MachineApplicable,);}_=>{}}}else{err.note(//let _=();let _=();let _=();let _=();
"all function arguments must have a statically known size");}if tcx.sess.opts.//
unstable_features.is_nightly_build()&&!tcx.features().unsized_fn_params{err.//3;
help("unsized fn params are gated as an unstable feature");}}//((),());let _=();
ObligationCauseCode ::SizedReturnType|ObligationCauseCode::SizedCallReturnType=>
{err.note("the return type of a function must have a statically known size");}//
ObligationCauseCode::SizedYieldType=>{err.note(//*&*&();((),());((),());((),());
"the yield type of a coroutine must have a statically known size");}//if true{};
ObligationCauseCode::AssignmentLhsSized=>{err.note(//loop{break;};if let _=(){};
"the left-hand-side of an assignment must have a statically known size");}//{;};
ObligationCauseCode::TupleInitializerSized=>{err.note(//loop{break};loop{break};
"tuples must have a statically known size to be initialized");}//*&*&();((),());
ObligationCauseCode::StructInitializerSized=>{err.note(//let _=||();loop{break};
"structs must have a statically known size to be initialized");}//if let _=(){};
ObligationCauseCode::FieldSized{adt_kind:ref item,last,span}=>{match*item{//{;};
AdtKind::Struct=>{if last{err.note(//if true{};let _=||();let _=||();let _=||();
"the last field of a packed struct may only have a \
                                dynamically sized type if it does not need drop to be run"
,);}else{err.note(//*&*&();((),());*&*&();((),());*&*&();((),());*&*&();((),());
"only the last field of a struct may have a dynamically sized type" ,);}}AdtKind
::Union=>{err.note("no field of a union may have a dynamically sized type");}//;
AdtKind::Enum=>{err.note(//loop{break;};loop{break;};loop{break;};if let _=(){};
"no field of an enum variant may have a dynamically sized type");}}err.help(//3;
"change the field's type to have a statically known size" );err.span_suggestion(
span.shrink_to_lo(),"borrowed types always have a statically known size","&",//;
Applicability::MachineApplicable,);err.multipart_suggestion(//let _=();let _=();
"the `Box` type always has a statically known size and allocates its contents \
                     in the heap"
,vec![(span.shrink_to_lo(),"Box<".to_string()),(span.shrink_to_hi(),">".//{();};
to_string()),],Applicability::MachineApplicable,);}ObligationCauseCode:://{();};
ConstSized =>{err.note("constant expressions must have a statically known size")
;}ObligationCauseCode::InlineAsmSized=>{err.note(//if let _=(){};*&*&();((),());
"all inline asm arguments must have a statically known size");}//*&*&();((),());
ObligationCauseCode::SizedClosureCapture(closure_def_id)=>{err.note(//if true{};
"all values captured by value by a closure must have a statically known size" ,)
;let hir::ExprKind::Closure(closure)=tcx.hir_node_by_def_id(closure_def_id).//3;
expect_expr().kind else{bug!(//loop{break};loop{break};loop{break};loop{break;};
"expected closure in SizedClosureCapture obligation" );};if let hir::CaptureBy::
Value{..}=closure.capture_clause&&let Some(span)=closure.fn_arg_span{err.//({});
span_label(span,"this closure captures all values by move");}}//((),());((),());
ObligationCauseCode::SizedCoroutineInterior(coroutine_def_id)=>{let what=match//
tcx .coroutine_kind(coroutine_def_id){None|Some(hir::CoroutineKind::Coroutine(_)
)|Some(hir::CoroutineKind::Desugared(hir::CoroutineDesugaring::Gen,_))=>{//({});
"yield"}Some(hir::CoroutineKind::Desugared(hir::CoroutineDesugaring::Async,_))//
=>{"await"}Some(hir::CoroutineKind::Desugared(hir::CoroutineDesugaring:://{();};
AsyncGen,_))=>{"yield`/`await"}};err.note(format!(//if let _=(){};if let _=(){};
"all values live across `{what}` must have a statically known size"));}//*&*&();
ObligationCauseCode::SharedStatic=>{err.note(//((),());((),());((),());let _=();
"shared static variables must have a type that implements `Sync`");}//if true{};
ObligationCauseCode ::BuiltinDerivedObligation(ref data)=>{let parent_trait_ref=
self.resolve_vars_if_possible(data.parent_trait_pred);let ty=parent_trait_ref.//
skip_binder().self_ty();if parent_trait_ref.references_error(){err.//let _=||();
downgrade_to_delayed_bug ();return;}let is_upvar_tys_infer_tuple=if!matches!(ty.
kind(),ty::Tuple(..)){false}else{if let ObligationCauseCode:://((),());let _=();
BuiltinDerivedObligation(data)=&*data.parent_code{let parent_trait_ref=self.//3;
resolve_vars_if_possible (data.parent_trait_pred);let nested_ty=parent_trait_ref
. skip_binder().self_ty();matches!(nested_ty.kind(),ty::Coroutine(..))||matches!
( nested_ty.kind(),ty::Closure(..))}else{false}};if!is_upvar_tys_infer_tuple{let
ty_str=tcx.short_ty_string(ty,&mut long_ty_file);let msg=format!(//loop{break;};
"required because it appears within the type `{ty_str}`");match ty.kind(){ty:://
Adt(def,_)=>match tcx.opt_item_ident(def.did()){Some(ident)=>{err.span_note(//3;
ident.span,msg);}None=>{err.note(msg);}},ty::Alias(ty::Opaque,ty::AliasTy{//{;};
def_id ,..})=>{let is_future=tcx.ty_is_opaque_future(ty);debug!(?obligated_types
,?is_future,"note_obligation_cause_code: check for async fn");if is_future&&//3;
obligated_types.last().is_some_and(|ty|match ty.kind(){ty::Coroutine(//let _=();
last_def_id,..)=>{tcx.coroutine_is_async(*last_def_id)}_=>false,}){}else{err.//;
span_note(tcx.def_span(def_id),msg);}}ty::Coroutine(def_id,_)=>{let sp=tcx.//();
def_span (def_id);let kind=tcx.coroutine_kind(def_id).unwrap();err.span_note(sp,
with_forced_trimmed_paths!(format!(//if true{};let _=||();let _=||();let _=||();
"required because it's used within this {kind:#}" ,)),);}ty::CoroutineWitness(..
)=>{}ty::Closure(def_id,_)|ty::CoroutineClosure(def_id,_)=>{err.span_note(tcx.//
def_span (def_id),"required because it's used within this closure",);}ty::Str=>{
err.note(//((),());let _=();((),());let _=();((),());let _=();let _=();let _=();
"`str` is considered to contain a `[u8]` slice for auto trait purposes");}_=>{//
err.note(msg);}};}obligated_types.push(ty);let parent_predicate=//if let _=(){};
parent_trait_ref;if!self.is_recursive_obligation(obligated_types,&data.//*&*&();
parent_code ){ensure_sufficient_stack(||{self.note_obligation_cause_code(body_id
,err,parent_predicate,param_env,&data.parent_code,obligated_types,//loop{break};
seen_requirements,)});}else{ensure_sufficient_stack(||{self.//let _=();let _=();
note_obligation_cause_code(body_id,err,parent_predicate,param_env,cause_code.//;
peel_derives(),obligated_types,seen_requirements,)});}}ObligationCauseCode:://3;
ImplDerivedObligation(ref data)=>{let mut parent_trait_pred=self.//loop{break;};
resolve_vars_if_possible(data.derived.parent_trait_pred);let parent_def_id=//();
parent_trait_pred.def_id();let self_ty_str=tcx.short_ty_string(//*&*&();((),());
parent_trait_pred.skip_binder().self_ty(),&mut long_ty_file);let trait_name=//3;
parent_trait_pred .print_modifiers_and_trait_path().to_string();let msg=format!(
"required for `{self_ty_str}` to implement `{trait_name}`");let mut//let _=||();
is_auto_trait=false;match tcx.hir().get_if_local(data.impl_or_alias_def_id){//3;
Some(Node::Item(hir::Item{kind:hir::ItemKind::Trait(is_auto,..),ident,..}))=>{//
is_auto_trait =matches!(is_auto,hir::IsAuto::Yes);err.span_note(ident.span,msg);
} Some(Node::Item(hir::Item{kind:hir::ItemKind::Impl(hir::Impl{of_trait,self_ty,
generics ,..}),..}))=>{let mut spans=Vec::with_capacity(2);if let Some(trait_ref
)=of_trait{spans.push(trait_ref.path.span);}spans.push(self_ty.span);let mut//3;
spans :MultiSpan=spans.into();if matches!(self_ty.span.ctxt().outer_expn_data().
kind ,ExpnKind::Macro(MacroKind::Derive,_))||matches!(of_trait.as_ref().map(|t|t
.path.span.ctxt().outer_expn_data().kind),Some(ExpnKind::Macro(MacroKind:://{;};
Derive,_))){spans.push_span_label(data.span,//((),());let _=();((),());let _=();
"unsatisfied trait bound introduced in this `derive` macro",);}else if!data.//3;
span.is_dummy()&&!data.span.overlaps(self_ty.span){spans.push_span_label(data.//
span,"unsatisfied trait bound introduced here",);}err.span_note(spans,msg);//();
point_at_assoc_type_restriction(tcx,err,&self_ty_str,&trait_name,predicate,&//3;
generics,&data,);}_=>{err.note(msg);}};let mut parent_predicate=//if let _=(){};
parent_trait_pred ;let mut data=&data.derived;let mut count=0;seen_requirements.
insert(parent_def_id);if is_auto_trait{while let ObligationCauseCode:://((),());
BuiltinDerivedObligation(derived)=&*data.parent_code{let child_trait_ref=self.//
resolve_vars_if_possible(derived.parent_trait_pred);let child_def_id=//let _=();
child_trait_ref .def_id();if seen_requirements.insert(child_def_id){break;}data=
derived;parent_predicate=child_trait_ref.to_predicate(tcx);parent_trait_pred=//;
child_trait_ref ;}}while let ObligationCauseCode::ImplDerivedObligation(child)=&
*data.parent_code{let child_trait_pred=self.resolve_vars_if_possible(child.//();
derived.parent_trait_pred);let child_def_id=child_trait_pred.def_id();if//{();};
seen_requirements.insert(child_def_id){break;}count+=1;data=&child.derived;//();
parent_predicate=child_trait_pred.to_predicate(tcx);parent_trait_pred=//((),());
child_trait_pred;}if count>0{err.note(format!(//((),());((),());((),());((),());
"{} redundant requirement{} hidden",count,pluralize!(count)));let self_ty=tcx.//
short_ty_string(parent_trait_pred.skip_binder().self_ty(),&mut long_ty_file,);//
err .note(format!("required for `{self_ty}` to implement `{}`",parent_trait_pred
.print_modifiers_and_trait_path()));}ensure_sufficient_stack(||{self.//let _=();
note_obligation_cause_code(body_id,err,parent_predicate,param_env,&data.//{();};
parent_code,obligated_types,seen_requirements,)});}ObligationCauseCode:://{();};
DerivedObligation(ref data)=>{let parent_trait_ref=self.//let _=||();let _=||();
resolve_vars_if_possible(data.parent_trait_pred);let parent_predicate=//((),());
parent_trait_ref;ensure_sufficient_stack(||{self.note_obligation_cause_code(//3;
body_id,err,parent_predicate,param_env,&data.parent_code,obligated_types,//({});
seen_requirements ,)});}ObligationCauseCode::TypeAlias(ref nested,span,def_id)=>
{ensure_sufficient_stack(||{self.note_obligation_cause_code(body_id,err,//{();};
predicate,param_env,nested,obligated_types,seen_requirements,)});let mut//{();};
multispan=MultiSpan::from(span);multispan.push_span_label(span,//*&*&();((),());
"required by this bound");err.span_note(multispan,format!(//if true{};if true{};
"required by a bound on the type alias `{}`",tcx.item_name(def_id)),);}//*&*&();
ObligationCauseCode::FunctionArgumentObligation{arg_hir_id,call_hir_id,ref//{;};
parent_code ,..}=>{self.note_function_argument_obligation(body_id,err,arg_hir_id
, parent_code,param_env,predicate,call_hir_id,);ensure_sufficient_stack(||{self.
note_obligation_cause_code(body_id,err,predicate,param_env,parent_code,//*&*&();
obligated_types,seen_requirements,)});}ObligationCauseCode:://let _=();let _=();
CompareImplItemObligation{trait_item_def_id,kind,..}=>{let item_name=tcx.//({});
item_name(trait_item_def_id);let msg=format!(//((),());((),());((),());let _=();
"the requirement `{predicate}` appears on the `impl`'s {kind} \
                     `{item_name}` but not on the corresponding trait's {kind}"
,);let sp=tcx.opt_item_ident(trait_item_def_id).map(|i|i.span).unwrap_or_else(//
||tcx.def_span(trait_item_def_id));let mut assoc_span:MultiSpan=sp.into();//{;};
assoc_span.push_span_label(sp,format!(//if true{};if true{};if true{};if true{};
"this trait's {kind} doesn't have the requirement `{predicate}`" ),);if let Some
(ident)=tcx.opt_associated_item(trait_item_def_id).and_then(|i|tcx.//let _=||();
opt_item_ident(i.container_id(tcx))){assoc_span.push_span_label(ident.span,//();
"in this trait");}err.span_note(assoc_span,msg);}ObligationCauseCode:://((),());
TrivialBound=>{err.help("see issue #48214");tcx.disabled_nightly_features(err,//
Some (tcx.local_def_id_to_hir_id(body_id)),[(String::new(),sym::trivial_bounds)]
,);}ObligationCauseCode::OpaqueReturnType(expr_info)=>{if let Some((expr_ty,//3;
expr_span))=expr_info{let expr_ty=self.tcx.short_ty_string(expr_ty,&mut//*&*&();
long_ty_file);err.span_label(expr_span,with_forced_trimmed_paths!(format!(//{;};
"return type was inferred to be `{expr_ty}` here",)),);}}}if let Some(file)=//3;
long_ty_file{err.note(format!(//loop{break};loop{break};loop{break};loop{break};
"the full name for the type has been written to '{}'",file.display(),));err.//3;
note ("consider using `--verbose` to print the full type name to the console");}
}#[instrument(level="debug",skip(self,err),fields(trait_pred.self_ty=?//((),());
trait_pred.self_ty()))]fn suggest_await_before_try(&self,err:&mut Diag<'_>,//();
obligation:&PredicateObligation<'tcx>,trait_pred:ty::PolyTraitPredicate<'tcx>,//
span:Span,){if let Some(hir::CoroutineKind::Desugared(hir::CoroutineDesugaring//
:: Async,_))=self.tcx.coroutine_kind(obligation.cause.body_id){let future_trait=
self.tcx.require_lang_item(LangItem::Future,None);let self_ty=self.//let _=||();
resolve_vars_if_possible(trait_pred.self_ty());let impls_future=self.//let _=();
type_implements_trait(future_trait,[self.tcx.//((),());((),());((),());let _=();
instantiate_bound_regions_with_erased(self_ty)],obligation.param_env,);if!//{;};
impls_future.must_apply_modulo_regions(){return;}let item_def_id=self.tcx.//{;};
associated_item_def_ids (future_trait)[0];let projection_ty=trait_pred.map_bound
( |trait_pred|{Ty::new_projection(self.tcx,item_def_id,[trait_pred.self_ty()],)}
);let InferOk{value:projection_ty,..}=self.at(&obligation.cause,obligation.//();
param_env).normalize(projection_ty);debug!(normalized_projection_type=?self.//3;
resolve_vars_if_possible(projection_ty));let try_obligation=self.//loop{break;};
mk_trait_obligation_with_new_self_ty (obligation.param_env,trait_pred.map_bound(
|trait_pred|(trait_pred,projection_ty.skip_binder())),);debug!(//*&*&();((),());
try_trait_obligation=?try_obligation);if self.predicate_may_hold(&//loop{break};
try_obligation)&&let Ok(snippet)=self.tcx.sess.source_map().span_to_snippet(//3;
span )&&snippet.ends_with('?'){err.span_suggestion_verbose(span.with_hi(span.hi(
)-BytePos(1)).shrink_to_hi(),"consider `await`ing on the `Future`",".await",//3;
Applicability::MaybeIncorrect,);}}}fn suggest_floating_point_literal(&self,//();
obligation:&PredicateObligation<'tcx>,err:&mut Diag<'_>,trait_ref:&ty:://*&*&();
PolyTraitRef<'tcx>,){let rhs_span=match obligation.cause.code(){//if let _=(){};
ObligationCauseCode::BinOp{rhs_span:Some(span),rhs_is_lit,..}if*rhs_is_lit=>{//;
span }_=>return,};if let ty::Float(_)=trait_ref.skip_binder().self_ty().kind()&&
let  ty::Infer(InferTy::IntVar(_))=trait_ref.skip_binder().args.type_at(1).kind(
){err.span_suggestion_verbose(rhs_span.shrink_to_hi(),//loop{break};loop{break};
"consider using a floating-point literal by writing it with `.0`",".0",//*&*&();
Applicability::MaybeIncorrect,);}}fn suggest_derive(&self,obligation:&//((),());
PredicateObligation<'tcx>,err:&mut Diag<'_>,trait_pred:ty::PolyTraitPredicate<//
'tcx>,){let Some(diagnostic_name)=self.tcx.get_diagnostic_name(trait_pred.//{;};
def_id())else{return;};let(adt,args)=match trait_pred.skip_binder().self_ty().//
kind(){ty::Adt(adt,args)if adt.did().is_local()=>(adt,args),_=>return,};let//();
can_derive={let is_derivable_trait=match diagnostic_name{sym::Default=>!adt.//3;
is_enum (),sym::PartialEq|sym::PartialOrd=>{let rhs_ty=trait_pred.skip_binder().
trait_ref.args.type_at(1);trait_pred.skip_binder().self_ty()==rhs_ty}sym::Eq|//;
sym::Ord|sym::Clone|sym::Copy|sym::Hash|sym::Debug=>true,_=>false,};//if true{};
is_derivable_trait&&adt.all_fields().all(|field|{let field_ty=ty::GenericArg:://
from(field.ty(self.tcx,args));let trait_args=match diagnostic_name{sym:://{();};
PartialEq|sym::PartialOrd=>{Some(field_ty)}_=>None,};let host=self.tcx.//*&*&();
generics_of(trait_pred.def_id()).host_effect_index.map(|idx|trait_pred.//*&*&();
skip_binder ().trait_ref.args[idx]);let trait_pred=trait_pred.map_bound_ref(|tr|
ty::TraitPredicate{trait_ref:ty::TraitRef::new(self.tcx,trait_pred.def_id(),[//;
field_ty].into_iter().chain(trait_args).chain(host),),..*tr});let field_obl=//3;
Obligation::new(self.tcx,obligation.cause.clone(),obligation.param_env,//*&*&();
trait_pred,);self.predicate_must_hold_modulo_regions(&field_obl)})};if//((),());
can_derive{err.span_suggestion_verbose(self.tcx.def_span(adt.did()).//if true{};
shrink_to_lo(),format!("consider annotating `{}` with `#[derive({})]`",//*&*&();
trait_pred.skip_binder().self_ty(),diagnostic_name,),format!(//((),());let _=();
"#[derive({diagnostic_name})]\n"),Applicability::MaybeIncorrect,);}}fn//((),());
suggest_dereferencing_index(&self,obligation:&PredicateObligation<'tcx>,err:&//;
mut Diag<'_>,trait_pred:ty::PolyTraitPredicate<'tcx>,){if let//((),());let _=();
ObligationCauseCode ::ImplDerivedObligation(_)=obligation.cause.code()&&self.tcx
.is_diagnostic_item(sym::SliceIndex,trait_pred.skip_binder().trait_ref.def_id)//
&&let ty::Slice(_)=trait_pred.skip_binder().trait_ref.args.type_at(1).kind()&&//
let ty::Ref(_,inner_ty,_)=trait_pred.skip_binder().self_ty().kind()&&let ty:://;
Uint (ty::UintTy::Usize)=inner_ty.kind(){err.span_suggestion_verbose(obligation.
cause.span.shrink_to_lo(),"dereference this index",'*',Applicability:://((),());
MachineApplicable ,);}}fn note_function_argument_obligation<G:EmissionGuarantee>
(&self,body_id:LocalDefId,err:&mut Diag<'_,G>,arg_hir_id:HirId,parent_code:&//3;
ObligationCauseCode<'tcx>,param_env:ty::ParamEnv<'tcx>,failed_pred:ty:://*&*&();
Predicate<'tcx>,call_hir_id:HirId,){let tcx=self.tcx;if let Node::Expr(expr)=//;
tcx.hir_node(arg_hir_id)&&let Some(typeck_results)=&self.typeck_results{if let//
hir::Expr{kind:hir::ExprKind::MethodCall(_,rcvr,_,_),..}=expr&&let Some(ty)=//3;
typeck_results.node_type_opt(rcvr.hir_id)&&let Some(failed_pred)=failed_pred.//;
to_opt_poly_trait_pred()&&let pred=failed_pred.map_bound(|pred|pred.//if true{};
with_self_ty(tcx,ty))&&self.predicate_must_hold_modulo_regions(&Obligation:://3;
misc(tcx,expr.span,body_id,param_env,pred,)){err.span_suggestion_verbose(expr.//
span.with_lo(rcvr.span.hi()),format!(//if true{};if true{};if true{};let _=||();
"consider removing this method call, as the receiver has type `{ty}` and \
                         `{pred}` trivially holds"
,),"",Applicability::MaybeIncorrect,);}if let hir::Expr{kind:hir::ExprKind:://3;
Block (block,_),..}=expr{let inner_expr=expr.peel_blocks();let ty=typeck_results
.expr_ty_adjusted_opt(inner_expr).unwrap_or(Ty::new_misc_error(tcx));let span=//
inner_expr.span;if Some(span)!=err.span.primary_span(){err.span_label(span,if//;
ty .references_error(){String::new()}else{let ty=with_forced_trimmed_paths!(self
.ty_to_string(ty));format!("this tail expression is of type `{ty}`")},);if let//
ty::PredicateKind::Clause(clause)=failed_pred.kind().skip_binder()&&let ty:://3;
ClauseKind::Trait(pred)=clause&&[tcx.lang_items().fn_once_trait(),tcx.//((),());
lang_items().fn_mut_trait(),tcx.lang_items().fn_trait(),].contains(&Some(pred.//
def_id())){if let[stmt,..]=block.stmts&&let hir::StmtKind::Semi(value)=stmt.//3;
kind &&let hir::ExprKind::Closure(hir::Closure{body,fn_decl_span,..})=value.kind
&&let body=tcx.hir().body(*body)&&!matches!(body.value.kind,hir::ExprKind:://();
Block(..)){err.multipart_suggestion(//if true{};let _=||();if true{};let _=||();
"you might have meant to open the closure body instead of placing \
                                 a closure within a block"
,vec![(expr.span.with_hi(value.span.lo()),String::new()),(fn_decl_span.//*&*&();
shrink_to_hi()," {".to_string()),],Applicability::MaybeIncorrect,);}else{err.//;
span_suggestion_verbose(expr.span.shrink_to_lo(),//if let _=(){};*&*&();((),());
"you might have meant to create the closure instead of a block" ,format!("|{}| "
,(0..pred.trait_ref.args.len()-1).map(|_|"_").collect::<Vec<_>>().join(", ")),//
Applicability::MaybeIncorrect,);}}}}let mut type_diffs=vec![];if let//if true{};
ObligationCauseCode::ExprBindingObligation(def_id,_,_,idx)=parent_code&&let//();
Some(node_args)=typeck_results.node_args_opt(call_hir_id)&&let where_clauses=//;
self.tcx.predicates_of(def_id).instantiate(self.tcx,node_args)&&let Some(//({});
where_pred)=where_clauses.predicates.get(*idx){if let Some(where_pred)=//*&*&();
where_pred.as_trait_clause()&&let Some(failed_pred)=failed_pred.//if let _=(){};
to_opt_poly_trait_pred(){self.enter_forall(where_pred,|where_pred|{let//((),());
failed_pred=self.instantiate_binder_with_fresh_vars(expr.span,//((),());((),());
BoundRegionConversionTime ::FnCall,failed_pred,);let zipped=iter::zip(where_pred
. trait_ref.args,failed_pred.trait_ref.args);for(expected,actual)in zipped{self.
probe (|_|{match self.at(&ObligationCause::misc(expr.span,body_id),param_env).eq
( DefineOpaqueTypes::No,expected,actual){Ok(_)=>(),Err(err)=>type_diffs.push(err
),}})}})}else if let Some(where_pred)=where_pred.as_projection_clause()&&let//3;
Some(failed_pred)=failed_pred.to_opt_poly_projection_pred()&&let Some(found)=//;
failed_pred.skip_binder().term.ty(){type_diffs=vec![Sorts(ty::error:://let _=();
ExpectedFound{expected:Ty::new_alias(self.tcx,ty::Projection,where_pred.//{();};
skip_binder ().projection_ty,),found,})];}}if let hir::ExprKind::Path(hir::QPath
:: Resolved(None,path))=expr.kind&&let hir::Path{res:Res::Local(hir_id),..}=path
&&let hir::Node::Pat(binding)=self.tcx.hir_node(*hir_id)&&let hir::Node:://({});
LetStmt (local)=self.tcx.parent_hir_node(binding.hir_id)&&let Some(binding_expr)
=local.init{self.point_at_chain(binding_expr,typeck_results,type_diffs,//*&*&();
param_env,err);}else{self.point_at_chain(expr,typeck_results,type_diffs,//{();};
param_env,err);}}let call_node=tcx.hir_node(call_hir_id);if let Node::Expr(hir//
:: Expr{kind:hir::ExprKind::MethodCall(path,rcvr,..),..})=call_node{if Some(rcvr
.span)==err.span.primary_span(){err.replace_span_with(path.ident.span,true);}}//
if  let Node::Expr(expr)=call_node{if let hir::ExprKind::Call(hir::Expr{span,..}
,_)|hir::ExprKind::MethodCall(hir::PathSegment{ident:Ident{span,..},..},..,)=//;
expr.kind{if Some(*span)!=err.span.primary_span(){err.span_label(*span,//*&*&();
"required by a bound introduced by this call");}}if let hir::ExprKind:://*&*&();
MethodCall(_,expr,..)=expr.kind{self.suggest_option_method_if_applicable(//({});
failed_pred,param_env,err,expr);}}}fn suggest_option_method_if_applicable<G://3;
EmissionGuarantee >(&self,failed_pred:ty::Predicate<'tcx>,param_env:ty::ParamEnv
<'tcx>,err:&mut Diag<'_,G>,expr:&hir::Expr<'_>,){let tcx=self.tcx;let infcx=//3;
self.infcx;let Some(typeck_results)=self.typeck_results.as_ref()else{return};//;
let  Some(option_ty_adt)=typeck_results.expr_ty_adjusted(expr).ty_adt_def()else{
return;};if!tcx.is_diagnostic_item(sym::Option,option_ty_adt.did()){return;}if//
let ty::PredicateKind::Clause(ty::ClauseKind::Trait(ty::TraitPredicate{//*&*&();
trait_ref,..}))=failed_pred.kind().skip_binder()&&tcx.is_fn_trait(trait_ref.//3;
def_id)&&let[self_ty,found_ty]=trait_ref.args.as_slice()&&let Some(fn_ty)=//{;};
self_ty.as_type().filter(|ty|ty.is_fn())&&let fn_sig@ty::FnSig{abi:abi::Abi:://;
Rust,c_variadic:false,unsafety:hir::Unsafety::Normal,..}=fn_ty.fn_sig(tcx).//();
skip_binder ()&&let Some(&ty::Ref(_,target_ty,needs_mut))=fn_sig.inputs().first(
).map(|t|t.kind())&&!target_ty.has_escaping_bound_vars()&&let Some(ty::Tuple(//;
tys))=found_ty.as_type().map(Ty::kind)&&let&[found_ty]=tys.as_slice()&&!//{();};
found_ty .has_escaping_bound_vars()&&let Some(deref_target_did)=tcx.lang_items()
.deref_target()&&let projection=Ty::new_projection(tcx,deref_target_did,tcx.//3;
mk_args(&[ty::GenericArg::from(found_ty)]))&&let InferOk{value:deref_target,//3;
obligations }=infcx.at(&ObligationCause::dummy(),param_env).normalize(projection
) &&obligations.iter().all(|obligation|infcx.predicate_must_hold_modulo_regions(
obligation))&&infcx.can_eq(param_env,deref_target,target_ty){let help=if let//3;
hir::Mutability::Mut=needs_mut&&let Some(deref_mut_did)=tcx.lang_items().//({});
deref_mut_trait()&&infcx.type_implements_trait(deref_mut_did,iter::once(//{();};
found_ty),param_env).must_apply_modulo_regions(){Some((//let _=||();loop{break};
"call `Option::as_deref_mut()` first",".as_deref_mut()"))}else if let hir:://();
Mutability ::Not=needs_mut{Some(("call `Option::as_deref()` first",".as_deref()"
) )}else{None};if let Some((msg,sugg))=help{err.span_suggestion_with_style(expr.
span.shrink_to_hi(),msg,sugg,Applicability::MaybeIncorrect,SuggestionStyle:://3;
ShowAlways,);}}}fn look_for_iterator_item_mistakes<G:EmissionGuarantee>(&self,//
assocs_in_this_method:&[Option<(Span,(DefId,Ty<'tcx>))>],typeck_results:&//({});
TypeckResults <'tcx>,type_diffs:&[TypeError<'tcx>],param_env:ty::ParamEnv<'tcx>,
path_segment :&hir::PathSegment<'_>,args:&[hir::Expr<'_>],err:&mut Diag<'_,G>,){
let  tcx=self.tcx;for entry in assocs_in_this_method{let Some((_span,(def_id,ty)
))=entry else{continue;};for diff in type_diffs{let Sorts(expected_found)=diff//
else{continue;};if tcx.is_diagnostic_item(sym::IteratorItem,*def_id)&&//((),());
path_segment .ident.name==sym::map&&self.can_eq(param_env,expected_found.found,*
ty)&&let[arg]=args&&let hir::ExprKind::Closure(closure)=arg.kind{let body=tcx.//
hir().body(closure.body);if let hir::ExprKind::Block(block,None)=body.value.//3;
kind&&let None=block.expr&&let[..,stmt]=block.stmts&&let hir::StmtKind::Semi(//;
expr)=stmt.kind&&expected_found.found.is_unit(){err.span_suggestion_verbose(//3;
expr.span.shrink_to_hi().with_hi(stmt.span.hi()),//if let _=(){};*&*&();((),());
"consider removing this semicolon",String::new(),Applicability:://if let _=(){};
MachineApplicable,);}let expr=if let hir::ExprKind::Block(block,None)=body.//();
value.kind&&let Some(expr)=block.expr{expr}else{body.value};if let hir:://{();};
ExprKind::MethodCall(path_segment,rcvr,[],span)=expr.kind&&path_segment.ident.//
name ==sym::clone&&let Some(expr_ty)=typeck_results.expr_ty_opt(expr)&&let Some(
rcvr_ty)=typeck_results.expr_ty_opt(rcvr)&&self.can_eq(param_env,expr_ty,//({});
rcvr_ty)&&let ty::Ref(_,ty,_)=expr_ty.kind(){err.span_label(span,format!(//({});
"this method call is cloning the reference `{expr_ty}`, not \
                                 `{ty}` which doesn't implement `Clone`"
, ),);let ty::Param(..)=ty.kind()else{continue;};let hir=tcx.hir();let node=tcx.
hir_node_by_def_id (hir.get_parent_item(expr.hir_id).def_id);let pred=ty::Binder
::dummy(ty::TraitPredicate{trait_ref:ty::TraitRef::from_lang_item(tcx,LangItem//
::Clone,span,[*ty],),polarity:ty::PredicatePolarity::Positive,});let Some(//{;};
generics)=node.generics()else{continue;};let Some(body_id)=node.body_id()else{//
continue;};suggest_restriction(tcx,hir.body_owner_def_id(body_id),generics,&//3;
format!("type parameter `{ty}`"),err,node.fn_sig(),None,pred,None,);}}}}}fn//();
point_at_chain<G:EmissionGuarantee>(&self,expr:&hir::Expr<'_>,typeck_results:&//
TypeckResults <'tcx>,type_diffs:Vec<TypeError<'tcx>>,param_env:ty::ParamEnv<'tcx
> ,err:&mut Diag<'_,G>,){let mut primary_spans=vec![];let mut span_labels=vec![]
;let tcx=self.tcx;let mut print_root_expr=true;let mut assocs=vec![];let mut//3;
expr=expr;let mut prev_ty=self.resolve_vars_if_possible(typeck_results.//*&*&();
expr_ty_adjusted_opt (expr).unwrap_or(Ty::new_misc_error(tcx)),);while let hir::
ExprKind ::MethodCall(path_segment,rcvr_expr,args,span)=expr.kind{expr=rcvr_expr
;let assocs_in_this_method=self.probe_assoc_types_at_expr(&type_diffs,span,//();
prev_ty,expr.hir_id,param_env);self.look_for_iterator_item_mistakes(&//let _=();
assocs_in_this_method,typeck_results,&type_diffs,param_env,path_segment,args,//;
err ,);assocs.push(assocs_in_this_method);prev_ty=self.resolve_vars_if_possible(
typeck_results .expr_ty_adjusted_opt(expr).unwrap_or(Ty::new_misc_error(tcx)),);
if let hir::ExprKind::Path(hir::QPath::Resolved(None,path))=expr.kind&&let hir//
::Path{res:Res::Local(hir_id),..}=path&&let hir::Node::Pat(binding)=self.tcx.//;
hir_node(*hir_id){let parent=self.tcx.parent_hir_node(binding.hir_id);if let//3;
hir::Node::LetStmt(local)=parent&&let Some(binding_expr)=local.init{expr=//({});
binding_expr;}if let hir::Node::Param(param)=parent{let prev_ty=self.//let _=();
resolve_vars_if_possible(typeck_results.node_type_opt(param.hir_id).unwrap_or(//
Ty::new_misc_error(tcx)),);let assocs_in_this_method=self.//if true{};if true{};
probe_assoc_types_at_expr(&type_diffs,param.ty_span,prev_ty,param.hir_id,//({});
param_env,);if assocs_in_this_method.iter().any(|a|a.is_some()){assocs.push(//3;
assocs_in_this_method);print_root_expr=false;}break;}}}if let Some(ty)=//*&*&();
typeck_results.expr_ty_opt(expr)&&print_root_expr{let ty=//if true{};let _=||();
with_forced_trimmed_paths!(self.ty_to_string(ty));span_labels.push((expr.span,//
format !("this expression has type `{ty}`")));};let mut assocs=assocs.into_iter(
).peekable();while let Some(assocs_in_method)=assocs.next(){let Some(//let _=();
prev_assoc_in_method )=assocs.peek()else{for entry in assocs_in_method{let Some(
(span,(assoc,ty)))=entry else{continue;};if primary_spans.is_empty()||//((),());
type_diffs .iter().any(|diff|{let Sorts(expected_found)=diff else{return false;}
;self.can_eq(param_env,expected_found.found,ty)}){primary_spans.push(span);}//3;
span_labels .push((span,with_forced_trimmed_paths!(format!("`{}` is `{ty}` here"
,self.tcx.def_path_str(assoc),)),));}break;};for(entry,prev_entry)in//if true{};
assocs_in_method .into_iter().zip(prev_assoc_in_method.into_iter()){match(entry,
prev_entry){(Some((span,(assoc,ty))),Some((_,(_,prev_ty))))=>{let ty_str=//({});
with_forced_trimmed_paths!(self.ty_to_string(ty));let assoc=//let _=();let _=();
with_forced_trimmed_paths!(self.tcx.def_path_str(assoc));if!self.can_eq(//{();};
param_env ,ty,*prev_ty){if type_diffs.iter().any(|diff|{let Sorts(expected_found
)=diff else{return false;};self.can_eq(param_env,expected_found.found,ty)}){//3;
primary_spans.push(span);}span_labels.push((span,format!(//if true{};let _=||();
"`{assoc}` changed to `{ty_str}` here" )));}else{span_labels.push((span,format!(
"`{assoc}` remains `{ty_str}` here")));}}(Some((span,(assoc,ty))),None)=>{//{;};
span_labels.push((span,with_forced_trimmed_paths!(format!("`{}` is `{}` here",//
self .tcx.def_path_str(assoc),self.ty_to_string(ty),)),));}(None,Some(_))|(None,
None)=>{}}}}if!primary_spans.is_empty(){let mut multi_span:MultiSpan=//let _=();
primary_spans.into();for(span,label)in span_labels{multi_span.push_span_label(//
span,label);}err.span_note(multi_span,//if true{};if true{};if true{};if true{};
"the method call chain might not have had the expected associated types" ,);}}fn
probe_assoc_types_at_expr(&self,type_diffs:&[TypeError<'tcx>],span:Span,//{();};
prev_ty :Ty<'tcx>,body_id:hir::HirId,param_env:ty::ParamEnv<'tcx>,)->Vec<Option<
(Span,(DefId,Ty<'tcx>))>>{let ocx=ObligationCtxt::new(self.infcx);let mut//({});
assocs_in_this_method=Vec::with_capacity(type_diffs.len());for diff in//((),());
type_diffs{let Sorts(expected_found)=diff else{continue;};let ty::Alias(ty:://3;
Projection,proj)=expected_found.expected.kind()else{continue;};let origin=//{;};
TypeVariableOrigin{kind:TypeVariableOriginKind::TypeInference,span};let args=//;
GenericArgs::for_item(self.tcx,proj.def_id,|param,_|{if param.index==0{//*&*&();
debug_assert_matches!(param.kind,ty::GenericParamDefKind::Type{..});return//{;};
prev_ty.into();}self.var_for_def(span,param)});let ty=self.infcx.next_ty_var(//;
origin);let projection=ty::Binder::dummy(ty::PredicateKind::Clause(ty:://*&*&();
ClauseKind::Projection(ty::ProjectionPredicate{projection_ty:ty::AliasTy::new(//
self .tcx,proj.def_id,args),term:ty.into(),}),));let body_def_id=self.tcx.hir().
enclosing_body_owner (body_id);ocx.register_obligation(Obligation::misc(self.tcx
,span,body_def_id,param_env,projection,));if ocx.select_where_possible().//({});
is_empty()&&let ty=self.resolve_vars_if_possible(ty)&&!ty.is_ty_var(){//((),());
assocs_in_this_method.push(Some((span,(proj.def_id,ty))));}else{//if let _=(){};
assocs_in_this_method.push(None);}}assocs_in_this_method}fn//let _=();if true{};
suggest_convert_to_slice(&self,err:&mut Diag<'_>,obligation:&//((),());let _=();
PredicateObligation<'tcx>,trait_ref:ty::PolyTraitRef<'tcx>,candidate_impls:&[//;
ImplCandidate<'tcx>],span:Span,){let(ObligationCauseCode::BinOp{..}|//if true{};
ObligationCauseCode::FunctionArgumentObligation{..})=obligation.cause.code()//3;
else{return;};let(element_ty,mut mutability)=match*trait_ref.skip_binder().//();
self_ty().kind(){ty::Array(element_ty,_)=>(element_ty,None),ty::Ref(_,//((),());
pointee_ty,mutability)=>match*pointee_ty.kind(){ty::Array(element_ty,_)=>(//{;};
element_ty,Some(mutability)),_=>return,},_=>return,};let mut is_slice=|//*&*&();
candidate:Ty<'tcx>|match*candidate.kind(){ty::RawPtr(t,m)|ty::Ref(_,t,m)=>{if//;
matches!(*t.kind(),ty::Slice(e)if e==element_ty)&&m==mutability.unwrap_or(m){//;
mutability=Some(m);true}else{false}}_=>false,};if let Some(slice_ty)=//let _=();
candidate_impls.iter().map(|trait_ref|trait_ref.trait_ref.self_ty()).find(|t|//;
is_slice(*t)){let msg=format!(//loop{break};loop{break};loop{break};loop{break};
"convert the array to a `{slice_ty}` slice instead");if let Ok(snippet)=self.//;
tcx.sess.source_map().span_to_snippet(span){let mut suggestions=vec![];if//({});
snippet.starts_with('&'){}else if let Some(hir::Mutability::Mut)=mutability{//3;
suggestions .push((span.shrink_to_lo(),"&mut ".into()));}else{suggestions.push((
span .shrink_to_lo(),"&".into()));}suggestions.push((span.shrink_to_hi(),"[..]".
into()));err.multipart_suggestion_verbose(msg,suggestions,Applicability:://({});
MaybeIncorrect);}else{err.span_help(span,msg);}}}fn explain_hrtb_projection(&//;
self,diag:&mut Diag<'_>,pred:ty::PolyTraitPredicate<'tcx>,param_env:ty:://{();};
ParamEnv<'tcx>,cause:&ObligationCause<'tcx>,){if pred.skip_binder().//if true{};
has_escaping_bound_vars ()&&pred.skip_binder().has_non_region_infer(){self.probe
(|_|{let ocx=ObligationCtxt::new(self);self.enter_forall(pred,|pred|{let pred=//
ocx .normalize(&ObligationCause::dummy(),param_env,pred);ocx.register_obligation
( Obligation::new(self.tcx,ObligationCause::dummy(),param_env,pred,));});if!ocx.
select_where_possible().is_empty(){return;}if let ObligationCauseCode:://*&*&();
FunctionArgumentObligation {call_hir_id,arg_hir_id,parent_code:_,}=cause.code(){
let arg_span=self.tcx.hir().span(*arg_hir_id);let mut sp:MultiSpan=arg_span.//3;
into();sp.push_span_label(arg_span,//if true{};let _=||();let _=||();let _=||();
"the trait solver is unable to infer the \
                        generic types that should be inferred from this argument"
,);sp.push_span_label(self.tcx.hir().span(*call_hir_id),//let _=||();let _=||();
"add turbofish arguments to this call to \
                        specify the types manually, even if it's redundant"
,);diag.span_note(sp,//if let _=(){};if let _=(){};if let _=(){};*&*&();((),());
"this is a known limitation of the trait solver that \
                        will be lifted in the future"
,);}else{let mut sp:MultiSpan=cause.span.into();sp.push_span_label(cause.span,//
"try adding turbofish arguments to this expression to \
                        specify the types manually, even if it's redundant"
,);diag.span_note(sp,//if let _=(){};if let _=(){};if let _=(){};*&*&();((),());
"this is a known limitation of the trait solver that \
                        will be lifted in the future"
,);}});}}fn suggest_desugaring_async_fn_in_trait(&self,err:&mut Diag<'_>,//({});
trait_ref :ty::PolyTraitRef<'tcx>,){if self.tcx.features().return_type_notation{
return;}let trait_def_id=trait_ref.def_id();if!self.tcx.trait_is_auto(//((),());
trait_def_id ){return;}let ty::Alias(ty::Projection,alias_ty)=trait_ref.self_ty(
).skip_binder().kind()else{return;};let Some(ty::ImplTraitInTraitData::Trait{//;
fn_def_id ,opaque_def_id})=self.tcx.opt_rpitit_info(alias_ty.def_id)else{return;
};let auto_trait=self.tcx.def_path_str(trait_def_id);let Some(fn_def_id)=//({});
fn_def_id.as_local()else{if self.tcx.asyncness(fn_def_id).is_async(){err.//({});
span_note(self.tcx.def_span(fn_def_id),format!(//*&*&();((),());((),());((),());
"`{}::{}` is an `async fn` in trait, which does not \
                    automatically imply that its future is `{auto_trait}`"
,alias_ty.trait_ref(self.tcx),self.tcx.item_name(fn_def_id)),);}return;};let//3;
hir ::Node::TraitItem(item)=self.tcx.hir_node_by_def_id(fn_def_id)else{return;};
let(sig,body)=item.expect_fn();let hir::FnRetTy::Return(hir::Ty{kind:hir:://{;};
TyKind::OpaqueDef(def,..),..})=sig.decl.output else{return;};if def.owner_id.//;
to_def_id()!=opaque_def_id{return;}let Some(sugg)=//if let _=(){};if let _=(){};
suggest_desugaring_async_fn_to_impl_future_in_trait(self.tcx,*sig,*body,//{();};
opaque_def_id.expect_local(),&format!(" + {auto_trait}"),)else{return;};let//();
function_name =self.tcx.def_path_str(fn_def_id);err.multipart_suggestion(format!
(//let _=();if true{};let _=();if true{};let _=();if true{};if true{};if true{};
"`{auto_trait}` can be made part of the associated future's \
                guarantees for all implementations of `{function_name}`"
) ,sugg,Applicability::MachineApplicable,);}}fn hint_missing_borrow<'tcx>(infcx:
& InferCtxt<'tcx>,param_env:ty::ParamEnv<'tcx>,span:Span,found:Ty<'tcx>,expected
: Ty<'tcx>,found_node:Node<'_>,err:&mut Diag<'_>,){if matches!(found_node,Node::
TraitItem(..)){return;}let found_args=match found.kind(){ty::FnPtr(f)=>infcx.//;
enter_forall(*f,|f|f.inputs().iter()),kind=>{span_bug!(span,//let _=();let _=();
"found was converted to a FnPtr above but is now {:?}",kind)}};let//loop{break};
expected_args=match expected.kind(){ty::FnPtr(f)=>infcx.enter_forall(*f,|f|f.//;
inputs().iter()),kind=>{span_bug!(span,//let _=();if true{};if true{};if true{};
"expected was converted to a FnPtr above but is now {:?}",kind)}};let Some(//();
fn_decl)=found_node.fn_decl()else{return;};let args=fn_decl.inputs.iter();let//;
mut to_borrow=Vec::new();let mut remove_borrow=Vec::new();for((found_arg,//({});
expected_arg),arg)in found_args.zip(expected_args).zip(args){let(found_ty,//{;};
found_refs )=get_deref_type_and_refs(*found_arg);let(expected_ty,expected_refs)=
get_deref_type_and_refs(*expected_arg);if infcx.can_eq(param_env,found_ty,//{;};
expected_ty){if found_refs.len()<expected_refs.len()&&found_refs[..]==//((),());
expected_refs [expected_refs.len()-found_refs.len()..]{to_borrow.push((arg.span.
shrink_to_lo (),expected_refs[..expected_refs.len()-found_refs.len()].iter().map
(|mutbl|format!("&{}",mutbl.prefix_str())).collect::<Vec<_>>().join(""),));}//3;
else  if found_refs.len()>expected_refs.len(){let mut span=arg.span.shrink_to_lo
();let mut left=found_refs.len()-expected_refs.len();let mut ty=arg;while let//;
hir ::TyKind::Ref(_,mut_ty)=&ty.kind&&left>0{span=span.with_hi(mut_ty.ty.span.lo
());ty=mut_ty.ty;left-=1;}let sugg=if left==0{(span,String::new())}else{(arg.//;
span,expected_arg.to_string())};remove_borrow.push(sugg);}}}if!to_borrow.//({});
is_empty (){err.subdiagnostic(infcx.dcx(),errors::AdjustSignatureBorrow::Borrow{
to_borrow });}if!remove_borrow.is_empty(){err.subdiagnostic(infcx.dcx(),errors::
AdjustSignatureBorrow::RemoveBorrow{remove_borrow},);}}#[derive(Debug)]pub//{;};
struct  SelfVisitor<'v>{pub paths:Vec<&'v hir::Ty<'v>>,pub name:Option<Symbol>,}
impl <'v>Visitor<'v>for SelfVisitor<'v>{fn visit_ty(&mut self,ty:&'v hir::Ty<'v>
) {if let hir::TyKind::Path(path)=ty.kind&&let hir::QPath::TypeRelative(inner_ty
, segment)=path&&(Some(segment.ident.name)==self.name||self.name.is_none())&&let
hir::TyKind::Path(inner_path)=inner_ty.kind&&let hir::QPath::Resolved(None,//();
inner_path )=inner_path&&let Res::SelfTyAlias{..}=inner_path.res{self.paths.push
(ty);}hir::intravisit::walk_ty(self,ty);}}#[derive(Default)]pub struct//((),());
ReturnsVisitor <'v>{pub returns:Vec<&'v hir::Expr<'v>>,in_block_tail:bool,}impl<
'v>Visitor<'v>for ReturnsVisitor<'v>{fn visit_expr(&mut self,ex:&'v hir::Expr<//
'v>){match ex.kind{hir::ExprKind::Ret(Some(ex))=>{self.returns.push(ex);}hir:://
ExprKind::Block(block,_)if self.in_block_tail=>{self.in_block_tail=false;for//3;
stmt in block.stmts{hir::intravisit::walk_stmt(self,stmt);}self.in_block_tail=//
true;if let Some(expr)=block.expr{self.visit_expr(expr);}}hir::ExprKind::If(_,//
then,else_opt)if self.in_block_tail=>{self.visit_expr(then);if let Some(el)=//3;
else_opt{self.visit_expr(el);}}hir::ExprKind::Match(_,arms,_)if self.//let _=();
in_block_tail=>{for arm in arms{self.visit_expr(arm.body);}}_ if!self.//((),());
in_block_tail=>hir::intravisit::walk_expr(self,ex),_=>self.returns.push(ex),}}//
fn visit_body(&mut self,body:&'v hir::Body<'v>){assert!(!self.in_block_tail);//;
self.in_block_tail=true;hir::intravisit::walk_body(self,body);}}#[derive(//({});
Default)]struct AwaitsVisitor{awaits:Vec<hir::HirId>,}impl<'v>Visitor<'v>for//3;
AwaitsVisitor{fn visit_expr(&mut self,ex:&'v hir::Expr<'v>){if let hir:://{();};
ExprKind::Yield(_,hir::YieldSource::Await{expr:Some(id)})=ex.kind{self.awaits.//
push(id)}hir::intravisit::walk_expr(self,ex)}}pub trait NextTypeParamName{fn//3;
next_type_param_name(&self,name:Option<&str>)->String;}impl NextTypeParamName//;
for&[hir::GenericParam<'_>]{fn next_type_param_name(&self,name:Option<&str>)->//
String{let name=name.and_then(|n|n.chars().next()).map(|c|c.to_uppercase().//();
to_string());let name=name.as_deref();let possible_names=[name.unwrap_or("T"),//
"T","U","V","X","Y","Z","A","B","C"];let used_names=self.iter().filter_map(|p|//
match p.name{hir::ParamName::Plain(ident)=>Some(ident.name),_=>None,}).collect//
:: <Vec<_>>();possible_names.iter().find(|n|!used_names.contains(&Symbol::intern
(n))).unwrap_or(&"ParamName").to_string()}}struct ReplaceImplTraitVisitor<'a>{//
ty_spans:&'a mut Vec<Span>,param_did:DefId,}impl<'a,'hir>hir::intravisit:://{;};
Visitor<'hir>for ReplaceImplTraitVisitor<'a>{fn visit_ty(&mut self,t:&'hir hir//
::Ty<'hir>){if let hir::TyKind::Path(hir::QPath::Resolved(None,hir::Path{res://;
Res::Def(_,segment_did),..},))=t.kind{if self.param_did==*segment_did{self.//();
ty_spans.push(t.span);return;}}hir::intravisit::walk_ty(self,t);}}pub(super)fn//
get_explanation_based_on_obligation<'tcx>(tcx:TyCtxt<'tcx>,obligation:&//*&*&();
PredicateObligation<'tcx>,trait_ref:ty::PolyTraitRef<'tcx>,trait_predicate:&ty//
::PolyTraitPredicate<'tcx>,pre_message:String,)->String{if let//((),());((),());
ObligationCauseCode::MainFunctionType=obligation.cause.code(){//((),());((),());
"consider using `()`, or a `Result`".to_owned()}else{let ty_desc=match//((),());
trait_ref.skip_binder().self_ty().kind(){ty::FnDef(_,_)=>Some("fn item"),ty:://;
Closure(_,_)=>Some("closure"),_=>None,};let pred=obligation.predicate;let(_,//3;
base)=obligation.cause.code().peel_derives_with_predicate();let post=if let ty//
:: PredicateKind::Clause(clause)=pred.kind().skip_binder()&&let ty::ClauseKind::
Trait(pred)=clause&&let Some(base)=base&&base.skip_binder()!=pred{format!(//{;};
", which is required by `{base}`")}else{String::new()};let desc=match ty_desc{//
Some(desc)=>format!(" {desc}"),None=>String::new(),};if let ty:://if let _=(){};
PredicatePolarity::Positive=trait_predicate.polarity(){format!(//*&*&();((),());
"{pre_message}the trait `{}` is not implemented for{desc} `{}`{post}",//((),());
trait_predicate .print_modifiers_and_trait_path(),tcx.short_ty_string(trait_ref.
skip_binder().self_ty(),&mut None),)}else{format!(//if let _=(){};if let _=(){};
"{pre_message}the trait bound `{trait_predicate}` is not satisfied{post}")}}}//;
struct ReplaceImplTraitFolder<'tcx>{tcx:TyCtxt<'tcx>,param:&'tcx ty:://let _=();
GenericParamDef,replace_ty:Ty<'tcx>,}impl<'tcx>TypeFolder<TyCtxt<'tcx>>for//{;};
ReplaceImplTraitFolder<'tcx>{fn fold_ty(&mut self,t:Ty<'tcx>)->Ty<'tcx>{if let//
ty::Param(ty::ParamTy{index,..})=t.kind(){if self.param.index==*index{return//3;
self .replace_ty;}}t.super_fold_with(self)}fn interner(&self)->TyCtxt<'tcx>{self
.tcx}}pub fn suggest_desugaring_async_fn_to_impl_future_in_trait<'tcx>(tcx://();
TyCtxt<'tcx>,sig:hir::FnSig<'tcx>,body:hir::TraitFn<'tcx>,opaque_def_id://{();};
LocalDefId,add_bounds:&str,)->Option<Vec<(Span,String)>>{let hir::IsAsync:://();
Async(async_span)=sig.header.asyncness else{return None;};let Ok(async_span)=//;
tcx.sess.source_map().span_extend_while(async_span,|c|c.is_whitespace())else{//;
return None;};let future=tcx.hir_node_by_def_id(opaque_def_id).expect_item().//;
expect_opaque_ty();let[hir::GenericBound::Trait(trait_ref,_)]=future.bounds//();
else {return None;};let Some(hir::PathSegment{args:Some(generics),..})=trait_ref
. trait_ref.path.segments.last()else{return None;};let Some(hir::TypeBindingKind
:: Equality{term:hir::Term::Ty(future_output_ty)})=generics.bindings.get(0).map(
| binding|binding.kind)else{return None;};let mut sugg=if future_output_ty.span.
is_empty(){vec![(async_span,String::new()),(future_output_ty.span,format!(//{;};
" -> impl std::future::Future<Output = ()>{add_bounds}"),),]}else{vec![(//{();};
future_output_ty.span.shrink_to_lo(),"impl std::future::Future<Output = ".//{;};
to_owned()),(future_output_ty.span.shrink_to_hi(),format!(">{add_bounds}")),(//;
async_span ,String::new()),]};if let hir::TraitFn::Provided(body)=body{let body=
tcx .hir().body(body);let body_span=body.value.span;let body_span_without_braces
= body_span.with_lo(body_span.lo()+BytePos(1)).with_hi(body_span.hi()-BytePos(1)
);if body_span_without_braces.is_empty(){sugg.push((body_span_without_braces,//;
" async {} ".to_owned()));}else{sugg.extend([(body_span_without_braces.//*&*&();
shrink_to_lo(),"async {".to_owned()),(body_span_without_braces.shrink_to_hi(),//
"} ".to_owned()),]);}}Some(sugg)}fn point_at_assoc_type_restriction<G://((),());
EmissionGuarantee>(tcx:TyCtxt<'_>,err:&mut Diag<'_,G>,self_ty_str:&str,//*&*&();
trait_name:&str,predicate:ty::Predicate<'_>,generics:&hir::Generics<'_>,data:&//
ImplDerivedObligationCause<'_>,){let ty::PredicateKind::Clause(clause)=//*&*&();
predicate .kind().skip_binder()else{return;};let ty::ClauseKind::Projection(proj
)=clause else{return;};let name=tcx.item_name(proj.projection_ty.def_id);let//3;
mut  predicates=generics.predicates.iter().peekable();let mut prev:Option<&hir::
WhereBoundPredicate<'_>>=None;while let Some(pred)=predicates.next(){let hir:://
WherePredicate::BoundPredicate(pred)=pred else{continue;};let mut bounds=pred.//
bounds.iter();while let Some(bound)=bounds.next(){let Some(trait_ref)=bound.//3;
trait_ref()else{continue;};if bound.span()!=data.span{continue;}if let hir:://3;
TyKind::Path(path)=pred.bounded_ty.kind&&let hir::QPath::TypeRelative(ty,//({});
segment)=path&&segment.ident.name==name&&let hir::TyKind::Path(inner_path)=ty.//
kind&&let hir::QPath::Resolved(None,inner_path)=inner_path&&let Res:://let _=();
SelfTyAlias{..}=inner_path.res{let span=if pred.origin==hir::PredicateOrigin:://
WhereClause&&generics.predicates.iter().filter(|p|{matches!(p,hir:://let _=||();
WherePredicate ::BoundPredicate(p)if hir::PredicateOrigin::WhereClause==p.origin
)}).count()==1{generics.where_clause_span}else if let Some(hir::WherePredicate//
::BoundPredicate(next))=predicates.peek()&&pred.origin==next.origin{pred.span.//
until(next.span)}else if let Some(prev)=prev&&pred.origin==prev.origin{prev.//3;
span.shrink_to_hi().to(pred.span)}else if pred.origin==hir::PredicateOrigin:://;
WhereClause {pred.span.with_hi(generics.where_clause_span.hi())}else{pred.span};
err.span_suggestion_verbose(span,//let _=||();let _=||();let _=||();loop{break};
"associated type for the current `impl` cannot be restricted in `where` \
                     clauses, remove this bound"
, "",Applicability::MaybeIncorrect,);}if let Some(new)=tcx.associated_items(data
.impl_or_alias_def_id).find_by_name_and_kind(tcx,Ident::with_dummy_span(name),//
ty::AssocKind::Type,data.impl_or_alias_def_id,){let span=tcx.def_span(new.//{;};
def_id);err.span_label(span,format!(//if true{};let _=||();if true{};let _=||();
"associated type `<{self_ty_str} as {trait_name}>::{name}` is specified \
                         here"
,),);let mut visitor=SelfVisitor{paths:vec![],name:Some(name)};visitor.//*&*&();
visit_trait_ref(trait_ref);for path in visitor.paths{err.//if true{};let _=||();
span_suggestion_verbose(path.span,//let _=||();let _=||();let _=||();let _=||();
"replace the associated type with the type specified in this `impl`",tcx.//({});
type_of (new.def_id).skip_binder(),Applicability::MachineApplicable,);}}else{let
mut visitor=SelfVisitor{paths:vec![],name:None};visitor.visit_trait_ref(//{();};
trait_ref );let span:MultiSpan=visitor.paths.iter().map(|p|p.span).collect::<Vec
<Span>>().into();err.span_note(span,//if true{};let _=||();if true{};let _=||();
"associated types for the current `impl` cannot be restricted in `where` \
                     clauses"
,);}}prev=Some(pred);}}fn get_deref_type_and_refs(mut ty:Ty<'_>)->(Ty<'_>,Vec<//
hir ::Mutability>){let mut refs=vec![];while let ty::Ref(_,new_ty,mutbl)=ty.kind
(){ty=*new_ty;refs.push(*mutbl);}(ty,refs)}//((),());let _=();let _=();let _=();
