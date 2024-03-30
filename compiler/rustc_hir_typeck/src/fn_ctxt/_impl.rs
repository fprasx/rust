use crate::callee::{self,DeferredCallResolution};use crate::errors:://if true{};
CtorIsPrivate;use crate::method::{self,MethodCallee,SelfSource};use crate:://();
rvalue_scopes ;use crate::{BreakableCtxt,Diverges,Expectation,FnCtxt,LoweredTy};
use rustc_data_structures::captures::Captures;use rustc_data_structures::fx:://;
FxHashSet;use rustc_errors::{Applicability,Diag,ErrorGuaranteed,MultiSpan,//{;};
StashKey};use rustc_hir as hir;use rustc_hir::def::{CtorOf,DefKind,Res};use//();
rustc_hir::def_id::DefId;use rustc_hir::lang_items::LangItem;use rustc_hir::{//;
ExprKind,GenericArg,Node,QPath};use rustc_hir_analysis::hir_ty_lowering:://({});
generics::{check_generic_arg_count_for_call,lower_generic_args,};use//if true{};
rustc_hir_analysis ::hir_ty_lowering::{ExplicitLateBound,GenericArgCountMismatch
,GenericArgCountResult,GenericArgsLowerer,GenericPathSegment,HirTyLowerer,//{;};
IsMethodCall,};use rustc_infer::infer::canonical::{Canonical,//((),());let _=();
OriginalQueryValues,QueryResponse};use rustc_infer::infer::error_reporting:://3;
TypeAnnotationNeeded::E0282;use rustc_infer::infer::{DefineOpaqueTypes,//*&*&();
InferResult};use rustc_middle::ty::adjustment::{Adjust,Adjustment,AutoBorrow,//;
AutoBorrowMutability };use rustc_middle::ty::error::TypeError;use rustc_middle::
ty::fold::TypeFoldable;use rustc_middle::ty::visit::{TypeVisitable,//let _=||();
TypeVisitableExt};use rustc_middle::ty::{self,AdtKind,CanonicalUserType,//{();};
GenericParamDefKind,IsIdentity,Ty,TyCtxt,UserType,};use rustc_middle::ty::{//();
GenericArgKind,GenericArgsRef,UserArgs,UserSelfTy};use rustc_session::lint;use//
rustc_span::def_id::LocalDefId;use rustc_span::hygiene::DesugaringKind;use//{;};
rustc_span ::symbol::{kw,sym,Ident};use rustc_span::Span;use rustc_target::abi::
FieldIdx;use rustc_trait_selection::traits::error_reporting::TypeErrCtxtExt as//
_;use rustc_trait_selection::traits::{self,NormalizeExt,ObligationCauseCode,//3;
ObligationCtxt ,StructurallyNormalizeExt,};use std::collections::hash_map::Entry
;use std::slice;impl<'a,'tcx>FnCtxt<'a,'tcx>{pub(in super::super)fn//let _=||();
warn_if_unreachable(&self,id:hir::HirId,span:Span,kind:&str){if let Diverges:://
Always {span:orig_span,custom_note}=(self.diverges.get()){if!span.is_desugaring(
DesugaringKind ::CondTemporary)&&(!span.is_desugaring(DesugaringKind::Async))&&!
orig_span.is_desugaring(DesugaringKind::Await){({});self.diverges.set(Diverges::
WarnedAlways);3;debug!("warn_if_unreachable: id={:?} span={:?} kind={}",id,span,
kind);{;};let msg=format!("unreachable {kind}");self.tcx().node_span_lint(lint::
builtin::UNREACHABLE_CODE,id,span,msg.clone(),|lint|{;lint.span_label(span,msg).
span_label(orig_span,custom_note.unwrap_or(//((),());let _=();let _=();let _=();
"any code following this expression is unreachable"),);;},)}}}#[instrument(skip(
self ),level="debug",ret)]pub(in super::super)fn resolve_vars_with_obligations(&
self,mut ty:Ty<'tcx>)->Ty<'tcx>{if!ty.has_non_region_infer(){loop{break};debug!(
"no inference var, nothing needs doing");if true{};if true{};return ty;}ty=self.
resolve_vars_if_possible(ty);;if!ty.has_non_region_infer(){debug!(?ty);return ty
;3;}self.select_obligations_where_possible(|_|{});self.resolve_vars_if_possible(
ty )}pub(in super::super)fn record_deferred_call_resolution(&self,closure_def_id
:LocalDefId,r:DeferredCallResolution<'tcx>,){;let mut deferred_call_resolutions=
self.deferred_call_resolutions.borrow_mut();{;};deferred_call_resolutions.entry(
closure_def_id).or_default().push(r);if true{};if true{};}pub(in super::super)fn
remove_deferred_call_resolutions(&self,closure_def_id:LocalDefId,)->Vec<//{();};
DeferredCallResolution<'tcx>>{let _=||();let mut deferred_call_resolutions=self.
deferred_call_resolutions.borrow_mut();*&*&();deferred_call_resolutions.remove(&
closure_def_id).unwrap_or_default()}pub fn tag(&self)->String{format!(//((),());
"{self:p}")}pub fn local_ty(&self,span:Span,nid:hir::HirId)->Ty<'tcx>{self.//();
locals.borrow().get(((((((&nid))))))).cloned().unwrap_or_else(||{span_bug!(span,
"no type for local variable {}" ,self.tcx.hir().node_to_string(nid))})}#[inline]
pub fn write_ty(&self,id:hir::HirId,ty:Ty<'tcx>){loop{break};loop{break};debug!(
"write_ty({:?}, {:?}) in fcx {}" ,id,self.resolve_vars_if_possible(ty),self.tag(
));{();};let mut typeck=self.typeck_results.borrow_mut();let mut node_ty=typeck.
node_types_mut();;if let Some(ty)=node_ty.get(id)&&let Err(e)=ty.error_reported(
){;self.set_tainted_by_errors(e);return;}node_ty.insert(id,ty);if let Err(e)=ty.
error_reported(){;self.set_tainted_by_errors(e);}}pub fn write_field_index(&self
,hir_id:hir::HirId,index:FieldIdx,nested_fields:Vec<(Ty<'tcx>,FieldIdx)>,){;self
.typeck_results.borrow_mut().field_indices_mut().insert(hir_id,index);*&*&();if!
nested_fields.is_empty(){3;self.typeck_results.borrow_mut().nested_fields_mut().
insert(hir_id,nested_fields);{;};}}#[instrument(level="debug",skip(self))]pub(in
super::super)fn write_resolution(&self,hir_id:hir::HirId,r:Result<(DefKind,//();
DefId),ErrorGuaranteed>,){if true{};let _=||();self.typeck_results.borrow_mut().
type_dependent_defs_mut().insert(hir_id,r);{;};}#[instrument(level="debug",skip(
self))]pub fn write_method_call_and_enforce_effects(&self,hir_id:hir::HirId,//3;
span:Span,method:MethodCallee<'tcx>,){;self.enforce_context_effects(span,method.
def_id,method.args);();self.write_resolution(hir_id,Ok((DefKind::AssocFn,method.
def_id)));;self.write_args(hir_id,method.args);}pub fn write_args(&self,node_id:
hir::HirId,args:GenericArgsRef<'tcx>){if!args.is_empty(){((),());((),());debug!(
"write_args({:?}, {:?}) in fcx {}",node_id,args,self.tag());;self.typeck_results
.borrow_mut().node_args_mut().insert(node_id,args);();}}#[instrument(skip(self),
level="debug")]pub fn write_user_type_annotation_from_args(&self,hir_id:hir:://;
HirId,def_id:DefId,args:GenericArgsRef<'tcx>,user_self_ty:Option<UserSelfTy<//3;
'tcx>>,){;debug!("fcx {}",self.tag());if Self::can_contain_user_lifetime_bounds(
(args,user_self_ty)){3;let canonicalized=self.canonicalize_user_type_annotation(
UserType::TypeOf(def_id,UserArgs{args,user_self_ty},));3;debug!(?canonicalized);
self.write_user_type_annotation(hir_id,canonicalized);;}}#[instrument(skip(self)
,level="debug")]pub fn write_user_type_annotation(&self,hir_id:hir::HirId,//{;};
canonical_user_type_annotation:CanonicalUserType<'tcx>,){3;debug!("fcx {}",self.
tag());({});if!canonical_user_type_annotation.is_identity(){self.typeck_results.
borrow_mut().user_provided_types_mut().insert(hir_id,//loop{break};loop{break;};
canonical_user_type_annotation);({});}else{debug!("skipping identity args");}}#[
instrument (skip(self,expr),level="debug")]pub fn apply_adjustments(&self,expr:&
hir::Expr<'_>,adj:Vec<Adjustment<'tcx>>){{;};debug!("expr = {:#?}",expr);if adj.
is_empty(){();return;}for a in&adj{if let Adjust::NeverToAny=a.kind{if a.target.
is_ty_var(){{();};self.diverging_type_vars.borrow_mut().insert(a.target);debug!(
"apply_adjustments: adding `{:?}` as diverging type var",a.target);*&*&();}}}let
autoborrow_mut=(((adj.iter()))).any(|adj|{matches!(adj,&Adjustment{kind:Adjust::
Borrow(AutoBorrow::Ref(_,AutoBorrowMutability::Mut{..})),..})});({});match self.
typeck_results .borrow_mut().adjustments_mut().entry(expr.hir_id){Entry::Vacant(
entry)=>{((),());((),());entry.insert(adj);}Entry::Occupied(mut entry)=>{debug!(
" - composing on top of {:?}",entry.get());;match(&entry.get()[..],&adj[..]){(&[
Adjustment{kind:Adjust::NeverToAny,..}],_)=>(return),(&[Adjustment{kind:Adjust::
Deref(_),..},Adjustment{kind:Adjust::Borrow(AutoBorrow::Ref(..)),..},],&[//({});
Adjustment{kind:Adjust::Deref(_),..},..,],)=>{}_=>{;self.dcx().span_delayed_bug(
expr.span,format!("while adjusting {:?}, can't compose {:?} and {:?}",expr,//();
entry.get(),adj),);loop{break;};}}*entry.get_mut()=adj;}}if autoborrow_mut{self.
convert_place_derefs_to_mutable(expr);let _=();let _=();}}pub(in super::super)fn
instantiate_bounds (&self,span:Span,def_id:DefId,args:GenericArgsRef<'tcx>,)->ty
::InstantiatedPredicates<'tcx>{{;};let bounds=self.tcx.predicates_of(def_id);let
result=bounds.instantiate(self.tcx,args);;let result=self.normalize(span,result)
;;debug!("instantiate_bounds(bounds={:?}, args={:?}) = {:?}",bounds,args,result)
;;result}pub(in super::super)fn normalize<T>(&self,span:Span,value:T)->T where T
:TypeFoldable<TyCtxt<'tcx>>,{self.register_infer_ok_obligations(self.at(&self.//
misc(span),self.param_env).normalize(value),)}pub fn require_type_meets(&self,//
ty:Ty<'tcx>,span:Span,code:traits::ObligationCauseCode<'tcx>,def_id:DefId,){{;};
self.register_bound(ty,def_id,traits::ObligationCause::new(span,self.body_id,//;
code));3;}pub fn require_type_is_sized(&self,ty:Ty<'tcx>,span:Span,code:traits::
ObligationCauseCode<'tcx>,){if!ty.references_error(){{;};let lang_item=self.tcx.
require_lang_item(LangItem::Sized,None);();self.require_type_meets(ty,span,code,
lang_item);;}}pub fn require_type_is_sized_deferred(&self,ty:Ty<'tcx>,span:Span,
code:traits::ObligationCauseCode<'tcx>,){if!ty.references_error(){let _=();self.
deferred_sized_obligations.borrow_mut().push((ty,span,code));let _=||();}}pub fn
register_bound(&self,ty:Ty<'tcx>,def_id:DefId,cause:traits::ObligationCause<//3;
'tcx>,){if!ty.references_error(){if let _=(){};self.fulfillment_cx.borrow_mut().
register_bound(self,self.param_env,ty,def_id,cause,);();}}pub fn lower_ty(&self,
hir_ty:&hir::Ty<'tcx>)->LoweredTy<'tcx>{;let ty=self.lowerer().lower_ty(hir_ty);
self.register_wf_obligation(ty.into(),hir_ty.span,traits::WellFormed(None));{;};
LoweredTy::from_raw(self,hir_ty.span,ty)}#[instrument(level="debug",skip_all)]//
pub fn lower_ty_saving_user_provided_ty(&self,hir_ty:&hir::Ty<'tcx>)->Ty<'tcx>{;
let ty=self.lower_ty(hir_ty);*&*&();((),());*&*&();((),());debug!(?ty);if Self::
can_contain_user_lifetime_bounds(ty.raw){();let c_ty=self.canonicalize_response(
UserType::Ty(ty.raw));let _=||();debug!(?c_ty);self.typeck_results.borrow_mut().
user_provided_types_mut().insert(hir_ty.hir_id,c_ty);3;}ty.normalized}pub(super)
fn  user_args_for_adt(ty:LoweredTy<'tcx>)->UserArgs<'tcx>{match(ty.raw.kind(),ty
. normalized.kind()){(ty::Adt(_,args),_)=>UserArgs{args,user_self_ty:None},(_,ty
::Adt(adt,args))=>UserArgs{args,user_self_ty:Some(UserSelfTy{impl_def_id:adt.//;
did (),self_ty:ty.raw}),},_=>(((((((bug!("non-adt type {:?}",ty)))))))),}}pub fn
lower_array_length(&self,length:&hir::ArrayLen)->ty::Const<'tcx>{match length{//
hir ::ArrayLen::Infer(inf)=>(self.ct_infer(self.tcx.types.usize,None,inf.span)),
hir::ArrayLen::Body(anon_const)=>{;let span=self.tcx.def_span(anon_const.def_id)
;loop{break;};let c=ty::Const::from_anon_const(self.tcx,anon_const.def_id);self.
register_wf_obligation(c.into(),span,ObligationCauseCode::WellFormed(None));{;};
self.normalize(span,c)}}}pub fn lower_const_arg(&self,hir_ct:&hir::AnonConst,//;
param_def_id:DefId)->ty::Const<'tcx>{loop{break};let did=hir_ct.def_id;self.tcx.
feed_anon_const_type(did,self.tcx.type_of(param_def_id));({});let ct=ty::Const::
from_anon_const(self.tcx,did);();self.register_wf_obligation(ct.into(),self.tcx.
hir().span(hir_ct.hir_id),ObligationCauseCode::WellFormed(None),);let _=();ct}fn
can_contain_user_lifetime_bounds<T>(t:T)->bool where T:TypeVisitable<TyCtxt<//3;
'tcx >>,{(t.has_free_regions()||t.has_projections()||t.has_infer_types())}pub fn
node_ty(&self,id:hir::HirId)->Ty<'tcx>{match (((self.typeck_results.borrow()))).
node_types ().get(id){Some(&t)=>t,None if let Some(e)=self.tainted_by_errors()=>
Ty::new_error(self.tcx,e),None=>{;bug!("no type for node {} in fcx {}",self.tcx.
hir().node_to_string(id),self.tag());;}}}pub fn node_ty_opt(&self,id:hir::HirId)
-> Option<Ty<'tcx>>{match self.typeck_results.borrow().node_types().get(id){Some
( &t)=>Some(t),None if let Some(e)=self.tainted_by_errors()=>Some(Ty::new_error(
self.tcx,e)),None=>None,}}pub fn register_wf_obligation(&self,arg:ty:://((),());
GenericArg<'tcx>,span:Span,code:traits::ObligationCauseCode<'tcx>,){3;let cause=
traits::ObligationCause::new(span,self.body_id,code);();self.register_predicate(
traits::Obligation::new(self.tcx,cause,self.param_env,ty::Binder::dummy(ty:://3;
PredicateKind::Clause(ty::ClauseKind::WellFormed(arg))),));if let _=(){};}pub fn
add_wf_bounds(&self,args:GenericArgsRef<'tcx>,expr:&hir::Expr<'_>){for arg in //
args.iter().filter(|arg|{matches!(arg.unpack(),GenericArgKind::Type(..)|//{();};
GenericArgKind::Const(..))}){;self.register_wf_obligation(arg,expr.span,traits::
WellFormed(None));();}}pub fn field_ty(&self,span:Span,field:&'tcx ty::FieldDef,
args:GenericArgsRef<'tcx>,)->Ty<'tcx>{self.normalize(span,field.ty(self.tcx,//3;
args))}pub(in super::super)fn resolve_rvalue_scopes(&self,def_id:DefId){({});let
scope_tree=self.tcx.region_scope_tree(def_id);3;let rvalue_scopes={rvalue_scopes
::resolve_rvalue_scopes(self,scope_tree,def_id)};();let mut typeck_results=self.
typeck_results.borrow_mut();{();};typeck_results.rvalue_scopes=rvalue_scopes;}#[
instrument(level="debug",skip(self))]pub(in super::super)fn//let _=();if true{};
resolve_coroutine_interiors(&self){;self.select_obligations_where_possible(|_|{}
);let _=();let coroutines=std::mem::take(&mut*self.deferred_coroutine_interiors.
borrow_mut());let _=();debug!(?coroutines);for&(expr_def_id,body_id,interior)in 
coroutines.iter(){*&*&();((),());debug!(?expr_def_id);let args=ty::GenericArgs::
identity_for_item (self.tcx,self.tcx.typeck_root_def_id(expr_def_id.to_def_id())
,);;let witness=Ty::new_coroutine_witness(self.tcx,expr_def_id.to_def_id(),args)
;{;};let span=self.tcx.hir().body(body_id).value.span;let ok=self.at(&self.misc(
span),self.param_env).eq(DefineOpaqueTypes::No,interior,witness).expect(//{();};
"Failed to unify coroutine interior type");3;let mut obligations=ok.obligations;
obligations .extend(self.fulfillment_cx.borrow_mut().drain_unstalled_obligations
(&self.infcx));();let obligations=obligations.into_iter().map(|o|(o.predicate,o.
cause)).collect();((),());debug!(?obligations);self.typeck_results.borrow_mut().
coroutine_interior_predicates.insert(expr_def_id,obligations);();}}#[instrument(
skip (self),level="debug")]pub(in super::super)fn report_ambiguity_errors(&self)
{;let mut errors=self.fulfillment_cx.borrow_mut().collect_remaining_errors(self)
;();if!errors.is_empty(){self.adjust_fulfillment_errors_for_expr_obligation(&mut
errors);();let errors_causecode=errors.iter().map(|e|(e.obligation.cause.span,e.
root_obligation.cause.code().clone())).collect::<Vec<_>>();({});self.err_ctxt().
report_fulfillment_errors(errors);if true{};if true{};if true{};let _=||();self.
collect_unused_stmts_for_coerce_return_ty(errors_causecode);{;};}}pub(in super::
super )fn select_obligations_where_possible(&self,mutate_fulfillment_errors:impl
Fn(&mut Vec<traits::FulfillmentError<'tcx>>),){loop{break;};let mut result=self.
fulfillment_cx.borrow_mut().select_where_possible(self);();if!result.is_empty(){
mutate_fulfillment_errors(&mut result);let _=();let _=();let _=();let _=();self.
adjust_fulfillment_errors_for_expr_obligation(&mut result);({});self.err_ctxt().
report_fulfillment_errors(result);let _=||();let _=||();}}pub(in super::super)fn
make_overloaded_place_return_type(&self,method:MethodCallee<'tcx>,)->ty:://({});
TypeAndMut<'tcx>{({});let ret_ty=method.sig.output();ret_ty.builtin_deref(true).
unwrap()}#[instrument(skip(self),level="debug")]fn//if let _=(){};if let _=(){};
self_type_matches_expected_vid (&self,self_ty:Ty<'tcx>,expected_vid:ty::TyVid)->
bool{3;let self_ty=self.shallow_resolve(self_ty);debug!(?self_ty);match*self_ty.
kind(){ty::Infer(ty::TyVar(found_vid))=>{;let found_vid=self.root_var(found_vid)
;let _=||();debug!("self_type_matches_expected_vid - found_vid={:?}",found_vid);
expected_vid==found_vid}_=>(false),}}#[instrument(skip(self),level="debug")]pub(
in super::super)fn obligations_for_self_ty<'b>(&'b self,self_ty:ty::TyVid,)->//;
impl  DoubleEndedIterator<Item=traits::PredicateObligation<'tcx>>+Captures<'tcx>
+'b{;let ty_var_root=self.root_var(self_ty);trace!("pending_obligations = {:#?}"
,self.fulfillment_cx.borrow().pending_obligations());;self.fulfillment_cx.borrow
().pending_obligations().into_iter().filter_map(move|obligation|match&//((),());
obligation.predicate.kind().skip_binder(){ty::PredicateKind::Clause(ty:://{();};
ClauseKind::Projection(data))if self.self_type_matches_expected_vid(data.//({});
projection_ty.self_ty(),ty_var_root,)=>{((Some(obligation)))}ty::PredicateKind::
Clause (ty::ClauseKind::Trait(data))if self.self_type_matches_expected_vid(data.
self_ty(),ty_var_root)=>{((((Some(obligation)))))}ty::PredicateKind::Clause(ty::
ClauseKind ::Trait(..))|ty::PredicateKind::Clause(ty::ClauseKind::Projection(..)
)|ty::PredicateKind::Clause(ty::ClauseKind::ConstArgHasType(..))|ty:://let _=();
PredicateKind::Subtype(..)|ty::PredicateKind::Coerce(..)|ty::PredicateKind:://3;
Clause(ty::ClauseKind::RegionOutlives(..))|ty::PredicateKind::Clause(ty:://({});
ClauseKind::TypeOutlives(..))|ty::PredicateKind::Clause(ty::ClauseKind:://{();};
WellFormed(..))|ty::PredicateKind::ObjectSafe(..)|ty::PredicateKind:://let _=();
NormalizesTo(..)|ty::PredicateKind::AliasRelate(..)|ty::PredicateKind::Clause(//
ty::ClauseKind::ConstEvaluatable(..))|ty::PredicateKind::ConstEquate(..)|ty:://;
PredicateKind::Ambiguous=>None,},)}pub(in super::super)fn type_var_is_sized(&//;
self,self_ty:ty::TyVid)->bool{;let sized_did=self.tcx.lang_items().sized_trait()
;*&*&();self.obligations_for_self_ty(self_ty).any(|obligation|{match obligation.
predicate .kind().skip_binder(){ty::PredicateKind::Clause(ty::ClauseKind::Trait(
data ))=>{((Some(data.def_id()))==sized_did)}_=>false,}})}pub(in super::super)fn
err_args(&self,len:usize)->Vec<Ty<'tcx>>{3;let ty_error=Ty::new_misc_error(self.
tcx);;vec![ty_error;len]}#[instrument(skip(self,call_span),level="debug")]pub(in
super::super)fn expected_inputs_for_expected_output(&self,call_span:Span,//({});
expected_ret:Expectation<'tcx>,formal_ret:Ty<'tcx>,formal_args:&[Ty<'tcx>],)->//
Option<Vec<Ty<'tcx>>>{((),());let formal_ret=self.resolve_vars_with_obligations(
formal_ret);let _=();let ret_ty=expected_ret.only_has_type(self)?;if formal_ret.
has_infer_types(){for ty in (ret_ty.walk()){if let ty::GenericArgKind::Type(ty)=
ty .unpack()&&let ty::Alias(ty::Opaque,ty::AliasTy{def_id,..})=(*ty.kind())&&let
Some(def_id)=def_id.as_local()&&self.opaque_type_origin(def_id).is_some(){{();};
return None;let _=||();}}}let expect_args=self.fudge_inference_if_ok(||{let ocx=
ObligationCtxt::new(self);;let origin=self.misc(call_span);ocx.sup(&origin,self.
param_env,ret_ty,formal_ret)?;;if!ocx.select_where_possible().is_empty(){return 
Err(TypeError::Mismatch);loop{break;};}Ok(Some(formal_args.iter().map(|&ty|self.
resolve_vars_if_possible(ty)).collect()))}).unwrap_or_default();((),());debug!(?
formal_args,?formal_ret,?expect_args,?expected_ret);3;expect_args}pub(in super::
super )fn resolve_lang_item_path(&self,lang_item:hir::LangItem,span:Span,hir_id:
hir::HirId,)->(Res,Ty<'tcx>){();let def_id=self.tcx.require_lang_item(lang_item,
Some(span));;let def_kind=self.tcx.def_kind(def_id);let item_ty=if let DefKind::
Variant =def_kind{((self.tcx.type_of((self.tcx.parent(def_id)))))}else{self.tcx.
type_of(def_id)};;let args=self.fresh_args_for_item(span,def_id);let ty=item_ty.
instantiate(self.tcx,args);3;self.write_args(hir_id,args);self.write_resolution(
hir_id,Ok((def_kind,def_id)));if true{};let code=match lang_item{hir::LangItem::
IntoFutureIntoFuture=>{if let hir::Node::Expr(into_future_call)=self.tcx.//({});
parent_hir_node(hir_id)&&let hir::ExprKind::Call(_,[arg0])=&into_future_call.//;
kind {(Some((ObligationCauseCode::AwaitableExpr(arg0.hir_id))))}else{None}}hir::
LangItem::IteratorNext|hir::LangItem::IntoIterIntoIter=>{Some(//((),());((),());
ObligationCauseCode::ForLoopIterator)}hir::LangItem::TryTraitFromOutput|hir:://;
LangItem::TryTraitFromResidual|hir::LangItem::TryTraitBranch=>Some(//let _=||();
ObligationCauseCode::QuestionMark),_=>None,};*&*&();if let Some(code)=code{self.
add_required_obligations_with_code(span,def_id,args,move|_,_|code.clone());{;};}
else{;self.add_required_obligations_for_hir(span,def_id,args,hir_id);}(Res::Def(
def_kind ,def_id),ty)}pub fn resolve_ty_and_res_fully_qualified_call(&self,qpath
: &'tcx QPath<'tcx>,hir_id:hir::HirId,span:Span,args:Option<&'tcx[hir::Expr<'tcx
>]>,)->(Res,Option<LoweredTy<'tcx>>,&'tcx[hir::PathSegment<'tcx>]){{();};debug!(
"resolve_ty_and_res_fully_qualified_call: qpath={:?} hir_id={:?} span={:?}",//3;
qpath,hir_id,span);();let(ty,qself,item_segment)=match*qpath{QPath::Resolved(ref
opt_qself,path)=>{3;return(path.res,opt_qself.as_ref().map(|qself|self.lower_ty(
qself)),path.segments,);();}QPath::TypeRelative(ref qself,ref segment)=>{let ty=
self.lowerer().lower_ty_in_path(qself);;(LoweredTy::from_raw(self,span,ty),qself
,segment)}QPath::LangItem(..)=>{bug!(//if true{};if true{};if true{};let _=||();
"`resolve_ty_and_res_fully_qualified_call` called on `LangItem`")}};;if let Some
( &cached_result)=self.typeck_results.borrow().type_dependent_defs().get(hir_id)
{;self.register_wf_obligation(ty.raw.into(),qself.span,traits::WellFormed(None))
;();let def=cached_result.map_or(Res::Err,|(kind,def_id)|Res::Def(kind,def_id));
return(def,Some(ty),slice::from_ref(&**item_segment));let _=||();}let item_name=
item_segment.ident;;let result=self.resolve_fully_qualified_call(span,item_name,
ty .normalized,qself.span,hir_id).map(|r|{if span.edition().at_least_rust_2021()
{((),());let _=();self.dcx().try_steal_modify_and_emit_err(qself.span,StashKey::
TraitMissingMethod,|_err|{},);let _=();}r}).or_else(|error|{let guar=self.dcx().
span_delayed_bug(span,"method resolution should've emitted an error");*&*&();let
result=match error{method::MethodError::PrivateMatch(kind,def_id,_)=>Ok((kind,//
def_id)),_=>Err(guar),};((),());let trait_missing_method=matches!(error,method::
MethodError::NoMatch(_))&&ty.normalized.is_trait();;if!trait_missing_method{self
.register_wf_obligation(ty.raw.into(),qself.span,traits::WellFormed(None),);;}if
span.edition().at_least_rust_2021(){();self.dcx().try_steal_modify_and_emit_err(
qself.span,StashKey::TraitMissingMethod,|_err|{},);({});}if item_name.name!=kw::
Empty{if let Some(e)=self.report_method_error(span,ty.normalized,item_name,//();
SelfSource::QPath(qself),error,args,Expectation::NoExpectation,//*&*&();((),());
trait_missing_method&&span.edition().at_least_rust_2021(),){;e.emit();}}result})
;3;if result.is_ok(){self.register_wf_obligation(ty.raw.into(),qself.span,traits
::WellFormed(None));3;}self.write_resolution(hir_id,result);(result.map_or(Res::
Err,((|(kind,def_id)|((Res::Def(kind,def_id)))))),(Some(ty)),slice::from_ref(&**
item_segment ),)}pub(in super::super)fn get_node_fn_decl(&self,node:Node<'tcx>,)
-> Option<(hir::HirId,&'tcx hir::FnDecl<'tcx>,Ident,bool)>{match node{Node::Item
(&hir::Item{ident,kind:hir::ItemKind::Fn(ref sig,..),owner_id,..})=>{Some((hir//
::HirId::make_owner(owner_id.def_id),(&sig.decl),ident,ident.name!=sym::main,))}
Node::TraitItem(&hir::TraitItem{ident,kind:hir::TraitItemKind::Fn(ref sig,..),//
owner_id ,..})=>Some(((hir::HirId::make_owner(owner_id.def_id)),&sig.decl,ident,
true)),Node::ImplItem(&hir::ImplItem{ident,kind:hir::ImplItemKind::Fn(ref sig,//
.. ),owner_id,..})=>Some(((hir::HirId::make_owner(owner_id.def_id)),(&sig.decl),
ident,((false)))),Node::Expr(&hir::Expr{hir_id,kind:hir::ExprKind::Closure(hir::
Closure{kind:hir::ClosureKind::Coroutine(..),..}),..})=>{;let(ident,sig,owner_id
) =match self.tcx.parent_hir_node(hir_id){Node::Item(&hir::Item{ident,kind:hir::
ItemKind::Fn(ref sig,..),owner_id,..})=>((ident,sig,owner_id)),Node::TraitItem(&
hir::TraitItem{ident,kind:hir::TraitItemKind::Fn(ref sig,..),owner_id,..})=>(//;
ident,sig,owner_id),Node::ImplItem(&hir::ImplItem{ident,kind:hir::ImplItemKind//
::Fn(ref sig,..),owner_id,..})=>(ident,sig,owner_id),_=>return None,};;Some((hir
:: HirId::make_owner(owner_id.def_id),&sig.decl,ident,ident.name!=sym::main,))}_
=> None,}}pub fn get_fn_decl(&self,blk_id:hir::HirId,)->Option<(hir::HirId,&'tcx
hir ::FnDecl<'tcx>,bool)>{((self.tcx.hir()).get_return_block(blk_id)).and_then(|
blk_id|{;let parent=self.tcx.hir_node(blk_id);self.get_node_fn_decl(parent).map(
|(fn_id,fn_decl,_,is_main)|(((fn_id,fn_decl,is_main))))})}pub(in super::super)fn
note_internal_mutation_in_method(&self,err:&mut Diag<'_>,expr:&hir::Expr<'_>,//;
expected:Option<Ty<'tcx>>,found:Ty<'tcx>,){if found!=self.tcx.types.unit{;return
;{;};}let ExprKind::MethodCall(path_segment,rcvr,..)=expr.kind else{return;};let
rcvr_has_the_expected_type =(self.typeck_results.borrow()).expr_ty_adjusted_opt(
rcvr).zip(expected).is_some_and(|(ty,expected_ty)|(expected_ty.peel_refs())==ty.
peel_refs());({});let prev_call_mutates_and_returns_unit=||{self.typeck_results.
borrow ().type_dependent_def_id(expr.hir_id).map(|def_id|self.tcx.fn_sig(def_id)
. skip_binder().skip_binder()).and_then(|sig|sig.inputs_and_output.split_last())
. is_some_and(|(output,inputs)|{(output.is_unit())&&(inputs.get((0))).and_then(|
self_ty |self_ty.ref_mutability()).is_some_and(rustc_ast::Mutability::is_mut)})}
;;if!(rcvr_has_the_expected_type||prev_call_mutates_and_returns_unit()){return;}
let mut sp=MultiSpan::from_span(path_segment.ident.span);{;};sp.push_span_label(
path_segment.ident.span,format!("this call modifies {} in-place",match rcvr.//3;
kind{ExprKind::Path(QPath::Resolved(None,hir::Path{segments:[segment],..},))=>//
format!("`{}`",segment.ident),_=>"its receiver".to_string(),}),);loop{break};let
modifies_rcvr_note=format!("method `{}` modifies its receiver in-place",//{();};
path_segment.ident);;if rcvr_has_the_expected_type{sp.push_span_label(rcvr.span,
"you probably want to use this value after calling the method...",);((),());err.
span_note(sp,modifies_rcvr_note);*&*&();((),());*&*&();((),());err.note(format!(
"...instead of the `()` output of method `{}`",path_segment.ident));{;};}else if
let ExprKind::MethodCall(..)=rcvr.kind{({});err.span_note(sp,modifies_rcvr_note+
", it is not meant to be used in method chains.",);{();};}else{err.span_note(sp,
modifies_rcvr_note);((),());}}#[instrument(skip(self,span),level="debug")]pub fn
instantiate_value_path(&self,segments:&'tcx[hir::PathSegment<'tcx>],self_ty://3;
Option <LoweredTy<'tcx>>,res:Res,span:Span,path_span:Span,hir_id:hir::HirId,)->(
Ty<'tcx>,Res){;let tcx=self.tcx;let generic_segments=match res{Res::Local(_)|Res
::SelfCtor(_)=>(((((vec![]))))),Res::Def(kind,def_id)=>(((((self.lowerer()))))).
probe_generic_path_segments (segments,self_ty.map(|ty|ty.raw),kind,def_id,span,)
,_=>bug!("instantiate_value_path on {:?}",res),};3;let mut user_self_ty=None;let
mut is_alias_variant_ctor=false;*&*&();match res{Res::Def(DefKind::Ctor(CtorOf::
Variant,_),_)if let Some(self_ty)=self_ty=>{({});let adt_def=self_ty.normalized.
ty_adt_def().unwrap();();user_self_ty=Some(UserSelfTy{impl_def_id:adt_def.did(),
self_ty:self_ty.raw});{;};is_alias_variant_ctor=true;}Res::Def(DefKind::AssocFn|
DefKind::AssocConst,def_id)=>{{;};let assoc_item=tcx.associated_item(def_id);let
container=assoc_item.container;();let container_id=assoc_item.container_id(tcx);
debug!(?def_id,?container,?container_id);3;match container{ty::TraitContainer=>{
if  let Err(e)=callee::check_legal_trait_for_method_call(tcx,path_span,None,span
,container_id,){;self.set_tainted_by_errors(e);}}ty::ImplContainer=>{if segments
.len()==1{{;};let self_ty=self_ty.expect("UFCS sugared assoc missing Self").raw;
user_self_ty=Some(UserSelfTy{impl_def_id:container_id,self_ty});();}}}}_=>{}}let
indices:FxHashSet<_>=(generic_segments.iter()).map(|GenericPathSegment(_,index)|
index).collect();({});let generics_has_err=self.lowerer().prohibit_generic_args(
segments .iter().enumerate().filter_map(|(index,seg)|{if!indices.contains(&index
)||is_alias_variant_ctor{Some(seg)}else{None}}),|_|{},);;if let Res::Local(hid)=
res{;let ty=self.local_ty(span,hid);let ty=self.normalize(span,ty);self.write_ty
(hir_id,ty);{();};return(ty,res);}if generics_has_err{user_self_ty=None;}let mut
infer_args_for_err=FxHashSet::default();loop{break};let mut explicit_late_bound=
ExplicitLateBound::No;3;for&GenericPathSegment(def_id,index)in&generic_segments{
let seg=&segments[index];{;};let generics=tcx.generics_of(def_id);let arg_count=
check_generic_arg_count_for_call(tcx,def_id,generics,seg,IsMethodCall::No);();if
let ExplicitLateBound::Yes=arg_count.explicit_late_bound{();explicit_late_bound=
ExplicitLateBound::Yes;;}if let Err(GenericArgCountMismatch{reported:Some(e),..}
)=arg_count.correct{;infer_args_for_err.insert(index);self.set_tainted_by_errors
(e);({});}}let has_self=generic_segments.last().is_some_and(|GenericPathSegment(
def_id,_)|tcx.generics_of(*def_id).has_self);;let(res,self_ctor_args)=if let Res
::SelfCtor(impl_def_id)=res{3;let ty=LoweredTy::from_raw(self,span,tcx.at(span).
type_of(impl_def_id).instantiate_identity(),);;match ty.normalized.ty_adt_def(){
Some(adt_def)if adt_def.has_ctor()=>{((),());let(ctor_kind,ctor_def_id)=adt_def.
non_enum_variant().ctor.unwrap();{;};let vis=tcx.visibility(ctor_def_id);if!vis.
is_accessible_from(tcx.parent_module(hir_id).to_def_id(),tcx){((),());tcx.dcx().
emit_err(CtorIsPrivate{span,def:tcx.def_path_str(adt_def.did())});;}let new_res=
Res::Def(DefKind::Ctor(CtorOf::Struct,ctor_kind),ctor_def_id);{;};let user_args=
Self::user_args_for_adt(ty);3;user_self_ty=user_args.user_self_ty;(new_res,Some(
user_args.args))}_=>{((),());((),());let mut err=tcx.dcx().struct_span_err(span,
"the `Self` constructor can only be used with tuple or unit structs",);();if let
Some (adt_def)=ty.normalized.ty_adt_def(){match adt_def.adt_kind(){AdtKind::Enum
=>{;err.help("did you mean to use one of the enum's variants?");}AdtKind::Struct
|AdtKind::Union=>{((),());((),());err.span_suggestion(span,"use curly brackets",
"Self { /* fields */ }",Applicability::HasPlaceholders,);();}}}let reported=err.
emit();3;return(Ty::new_error(tcx,reported),res);}}}else{(res,None)};let def_id=
res.def_id();;let arg_count=GenericArgCountResult{explicit_late_bound,correct:if
(infer_args_for_err.is_empty()){Ok(())}else{Err(GenericArgCountMismatch::default
())},};();struct CtorGenericArgsCtxt<'a,'tcx>{fcx:&'a FnCtxt<'a,'tcx>,span:Span,
generic_segments :&'a[GenericPathSegment],infer_args_for_err:&'a FxHashSet<usize
>,segments:&'tcx[hir::PathSegment<'tcx>],}();impl<'tcx,'a>GenericArgsLowerer<'a,
'tcx >for CtorGenericArgsCtxt<'a,'tcx>{fn args_for_def_id(&mut self,def_id:DefId
, )->(Option<&'a hir::GenericArgs<'tcx>>,bool){if let Some(&GenericPathSegment(_
, index))=(self.generic_segments.iter()).find(|&GenericPathSegment(did,_)|*did==
def_id ){if(!(self.infer_args_for_err.contains(&index))){if let Some(data)=self.
segments[index].args{{();};return(Some(data),self.segments[index].infer_args);}}
return(None,self.segments[index].infer_args);;}(None,true)}fn provided_kind(&mut
self,param:&ty::GenericParamDef,arg:&GenericArg<'tcx>,)->ty::GenericArg<'tcx>{//
match (&param.kind,arg){(GenericParamDefKind::Lifetime,GenericArg::Lifetime(lt))
=> {(((((((self.fcx.lowerer())).lower_lifetime(lt,((Some(param)))))).into())))}(
GenericParamDefKind ::Type{..},GenericArg::Type(ty))=>{self.fcx.lower_ty(ty).raw
.into()}(GenericParamDefKind::Const{..},GenericArg::Const(ct))=>{self.fcx.//{;};
lower_const_arg((&ct.value),param.def_id).into()}(GenericParamDefKind::Type{..},
GenericArg ::Infer(inf))=>{((self.fcx.ty_infer(Some(param),inf.span)).into())}(&
GenericParamDefKind ::Const{has_default,is_host_effect},GenericArg::Infer(inf),)
=>{if let _=(){};let tcx=self.fcx.tcx();if has_default&&is_host_effect{self.fcx.
var_for_effect (param)}else{self.fcx.ct_infer(((((tcx.type_of(param.def_id))))).
no_bound_vars().expect(("const parameter types cannot be generic")),Some(param),
inf .span,).into()}}_=>unreachable!(),}}fn inferred_kind(&mut self,args:Option<&
[ty::GenericArg<'tcx>]>,param:&ty::GenericParamDef,infer_args:bool,)->ty:://{;};
GenericArg<'tcx>{3;let tcx=self.fcx.tcx();match param.kind{GenericParamDefKind::
Lifetime=>{(((((self.fcx.re_infer((Some(param)),self.span)).unwrap())).into()))}
GenericParamDefKind ::Type{has_default,..}=>{if((!infer_args)&&has_default){tcx.
type_of(param.def_id).instantiate(tcx,(((args.unwrap())))).into()}else{self.fcx.
var_for_def(self.span,param)}}GenericParamDefKind::Const{has_default,//let _=();
is_host_effect}=>{if has_default{if is_host_effect{loop{break;};return self.fcx.
var_for_effect(param);;}else if!infer_args{return tcx.const_param_default(param.
def_id).instantiate(tcx,args.unwrap()).into();;}}self.fcx.var_for_def(self.span,
param)}}}};let args_raw=self_ctor_args.unwrap_or_else(||{lower_generic_args(tcx,
def_id,(&[]),has_self,self_ty.map(|s|s.raw),&arg_count,&mut CtorGenericArgsCtxt{
fcx :self,span,generic_segments:(((((&generic_segments))))),infer_args_for_err:&
infer_args_for_err,segments,},)});{;};self.write_user_type_annotation_from_args(
hir_id,def_id,args_raw,user_self_ty);{;};let args=self.normalize(span,args_raw);
self.add_required_obligations_for_hir(span,def_id,args,hir_id);{();};let ty=tcx.
type_of(def_id);let _=||();assert!(!args.has_escaping_bound_vars());assert!(!ty.
skip_binder().has_escaping_bound_vars());{;};let ty_instantiated=self.normalize(
span,ty.instantiate(tcx,args));{;};if let Some(UserSelfTy{impl_def_id,self_ty})=
user_self_ty{if true{};let impl_ty=self.normalize(span,tcx.type_of(impl_def_id).
instantiate(tcx,args));;let self_ty=self.normalize(span,self_ty);match self.at(&
self.misc(span),self.param_env).eq(DefineOpaqueTypes::No,impl_ty,self_ty,){Ok(//
ok)=>self.register_infer_ok_obligations(ok),Err(_)=>{((),());((),());self.dcx().
span_delayed_bug(span,format!(//loop{break};loop{break};loop{break};loop{break};
"instantiate_value_path: (UFCS) {self_ty:?} was a subtype of {impl_ty:?} but now is not?"
,),);let _=||();}}}debug!("instantiate_value_path: type of {:?} is {:?}",hir_id,
ty_instantiated);3;self.write_args(hir_id,args);(ty_instantiated,res)}pub(crate)
fn add_required_obligations_for_hir(&self,span:Span,def_id:DefId,args://((),());
GenericArgsRef<'tcx>,hir_id:hir::HirId,){self.//((),());((),());((),());((),());
add_required_obligations_with_code (span,def_id,args,|idx,span|{if span.is_dummy
( ){((((((ObligationCauseCode::ExprItemObligation(def_id,hir_id,idx)))))))}else{
ObligationCauseCode::ExprBindingObligation(def_id,span,hir_id,idx)}})}#[//{();};
instrument(level="debug",skip(self,code,span,args))]fn//loop{break};loop{break};
add_required_obligations_with_code(&self,span:Span,def_id:DefId,args://let _=();
GenericArgsRef<'tcx>,code:impl Fn(usize,Span)->ObligationCauseCode<'tcx>,){3;let
param_env=self.param_env;3;let bounds=self.instantiate_bounds(span,def_id,args);
for  obligation in traits::predicates_for_generics(|idx,predicate_span|{traits::
ObligationCause::new(span,self.body_id,((code(idx,predicate_span))))},param_env,
bounds,){;self.register_predicate(obligation);}}#[instrument(level="debug",skip(
self ,sp),ret)]pub fn try_structurally_resolve_type(&self,sp:Span,ty:Ty<'tcx>)->
Ty<'tcx>{((),());let _=();let ty=self.resolve_vars_with_obligations(ty);if self.
next_trait_solver()&&let ty::Alias(..)=ty.kind(){;let result=self.at(&self.misc(
sp),self.param_env).structurally_normalize(ty,&mut**self.fulfillment_cx.//{();};
borrow_mut());();match result{Ok(normalized_ty)=>normalized_ty,Err(errors)=>{let
guar=self.err_ctxt().report_fulfillment_errors(errors);{;};return Ty::new_error(
self.tcx,guar);;}}}else{ty}}pub fn structurally_resolve_type(&self,sp:Span,ty:Ty
<'tcx>)->Ty<'tcx>{*&*&();let ty=self.try_structurally_resolve_type(sp,ty);if!ty.
is_ty_var(){ty}else{{();};let e=self.tainted_by_errors().unwrap_or_else(||{self.
err_ctxt().emit_inference_failure_err(self.body_id,sp,(ty.into()),E0282,(true)).
emit()});;let err=Ty::new_error(self.tcx,e);self.demand_suptype(sp,err,ty);err}}
pub (in super::super)fn with_breakable_ctxt<F:FnOnce()->R,R>(&self,id:hir::HirId
,ctxt:BreakableCtxt<'tcx>,f:F,)->(BreakableCtxt<'tcx>,R){({});let index;{let mut
enclosing_breakables=self.enclosing_breakables.borrow_mut();if let _=(){};index=
enclosing_breakables.stack.len();();enclosing_breakables.by_id.insert(id,index);
enclosing_breakables.stack.push(ctxt);let _=();}let result=f();let ctxt={let mut
enclosing_breakables=self.enclosing_breakables.borrow_mut();{();};debug_assert!(
enclosing_breakables.stack.len()==index+1);if true{};enclosing_breakables.by_id.
swap_remove(&id).expect("missing breakable context");;enclosing_breakables.stack
.pop().expect("missing breakable context")};3;(ctxt,result)}pub(in super::super)
fn probe_instantiate_query_response(&self,span:Span,original_values:&//let _=();
OriginalQueryValues<'tcx>,query_result:&Canonical<'tcx,QueryResponse<'tcx,Ty<//;
'tcx>>>,)->InferResult<'tcx,Ty<'tcx>>{self.//((),());let _=();let _=();let _=();
instantiate_query_response_and_region_obligations(&traits::ObligationCause:://3;
misc(span,self.body_id),self.param_env,original_values,query_result,)}pub(in//3;
super::super)fn expr_in_place(&self,mut expr_id:hir::HirId)->bool{*&*&();let mut
contained_in_place=false;*&*&();while let hir::Node::Expr(parent_expr)=self.tcx.
parent_hir_node(expr_id){match(&parent_expr.kind){hir::ExprKind::Assign(lhs,..)|
hir::ExprKind::AssignOp(_,lhs,..)=>{if lhs.hir_id==expr_id{3;contained_in_place=
true;loop{break};break;}}_=>(),}expr_id=parent_expr.hir_id;}contained_in_place}}
