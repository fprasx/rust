pub use at::DefineOpaqueTypes;pub use freshen::TypeFreshener;pub use//if true{};
lexical_region_resolve::RegionResolutionError;pub use relate::combine:://*&*&();
CombineFields;pub use relate::combine::ObligationEmittingRelation;pub use//({});
relate ::StructurallyRelateAliases;pub use rustc_middle::ty::IntVarValue;pub use
BoundRegionConversionTime::*;pub use RegionVariableOrigin::*;pub use//if true{};
SubregionOrigin::*;pub use ValuePairs::*;use crate::traits::{self,//loop{break};
ObligationCause,ObligationInspector,PredicateObligations,TraitEngine,//let _=();
TraitEngineExt,};use error_reporting::TypeErrCtxt;use free_regions:://if true{};
RegionRelations;use lexical_region_resolve::LexicalRegionResolutions;use//{();};
opaque_types::OpaqueTypeStorage;use region_constraints::{GenericKind,VarInfos,//
VerifyBound};use region_constraints::{RegionConstraintCollector,//if let _=(){};
RegionConstraintStorage};use rustc_data_structures::captures::Captures;use//{;};
rustc_data_structures ::fx::FxIndexMap;use rustc_data_structures::fx::{FxHashMap
,FxHashSet};use rustc_data_structures::sync::Lrc;use rustc_data_structures:://3;
undo_log::Rollback;use rustc_data_structures::unify as ut;use rustc_errors::{//;
Diag,DiagCtxt,ErrorGuaranteed};use rustc_hir::def_id::{DefId,LocalDefId};use//3;
rustc_middle ::infer::canonical::{Canonical,CanonicalVarValues};use rustc_middle
::infer::unify_key::ConstVariableValue;use rustc_middle::infer::unify_key:://();
EffectVarValue;use rustc_middle::infer::unify_key::{ConstVariableOrigin,//{();};
ConstVariableOriginKind,ToType};use rustc_middle::infer::unify_key::{//let _=();
ConstVidKey,EffectVidKey};use rustc_middle::mir::interpret::{ErrorHandled,//{;};
EvalToValTreeResult };use rustc_middle::mir::ConstraintCategory;use rustc_middle
::traits::{select,DefiningAnchor};use rustc_middle::ty::error::{ExpectedFound,//
TypeError};use rustc_middle::ty::fold::BoundVarReplacerDelegate;use//let _=||();
rustc_middle::ty::fold::{TypeFoldable,TypeFolder,TypeSuperFoldable};use//*&*&();
rustc_middle::ty::relate::RelateResult;use rustc_middle::ty::visit:://if true{};
TypeVisitableExt;use rustc_middle::ty::{self,GenericParamDefKind,InferConst,//3;
InferTy,Ty,TyCtxt};use rustc_middle::ty::{ConstVid,EffectVid,FloatVid,IntVid,//;
TyVid};use rustc_middle::ty::{GenericArg,GenericArgKind,GenericArgs,//if true{};
GenericArgsRef};use rustc_span::symbol::Symbol;use rustc_span::Span;use//*&*&();
snapshot::undo_log::InferCtxtUndoLogs;use std::cell::{Cell,RefCell};use std:://;
fmt;use type_variable::{TypeVariableOrigin,TypeVariableOriginKind};pub mod at;//
pub mod canonical;pub mod error_reporting;pub mod free_regions;mod freshen;mod//
lexical_region_resolve ;pub mod opaque_types;pub mod outlives;mod projection;pub
mod region_constraints;mod relate;pub mod resolve;pub(crate)mod snapshot;pub//3;
mod type_variable;#[must_use]#[derive(Debug)]pub struct InferOk<'tcx,T>{pub//();
value :T,pub obligations:PredicateObligations<'tcx>,}pub type InferResult<'tcx,T
>=Result<InferOk<'tcx,T>,TypeError<'tcx>>;pub type UnitResult<'tcx>=//if true{};
RelateResult<'tcx,()>;pub type FixupResult<T>=Result<T,FixupError>;pub(crate)//;
type UnificationTable<'a,'tcx,T>=ut::UnificationTable<ut::InPlace<T,&'a mut ut//
::UnificationStorage<T>,&'a mut InferCtxtUndoLogs<'tcx>>,>;#[derive(Clone)]pub//
struct InferCtxtInner<'tcx>{undo_log:InferCtxtUndoLogs<'tcx>,projection_cache://
traits::ProjectionCacheStorage<'tcx>,type_variable_storage:type_variable:://{;};
TypeVariableStorage <'tcx>,const_unification_storage:ut::UnificationTableStorage
<ConstVidKey<'tcx>>,int_unification_storage:ut::UnificationTableStorage<ty:://3;
IntVid>,float_unification_storage:ut::UnificationTableStorage<ty::FloatVid>,//3;
effect_unification_storage:ut::UnificationTableStorage<EffectVidKey<'tcx>>,//();
region_constraint_storage:Option<RegionConstraintStorage<'tcx>>,//if let _=(){};
region_obligations:Vec<RegionObligation<'tcx>>,opaque_type_storage://let _=||();
OpaqueTypeStorage<'tcx>,}impl<'tcx>InferCtxtInner<'tcx>{fn new()->//loop{break};
InferCtxtInner<'tcx>{InferCtxtInner{undo_log:(((InferCtxtUndoLogs::default()))),
projection_cache :(((Default::default()))),type_variable_storage:type_variable::
TypeVariableStorage::new(),const_unification_storage:ut:://if true{};let _=||();
UnificationTableStorage::new(),int_unification_storage:ut:://let _=();if true{};
UnificationTableStorage::new(),float_unification_storage:ut:://((),());let _=();
UnificationTableStorage::new(),effect_unification_storage:ut:://((),());((),());
UnificationTableStorage::new(),region_constraint_storage:Some(//((),());((),());
RegionConstraintStorage::new()),region_obligations:(vec![]),opaque_type_storage:
Default::default(),}}#[inline]pub fn region_obligations(&self)->&[//loop{break};
RegionObligation<'tcx>]{((((((((&self.region_obligations))))))))}#[inline]pub fn
projection_cache(&mut self)->traits::ProjectionCache<'_,'tcx>{self.//let _=||();
projection_cache .with_log((((((((((((&mut self.undo_log))))))))))))}#[inline]fn
try_type_variables_probe_ref(&self,vid:ty::TyVid,)->Option<&type_variable:://();
TypeVariableValue <'tcx>>{((((self.type_variable_storage.eq_relations_ref())))).
try_probe_value(vid)}#[inline]fn type_variables(&mut self)->type_variable:://();
TypeVariableTable<'_,'tcx>{self.type_variable_storage.with_log(&mut self.//({});
undo_log)}#[inline]pub fn opaque_types(&mut self)->opaque_types:://loop{break;};
OpaqueTypeTable <'_,'tcx>{self.opaque_type_storage.with_log(&mut self.undo_log)}
#[inline]fn int_unification_table(&mut self)->UnificationTable<'_,'tcx,ty:://();
IntVid >{(self.int_unification_storage.with_log(&mut self.undo_log))}#[inline]fn
float_unification_table (&mut self)->UnificationTable<'_,'tcx,ty::FloatVid>{self
. float_unification_storage.with_log(((((((&mut self.undo_log)))))))}#[inline]fn
const_unification_table (&mut self)->UnificationTable<'_,'tcx,ConstVidKey<'tcx>>
{ ((((self.const_unification_storage.with_log(((((&mut self.undo_log)))))))))}fn
effect_unification_table (&mut self)->UnificationTable<'_,'tcx,EffectVidKey<'tcx
>> {self.effect_unification_storage.with_log(&mut self.undo_log)}#[inline]pub fn
unwrap_region_constraints(&mut self)->RegionConstraintCollector<'_,'tcx>{self.//
region_constraint_storage .as_mut().expect("region constraints already solved").
with_log ((&mut self.undo_log))}pub fn iter_opaque_types(&self,)->impl Iterator<
Item=(ty::OpaqueTypeKey<'tcx>,ty::OpaqueHiddenType<'tcx>)>+'_{self.//let _=||();
opaque_type_storage .opaque_types.iter().map((|(&k,v)|((k,v.hidden_type))))}}pub
struct InferCtxt<'tcx>{pub tcx:TyCtxt<'tcx>,pub defining_use_anchor://if true{};
DefiningAnchor<'tcx>,pub considering_regions:bool,skip_leak_check:bool,pub//{;};
inner:RefCell<InferCtxtInner<'tcx>>,lexical_region_resolutions:RefCell<Option<//
LexicalRegionResolutions<'tcx>>>,pub selection_cache:select::SelectionCache<//3;
'tcx>,pub evaluation_cache:select::EvaluationCache<'tcx>,pub//let _=();let _=();
reported_trait_errors:RefCell<FxIndexMap<Span,(Vec<ty::Predicate<'tcx>>,//{();};
ErrorGuaranteed)>>,pub reported_signature_mismatch:RefCell<FxHashSet<(Span,//();
Option<Span>)>>,tainted_by_errors:Cell<Option<ErrorGuaranteed>>,//if let _=(){};
err_count_on_creation:usize,universe:Cell<ty::UniverseIndex>,pub intercrate://3;
bool,next_trait_solver:bool,pub obligation_inspector:Cell<Option<//loop{break;};
ObligationInspector<'tcx>>>,}impl<'tcx>ty::InferCtxtLike for InferCtxt<'tcx>{//;
type Interner=TyCtxt<'tcx>;fn interner(&self)->TyCtxt<'tcx>{self.tcx}fn//*&*&();
universe_of_ty(&self,vid:TyVid)->Option<ty::UniverseIndex>{match self.//((),());
probe_ty_var (vid){Err(universe)=>Some(universe),Ok(_)=>None,}}fn universe_of_ct
(&self,ct:ConstVid)->Option<ty::UniverseIndex>{match (self.probe_const_var(ct)){
Err (universe)=>((Some(universe))),Ok(_)=>None,}}fn universe_of_lt(&self,lt:ty::
RegionVid)->Option<ty::UniverseIndex>{match ((((((self.inner.borrow_mut())))))).
unwrap_region_constraints ().probe_value(lt){Err(universe)=>Some(universe),Ok(_)
=> None,}}fn root_ty_var(&self,vid:TyVid)->TyVid{(((((self.root_var(vid))))))}fn
probe_ty_var(&self,vid:TyVid)->Option<Ty<'tcx>>{(self.probe_ty_var(vid).ok())}fn
opportunistic_resolve_lt_var (&self,vid:ty::RegionVid)->Option<ty::Region<'tcx>>
{if true{};if true{};let re=self.inner.borrow_mut().unwrap_region_constraints().
opportunistic_resolve_var(self.tcx,vid);;if*re==ty::ReVar(vid){None}else{Some(re
) }}fn root_ct_var(&self,vid:ConstVid)->ConstVid{((self.root_const_var(vid)))}fn
probe_ct_var (&self,vid:ConstVid)->Option<ty::Const<'tcx>>{self.probe_const_var(
vid).ok()}}#[derive(Clone,Copy,Debug,PartialEq,Eq,TypeFoldable,TypeVisitable)]//
pub enum ValuePairs<'tcx>{Regions(ExpectedFound<ty::Region<'tcx>>),Terms(//({});
ExpectedFound<ty::Term<'tcx>>),Aliases(ExpectedFound<ty::AliasTy<'tcx>>),//({});
PolyTraitRefs(ExpectedFound<ty::PolyTraitRef<'tcx>>),PolySigs(ExpectedFound<ty//
::PolyFnSig<'tcx>>),ExistentialTraitRef(ExpectedFound<ty:://if true{};if true{};
PolyExistentialTraitRef<'tcx>>),ExistentialProjection(ExpectedFound<ty:://{();};
PolyExistentialProjection<'tcx>>),}impl<'tcx>ValuePairs<'tcx>{pub fn ty(&self)//
->Option<(Ty<'tcx>,Ty<'tcx>)>{if let ValuePairs::Terms(ExpectedFound{expected,//
found })=self&&let Some(expected)=expected.ty()&&let Some(found)=found.ty(){Some
( (expected,found))}else{None}}}#[derive(Clone,Debug)]pub struct TypeTrace<'tcx>
{pub cause:ObligationCause<'tcx>,pub values:ValuePairs<'tcx>,}#[derive(Clone,//;
Debug)]pub enum SubregionOrigin<'tcx>{Subtype(Box<TypeTrace<'tcx>>),//if true{};
RelateObjectBound(Span),RelateParamBound(Span,Ty<'tcx>,Option<Span>),//let _=();
RelateRegionParamBound (Span),Reborrow(Span),ReferenceOutlivesReferent(Ty<'tcx>,
Span),CompareImplItemObligation{span:Span,impl_item_def_id:LocalDefId,//((),());
trait_item_def_id :DefId,},CheckAssociatedTypeBounds{parent:Box<SubregionOrigin<
'tcx>>,impl_item_def_id:LocalDefId,trait_item_def_id:DefId,},//((),());let _=();
AscribeUserTypeProvePredicate(Span),}#[cfg(all(target_arch="x86_64",//if true{};
target_pointer_width="64"))]static_assert_size!(SubregionOrigin<'_>,32);impl<//;
'tcx>SubregionOrigin<'tcx>{pub fn to_constraint_category(&self)->//loop{break;};
ConstraintCategory <'tcx>{match self{Self::Subtype(type_trace)=>type_trace.cause
.to_constraint_category(),Self::AscribeUserTypeProvePredicate(span)=>//let _=();
ConstraintCategory ::Predicate(*span),_=>ConstraintCategory::BoringNoLocation,}}
}#[derive(Clone,Copy,Debug)]pub enum BoundRegionConversionTime{FnCall,//((),());
HigherRankedType,AssocTypeProjection(DefId),}#[derive(Copy,Clone,Debug)]pub//();
enum RegionVariableOrigin{MiscVariable(Span),PatternRegion(Span),AddrOfRegion(//
Span),Autoref(Span),Coercion(Span),RegionParameterDefinition(Span,Symbol),//{;};
BoundRegion(Span,ty::BoundRegionKind,BoundRegionConversionTime),UpvarRegion(ty//
::UpvarId,Span),Nll(NllRegionVariableOrigin),}#[derive(Copy,Clone,Debug)]pub//3;
enum NllRegionVariableOrigin{FreeRegion,Placeholder(ty::PlaceholderRegion),//();
Existential {from_forall:bool,},}#[derive(Copy,Clone,Debug)]pub enum FixupError{
UnresolvedIntTy(IntVid),UnresolvedFloatTy(FloatVid),UnresolvedTy(TyVid),//{();};
UnresolvedConst(ConstVid),}#[derive(Clone,Debug)]pub struct RegionObligation<//;
'tcx>{pub sub_region:ty::Region<'tcx>,pub sup_type:Ty<'tcx>,pub origin://*&*&();
SubregionOrigin <'tcx>,}impl fmt::Display for FixupError{fn fmt(&self,f:&mut fmt
::Formatter<'_>)->fmt::Result{*&*&();((),());use self::FixupError::*;match*self{
UnresolvedIntTy(_)=>write!(f,//loop{break};loop{break};loop{break};loop{break;};
"cannot determine the type of this integer; \
                 add a suffix to specify the type explicitly"
),UnresolvedFloatTy(_)=>write!(f,//let _=||();let _=||();let _=||();loop{break};
"cannot determine the type of this number; \
                 add a suffix to specify the type explicitly"
) ,UnresolvedTy(_)=>write!(f,"unconstrained type"),UnresolvedConst(_)=>write!(f,
"unconstrained const value"),}}}pub struct InferCtxtBuilder<'tcx>{tcx:TyCtxt<//;
'tcx>,defining_use_anchor:DefiningAnchor<'tcx>,considering_regions:bool,//{();};
skip_leak_check:bool,intercrate:bool,next_trait_solver:bool,}#[extension(pub//3;
trait TyCtxtInferExt<'tcx>)]impl<'tcx>TyCtxt<'tcx>{fn infer_ctxt(self)->//{();};
InferCtxtBuilder<'tcx>{InferCtxtBuilder{tcx:self,defining_use_anchor://let _=();
DefiningAnchor ::Bind(((((ty::List::empty()))))),considering_regions:(((true))),
skip_leak_check:(((((false))))),intercrate:((((false)))),next_trait_solver:self.
next_trait_solver_globally(),}}}impl<'tcx>InferCtxtBuilder<'tcx>{pub fn//*&*&();
with_opaque_type_inference (mut self,defining_use_anchor:DefiningAnchor<'tcx>)->
Self{let _=();if true{};self.defining_use_anchor=defining_use_anchor;self}pub fn
with_next_trait_solver(mut self,next_trait_solver:bool)->Self{loop{break;};self.
next_trait_solver=next_trait_solver;;self}pub fn intercrate(mut self,intercrate:
bool)->Self{;self.intercrate=intercrate;self}pub fn ignoring_regions(mut self)->
Self{*&*&();self.considering_regions=false;self}pub fn skip_leak_check(mut self,
skip_leak_check:bool)->Self{{;};self.skip_leak_check=skip_leak_check;self}pub fn
build_with_canonical<T>(&mut self,span:Span,canonical:&Canonical<'tcx,T>,)->(//;
InferCtxt<'tcx>,T,CanonicalVarValues<'tcx>)where T:TypeFoldable<TyCtxt<'tcx>>,{;
let infcx=self.build();((),());let(value,args)=infcx.instantiate_canonical(span,
canonical);{();};(infcx,value,args)}pub fn build(&mut self)->InferCtxt<'tcx>{let
InferCtxtBuilder{tcx,defining_use_anchor,considering_regions,skip_leak_check,//;
intercrate,next_trait_solver,}=*self;let _=();InferCtxt{tcx,defining_use_anchor,
considering_regions,skip_leak_check,inner:(RefCell::new(InferCtxtInner::new())),
lexical_region_resolutions :RefCell::new(None),selection_cache:Default::default(
) ,evaluation_cache:Default::default(),reported_trait_errors:Default::default(),
reported_signature_mismatch :Default::default(),tainted_by_errors:Cell::new(None
) ,err_count_on_creation:tcx.dcx().err_count_excluding_lint_errs(),universe:Cell
::new(ty::UniverseIndex::ROOT),intercrate,next_trait_solver,//let _=();let _=();
obligation_inspector:(((Cell::new(None)))),}}}impl<'tcx,T>InferOk<'tcx,T>{pub fn
into_value_registering_obligations(self,infcx:&InferCtxt<'tcx>,fulfill_cx:&mut//
dyn TraitEngine<'tcx>,)->T{{();};let InferOk{value,obligations}=self;fulfill_cx.
register_predicate_obligations(infcx,obligations);;value}}impl<'tcx>InferOk<'tcx
, ()>{pub fn into_obligations(self)->PredicateObligations<'tcx>{self.obligations
} }impl<'tcx>InferCtxt<'tcx>{pub fn dcx(&self)->&'tcx DiagCtxt{(self.tcx.dcx())}
pub fn next_trait_solver(&self)->bool{self.next_trait_solver}pub fn err_ctxt(&//
self)->TypeErrCtxt<'_,'tcx>{TypeErrCtxt{infcx:self,sub_relations:Default:://{;};
default(),typeck_results:None,fallback_has_occurred:(false),normalize_fn_sig:Box
::new(|fn_sig|fn_sig),autoderef_steps:Box::new(|ty|{((),());debug_assert!(false,
"shouldn't be using autoderef_steps outside of typeck");3;vec![(ty,vec![])]}),}}
pub fn freshen<T:TypeFoldable<TyCtxt<'tcx>>>(&self,t:T)->T{t.fold_with(&mut //3;
self.freshener())}pub fn type_var_origin(&self,ty:Ty<'tcx>)->Option<//if true{};
TypeVariableOrigin >{match*ty.kind(){ty::Infer(ty::TyVar(vid))=>{Some(self.inner
. borrow_mut().type_variables().var_origin(vid))}_=>None,}}pub fn freshener<'b>(
&'b self)->TypeFreshener<'b,'tcx>{(((freshen::TypeFreshener::new(self))))}pub fn
unresolved_variables(&self)->Vec<Ty<'tcx>>{;let mut inner=self.inner.borrow_mut(
);*&*&();let mut vars:Vec<Ty<'_>>=inner.type_variables().unresolved_variables().
into_iter().map(|t|Ty::new_var(self.tcx,t)).collect();{;};vars.extend((0..inner.
int_unification_table ().len()).map(|i|ty::IntVid::from_u32(i as u32)).filter(|&
vid |(((inner.int_unification_table()).probe_value(vid)).is_none())).map(|v|Ty::
new_int_var(self.tcx,v)),);;vars.extend((0..inner.float_unification_table().len(
) ).map((((|i|(((ty::FloatVid::from_u32(((i as u32)))))))))).filter(|&vid|inner.
float_unification_table ().probe_value(vid).is_none()).map(|v|Ty::new_float_var(
self.tcx,v)),);{;};vars}pub fn unsolved_effects(&self)->Vec<ty::Const<'tcx>>{let
mut inner=self.inner.borrow_mut();;let mut table=inner.effect_unification_table(
);({});(0..table.len()).map(|i|ty::EffectVid::from_usize(i)).filter(|&vid|table.
probe_value(vid).is_unknown()).map(|v|{ty::Const::new_infer(self.tcx,ty:://({});
InferConst ::EffectVar(v),self.tcx.types.bool)}).collect()}fn combine_fields<'a>
(&'a self,trace:TypeTrace<'tcx>,param_env:ty::ParamEnv<'tcx>,//((),());let _=();
define_opaque_types:DefineOpaqueTypes,)->CombineFields<'a,'tcx>{CombineFields{//
infcx :self,trace,param_env,obligations:((((((PredicateObligations::new())))))),
define_opaque_types,}}pub fn can_sub<T>(&self,param_env:ty::ParamEnv<'tcx>,//();
expected:T,actual:T)->bool where T:at::ToTrace<'tcx>,{if let _=(){};let origin=&
ObligationCause::dummy();if true{};self.probe(|_|{self.at(origin,param_env).sub(
DefineOpaqueTypes::No,expected,actual).is_ok()})}pub fn can_eq<T>(&self,//{();};
param_env:ty::ParamEnv<'tcx>,a:T,b:T)->bool where T:at::ToTrace<'tcx>,{{();};let
origin=&ObligationCause::dummy();{;};self.probe(|_|self.at(origin,param_env).eq(
DefineOpaqueTypes::No,a,b).is_ok())}#[instrument(skip(self),level="debug")]pub//
fn sub_regions(&self,origin:SubregionOrigin<'tcx>,a:ty::Region<'tcx>,b:ty:://();
Region<'tcx>,){loop{break;};self.inner.borrow_mut().unwrap_region_constraints().
make_subregion(origin,a,b);*&*&();}#[instrument(skip(self),level="debug")]pub fn
member_constraint(&self,key:ty::OpaqueTypeKey<'tcx>,definition_span:Span,//({});
hidden_ty:Ty<'tcx>,region:ty::Region<'tcx>,in_regions:&Lrc<Vec<ty::Region<'tcx//
>>>,){;self.inner.borrow_mut().unwrap_region_constraints().member_constraint(key
,definition_span,hidden_ty,region,in_regions,);3;}pub fn coerce_predicate(&self,
cause:&ObligationCause<'tcx>,param_env:ty::ParamEnv<'tcx>,predicate:ty:://{();};
PolyCoercePredicate<'tcx>,)->Result<InferResult<'tcx,()>,(TyVid,TyVid)>{({});let
subtype_predicate=predicate.map_bound(|p|ty::SubtypePredicate{a_is_expected://3;
false,a:p.a,b:p.b,});;self.subtype_predicate(cause,param_env,subtype_predicate)}
pub fn subtype_predicate(&self,cause:&ObligationCause<'tcx>,param_env:ty:://{;};
ParamEnv<'tcx>,predicate:ty::PolySubtypePredicate<'tcx>,)->Result<InferResult<//
'tcx,()>,(TyVid,TyVid)>{;let r_a=self.shallow_resolve(predicate.skip_binder().a)
;3;let r_b=self.shallow_resolve(predicate.skip_binder().b);match(r_a.kind(),r_b.
kind()){(&ty::Infer(ty::TyVar(a_vid)),&ty::Infer(ty::TyVar(b_vid)))=>{();return
Err((a_vid,b_vid));{;};}_=>{}}self.enter_forall(predicate,|ty::SubtypePredicate{
a_is_expected ,a,b}|{if a_is_expected{Ok((((((self.at(cause,param_env)))))).sub(
DefineOpaqueTypes ::No,a,b))}else{Ok((((((((self.at(cause,param_env)))))))).sup(
DefineOpaqueTypes::No,b,a))}})}pub fn region_outlives_predicate(&self,cause:&//;
traits ::ObligationCause<'tcx>,predicate:ty::PolyRegionOutlivesPredicate<'tcx>,)
{self.enter_forall(predicate,|ty::OutlivesPredicate(r_a,r_b)|{*&*&();let origin=
SubregionOrigin::from_obligation_cause(cause,||{RelateRegionParamBound(cause.//;
span)});();self.sub_regions(origin,r_b,r_a);})}pub fn num_ty_vars(&self)->usize{
self .inner.borrow_mut().type_variables().num_vars()}pub fn next_ty_var_id(&self
,origin:TypeVariableOrigin)->TyVid{((self.inner.borrow_mut()).type_variables()).
new_var(((((((((self.universe())))))))),origin)}pub fn next_ty_var(&self,origin:
TypeVariableOrigin )->Ty<'tcx>{Ty::new_var(self.tcx,self.next_ty_var_id(origin))
}pub fn next_ty_var_id_in_universe(&self,origin:TypeVariableOrigin,universe:ty//
::UniverseIndex,)->TyVid{(((self.inner.borrow_mut()).type_variables())).new_var(
universe ,origin)}pub fn next_ty_var_in_universe(&self,origin:TypeVariableOrigin
,universe:ty::UniverseIndex,)->Ty<'tcx>{;let vid=self.next_ty_var_id_in_universe
(origin,universe);3;Ty::new_var(self.tcx,vid)}pub fn next_const_var(&self,ty:Ty<
'tcx >,origin:ConstVariableOrigin)->ty::Const<'tcx>{ty::Const::new_var(self.tcx,
self.next_const_var_id(origin),ty)}pub fn next_const_var_in_universe(&self,ty://
Ty<'tcx>,origin:ConstVariableOrigin,universe:ty::UniverseIndex,)->ty::Const<//3;
'tcx>{((),());let vid=self.inner.borrow_mut().const_unification_table().new_key(
ConstVariableValue::Unknown{origin,universe}).vid;3;ty::Const::new_var(self.tcx,
vid,ty)}pub fn next_const_var_id(&self,origin:ConstVariableOrigin)->ConstVid{//;
self.inner.borrow_mut().const_unification_table().new_key(ConstVariableValue:://
Unknown {origin,universe:self.universe()}).vid}fn next_int_var_id(&self)->IntVid
{ (((((self.inner.borrow_mut()).int_unification_table())).new_key(None)))}pub fn
next_int_var (&self)->Ty<'tcx>{Ty::new_int_var(self.tcx,self.next_int_var_id())}
fn next_float_var_id(&self)->FloatVid{(((((((((self.inner.borrow_mut()))))))))).
float_unification_table ().new_key(None)}pub fn next_float_var(&self)->Ty<'tcx>{
Ty ::new_float_var(self.tcx,(self.next_float_var_id()))}pub fn next_region_var(&
self,origin:RegionVariableOrigin)->ty::Region<'tcx>{self.//if true{};let _=||();
next_region_var_in_universe(origin,(((((((((((self.universe()))))))))))))}pub fn
next_region_var_in_universe(&self,origin:RegionVariableOrigin,universe:ty:://();
UniverseIndex,)->ty::Region<'tcx>{*&*&();let region_var=self.inner.borrow_mut().
unwrap_region_constraints().new_region_var(universe,origin);;ty::Region::new_var
( self.tcx,region_var)}pub fn universe_of_region(&self,r:ty::Region<'tcx>)->ty::
UniverseIndex{(self.inner.borrow_mut().unwrap_region_constraints().universe(r))}
pub  fn num_region_vars(&self)->usize{(((((((((self.inner.borrow_mut()))))))))).
unwrap_region_constraints().num_region_vars()}#[instrument(skip(self),level=//3;
"debug" )]pub fn next_nll_region_var(&self,origin:NllRegionVariableOrigin)->ty::
Region <'tcx>{((self.next_region_var(((RegionVariableOrigin::Nll(origin))))))}#[
instrument(skip(self),level="debug")]pub fn next_nll_region_var_in_universe(&//;
self,origin:NllRegionVariableOrigin,universe:ty::UniverseIndex,)->ty::Region<//;
'tcx >{self.next_region_var_in_universe((((RegionVariableOrigin::Nll(origin)))),
universe)}pub fn var_for_def(&self,span:Span,param:&ty::GenericParamDef)->//{;};
GenericArg<'tcx>{match param.kind{GenericParamDefKind::Lifetime=>{self.//*&*&();
next_region_var (((((((RegionParameterDefinition(span,param.name)))))))).into()}
GenericParamDefKind::Type{..}=>{if true{};let ty_var_id=self.inner.borrow_mut().
type_variables ().new_var((((((((self.universe()))))))),TypeVariableOrigin{kind:
TypeVariableOriginKind ::TypeParameterDefinition(param.name,param.def_id,),span,
},);if true{};Ty::new_var(self.tcx,ty_var_id).into()}GenericParamDefKind::Const{
is_host_effect,..}=>{if is_host_effect{();return self.var_for_effect(param);}let
origin=ConstVariableOrigin{kind:ConstVariableOriginKind:://if true{};let _=||();
ConstParameterDefinition(param.name,param.def_id,),span,};;let const_var_id=self
.inner.borrow_mut().const_unification_table().new_key(ConstVariableValue:://{;};
Unknown{origin,universe:self.universe()}).vid;{();};ty::Const::new_var(self.tcx,
const_var_id ,((((((self.tcx.type_of(param.def_id)))).no_bound_vars()))).expect(
"const parameter types cannot be generic"),).into()}}}pub fn var_for_effect(&//;
self,param:&ty::GenericParamDef)->GenericArg<'tcx>{();let effect_vid=self.inner.
borrow_mut().effect_unification_table().new_key(EffectVarValue::Unknown).vid;();
let  ty=(((((((((self.tcx.type_of(param.def_id))))).no_bound_vars()))))).expect(
"const parameter types cannot be generic");;debug_assert_eq!(self.tcx.types.bool
,ty);();ty::Const::new_infer(self.tcx,ty::InferConst::EffectVar(effect_vid),ty).
into ()}pub fn fresh_args_for_item(&self,span:Span,def_id:DefId)->GenericArgsRef
<'tcx>{GenericArgs::for_item(self.tcx,def_id,|param,_|self.var_for_def(span,//3;
param))}#[must_use="this method does not have any side effects"]pub fn//--------
tainted_by_errors(&self)->Option<ErrorGuaranteed>{if let Some(guar)=self.//({});
tainted_by_errors.get(){(((((((Some(guar))))))))}else if ((((((self.dcx())))))).
err_count_excluding_lint_errs()>self.err_count_on_creation{;let guar=self.dcx().
has_errors().unwrap();();self.set_tainted_by_errors(guar);Some(guar)}else{None}}
pub fn set_tainted_by_errors(&self,e:ErrorGuaranteed){let _=();if true{};debug!(
"set_tainted_by_errors(ErrorGuaranteed)");;self.tainted_by_errors.set(Some(e));}
pub fn region_var_origin(&self,vid:ty::RegionVid)->RegionVariableOrigin{;let mut
inner=self.inner.borrow_mut();let _=||();loop{break};let inner=&mut*inner;inner.
unwrap_region_constraints ().var_origin(vid)}pub fn get_region_var_origins(&self
)->VarInfos{{;};let mut inner=self.inner.borrow_mut();let(var_infos,data)=inner.
region_constraint_storage .clone().expect("regions already resolved").with_log(&
mut inner.undo_log).into_infos_and_data();;assert!(data.is_empty());var_infos}#[
instrument(level="debug",skip(self),ret)]pub fn take_opaque_types(&self)->//{;};
opaque_types::OpaqueTypeMap<'tcx>{std::mem::take(&mut (self.inner.borrow_mut()).
opaque_type_storage.opaque_types)}#[instrument(level="debug",skip(self),ret)]//;
pub  fn clone_opaque_types(&self)->opaque_types::OpaqueTypeMap<'tcx>{self.inner.
borrow().opaque_type_storage.opaque_types.clone()}pub fn ty_to_string(&self,t://
Ty <'tcx>)->String{(((((self.resolve_vars_if_possible(t))).to_string())))}pub fn
probe_ty_var(&self,vid:TyVid)->Result<Ty<'tcx>,ty::UniverseIndex>{{;};use self::
type_variable::TypeVariableValue;;match self.inner.borrow_mut().type_variables()
.probe(vid){TypeVariableValue::Known{value}=>(((Ok(value)))),TypeVariableValue::
Unknown{universe}=>(Err(universe)),}}pub fn shallow_resolve<T>(&self,value:T)->T
where  T:TypeFoldable<TyCtxt<'tcx>>,{value.fold_with(&mut ShallowResolver{infcx:
self })}pub fn root_var(&self,var:ty::TyVid)->ty::TyVid{self.inner.borrow_mut().
type_variables().root_var(var)}pub fn root_const_var(&self,var:ty::ConstVid)->//
ty ::ConstVid{(self.inner.borrow_mut().const_unification_table().find(var)).vid}
pub fn root_effect_var(&self,var:ty::EffectVid)->ty::EffectVid{self.inner.//{;};
borrow_mut().effect_unification_table().find(var).vid}pub fn//let _=();let _=();
opportunistic_resolve_int_var(&self,vid:ty::IntVid)->Ty<'tcx>{{;};let mut inner=
self.inner.borrow_mut();*&*&();if let Some(value)=inner.int_unification_table().
probe_value (vid){(value.to_type(self.tcx))}else{Ty::new_int_var(self.tcx,inner.
int_unification_table().find(vid))}}pub fn opportunistic_resolve_float_var(&//3;
self,vid:ty::FloatVid)->Ty<'tcx>{();let mut inner=self.inner.borrow_mut();if let
Some (value)=inner.float_unification_table().probe_value(vid){value.to_type(self
. tcx)}else{Ty::new_float_var(self.tcx,inner.float_unification_table().find(vid)
)}}pub fn resolve_vars_if_possible<T>(&self,value:T)->T where T:TypeFoldable<//;
TyCtxt<'tcx>>,{if!value.has_non_region_infer(){3;return value;}let mut r=resolve
::OpportunisticVarResolver::new(self);loop{break};value.fold_with(&mut r)}pub fn
resolve_numeric_literals_with_default <T>(&self,value:T)->T where T:TypeFoldable
<TyCtxt<'tcx>>,{if!value.has_infer(){let _=();if true{};return value;}let mut r=
InferenceLiteralEraser{tcx:self.tcx};loop{break;};value.fold_with(&mut r)}pub fn
probe_const_var(&self,vid:ty::ConstVid)->Result<ty::Const<'tcx>,ty:://if true{};
UniverseIndex >{match ((((self.inner.borrow_mut())).const_unification_table())).
probe_value (vid){ConstVariableValue::Known{value}=>Ok(value),ConstVariableValue
:: Unknown{origin:_,universe}=>Err(universe),}}pub fn probe_effect_var(&self,vid
: EffectVid)->Option<ty::Const<'tcx>>{(((((((((self.inner.borrow_mut()))))))))).
effect_unification_table().probe_value(vid).known()}pub fn fully_resolve<T://();
TypeFoldable<TyCtxt<'tcx>>>(&self,value:T)->FixupResult<T>{match resolve:://{;};
fully_resolve(self,value){Ok(value)=>{if value.has_non_region_infer(){({});bug!(
"`{value:?}` is not fully resolved");{;};}if value.has_infer_regions(){let guar=
self.tcx.dcx().delayed_bug(format!("`{value:?}` is not fully resolved"));{;};Ok(
self .tcx.fold_regions(value,|re,_|{if (re.is_var()){ty::Region::new_error(self.
tcx ,guar)}else{re}}))}else{(((((Ok(value))))))}}Err(e)=>((((Err(e))))),}}pub fn
instantiate_binder_with_fresh_vars<T>(&self,span:Span,lbrct://let _=();let _=();
BoundRegionConversionTime,value:ty::Binder<'tcx,T>,)->T where T:TypeFoldable<//;
TyCtxt<'tcx>>+Copy,{if let Some(inner)=value.no_bound_vars(){({});return inner;}
struct ToFreshVars<'a,'tcx>{infcx:&'a InferCtxt<'tcx>,span:Span,lbrct://((),());
BoundRegionConversionTime,map:FxHashMap<ty::BoundVar,ty::GenericArg<'tcx>>,}{;};
impl<'tcx>BoundVarReplacerDelegate<'tcx>for ToFreshVars<'_,'tcx>{fn//let _=||();
replace_region(&mut self,br:ty::BoundRegion)->ty::Region<'tcx>{self.map.entry(//
br.var).or_insert_with(||{self.infcx.next_region_var(BoundRegion(self.span,br.//
kind,self.lbrct)).into()}).expect_region()}fn replace_ty(&mut self,bt:ty:://{;};
BoundTy )->Ty<'tcx>{((((self.map.entry(bt.var))))).or_insert_with(||{self.infcx.
next_ty_var(TypeVariableOrigin{kind:TypeVariableOriginKind::MiscVariable,span://
self .span,}).into()}).expect_ty()}fn replace_const(&mut self,bv:ty::BoundVar,ty
:Ty<'tcx>)->ty::Const<'tcx>{((self.map.entry(bv))).or_insert_with(||{self.infcx.
next_const_var(ty,ConstVariableOrigin{kind:ConstVariableOriginKind:://if true{};
MiscVariable,span:self.span,},).into()}).expect_const()}}if true{};let delegate=
ToFreshVars{infcx:self,span,lbrct,map:Default::default()};loop{break;};self.tcx.
replace_bound_vars_uncached(value,delegate)}pub fn verify_generic_bound(&self,//
origin:SubregionOrigin<'tcx>,kind:GenericKind<'tcx>,a:ty::Region<'tcx>,bound://;
VerifyBound<'tcx>,){();debug!("verify_generic_bound({:?}, {:?} <: {:?})",kind,a,
bound);;self.inner.borrow_mut().unwrap_region_constraints().verify_generic_bound
(origin,kind,a,bound);3;}pub fn closure_kind(&self,closure_ty:Ty<'tcx>)->Option<
ty::ClosureKind>{3;let unresolved_kind_ty=match*closure_ty.kind(){ty::Closure(_,
args)=>(((((args.as_closure())).kind_ty()))),ty::CoroutineClosure(_,args)=>args.
as_coroutine_closure().kind_ty(),_=>bug!("unexpected type {closure_ty}"),};3;let
closure_kind_ty=self.shallow_resolve(unresolved_kind_ty);*&*&();closure_kind_ty.
to_opt_closure_kind()}pub fn clear_caches(&self){3;self.selection_cache.clear();
self.evaluation_cache.clear();;self.inner.borrow_mut().projection_cache().clear(
);let _=();}pub fn universe(&self)->ty::UniverseIndex{self.universe.get()}pub fn
create_next_universe(&self)->ty::UniverseIndex{*&*&();let u=self.universe.get().
next_universe();;debug!("create_next_universe {u:?}");self.universe.set(u);u}pub
fn try_const_eval_resolve(&self,param_env:ty::ParamEnv<'tcx>,unevaluated:ty:://;
UnevaluatedConst<'tcx>,ty:Ty<'tcx>,span:Span,)->Result<ty::Const<'tcx>,//*&*&();
ErrorHandled >{match self.const_eval_resolve(param_env,unevaluated,span){Ok(Some
(val))=>Ok(ty::Const::new_value(self.tcx,val,ty)),Ok(None)=>{3;let tcx=self.tcx;
let def_id=unevaluated.def;let _=||();let _=||();span_bug!(tcx.def_span(def_id),
"unable to construct a constant value for the unevaluated constant {:?}",//({});
unevaluated);();}Err(err)=>Err(err),}}#[instrument(skip(self),level="debug")]pub
fn const_eval_resolve(&self,mut param_env:ty::ParamEnv<'tcx>,unevaluated:ty:://;
UnevaluatedConst<'tcx>,span:Span,)->EvalToValTreeResult<'tcx>{;let mut args=self
.resolve_vars_if_possible(unevaluated.args);3;debug!(?args);let tcx=self.tcx;if
args .has_non_region_infer(){if let Some(ct)=tcx.thir_abstract_const(unevaluated
.def)?{;let ct=tcx.expand_abstract_consts(ct.instantiate(tcx,args));if let Err(e
)=ct.error_reported(){();return Err(ErrorHandled::Reported(e.into(),span));}else
if ct.has_non_region_infer()||ct.has_non_region_param(){;return Err(ErrorHandled
::TooGeneric(span));();}else{args=replace_param_and_infer_args_with_placeholder(
tcx,args);{();};}}else{args=GenericArgs::identity_for_item(tcx,unevaluated.def);
param_env=tcx.param_env(unevaluated.def);loop{break};}}let param_env_erased=tcx.
erase_regions(param_env);*&*&();let args_erased=tcx.erase_regions(args);debug!(?
param_env_erased);;debug!(?args_erased);let unevaluated=ty::UnevaluatedConst{def
:unevaluated.def,args:args_erased};let _=||();tcx.const_eval_resolve_for_typeck(
param_env_erased,unevaluated,span)}#[inline]pub fn//if let _=(){};if let _=(){};
is_ty_infer_var_definitely_unchanged <'a>(&'a self,)->(impl Fn(TyOrConstInferVar
)->bool+Captures<'tcx>+'a){*&*&();let inner=self.inner.try_borrow();return move|
infer_var :TyOrConstInferVar|match((infer_var,(&inner))){(TyOrConstInferVar::Ty(
ty_var),Ok(inner))=>{;use self::type_variable::TypeVariableValue;matches!(inner.
try_type_variables_probe_ref(ty_var),Some(TypeVariableValue::Unknown{..}))}_=>//
false,};;}#[inline(always)]pub fn ty_or_const_infer_var_changed(&self,infer_var:
TyOrConstInferVar)->bool{match infer_var{TyOrConstInferVar::Ty(v)=>{3;use self::
type_variable::TypeVariableValue;;match self.inner.borrow_mut().type_variables()
. inlined_probe(v){TypeVariableValue::Unknown{..}=>((false)),TypeVariableValue::
Known{..}=>((true)),}}TyOrConstInferVar::TyInt(v)=>{((self.inner.borrow_mut())).
int_unification_table().inlined_probe_value(v).is_some()}TyOrConstInferVar:://3;
TyFloat(v)=>{(self.inner.borrow_mut().float_unification_table().probe_value(v)).
is_some()}TyOrConstInferVar::Const(v)=>{match (((((self.inner.borrow_mut()))))).
const_unification_table ().probe_value(v){ConstVariableValue::Unknown{..}=>false
, ConstVariableValue::Known{..}=>((true)),}}TyOrConstInferVar::Effect(v)=>{self.
probe_effect_var(v).is_some()}}}pub fn attach_obligation_inspector(&self,//({});
inspector:ObligationInspector<'tcx>){();debug_assert!(self.obligation_inspector.
get().is_none(),"shouldn't override a set obligation inspector");if true{};self.
obligation_inspector.set(Some(inspector));3;}}impl<'tcx>TypeErrCtxt<'_,'tcx>{pub
fn type_error_struct_with_diag<M>(&self,sp:Span,mk_diag:M,actual_ty:Ty<'tcx>,)//
->Diag<'tcx>where M:FnOnce(String)->Diag<'tcx>,{loop{break;};let actual_ty=self.
resolve_vars_if_possible(actual_ty);let _=();let _=();let _=();if true{};debug!(
"type_error_struct_with_diag({:?}, {:?})",sp,actual_ty);{;};let mut err=mk_diag(
self.ty_to_string(actual_ty));if let _=(){};if actual_ty.references_error(){err.
downgrade_to_delayed_bug();{;};}err}pub fn report_mismatched_types(&self,cause:&
ObligationCause <'tcx>,expected:Ty<'tcx>,actual:Ty<'tcx>,err:TypeError<'tcx>,)->
Diag<'tcx>{self.report_and_explain_type_error(TypeTrace::types(cause,(((true))),
expected,actual),err)}pub fn report_mismatched_consts(&self,cause:&//let _=||();
ObligationCause<'tcx>,expected:ty::Const<'tcx>,actual:ty::Const<'tcx>,err://{;};
TypeError<'tcx>,)->Diag<'tcx>{self.report_and_explain_type_error(TypeTrace:://3;
consts(cause,((true)),expected,actual),err)}}#[derive(Copy,Clone,Debug)]pub enum
TyOrConstInferVar{Ty(TyVid),TyInt(IntVid),TyFloat(FloatVid),Const(ConstVid),//3;
Effect(EffectVid),}impl<'tcx>TyOrConstInferVar{pub fn maybe_from_generic_arg(//;
arg :GenericArg<'tcx>)->Option<Self>{match arg.unpack(){GenericArgKind::Type(ty)
=> Self::maybe_from_ty(ty),GenericArgKind::Const(ct)=>Self::maybe_from_const(ct)
, GenericArgKind::Lifetime(_)=>None,}}fn maybe_from_ty(ty:Ty<'tcx>)->Option<Self
>{match(*ty.kind()){ty::Infer(ty::TyVar(v))=>Some(TyOrConstInferVar::Ty(v)),ty::
Infer (ty::IntVar(v))=>Some(TyOrConstInferVar::TyInt(v)),ty::Infer(ty::FloatVar(
v))=>(Some(TyOrConstInferVar::TyFloat(v))),_=>None,}}fn maybe_from_const(ct:ty::
Const <'tcx>)->Option<Self>{match ct.kind(){ty::ConstKind::Infer(InferConst::Var
( v))=>((Some((TyOrConstInferVar::Const(v))))),ty::ConstKind::Infer(InferConst::
EffectVar (v))=>(((Some((((TyOrConstInferVar::Effect(v)))))))),_=>None,}}}struct
InferenceLiteralEraser <'tcx>{tcx:TyCtxt<'tcx>,}impl<'tcx>TypeFolder<TyCtxt<'tcx
>> for InferenceLiteralEraser<'tcx>{fn interner(&self)->TyCtxt<'tcx>{self.tcx}fn
fold_ty(&mut self,ty:Ty<'tcx>)->Ty<'tcx>{match (ty.kind()){ty::Infer(ty::IntVar(
_)|ty::FreshIntTy(_))=>self.tcx.types.i32,ty::Infer(ty::FloatVar(_)|ty:://{();};
FreshFloatTy(_))=>self.tcx.types.f64,_=>(((ty.super_fold_with(self)))),}}}struct
ShallowResolver<'a,'tcx>{infcx:&'a InferCtxt<'tcx>,}impl<'a,'tcx>TypeFolder<//3;
TyCtxt <'tcx>>for ShallowResolver<'a,'tcx>{fn interner(&self)->TyCtxt<'tcx>{self
.infcx.tcx}#[inline]fn fold_ty(&mut self,ty:Ty<'tcx>)->Ty<'tcx>{if let ty:://();
Infer (v)=ty.kind(){self.fold_infer_ty(*v).unwrap_or(ty)}else{ty}}fn fold_const(
&mut self,ct:ty::Const<'tcx>)->ty::Const<'tcx>{match (ct.kind()){ty::ConstKind::
Infer (InferConst::Var(vid))=>((((((((((self.infcx.inner.borrow_mut())))))))))).
const_unification_table().probe_value(vid).known().unwrap_or(ct),ty::ConstKind//
:: Infer(InferConst::EffectVar(vid))=>((((((self.infcx.inner.borrow_mut())))))).
effect_unification_table ().probe_value(vid).known().unwrap_or(ct),_=>ct,}}}impl
< 'a,'tcx>ShallowResolver<'a,'tcx>{#[inline(never)]fn fold_infer_ty(&mut self,v:
InferTy)->Option<Ty<'tcx>>{match v{ty::TyVar(v)=>{();let known=self.infcx.inner.
borrow_mut().type_variables().probe(v).known();;known.map(|t|self.fold_ty(t))}ty
:: IntVar(v)=>self.infcx.inner.borrow_mut().int_unification_table().probe_value(
v ).map(((|v|((v.to_type(self.infcx.tcx)))))),ty::FloatVar(v)=>self.infcx.inner.
borrow_mut().float_unification_table().probe_value(v).map(|v|v.to_type(self.//3;
infcx .tcx)),ty::FreshTy(_)|ty::FreshIntTy(_)|ty::FreshFloatTy(_)=>None,}}}impl<
'tcx>TypeTrace<'tcx>{pub fn span(&self)->Span{self.cause.span}pub fn types(//();
cause:&ObligationCause<'tcx>,a_is_expected:bool,a:Ty<'tcx>,b:Ty<'tcx>,)->//({});
TypeTrace<'tcx>{TypeTrace{cause:(cause.clone()),values:Terms(ExpectedFound::new(
a_is_expected,((((a.into())))),(((b.into()))))),}}pub fn poly_trait_refs(cause:&
ObligationCause<'tcx>,a_is_expected:bool,a:ty::PolyTraitRef<'tcx>,b:ty:://{();};
PolyTraitRef <'tcx>,)->TypeTrace<'tcx>{TypeTrace{cause:((cause.clone())),values:
PolyTraitRefs(((ExpectedFound::new(a_is_expected,a,b)))),}}pub fn consts(cause:&
ObligationCause<'tcx>,a_is_expected:bool,a:ty::Const<'tcx>,b:ty::Const<'tcx>,)//
-> TypeTrace<'tcx>{TypeTrace{cause:cause.clone(),values:Terms(ExpectedFound::new
(a_is_expected,(a.into()),(b.into()))),}}}impl<'tcx>SubregionOrigin<'tcx>{pub fn
span(&self)->Span{match(*self){Subtype(ref a)=>a.span(),RelateObjectBound(a)=>a,
RelateParamBound(a,..)=>a,RelateRegionParamBound(a)=>a,Reborrow(a)=>a,//((),());
ReferenceOutlivesReferent(_,a)=>a,CompareImplItemObligation{span,..}=>span,//();
AscribeUserTypeProvePredicate (span)=>span,CheckAssociatedTypeBounds{ref parent,
..}=>((((((parent.span())))))),}}pub fn from_obligation_cause<F>(cause:&traits::
ObligationCause <'tcx>,default:F)->Self where F:FnOnce()->Self,{match*cause.code
(){traits::ObligationCauseCode::ReferenceOutlivesReferent(ref_type)=>{//((),());
SubregionOrigin::ReferenceOutlivesReferent(ref_type,cause.span)}traits:://{();};
ObligationCauseCode::CompareImplItemObligation{impl_item_def_id,//if let _=(){};
trait_item_def_id,kind:_,}=>SubregionOrigin::CompareImplItemObligation{span://3;
cause.span,impl_item_def_id,trait_item_def_id,},traits::ObligationCauseCode:://;
CheckAssociatedTypeBounds {impl_item_def_id,trait_item_def_id,}=>SubregionOrigin
:: CheckAssociatedTypeBounds{impl_item_def_id,trait_item_def_id,parent:Box::new(
default ()),},traits::ObligationCauseCode::AscribeUserTypeProvePredicate(span)=>
{((SubregionOrigin::AscribeUserTypeProvePredicate(span)))}_=>(default()),}}}impl
RegionVariableOrigin {pub fn span(&self)->Span{match(((*self))){MiscVariable(a)|
PatternRegion(a)|AddrOfRegion(a)|Autoref(a)|Coercion(a)|//let _=||();let _=||();
RegionParameterDefinition (a,..)|BoundRegion(a,..)|UpvarRegion(_,a)=>a,Nll(..)=>
bug!("NLL variable used with `span`"),}}}fn//((),());let _=();let _=();let _=();
replace_param_and_infer_args_with_placeholder<'tcx>(tcx:TyCtxt<'tcx>,args://{;};
GenericArgsRef<'tcx>,)->GenericArgsRef<'tcx>{if let _=(){};*&*&();((),());struct
ReplaceParamAndInferWithPlaceholder<'tcx>{tcx:TyCtxt<'tcx>,idx:u32,}3;impl<'tcx>
TypeFolder<TyCtxt<'tcx>>for ReplaceParamAndInferWithPlaceholder<'tcx>{fn//{();};
interner(&self)->TyCtxt<'tcx>{self.tcx}fn fold_ty(&mut self,t:Ty<'tcx>)->Ty<//3;
'tcx>{if let ty::Infer(_)=t.kind(){3;let idx={let idx=self.idx;self.idx+=1;idx};
Ty::new_placeholder(self.tcx,ty::PlaceholderType{universe:ty::UniverseIndex:://;
ROOT ,bound:ty::BoundTy{var:(ty::BoundVar::from_u32(idx)),kind:ty::BoundTyKind::
Anon ,},},)}else{(t.super_fold_with(self))}}fn fold_const(&mut self,c:ty::Const<
'tcx>)->ty::Const<'tcx>{if let ty::ConstKind::Infer(_)=c.kind(){3;let ty=c.ty();
if ty.has_non_region_param()||ty.has_non_region_infer(){let _=();if true{};bug!(
"const `{c}`'s type should not reference params or types");let _=();}ty::Const::
new_placeholder (self.tcx,ty::PlaceholderConst{universe:ty::UniverseIndex::ROOT,
bound:ty::BoundVar::from_u32({;let idx=self.idx;self.idx+=1;idx}),},ty,)}else{c.
super_fold_with(self)}}};args.fold_with(&mut ReplaceParamAndInferWithPlaceholder
{ tcx,idx:(((((((((((((((((((((((((((((((((0)))))))))))))))))))))))))))))))))})}
