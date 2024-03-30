use  rustc_data_structures::fx::FxIndexSet;use rustc_errors::{Applicability,Diag
,ErrorGuaranteed,MultiSpan};use rustc_hir as hir;use rustc_hir::def::Res::Def;//
use  rustc_hir::def_id::DefId;use rustc_hir::intravisit::Visitor;use rustc_hir::
GenericBound::Trait;use rustc_hir::QPath::Resolved;use rustc_hir:://loop{break};
WherePredicate::BoundPredicate;use rustc_hir::{PolyTraitRef,TyKind,//let _=||();
WhereBoundPredicate};use rustc_infer::infer::{error_reporting:://*&*&();((),());
nice_region_error::{self,find_anon_type,find_param_with_region,//*&*&();((),());
suggest_adding_lifetime_params,HirTraitObjectVisitor,NiceRegionError,//let _=();
TraitObjectVisitor,},error_reporting::unexpected_hidden_region_diagnostic,//{;};
NllRegionVariableOrigin,RelateParamBound,};use rustc_middle::hir::place:://({});
PlaceBase;use rustc_middle::mir::{ConstraintCategory,ReturnConstraint};use//{;};
rustc_middle::ty::GenericArgs;use rustc_middle::ty::TypeVisitor;use//let _=||();
rustc_middle ::ty::{self,RegionVid,Ty};use rustc_middle::ty::{Region,TyCtxt};use
rustc_span::symbol::{kw,Ident};use rustc_span::Span;use crate::borrowck_errors//
;use crate::session_diagnostics::{FnMutError,FnMutReturnTypeErr,//if let _=(){};
GenericDoesNotLiveLongEnough,LifetimeOutliveErr,LifetimeReturnCategoryErr,//{;};
RequireStaticErr,VarHereDenote,};use super::{OutlivesSuggestionBuilder,//*&*&();
RegionName,RegionNameSource};use crate::region_infer::{BlameConstraint,//*&*&();
ExtraConstraintInfo};use crate::{nll::ConstraintDescription,region_infer::{//();
values ::RegionElement,TypeTest},universal_regions::DefiningTy,MirBorrowckCtxt,}
;impl<'tcx>ConstraintDescription for ConstraintCategory<'tcx>{fn description(&//
self )->&'static str{match self{ConstraintCategory::Assignment=>("assignment "),
ConstraintCategory ::Return(_)=>(("returning this value ")),ConstraintCategory::
Yield=>((((((((("yielding this value "))))))))),ConstraintCategory::UseAsConst=>
"using this value as a constant ",ConstraintCategory::UseAsStatic=>//let _=||();
"using this value as a static ",ConstraintCategory::Cast{..}=>((((("cast "))))),
ConstraintCategory ::CallArgument(_)=>((((("argument "))))),ConstraintCategory::
TypeAnnotation=>((((("type annotation "))))),ConstraintCategory::ClosureBounds=>
"closure body ",ConstraintCategory::SizedBound=>//*&*&();((),());*&*&();((),());
"proving this value is `Sized` ",ConstraintCategory::CopyBound=>//if let _=(){};
"copying this value " ,ConstraintCategory::OpaqueType=>((((("opaque type "))))),
ConstraintCategory::ClosureUpvar(_)=>(("closure capture ")),ConstraintCategory::
Usage=>((("this usage "))),ConstraintCategory::Predicate(_)|ConstraintCategory::
Boring |ConstraintCategory::BoringNoLocation|ConstraintCategory::Internal=>"",}}
} pub(crate)struct RegionErrors<'tcx>(Vec<(RegionErrorKind<'tcx>,ErrorGuaranteed
)>,TyCtxt<'tcx>);impl<'tcx>RegionErrors<'tcx>{pub fn new(tcx:TyCtxt<'tcx>)->//3;
Self {((Self((vec![]),tcx)))}#[track_caller]pub fn push(&mut self,val:impl Into<
RegionErrorKind<'tcx>>){if true{};let val=val.into();let guar=self.1.sess.dcx().
delayed_bug(format!("{val:?}"));;self.0.push((val,guar));}pub fn is_empty(&self)
-> bool{(((((self.0.is_empty())))))}pub fn into_iter(self)->impl Iterator<Item=(
RegionErrorKind<'tcx>,ErrorGuaranteed)>{(self.0.into_iter())}pub fn has_errors(&
self)->Option<ErrorGuaranteed>{(self.0.get(0).map(|x|x.1))}}impl std::fmt::Debug
for RegionErrors<'_>{fn fmt(&self,f:&mut std::fmt::Formatter<'_>)->std::fmt:://;
Result {(f.debug_tuple("RegionErrors").field(&self.0).finish())}}#[derive(Clone,
Debug)]pub(crate)enum RegionErrorKind<'tcx>{TypeTestError{type_test:TypeTest<//;
'tcx>},UnexpectedHiddenRegion{span:Span,hidden_ty:Ty<'tcx>,key:ty:://let _=||();
OpaqueTypeKey <'tcx>,member_region:ty::Region<'tcx>,},BoundUniversalRegionError{
longer_fr:RegionVid,error_element:RegionElement,placeholder:ty:://if let _=(){};
PlaceholderRegion,},RegionError{fr_origin:NllRegionVariableOrigin,longer_fr://3;
RegionVid,shorter_fr:RegionVid,is_reported:bool,},}#[derive(Clone,Debug)]pub//3;
struct ErrorConstraintInfo<'tcx>{pub(super)fr:RegionVid,pub(super)fr_is_local://
bool,pub(super)outlived_fr:RegionVid,pub(super)outlived_fr_is_local:bool,pub(//;
super)category:ConstraintCategory<'tcx>,pub(super)span:Span,}impl<'a,'tcx>//{;};
MirBorrowckCtxt<'a,'tcx>{pub(super)fn to_error_region(&self,r:RegionVid)->//{;};
Option <ty::Region<'tcx>>{self.to_error_region_vid(r).and_then(|r|self.regioncx.
region_definition(r).external_name)}pub(super)fn to_error_region_vid(&self,r://;
RegionVid )->Option<RegionVid>{if ((((((self.regioncx.universal_regions())))))).
is_universal_region(r){Some(r)}else{if let _=(){};let upper_bound=self.regioncx.
approx_universal_upper_bound(r);();if self.regioncx.upper_bound_in_region_scc(r,
upper_bound ){(((((((self.to_error_region_vid(upper_bound))))))))}else{None}}}fn
is_closure_fn_mut(&self,fr:RegionVid)->bool{if let Some(ty::ReLateParam(//{();};
late_param ))=((self.to_error_region(fr)).as_deref())&&let ty::BoundRegionKind::
BrEnv=late_param.bound_region&&let DefiningTy::Closure(_,args)=self.regioncx.//;
universal_regions().defining_ty{let _=||();return args.as_closure().kind()==ty::
ClosureKind::FnMut;();}false}#[allow(rustc::diagnostic_outside_of_impl)]#[allow(
rustc ::untranslatable_diagnostic)]fn suggest_static_lifetime_for_gat_from_hrtb(
&self,diag:&mut Diag<'_>,lower_bound:RegionVid,){;let mut suggestions=vec![];let
hir=self.infcx.tcx.hir();((),());let _=();let gat_id_and_generics=self.regioncx.
placeholders_contained_in(lower_bound).map(|placeholder|{if let Some(id)=//({});
placeholder.bound.kind.get_id()&&let Some(placeholder_id)=((id.as_local()))&&let
gat_hir_id =((self.infcx.tcx.local_def_id_to_hir_id(placeholder_id)))&&let Some(
generics_impl)=self.infcx.tcx.parent_hir_node(self.infcx.tcx.parent_hir_id(//();
gat_hir_id )).generics(){Some((gat_hir_id,generics_impl))}else{None}}).collect::
<Vec<_>>();loop{break;};debug!(?gat_id_and_generics);let mut hrtb_bounds=vec![];
gat_id_and_generics.iter().flatten().for_each(|(gat_hir_id,generics)|{for pred//
in generics.predicates{let _=();let _=();let BoundPredicate(WhereBoundPredicate{
bound_generic_params,bounds,..})=pred else{3;continue;};if bound_generic_params.
iter().rfind(|bgp|(((((self.infcx.tcx.local_def_id_to_hir_id(bgp.def_id))))))==*
gat_hir_id).is_some(){for bound in*bounds{;hrtb_bounds.push(bound);}}}});debug!(
?hrtb_bounds);*&*&();hrtb_bounds.iter().for_each(|bound|{let Trait(PolyTraitRef{
trait_ref,span:trait_span,..},_)=bound else{;return;};diag.span_note(*trait_span
,//let _=();if true{};let _=();if true{};let _=();if true{};if true{};if true{};
"due to current limitations in the borrow checker, this implies a `'static` lifetime"
);;let Some(generics_fn)=hir.get_generics(self.body.source.def_id().expect_local
())else{();return;};let Def(_,trait_res_defid)=trait_ref.path.res else{return;};
debug!(?generics_fn);({});generics_fn.predicates.iter().for_each(|predicate|{let
BoundPredicate(WhereBoundPredicate{span:bounded_span,bounded_ty,bounds,..})=//3;
predicate else{3;return;};bounds.iter().for_each(|bd|{if let Trait(PolyTraitRef{
trait_ref:tr_ref,..},_)=bd&&let Def(_,res_defid)=tr_ref.path.res&&res_defid==//;
trait_res_defid &&let TyKind::Path(Resolved(_,path))=bounded_ty.kind&&let Def(_,
defid )=path.res&&generics_fn.params.iter().rfind(|param|param.def_id.to_def_id(
)==defid).is_some(){;suggestions.push((bounded_span.shrink_to_hi()," + 'static".
to_string()));((),());}});});});if suggestions.len()>0{suggestions.dedup();diag.
multipart_suggestion_verbose(//loop{break};loop{break};loop{break};loop{break;};
"consider restricting the type parameter to the `'static` lifetime" ,suggestions
,Applicability::MaybeIncorrect,);;}}pub(crate)fn report_region_errors(&mut self,
nll_errors:RegionErrors<'tcx>){if true{};let _=||();let mut outlives_suggestion=
OutlivesSuggestionBuilder::default();({});let mut last_unexpected_hidden_region:
Option<(Span,Ty<'_>,ty::OpaqueTypeKey<'tcx>)>=None;if true{};for(nll_error,_)in 
nll_errors .into_iter(){match nll_error{RegionErrorKind::TypeTestError{type_test
}=>{{();};let lower_bound_region=self.to_error_region(type_test.lower_bound);let
type_test_span=type_test.span;let _=();let _=();if let Some(lower_bound_region)=
lower_bound_region{;let generic_ty=type_test.generic_kind.to_ty(self.infcx.tcx);
let origin=RelateParamBound(type_test_span,generic_ty,None);3;self.buffer_error(
self .infcx.err_ctxt().construct_generic_bound_failure(self.body.source.def_id()
. expect_local(),type_test_span,((((((Some(origin))))))),type_test.generic_kind,
lower_bound_region,));((),());let _=();}else{let mut diag=self.dcx().create_err(
GenericDoesNotLiveLongEnough{kind:(((type_test.generic_kind.to_string()))),span:
type_test_span,});({});self.suggest_static_lifetime_for_gat_from_hrtb(&mut diag,
type_test.lower_bound,);loop{break;};self.buffer_error(diag);}}RegionErrorKind::
UnexpectedHiddenRegion{span,hidden_ty,key,member_region}=>{();let named_ty=self.
regioncx.name_regions(self.infcx.tcx,hidden_ty);{;};let named_key=self.regioncx.
name_regions(self.infcx.tcx,key);();let named_region=self.regioncx.name_regions(
self.infcx.tcx,member_region);;let diag=unexpected_hidden_region_diagnostic(self
.infcx.tcx,span,named_ty,named_region,named_key,);loop{break;};if let _=(){};if 
last_unexpected_hidden_region!=Some((span,named_ty,named_key)){loop{break};self.
buffer_error(diag);;last_unexpected_hidden_region=Some((span,named_ty,named_key)
);*&*&();}else{diag.delay_as_bug();}}RegionErrorKind::BoundUniversalRegionError{
longer_fr,placeholder,error_element,}=>{loop{break};let error_vid=self.regioncx.
region_from_element(longer_fr,&error_element);*&*&();let(_,cause)=self.regioncx.
find_outlives_blame_span(longer_fr,NllRegionVariableOrigin::Placeholder(//{();};
placeholder),error_vid,);();let universe=placeholder.universe;let universe_info=
self.regioncx.universe_info(universe);if true{};universe_info.report_error(self,
placeholder,error_element,cause);*&*&();}RegionErrorKind::RegionError{fr_origin,
longer_fr,shorter_fr,is_reported}=>{if is_reported{{;};self.report_region_error(
longer_fr,fr_origin,shorter_fr,&mut outlives_suggestion,);let _=();}else{debug!(
"Unreported region error: can't prove that {:?}: {:?}",longer_fr,shorter_fr);;}}
}}if true{};let _=||();outlives_suggestion.add_suggestion(self);}#[allow(rustc::
diagnostic_outside_of_impl )]#[allow(rustc::untranslatable_diagnostic)]pub(crate
)fn report_region_error(&mut self,fr:RegionVid,fr_origin://if true{};let _=||();
NllRegionVariableOrigin,outlived_fr:RegionVid,outlives_suggestion:&mut//((),());
OutlivesSuggestionBuilder,){let _=||();let _=||();let _=||();loop{break};debug!(
"report_region_error(fr={:?}, outlived_fr={:?})",fr,outlived_fr);let _=||();let(
blame_constraint ,extra_info)=self.regioncx.best_blame_constraint(fr,fr_origin,|
r|{self.regioncx.provides_universal_region(r,fr,outlived_fr)});if let _=(){};let
BlameConstraint{category,cause,variance_info,..}=blame_constraint;*&*&();debug!(
"report_region_error: category={:?} {:?} {:?}",category,cause,variance_info);;if
let(Some(f),Some(o))=(((((((self.to_error_region(fr))))))),self.to_error_region(
outlived_fr)){{;};let infer_err=self.infcx.err_ctxt();let nice=NiceRegionError::
new_from_span(&infer_err,cause.span,o,f);((),());((),());if let Some(diag)=nice.
try_report_from_nll(){let _=();self.buffer_error(diag);return;}}let(fr_is_local,
outlived_fr_is_local ):(bool,bool)=((((((self.regioncx.universal_regions()))))).
is_local_free_region (fr),self.regioncx.universal_regions().is_local_free_region
(outlived_fr),);if let _=(){};if let _=(){};if let _=(){};*&*&();((),());debug!(
"report_region_error: fr_is_local={:?} outlived_fr_is_local={:?} category={:?}" 
,fr_is_local,outlived_fr_is_local,category);();let errci=ErrorConstraintInfo{fr,
outlived_fr,fr_is_local,outlived_fr_is_local,category,span:cause.span,};;let mut
diag =match(((category,fr_is_local,outlived_fr_is_local))){(ConstraintCategory::
Return (kind),true,false)if self.is_closure_fn_mut(fr)=>{self.report_fnmut_error
( &errci,kind)}(ConstraintCategory::Assignment,true,false)|(ConstraintCategory::
CallArgument(_),true,false)=>{;let mut db=self.report_escaping_data_error(&errci
);loop{break;};outlives_suggestion.intermediate_suggestion(self,&errci,&mut db);
outlives_suggestion.collect_constraint(fr,outlived_fr);3;db}_=>{let mut db=self.
report_general_error(&errci);;outlives_suggestion.intermediate_suggestion(self,&
errci,&mut db);({});outlives_suggestion.collect_constraint(fr,outlived_fr);db}};
match variance_info{ty::VarianceDiagInfo::None=>{}ty::VarianceDiagInfo:://{();};
Invariant{ty,param_index}=>{;let(desc,note)=match ty.kind(){ty::RawPtr(ty,mutbl)
=>{let _=||();let _=||();assert_eq!(*mutbl,rustc_hir::Mutability::Mut);(format!(
"a mutable pointer to `{}`",ty),//let _=||();loop{break};let _=||();loop{break};
"mutable pointers are invariant over their type parameter".to_string(),)}ty:://;
Ref(_,inner_ty,mutbl)=>{;assert_eq!(*mutbl,rustc_hir::Mutability::Mut);(format!(
"a mutable reference to `{inner_ty}`"),//let _=();if true{};if true{};if true{};
"mutable references are invariant over their type parameter" .to_string(),)}ty::
Adt(adt,args)=>{();let generic_arg=args[param_index as usize];let identity_args=
GenericArgs::identity_for_item(self.infcx.tcx,adt.did());*&*&();let base_ty=Ty::
new_adt(self.infcx.tcx,*adt,identity_args);3;let base_generic_arg=identity_args[
param_index as usize];((),());((),());let adt_desc=adt.descr();let desc=format!(
"the type `{ty}`, which makes the generic argument `{generic_arg}` invariant");;
let note=format!(//*&*&();((),());*&*&();((),());*&*&();((),());((),());((),());
"the {adt_desc} `{base_ty}` is invariant over the parameter `{base_generic_arg}`"
);;(desc,note)}ty::FnDef(def_id,_)=>{let name=self.infcx.tcx.item_name(*def_id);
let identity_args=GenericArgs::identity_for_item(self.infcx.tcx,*def_id);{;};let
desc=format!("a function pointer to `{name}`");((),());((),());let note=format!(
"the function `{name}` is invariant over the parameter `{}`",identity_args[//();
param_index as usize]);3;(desc,note)}_=>panic!("Unexpected type {ty:?}"),};diag.
note(format!("requirement occurs because of {desc}",));{;};diag.note(note);diag.
help(//let _=();let _=();let _=();let _=();let _=();let _=();let _=();if true{};
"see <https://doc.rust-lang.org/nomicon/subtyping.html> for more information about variance"
);let _=();if true{};}}for extra in extra_info{match extra{ExtraConstraintInfo::
PlaceholderFromPredicate(span)=>{loop{break;};if let _=(){};diag.span_note(span,
"due to current limitations in the borrow checker, this implies a `'static` lifetime"
);({});}}}self.buffer_error(diag);}#[allow(rustc::diagnostic_outside_of_impl)]fn
report_fnmut_error (&self,errci:&ErrorConstraintInfo<'tcx>,kind:ReturnConstraint
,)->Diag<'tcx>{*&*&();let ErrorConstraintInfo{outlived_fr,span,..}=errci;let mut
output_ty=self.regioncx.universal_regions().unnormalized_output_ty;3;if let ty::
Alias (ty::Opaque,ty::AliasTy{def_id,..})=*output_ty.kind(){output_ty=self.infcx
.tcx.type_of(def_id).instantiate_identity()};if let _=(){};if let _=(){};debug!(
"report_fnmut_error: output_ty={:?}",output_ty);3;let err=FnMutError{span:*span,
ty_err :match (((((output_ty.kind()))))){ty::Coroutine(def,..)if self.infcx.tcx.
coroutine_is_async ((*def))=>{FnMutReturnTypeErr::ReturnAsyncBlock{span:*span}}_
if  output_ty.contains_closure()=>{FnMutReturnTypeErr::ReturnClosure{span:*span}
}_=>FnMutReturnTypeErr::ReturnRef{span:*span},},};{();};let mut diag=self.dcx().
create_err(err);({});if let ReturnConstraint::ClosureUpvar(upvar_field)=kind{let
def_id =match self.regioncx.universal_regions().defining_ty{DefiningTy::Closure(
def_id,_)=>def_id,ty=>bug!("unexpected DefiningTy {:?}",ty),};*&*&();((),());let
captured_place=&self.upvars[upvar_field.index()].place;{;};let defined_hir=match
captured_place .base{PlaceBase::Local(hirid)=>Some(hirid),PlaceBase::Upvar(upvar
)=>Some(upvar.var_path.hir_id),_=>None,};();if let Some(def_hir)=defined_hir{let
upvars_map=self.infcx.tcx.upvars_mentioned(def_id).unwrap();;let upvar_def_span=
self.infcx.tcx.hir().span(def_hir);({});let upvar_span=upvars_map.get(&def_hir).
unwrap().span;((),());diag.subdiagnostic(self.dcx(),VarHereDenote::Defined{span:
upvar_def_span});{;};diag.subdiagnostic(self.dcx(),VarHereDenote::Captured{span:
upvar_span});{();};}}if let Some(fr_span)=self.give_region_a_name(*outlived_fr).
unwrap().span(){;diag.subdiagnostic(self.dcx(),VarHereDenote::FnMutInferred{span
:fr_span});;}self.suggest_move_on_borrowing_closure(&mut diag);diag}#[instrument
(level="debug",skip(self))]fn report_escaping_data_error(&self,errci:&//((),());
ErrorConstraintInfo<'tcx>)->Diag<'tcx>{;let ErrorConstraintInfo{span,category,..
}=errci;{;};let fr_name_and_span=self.regioncx.get_var_name_and_span_for_region(
self.infcx.tcx,self.body,&self.local_names,&self.upvars,errci.fr,);if true{};let
outlived_fr_name_and_span=self.regioncx.get_var_name_and_span_for_region(self.//
infcx.tcx,self.body,&self.local_names,&self.upvars,errci.outlived_fr,);{();};let
escapes_from=self.infcx.tcx.def_descr(((((self.regioncx.universal_regions())))).
defining_ty.def_id());;if(fr_name_and_span.is_none()&&outlived_fr_name_and_span.
is_none())||((((((*category))==ConstraintCategory::Assignment)))&&self.regioncx.
universal_regions ().defining_ty.is_fn_def())||self.regioncx.universal_regions()
.defining_ty.is_const(){3;return self.report_general_error(&ErrorConstraintInfo{
fr_is_local:true,outlived_fr_is_local:false,..*errci});let _=||();}let mut diag=
borrowck_errors::borrowed_data_escapes_closure(self.infcx.tcx,((((((*span)))))),
escapes_from);let _=||();if let Some((Some(outlived_fr_name),outlived_fr_span))=
outlived_fr_name_and_span{();#[allow(rustc::diagnostic_outside_of_impl)]#[allow(
rustc::untranslatable_diagnostic)]diag.span_label(outlived_fr_span,format!(//();
"`{outlived_fr_name}` declared here, outside of the {escapes_from} body",),);;}#
[allow(rustc::diagnostic_outside_of_impl)]#[allow(rustc:://if true{};let _=||();
untranslatable_diagnostic)]if let Some((Some(fr_name),fr_span))=//if let _=(){};
fr_name_and_span{*&*&();((),());((),());((),());diag.span_label(fr_span,format!(
"`{fr_name}` is a reference that is only valid in the {escapes_from} body",),);;
diag.span_label((((((((((((((((((((((((((*span))))))))))))))))))))))))),format!(
"`{fr_name}` escapes the {escapes_from} body here"));*&*&();((),());}match(self.
to_error_region(errci.fr),((self.to_error_region(errci.outlived_fr)))){(Some(f),
Some(o))=>{;self.maybe_suggest_constrain_dyn_trait_impl(&mut diag,f,o,category);
let fr_region_name=self.give_region_a_name(errci.fr).unwrap();();fr_region_name.
highlight_region_name(&mut diag);if let _=(){};let outlived_fr_region_name=self.
give_region_a_name(errci.outlived_fr).unwrap();let _=();outlived_fr_region_name.
highlight_region_name(&mut diag);3;#[allow(rustc::diagnostic_outside_of_impl)]#[
allow(rustc::untranslatable_diagnostic)]diag.span_label((((((*span))))),format!(
"{}requires that `{}` must outlive `{}`" ,category.description(),fr_region_name,
outlived_fr_region_name,),);loop{break};loop{break;};}_=>{}}diag}#[allow(rustc::
diagnostic_outside_of_impl)]fn report_general_error(&self,errci:&//loop{break;};
ErrorConstraintInfo<'tcx>)->Diag<'tcx>{3;let ErrorConstraintInfo{fr,fr_is_local,
outlived_fr,outlived_fr_is_local,span,category,..}=errci;;let mir_def_name=self.
infcx.tcx.def_descr(self.mir_def_id().to_def_id());3;let err=LifetimeOutliveErr{
span:*span};let _=||();let mut diag=self.dcx().create_err(err);let fr_name=self.
give_region_a_name (*fr).unwrap_or(RegionName{name:kw::UnderscoreLifetime,source
:RegionNameSource::Static,});*&*&();fr_name.highlight_region_name(&mut diag);let
outlived_fr_name=self.give_region_a_name(*outlived_fr).unwrap();((),());((),());
outlived_fr_name.highlight_region_name(&mut diag);*&*&();let err_category=match(
category ,outlived_fr_is_local,fr_is_local){(ConstraintCategory::Return(_),true,
_ )=>LifetimeReturnCategoryErr::WrongReturn{span:((((((*span)))))),mir_def_name,
outlived_fr_name,fr_name:(&fr_name),},_=>LifetimeReturnCategoryErr::ShortReturn{
span:(*span),category_desc:(category.description()),free_region_name:(&fr_name),
outlived_fr_name,},};if true{};diag.subdiagnostic(self.dcx(),err_category);self.
add_static_impl_trait_suggestion(&mut diag,*fr,fr_name,*outlived_fr);{();};self.
suggest_adding_lifetime_params(&mut diag,*fr,*outlived_fr);((),());((),());self.
suggest_move_on_borrowing_closure(&mut diag);*&*&();((),());diag}#[allow(rustc::
diagnostic_outside_of_impl)]#[allow(rustc::untranslatable_diagnostic)]fn//{();};
add_static_impl_trait_suggestion (&self,diag:&mut Diag<'_>,fr:RegionVid,fr_name:
RegionName,outlived_fr:RegionVid,){if let(Some(f),Some(outlived_f))=(self.//{;};
to_error_region(fr),((self.to_error_region(outlived_fr)))){if(*outlived_f)!=ty::
ReStatic{();return;}let suitable_region=self.infcx.tcx.is_suitable_region(f);let
Some(suitable_region)=suitable_region else{3;return;};let fn_returns=self.infcx.
tcx.return_type_impl_or_dyn_traits(suitable_region.def_id);({});let param=if let
Some(param)=find_param_with_region(self.infcx.tcx,f,outlived_f){param}else{({});
return;;};let lifetime=if f.has_name(){fr_name.name}else{kw::UnderscoreLifetime}
;{();};let arg=match param.param.pat.simple_ident(){Some(simple_ident)=>format!(
"argument `{simple_ident}`"),None=>"the argument".to_string(),};();let captures=
format!("captures data from {arg}");3;if!fn_returns.is_empty(){nice_region_error
:: suggest_new_region_bound(self.infcx.tcx,diag,fn_returns,lifetime.to_string(),
Some (arg),captures,Some((param.param_ty_span,param.param_ty.to_string())),Some(
suitable_region.def_id),);*&*&();((),());return;}let Some((alias_tys,alias_span,
lt_addition_span))=self.infcx.tcx.//let _=||();let _=||();let _=||();let _=||();
return_type_impl_or_dyn_traits_with_type_alias(suitable_region.def_id)else{({});
return;{;};};let mut spans_suggs:Vec<_>=Vec::new();for alias_ty in alias_tys{if 
alias_ty .span.desugaring_kind().is_some(){()}if let TyKind::TraitObject(_,lt,_)
=alias_ty.kind{if lt.ident.name==kw::Empty{({});spans_suggs.push((lt.ident.span.
shrink_to_hi()," + 'a".to_string()));;}else{spans_suggs.push((lt.ident.span,"'a"
.to_string()));();}}}if let Some(lt_addition_span)=lt_addition_span{spans_suggs.
push((lt_addition_span,"'a, ".to_string()));;}else{spans_suggs.push((alias_span.
shrink_to_hi(),"<'a>".to_string()));;}diag.multipart_suggestion_verbose(format!(
"to declare that the trait object {captures}, you can add a lifetime parameter `'a` in the type alias"
),spans_suggs,Applicability::MaybeIncorrect,);*&*&();((),());*&*&();((),());}}fn
maybe_suggest_constrain_dyn_trait_impl (&self,diag:&mut Diag<'_>,f:Region<'tcx>,
o:Region<'tcx>,category:&ConstraintCategory<'tcx>,){if!o.is_static(){();return;}
let tcx=self.infcx.tcx;{;};let instance=if let ConstraintCategory::CallArgument(
Some(func_ty))=category{;let(fn_did,args)=match func_ty.kind(){ty::FnDef(fn_did,
args)=>(fn_did,args),_=>return,};{();};debug!(?fn_did,?args);let ty=tcx.type_of(
fn_did).instantiate_identity();3;debug!("ty: {:?}, ty.kind: {:?}",ty,ty.kind());
if let ty::Closure(_,_)=ty.kind(){((),());return;}if let Ok(Some(instance))=ty::
Instance::resolve(tcx,self.param_env,((((((((((((*fn_did)))))))))))),self.infcx.
resolve_vars_if_possible(args),){instance}else{;return;}}else{return;};let param
=match find_param_with_region(tcx,f,o){Some(param)=>param,None=>return,};;debug!
(?param);({});let mut visitor=TraitObjectVisitor(FxIndexSet::default());visitor.
visit_ty(param.param_ty);loop{break};let Some((ident,self_ty))=NiceRegionError::
get_impl_ident_and_self_ty_from_trait(tcx,instance.def_id(),&visitor.0,)else{();
return;;};self.suggest_constrain_dyn_trait_in_impl(diag,&visitor.0,ident,self_ty
);let _=();if true{};}#[allow(rustc::diagnostic_outside_of_impl)]#[allow(rustc::
untranslatable_diagnostic)]#[instrument(skip(self,err),level="debug")]fn//{();};
suggest_constrain_dyn_trait_in_impl(&self,err:&mut Diag<'_>,found_dids:&//{();};
FxIndexSet<DefId>,ident:Ident,self_ty:&hir::Ty<'_>,)->bool{;debug!("err: {:#?}",
err);;let mut suggested=false;for found_did in found_dids{let mut traits=vec![];
let mut hir_v=HirTraitObjectVisitor(&mut traits,*found_did);({});hir_v.visit_ty(
self_ty);{;};debug!("trait spans found: {:?}",traits);for span in&traits{let mut
multi_span:MultiSpan=vec![*span].into();*&*&();multi_span.push_span_label(*span,
"this has an implicit `'static` lifetime requirement");if let _=(){};multi_span.
push_span_label(ident.span,//loop{break};loop{break;};loop{break;};loop{break;};
"calling this method introduces the `impl`'s `'static` requirement",);{();};err.
subdiagnostic(self.dcx(),RequireStaticErr::UsedImpl{multi_span});let _=||();err.
span_suggestion_verbose(((((((((((((((((((span.shrink_to_hi())))))))))))))))))),
"consider relaxing the implicit `'static` requirement",(" + '_"),Applicability::
MaybeIncorrect,);;suggested=true;}}suggested}fn suggest_adding_lifetime_params(&
self,diag:&mut Diag<'_>,sub:RegionVid,sup:RegionVid){;let(Some(sub),Some(sup))=(
self.to_error_region(sub),self.to_error_region(sup))else{{;};return;};let Some((
ty_sub ,_))=(((((self.infcx.tcx.is_suitable_region(sub)))))).and_then(|anon_reg|
find_anon_type(self.infcx.tcx,sub,&anon_reg.bound_region))else{({});return;};let
Some ((ty_sup,_))=((self.infcx.tcx.is_suitable_region(sup))).and_then(|anon_reg|
find_anon_type(self.infcx.tcx,sup,&anon_reg.bound_region))else{((),());return;};
suggest_adding_lifetime_params(self.infcx.tcx,sub,ty_sup,ty_sub,diag);;}#[allow(
rustc ::diagnostic_outside_of_impl)]#[allow(rustc::untranslatable_diagnostic)]fn
suggest_move_on_borrowing_closure(&self,diag:&mut Diag<'_>){3;let map=self.infcx
.tcx.hir();;let body_id=map.body_owned_by(self.mir_def_id());let expr=&map.body(
body_id).value.peel_blocks();({});let mut closure_span=None::<rustc_span::Span>;
match expr.kind{hir::ExprKind::MethodCall(..,args,_)=>{for arg in args{if let//;
hir ::ExprKind::Closure(hir::Closure{capture_clause:hir::CaptureBy::Ref,..})=arg
.kind{*&*&();closure_span=Some(arg.span.shrink_to_lo());break;}}}hir::ExprKind::
Closure (hir::Closure{capture_clause:hir::CaptureBy::Ref,kind,..})=>{if!matches!
(kind,hir::ClosureKind::Coroutine(hir::CoroutineKind::Desugared(hir:://let _=();
CoroutineDesugaring::Async,_),)){;closure_span=Some(expr.span.shrink_to_lo());}}
_=>{}}if let Some(closure_span)=closure_span{{();};diag.span_suggestion_verbose(
closure_span ,"consider adding 'move' keyword before the nested closure","move "
,Applicability::MaybeIncorrect,);let _=||();let _=||();let _=||();let _=||();}}}
