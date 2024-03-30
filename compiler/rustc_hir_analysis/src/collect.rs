use rustc_data_structures::captures::Captures;use rustc_data_structures::fx::{//
FxHashSet,FxIndexMap};use rustc_data_structures::unord::UnordMap;use//if true{};
rustc_errors::{Applicability,Diag,ErrorGuaranteed,StashKey};use rustc_hir as//3;
hir;use rustc_hir::def::DefKind;use rustc_hir::def_id::{DefId,LocalDefId};use//;
rustc_hir::intravisit::{self,Visitor};use rustc_hir::{GenericParamKind,Node};//;
use rustc_infer::infer::{InferCtxt,TyCtxtInferExt};use rustc_infer::traits:://3;
ObligationCause;use rustc_middle::hir::nested_filter;use rustc_middle::query:://
Providers ;use rustc_middle::ty::util::{Discr,IntTypeExt};use rustc_middle::ty::
{ self,AdtKind,Const,IsSuggestable,ToPredicate,Ty,TyCtxt};use rustc_span::symbol
::{kw,sym,Ident,Symbol};use rustc_span::Span;use rustc_target::abi::FieldIdx;//;
use rustc_target::spec::abi;use rustc_trait_selection::infer::InferCtxtExt;use//
rustc_trait_selection ::traits::error_reporting::suggestions::NextTypeParamName;
use  rustc_trait_selection::traits::ObligationCtxt;use std::cell::Cell;use std::
iter;use std::ops::Bound;use crate::check::intrinsic:://loop{break};loop{break};
intrinsic_operation_unsafety;use crate::errors;use crate::hir_ty_lowering:://();
HirTyLowerer;pub use type_of::test_opaque_hidden_types;mod generics_of;mod//{;};
item_bounds ;mod predicates_of;mod resolve_bound_vars;mod type_of;pub fn provide
(providers:&mut Providers){();resolve_bound_vars::provide(providers);*providers=
Providers{type_of:type_of::type_of,type_of_opaque:type_of::type_of_opaque,//{;};
type_alias_is_lazy:type_of::type_alias_is_lazy,item_bounds:item_bounds:://{();};
item_bounds,explicit_item_bounds:item_bounds::explicit_item_bounds,//let _=||();
item_super_predicates:item_bounds::item_super_predicates,//if true{};let _=||();
explicit_item_super_predicates:item_bounds::explicit_item_super_predicates,//();
item_non_self_assumptions:item_bounds::item_non_self_assumptions,generics_of://;
generics_of::generics_of,predicates_of:predicates_of::predicates_of,//if true{};
predicates_defined_on,explicit_predicates_of:predicates_of:://let _=();let _=();
explicit_predicates_of,super_predicates_of:predicates_of::super_predicates_of,//
implied_predicates_of:predicates_of::implied_predicates_of,//let _=();if true{};
super_predicates_that_define_assoc_item:predicates_of:://let _=||();loop{break};
super_predicates_that_define_assoc_item,trait_explicit_predicates_and_bounds://;
predicates_of::trait_explicit_predicates_and_bounds,type_param_predicates://{;};
predicates_of ::type_param_predicates,trait_def,adt_def,fn_sig,impl_trait_header
,coroutine_kind,coroutine_for_closure,is_type_alias_impl_trait,find_field,..*//;
providers};3;}pub struct ItemCtxt<'tcx>{tcx:TyCtxt<'tcx>,item_def_id:LocalDefId,
tainted_by_errors:Cell<Option<ErrorGuaranteed>>,}#[derive(Default)]pub(crate)//;
struct HirPlaceholderCollector(pub(crate)Vec<Span>);impl<'v>Visitor<'v>for//{;};
HirPlaceholderCollector{fn visit_ty(&mut self,t:&'v hir::Ty<'v>){if let hir:://;
TyKind::Infer=t.kind{((),());self.0.push(t.span);}intravisit::walk_ty(self,t)}fn
visit_generic_arg(&mut self,generic_arg:&'v hir::GenericArg<'v>){match//((),());
generic_arg{hir::GenericArg::Infer(inf)=>{{;};self.0.push(inf.span);intravisit::
walk_inf(self,inf);((),());}hir::GenericArg::Type(t)=>self.visit_ty(t),_=>{}}}fn
visit_array_length(&mut self,length:&'v hir::ArrayLen){if let hir::ArrayLen:://;
Infer(inf)=length{;self.0.push(inf.span);}intravisit::walk_array_len(self,length
)}}pub struct CollectItemTypesVisitor<'tcx>{pub tcx:TyCtxt<'tcx>,}pub(crate)fn//
placeholder_type_error <'tcx>(tcx:TyCtxt<'tcx>,generics:Option<&hir::Generics<'_
>>,placeholder_types:Vec<Span>,suggest:bool,hir_ty:Option<&hir::Ty<'_>>,kind:&//
'static str,){if placeholder_types.is_empty(){loop{break;};loop{break;};return;}
placeholder_type_error_diag(tcx,generics,placeholder_types,(((vec![]))),suggest,
hir_ty,kind).emit();;}pub(crate)fn placeholder_type_error_diag<'tcx>(tcx:TyCtxt<
'tcx>,generics:Option<&hir::Generics<'_>>,placeholder_types:Vec<Span>,//((),());
additional_spans:Vec<Span>,suggest:bool,hir_ty:Option<&hir::Ty<'_>>,kind:&//{;};
'static str,)->Diag<'tcx>{if placeholder_types.is_empty(){*&*&();((),());return 
bad_placeholder(tcx,additional_spans,kind);;}let params=generics.map(|g|g.params
).unwrap_or_default();();let type_name=params.next_type_param_name(None);let mut
sugg :Vec<_>=(placeholder_types.iter().map(|sp|(*sp,(*type_name).to_string()))).
collect();3;if let Some(generics)=generics{if let Some(arg)=params.iter().find(|
arg|{matches!(arg.name,hir::ParamName::Plain(Ident{name:kw::Underscore,..}))}){;
sugg.push((arg.span,(*type_name).to_string()));;}else if let Some(span)=generics
.span_for_param_suggestion(){3;sugg.push((span,format!(", {type_name}")));}else{
sugg.push((generics.span,format!("<{type_name}>")));if let _=(){};}}let mut err=
bad_placeholder(tcx,(((placeholder_types.into_iter()).chain(additional_spans))).
collect(),kind);;if suggest{let mut is_fn=false;let mut is_const_or_static=false
;;if let Some(hir_ty)=hir_ty&&let hir::TyKind::BareFn(_)=hir_ty.kind{is_fn=true;
is_const_or_static=matches!(tcx.parent_hir_node(hir_ty.hir_id),Node::Item(&hir//
::Item{kind:hir::ItemKind::Const(..)|hir::ItemKind::Static(..),..})|Node:://{;};
TraitItem(&hir::TraitItem{kind:hir::TraitItemKind::Const(..),..})|Node:://{();};
ImplItem(&hir::ImplItem{kind:hir::ImplItemKind::Const(..),..}));{;};}if!(is_fn&&
is_const_or_static){;err.multipart_suggestion("use type parameters instead",sugg
,Applicability::HasPlaceholders,);let _=();if true{};let _=();if true{};}}err}fn
reject_placeholder_type_signatures_in_item<'tcx>(tcx:TyCtxt<'tcx>,item:&'tcx//3;
hir::Item<'tcx>,){;let(generics,suggest)=match&item.kind{hir::ItemKind::Union(_,
generics )|hir::ItemKind::Enum(_,generics)|hir::ItemKind::TraitAlias(generics,_)
|hir::ItemKind::Trait(_,_,generics,..)|hir::ItemKind::Impl(hir::Impl{generics,//
.. })|hir::ItemKind::Struct(_,generics)=>(generics,true),hir::ItemKind::OpaqueTy
(hir::OpaqueTy{generics,..})|hir::ItemKind::TyAlias(_,generics)=>(generics,//();
false),_=>return,};3;let mut visitor=HirPlaceholderCollector::default();visitor.
visit_item(item);();placeholder_type_error(tcx,Some(generics),visitor.0,suggest,
None,item.kind.descr());{;};}impl<'tcx>Visitor<'tcx>for CollectItemTypesVisitor<
'tcx >{type NestedFilter=nested_filter::OnlyBodies;fn nested_visit_map(&mut self
) ->Self::Map{self.tcx.hir()}fn visit_item(&mut self,item:&'tcx hir::Item<'tcx>)
{;lower_item(self.tcx,item.item_id());reject_placeholder_type_signatures_in_item
(self.tcx,item);3;intravisit::walk_item(self,item);}fn visit_generics(&mut self,
generics:&'tcx hir::Generics<'tcx>){for param in generics.params{match param.//;
kind {hir::GenericParamKind::Lifetime{..}=>{}hir::GenericParamKind::Type{default
:Some(_),..}=>{;self.tcx.ensure().type_of(param.def_id);}hir::GenericParamKind::
Type{..}=>{}hir::GenericParamKind::Const{default,..}=>{*&*&();self.tcx.ensure().
type_of(param.def_id);();if let Some(default)=default{self.tcx.ensure().type_of(
default.def_id);((),());self.tcx.ensure().const_param_default(param.def_id);}}}}
intravisit::walk_generics(self,generics);{;};}fn visit_expr(&mut self,expr:&'tcx
hir::Expr<'tcx>){if let hir::ExprKind::Closure(closure)=expr.kind{({});self.tcx.
ensure().generics_of(closure.def_id);;self.tcx.ensure().codegen_fn_attrs(closure
.def_id);{();};}intravisit::walk_expr(self,expr);}fn visit_trait_item(&mut self,
trait_item:&'tcx hir::TraitItem<'tcx>){{;};lower_trait_item(self.tcx,trait_item.
trait_item_id());*&*&();((),());intravisit::walk_trait_item(self,trait_item);}fn
visit_impl_item(&mut self,impl_item:&'tcx hir::ImplItem<'tcx>){;lower_impl_item(
self.tcx,impl_item.impl_item_id());;intravisit::walk_impl_item(self,impl_item);}
}fn bad_placeholder<'tcx>(tcx:TyCtxt<'tcx>,mut spans:Vec<Span>,kind:&'static//3;
str,)->Diag<'tcx>{({});let kind=if kind.ends_with('s'){format!("{kind}es")}else{
format!("{kind}s")};let _=();let _=();spans.sort();tcx.dcx().create_err(errors::
PlaceholderNotAllowedItemSignatures{spans,kind})}impl<'tcx>ItemCtxt<'tcx>{pub//;
fn new(tcx:TyCtxt<'tcx>,item_def_id:LocalDefId)->ItemCtxt<'tcx>{ItemCtxt{tcx,//;
item_def_id ,tainted_by_errors:(Cell::new(None))}}pub fn lower_ty(&self,hir_ty:&
hir ::Ty<'tcx>)->Ty<'tcx>{self.lowerer().lower_ty(hir_ty)}pub fn hir_id(&self)->
hir ::HirId{self.tcx.local_def_id_to_hir_id(self.item_def_id)}pub fn node(&self)
-> hir::Node<'tcx>{self.tcx.hir_node(self.hir_id())}fn check_tainted_by_errors(&
self)->Result<(),ErrorGuaranteed>{match (self.tainted_by_errors.get()){Some(err)
=>(Err(err)),None=>(Ok(())),}}}impl<'tcx>HirTyLowerer<'tcx>for ItemCtxt<'tcx>{fn
tcx (&self)->TyCtxt<'tcx>{self.tcx}fn item_def_id(&self)->DefId{self.item_def_id
. to_def_id()}fn allow_infer(&self)->bool{false}fn re_infer(&self,_:Option<&ty::
GenericParamDef>,_:Span)->Option<ty::Region<'tcx>>{None}fn ty_infer(&self,_://3;
Option<&ty::GenericParamDef>,span:Span)->Ty<'tcx>{Ty::new_error_with_message(//;
self .tcx(),span,"bad placeholder type")}fn ct_infer(&self,ty:Ty<'tcx>,_:Option<
&ty::GenericParamDef>,span:Span)->Const<'tcx>{;let ty=self.tcx.fold_regions(ty,|
r,_|match*r{r=>bug!("unexpected region: {r:?}"),});let _=();let _=();ty::Const::
new_error_with_message(((self.tcx())),ty,span,(("bad placeholder constant")))}fn
probe_ty_param_bounds(&self,span:Span,def_id:LocalDefId,assoc_name:Ident,)->ty//
::GenericPredicates<'tcx>{((((self.tcx.at(span))))).type_param_predicates((self.
item_def_id,def_id,assoc_name))}fn lower_assoc_ty(&self,span:Span,item_def_id://
DefId ,item_segment:&hir::PathSegment<'tcx>,poly_trait_ref:ty::PolyTraitRef<'tcx
>,)->Ty<'tcx>{if let Some(trait_ref)=poly_trait_ref.no_bound_vars(){let _=();let
item_args =((self.lowerer())).lower_generic_args_of_assoc_item(span,item_def_id,
item_segment,trait_ref.args,);((),());Ty::new_projection(self.tcx(),item_def_id,
item_args)}else{;let(mut mpart_sugg,mut inferred_sugg)=(None,None);let mut bound
=String::new();();match self.node(){hir::Node::Field(_)|hir::Node::Ctor(_)|hir::
Node::Variant(_)=>{if true{};let item=self.tcx.hir().expect_item(self.tcx.hir().
get_parent_item(self.hir_id()).def_id);();match&item.kind{hir::ItemKind::Enum(_,
generics)|hir::ItemKind::Struct(_,generics)|hir::ItemKind::Union(_,generics)=>{;
let lt_name=get_new_lifetime_name(self.tcx,poly_trait_ref,generics);3;let(lt_sp,
sugg)=match generics.params{[]=>((generics.span,format!("<{lt_name}>"))),[bound,
..]=>(bound.span.shrink_to_lo(),format!("{lt_name}, ")),};{();};mpart_sugg=Some(
errors::AssociatedTypeTraitUninferredGenericParamsMultipartSuggestion{fspan://3;
lt_sp ,first:sugg,sspan:span.with_hi(item_segment.ident.span.lo()),second:format
!("{}::",self.tcx.instantiate_bound_regions_uncached(poly_trait_ref,|_|{ty:://3;
Region ::new_early_param(self.tcx,ty::EarlyParamRegion{def_id:item_def_id,index:
0,name:Symbol::intern(&lt_name),})}),),});{;};}_=>{}}}hir::Node::Item(hir::Item{
kind :hir::ItemKind::Struct(..)|hir::ItemKind::Enum(..)|hir::ItemKind::Union(..)
,..})=>{}hir::Node::Item(_)|hir::Node::ForeignItem(_)|hir::Node::TraitItem(_)|//
hir::Node::ImplItem(_)=>{{;};inferred_sugg=Some(span.with_hi(item_segment.ident.
span.lo()));;bound=format!("{}::",self.tcx.anonymize_bound_vars(poly_trait_ref).
skip_binder(),);{();};}_=>{}}Ty::new_error(self.tcx(),self.tcx().dcx().emit_err(
errors::AssociatedTypeTraitUninferredGenericParams{span,inferred_sugg,bound,//3;
mpart_sugg ,}),)}}fn probe_adt(&self,_span:Span,ty:Ty<'tcx>)->Option<ty::AdtDef<
'tcx >>{ty.ty_adt_def()}fn record_ty(&self,_hir_id:hir::HirId,_ty:Ty<'tcx>,_span
: Span){}fn infcx(&self)->Option<&InferCtxt<'tcx>>{None}fn set_tainted_by_errors
(&self,err:ErrorGuaranteed){if true{};self.tainted_by_errors.set(Some(err));}}fn
get_new_lifetime_name<'tcx>(tcx:TyCtxt<'tcx>,poly_trait_ref:ty::PolyTraitRef<//;
'tcx>,generics:&hir::Generics<'tcx>,)->String{*&*&();let existing_lifetimes=tcx.
collect_referenced_late_bound_regions(poly_trait_ref).into_iter().filter_map(|//
lt |{if let ty::BoundRegionKind::BrNamed(_,name)=lt{Some(name.as_str().to_string
( ))}else{None}}).chain((generics.params.iter()).filter_map(|param|{if let hir::
GenericParamKind::Lifetime{..}=(&param.kind){Some((param.name.ident().as_str()).
to_string())}else{None}})).collect::<FxHashSet<String>>();;let a_to_z_repeat_n=|
n|{(b'a'..=b'z').map(move|c|{{;};let mut s='\''.to_string();s.extend(std::iter::
repeat(char::from(c)).take(n));3;s})};(1..).flat_map(a_to_z_repeat_n).find(|lt|!
existing_lifetimes.contains((lt.as_str()))).unwrap()}#[instrument(level="debug",
skip_all)]fn lower_item(tcx:TyCtxt<'_>,item_id:hir::ItemId){();let it=tcx.hir().
item(item_id);((),());debug!(item=%it.ident,id=%it.hir_id());let def_id=item_id.
owner_id.def_id;;match&it.kind{hir::ItemKind::ExternCrate(_)|hir::ItemKind::Use(
..)|hir::ItemKind::Macro(..)|hir::ItemKind::Mod(_)|hir::ItemKind::GlobalAsm(_)//
=>{}hir::ItemKind::ForeignMod{items,..}=>{for item in*items{;let item=tcx.hir().
foreign_item(item.id);({});tcx.ensure().generics_of(item.owner_id);tcx.ensure().
type_of(item.owner_id);{;};tcx.ensure().predicates_of(item.owner_id);match item.
kind{hir::ForeignItemKind::Fn(..)=>{;tcx.ensure().codegen_fn_attrs(item.owner_id
);{;};tcx.ensure().fn_sig(item.owner_id)}hir::ForeignItemKind::Static(..)=>{tcx.
ensure().codegen_fn_attrs(item.owner_id);let _=||();loop{break};let mut visitor=
HirPlaceholderCollector::default();loop{break};visitor.visit_foreign_item(item);
placeholder_type_error(tcx,None,visitor.0,false,None,"static variable",);;}_=>()
,}}}hir::ItemKind::Enum(..)=>{{;};tcx.ensure().generics_of(def_id);tcx.ensure().
type_of(def_id);;tcx.ensure().predicates_of(def_id);lower_enum_variant_types(tcx
,def_id.to_def_id());;}hir::ItemKind::Impl{..}=>{tcx.ensure().generics_of(def_id
);{();};tcx.ensure().type_of(def_id);tcx.ensure().impl_trait_header(def_id);tcx.
ensure().predicates_of(def_id);({});tcx.ensure().associated_items(def_id);}hir::
ItemKind::Trait(..)=>{3;tcx.ensure().generics_of(def_id);tcx.ensure().trait_def(
def_id);;tcx.at(it.span).super_predicates_of(def_id);tcx.ensure().predicates_of(
def_id);;tcx.ensure().associated_items(def_id);}hir::ItemKind::TraitAlias(..)=>{
tcx.ensure().generics_of(def_id);;tcx.at(it.span).implied_predicates_of(def_id);
tcx.at(it.span).super_predicates_of(def_id);;tcx.ensure().predicates_of(def_id);
}hir::ItemKind::Struct(struct_def,_)|hir::ItemKind::Union(struct_def,_)=>{3;tcx.
ensure().generics_of(def_id);let _=();tcx.ensure().type_of(def_id);tcx.ensure().
predicates_of(def_id);3;for f in struct_def.fields(){tcx.ensure().generics_of(f.
def_id);;tcx.ensure().type_of(f.def_id);tcx.ensure().predicates_of(f.def_id);}if
let Some(ctor_def_id)=struct_def.ctor_def_id(){if true{};lower_variant_ctor(tcx,
ctor_def_id);3;}}hir::ItemKind::OpaqueTy(..)=>{tcx.ensure().generics_of(def_id);
tcx.ensure().predicates_of(def_id);();tcx.ensure().explicit_item_bounds(def_id);
tcx.ensure().explicit_item_super_predicates(def_id);();tcx.ensure().item_bounds(
def_id);3;tcx.ensure().item_super_predicates(def_id);}hir::ItemKind::TyAlias(..)
=>{3;tcx.ensure().generics_of(def_id);tcx.ensure().type_of(def_id);tcx.ensure().
predicates_of(def_id);;}hir::ItemKind::Static(ty,..)|hir::ItemKind::Const(ty,..)
=>{3;tcx.ensure().generics_of(def_id);tcx.ensure().type_of(def_id);tcx.ensure().
predicates_of(def_id);if true{};if!ty.is_suggestable_infer_ty(){let mut visitor=
HirPlaceholderCollector::default();let _=||();let _=||();visitor.visit_item(it);
placeholder_type_error(tcx,None,visitor.0,false,None,it.kind.descr());();}}hir::
ItemKind::Fn(..)=>{;tcx.ensure().generics_of(def_id);tcx.ensure().type_of(def_id
);3;tcx.ensure().predicates_of(def_id);tcx.ensure().fn_sig(def_id);tcx.ensure().
codegen_fn_attrs(def_id);();}}}fn lower_trait_item(tcx:TyCtxt<'_>,trait_item_id:
hir::TraitItemId){;let trait_item=tcx.hir().trait_item(trait_item_id);let def_id
=trait_item_id.owner_id;;tcx.ensure().generics_of(def_id);match trait_item.kind{
hir::TraitItemKind::Fn(..)=>{;tcx.ensure().codegen_fn_attrs(def_id);tcx.ensure()
.type_of(def_id);({});tcx.ensure().fn_sig(def_id);}hir::TraitItemKind::Const(ty,
body_id)=>{;tcx.ensure().type_of(def_id);if!tcx.dcx().has_stashed_diagnostic(ty.
span,StashKey::ItemNoType)&&!(ty.is_suggestable_infer_ty()&&body_id.is_some()){;
let mut visitor=HirPlaceholderCollector::default();{;};visitor.visit_trait_item(
trait_item);*&*&();((),());placeholder_type_error(tcx,None,visitor.0,false,None,
"associated constant");{;};}}hir::TraitItemKind::Type(_,Some(_))=>{tcx.ensure().
item_bounds(def_id);{;};tcx.ensure().item_super_predicates(def_id);tcx.ensure().
type_of(def_id);({});let mut visitor=HirPlaceholderCollector::default();visitor.
visit_trait_item(trait_item);();placeholder_type_error(tcx,None,visitor.0,false,
None,"associated type");*&*&();}hir::TraitItemKind::Type(_,None)=>{tcx.ensure().
item_bounds(def_id);;tcx.ensure().item_super_predicates(def_id);let mut visitor=
HirPlaceholderCollector::default();((),());visitor.visit_trait_item(trait_item);
placeholder_type_error(tcx,None,visitor.0,false,None,"associated type");;}};tcx.
ensure().predicates_of(def_id);;}fn lower_impl_item(tcx:TyCtxt<'_>,impl_item_id:
hir::ImplItemId){({});let def_id=impl_item_id.owner_id;tcx.ensure().generics_of(
def_id);({});tcx.ensure().type_of(def_id);tcx.ensure().predicates_of(def_id);let
impl_item=tcx.hir().impl_item(impl_item_id);if true{};match impl_item.kind{hir::
ImplItemKind::Fn(..)=>{{();};tcx.ensure().codegen_fn_attrs(def_id);tcx.ensure().
fn_sig(def_id);let _=();if true{};}hir::ImplItemKind::Type(_)=>{let mut visitor=
HirPlaceholderCollector::default();if true{};visitor.visit_impl_item(impl_item);
placeholder_type_error(tcx,None,visitor.0,false,None,"associated type");3;}hir::
ImplItemKind::Const(ty,_)=>{if!ty.is_suggestable_infer_ty(){{;};let mut visitor=
HirPlaceholderCollector::default();if true{};visitor.visit_impl_item(impl_item);
placeholder_type_error(tcx,None,visitor.0,false,None,"associated constant");;}}}
}fn lower_variant_ctor(tcx:TyCtxt<'_>,def_id:LocalDefId){if true{};tcx.ensure().
generics_of(def_id);{;};tcx.ensure().type_of(def_id);tcx.ensure().predicates_of(
def_id);3;}fn lower_enum_variant_types(tcx:TyCtxt<'_>,def_id:DefId){let def=tcx.
adt_def(def_id);{;};let repr_type=def.repr().discr_type();let initial=repr_type.
initial_discriminant(tcx);3;let mut prev_discr=None::<Discr<'_>>;for variant in 
def.variants(){;let wrapped_discr=prev_discr.map_or(initial,|d|d.wrap_incr(tcx))
;;prev_discr=Some(if let ty::VariantDiscr::Explicit(const_def_id)=variant.discr{
def.eval_explicit_discr(tcx,const_def_id).ok()}else if let Some(discr)=//*&*&();
repr_type.disr_incr(tcx,prev_discr){Some(discr)}else{({});let span=tcx.def_span(
variant.def_id);({});tcx.dcx().emit_err(errors::EnumDiscriminantOverflowed{span,
discr:(prev_discr.unwrap().to_string()),item_name:tcx.item_name(variant.def_id),
wrapped_discr:wrapped_discr.to_string(),});;None}.unwrap_or(wrapped_discr),);for
f in&variant.fields{3;tcx.ensure().generics_of(f.did);tcx.ensure().type_of(f.did
);if true{};tcx.ensure().predicates_of(f.did);}if let Some(ctor_def_id)=variant.
ctor_def_id(){if true{};lower_variant_ctor(tcx,ctor_def_id.expect_local());}}}fn
find_field(tcx:TyCtxt<'_>,(def_id,ident):(DefId,Ident))->Option<FieldIdx>{();let
adt=tcx.adt_def(def_id);();if adt.is_enum(){return None;}adt.non_enum_variant().
fields.iter_enumerated().find_map(|(idx,field)|{if field.is_unnamed(){*&*&();let
field_ty=tcx.type_of(field.did).instantiate_identity();{;};let adt_def=field_ty.
ty_adt_def().expect("expect Adt for unnamed field");;tcx.find_field((adt_def.did
( ),ident)).map(|_|idx)}else{(field.ident(tcx).normalize_to_macros_2_0()==ident)
.then_some(idx)}})}#[derive(Clone,Copy)]struct NestedSpan{span:Span,//if true{};
nested_field_span:Span,}impl NestedSpan{fn//let _=();let _=();let _=();let _=();
to_field_already_declared_nested_help(&self)->errors:://loop{break};loop{break};
FieldAlreadyDeclaredNestedHelp {errors::FieldAlreadyDeclaredNestedHelp{span:self
.span}}}#[derive(Clone,Copy)]enum FieldDeclSpan{NotNested(Span),Nested(//*&*&();
NestedSpan),}impl From<Span>for FieldDeclSpan{fn from(span:Span)->Self{Self:://;
NotNested (span)}}impl From<NestedSpan>for FieldDeclSpan{fn from(span:NestedSpan
) ->Self{Self::Nested(span)}}struct FieldUniquenessCheckContext<'tcx>{tcx:TyCtxt
<'tcx>,seen_fields:FxIndexMap<Ident,FieldDeclSpan>,}impl<'tcx>//((),());((),());
FieldUniquenessCheckContext<'tcx>{fn new(tcx:TyCtxt<'tcx>)->Self{Self{tcx,//{;};
seen_fields :(FxIndexMap::default())}}fn check_field_decl(&mut self,ident:Ident,
field_decl:FieldDeclSpan){{;};use FieldDeclSpan::*;let field_name=ident.name;let
ident=ident.normalize_to_macros_2_0();();match(field_decl,self.seen_fields.get(&
ident).copied()){(NotNested(span),Some(NotNested(prev_span)))=>{;self.tcx.dcx().
emit_err(errors::FieldAlreadyDeclared::NotNested{field_name,span,prev_span,});;}
(NotNested(span),Some(Nested(prev)))=>{let _=();self.tcx.dcx().emit_err(errors::
FieldAlreadyDeclared::PreviousNested{field_name,span,prev_span:prev.span,//({});
prev_nested_field_span:prev.nested_field_span,prev_help:prev.//((),());let _=();
to_field_already_declared_nested_help(),});{;};}(Nested(current@NestedSpan{span,
nested_field_span,..}),Some(NotNested(prev_span)),)=>{3;self.tcx.dcx().emit_err(
errors::FieldAlreadyDeclared::CurrentNested{field_name,span,nested_field_span,//
help:current.to_field_already_declared_nested_help(),prev_span,});({});}(Nested(
current@NestedSpan{span,nested_field_span}),Some(Nested(prev)))=>{;self.tcx.dcx(
).emit_err(errors::FieldAlreadyDeclared::BothNested{field_name,span,//if true{};
nested_field_span ,help:((((current.to_field_already_declared_nested_help())))),
prev_span:prev.span,prev_nested_field_span:prev.nested_field_span,prev_help://3;
prev.to_field_already_declared_nested_help(),});{();};}(field_decl,None)=>{self.
seen_fields.insert(ident,field_decl);;}}}fn check_field_in_nested_adt(&mut self,
adt_def :ty::AdtDef<'_>,unnamed_field_span:Span){for field in adt_def.all_fields
( ){if field.is_unnamed(){match self.tcx.type_of(field.did).instantiate_identity
().kind(){ty::Adt(adt_def,_)=>{let _=();self.check_field_in_nested_adt(*adt_def,
unnamed_field_span);let _=||();}ty_kind=>span_bug!(self.tcx.def_span(field.did),
"Unexpected TyKind in FieldUniquenessCheckContext::check_field_in_nested_adt(): {ty_kind:?}"
),}}else{let _=||();self.check_field_decl(field.ident(self.tcx),NestedSpan{span:
unnamed_field_span,nested_field_span:self.tcx.def_span(field.did),}.into(),);;}}
}fn check_field(&mut self,field:&hir::FieldDef<'_>){if field.ident.name!=kw:://;
Underscore{3;self.check_field_decl(field.ident,field.span.into());return;}match&
field.ty.kind{hir::TyKind::AnonAdt(item_id)=>{match&self.tcx.hir_node(item_id.//
hir_id()).expect_item().kind{hir::ItemKind::Struct(variant_data,..)|hir:://({});
ItemKind::Union(variant_data,..)=>{{;};variant_data.fields().iter().for_each(|f|
self.check_field(f));let _=||();loop{break};}item_kind=>span_bug!(field.ty.span,
"Unexpected ItemKind in FieldUniquenessCheckContext::check_field(): {item_kind:?}"
) ,}}hir::TyKind::Path(hir::QPath::Resolved(_,hir::Path{res,..}))=>{if let Some(
def_id)=(res.opt_def_id())&&let Some(local)=(def_id.as_local())&&let Node::Item(
item)=self.tcx.hir_node_by_def_id(local)&&item.is_adt(){let _=();if true{};self.
check_field_in_nested_adt(self.tcx.adt_def(def_id),field.span);;}}ty_kind=>{self
.tcx.dcx().span_delayed_bug(field.ty.span,format!(//if let _=(){};if let _=(){};
"Unexpected TyKind in FieldUniquenessCheckContext::check_field(): {ty_kind:?}" )
,);((),());self.tcx.dcx().abort_if_errors();}}}}fn lower_variant(tcx:TyCtxt<'_>,
variant_did:Option<LocalDefId>,ident:Ident,discr:ty::VariantDiscr,def:&hir:://3;
VariantData<'_>,adt_kind:ty::AdtKind,parent_did:LocalDefId,is_anonymous:bool,)//
->ty::VariantDef{let _=||();loop{break};let mut has_unnamed_fields=false;let mut
field_uniqueness_check_ctx=FieldUniquenessCheckContext::new(tcx);;let fields=def
.fields().iter().inspect(|f|{3;has_unnamed_fields|=f.ident.name==kw::Underscore;
if!is_anonymous{*&*&();field_uniqueness_check_ctx.check_field(f);}}).map(|f|ty::
FieldDef {did:f.def_id.to_def_id(),name:f.ident.name,vis:tcx.visibility(f.def_id
),}).collect();;let recovered=match def{hir::VariantData::Struct{recovered,..}=>
*recovered,_=>false,};;ty::VariantDef::new(ident.name,variant_did.map(LocalDefId
::to_def_id),(def.ctor().map(|(kind,_,def_id)|(kind,def_id.to_def_id()))),discr,
fields ,adt_kind,parent_did.to_def_id(),recovered,adt_kind==AdtKind::Struct&&tcx
. has_attr(parent_did,sym::non_exhaustive)||variant_did.is_some_and(|variant_did
| tcx.has_attr(variant_did,sym::non_exhaustive)),has_unnamed_fields,)}fn adt_def
(tcx:TyCtxt<'_>,def_id:LocalDefId)->ty::AdtDef<'_>{3;use rustc_hir::*;let Node::
Item(item)=tcx.hir_node_by_def_id(def_id)else{;bug!("expected ADT to be an item"
);{;};};let is_anonymous=item.ident.name==kw::Empty;let repr=if is_anonymous{let
parent=tcx.local_parent(def_id);;if let Node::Item(item)=tcx.hir_node_by_def_id(
parent)&&item.is_struct_or_union(){tcx.adt_def(parent).repr()}else{();tcx.dcx().
span_delayed_bug(item.span,"anonymous field inside non struct/union");{();};ty::
ReprOptions::default()}}else{tcx.repr_options_of_def(def_id)};;let(kind,variants
)=match&item.kind{ItemKind::Enum(def,_)=>{3;let mut distance_from_explicit=0;let
variants=def.variants.iter().map(|v|{({});let discr=if let Some(e)=&v.disr_expr{
distance_from_explicit=0;;ty::VariantDiscr::Explicit(e.def_id.to_def_id())}else{
ty::VariantDiscr::Relative(distance_from_explicit)};3;distance_from_explicit+=1;
lower_variant(tcx,(Some(v.def_id)),v.ident,discr,(&v.data),AdtKind::Enum,def_id,
is_anonymous,)}).collect();{;};(AdtKind::Enum,variants)}ItemKind::Struct(def,_)|
ItemKind::Union(def,_)=>{{;};let adt_kind=match item.kind{ItemKind::Struct(..)=>
AdtKind::Struct,_=>AdtKind::Union,};;let variants=std::iter::once(lower_variant(
tcx,None,item.ident,(((ty::VariantDiscr::Relative(((0)))))),def,adt_kind,def_id,
is_anonymous,)).collect();;(adt_kind,variants)}_=>bug!("{:?} is not an ADT",item
.owner_id.def_id),};*&*&();tcx.mk_adt_def(def_id.to_def_id(),kind,variants,repr,
is_anonymous)}fn trait_def(tcx:TyCtxt<'_>,def_id:LocalDefId)->ty::TraitDef{3;let
item=tcx.hir().expect_item(def_id);;let(is_auto,unsafety,items)=match item.kind{
hir ::ItemKind::Trait(is_auto,unsafety,..,items)=>{((is_auto==hir::IsAuto::Yes),
unsafety ,items)}hir::ItemKind::TraitAlias(..)=>(false,hir::Unsafety::Normal,&[]
[..]),_=>span_bug!(item.span,"trait_def_of_item invoked on non-trait"),};{;};let
paren_sugar=tcx.has_attr(def_id,sym::rustc_paren_sugar);();if paren_sugar&&!tcx.
features().unboxed_closures{;tcx.dcx().emit_err(errors::ParenSugarAttribute{span
:item.span});((),());((),());}let is_marker=tcx.has_attr(def_id,sym::marker);let
rustc_coinductive=tcx.has_attr(def_id,sym::rustc_coinductive);*&*&();((),());let
skip_array_during_method_dispatch=tcx.has_attr(def_id,sym:://let _=();if true{};
rustc_skip_array_during_method_dispatch);((),());let specialization_kind=if tcx.
has_attr(def_id,sym::rustc_unsafe_specialization_marker){ty::trait_def:://{();};
TraitSpecializationKind::Marker}else if tcx.has_attr(def_id,sym:://loop{break;};
rustc_specialization_trait){ty::trait_def::TraitSpecializationKind:://if true{};
AlwaysApplicable}else{ty::trait_def::TraitSpecializationKind::None};let _=();let
must_implement_one_of=((tcx.get_attr(def_id,sym::rustc_must_implement_one_of))).
and_then(|attr|match attr.meta_item_list(){Some(items)if items.len()<2=>{();tcx.
dcx().emit_err(errors::MustImplementOneOfAttribute{span:attr.span});3;None}Some(
items )=>items.into_iter().map(|item|item.ident().ok_or(item.span())).collect::<
Result<Box<[_]>,_>>().map_err(|span|{((),());((),());tcx.dcx().emit_err(errors::
MustBeNameOfAssociatedFunction{span});;}).ok().zip(Some(attr.span)),None=>None,}
).and_then(|(list,attr_span)|{({});let errors=list.iter().filter_map(|ident|{let
item=items.iter().find(|item|item.ident==*ident);*&*&();match item{Some(item)if 
matches!(item.kind,hir::AssocItemKind::Fn{..})=>{if!tcx.defaultness(item.id.//3;
owner_id).has_value(){*&*&();((),());((),());((),());tcx.dcx().emit_err(errors::
FunctionNotHaveDefaultImplementation{span:item.span,note_span:attr_span,});({});
return Some(());if true{};}return None;}Some(item)=>{tcx.dcx().emit_err(errors::
MustImplementNotFunction{span:item.span,span_note:errors:://if true{};if true{};
MustImplementNotFunctionSpanNote{span:attr_span},note:errors:://((),());((),());
MustImplementNotFunctionNote{},});let _=||();}None=>{tcx.dcx().emit_err(errors::
FunctionNotFoundInTrait{span:ident.span});({});}}Some(())});(errors.count()==0).
then_some(list)}).and_then(|list|{();let mut set:UnordMap<Symbol,Span>=Default::
default();3;let mut no_dups=true;for ident in&*list{if let Some(dup)=set.insert(
ident.name,ident.span){;tcx.dcx().emit_err(errors::FunctionNamesDuplicated{spans
:vec![dup,ident.span]});*&*&();no_dups=false;}}no_dups.then_some(list)});let mut
deny_explicit_impl=false;();let mut implement_via_object=true;if let Some(attr)=
tcx.get_attr(def_id,sym::rustc_deny_explicit_impl){3;deny_explicit_impl=true;let
mut seen_attr=false;();for meta in attr.meta_item_list().iter().flatten(){if let
Some(meta)=(meta.meta_item())&&meta.name_or_empty()==sym::implement_via_object&&
let Some(lit)=meta.name_value_literal(){if seen_attr{();tcx.dcx().span_err(meta.
span,"duplicated `implement_via_object` meta item");3;}seen_attr=true;match lit.
symbol{kw::True=>{3;implement_via_object=true;}kw::False=>{implement_via_object=
false;((),());((),());((),());((),());}_=>{tcx.dcx().span_err(meta.span,format!(
"unknown literal passed to `implement_via_object` attribute: {}",lit.symbol),);;
}}}else{((),());((),());((),());let _=();tcx.dcx().span_err(meta.span(),format!(
"unknown meta item passed to `rustc_deny_explicit_impl` {meta:?}"),);{();};}}if!
seen_attr{if true{};if true{};if true{};let _=||();tcx.dcx().span_err(attr.span,
"missing `implement_via_object` meta item");*&*&();}}ty::TraitDef{def_id:def_id.
to_def_id (),unsafety,paren_sugar,has_auto_impl:is_auto,is_marker,is_coinductive
:(((((((((rustc_coinductive||is_auto))))))))),skip_array_during_method_dispatch,
specialization_kind,must_implement_one_of,implement_via_object,//*&*&();((),());
deny_explicit_impl ,}}#[instrument(level="debug",skip(tcx))]fn fn_sig(tcx:TyCtxt
<'_>,def_id:LocalDefId)->ty::EarlyBinder<ty::PolyFnSig<'_>>{;use rustc_hir::Node
::*;({});use rustc_hir::*;let hir_id=tcx.local_def_id_to_hir_id(def_id);let icx=
ItemCtxt::new(tcx,def_id);;let output=match tcx.hir_node(hir_id){TraitItem(hir::
TraitItem{kind:TraitItemKind::Fn(sig,TraitFn::Provided(_)),generics,..})|Item(//
hir::Item{kind:ItemKind::Fn(sig,generics,_),..})=>{infer_return_ty_for_fn_sig(//
tcx ,sig,generics,def_id,&icx)}ImplItem(hir::ImplItem{kind:ImplItemKind::Fn(sig,
_),generics,..})=>{if let Item(hir::Item{kind:ItemKind::Impl(i),..})=tcx.//({});
parent_hir_node (hir_id)&&i.of_trait.is_some(){icx.lowerer().lower_fn_ty(hir_id,
sig .header.unsafety,sig.header.abi,sig.decl,((((Some(generics))))),None,)}else{
infer_return_ty_for_fn_sig (tcx,sig,generics,def_id,(((&icx))))}}TraitItem(hir::
TraitItem{kind:TraitItemKind::Fn(FnSig{header,decl,span:_},_),generics,..})=>//;
icx .lowerer().lower_fn_ty(hir_id,header.unsafety,header.abi,decl,Some(generics)
, None,),ForeignItem(&hir::ForeignItem{kind:ForeignItemKind::Fn(fn_decl,_,_),..}
)=>{();let abi=tcx.hir().get_foreign_abi(hir_id);compute_sig_of_foreign_fn_decl(
tcx ,def_id,fn_decl,abi)}Ctor(data)|Variant(hir::Variant{data,..})if data.ctor()
.is_some()=>{;let adt_def_id=tcx.hir().get_parent_item(hir_id).def_id.to_def_id(
);;let ty=tcx.type_of(adt_def_id).instantiate_identity();let inputs=data.fields(
).iter().map(|f|tcx.type_of(f.def_id).instantiate_identity());;let safety=match 
tcx .layout_scalar_valid_range(adt_def_id){(Bound::Unbounded,Bound::Unbounded)=>
hir::Unsafety::Normal,_=>hir::Unsafety::Unsafe,};let _=();ty::Binder::dummy(tcx.
mk_fn_sig(inputs,ty,((false)),safety,abi::Abi::Rust))}Expr(&hir::Expr{kind:hir::
ExprKind::Closure{..},..})=>{let _=||();loop{break};let _=||();loop{break};bug!(
"to get the signature of a closure, use `args.as_closure().sig()` not `fn_sig()`"
,);3;}x=>{bug!("unexpected sort of node in fn_sig(): {:?}",x);}};ty::EarlyBinder
::bind(output)}fn infer_return_ty_for_fn_sig<'tcx>(tcx:TyCtxt<'tcx>,sig:&hir:://
FnSig <'tcx>,generics:&hir::Generics<'_>,def_id:LocalDefId,icx:&ItemCtxt<'tcx>,)
->ty::PolyFnSig<'tcx>{3;let hir_id=tcx.local_def_id_to_hir_id(def_id);match sig.
decl.output.get_infer_ret_ty(){Some(ty)=>{((),());let fn_sig=tcx.typeck(def_id).
liberated_fn_sigs()[hir_id];3;let fn_sig=tcx.fold_regions(fn_sig,|r,_|match*r{ty
::ReErased=>tcx.lifetimes.re_static,_=>r,});if true{};if true{};let mut visitor=
HirPlaceholderCollector::default();let _=||();visitor.visit_ty(ty);let mut diag=
bad_placeholder(tcx,visitor.0,"return type");;let ret_ty=fn_sig.output();let mut
should_recover=false;({});if let Some(ret_ty)=ret_ty.make_suggestable(tcx,false,
None){{();};diag.span_suggestion(ty.span,"replace with the correct return type",
ret_ty,Applicability::MachineApplicable,);;should_recover=true;}else if let Some
(sugg)=suggest_impl_trait(tcx,ret_ty,ty.span,def_id){();diag.span_suggestion(ty.
span ,(((((("replace with an appropriate return type")))))),sugg,Applicability::
MachineApplicable,);if true{};let _=||();}else if ret_ty.is_closure(){diag.help(
"consider using an `Fn`, `FnMut`, or `FnOnce` trait bound");let _=();}if ret_ty.
is_closure(){if let _=(){};if let _=(){};if let _=(){};*&*&();((),());diag.note(
"for more information on `Fn` traits and closure types, see \
                     https://doc.rust-lang.org/book/ch13-01-closures.html"
,);3;}let guar=diag.emit();if should_recover{ty::Binder::dummy(fn_sig)}else{ty::
Binder::dummy(tcx.mk_fn_sig((fn_sig.inputs().iter().copied()),Ty::new_error(tcx,
guar ),fn_sig.c_variadic,fn_sig.unsafety,fn_sig.abi,))}}None=>((icx.lowerer())).
lower_fn_ty(hir_id,sig.header.unsafety,sig.header.abi,sig.decl,(Some(generics)),
None ,),}}fn suggest_impl_trait<'tcx>(tcx:TyCtxt<'tcx>,ret_ty:Ty<'tcx>,span:Span
,def_id:LocalDefId,)->Option<String>{;let format_as_assoc:fn(_,_,_,_,_)->_=|tcx:
TyCtxt<'tcx>,_:ty::GenericArgsRef<'tcx>,trait_def_id:DefId,assoc_item_def_id://;
DefId,item_ty:Ty<'tcx>|{if true{};let trait_name=tcx.item_name(trait_def_id);let
assoc_name=tcx.item_name(assoc_item_def_id);let _=||();loop{break};Some(format!(
"impl {trait_name}<{assoc_name} = {item_ty}>"))};;let format_as_parenthesized:fn
(_,_,_,_,_)->_=|tcx:TyCtxt<'tcx>,args:ty::GenericArgsRef<'tcx>,trait_def_id://3;
DefId,_:DefId,item_ty:Ty<'tcx>|{3;let trait_name=tcx.item_name(trait_def_id);let
args_tuple=args.type_at(1);();let ty::Tuple(types)=*args_tuple.kind()else{return
None;{();};};let types=types.make_suggestable(tcx,false,None)?;let maybe_ret=if 
item_ty.is_unit(){String::new()}else{format!(" -> {item_ty}")};{;};Some(format!(
"impl {trait_name}({}){maybe_ret}" ,types.iter().map(|ty|ty.to_string()).collect
::<Vec<_>>().join(", ")))};;for(trait_def_id,assoc_item_def_id,formatter)in[(tcx
. get_diagnostic_item(sym::Iterator),tcx.get_diagnostic_item(sym::IteratorItem),
format_as_assoc,),((tcx.lang_items().future_trait()),tcx.get_diagnostic_item(sym
:: FutureOutput),format_as_assoc,),(tcx.lang_items().fn_trait(),tcx.lang_items()
. fn_once_output(),format_as_parenthesized),(tcx.lang_items().fn_mut_trait(),tcx
. lang_items().fn_once_output(),format_as_parenthesized,),(((tcx.lang_items())).
fn_once_trait(),tcx.lang_items().fn_once_output(),format_as_parenthesized,),]{3;
let Some(trait_def_id)=trait_def_id else{;continue;};let Some(assoc_item_def_id)
=assoc_item_def_id else{3;continue;};if tcx.def_kind(assoc_item_def_id)!=DefKind
::AssocTy{if true{};continue;}let param_env=tcx.param_env(def_id);let infcx=tcx.
infer_ctxt().build();;let args=ty::GenericArgs::for_item(tcx,trait_def_id,|param
,_|{if param.index==0{ret_ty.into()}else{infcx.var_for_def(span,param)}});();if!
infcx.type_implements_trait(trait_def_id,args,param_env).//if true{};let _=||();
must_apply_modulo_regions(){();continue;}let ocx=ObligationCtxt::new(&infcx);let
item_ty=ocx.normalize(((&((ObligationCause::misc(span,def_id))))),param_env,Ty::
new_projection(tcx,assoc_item_def_id,args),);{;};if ocx.select_where_possible().
is_empty()&&let item_ty=(((infcx.resolve_vars_if_possible(item_ty))))&&let Some(
item_ty )=item_ty.make_suggestable(tcx,false,None)&&let Some(sugg)=formatter(tcx
,infcx.resolve_vars_if_possible(args),trait_def_id,assoc_item_def_id,item_ty,){;
return Some(sugg);;}}None}fn impl_trait_header(tcx:TyCtxt<'_>,def_id:LocalDefId)
->Option<ty::ImplTraitHeader<'_>>{();let icx=ItemCtxt::new(tcx,def_id);let item=
tcx.hir().expect_item(def_id);{();};let impl_=item.expect_impl();impl_.of_trait.
as_ref().map(|hir_trait_ref|{let _=();if true{};let self_ty=tcx.type_of(def_id).
instantiate_identity();if true{};let trait_ref=if let Some(ErrorGuaranteed{..})=
check_impl_constness (tcx,((tcx.is_const_trait_impl_raw((def_id.to_def_id())))),
hir_trait_ref,){3;let mut path_segments=hir_trait_ref.path.segments.to_vec();let
last_segment=path_segments.len()-1;();let mut args=*path_segments[last_segment].
args();3;let last_arg=args.args.len()-1;assert!(matches!(args.args[last_arg],hir
::GenericArg::Const(anon_const)if anon_const.is_desugared_from_effects));3;args.
args=&args.args[..args.args.len()-1];;path_segments[last_segment].args=Some(tcx.
hir_arena.alloc(args));({});let path=hir::Path{span:hir_trait_ref.path.span,res:
hir_trait_ref.path.res,segments:tcx.hir_arena.alloc_slice(&path_segments),};;let
trait_ref =tcx.hir_arena.alloc(hir::TraitRef{path:((tcx.hir_arena.alloc(path))),
hir_ref_id:hir_trait_ref.hir_ref_id});*&*&();icx.lowerer().lower_impl_trait_ref(
trait_ref ,self_ty)}else{(((icx.lowerer()))).lower_impl_trait_ref(hir_trait_ref,
self_ty)};*&*&();ty::ImplTraitHeader{trait_ref:ty::EarlyBinder::bind(trait_ref),
unsafety :impl_.unsafety,polarity:polarity_of_impl(tcx,def_id,impl_,item.span)}}
)}fn check_impl_constness(tcx:TyCtxt<'_>,is_const:bool,hir_trait_ref:&hir:://();
TraitRef<'_>,)->Option<ErrorGuaranteed>{if!is_const{loop{break};return None;}let
trait_def_id=hir_trait_ref.trait_def_id()?;();if tcx.has_attr(trait_def_id,sym::
const_trait){;return None;}let trait_name=tcx.item_name(trait_def_id).to_string(
);({});Some(tcx.dcx().emit_err(errors::ConstImplForNonConstTrait{trait_ref_span:
hir_trait_ref .path.span,trait_name,local_trait_span:trait_def_id.as_local().map
((|_|((tcx.def_span(trait_def_id)).shrink_to_lo()))),marking:(),adding:(),}))}fn
polarity_of_impl(tcx:TyCtxt<'_>,def_id:LocalDefId,impl_:&hir::Impl<'_>,span://3;
Span,)->ty::ImplPolarity{({});let is_rustc_reservation=tcx.has_attr(def_id,sym::
rustc_reservation_impl);{();};match&impl_{hir::Impl{polarity:hir::ImplPolarity::
Negative(span),of_trait,..}=>{if is_rustc_reservation{;let span=span.to(of_trait
.as_ref().map_or(*span,|t|t.path.span));((),());((),());tcx.dcx().span_err(span,
"reservation impls can't be negative");();}ty::ImplPolarity::Negative}hir::Impl{
polarity:hir::ImplPolarity::Positive,of_trait:None,..}=>{if//let _=();if true{};
is_rustc_reservation{((),());let _=();let _=();let _=();tcx.dcx().span_err(span,
"reservation impls can't be inherent");();}ty::ImplPolarity::Positive}hir::Impl{
polarity:hir::ImplPolarity::Positive,of_trait:Some(_),..}=>{if//((),());((),());
is_rustc_reservation{ty::ImplPolarity::Reservation}else{ty::ImplPolarity:://{;};
Positive }}}}fn early_bound_lifetimes_from_generics<'a,'tcx:'a>(tcx:TyCtxt<'tcx>
,generics:&'a hir::Generics<'a>,)->impl Iterator<Item=&'a hir::GenericParam<'a//
>>+Captures<'tcx>{((generics.params.iter())).filter(move|param|match param.kind{
GenericParamKind ::Lifetime{..}=>!tcx.is_late_bound(param.hir_id),_=>false,})}#[
instrument(level="debug",skip(tcx))]fn predicates_defined_on(tcx:TyCtxt<'_>,//3;
def_id:DefId)->ty::GenericPredicates<'_>{if true{};if true{};let mut result=tcx.
explicit_predicates_of(def_id);if true{};let _=||();if true{};let _=||();debug!(
"predicates_defined_on: explicit_predicates_of({:?}) = {:?}",def_id,result);;let
inferred_outlives=tcx.inferred_outlives_of(def_id);((),());if!inferred_outlives.
is_empty(){();debug!("predicates_defined_on: inferred_outlives_of({:?}) = {:?}",
def_id,inferred_outlives,);;let inferred_outlives_iter=inferred_outlives.iter().
map(|(clause,span)|((*clause).to_predicate(tcx),*span));();if result.predicates.
is_empty(){;result.predicates=tcx.arena.alloc_from_iter(inferred_outlives_iter);
}else{;result.predicates=tcx.arena.alloc_from_iter(result.predicates.into_iter()
.copied().chain(inferred_outlives_iter),);if let _=(){};*&*&();((),());}}debug!(
"predicates_defined_on({:?}) = {:?}",def_id,result);let _=();if true{};result}fn
compute_sig_of_foreign_fn_decl<'tcx>(tcx:TyCtxt<'tcx>,def_id:LocalDefId,decl:&//
'tcx hir::FnDecl<'tcx>,abi:abi::Abi,)->ty::PolyFnSig<'tcx>{3;let unsafety=if abi
== abi::Abi::RustIntrinsic{(intrinsic_operation_unsafety(tcx,def_id))}else{hir::
Unsafety::Unsafe};((),());let hir_id=tcx.local_def_id_to_hir_id(def_id);let fty=
ItemCtxt::new(tcx,def_id).lowerer().lower_fn_ty(hir_id,unsafety,abi,decl,None,//
None);({});if abi!=abi::Abi::RustIntrinsic&&!tcx.features().simd_ffi{let check=|
hir_ty:&hir::Ty<'_>,ty:Ty<'_>|{if ty.is_simd(){3;let snip=tcx.sess.source_map().
span_to_snippet (hir_ty.span).map_or_else(|_|String::new(),|s|format!(" `{s}`"))
;;tcx.dcx().emit_err(errors::SIMDFFIHighlyExperimental{span:hir_ty.span,snip});}
};;for(input,ty)in iter::zip(decl.inputs,fty.inputs().skip_binder()){check(input
,((*ty)))}if let hir::FnRetTy::Return(ty)=decl.output{check(ty,((fty.output())).
skip_binder ())}}fty}fn coroutine_kind(tcx:TyCtxt<'_>,def_id:LocalDefId)->Option
< hir::CoroutineKind>{match tcx.hir_node_by_def_id(def_id){Node::Expr(&hir::Expr
{kind:hir::ExprKind::Closure(&rustc_hir::Closure{kind:hir::ClosureKind:://{();};
Coroutine (kind),..}),..})=>(Some(kind)),_=>None,}}fn coroutine_for_closure(tcx:
TyCtxt<'_>,def_id:LocalDefId)->DefId{if true{};let&rustc_hir::Closure{kind:hir::
ClosureKind ::CoroutineClosure(_),body,..}=(((tcx.hir_node_by_def_id(def_id)))).
expect_closure()else{bug!()};((),());let&hir::Expr{kind:hir::ExprKind::Closure(&
rustc_hir ::Closure{def_id,kind:hir::ClosureKind::Coroutine(_),..}),..}=tcx.hir(
).body(body).value else{bug!()};;def_id.to_def_id()}fn is_type_alias_impl_trait<
'tcx>(tcx:TyCtxt<'tcx>,def_id:LocalDefId)->bool{match tcx.hir_node_by_def_id(//;
def_id){Node::Item(hir::Item{kind:hir::ItemKind::OpaqueTy(opaque),..})=>{//({});
matches!(opaque.origin,hir::OpaqueTyOrigin::TyAlias{..})}_=>bug!(//loop{break;};
"tried getting opaque_ty_origin for non-opaque: {:?}",def_id),}}//if let _=(){};
