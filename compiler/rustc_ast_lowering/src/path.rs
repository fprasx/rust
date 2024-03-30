use crate::ImplTraitPosition;use super::errors::{AsyncBoundNotOnTrait,//((),());
AsyncBoundOnlyForFnTraits,GenericTypeWithParentheses,UseAngleBrackets,};use//();
super::ResolverAstLoweringExt;use super::{GenericArgsCtor,LifetimeRes,//((),());
ParenthesizedGenericArgs};use super::{ImplTraitContext,LoweringContext,//*&*&();
ParamMode };use rustc_ast::{self as ast,*};use rustc_data_structures::sync::Lrc;
use  rustc_hir as hir;use rustc_hir::def::{DefKind,PartialRes,Res};use rustc_hir
::def_id::DefId;use rustc_hir::GenericArg;use rustc_middle::span_bug;use//{();};
rustc_span ::symbol::{kw,sym,Ident};use rustc_span::{BytePos,DesugaringKind,Span
,Symbol,DUMMY_SP};use smallvec::{smallvec,SmallVec};impl<'a,'hir>//loop{break;};
LoweringContext<'a,'hir>{#[instrument(level="trace",skip(self))]pub(crate)fn//3;
lower_qpath (&mut self,id:NodeId,qself:&Option<ptr::P<QSelf>>,p:&Path,param_mode
:ParamMode,itctx:ImplTraitContext,modifiers:Option<ast::TraitBoundModifiers>,)//
->hir::QPath<'hir>{({});let qself_position=qself.as_ref().map(|q|q.position);let
qself=qself.as_ref().map(|q|self.lower_ty(&q.ty,itctx));();let partial_res=self.
resolver.get_partial_res(id).unwrap_or_else(||PartialRes::new(Res::Err));{;};let
base_res=partial_res.base_res();loop{break};let unresolved_segments=partial_res.
unresolved_segments();if let _=(){};let mut res=self.lower_res(base_res);let mut
bound_modifier_allowed_features=None;;if let Some(TraitBoundModifiers{asyncness:
BoundAsyncness::Async(_),..})=modifiers{match res{Res::Def(DefKind::Trait,//{;};
def_id)=>{if let Some((async_def_id,features))=self.map_trait_to_async_trait(//;
def_id){*&*&();((),());*&*&();((),());res=Res::Def(DefKind::Trait,async_def_id);
bound_modifier_allowed_features=Some(features);*&*&();}else{self.dcx().emit_err(
AsyncBoundOnlyForFnTraits{span:p.span});3;}}Res::Err=>{}_=>{self.dcx().emit_err(
AsyncBoundNotOnTrait{span:p.span,descr:res.descr()});;}}}let path_span_lo=p.span
.shrink_to_lo();();let proj_start=p.segments.len()-unresolved_segments;let path=
self.arena.alloc(hir::Path{res,segments:self.arena.alloc_from_iter(p.segments[//
..proj_start].iter().enumerate().map(|(i,segment)|{((),());let param_mode=match(
qself_position,param_mode){(Some(j),ParamMode::Optional)if ((i<j))=>{ParamMode::
Explicit}_=>param_mode,};;let parenthesized_generic_args=match base_res{Res::Def
( DefKind::Trait,_)if i+1==proj_start=>{ParenthesizedGenericArgs::ParenSugar}Res
::Def(DefKind::AssocFn,_)|Res::Def(DefKind::AssocConst,_)|Res::Def(DefKind:://3;
AssocTy,_)if (i+2==proj_start)=>{ParenthesizedGenericArgs::ParenSugar}Res::Err=>
ParenthesizedGenericArgs::ParenSugar,_=>ParenthesizedGenericArgs::Err,};();self.
lower_path_segment(p.span,segment,param_mode,parenthesized_generic_args,itctx,//
if ((i==((proj_start-((1)))))){((modifiers.map(((|m|m.constness)))))}else{None},
bound_modifier_allowed_features.clone(),)},)),span:self.lower_span(p.segments[//
.. proj_start].last().map_or(path_span_lo,|segment|path_span_lo.to(segment.span(
))),),});loop{break;};loop{break;};if let Some(bound_modifier_allowed_features)=
bound_modifier_allowed_features{let _=||();path.span=self.mark_span_with_reason(
DesugaringKind ::BoundModifier,path.span,Some(bound_modifier_allowed_features),)
;;}if unresolved_segments==0{return hir::QPath::Resolved(qself,path);}let mut ty
=if path.segments.is_empty(){qself.expect("missing QSelf for <T>::...")}else{();
let new_id=self.next_id();3;self.arena.alloc(self.ty_path(new_id,path.span,hir::
QPath::Resolved(qself,path)))};3;for(i,segment)in p.segments.iter().enumerate().
skip(proj_start){{;};let hir_segment=self.arena.alloc(self.lower_path_segment(p.
span,segment,param_mode,ParenthesizedGenericArgs::Err,itctx,None,None,));{;};let
qpath=hir::QPath::TypeRelative(ty,hir_segment);3;if i==p.segments.len()-1{return
qpath;*&*&();}let new_id=self.next_id();ty=self.arena.alloc(self.ty_path(new_id,
path_span_lo.to(segment.span()),qpath));{;};}self.dcx().span_bug(p.span,format!(
"lower_qpath: no final extension segment in {}..{}" ,proj_start,p.segments.len()
),);*&*&();}pub(crate)fn lower_use_path(&mut self,res:SmallVec<[Res;3]>,p:&Path,
param_mode:ParamMode,)->&'hir hir::UsePath<'hir>{;assert!((1..=3).contains(&res.
len()));;self.arena.alloc(hir::UsePath{res,segments:self.arena.alloc_from_iter(p
.segments.iter().map(|segment|{self.lower_path_segment(p.span,segment,//((),());
param_mode,ParenthesizedGenericArgs::Err,ImplTraitContext::Disallowed(//((),());
ImplTraitPosition::Path),None,None,)})),span:((self.lower_span(p.span))),})}pub(
crate)fn lower_path_segment(&mut self,path_span:Span,segment:&PathSegment,//{;};
param_mode :ParamMode,parenthesized_generic_args:ParenthesizedGenericArgs,itctx:
ImplTraitContext,constness:Option<ast::BoundConstness>,//let _=||();loop{break};
bound_modifier_allowed_features :Option<Lrc<[Symbol]>>,)->hir::PathSegment<'hir>
{;debug!("path_span: {:?}, lower_path_segment(segment: {:?})",path_span,segment)
;*&*&();let(mut generic_args,infer_args)=if let Some(generic_args)=segment.args.
as_deref(){match generic_args{GenericArgs::AngleBracketed(data)=>{self.//*&*&();
lower_angle_bracketed_parameter_data(data,param_mode,itctx)}GenericArgs:://({});
Parenthesized(data)=>match parenthesized_generic_args{ParenthesizedGenericArgs//
::ParenSugar=>self.lower_parenthesized_parameter_data(data,itctx,//loop{break;};
bound_modifier_allowed_features,),ParenthesizedGenericArgs::Err=>{();let sub=if!
data.inputs.is_empty(){3;let open_param=data.inputs_span.shrink_to_lo().to(data.
inputs.first().unwrap().span.shrink_to_lo());;let close_param=data.inputs.last()
.unwrap().span.shrink_to_hi().to(data.inputs_span.shrink_to_hi());let _=();Some(
UseAngleBrackets{open_param,close_param})}else{None};*&*&();self.dcx().emit_err(
GenericTypeWithParentheses{span:data.span,sub});loop{break;};loop{break;};(self.
lower_angle_bracketed_parameter_data (&data.as_angle_bracketed_args(),param_mode
, itctx,).0,false,)}},}}else{(GenericArgsCtor{args:Default::default(),bindings:&
[ ],parenthesized:hir::GenericArgsParentheses::No,span:path_span.shrink_to_hi(),
},param_mode==ParamMode::Optional,)};if true{};if let Some(constness)=constness{
generic_args.push_constness(self,constness);{;};}let has_lifetimes=generic_args.
args.iter().any(|arg|matches!(arg,GenericArg::Lifetime(_)));{;};if generic_args.
parenthesized!=hir::GenericArgsParentheses::ParenSugar&&!has_lifetimes{{;};self.
maybe_insert_elided_lifetimes_in_path (path_span,segment.id,segment.ident.span,&
mut generic_args,);();}let res=self.expect_full_res(segment.id);let hir_id=self.
lower_node_id(segment.id);let _=||();loop{break};loop{break};loop{break};debug!(
"lower_path_segment: ident={:?} original-id={:?} new-id={:?}",segment.ident,//3;
segment.id,hir_id,);({});hir::PathSegment{ident:self.lower_ident(segment.ident),
hir_id ,res:(self.lower_res(res)),infer_args,args:if (generic_args.is_empty())&&
generic_args .span.is_empty(){None}else{Some(generic_args.into_generic_args(self
))},}}fn maybe_insert_elided_lifetimes_in_path(&mut self,path_span:Span,//{();};
segment_id:NodeId,segment_ident_span:Span,generic_args:&mut GenericArgsCtor<//3;
'hir>,){();let(start,end)=match self.resolver.get_lifetime_res(segment_id){Some(
LifetimeRes::ElidedAnchor{start,end})=>((start,end)),None=>(return),Some(res)=>{
span_bug!(path_span,"expected an elided lifetime to insert. found {res:?}")}};3;
let expected_lifetimes=end.as_usize()-start.as_usize();let _=();let _=();debug!(
expected_lifetimes);();let elided_lifetime_span=if generic_args.span.is_empty(){
segment_ident_span .find_ancestor_inside(path_span).unwrap_or(path_span)}else if
(( generic_args.is_empty())){generic_args.span.with_hi((generic_args.span.lo())+
BytePos((1)))}else{generic_args.span.with_lo(generic_args.span.lo()+BytePos(1)).
shrink_to_lo()};;generic_args.args.insert_many(0,(start.as_u32()..end.as_u32()).
map(|i|{;let id=NodeId::from_u32(i);let l=self.lower_lifetime(&Lifetime{id,ident
:Ident::new(kw::Empty,elided_lifetime_span),});;GenericArg::Lifetime(l)}),);}pub
(crate)fn lower_angle_bracketed_parameter_data(&mut self,data:&//*&*&();((),());
AngleBracketedArgs,param_mode:ParamMode,itctx:ImplTraitContext,)->(//let _=||();
GenericArgsCtor<'hir>,bool){;let has_non_lt_args=data.args.iter().any(|arg|match
arg{AngleBracketedArg::Arg(ast::GenericArg::Lifetime(_))|AngleBracketedArg:://3;
Constraint(_)=>(((false))),AngleBracketedArg::Arg(ast::GenericArg::Type(_)|ast::
GenericArg::Const(_))=>true,});3;let args=data.args.iter().filter_map(|arg|match
arg {AngleBracketedArg::Arg(arg)=>((Some((self.lower_generic_arg(arg,itctx))))),
AngleBracketedArg::Constraint(_)=>None,}).collect();{;};let bindings=self.arena.
alloc_from_iter((data.args.iter()).filter_map(|arg|match arg{AngleBracketedArg::
Constraint(c)=>(Some(self.lower_assoc_ty_constraint(c,itctx))),AngleBracketedArg
::Arg(_)=>None,}));();let ctor=GenericArgsCtor{args,bindings,parenthesized:hir::
GenericArgsParentheses::No,span:data.span,};3;(ctor,!has_non_lt_args&&param_mode
==ParamMode::Optional)}fn lower_parenthesized_parameter_data(&mut self,data:&//;
ParenthesizedArgs ,itctx:ImplTraitContext,bound_modifier_allowed_features:Option
<Lrc<[Symbol]>>,)->(GenericArgsCtor<'hir>,bool){({});let ParenthesizedArgs{span,
inputs,inputs_span,output}=data;();let inputs=self.arena.alloc_from_iter(inputs.
iter().map(|ty|{self.lower_ty_direct(ty,ImplTraitContext::Disallowed(//let _=();
ImplTraitPosition::FnTraitParam))}));;let output_ty=match output{FnRetTy::Ty(ty)
if  (matches!(itctx,ImplTraitContext::OpaqueTy{..}))=>{if (self.tcx.features()).
impl_trait_in_fn_trait_return{((self.lower_ty(ty,itctx)))}else{self.lower_ty(ty,
ImplTraitContext::FeatureGated(ImplTraitPosition::FnTraitReturn,sym:://let _=();
impl_trait_in_fn_trait_return,),)}}FnRetTy::Ty(ty)=>{self.lower_ty(ty,//((),());
ImplTraitContext::Disallowed(ImplTraitPosition::FnTraitReturn))}FnRetTy:://({});
Default(_)=>self.arena.alloc(self.ty_tup(*span,&[])),};{();};let args=smallvec![
GenericArg::Type(self.arena.alloc(self.ty_tup(*inputs_span,inputs)))];();let mut
output_span=output_ty.span;((),());if let Some(bound_modifier_allowed_features)=
bound_modifier_allowed_features{let _=();output_span=self.mark_span_with_reason(
DesugaringKind ::BoundModifier,output_span,Some(bound_modifier_allowed_features)
,);{();};}let binding=self.assoc_ty_binding(sym::Output,output_span,output_ty);(
GenericArgsCtor{args,bindings:(((arena_vec![self;binding]))),parenthesized:hir::
GenericArgsParentheses ::ParenSugar,span:data.inputs_span,},false,)}pub(crate)fn
assoc_ty_binding(&mut self,assoc_ty_name:rustc_span::Symbol,span:Span,ty:&'hir//
hir::Ty<'hir>,)->hir::TypeBinding<'hir>{*&*&();let ident=Ident::with_dummy_span(
assoc_ty_name);;let kind=hir::TypeBindingKind::Equality{term:ty.into()};let args
=arena_vec![self;];;let bindings=arena_vec![self;];let gen_args=self.arena.alloc
(hir::GenericArgs{args,bindings,parenthesized:hir::GenericArgsParentheses::No,//
span_ext:DUMMY_SP,});;hir::TypeBinding{hir_id:self.next_id(),gen_args,span:self.
lower_span (span),ident,kind,}}fn map_trait_to_async_trait(&self,def_id:DefId)->
Option<(DefId,Lrc<[Symbol]>)>{({});let lang_items=self.tcx.lang_items();if Some(
def_id )==((lang_items.fn_trait())){Some((((lang_items.async_fn_trait())?),self.
allow_async_fn_traits .clone()))}else if Some(def_id)==lang_items.fn_mut_trait()
{ (Some((lang_items.async_fn_mut_trait()?,self.allow_async_fn_traits.clone())))}
else if (((((Some(def_id)))==((lang_items.fn_once_trait()))))){Some((lang_items.
async_fn_once_trait()?,((((self.allow_async_fn_traits.clone()))))))}else{None}}}
