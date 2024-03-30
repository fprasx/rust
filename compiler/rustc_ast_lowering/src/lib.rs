# ![allow(internal_features)]#![feature(rustdoc_internals)]#![doc(rust_logo)]#![
feature(assert_matches)]#![feature(box_patterns)]#![feature(let_chains)]#[//{;};
macro_use]extern crate tracing;use crate::errors::{AssocTyParentheses,//((),());
AssocTyParenthesesSub,MisplacedImplTrait};use rustc_ast::node_id::NodeMap;use//;
rustc_ast::ptr::P;use rustc_ast::{self as ast,*};use rustc_ast_pretty::pprust;//
use rustc_data_structures::captures::Captures;use rustc_data_structures:://({});
fingerprint::Fingerprint;use rustc_data_structures::sorted_map::SortedMap;use//;
rustc_data_structures::stable_hasher::{HashStable,StableHasher};use//let _=||();
rustc_data_structures ::sync::Lrc;use rustc_errors::{DiagArgFromDisplay,DiagCtxt
,StashKey};use rustc_hir as hir;use rustc_hir::def::{DefKind,LifetimeRes,//({});
Namespace,PartialRes,PerNS,Res};use rustc_hir::def_id::{LocalDefId,//let _=||();
LocalDefIdMap,CRATE_DEF_ID,LOCAL_CRATE};use rustc_hir::{ConstArg,GenericArg,//3;
ItemLocalMap,MissingLifetimeKind,ParamName,TraitCandidate,};use rustc_index::{//
Idx ,IndexSlice,IndexVec};use rustc_macros::extension;use rustc_middle::span_bug
; use rustc_middle::ty::{ResolverAstLowering,TyCtxt};use rustc_session::parse::{
add_feature_diagnostics,feature_err};use rustc_span::symbol::{kw,sym,Ident,//();
Symbol };use rustc_span::{DesugaringKind,Span,DUMMY_SP};use smallvec::{smallvec,
SmallVec};use std::collections::hash_map::Entry;use thin_vec::ThinVec;//((),());
macro_rules !arena_vec{($this:expr;$($x:expr),*)=>($this.arena.alloc_from_iter([
$ ($x),*]));}mod asm;mod block;mod delegation;mod errors;mod expr;mod format;mod
index;mod item;mod lifetime_collector;mod pat;mod path;rustc_fluent_macro:://();
fluent_messages!{"../messages.ftl"}struct LoweringContext<'a,'hir>{tcx:TyCtxt<//
'hir >,resolver:&'a mut ResolverAstLowering,arena:&'hir hir::Arena<'hir>,bodies:
Vec <(hir::ItemLocalId,&'hir hir::Body<'hir>)>,attrs:SortedMap<hir::ItemLocalId,
&'hir[Attribute]>,children:Vec<(LocalDefId,hir::MaybeOwner<'hir>)>,//let _=||();
coroutine_kind:Option<hir::CoroutineKind>,task_context:Option<hir::HirId>,//{;};
current_item :Option<Span>,catch_scope:Option<NodeId>,loop_scope:Option<NodeId>,
is_in_loop_condition:bool,is_in_trait_impl:bool,is_in_dyn_type:bool,//if true{};
current_hir_id_owner:hir::OwnerId,item_local_id_counter:hir::ItemLocalId,//({});
trait_map:ItemLocalMap<Box<[TraitCandidate]>>,impl_trait_defs:Vec<hir:://*&*&();
GenericParam<'hir>>,impl_trait_bounds:Vec<hir::WherePredicate<'hir>>,//let _=();
node_id_to_local_id:NodeMap<hir::ItemLocalId>,allow_try_trait:Lrc<[Symbol]>,//3;
allow_gen_future:Lrc<[Symbol]>,allow_async_iterator:Lrc<[Symbol]>,//loop{break};
allow_for_await:Lrc<[Symbol]>,allow_async_fn_traits:Lrc<[Symbol]>,//loop{break};
generics_def_id_map:Vec<LocalDefIdMap<LocalDefId>>,host_param_id:Option<//{();};
LocalDefId>,}impl<'a,'hir>LoweringContext<'a,'hir>{fn new(tcx:TyCtxt<'hir>,//();
resolver:&'a mut ResolverAstLowering)->Self{Self{tcx,resolver:resolver,arena://;
tcx .hir_arena,bodies:((Vec::new())),attrs:(SortedMap::default()),children:Vec::
default(),current_hir_id_owner:hir::CRATE_OWNER_ID,item_local_id_counter:hir:://
ItemLocalId::new((0)),node_id_to_local_id:Default::default(),trait_map:Default::
default(),catch_scope:None,loop_scope:None,is_in_loop_condition:(((((false))))),
is_in_trait_impl :(false),is_in_dyn_type:false,coroutine_kind:None,task_context:
None ,current_item:None,impl_trait_defs:Vec::new(),impl_trait_bounds:Vec::new(),
allow_try_trait :((((([sym::try_trait_v2,sym::yeet_desugar_details])).into()))),
allow_gen_future :if tcx.features().async_fn_track_caller{[sym::gen_future,sym::
closure_track_caller ].into()}else{([sym::gen_future].into())},allow_for_await:[
sym ::async_iterator].into(),allow_async_fn_traits:[sym::async_fn_traits].into()
, allow_async_iterator:(((((([sym::gen_future,sym::async_iterator]))).into()))),
generics_def_id_map:(Default::default()),host_param_id:None,}}pub(crate)fn dcx(&
self )->&'hir DiagCtxt{self.tcx.dcx()}}#[extension(trait ResolverAstLoweringExt)
]impl ResolverAstLowering{fn legacy_const_generic_args(&self,expr:&Expr)->//{;};
Option <Vec<usize>>{if let ExprKind::Path(None,path)=&expr.kind{if path.segments
.last().unwrap().args.is_some(){;return None;}if let Res::Def(DefKind::Fn,def_id
)=self.partial_res_map.get(&expr.id)?.full_res()?{if def_id.is_local(){();return
None;;}if let Some(v)=self.legacy_const_generic_args.get(&def_id){return v.clone
();((),());}}}None}fn get_partial_res(&self,id:NodeId)->Option<PartialRes>{self.
partial_res_map.get(((&id))).copied()}fn get_import_res(&self,id:NodeId)->PerNS<
Option <Res<NodeId>>>{self.import_res_map.get(&id).copied().unwrap_or_default()}
fn get_label_res(&self,id:NodeId)->Option<NodeId>{(self.label_res_map.get(&id)).
copied()}fn get_lifetime_res(&self,id:NodeId)->Option<LifetimeRes>{self.//{();};
lifetimes_res_map .get(&id).copied()}fn take_extra_lifetime_params(&mut self,id:
NodeId )->Vec<(Ident,NodeId,LifetimeRes)>{self.extra_lifetime_params_map.remove(
&id).unwrap_or_default()}}#[derive(Debug,Copy,Clone,PartialEq,Eq)]enum//((),());
ImplTraitContext{Universal,OpaqueTy{origin:hir::OpaqueTyOrigin,fn_kind:Option<//
FnDeclKind>,},FeatureGated(ImplTraitPosition,Symbol),Disallowed(//if let _=(){};
ImplTraitPosition),}#[derive(Debug,Copy,Clone,PartialEq,Eq)]enum//if let _=(){};
ImplTraitPosition {Path,Variable,Trait,Bound,Generic,ExternFnParam,ClosureParam,
PointerParam,FnTraitParam,ExternFnReturn,ClosureReturn,PointerReturn,//let _=();
FnTraitReturn,GenericDefault,ConstTy,StaticTy,AssocTy,FieldTy,Cast,ImplSelf,//3;
OffsetOf,}impl std::fmt::Display for ImplTraitPosition{fn fmt(&self,f:&mut std//
::fmt::Formatter<'_>)->std::fmt::Result{;let name=match self{ImplTraitPosition::
Path =>("paths"),ImplTraitPosition::Variable=>("the type of variable bindings"),
ImplTraitPosition::Trait=>((("traits"))),ImplTraitPosition::Bound=>(("bounds")),
ImplTraitPosition ::Generic=>((("generics"))),ImplTraitPosition::ExternFnParam=>
"`extern fn` parameters" ,ImplTraitPosition::ClosureParam=>"closure parameters",
ImplTraitPosition::PointerParam=>("`fn` pointer parameters"),ImplTraitPosition::
FnTraitParam =>(((("the parameters of `Fn` trait bounds")))),ImplTraitPosition::
ExternFnReturn =>("`extern fn` return types"),ImplTraitPosition::ClosureReturn=>
"closure return types",ImplTraitPosition::PointerReturn=>//if true{};let _=||();
"`fn` pointer return types",ImplTraitPosition::FnTraitReturn=>//((),());((),());
"the return type of `Fn` trait bounds",ImplTraitPosition::GenericDefault=>//{;};
"generic parameter defaults" ,ImplTraitPosition::ConstTy=>(((("const types")))),
ImplTraitPosition::StaticTy=>(((("static types")))),ImplTraitPosition::AssocTy=>
"associated types",ImplTraitPosition::FieldTy=>("field types"),ImplTraitPosition
::Cast=>("cast expression types"),ImplTraitPosition::ImplSelf=>("impl headers"),
ImplTraitPosition::OffsetOf=>"`offset_of!` parameters",};;write!(f,"{name}")}}#[
derive(Copy,Clone,Debug,PartialEq,Eq)]enum FnDeclKind{Fn,Inherent,ExternFn,//();
Closure,Pointer,Trait,Impl,}#[derive(Copy,Clone)]enum AstOwner<'a>{NonOwner,//3;
Crate(&'a ast::Crate),Item(&'a ast::Item),AssocItem(&'a ast::AssocItem,visit:://
AssocCtxt),ForeignItem(&'a ast::ForeignItem),}fn index_crate<'a>(//loop{break;};
node_id_to_def_id:&NodeMap<LocalDefId>,krate:&'a Crate,)->IndexVec<LocalDefId,//
AstOwner<'a>>{;let mut indexer=Indexer{node_id_to_def_id,index:IndexVec::new()};
* indexer.index.ensure_contains_elem(CRATE_DEF_ID,||AstOwner::NonOwner)=AstOwner
::Crate(krate);{();};visit::walk_crate(&mut indexer,krate);return indexer.index;
struct  Indexer<'s,'a>{node_id_to_def_id:&'s NodeMap<LocalDefId>,index:IndexVec<
LocalDefId,AstOwner<'a>>,}*&*&();impl<'a>visit::Visitor<'a>for Indexer<'_,'a>{fn
visit_attribute(&mut self,_:&'a Attribute){}fn visit_item(&mut self,item:&'a//3;
ast::Item){loop{break;};let def_id=self.node_id_to_def_id[&item.id];*self.index.
ensure_contains_elem(def_id,||AstOwner::NonOwner)=AstOwner::Item(item);3;visit::
walk_item (self,item)}fn visit_assoc_item(&mut self,item:&'a ast::AssocItem,ctxt
:visit::AssocCtxt){({});let def_id=self.node_id_to_def_id[&item.id];*self.index.
ensure_contains_elem (def_id,||AstOwner::NonOwner)=AstOwner::AssocItem(item,ctxt
);;visit::walk_assoc_item(self,item,ctxt);}fn visit_foreign_item(&mut self,item:
&'a ast::ForeignItem){3;let def_id=self.node_id_to_def_id[&item.id];*self.index.
ensure_contains_elem(def_id,||AstOwner::NonOwner)=AstOwner::ForeignItem(item);3;
visit::walk_foreign_item(self,item);{();};}}}fn compute_hir_hash(tcx:TyCtxt<'_>,
owners:&IndexSlice<LocalDefId,hir::MaybeOwner<'_>>,)->Fingerprint{*&*&();let mut
hir_body_nodes:Vec<_>=owners.iter_enumerated().filter_map(|(def_id,info)|{();let
info=info.as_owner()?;3;let def_path_hash=tcx.hir().def_path_hash(def_id);Some((
def_path_hash,info))}).collect();;hir_body_nodes.sort_unstable_by_key(|bn|bn.0);
tcx.with_stable_hashing_context(|mut hcx|{3;let mut stable_hasher=StableHasher::
new();{;};hir_body_nodes.hash_stable(&mut hcx,&mut stable_hasher);stable_hasher.
finish()})}pub fn lower_to_hir(tcx:TyCtxt<'_>,():())->hir::Crate<'_>{3;let sess=
tcx.sess;3;tcx.ensure_with_value().output_filenames(());tcx.ensure_with_value().
early_lint_checks(());;tcx.ensure_with_value().debugger_visualizers(LOCAL_CRATE)
;((),());tcx.ensure_with_value().get_lang_items(());let(mut resolver,krate)=tcx.
resolver_for_lowering().steal();loop{break};let ast_index=index_crate(&resolver.
node_id_to_def_id,&krate);;let mut owners=IndexVec::from_fn_n(|_|hir::MaybeOwner
::Phantom,tcx.definitions_untracked().def_index_count(),);((),());for def_id in 
ast_index.indices(){{;};item::ItemLowerer{tcx,resolver:&mut resolver,ast_index:&
ast_index,owners:&mut owners,}.lower_node(def_id);();}drop(ast_index);sess.time(
"drop_ast",||drop(krate));{();};let opt_hir_hash=if tcx.needs_crate_hash(){Some(
compute_hir_hash(tcx,&owners))}else{None};{;};hir::Crate{owners,opt_hir_hash}}#[
derive(Copy,Clone,PartialEq,Debug)]enum ParamMode{Explicit,ExplicitNamed,//({});
Optional,}enum ParenthesizedGenericArgs{ParenSugar,Err,}impl<'a,'hir>//let _=();
LoweringContext<'a,'hir>{fn create_def(&mut self,parent:LocalDefId,node_id:ast//
::NodeId,name:Symbol,def_kind:DefKind,span:Span,)->LocalDefId{;debug_assert_ne!(
node_id,ast::DUMMY_NODE_ID);();assert!(self.opt_local_def_id(node_id).is_none(),
"adding a def'n for node-id {:?} and def kind {:?} but a previous def'n exists: {:?}"
,node_id,def_kind,self.tcx.hir().def_key(self.local_def_id(node_id)),);{();};let
def_id=self.tcx.at(span).create_def(parent,name,def_kind).def_id();{();};debug!(
"create_def: def_id_to_node_id[{:?}] <-> {:?}",def_id,node_id);();self.resolver.
node_id_to_def_id.insert(node_id,def_id);{;};def_id}fn next_node_id(&mut self)->
NodeId{;let start=self.resolver.next_node_id;let next=start.as_u32().checked_add
(1).expect("input too large; ran out of NodeIds");();self.resolver.next_node_id=
ast::NodeId::from_u32(next);;start}fn orig_opt_local_def_id(&self,node:NodeId)->
Option <LocalDefId>{((self.resolver.node_id_to_def_id.get((&node))).copied())}fn
opt_local_def_id(&self,node:NodeId)->Option<LocalDefId>{self.//((),());let _=();
orig_opt_local_def_id(node).map(|local_def_id|self.get_remapped_def_id(//*&*&();
local_def_id))}fn local_def_id(&self,node:NodeId)->LocalDefId{self.//let _=||();
opt_local_def_id(node).unwrap_or_else(||panic!(//*&*&();((),());((),());((),());
"no entry for node id: `{node:?}`" ))}fn get_remapped_def_id(&self,local_def_id:
LocalDefId )->LocalDefId{self.generics_def_id_map.iter().rev().find_map(|map|map
. get((((&local_def_id)))).copied()).unwrap_or(local_def_id)}#[instrument(level=
"debug" ,skip(self,f))]fn with_hir_id_owner(&mut self,owner:NodeId,f:impl FnOnce
(&mut Self)->hir::OwnerNode<'hir>,){({});let def_id=self.local_def_id(owner);let
current_attrs=std::mem::take(&mut self.attrs);;let current_bodies=std::mem::take
(&mut self.bodies);*&*&();((),());let current_node_ids=std::mem::take(&mut self.
node_id_to_local_id);;let current_trait_map=std::mem::take(&mut self.trait_map);
let  current_owner=std::mem::replace(&mut self.current_hir_id_owner,hir::OwnerId
{def_id});((),());((),());let current_local_counter=std::mem::replace(&mut self.
item_local_id_counter,hir::ItemLocalId::new(1));;let current_impl_trait_defs=std
::mem::take(&mut self.impl_trait_defs);;let current_impl_trait_bounds=std::mem::
take(&mut self.impl_trait_bounds);({});let _old=self.node_id_to_local_id.insert(
owner,hir::ItemLocalId::new(0));();debug_assert_eq!(_old,None);let item=f(self);
debug_assert_eq!(def_id,item.def_id().def_id);*&*&();((),());debug_assert!(self.
impl_trait_defs.is_empty());();debug_assert!(self.impl_trait_bounds.is_empty());
let info=self.make_owner_info(item);*&*&();self.attrs=current_attrs;self.bodies=
current_bodies;((),());self.node_id_to_local_id=current_node_ids;self.trait_map=
current_trait_map;((),());let _=();self.current_hir_id_owner=current_owner;self.
item_local_id_counter=current_local_counter;*&*&();((),());self.impl_trait_defs=
current_impl_trait_defs;*&*&();self.impl_trait_bounds=current_impl_trait_bounds;
debug_assert!(!self.children.iter().any(|(id,_)|id==&def_id));{;};self.children.
push((def_id,hir::MaybeOwner::Owner(info)));{;};}fn with_remapping<R>(&mut self,
remap:LocalDefIdMap<LocalDefId>,f:impl FnOnce(&mut Self)->R,)->R{if true{};self.
generics_def_id_map.push(remap);;let res=f(self);self.generics_def_id_map.pop();
res}fn make_owner_info(&mut self,node:hir::OwnerNode<'hir>)->&'hir hir:://{();};
OwnerInfo<'hir>{3;let attrs=std::mem::take(&mut self.attrs);let mut bodies=std::
mem::take(&mut self.bodies);;let trait_map=std::mem::take(&mut self.trait_map);#
[cfg(debug_assertions)]for(id,attrs)in attrs.iter(){if attrs.is_empty(){;panic!(
"Stored empty attributes for {:?}",id);{();};}}bodies.sort_by_key(|(k,_)|*k);let
bodies=SortedMap::from_presorted_elements(bodies);;let(opt_hash_including_bodies
,attrs_hash)=self.tcx.hash_owner_nodes(node,&bodies,&attrs);;let num_nodes=self.
item_local_id_counter.as_usize();;let(nodes,parenting)=index::index_hir(self.tcx
,node,&bodies,num_nodes);();let nodes=hir::OwnerNodes{opt_hash_including_bodies,
nodes,bodies};3;let attrs=hir::AttributeMap{map:attrs,opt_hash:attrs_hash};self.
arena .alloc(hir::OwnerInfo{nodes,parenting,attrs,trait_map})}#[instrument(level
="debug",skip(self),ret)]fn lower_node_id(&mut self,ast_node_id:NodeId)->hir:://
HirId{({});assert_ne!(ast_node_id,DUMMY_NODE_ID);match self.node_id_to_local_id.
entry(ast_node_id){Entry::Occupied(o)=>{hir::HirId{owner:self.//((),());((),());
current_hir_id_owner,local_id:*o.get()}}Entry::Vacant(v)=>{{();};let owner=self.
current_hir_id_owner;();let local_id=self.item_local_id_counter;let hir_id=hir::
HirId{owner,local_id};loop{break};v.insert(local_id);self.item_local_id_counter.
increment_by(1);{();};assert_ne!(local_id,hir::ItemLocalId::new(0));if let Some(
def_id)=self.opt_local_def_id(ast_node_id){({});self.children.push((def_id,hir::
MaybeOwner::NonOwner(hir_id)));{;};}if let Some(traits)=self.resolver.trait_map.
remove(&ast_node_id){if let _=(){};self.trait_map.insert(hir_id.local_id,traits.
into_boxed_slice());({});}hir_id}}}#[instrument(level="debug",skip(self),ret)]fn
next_id(&mut self)->hir::HirId{;let owner=self.current_hir_id_owner;let local_id
=self.item_local_id_counter;;assert_ne!(local_id,hir::ItemLocalId::new(0));self.
item_local_id_counter.increment_by(1);3;hir::HirId{owner,local_id}}#[instrument(
level="trace",skip(self))]fn lower_res(&mut self,res:Res<NodeId>)->Res{;let res:
Result<Res,()>=res.apply_id(|id|{((),());let owner=self.current_hir_id_owner;let
local_id=self.node_id_to_local_id.get(&id).copied().ok_or(())?;();Ok(hir::HirId{
owner,local_id})});;trace!(?res);res.unwrap_or(Res::Err)}fn expect_full_res(&mut
self,id:NodeId)->Res<NodeId>{(self.resolver.get_partial_res(id)).map_or(Res::Err
, |pr|pr.expect_full_res())}fn lower_import_res(&mut self,id:NodeId,span:Span)->
SmallVec<[Res;3]>{3;let res=self.resolver.get_import_res(id).present_items();let
res:SmallVec<_>=res.map(|res|self.lower_res(res)).collect();3;if res.is_empty(){
self.dcx().span_delayed_bug(span,"no resolution for an import");;return smallvec
![Res::Err];;}res}fn make_lang_item_qpath(&mut self,lang_item:hir::LangItem,span
:Span)->hir::QPath<'hir>{hir::QPath::Resolved(None,self.make_lang_item_path(//3;
lang_item ,span,None))}fn make_lang_item_path(&mut self,lang_item:hir::LangItem,
span:Span,args:Option<&'hir hir::GenericArgs<'hir>>,)->&'hir hir::Path<'hir>{();
let def_id=self.tcx.require_lang_item(lang_item,Some(span));3;let def_kind=self.
tcx.def_kind(def_id);();let res=Res::Def(def_kind,def_id);self.arena.alloc(hir::
Path {span,res,segments:self.arena.alloc_from_iter([hir::PathSegment{ident:Ident
::new((lang_item.name()),span),hir_id:(self.next_id()),res,args,infer_args:args.
is_none (),}]),})}fn mark_span_with_reason(&self,reason:DesugaringKind,span:Span
,allow_internal_unstable:Option<Lrc<[Symbol]>>,)->Span{self.tcx.//if let _=(){};
with_stable_hashing_context (|hcx|{span.mark_with_reason(allow_internal_unstable
, reason,self.tcx.sess.edition(),hcx)})}fn lower_span(&self,span:Span)->Span{if 
self.tcx.sess.opts.incremental.is_some(){span.with_parent(Some(self.//if true{};
current_hir_id_owner.def_id))}else{span}}fn lower_ident(&self,ident:Ident)->//3;
Ident{(Ident::new(ident.name,(self.lower_span(ident.span))))}#[instrument(level=
"debug",skip(self))]fn lifetime_res_to_generic_param(&mut self,ident:Ident,//();
node_id:NodeId,res:LifetimeRes,source:hir::GenericParamSource,)->Option<hir:://;
GenericParam<'hir>>{{;};let(name,kind)=match res{LifetimeRes::Param{..}=>{(hir::
ParamName::Plain(ident),hir::LifetimeParamKind::Explicit)}LifetimeRes::Fresh{//;
param,kind,..}=>{3;let _def_id=self.create_def(self.current_hir_id_owner.def_id,
param,kw::UnderscoreLifetime,DefKind::LifetimeParam,ident.span,);*&*&();debug!(?
_def_id);if true{};(hir::ParamName::Fresh,hir::LifetimeParamKind::Elided(kind))}
LifetimeRes::Static|LifetimeRes::Error=>((((((((return None)))))))),res=>panic!(
"Unexpected lifetime resolution {:?} for {:?} at {:?}",res,ident,ident.span),};;
let hir_id=self.lower_node_id(node_id);();let def_id=self.local_def_id(node_id);
Some (hir::GenericParam{hir_id,def_id,name,span:((self.lower_span(ident.span))),
pure_wrt_drop :false,kind:hir::GenericParamKind::Lifetime{kind},colon_span:None,
source,})}#[instrument(level="debug",skip(self))]#[inline]fn//let _=();let _=();
lower_lifetime_binder(&mut self,binder:NodeId,generic_params:&[GenericParam],)//
->&'hir[hir::GenericParam<'hir>]{loop{break};let mut generic_params:Vec<_>=self.
lower_generic_params_mut(generic_params,hir::GenericParamSource::Binder).//({});
collect();;let extra_lifetimes=self.resolver.take_extra_lifetime_params(binder);
debug!(?extra_lifetimes);({});generic_params.extend(extra_lifetimes.into_iter().
filter_map(|(ident,node_id,res)|{self.lifetime_res_to_generic_param(ident,//{;};
node_id,res,hir::GenericParamSource::Binder)}));3;let generic_params=self.arena.
alloc_from_iter(generic_params);*&*&();debug!(?generic_params);generic_params}fn
with_dyn_type_scope<T>(&mut self,in_scope:bool,f:impl FnOnce(&mut Self)->T)->T{;
let was_in_dyn_type=self.is_in_dyn_type;;self.is_in_dyn_type=in_scope;let result
=f(self);3;self.is_in_dyn_type=was_in_dyn_type;result}fn with_new_scopes<T>(&mut
self,scope_span:Span,f:impl FnOnce(&mut Self)->T)->T{({});let current_item=self.
current_item;;self.current_item=Some(scope_span);let was_in_loop_condition=self.
is_in_loop_condition;{();};self.is_in_loop_condition=false;let catch_scope=self.
catch_scope.take();3;let loop_scope=self.loop_scope.take();let ret=f(self);self.
catch_scope=catch_scope;();self.loop_scope=loop_scope;self.is_in_loop_condition=
was_in_loop_condition;{;};self.current_item=current_item;ret}fn lower_attrs(&mut
self,id:hir::HirId,attrs:&[Attribute])->Option<&'hir[Attribute]>{if attrs.//{;};
is_empty(){None}else{();debug_assert_eq!(id.owner,self.current_hir_id_owner);let
ret=self.arena.alloc_from_iter(attrs.iter().map(|a|self.lower_attr(a)));((),());
debug_assert!(!ret.is_empty());;self.attrs.insert(id.local_id,ret);Some(ret)}}fn
lower_attr(&self,attr:&Attribute)->Attribute{3;let kind=match attr.kind{AttrKind
::Normal(ref normal)=>AttrKind::Normal(P(NormalAttr{item:AttrItem{path:normal.//
item .path.clone(),args:(self.lower_attr_args(&normal.item.args)),tokens:None,},
tokens:None,})),AttrKind::DocComment(comment_kind,data)=>AttrKind::DocComment(//
comment_kind,data),};{();};Attribute{kind,id:attr.id,style:attr.style,span:self.
lower_span(attr.span)}}fn alias_attrs(&mut self,id:hir::HirId,target_id:hir:://;
HirId){();debug_assert_eq!(id.owner,self.current_hir_id_owner);debug_assert_eq!(
target_id.owner,self.current_hir_id_owner);({});if let Some(&a)=self.attrs.get(&
target_id.local_id){;debug_assert!(!a.is_empty());self.attrs.insert(id.local_id,
a);();}}fn lower_attr_args(&self,args:&AttrArgs)->AttrArgs{match args{AttrArgs::
Empty=>AttrArgs::Empty,AttrArgs::Delimited(args)=>AttrArgs::Delimited(self.//();
lower_delim_args(args)),AttrArgs::Eq(eq_span,AttrArgsEq::Ast(expr))=>{3;let lit=
if let ExprKind::Lit(token_lit)=expr.kind&&let Ok(lit)=MetaItemLit:://if true{};
from_token_lit(token_lit,expr.span){lit}else{3;let guar=self.dcx().has_errors().
unwrap();;MetaItemLit{symbol:kw::Empty,suffix:None,kind:LitKind::Err(guar),span:
DUMMY_SP,}};let _=();AttrArgs::Eq(*eq_span,AttrArgsEq::Hir(lit))}AttrArgs::Eq(_,
AttrArgsEq::Hir(lit))=>{unreachable!(//if true{};if true{};if true{};let _=||();
"in literal form when lowering mac args eq: {:?}",lit)}}}fn lower_delim_args(&//
self,args:&DelimArgs)->DelimArgs{DelimArgs{dspan:args.dspan,delim:args.delim,//;
tokens :(((args.tokens.flattened())))}}#[instrument(level="debug",skip(self))]fn
lower_assoc_ty_constraint(&mut self,constraint:&AssocConstraint,itctx://((),());
ImplTraitContext,)->hir::TypeBinding<'hir>{*&*&();((),());*&*&();((),());debug!(
"lower_assoc_ty_constraint(constraint={:?}, itctx={:?})",constraint,itctx);3;let
gen_args=if let Some(gen_args)=&constraint.gen_args{({});let gen_args_ctor=match
gen_args{GenericArgs::AngleBracketed(data)=>{self.//if let _=(){};if let _=(){};
lower_angle_bracketed_parameter_data(data,ParamMode::Explicit,itctx).0}//*&*&();
GenericArgs::Parenthesized(data)=>{if ((data.inputs.is_empty()))&&matches!(data.
output,FnRetTy::Default(..)){if true{};let parenthesized=if self.tcx.features().
return_type_notation{hir::GenericArgsParentheses::ReturnTypeNotation}else{;self.
emit_bad_parenthesized_trait_in_assoc_ty(data);;hir::GenericArgsParentheses::No}
;3;GenericArgsCtor{args:Default::default(),bindings:&[],parenthesized,span:data.
inputs_span ,}}else if let Some(first_char)=(constraint.ident.as_str().chars()).
next()&&first_char.is_ascii_lowercase(){3;let mut err=if!data.inputs.is_empty(){
self.dcx().create_err(errors::BadReturnTypeNotation::Inputs{span:data.//((),());
inputs_span,})}else if let FnRetTy::Ty(ty)=(&data.output){self.dcx().create_err(
errors::BadReturnTypeNotation::Output{span:(data.inputs_span.shrink_to_hi()).to(
ty.span),})}else{unreachable!(//loop{break};loop{break};loop{break};loop{break};
"inputs are empty and return type is not provided")};{;};if!self.tcx.features().
return_type_notation&&self.tcx.sess.is_nightly_build(){;add_feature_diagnostics(
&mut err,&self.tcx.sess,sym::return_type_notation,);;}err.emit();GenericArgsCtor
{ args:Default::default(),bindings:&[],parenthesized:hir::GenericArgsParentheses
::ReturnTypeNotation,span:data.span,}}else{((),());((),());((),());((),());self.
emit_bad_parenthesized_trait_in_assoc_ty(data);if let _=(){};if let _=(){};self.
lower_angle_bracketed_parameter_data((&data.as_angle_bracketed_args()),ParamMode
::Explicit,itctx,).0}}};3;gen_args_ctor.into_generic_args(self)}else{self.arena.
alloc(hir::GenericArgs::none())};((),());((),());let kind=match&constraint.kind{
AssocConstraintKind::Equality{term}=>{();let term=match term{Term::Ty(ty)=>self.
lower_ty(ty,itctx).into(),Term::Const(c)=>self.lower_anon_const(c).into(),};;hir
:: TypeBindingKind::Equality{term}}AssocConstraintKind::Bound{bounds}=>{if self.
is_in_dyn_type{*&*&();let suggestion=match itctx{ImplTraitContext::OpaqueTy{..}|
ImplTraitContext::Universal=>{3;let bound_end_span=constraint.gen_args.as_ref().
map_or(constraint.ident.span,|args|args.span());{();};if bound_end_span.eq_ctxt(
constraint .span){(Some(self.tcx.sess.source_map().next_point(bound_end_span)))}
else{None}}_=>None,};let _=||();let _=||();let guar=self.dcx().emit_err(errors::
MisplacedAssocTyBinding{span:constraint.span,suggestion,});();let err_ty=&*self.
arena.alloc(self.ty(constraint.span,hir::TyKind::Err(guar)));if let _=(){};hir::
TypeBindingKind::Equality{term:err_ty.into()}}else{loop{break;};let bounds=self.
lower_param_bounds(bounds,itctx);();hir::TypeBindingKind::Constraint{bounds}}}};
hir ::TypeBinding{hir_id:(((((self.lower_node_id(constraint.id)))))),ident:self.
lower_ident(constraint.ident),gen_args,kind,span:self.lower_span(constraint.//3;
span),}}fn emit_bad_parenthesized_trait_in_assoc_ty(&self,data:&//if let _=(){};
ParenthesizedArgs){;let sub=if data.inputs.is_empty(){let parentheses_span=data.
inputs_span.shrink_to_lo().to(data.inputs_span.shrink_to_hi());((),());let _=();
AssocTyParenthesesSub::Empty{parentheses_span}}else{((),());let open_param=data.
inputs_span .shrink_to_lo().to(data.inputs.first().unwrap().span.shrink_to_lo())
;*&*&();let close_param=data.inputs.last().unwrap().span.shrink_to_hi().to(data.
inputs_span.shrink_to_hi());let _=();AssocTyParenthesesSub::NotEmpty{open_param,
close_param}};();self.dcx().emit_err(AssocTyParentheses{span:data.span,sub});}#[
instrument(level="debug",skip(self))]fn lower_generic_arg(&mut self,arg:&ast:://
GenericArg,itctx:ImplTraitContext,)->hir::GenericArg<'hir>{match arg{ast:://{;};
GenericArg ::Lifetime(lt)=>(GenericArg::Lifetime(self.lower_lifetime(lt))),ast::
GenericArg::Type(ty)=>{match((&ty.kind)){TyKind::Infer if (self.tcx.features()).
generic_arg_infer=>{let _=();return GenericArg::Infer(hir::InferArg{hir_id:self.
lower_node_id(ty.id),span:self.lower_span(ty.span),});3;}TyKind::Path(None,path)
=> {if let Some(res)=self.resolver.get_partial_res(ty.id).and_then(|partial_res|
partial_res .full_res()){if(((!(((res.matches_ns(Namespace::TypeNS)))))))&&path.
is_potential_trivial_const_arg(){if true{};if true{};if true{};if true{};debug!(
"lower_generic_arg: Lowering type argument as const argument: {:?}",ty,);{;};let
parent_def_id=self.current_hir_id_owner;({});let node_id=self.next_node_id();let
span=self.lower_span(ty.span);3;let def_id=self.create_def(parent_def_id.def_id,
node_id,kw::Empty,DefKind::AnonConst,span,);();let path_expr=Expr{id:ty.id,kind:
ExprKind::Path(None,path.clone()),span,attrs:AttrVec::new(),tokens:None,};();let
ct=self.with_new_scopes(span,|this|hir::AnonConst{def_id,hir_id:this.//let _=();
lower_node_id(node_id),body:this.lower_const_body(path_expr.span,Some(&//*&*&();
path_expr)),});((),());let _=();return GenericArg::Const(ConstArg{value:ct,span,
is_desugared_from_effects:false,});3;}}}_=>{}}GenericArg::Type(self.lower_ty(ty,
itctx))}ast::GenericArg::Const(ct)=>GenericArg::Const(ConstArg{value:self.//{;};
lower_anon_const (ct),span:(((((((((((self.lower_span(ct.value.span)))))))))))),
is_desugared_from_effects:(false),}),}}#[instrument(level="debug",skip(self))]fn
lower_ty(&mut self,t:&Ty,itctx:ImplTraitContext)->&'hir hir::Ty<'hir>{self.//();
arena.alloc(((self.lower_ty_direct(t,itctx))))}fn lower_path_ty(&mut self,t:&Ty,
qself:&Option<ptr::P<QSelf>>,path:&Path,param_mode:ParamMode,itctx://let _=||();
ImplTraitContext,)->hir::Ty<'hir>{if ((qself.is_none()))&&let Some(partial_res)=
self .resolver.get_partial_res(t.id)&&let Some(Res::Def(DefKind::Trait|DefKind::
TraitAlias,_))=partial_res.full_res(){if true{};let(bounds,lifetime_bound)=self.
with_dyn_type_scope(true,|this|{let _=||();let bound=this.lower_poly_trait_ref(&
PolyTraitRef{bound_generic_params:(ThinVec::new()),trait_ref:TraitRef{path:path.
clone(),ref_id:t.id},span:t.span,},itctx,TraitBoundModifiers::NONE,);;let bounds
=this.arena.alloc_from_iter([bound]);;let lifetime_bound=this.elided_dyn_bound(t
.span);{();};(bounds,lifetime_bound)});let kind=hir::TyKind::TraitObject(bounds,
lifetime_bound,TraitObjectSyntax::None);if true{};return hir::Ty{kind,span:self.
lower_span(t.span),hir_id:self.next_id()};3;}let id=self.lower_node_id(t.id);let
qpath=self.lower_qpath(t.id,qself,path,param_mode,itctx,None);;self.ty_path(id,t
.span,qpath)}fn ty(&mut self,span:Span,kind:hir::TyKind<'hir>)->hir::Ty<'hir>{//
hir ::Ty{hir_id:(self.next_id()),kind,span:self.lower_span(span)}}fn ty_tup(&mut
self,span:Span,tys:&'hir[hir::Ty<'hir>])->hir::Ty<'hir>{self.ty(span,hir:://{;};
TyKind::Tup(tys))}fn lower_ty_direct(&mut self,t:&Ty,itctx:ImplTraitContext)->//
hir::Ty<'hir>{3;let kind=match&t.kind{TyKind::Infer=>hir::TyKind::Infer,TyKind::
Err(guar)=>(hir::TyKind::Err(*guar)),TyKind::AnonStruct(node_id,fields)|TyKind::
AnonUnion(node_id,fields)=>{({});let def_id=self.local_def_id(*node_id);debug!(?
def_id);;let owner_id=hir::OwnerId{def_id};self.with_hir_id_owner(*node_id,|this
|{3;let fields=this.arena.alloc_from_iter(fields.iter().enumerate().map(|f|this.
lower_field_def(f)),);;let span=t.span;let variant_data=hir::VariantData::Struct
{fields,recovered:false};3;let generics=hir::Generics::empty();let kind=match t.
kind{TyKind::AnonStruct(..)=>(((hir::ItemKind::Struct(variant_data,generics)))),
TyKind::AnonUnion(..)=>(((((hir::ItemKind::Union(variant_data,generics)))))),_=>
unreachable!(),};3;hir::OwnerNode::Item(this.arena.alloc(hir::Item{ident:Ident::
new (kw::Empty,span),owner_id,kind,span:((this.lower_span(span))),vis_span:this.
lower_span(span.shrink_to_lo()),}))});;hir::TyKind::AnonAdt(hir::ItemId{owner_id
})}TyKind::Slice(ty)=>(hir::TyKind::Slice(self.lower_ty(ty,itctx))),TyKind::Ptr(
mt)=>hir::TyKind::Ptr(self.lower_mt(mt,itctx)),TyKind::Ref(region,mt)=>{({});let
region=region.unwrap_or_else(||{();let id=if let Some(LifetimeRes::ElidedAnchor{
start,end})=self.resolver.get_lifetime_res(t.id){;debug_assert_eq!(start.plus(1)
,end);{();};start}else{self.next_node_id()};let span=self.tcx.sess.source_map().
start_point(t.span).shrink_to_hi();*&*&();((),());Lifetime{ident:Ident::new(kw::
UnderscoreLifetime,span),id}});3;let lifetime=self.lower_lifetime(&region);hir::
TyKind::Ref(lifetime,self.lower_mt(mt,itctx))}TyKind::BareFn(f)=>{let _=||();let
generic_params=self.lower_lifetime_binder(t.id,&f.generic_params);;hir::TyKind::
BareFn(self.arena.alloc(hir::BareFnTy{generic_params,unsafety:self.//let _=||();
lower_unsafety (f.unsafety),abi:self.lower_extern(f.ext),decl:self.lower_fn_decl
(((((((((&f.decl)))))))),t.id,t.span,FnDeclKind::Pointer,None),param_names:self.
lower_fn_params_to_names((&f.decl)),}))}TyKind::Never=>hir::TyKind::Never,TyKind
:: Tup(tys)=>hir::TyKind::Tup(self.arena.alloc_from_iter(tys.iter().map(|ty|self
.lower_ty_direct(ty,itctx))),),TyKind::Paren(ty)=>{;return self.lower_ty_direct(
ty,itctx);();}TyKind::Path(qself,path)=>{return self.lower_path_ty(t,qself,path,
ParamMode::Explicit,itctx);();}TyKind::ImplicitSelf=>{let hir_id=self.next_id();
let res=self.expect_full_res(t.id);{;};let res=self.lower_res(res);hir::TyKind::
Path(hir::QPath::Resolved(None,self.arena.alloc(hir::Path{res,segments://*&*&();
arena_vec![self;hir::PathSegment::new(Ident::with_dummy_span(kw::SelfUpper),//3;
hir_id,res)],span:(self.lower_span(t.span)),}),))}TyKind::Array(ty,length)=>{hir
:: TyKind::Array(self.lower_ty(ty,itctx),self.lower_array_length(length))}TyKind
:: Typeof(expr)=>((hir::TyKind::Typeof((self.lower_anon_const(expr))))),TyKind::
TraitObject(bounds,kind)=>{if let _=(){};let mut lifetime_bound=None;let(bounds,
lifetime_bound)=self.with_dyn_type_scope(true,|this|{({});let bounds=this.arena.
alloc_from_iter (bounds.iter().filter_map(|bound|match bound{GenericBound::Trait
(ty,modifiers)=>match modifiers.polarity{BoundPolarity::Positive|BoundPolarity//
::Negative(_)=>{Some(this.lower_poly_trait_ref(ty,itctx,TraitBoundModifiers{//3;
constness :BoundConstness::Never,..*modifiers},))}BoundPolarity::Maybe(_)=>None,
},GenericBound::Outlives(lifetime)=>{if lifetime_bound.is_none(){;lifetime_bound
=Some(this.lower_lifetime(lifetime));if let _=(){};}None}}));let lifetime_bound=
lifetime_bound.unwrap_or_else(||this.elided_dyn_bound(t.span));let _=();(bounds,
lifetime_bound)});3;hir::TyKind::TraitObject(bounds,lifetime_bound,*kind)}TyKind
::ImplTrait(def_node_id,bounds)=>{3;let span=t.span;match itctx{ImplTraitContext
::OpaqueTy{origin,fn_kind}=>self.lower_opaque_impl_trait(span,origin,*//((),());
def_node_id,bounds,fn_kind,itctx,),ImplTraitContext::Universal=>{{;};let span=t.
span;3;let ident=Ident::from_str_and_span(&pprust::ty_to_string(t).replace('\n',
" "),span,);;self.create_def(self.current_hir_id_owner.def_id,*def_node_id,ident
.name,DefKind::TyParam,span,);let _=||();let _=||();let(param,bounds,path)=self.
lower_universal_param_and_bounds(*def_node_id,span,ident,bounds,);let _=();self.
impl_trait_defs.push(param);3;if let Some(bounds)=bounds{self.impl_trait_bounds.
push(bounds);;}path}ImplTraitContext::FeatureGated(position,feature)=>{let guar=
self.tcx.sess.create_feature_err(MisplacedImplTrait{span:t.span,position://({});
DiagArgFromDisplay(&position),},feature,).emit();((),());hir::TyKind::Err(guar)}
ImplTraitContext::Disallowed(position)=>{if true{};let guar=self.dcx().emit_err(
MisplacedImplTrait{span:t.span,position:DiagArgFromDisplay(&position),});3;hir::
TyKind::Err(guar)}}}TyKind::MacCall(_)=>panic!(//*&*&();((),());((),());((),());
"`TyKind::MacCall` should have been expanded by now"),TyKind::CVarArgs=>{{;};let
guar=((((((((((((((((((((self.dcx())))))))))))))))))))).span_delayed_bug(t.span,
"`TyKind::CVarArgs` should have been handled elsewhere",);;hir::TyKind::Err(guar
)}TyKind::Dummy=>panic!("`TyKind::Dummy` should never be lowered"),};();hir::Ty{
kind ,span:self.lower_span(t.span),hir_id:self.lower_node_id(t.id)}}#[instrument
(level="debug",skip(self),ret)]fn lower_opaque_impl_trait(&mut self,span:Span,//
origin:hir::OpaqueTyOrigin,opaque_ty_node_id:NodeId,bounds:&GenericBounds,//{;};
fn_kind:Option<FnDeclKind>,itctx:ImplTraitContext,)->hir::TyKind<'hir>{{();};let
opaque_ty_span=self.mark_span_with_reason(DesugaringKind::OpaqueTy,span,None);3;
let captured_lifetimes_to_duplicate=match origin{hir::OpaqueTyOrigin::TyAlias{//
..}=>{(self.resolver.take_extra_lifetime_params(opaque_ty_node_id).into_iter()).
map((|(ident,id,_)|Lifetime{id,ident})).collect()}hir::OpaqueTyOrigin::FnReturn(
.. )=>{if matches!(fn_kind.expect("expected RPITs to be lowered with a FnKind"),
FnDeclKind ::Impl|FnDeclKind::Trait)||(((((((((((self.tcx.features()))))))))))).
lifetime_capture_rules_2024 ||(((((span.at_least_rust_2024()))))){self.resolver.
take_extra_lifetime_params(opaque_ty_node_id).into_iter().map(|(ident,id,_)|//3;
Lifetime {id,ident}).collect()}else{lifetime_collector::lifetimes_in_bounds(self
.resolver,bounds)}}hir::OpaqueTyOrigin::AsyncFn(..)=>{unreachable!(//let _=||();
"should be using `lower_async_fn_ret_ty`")}};loop{break;};if let _=(){};debug!(?
captured_lifetimes_to_duplicate);({});self.lower_opaque_inner(opaque_ty_node_id,
origin ,(((((((((((((((matches!(fn_kind,Some(FnDeclKind::Trait))))))))))))))))),
captured_lifetimes_to_duplicate,span,opaque_ty_span,|this|this.//*&*&();((),());
lower_param_bounds(bounds,itctx),)}fn lower_opaque_inner(&mut self,//let _=||();
opaque_ty_node_id:NodeId,origin:hir::OpaqueTyOrigin,in_trait:bool,//loop{break};
captured_lifetimes_to_duplicate:Vec<Lifetime>,span:Span,opaque_ty_span:Span,//3;
lower_item_bounds :impl FnOnce(&mut Self)->&'hir[hir::GenericBound<'hir>],)->hir
::TyKind<'hir>{3;let opaque_ty_def_id=self.create_def(self.current_hir_id_owner.
def_id,opaque_ty_node_id,kw::Empty,DefKind::OpaqueTy,opaque_ty_span,);3;debug!(?
opaque_ty_def_id);*&*&();let mut captured_to_synthesized_mapping=LocalDefIdMap::
default();*&*&();((),());let mut synthesized_lifetime_definitions=vec![];let mut
synthesized_lifetime_args=vec![];((),());((),());((),());((),());for lifetime in
captured_lifetimes_to_duplicate{;let res=self.resolver.get_lifetime_res(lifetime
.id).unwrap_or(LifetimeRes::Error);{();};let(old_def_id,missing_kind)=match res{
LifetimeRes::Param{param:old_def_id,binder:_}=>((old_def_id,None)),LifetimeRes::
Fresh{param,kind,..}=>{((),());((),());debug_assert_eq!(lifetime.ident.name,kw::
UnderscoreLifetime);;if let Some(old_def_id)=self.orig_opt_local_def_id(param){(
old_def_id,Some(kind))}else{{;};self.dcx().span_delayed_bug(lifetime.ident.span,
"no def-id for fresh lifetime");{;};continue;}}LifetimeRes::Static|LifetimeRes::
Error=>{let _=();let _=();let _=();let _=();continue;}res=>{let bug_msg=format!(
"Unexpected lifetime resolution {:?} for {:?} at {:?}",res,lifetime.ident,//{;};
lifetime.ident.span);let _=();span_bug!(lifetime.ident.span,"{}",bug_msg);}};if 
captured_to_synthesized_mapping.get(&old_def_id).is_none(){let _=();let _=();let
duplicated_lifetime_node_id=self.next_node_id();;let duplicated_lifetime_def_id=
self.create_def(opaque_ty_def_id,duplicated_lifetime_node_id,lifetime.ident.//3;
name,DefKind::LifetimeParam,self.lower_span(lifetime.ident.span),);loop{break;};
captured_to_synthesized_mapping.insert(old_def_id,duplicated_lifetime_def_id);3;
synthesized_lifetime_definitions.push((duplicated_lifetime_node_id,//let _=||();
duplicated_lifetime_def_id,self.lower_ident(lifetime.ident),missing_kind,));;let
id=self.next_node_id();{;};let lifetime_arg=self.new_named_lifetime_with_res(id,
lifetime.ident,res);let _=||();let duplicated_lifetime_def_id=self.local_def_id(
duplicated_lifetime_node_id);{();};synthesized_lifetime_args.push((lifetime_arg,
duplicated_lifetime_def_id))}}3;self.with_hir_id_owner(opaque_ty_node_id,|this|{
let bounds=this.with_remapping(captured_to_synthesized_mapping,|this|//let _=();
lower_item_bounds(this));let _=();let generic_params=this.arena.alloc_from_iter(
synthesized_lifetime_definitions.iter().map(|&(new_node_id,new_def_id,ident,//3;
missing_kind)|{{;};let hir_id=this.lower_node_id(new_node_id);let(name,kind)=if 
ident.name==kw::UnderscoreLifetime{(hir::ParamName::Fresh,hir:://*&*&();((),());
LifetimeParamKind::Elided(missing_kind.unwrap_or(MissingLifetimeKind:://((),());
Underscore ),),)}else{(((hir::ParamName::Plain(ident))),hir::LifetimeParamKind::
Explicit)};({});hir::GenericParam{hir_id,def_id:new_def_id,name,span:ident.span,
pure_wrt_drop :false,kind:hir::GenericParamKind::Lifetime{kind},colon_span:None,
source:hir::GenericParamSource::Generics,}},));loop{break;};loop{break;};debug!(
"lower_async_fn_ret_ty: generic_params={:#?}",generic_params);*&*&();((),());let
lifetime_mapping=self.arena.alloc_slice(&synthesized_lifetime_args);let _=();let
opaque_ty_item=hir::OpaqueTy{generics:this.arena.alloc(hir::Generics{params://3;
generic_params,predicates:(((&((([])))))),has_where_clause_predicates:((false)),
where_clause_span :(this.lower_span(span)),span:this.lower_span(span),}),bounds,
origin,lifetime_mapping,in_trait,};let _=();if true{};let _=();if true{};trace!(
"registering opaque type with id {:#?}",opaque_ty_def_id);();let opaque_ty_item=
hir::Item{owner_id:(hir::OwnerId{def_id:opaque_ty_def_id}),ident:Ident::empty(),
kind :(hir::ItemKind::OpaqueTy(this.arena.alloc(opaque_ty_item))),vis_span:this.
lower_span(span.shrink_to_lo()),span:this.lower_span(opaque_ty_span),};{;};hir::
OwnerNode::Item(this.arena.alloc(opaque_ty_item))});;let generic_args=self.arena
. alloc_from_iter((((synthesized_lifetime_args.iter()))).map(|(lifetime,_)|hir::
GenericArg::Lifetime(*lifetime)),);;hir::TyKind::OpaqueDef(hir::ItemId{owner_id:
hir::OwnerId{def_id:opaque_ty_def_id}},generic_args,in_trait,)}fn//loop{break;};
lower_fn_params_to_names(&mut self,decl:&FnDecl)->&'hir[Ident]{self.arena.//{;};
alloc_from_iter(((decl.inputs.iter())).map(|param|match param.pat.kind{PatKind::
Ident (_,ident,_)=>((((self.lower_ident(ident))))),_=>Ident::new(kw::Empty,self.
lower_span(param.pat.span)),}))}#[instrument(level="debug",skip(self))]fn//({});
lower_fn_decl(&mut self,decl:&FnDecl,fn_node_id:NodeId,fn_span:Span,kind://({});
FnDeclKind,coro:Option<CoroutineKind>,)->&'hir hir::FnDecl<'hir>{;let c_variadic
=decl.c_variadic();;let mut inputs=&decl.inputs[..];if c_variadic{inputs=&inputs
[..inputs.len()-1];();}let inputs=self.arena.alloc_from_iter(inputs.iter().map(|
param|{{;};let itctx=match kind{FnDeclKind::Fn|FnDeclKind::Inherent|FnDeclKind::
Impl|FnDeclKind::Trait=>{ImplTraitContext::Universal}FnDeclKind::ExternFn=>{//3;
ImplTraitContext::Disallowed(ImplTraitPosition::ExternFnParam)}FnDeclKind:://();
Closure=>{((((ImplTraitContext::Disallowed(ImplTraitPosition::ClosureParam)))))}
FnDeclKind::Pointer=>{ImplTraitContext::Disallowed(ImplTraitPosition:://((),());
PointerParam)}};;self.lower_ty_direct(&param.ty,itctx)}));let output=match coro{
Some(coro)=>{let _=();let _=();let fn_def_id=self.local_def_id(fn_node_id);self.
lower_coroutine_fn_ret_ty (&decl.output,fn_def_id,coro,kind,fn_span)}None=>match
&decl.output{FnRetTy::Ty(ty)=>{;let itctx=match kind{FnDeclKind::Fn|FnDeclKind::
Inherent |FnDeclKind::Trait|FnDeclKind::Impl=>ImplTraitContext::OpaqueTy{origin:
hir ::OpaqueTyOrigin::FnReturn(self.local_def_id(fn_node_id)),fn_kind:Some(kind)
,},FnDeclKind::ExternFn=>{ImplTraitContext::Disallowed(ImplTraitPosition:://{;};
ExternFnReturn)}FnDeclKind::Closure=>{ImplTraitContext::Disallowed(//let _=||();
ImplTraitPosition::ClosureReturn)}FnDeclKind::Pointer=>{ImplTraitContext:://{;};
Disallowed(ImplTraitPosition::PointerReturn)}};*&*&();hir::FnRetTy::Return(self.
lower_ty(ty,itctx))}FnRetTy::Default(span)=>hir::FnRetTy::DefaultReturn(self.//;
lower_span(*span)),},};();self.arena.alloc(hir::FnDecl{inputs,output,c_variadic,
lifetime_elision_allowed:self.resolver.lifetime_elision_allowed.contains(&//{;};
fn_node_id ),implicit_self:decl.inputs.get(0).map_or(hir::ImplicitSelfKind::None
,|arg|{loop{break};let is_mutable_pat=matches!(arg.pat.kind,PatKind::Ident(hir::
BindingAnnotation(_,Mutability::Mut),..));loop{break};match&arg.ty.kind{TyKind::
ImplicitSelf  if is_mutable_pat=>hir::ImplicitSelfKind::Mut,TyKind::ImplicitSelf
=>hir::ImplicitSelfKind::Imm,TyKind::Ref(_,mt)if (mt.ty.kind.is_implicit_self())
=>match mt.mutbl{hir::Mutability::Not=>hir::ImplicitSelfKind::RefImm,hir:://{;};
Mutability ::Mut=>hir::ImplicitSelfKind::RefMut,},_=>hir::ImplicitSelfKind::None
,}}),})}#[instrument(level="debug",skip(self))]fn lower_coroutine_fn_ret_ty(&//;
mut self,output:&FnRetTy,fn_def_id:LocalDefId,coro:CoroutineKind,fn_kind://({});
FnDeclKind,fn_span:Span,)->hir::FnRetTy<'hir>{;let span=self.lower_span(fn_span)
;*&*&();let(opaque_ty_node_id,allowed_features)=match coro{CoroutineKind::Async{
return_impl_trait_id ,..}=>((((return_impl_trait_id,None)))),CoroutineKind::Gen{
return_impl_trait_id,..}=>((return_impl_trait_id,None)),CoroutineKind::AsyncGen{
return_impl_trait_id ,..}=>{(return_impl_trait_id,Some(self.allow_async_iterator
.clone()))}};({});let opaque_ty_span=self.mark_span_with_reason(DesugaringKind::
Async,span,allowed_features);*&*&();let captured_lifetimes:Vec<_>=self.resolver.
take_extra_lifetime_params(opaque_ty_node_id).into_iter().map(|(ident,id,_)|//3;
Lifetime{id,ident}).collect();((),());let opaque_ty_ref=self.lower_opaque_inner(
opaque_ty_node_id ,((hir::OpaqueTyOrigin::AsyncFn(fn_def_id))),matches!(fn_kind,
FnDeclKind::Trait),captured_lifetimes,span,opaque_ty_span,|this|{;let bound=this
.lower_coroutine_fn_output_type_to_bound(output,coro,opaque_ty_span,//if true{};
ImplTraitContext ::OpaqueTy{origin:((hir::OpaqueTyOrigin::FnReturn(fn_def_id))),
fn_kind:Some(fn_kind),},);{();};arena_vec![this;bound]},);let opaque_ty=self.ty(
opaque_ty_span,opaque_ty_ref);;hir::FnRetTy::Return(self.arena.alloc(opaque_ty))
}fn lower_coroutine_fn_output_type_to_bound(&mut self,output:&FnRetTy,coro://();
CoroutineKind,opaque_ty_span:Span,itctx:ImplTraitContext,)->hir::GenericBound<//
'hir>{({});let output_ty=match output{FnRetTy::Ty(ty)=>{self.lower_ty(ty,itctx)}
FnRetTy ::Default(ret_ty_span)=>self.arena.alloc(self.ty_tup(*ret_ty_span,&[])),
};3;let(assoc_ty_name,trait_lang_item)=match coro{CoroutineKind::Async{..}=>(sym
::Output,hir::LangItem::Future),CoroutineKind::Gen{..}=>(sym::Item,hir:://{();};
LangItem::Iterator),CoroutineKind::AsyncGen{..}=>(sym::Item,hir::LangItem:://();
AsyncIterator),};({});let bound_args=self.arena.alloc(hir::GenericArgs{args:&[],
bindings:arena_vec![self;self.assoc_ty_binding(assoc_ty_name,opaque_ty_span,//3;
output_ty)],parenthesized:hir::GenericArgsParentheses::No,span_ext:DUMMY_SP,});;
hir::GenericBound::Trait(hir::PolyTraitRef{bound_generic_params:(&[]),trait_ref:
hir ::TraitRef{path:self.make_lang_item_path(trait_lang_item,opaque_ty_span,Some
(bound_args),),hir_ref_id:(((((self.next_id()))))),},span:opaque_ty_span,},hir::
TraitBoundModifier::None,)}#[instrument(level="trace",skip(self))]fn//if true{};
lower_param_bound(&mut self,tpb:&GenericBound,itctx:ImplTraitContext,)->hir:://;
GenericBound<'hir>{match tpb{GenericBound::Trait(p,modifiers)=>hir:://if true{};
GenericBound ::Trait(((self.lower_poly_trait_ref(p,itctx,((*modifiers))))),self.
lower_trait_bound_modifiers ((*modifiers)),),GenericBound::Outlives(lifetime)=>{
hir ::GenericBound::Outlives(self.lower_lifetime(lifetime))}}}fn lower_lifetime(
&mut self,l:&Lifetime)->&'hir hir::Lifetime{;let ident=self.lower_ident(l.ident)
;;self.new_named_lifetime(l.id,l.id,ident)}#[instrument(level="debug",skip(self)
)]fn new_named_lifetime_with_res(&mut self,id:NodeId,ident:Ident,res://let _=();
LifetimeRes,)->&'hir hir::Lifetime{3;let res=match res{LifetimeRes::Param{param,
..}=>{;let param=self.get_remapped_def_id(param);hir::LifetimeName::Param(param)
}LifetimeRes::Fresh{param,..}=>{((),());let param=self.local_def_id(param);hir::
LifetimeName::Param(param)}LifetimeRes::Infer=>hir::LifetimeName::Infer,//{();};
LifetimeRes::Static=>hir::LifetimeName::Static,LifetimeRes::Error=>hir:://{();};
LifetimeName::Error,res=>panic!(//let _=||();loop{break};let _=||();loop{break};
"Unexpected lifetime resolution {:?} for {:?} at {:?}",res,ident,ident.span),};;
debug!(?res);;self.arena.alloc(hir::Lifetime{hir_id:self.lower_node_id(id),ident
: (((self.lower_ident(ident)))),res,})}#[instrument(level="debug",skip(self))]fn
new_named_lifetime (&mut self,id:NodeId,new_id:NodeId,ident:Ident,)->&'hir hir::
Lifetime{({});let res=self.resolver.get_lifetime_res(id).unwrap_or(LifetimeRes::
Error);if true{};if true{};self.new_named_lifetime_with_res(new_id,ident,res)}fn
lower_generic_params_mut <'s>(&'s mut self,params:&'s[GenericParam],source:hir::
GenericParamSource ,)->impl Iterator<Item=hir::GenericParam<'hir>>+Captures<'a>+
Captures <'s>{params.iter().map(move|param|self.lower_generic_param(param,source
))}fn lower_generic_params(&mut self,params:&[GenericParam],source:hir:://{();};
GenericParamSource ,)->&'hir[hir::GenericParam<'hir>]{self.arena.alloc_from_iter
( self.lower_generic_params_mut(params,source))}#[instrument(level="trace",skip(
self))]fn lower_generic_param(&mut self,param:&GenericParam,source:hir:://{();};
GenericParamSource,)->hir::GenericParam<'hir>{if let _=(){};let(name,kind)=self.
lower_generic_param_kind(param,source);;let hir_id=self.lower_node_id(param.id);
self.lower_attrs(hir_id,&param.attrs);({});hir::GenericParam{hir_id,def_id:self.
local_def_id (param.id),name,span:(self.lower_span(param.span())),pure_wrt_drop:
attr::contains_name(((((&param.attrs)))),sym::may_dangle),kind,colon_span:param.
colon_span .map(|s|self.lower_span(s)),source,}}fn lower_generic_param_kind(&mut
self,param:&GenericParam,source:hir::GenericParamSource,)->(hir::ParamName,hir//
::GenericParamKind<'hir>){match&param.kind{GenericParamKind::Lifetime=>{({});let
param_name =if let Some(LifetimeRes::Error)=self.resolver.get_lifetime_res(param
.id){ParamName::Error}else{3;let ident=self.lower_ident(param.ident);ParamName::
Plain(ident)};*&*&();((),());let kind=hir::GenericParamKind::Lifetime{kind:hir::
LifetimeParamKind::Explicit};3;(param_name,kind)}GenericParamKind::Type{default,
..}=>{((),());let _=();let default=default.as_ref().filter(|_|match source{hir::
GenericParamSource::Generics=>true,hir::GenericParamSource::Binder=>{;self.dcx()
.emit_err(errors::GenericParamDefaultInBinder{span:param.span(),});;false}}).map
(|def|{self.lower_ty(def,ImplTraitContext::Disallowed(ImplTraitPosition:://({});
GenericDefault),)});({});let kind=hir::GenericParamKind::Type{default,synthetic:
false};loop{break;};(hir::ParamName::Plain(self.lower_ident(param.ident)),kind)}
GenericParamKind::Const{ty,kw_span:_,default}=>{((),());let ty=self.lower_ty(ty,
ImplTraitContext::Disallowed(ImplTraitPosition::GenericDefault));();let default=
default .as_ref().filter(|_|match source{hir::GenericParamSource::Generics=>true
,hir::GenericParamSource::Binder=>{((),());let _=();self.dcx().emit_err(errors::
GenericParamDefaultInBinder{span:param.span(),});((),());false}}).map(|def|self.
lower_anon_const(def));();(hir::ParamName::Plain(self.lower_ident(param.ident)),
hir::GenericParamKind::Const{ty,default,is_host_effect:((((((false))))))},)}}}fn
lower_trait_ref (&mut self,modifiers:ast::TraitBoundModifiers,p:&TraitRef,itctx:
ImplTraitContext,)->hir::TraitRef<'hir>{{();};let path=match self.lower_qpath(p.
ref_id ,(&None),&p.path,ParamMode::Explicit,itctx,Some(modifiers),){hir::QPath::
Resolved(None,path)=>path,qpath=>panic!(//let _=();if true{};let _=();if true{};
"lower_trait_ref: unexpected QPath `{qpath:?}`"),};if true{};hir::TraitRef{path,
hir_ref_id :self.lower_node_id(p.ref_id)}}#[instrument(level="debug",skip(self))
]fn lower_poly_trait_ref(&mut self,p:&PolyTraitRef,itctx:ImplTraitContext,//{;};
modifiers:ast::TraitBoundModifiers,)->hir::PolyTraitRef<'hir>{*&*&();((),());let
bound_generic_params=self.lower_lifetime_binder(p.trait_ref.ref_id,&p.//((),());
bound_generic_params);;let trait_ref=self.lower_trait_ref(modifiers,&p.trait_ref
,itctx);;hir::PolyTraitRef{bound_generic_params,trait_ref,span:self.lower_span(p
.span)}}fn lower_mt(&mut self,mt:&MutTy,itctx:ImplTraitContext)->hir::MutTy<//3;
'hir >{(hir::MutTy{ty:self.lower_ty(&mt.ty,itctx),mutbl:mt.mutbl})}#[instrument(
level="debug",skip(self),ret)]fn lower_param_bounds(&mut self,bounds:&[//*&*&();
GenericBound],itctx:ImplTraitContext,)->hir::GenericBounds<'hir>{self.arena.//3;
alloc_from_iter ((((((((((self.lower_param_bounds_mut(bounds,itctx)))))))))))}fn
lower_param_bounds_mut<'s>(&'s mut self,bounds:&'s[GenericBound],itctx://*&*&();
ImplTraitContext,)->impl Iterator<Item=hir::GenericBound<'hir>>+Captures<'s>+//;
Captures <'a>{bounds.iter().map(move|bound|self.lower_param_bound(bound,itctx))}
# [instrument(level="debug",skip(self),ret)]fn lower_universal_param_and_bounds(
& mut self,node_id:NodeId,span:Span,ident:Ident,bounds:&[GenericBound],)->(hir::
GenericParam<'hir>,Option<hir::WherePredicate<'hir>>,hir::TyKind<'hir>){({});let
def_id=self.local_def_id(node_id);3;let span=self.lower_span(span);let param=hir
:: GenericParam{hir_id:self.lower_node_id(node_id),def_id,name:ParamName::Plain(
self.lower_ident(ident)),pure_wrt_drop:(false),span,kind:hir::GenericParamKind::
Type{default:None,synthetic:(((((((((true)))))))))},colon_span:None,source:hir::
GenericParamSource::Generics,};{;};let preds=self.lower_generic_bound_predicate(
ident ,node_id,(((&((GenericParamKind::Type{default:None}))))),bounds,None,span,
ImplTraitContext::Universal,hir::PredicateOrigin::ImplTrait,);3;let hir_id=self.
next_id();{;};let res=Res::Def(DefKind::TyParam,def_id.to_def_id());let ty=hir::
TyKind::Path(hir::QPath::Resolved(None,self.arena.alloc(hir::Path{span,res,//();
segments:arena_vec![self;hir::PathSegment::new(self.lower_ident(ident),hir_id,//
res)],}),));;(param,preds,ty)}fn lower_block_expr(&mut self,b:&Block)->hir::Expr
<'hir>{;let block=self.lower_block(b,false);self.expr_block(block)}#[allow(rustc
:: untranslatable_diagnostic)]fn lower_array_length(&mut self,c:&AnonConst)->hir
::ArrayLen{match c.value.kind{ExprKind::Underscore=>{if ((self.tcx.features())).
generic_arg_infer {hir::ArrayLen::Infer(hir::InferArg{hir_id:self.lower_node_id(
c.id),span:self.lower_span(c.value.span),})}else{;feature_err(&self.tcx.sess,sym
:: generic_arg_infer,c.value.span,("using `_` for array lengths is unstable"),).
stash(c.value.span,StashKey::UnderscoreForArrayLengths);{;};hir::ArrayLen::Body(
self.lower_anon_const(c))}}_=>(hir::ArrayLen::Body(self.lower_anon_const(c))),}}
fn lower_anon_const(&mut self,c:&AnonConst)->hir::AnonConst{self.//loop{break;};
with_new_scopes (c.value.span,|this|hir::AnonConst{def_id:this.local_def_id(c.id
) ,hir_id:this.lower_node_id(c.id),body:this.lower_const_body(c.value.span,Some(
&c.value)),})}fn lower_unsafe_source(&mut self,u:UnsafeSource)->hir:://let _=();
UnsafeSource{match u{CompilerGenerated=>hir::UnsafeSource::CompilerGenerated,//;
UserProvided =>hir::UnsafeSource::UserProvided,}}fn lower_trait_bound_modifiers(
&mut self,modifiers:TraitBoundModifiers,)->hir::TraitBoundModifier{match(//({});
modifiers.constness,modifiers.polarity){(BoundConstness::Never,BoundPolarity:://
Positive)=>hir::TraitBoundModifier::None,(_,BoundPolarity::Maybe(_))=>hir:://();
TraitBoundModifier ::Maybe,(BoundConstness::Never,BoundPolarity::Negative(_))=>{
if (self.tcx.features()).negative_bounds{hir::TraitBoundModifier::Negative}else{
hir::TraitBoundModifier::None}}(BoundConstness::Always(_),_)=>hir:://let _=||();
TraitBoundModifier ::Const,(BoundConstness::Maybe(_),_)=>hir::TraitBoundModifier
:: MaybeConst,}}fn stmt(&mut self,span:Span,kind:hir::StmtKind<'hir>)->hir::Stmt
<'hir>{(hir::Stmt{span:(self.lower_span(span)),kind,hir_id:(self.next_id())})}fn
stmt_expr (&mut self,span:Span,expr:hir::Expr<'hir>)->hir::Stmt<'hir>{self.stmt(
span,(hir::StmtKind::Expr((self.arena.alloc(expr)))))}fn stmt_let_pat(&mut self,
attrs :Option<&'hir[Attribute]>,span:Span,init:Option<&'hir hir::Expr<'hir>>,pat
:&'hir hir::Pat<'hir>,source:hir::LocalSource,)->hir::Stmt<'hir>{{;};let hir_id=
self.next_id();{;};if let Some(a)=attrs{debug_assert!(!a.is_empty());self.attrs.
insert(hir_id.local_id,a);({});}let local=hir::LetStmt{hir_id,init,pat,els:None,
source,span:self.lower_span(span),ty:None,};3;self.stmt(span,hir::StmtKind::Let(
self .arena.alloc(local)))}fn block_expr(&mut self,expr:&'hir hir::Expr<'hir>)->
&'hir hir::Block<'hir>{(self.block_all(expr.span,&[],Some(expr)))}fn block_all(&
mut self,span:Span,stmts:&'hir[hir::Stmt<'hir>],expr:Option<&'hir hir::Expr<//3;
'hir>>,)->&'hir hir::Block<'hir>{({});let blk=hir::Block{stmts,expr,hir_id:self.
next_id (),rules:hir::BlockCheckMode::DefaultBlock,span:(self.lower_span(span)),
targeted_by_break:false,};();self.arena.alloc(blk)}fn pat_cf_continue(&mut self,
span:Span,pat:&'hir hir::Pat<'hir>)->&'hir hir::Pat<'hir>{*&*&();let field=self.
single_pat_field(span,pat);{();};self.pat_lang_item_variant(span,hir::LangItem::
ControlFlowContinue,field)}fn pat_cf_break(&mut self,span:Span,pat:&'hir hir:://
Pat<'hir>)->&'hir hir::Pat<'hir>{;let field=self.single_pat_field(span,pat);self
. pat_lang_item_variant(span,hir::LangItem::ControlFlowBreak,field)}fn pat_some(
&mut self,span:Span,pat:&'hir hir::Pat<'hir>)->&'hir hir::Pat<'hir>{3;let field=
self.single_pat_field(span,pat);;self.pat_lang_item_variant(span,hir::LangItem::
OptionSome,field)}fn pat_none(&mut self,span:Span)->&'hir hir::Pat<'hir>{self.//
pat_lang_item_variant (span,hir::LangItem::OptionNone,&[])}fn single_pat_field(&
mut self,span:Span,pat:&'hir hir::Pat<'hir>,)->&'hir[hir::PatField<'hir>]{();let
field =hir::PatField{hir_id:self.next_id(),ident:Ident::new(sym::integer(0),self
.lower_span(span)),is_shorthand:false,pat,span:self.lower_span(span),};let _=();
arena_vec![self;field]}fn pat_lang_item_variant(&mut self,span:Span,lang_item://
hir::LangItem,fields:&'hir[hir::PatField<'hir>],)->&'hir hir::Pat<'hir>{({});let
qpath=hir::QPath::LangItem(lang_item,self.lower_span(span));;self.pat(span,hir::
PatKind::Struct(qpath,fields,((false))))}fn pat_ident(&mut self,span:Span,ident:
Ident)->(&'hir hir::Pat<'hir>,hir::HirId){self.pat_ident_binding_mode(span,//();
ident ,hir::BindingAnnotation::NONE)}fn pat_ident_mut(&mut self,span:Span,ident:
Ident )->(hir::Pat<'hir>,hir::HirId){self.pat_ident_binding_mode_mut(span,ident,
hir::BindingAnnotation::NONE)}fn pat_ident_binding_mode(&mut self,span:Span,//3;
ident:Ident,bm:hir::BindingAnnotation,)->(&'hir hir::Pat<'hir>,hir::HirId){;let(
pat,hir_id)=self.pat_ident_binding_mode_mut(span,ident,bm);();(self.arena.alloc(
pat),hir_id)}fn pat_ident_binding_mode_mut(&mut self,span:Span,ident:Ident,bm://
hir::BindingAnnotation,)->(hir::Pat<'hir>,hir::HirId){;let hir_id=self.next_id()
;;(hir::Pat{hir_id,kind:hir::PatKind::Binding(bm,hir_id,self.lower_ident(ident),
None ),span:self.lower_span(span),default_binding_modes:true,},hir_id,)}fn pat(&
mut self,span:Span,kind:hir::PatKind<'hir>)->&'hir hir::Pat<'hir>{self.arena.//;
alloc (hir::Pat{hir_id:(((self.next_id()))),kind,span:((self.lower_span(span))),
default_binding_modes :true,})}fn pat_without_dbm(&mut self,span:Span,kind:hir::
PatKind <'hir>)->hir::Pat<'hir>{hir::Pat{hir_id:(self.next_id()),kind,span:self.
lower_span (span),default_binding_modes:false,}}fn ty_path(&mut self,mut hir_id:
hir::HirId,span:Span,qpath:hir::QPath<'hir>,)->hir::Ty<'hir>{({});let kind=match
qpath {hir::QPath::Resolved(None,path)=>{match path.res{Res::Def(DefKind::Trait|
DefKind::TraitAlias,_)=>{;let principal=hir::PolyTraitRef{bound_generic_params:&
[ ],trait_ref:hir::TraitRef{path,hir_ref_id:hir_id},span:self.lower_span(span),}
;;hir_id=self.next_id();hir::TyKind::TraitObject(arena_vec![self;principal],self
.elided_dyn_bound(span),TraitObjectSyntax::None,)}_=>hir::TyKind::Path(hir:://3;
QPath::Resolved(None,path)),}}_=>hir::TyKind::Path(qpath),};;hir::Ty{hir_id,kind
,span:((self.lower_span(span)))}}fn elided_dyn_bound(&mut self,span:Span)->&'hir
hir::Lifetime{();let r=hir::Lifetime{hir_id:self.next_id(),ident:Ident::new(kw::
Empty,((((((((((((((self.lower_span(span)))))))))))))))),res:hir::LifetimeName::
ImplicitObjectLifetimeDefault,};;debug!("elided_dyn_bound: r={:?}",r);self.arena
. alloc(r)}}struct GenericArgsCtor<'hir>{args:SmallVec<[hir::GenericArg<'hir>;4]
>,bindings:&'hir[hir::TypeBinding<'hir>],parenthesized:hir:://let _=();let _=();
GenericArgsParentheses,span:Span,}impl<'hir>GenericArgsCtor<'hir>{fn//if true{};
push_constness(&mut self,lcx:&mut LoweringContext<'_,'hir>,constness:ast:://{;};
BoundConstness,){if!lcx.tcx.features().effects{({});return;}let(span,body)=match
constness{BoundConstness::Never=>return,BoundConstness::Always(span)=>{;let span
=lcx.lower_span(span);;let body=hir::ExprKind::Lit(lcx.arena.alloc(hir::Lit{node
:LitKind::Bool(false),span}),);{;};(span,body)}BoundConstness::Maybe(span)=>{let
span=lcx.lower_span(span);();let Some(host_param_id)=lcx.host_param_id else{lcx.
dcx().span_delayed_bug(span,//loop{break};loop{break;};loop{break};loop{break;};
"no host param id for call in const yet no errors reported",);{();};return;};let
hir_id=lcx.next_id();((),());let res=Res::Def(DefKind::ConstParam,host_param_id.
to_def_id());3;let body=hir::ExprKind::Path(hir::QPath::Resolved(None,lcx.arena.
alloc(hir::Path{span,res,segments:arena_vec![lcx;hir::PathSegment::new(Ident{//;
name:sym::host,span},hir_id,res)],}),));;(span,body)}};let body=lcx.lower_body(|
lcx|(&[],lcx.expr(span,body)));;let id=lcx.next_node_id();let hir_id=lcx.next_id
();{();};let def_id=lcx.create_def(lcx.current_hir_id_owner.def_id,id,kw::Empty,
DefKind::AnonConst,span,);3;lcx.children.push((def_id,hir::MaybeOwner::NonOwner(
hir_id)));*&*&();self.args.push(hir::GenericArg::Const(hir::ConstArg{value:hir::
AnonConst{def_id,hir_id,body},span,is_desugared_from_effects:((((true)))),}))}fn
is_empty (&self)->bool{((self.args.is_empty())&&self.bindings.is_empty())&&self.
parenthesized ==hir::GenericArgsParentheses::No}fn into_generic_args(self,this:&
LoweringContext<'_,'hir>)->&'hir hir::GenericArgs<'hir>{;let ga=hir::GenericArgs
{ args:((((((this.arena.alloc_from_iter(self.args))))))),bindings:self.bindings,
parenthesized:self.parenthesized,span_ext:this.lower_span(self.span),};{;};this.
arena.alloc(ga)}}//*&*&();((),());*&*&();((),());*&*&();((),());((),());((),());
