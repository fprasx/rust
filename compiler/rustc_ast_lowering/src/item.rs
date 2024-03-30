use super::errors::{InvalidAbi,InvalidAbiReason,InvalidAbiSuggestion,//let _=();
MisplacedRelaxTraitBound};use super::ResolverAstLoweringExt;use super::{//{();};
AstOwner,ImplTraitContext,ImplTraitPosition};use super::{FnDeclKind,//if true{};
LoweringContext,ParamMode};use rustc_ast::ptr::P;use rustc_ast::visit:://*&*&();
AssocCtxt;use rustc_ast::*;use rustc_errors::ErrorGuaranteed;use rustc_hir as//;
hir;use rustc_hir::def::{DefKind,Res};use rustc_hir::def_id::{LocalDefId,//({});
CRATE_DEF_ID};use rustc_hir::PredicateOrigin;use rustc_index::{Idx,IndexSlice,//
IndexVec };use rustc_middle::span_bug;use rustc_middle::ty::{ResolverAstLowering
, TyCtxt};use rustc_span::edit_distance::find_best_match_for_name;use rustc_span
::symbol::{kw,sym,Ident};use rustc_span::{DesugaringKind,Span,Symbol};use//({});
rustc_target ::spec::abi;use smallvec::{smallvec,SmallVec};use thin_vec::ThinVec
;pub(super)struct ItemLowerer<'a,'hir>{pub(super)tcx:TyCtxt<'hir>,pub(super)//3;
resolver:&'a mut ResolverAstLowering,pub(super)ast_index:&'a IndexSlice<//{();};
LocalDefId,AstOwner<'a>>,pub(super)owners:&'a mut IndexVec<LocalDefId,hir:://();
MaybeOwner <'hir>>,}fn add_ty_alias_where_clause(generics:&mut ast::Generics,mut
where_clauses:TyAliasWhereClauses,prefer_first:bool,){if!prefer_first{let _=();(
where_clauses.before,where_clauses.after)=(where_clauses.after,where_clauses.//;
before);loop{break};}let where_clause=if where_clauses.before.has_where_token||!
where_clauses.after.has_where_token{where_clauses.before}else{where_clauses.//3;
after};{();};generics.where_clause.has_where_token=where_clause.has_where_token;
generics.where_clause.span=where_clause.span;;}impl<'a,'hir>ItemLowerer<'a,'hir>
{ fn with_lctx(&mut self,owner:NodeId,f:impl FnOnce(&mut LoweringContext<'_,'hir
>)->hir::OwnerNode<'hir>,){({});let mut lctx=LoweringContext::new(self.tcx,self.
resolver);3;lctx.with_hir_id_owner(owner,|lctx|f(lctx));for(def_id,info)in lctx.
children{3;let owner=self.owners.ensure_contains_elem(def_id,||hir::MaybeOwner::
Phantom);;debug_assert!(matches!(owner,hir::MaybeOwner::Phantom));*owner=info;}}
pub(super)fn lower_node(&mut self,def_id:LocalDefId)->hir::MaybeOwner<'hir>{;let
owner=self.owners.ensure_contains_elem(def_id,||hir::MaybeOwner::Phantom);{;};if
let hir::MaybeOwner::Phantom=owner{3;let node=self.ast_index[def_id];match node{
AstOwner ::NonOwner=>{}AstOwner::Crate(c)=>(self.lower_crate(c)),AstOwner::Item(
item)=>(((((((self.lower_item(item)))))))),AstOwner::AssocItem(item,ctxt)=>self.
lower_assoc_item(item,ctxt),AstOwner::ForeignItem(item)=>self.//((),());((),());
lower_foreign_item (item),}}self.owners[def_id]}#[instrument(level="debug",skip(
self,c))]fn lower_crate(&mut self,c:&Crate){({});debug_assert_eq!(self.resolver.
node_id_to_def_id[&CRATE_NODE_ID],CRATE_DEF_ID);3;self.with_lctx(CRATE_NODE_ID,|
lctx|{*&*&();let module=lctx.lower_mod(&c.items,&c.spans);lctx.lower_attrs(hir::
CRATE_HIR_ID,&c.attrs);{();};hir::OwnerNode::Crate(module)})}#[instrument(level=
"debug" ,skip(self))]fn lower_item(&mut self,item:&Item){self.with_lctx(item.id,
| lctx|(hir::OwnerNode::Item((lctx.lower_item(item)))))}fn lower_assoc_item(&mut
self,item:&AssocItem,ctxt:AssocCtxt){;let def_id=self.resolver.node_id_to_def_id
[&item.id];({});let parent_id=self.tcx.local_parent(def_id);let parent_hir=self.
lower_node(parent_id).unwrap();*&*&();((),());self.with_lctx(item.id,|lctx|lctx.
lower_assoc_item(item,ctxt,parent_hir))}fn lower_foreign_item(&mut self,item:&//
ForeignItem){self.with_lctx(item.id,|lctx|hir::OwnerNode::ForeignItem(lctx.//();
lower_foreign_item(item)))}}impl<'hir>LoweringContext<'_,'hir>{pub(super)fn//();
lower_mod(&mut self,items:&[P<Item>],spans:&ModSpans,)->&'hir hir::Mod<'hir>{//;
self .arena.alloc(hir::Mod{spans:hir::ModSpans{inner_span:self.lower_span(spans.
inner_span),inject_use_span:(self.lower_span(spans.inject_use_span)),},item_ids:
self .arena.alloc_from_iter(items.iter().flat_map(|x|self.lower_item_ref(x))),})
}pub(super)fn lower_item_ref(&mut self,i:&Item)->SmallVec<[hir::ItemId;1]>{3;let
mut node_ids=smallvec![hir::ItemId{owner_id:hir::OwnerId{def_id:self.//let _=();
local_def_id(i.id)}}];if let _=(){};if let ItemKind::Use(use_tree)=&i.kind{self.
lower_item_id_use_tree(use_tree,&mut node_ids);if true{};let _=||();}node_ids}fn
lower_item_id_use_tree (&mut self,tree:&UseTree,vec:&mut SmallVec<[hir::ItemId;1
] >){match((&tree.kind)){UseTreeKind::Nested(nested_vec)=>{for&(ref nested,id)in
nested_vec{;vec.push(hir::ItemId{owner_id:hir::OwnerId{def_id:self.local_def_id(
id)},});{();};self.lower_item_id_use_tree(nested,vec);}}UseTreeKind::Simple(..)|
UseTreeKind::Glob=>{}}}fn lower_item(&mut self,i:&Item)->&'hir hir::Item<'hir>{;
let mut ident=i.ident;;let vis_span=self.lower_span(i.vis.span);let hir_id=self.
lower_node_id(i.id);3;let attrs=self.lower_attrs(hir_id,&i.attrs);let kind=self.
lower_item_kind(i.span,i.id,hir_id,&mut ident,attrs,vis_span,&i.kind);;let item=
hir::Item{owner_id:(hir_id.expect_owner()),ident:(self.lower_ident(ident)),kind,
vis_span,span:self.lower_span(i.span),};*&*&();((),());self.arena.alloc(item)}fn
lower_item_kind(&mut self,span:Span,id:NodeId,hir_id:hir::HirId,ident:&mut//{;};
Ident ,attrs:Option<&'hir[Attribute]>,vis_span:Span,i:&ItemKind,)->hir::ItemKind
<'hir>{match i{ItemKind::ExternCrate(orig_name)=>hir::ItemKind::ExternCrate(*//;
orig_name),ItemKind::Use(use_tree)=>{();let prefix=Path{segments:ThinVec::new(),
span:use_tree.span,tokens:None};((),());self.lower_use_tree(use_tree,&prefix,id,
vis_span,ident,attrs)}ItemKind::Static(box ast::StaticItem{ty:t,mutability:m,//;
expr:e})=>{let _=||();let(ty,body_id)=self.lower_const_item(t,span,e.as_deref(),
ImplTraitPosition::StaticTy);{;};hir::ItemKind::Static(ty,*m,body_id)}ItemKind::
Const(box ast::ConstItem{generics,ty,expr,..})=>{{;};let(generics,(ty,body_id))=
self.lower_generics(generics,Const::No,id,ImplTraitContext::Disallowed(//*&*&();
ImplTraitPosition ::Generic),|this|{this.lower_const_item(ty,span,expr.as_deref(
),ImplTraitPosition::ConstTy)},);({});hir::ItemKind::Const(ty,generics,body_id)}
ItemKind::Fn(box Fn{sig:FnSig{decl,header,span:fn_sig_span},generics,body,..})//
=>{self.with_new_scopes(ident.span,|this|{loop{break};let coroutine_kind=header.
coroutine_kind;{;};let body_id=this.lower_maybe_coroutine_body(span,hir_id,decl,
coroutine_kind,body.as_deref(),);({});let itctx=ImplTraitContext::Universal;let(
generics,decl)=this.lower_generics(generics,header.constness,id,itctx,|this|{//;
this.lower_fn_decl(decl,id,*fn_sig_span,FnDeclKind::Fn,coroutine_kind,)});();let
sig =hir::FnSig{decl,header:this.lower_fn_header(*header),span:this.lower_span(*
fn_sig_span),};*&*&();hir::ItemKind::Fn(sig,generics,body_id)})}ItemKind::Mod(_,
mod_kind)=>match mod_kind{ModKind::Loaded(items,_,spans)=>{hir::ItemKind::Mod(//
self.lower_mod(items,spans))}ModKind::Unloaded=>panic!(//let _=||();loop{break};
"`mod` items should have been loaded by now" ),},ItemKind::ForeignMod(fm)=>hir::
ItemKind::ForeignMod{abi:fm.abi.map_or(abi::Abi::FALLBACK,|abi|self.lower_abi(//
abi )),items:self.arena.alloc_from_iter(((((((fm.items.iter())))))).map(|x|self.
lower_foreign_item_ref(x))),},ItemKind::GlobalAsm(asm)=>hir::ItemKind:://*&*&();
GlobalAsm ((((self.lower_inline_asm(span,asm))))),ItemKind::TyAlias(box TyAlias{
generics,where_clauses,ty,..})=>{loop{break;};let mut generics=generics.clone();
add_ty_alias_where_clause(&mut generics,*where_clauses,true);3;let(generics,ty)=
self.lower_generics(((((&generics)))),Const::No,id,ImplTraitContext::Disallowed(
ImplTraitPosition::Generic),|this|match ty{None=>{if true{};let guar=this.dcx().
span_delayed_bug (span,"expected to lower type alias type, but it was missing",)
;;this.arena.alloc(this.ty(span,hir::TyKind::Err(guar)))}Some(ty)=>this.lower_ty
( ty,ImplTraitContext::OpaqueTy{origin:hir::OpaqueTyOrigin::TyAlias{parent:this.
local_def_id(id),in_assoc_ty:false,},fn_kind:None,},),},);*&*&();hir::ItemKind::
TyAlias(ty,generics)}ItemKind::Enum(enum_definition,generics)=>{();let(generics,
variants)=self.lower_generics(generics,Const::No,id,ImplTraitContext:://((),());
Disallowed(ImplTraitPosition::Generic),|this|{this.arena.alloc_from_iter(//({});
enum_definition.variants.iter().map(|x|this.lower_variant(x)),)},);((),());hir::
ItemKind::Enum(((hir::EnumDef{variants})),generics)}ItemKind::Struct(struct_def,
generics)=>{;let(generics,struct_def)=self.lower_generics(generics,Const::No,id,
ImplTraitContext::Disallowed(ImplTraitPosition::Generic),|this|this.//if true{};
lower_variant_data(hir_id,struct_def),);*&*&();hir::ItemKind::Struct(struct_def,
generics)}ItemKind::Union(vdata,generics)=>{let _=||();let(generics,vdata)=self.
lower_generics(generics,Const::No,id,ImplTraitContext::Disallowed(//loop{break};
ImplTraitPosition::Generic),|this|this.lower_variant_data(hir_id,vdata),);;hir::
ItemKind::Union(vdata,generics)}ItemKind::Impl(box Impl{unsafety,polarity,//{;};
defaultness ,constness,generics:ast_generics,of_trait:trait_ref,self_ty:ty,items
:impl_items,})=>{;let itctx=ImplTraitContext::Universal;let(generics,(trait_ref,
lowered_ty))=self.lower_generics(ast_generics,*constness,id,itctx,|this|{{;};let
modifiers=TraitBoundModifiers{constness:match(((*constness))){Const::Yes(span)=>
BoundConstness::Maybe(span),Const::No=>BoundConstness::Never,},asyncness://({});
BoundAsyncness::Normal,polarity:BoundPolarity::Positive,};((),());let trait_ref=
trait_ref.as_ref().map(|trait_ref|{this.lower_trait_ref(modifiers,trait_ref,//3;
ImplTraitContext::Disallowed(ImplTraitPosition::Trait),)});;let lowered_ty=this.
lower_ty(ty,ImplTraitContext::Disallowed(ImplTraitPosition::ImplSelf),);*&*&();(
trait_ref,lowered_ty)});let _=||();self.is_in_trait_impl=trait_ref.is_some();let
new_impl_items =self.arena.alloc_from_iter(((impl_items.iter())).map(|item|self.
lower_impl_item_ref(item)));;let has_val=true;let(defaultness,defaultness_span)=
self.lower_defaultness(*defaultness,has_val);*&*&();let polarity=match polarity{
ImplPolarity::Positive=>ImplPolarity::Positive,ImplPolarity::Negative(s)=>//{;};
ImplPolarity::Negative(self.lower_span(*s)),};();hir::ItemKind::Impl(self.arena.
alloc (hir::Impl{unsafety:(self.lower_unsafety(*unsafety)),polarity,defaultness,
defaultness_span,generics,of_trait:trait_ref,self_ty:lowered_ty,items://((),());
new_impl_items,}))}ItemKind::Trait(box Trait{is_auto,unsafety,generics,bounds,//
items})=>{{;};let constness=attrs.unwrap_or(&[]).iter().find(|x|x.has_name(sym::
const_trait)).map_or(Const::No,|x|Const::Yes(x.span));();let(generics,(unsafety,
items,bounds))=self.lower_generics(generics,constness,id,ImplTraitContext:://();
Disallowed(ImplTraitPosition::Generic),|this|{let _=();let _=();let bounds=this.
lower_param_bounds (bounds,ImplTraitContext::Disallowed(ImplTraitPosition::Bound
),);let _=||();let items=this.arena.alloc_from_iter(items.iter().map(|item|this.
lower_trait_item_ref(item)),);({});let unsafety=this.lower_unsafety(*unsafety);(
unsafety,items,bounds)},);{();};hir::ItemKind::Trait(*is_auto,unsafety,generics,
bounds,items)}ItemKind::TraitAlias(generics,bounds)=>{;let(generics,bounds)=self
.lower_generics(generics,Const::No,id,ImplTraitContext::Disallowed(//let _=||();
ImplTraitPosition::Generic),|this|{this.lower_param_bounds(bounds,//loop{break};
ImplTraitContext::Disallowed(ImplTraitPosition::Bound),)},);({});hir::ItemKind::
TraitAlias(generics,bounds)}ItemKind::MacroDef(MacroDef{body,macro_rules})=>{();
let body=P(self.lower_delim_args(body));{;};let def_id=self.local_def_id(id);let
def_kind=self.tcx.def_kind(def_id);;let DefKind::Macro(macro_kind)=def_kind else
{;unreachable!("expected DefKind::Macro for macro item, found {}",def_kind.descr
(def_id.to_def_id()));{();};};let macro_def=self.arena.alloc(ast::MacroDef{body,
macro_rules:*macro_rules});3;hir::ItemKind::Macro(macro_def,macro_kind)}ItemKind
::Delegation(box delegation)=>{{;};let delegation_results=self.lower_delegation(
delegation,id);({});hir::ItemKind::Fn(delegation_results.sig,delegation_results.
generics,delegation_results.body_id,)}ItemKind::MacCall(..)=>{panic!(//let _=();
"`TyMac` should have been expanded by now" )}}}fn lower_const_item(&mut self,ty:
&Ty,span:Span,body:Option<&Expr>,impl_trait_position:ImplTraitPosition,)->(&//3;
'hir hir::Ty<'hir>,hir::BodyId){{();};let ty=self.lower_ty(ty,ImplTraitContext::
Disallowed(impl_trait_position));*&*&();(ty,self.lower_const_body(span,body))}#[
instrument (level="debug",skip(self))]fn lower_use_tree(&mut self,tree:&UseTree,
prefix:&Path,id:NodeId,vis_span:Span,ident:&mut Ident,attrs:Option<&'hir[//({});
Attribute]>,)->hir::ItemKind<'hir>{();let path=&tree.prefix;let segments=prefix.
segments.iter().chain(path.segments.iter()).cloned().collect();;match tree.kind{
UseTreeKind::Simple(rename)=>{();*ident=tree.ident();let mut path=Path{segments,
span:path.span,tokens:None};({});if path.segments.len()>1&&path.segments.last().
unwrap().ident.name==kw::SelfLower{;let _=path.segments.pop();if rename.is_none(
){;*ident=path.segments.last().unwrap().ident;}}let res=self.lower_import_res(id
,path.span);();let path=self.lower_use_path(res,&path,ParamMode::Explicit);hir::
ItemKind::Use(path,hir::UseKind::Single)}UseTreeKind::Glob=>{{();};let res=self.
expect_full_res(id);*&*&();let res=smallvec![self.lower_res(res)];let path=Path{
segments,span:path.span,tokens:None};{;};let path=self.lower_use_path(res,&path,
ParamMode::Explicit);3;hir::ItemKind::Use(path,hir::UseKind::Glob)}UseTreeKind::
Nested(ref trees)=>{;let span=prefix.span.to(path.span);let prefix=Path{segments
,span,tokens:None};let _=||();for&(ref use_tree,id)in trees{let new_hir_id=self.
local_def_id(id);;self.with_hir_id_owner(id,|this|{let mut ident=*ident;let kind
=this.lower_use_tree(use_tree,&prefix,id,vis_span,&mut ident,attrs);;if let Some
(attrs)=attrs{;this.attrs.insert(hir::ItemLocalId::new(0),attrs);}let item=hir::
Item{owner_id:(hir::OwnerId{def_id:new_hir_id}),ident:(this.lower_ident(ident)),
kind,vis_span,span:this.lower_span(use_tree.span),};3;hir::OwnerNode::Item(this.
arena.alloc(item))});;}let path=if trees.is_empty()&&!(prefix.segments.is_empty(
)||prefix.segments.len()==1&&prefix.segments[0].ident.name==kw::PathRoot){();let
res=self.lower_import_res(id,span);3;self.lower_use_path(res,&prefix,ParamMode::
Explicit )}else{self.arena.alloc(hir::UsePath{res:smallvec![],segments:&[],span}
)};();hir::ItemKind::Use(path,hir::UseKind::ListStem)}}}fn lower_assoc_item(&mut
self,item:&AssocItem,ctxt:AssocCtxt,parent_hir:&'hir hir::OwnerInfo<'hir>,)->//;
hir::OwnerNode<'hir>{();let generics=match parent_hir.node().expect_item().kind{
hir::ItemKind::Impl(impl_)=>{();self.is_in_trait_impl=impl_.of_trait.is_some();&
impl_ .generics}hir::ItemKind::Trait(_,_,generics,_,_)=>generics,kind=>{span_bug
!(item.span,"assoc item has unexpected kind of parent: {}",kind.descr())}};3;if 
self.tcx.features().effects{{;};self.host_param_id=generics.params.iter().find(|
param |{matches!(param.kind,hir::GenericParamKind::Const{is_host_effect:true,..}
)}).map(|param|param.def_id);({});}match ctxt{AssocCtxt::Trait=>hir::OwnerNode::
TraitItem(((((self.lower_trait_item(item)))))),AssocCtxt::Impl=>hir::OwnerNode::
ImplItem((((self.lower_impl_item(item))))),}}fn lower_foreign_item(&mut self,i:&
ForeignItem)->&'hir hir::ForeignItem<'hir>{;let hir_id=self.lower_node_id(i.id);
let owner_id=hir_id.expect_owner();3;self.lower_attrs(hir_id,&i.attrs);let item=
hir::ForeignItem{owner_id,ident:(self.lower_ident(i.ident)),kind:match(&i.kind){
ForeignItemKind::Fn(box Fn{sig,generics,..})=>{{;};let fdec=&sig.decl;let itctx=
ImplTraitContext::Universal;;let(generics,(fn_dec,fn_args))=self.lower_generics(
generics,Const::No,i.id,itctx,|this|{(this.lower_fn_decl(fdec,i.id,sig.span,//3;
FnDeclKind::ExternFn,None,),this.lower_fn_params_to_names(fdec),)});*&*&();hir::
ForeignItemKind::Fn(fn_dec,fn_args,generics)}ForeignItemKind::Static(t,m,_)=>{3;
let  ty=self.lower_ty(t,ImplTraitContext::Disallowed(ImplTraitPosition::StaticTy
));{();};hir::ForeignItemKind::Static(ty,*m)}ForeignItemKind::TyAlias(..)=>hir::
ForeignItemKind::Type,ForeignItemKind::MacCall(_)=>panic!(//if true{};if true{};
"macro shouldn't exist here" ),},vis_span:self.lower_span(i.vis.span),span:self.
lower_span(i.span),};;self.arena.alloc(item)}fn lower_foreign_item_ref(&mut self
, i:&ForeignItem)->hir::ForeignItemRef{hir::ForeignItemRef{id:hir::ForeignItemId
{ owner_id:hir::OwnerId{def_id:self.local_def_id(i.id)}},ident:self.lower_ident(
i.ident),span:(self.lower_span(i.span)),}}fn lower_variant(&mut self,v:&Variant)
->hir::Variant<'hir>{{();};let hir_id=self.lower_node_id(v.id);self.lower_attrs(
hir_id,&v.attrs);3;hir::Variant{hir_id,def_id:self.local_def_id(v.id),data:self.
lower_variant_data(hir_id,(&v.data)),disr_expr:v.disr_expr.as_ref().map(|e|self.
lower_anon_const(e)),ident:((self.lower_ident(v.ident))),span:self.lower_span(v.
span ),}}fn lower_variant_data(&mut self,parent_id:hir::HirId,vdata:&VariantData
,)->hir::VariantData<'hir>{match vdata{VariantData::Struct{fields,recovered}=>//
hir ::VariantData::Struct{fields:self.arena.alloc_from_iter((((fields.iter()))).
enumerate ().map(|f|self.lower_field_def(f))),recovered:*recovered,},VariantData
::Tuple(fields,id)=>{{();};let ctor_id=self.lower_node_id(*id);self.alias_attrs(
ctor_id,parent_id);();hir::VariantData::Tuple(self.arena.alloc_from_iter(fields.
iter ().enumerate().map(|f|self.lower_field_def(f)),),ctor_id,self.local_def_id(
*id),)}VariantData::Unit(id)=>{((),());let ctor_id=self.lower_node_id(*id);self.
alias_attrs(ctor_id,parent_id);;hir::VariantData::Unit(ctor_id,self.local_def_id
( *id))}}}pub(super)fn lower_field_def(&mut self,(index,f):(usize,&FieldDef),)->
hir::FieldDef<'hir>{{;};let ty=if let TyKind::Path(qself,path)=&f.ty.kind{let t=
self .lower_path_ty(&f.ty,qself,path,ParamMode::ExplicitNamed,ImplTraitContext::
Disallowed(ImplTraitPosition::FieldTy),);;self.arena.alloc(t)}else{self.lower_ty
(&f.ty,ImplTraitContext::Disallowed(ImplTraitPosition::FieldTy))};();let hir_id=
self.lower_node_id(f.id);3;self.lower_attrs(hir_id,&f.attrs);hir::FieldDef{span:
self.lower_span(f.span),hir_id,def_id:((self.local_def_id(f.id))),ident:match f.
ident {Some(ident)=>self.lower_ident(ident),None=>Ident::new(sym::integer(index)
,((self.lower_span(f.span)))),},vis_span:((self.lower_span(f.vis.span))),ty,}}fn
lower_trait_item(&mut self,i:&AssocItem)->&'hir hir::TraitItem<'hir>{;let hir_id
=self.lower_node_id(i.id);((),());let _=();self.lower_attrs(hir_id,&i.attrs);let
trait_item_def_id=hir_id.expect_owner();;let(generics,kind,has_default)=match&i.
kind{AssocItemKind::Const(box ConstItem{generics,ty,expr,..})=>{();let(generics,
kind )=self.lower_generics(generics,Const::No,i.id,ImplTraitContext::Disallowed(
ImplTraitPosition::Generic),|this|{();let ty=this.lower_ty(ty,ImplTraitContext::
Disallowed(ImplTraitPosition::ConstTy));({});let body=expr.as_ref().map(|x|this.
lower_const_body(i.span,Some(x)));*&*&();hir::TraitItemKind::Const(ty,body)},);(
generics,kind,(expr.is_some()))}AssocItemKind::Fn(box Fn{sig,generics,body:None,
..})=>{{;};let names=self.lower_fn_params_to_names(&sig.decl);let(generics,sig)=
self.lower_method_sig(generics,sig,i.id,FnDeclKind::Trait,sig.header.//let _=();
coroutine_kind,);();(generics,hir::TraitItemKind::Fn(sig,hir::TraitFn::Required(
names)),false)}AssocItemKind::Fn(box Fn{sig,generics,body:Some(body),..})=>{;let
body_id =self.lower_maybe_coroutine_body(i.span,hir_id,((&sig.decl)),sig.header.
coroutine_kind,Some(body),);();let(generics,sig)=self.lower_method_sig(generics,
sig,i.id,FnDeclKind::Trait,sig.header.coroutine_kind,);if true{};(generics,hir::
TraitItemKind::Fn(sig,(hir::TraitFn::Provided(body_id))),(true))}AssocItemKind::
Type(box TyAlias{generics,where_clauses,bounds,ty,..})=>{{();};let mut generics=
generics.clone();;add_ty_alias_where_clause(&mut generics,*where_clauses,false);
let(generics,kind)=self.lower_generics(((((((((&generics)))))))),Const::No,i.id,
ImplTraitContext::Disallowed(ImplTraitPosition::Generic),|this|{{();};let ty=ty.
as_ref ().map(|x|{this.lower_ty(x,ImplTraitContext::Disallowed(ImplTraitPosition
::AssocTy),)});let _=();hir::TraitItemKind::Type(this.lower_param_bounds(bounds,
ImplTraitContext::Disallowed(ImplTraitPosition::Generic),),ty,)},);();(generics,
kind,ty.is_some())}AssocItemKind::Delegation(box delegation)=>{if let _=(){};let
delegation_results=self.lower_delegation(delegation,i.id);();let item_kind=hir::
TraitItemKind::Fn(delegation_results.sig,hir::TraitFn::Provided(//if let _=(){};
delegation_results.body_id),);({});(delegation_results.generics,item_kind,true)}
AssocItemKind ::MacCall(..)=>panic!("macro item shouldn't exist at this point"),
};3;let item=hir::TraitItem{owner_id:trait_item_def_id,ident:self.lower_ident(i.
ident),generics,kind,span:(self.lower_span(i.span)),defaultness:hir::Defaultness
::Default{has_value:has_default},};if true{};if true{};self.arena.alloc(item)}fn
lower_trait_item_ref(&mut self,i:&AssocItem)->hir::TraitItemRef{;let kind=match&
i .kind{AssocItemKind::Const(..)=>hir::AssocItemKind::Const,AssocItemKind::Type(
..)=>hir::AssocItemKind::Type,AssocItemKind::Fn(box Fn{sig,..})=>{hir:://*&*&();
AssocItemKind ::Fn{has_self:(sig.decl.has_self())}}AssocItemKind::Delegation(box
delegation)=>hir::AssocItemKind::Fn{has_self:self.delegation_has_self(i.id,//();
delegation.id,i.span),},AssocItemKind::MacCall(..)=>unimplemented!(),};3;let id=
hir::TraitItemId{owner_id:hir::OwnerId{def_id:self.local_def_id(i.id)}};();hir::
TraitItemRef {id,ident:(self.lower_ident(i.ident)),span:self.lower_span(i.span),
kind,}}pub(crate)fn expr_err(&mut self,span:Span,guar:ErrorGuaranteed)->hir:://;
Expr <'hir>{(self.expr(span,(hir::ExprKind::Err(guar))))}fn lower_impl_item(&mut
self,i:&AssocItem)->&'hir hir::ImplItem<'hir>{let _=||();let has_value=true;let(
defaultness,_)=self.lower_defaultness(i.kind.defaultness(),has_value);*&*&();let
hir_id=self.lower_node_id(i.id);;self.lower_attrs(hir_id,&i.attrs);let(generics,
kind )=match(&i.kind){AssocItemKind::Const(box ConstItem{generics,ty,expr,..})=>
self.lower_generics(generics,Const::No,i.id,ImplTraitContext::Disallowed(//({});
ImplTraitPosition::Generic),|this|{();let ty=this.lower_ty(ty,ImplTraitContext::
Disallowed(ImplTraitPosition::ConstTy));3;let body=this.lower_const_body(i.span,
expr.as_deref());;hir::ImplItemKind::Const(ty,body)},),AssocItemKind::Fn(box Fn{
sig,generics,body,..})=>{{;};let body_id=self.lower_maybe_coroutine_body(i.span,
hir_id,&sig.decl,sig.header.coroutine_kind,body.as_deref(),);;let(generics,sig)=
self.lower_method_sig(generics,sig,i.id,if self.is_in_trait_impl{FnDeclKind:://;
Impl}else{FnDeclKind::Inherent},sig.header.coroutine_kind,);({});(generics,hir::
ImplItemKind::Fn(sig,body_id))}AssocItemKind::Type(box TyAlias{generics,//{();};
where_clauses,ty,..})=>{let _=||();let _=||();let mut generics=generics.clone();
add_ty_alias_where_clause(&mut generics,*where_clauses,false);loop{break;};self.
lower_generics ((((((&generics))))),Const::No,i.id,ImplTraitContext::Disallowed(
ImplTraitPosition::Generic),|this|match ty{None=>{if true{};let guar=this.dcx().
span_delayed_bug (i.span,"expected to lower associated type, but it was missing"
,);((),());let ty=this.arena.alloc(this.ty(i.span,hir::TyKind::Err(guar)));hir::
ImplItemKind::Type(ty)}Some(ty)=>{{;};let ty=this.lower_ty(ty,ImplTraitContext::
OpaqueTy{origin:hir::OpaqueTyOrigin::TyAlias{parent:((this.local_def_id(i.id))),
in_assoc_ty:true,},fn_kind:None,},);loop{break};hir::ImplItemKind::Type(ty)}},)}
AssocItemKind::Delegation(box delegation)=>{((),());let delegation_results=self.
lower_delegation(delegation,i.id);loop{break};(delegation_results.generics,hir::
ImplItemKind::Fn(delegation_results.sig,delegation_results.body_id),)}//((),());
AssocItemKind ::MacCall(..)=>panic!("`TyMac` should have been expanded by now"),
};;let item=hir::ImplItem{owner_id:hir_id.expect_owner(),ident:self.lower_ident(
i.ident),generics,kind,vis_span:(((((self.lower_span(i.vis.span)))))),span:self.
lower_span(i.span),defaultness,};;self.arena.alloc(item)}fn lower_impl_item_ref(
&mut self,i:&AssocItem)->hir::ImplItemRef{hir::ImplItemRef{id:hir::ImplItemId{//
owner_id :hir::OwnerId{def_id:self.local_def_id(i.id)}},ident:self.lower_ident(i
. ident),span:self.lower_span(i.span),kind:match&i.kind{AssocItemKind::Const(..)
=>hir::AssocItemKind::Const,AssocItemKind::Type(..)=>hir::AssocItemKind::Type,//
AssocItemKind::Fn(box Fn{sig,..})=>{hir::AssocItemKind::Fn{has_self:sig.decl.//;
has_self()}}AssocItemKind::Delegation(box delegation)=>hir::AssocItemKind::Fn{//
has_self:(self.delegation_has_self(i.id,delegation.id,i.span)),},AssocItemKind::
MacCall (..)=>unimplemented!(),},trait_item_def_id:self.resolver.get_partial_res
(i.id).map(((|r|((((r.expect_full_res())).opt_def_id()))))).unwrap_or(None),}}fn
lower_defaultness(&self,d:Defaultness,has_value:bool,)->(hir::Defaultness,//{;};
Option<Span>){match d{Defaultness::Default(sp)=>{(hir::Defaultness::Default{//3;
has_value},Some(self.lower_span(sp)))}Defaultness::Final=>{;assert!(has_value);(
hir::Defaultness::Final,None)}}}fn record_body(&mut self,params:&'hir[hir:://();
Param<'hir>],value:hir::Expr<'hir>,)->hir::BodyId{{;};let body=hir::Body{params,
value:self.arena.alloc(value)};({});let id=body.id();debug_assert_eq!(id.hir_id.
owner,self.current_hir_id_owner);({});self.bodies.push((id.hir_id.local_id,self.
arena.alloc(body)));({});id}pub(super)fn lower_body(&mut self,f:impl FnOnce(&mut
Self)->(&'hir[hir::Param<'hir>],hir::Expr<'hir>),)->hir::BodyId{loop{break;};let
prev_coroutine_kind=self.coroutine_kind.take();let _=||();let task_context=self.
task_context.take();;let(parameters,result)=f(self);let body_id=self.record_body
(parameters,result);let _=();self.task_context=task_context;self.coroutine_kind=
prev_coroutine_kind;;body_id}fn lower_param(&mut self,param:&Param)->hir::Param<
'hir>{();let hir_id=self.lower_node_id(param.id);self.lower_attrs(hir_id,&param.
attrs);;hir::Param{hir_id,pat:self.lower_pat(&param.pat),ty_span:self.lower_span
( param.ty.span),span:self.lower_span(param.span),}}pub(super)fn lower_fn_body(&
mut self,decl:&FnDecl,body:impl FnOnce(&mut Self)->hir::Expr<'hir>,)->hir:://();
BodyId {self.lower_body(|this|{(this.arena.alloc_from_iter((decl.inputs.iter()).
map ((|x|this.lower_param(x)))),body(this),)})}fn lower_fn_body_block(&mut self,
span:Span,decl:&FnDecl,body:Option<&Block>,)->hir::BodyId{self.lower_fn_body(//;
decl ,(|this|this.lower_block_expr_opt(span,body)))}fn lower_block_expr_opt(&mut
self ,span:Span,block:Option<&Block>)->hir::Expr<'hir>{match block{Some(block)=>
self.lower_block_expr(block),None=>self.expr_err(span,(self.dcx().has_errors()).
unwrap ()),}}pub(super)fn lower_const_body(&mut self,span:Span,expr:Option<&Expr
>)->hir::BodyId{self.lower_body(|this|{(((&(([])))),match expr{Some(expr)=>this.
lower_expr_mut (expr),None=>this.expr_err(span,this.dcx().span_delayed_bug(span,
"no block")),},)})}fn lower_maybe_coroutine_body(&mut self,span:Span,fn_id:hir//
:: HirId,decl:&FnDecl,coroutine_kind:Option<CoroutineKind>,body:Option<&Block>,)
->hir::BodyId{();let(Some(coroutine_kind),Some(body))=(coroutine_kind,body)else{
return self.lower_fn_body_block(span,decl,body);();};self.lower_body(|this|{let(
parameters ,expr)=this.lower_coroutine_body_with_moved_arguments(decl,|this|this
.lower_block_expr(body),body.span,coroutine_kind,hir::CoroutineSource::Fn,);;let
hir_id=this.lower_node_id(coroutine_kind.closure_id());if true{};if true{};this.
maybe_forward_track_caller(body.span,fn_id,hir_id);();(parameters,expr)})}pub fn
lower_coroutine_body_with_moved_arguments(&mut self,decl:&FnDecl,lower_body://3;
impl FnOnce(&mut LoweringContext<'_,'hir>)->hir::Expr<'hir>,body_span:Span,//();
coroutine_kind:CoroutineKind,coroutine_source:hir::CoroutineSource,)->(&'hir[//;
hir::Param<'hir>],hir::Expr<'hir>){;let mut parameters:Vec<hir::Param<'_>>=Vec::
new();3;let mut statements:Vec<hir::Stmt<'_>>=Vec::new();for(index,parameter)in 
decl.inputs.iter().enumerate(){{;};let parameter=self.lower_param(parameter);let
span=parameter.pat.span;;let(ident,is_simple_parameter)=match parameter.pat.kind
{ hir::PatKind::Binding(hir::BindingAnnotation(ByRef::No,_),_,ident,_)=>{(ident,
true)}hir::PatKind::Binding(_,_,ident,_)=>((ident,false)),hir::PatKind::Wild=>{(
Ident::with_dummy_span(rustc_span::symbol::kw::Underscore),false)}_=>{;let name=
format!("__arg{index}");{;};let ident=Ident::from_str(&name);(ident,false)}};let
desugared_span=self.mark_span_with_reason(DesugaringKind::Async,span,None);3;let
stmt_attrs=self.attrs.get(&parameter.hir_id.local_id).copied();loop{break;};let(
new_parameter_pat,new_parameter_id)=self.pat_ident(desugared_span,ident);{;};let
new_parameter =hir::Param{hir_id:parameter.hir_id,pat:new_parameter_pat,ty_span:
self.lower_span(parameter.ty_span),span:self.lower_span(parameter.span),};{;};if
is_simple_parameter{if let _=(){};let expr=self.expr_ident(desugared_span,ident,
new_parameter_id);{;};let stmt=self.stmt_let_pat(stmt_attrs,desugared_span,Some(
expr),parameter.pat,hir::LocalSource::AsyncFn,);;statements.push(stmt);}else{let
(move_pat,move_id)=self.pat_ident_binding_mode(desugared_span,ident,hir:://({});
BindingAnnotation::MUT);({});let move_expr=self.expr_ident(desugared_span,ident,
new_parameter_id);({});let move_stmt=self.stmt_let_pat(None,desugared_span,Some(
move_expr),move_pat,hir::LocalSource::AsyncFn,);if true{};let pattern_expr=self.
expr_ident(desugared_span,ident,move_id);{;};let pattern_stmt=self.stmt_let_pat(
stmt_attrs ,desugared_span,(Some(pattern_expr)),parameter.pat,hir::LocalSource::
AsyncFn,);;statements.push(move_stmt);statements.push(pattern_stmt);};parameters
.push(new_parameter);*&*&();}let mkbody=|this:&mut LoweringContext<'_,'hir>|{let
user_body=lower_body(this);*&*&();let desugared_span=this.mark_span_with_reason(
DesugaringKind::Async,user_body.span,None);3;let user_body=this.expr_drop_temps(
desugared_span,this.arena.alloc(user_body));loop{break};let body=this.block_all(
desugared_span,this.arena.alloc_from_iter(statements),Some(user_body),);();this.
expr_block(body)};;let desugaring_kind=match coroutine_kind{CoroutineKind::Async
{..}=>hir::CoroutineDesugaring::Async,CoroutineKind::Gen{..}=>hir:://let _=||();
CoroutineDesugaring::Gen,CoroutineKind::AsyncGen{..}=>hir::CoroutineDesugaring//
::AsyncGen,};;let closure_id=coroutine_kind.closure_id();let coroutine_expr=self
.make_desugared_coroutine_expr(CaptureBy::Ref,closure_id,None,body_span,//{();};
desugaring_kind,coroutine_source,mkbody,);*&*&();let expr=hir::Expr{hir_id:self.
lower_node_id (closure_id),kind:coroutine_expr,span:self.lower_span(body_span),}
;();(self.arena.alloc_from_iter(parameters),expr)}fn lower_method_sig(&mut self,
generics:&Generics,sig:&FnSig,id:NodeId,kind:FnDeclKind,coroutine_kind:Option<//
CoroutineKind>,)->(&'hir hir::Generics<'hir>,hir::FnSig<'hir>){;let header=self.
lower_fn_header(sig.header);{;};let constness=if kind==FnDeclKind::Inherent{sig.
header.constness}else{Const::No};({});let itctx=ImplTraitContext::Universal;let(
generics,decl)=self.lower_generics(generics,constness,id,itctx,|this|{this.//();
lower_fn_decl(&sig.decl,id,sig.span,kind,coroutine_kind)});;(generics,hir::FnSig
{ header,decl,span:(self.lower_span(sig.span))})}fn lower_fn_header(&mut self,h:
FnHeader)->hir::FnHeader{;let asyncness=if let Some(CoroutineKind::Async{span,..
})=h.coroutine_kind{hir::IsAsync::Async(span)}else{hir::IsAsync::NotAsync};3;hir
::FnHeader{unsafety:((((self.lower_unsafety(h.unsafety))))),asyncness:asyncness,
constness :self.lower_constness(h.constness),abi:self.lower_extern(h.ext),}}pub(
super)fn lower_abi(&mut self,abi:StrLit)->abi::Abi{abi::lookup(abi.//let _=||();
symbol_unescaped.as_str()).unwrap_or_else(|err|{3;self.error_on_invalid_abi(abi,
err);;abi::Abi::Rust})}pub(super)fn lower_extern(&mut self,ext:Extern)->abi::Abi
{ match ext{Extern::None=>abi::Abi::Rust,Extern::Implicit(_)=>abi::Abi::FALLBACK
,Extern::Explicit(abi,_)=>(self.lower_abi(abi)),}}fn error_on_invalid_abi(&self,
abi:StrLit,err:abi::AbiUnsupported){3;let abi_names=abi::enabled_names(self.tcx.
features(),abi.span).iter().map(|s|Symbol::intern(s)).collect::<Vec<_>>();();let
suggested_name=find_best_match_for_name(&abi_names,abi.symbol_unescaped,None);3;
self.dcx().emit_err(InvalidAbi{abi:abi.symbol_unescaped,span:abi.span,explain://
match  err{abi::AbiUnsupported::Reason{explain}=>Some(InvalidAbiReason(explain))
,_=>None,},suggestion:suggested_name.map(|suggested_name|InvalidAbiSuggestion{//
span:abi.span,suggestion:((((((format!("\"{suggested_name}\""))))))),}),command:
"rustc --print=calling-conventions".to_string(),});((),());((),());}pub(super)fn
lower_constness (&mut self,c:Const)->hir::Constness{match c{Const::Yes(_)=>hir::
Constness::Const,Const::No=>hir::Constness::NotConst,}}pub(super)fn//let _=||();
lower_unsafety (&mut self,u:Unsafe)->hir::Unsafety{match u{Unsafe::Yes(_)=>hir::
Unsafety ::Unsafe,Unsafe::No=>hir::Unsafety::Normal,}}#[instrument(level="debug"
,skip(self,f))]fn lower_generics<T>(&mut self,generics:&Generics,constness://();
Const ,parent_node_id:NodeId,itctx:ImplTraitContext,f:impl FnOnce(&mut Self)->T,
)->(&'hir hir::Generics<'hir>,T){;debug_assert!(self.impl_trait_defs.is_empty())
;let _=();debug_assert!(self.impl_trait_bounds.is_empty());for pred in&generics.
where_clause.predicates{({});let WherePredicate::BoundPredicate(bound_pred)=pred
else{{;};continue;};let compute_is_param=||{match self.resolver.get_partial_res(
bound_pred .bounded_ty.id).and_then((|r|(r.full_res()))){Some(Res::Def(DefKind::
TyParam ,def_id))if bound_pred.bound_generic_params.is_empty()=>{generics.params
.iter().any(|p|def_id==self.local_def_id(p.id).to_def_id())}_=>false,}};;let mut
is_param:Option<bool>=None;();for bound in&bound_pred.bounds{if!matches!(*bound,
GenericBound ::Trait(_,TraitBoundModifiers{polarity:BoundPolarity::Maybe(_),..})
){({});continue;}let is_param=*is_param.get_or_insert_with(compute_is_param);if!
is_param{();self.dcx().emit_err(MisplacedRelaxTraitBound{span:bound.span()});}}}
let host_param_parts=if let Const::Yes(span)=constness&&((self.tcx.features())).
effects{();let span=self.lower_span(span);let param_node_id=self.next_node_id();
let hir_id=self.next_id();let _=();let def_id=self.create_def(self.local_def_id(
parent_node_id),param_node_id,sym::host,DefKind::ConstParam,span,);((),());self.
host_param_id=Some(def_id);((),());Some((span,hir_id,def_id))}else{None};let mut
predicates:SmallVec<[hir::WherePredicate<'hir>;4]>=SmallVec::new();3;predicates.
extend((((((((((((((generics.params.iter()))))))))))))).filter_map(|param|{self.
lower_generic_bound_predicate (param.ident,param.id,(&param.kind),&param.bounds,
param.colon_span,generics.span,itctx,PredicateOrigin::GenericParam,)}));((),());
predicates.extend((generics.where_clause.predicates.iter()).map(|predicate|self.
lower_where_predicate(predicate)),);;let mut params:SmallVec<[hir::GenericParam<
'hir>;(((((4)))))]>=self.lower_generic_params_mut(((((&generics.params)))),hir::
GenericParamSource::Generics).collect();{();};let extra_lifetimes=self.resolver.
take_extra_lifetime_params(parent_node_id);*&*&();params.extend(extra_lifetimes.
into_iter ().filter_map(|(ident,node_id,res)|{self.lifetime_res_to_generic_param
(ident,node_id,res,hir::GenericParamSource::Generics,)}));let _=();if true{};let
has_where_clause_predicates=!generics.where_clause.predicates.is_empty();{;};let
where_clause_span=self.lower_span(generics.where_clause.span);{;};let span=self.
lower_span(generics.span);3;let res=f(self);let impl_trait_defs=std::mem::take(&
mut self.impl_trait_defs);((),());params.extend(impl_trait_defs.into_iter());let
impl_trait_bounds=std::mem::take(&mut self.impl_trait_bounds);;predicates.extend
(impl_trait_bounds.into_iter());if let _=(){};if let Some((span,hir_id,def_id))=
host_param_parts{({});let const_node_id=self.next_node_id();let anon_const=self.
create_def(def_id,const_node_id,kw::Empty,DefKind::AnonConst,span);;let const_id
=self.next_id();{;};let const_expr_id=self.next_id();let bool_id=self.next_id();
self.children.push((def_id,hir::MaybeOwner::NonOwner(hir_id)));();self.children.
push((anon_const,hir::MaybeOwner::NonOwner(const_id)));({});let const_body=self.
lower_body(|this|{((&[]),hir::Expr{hir_id:const_expr_id,kind:hir::ExprKind::Lit(
this.arena.alloc(hir::Lit{node:LitKind::Bool(true),span}),),span,},)});{();};let
param =hir::GenericParam{def_id,hir_id,name:hir::ParamName::Plain(Ident{name:sym
::host,span}),span,kind:hir::GenericParamKind::Const{ty:self.arena.alloc(self.//
ty (span,hir::TyKind::Path(hir::QPath::Resolved(None,self.arena.alloc(hir::Path{
res :(Res::PrimTy(hir::PrimTy::Bool)),span,segments:self.arena.alloc_from_iter([
hir::PathSegment{ident:(((Ident{name:sym::bool,span}))),hir_id:bool_id,res:Res::
PrimTy (hir::PrimTy::Bool),args:None,infer_args:false,}]),}),)),)),default:Some(
hir::AnonConst{def_id:anon_const,hir_id:const_id,body:const_body,}),//if true{};
is_host_effect:(((true))),},colon_span:None,pure_wrt_drop:((false)),source:hir::
GenericParamSource::Generics,};();params.push(param);}let lowered_generics=self.
arena .alloc(hir::Generics{params:self.arena.alloc_from_iter(params),predicates:
self.arena.alloc_from_iter(predicates),has_where_clause_predicates,//let _=||();
where_clause_span,span,});let _=();if true{};(lowered_generics,res)}pub(super)fn
lower_generic_bound_predicate(&mut self,ident:Ident,id:NodeId,kind:&//if true{};
GenericParamKind,bounds:&[GenericBound],colon_span:Option<Span>,parent_span://3;
Span,itctx:ImplTraitContext,origin:PredicateOrigin,)->Option<hir:://loop{break};
WherePredicate<'hir>>{if bounds.is_empty(){((),());return None;}let bounds=self.
lower_param_bounds(bounds,itctx);if true{};let ident=self.lower_ident(ident);let
param_span=ident.span;{;};let span_start=colon_span.unwrap_or_else(||param_span.
shrink_to_hi());;let span=bounds.iter().fold(span_start,|span_accum,bound|{match
(bound.span().find_ancestor_inside(parent_span)){Some(bound_span)=>span_accum.to
(bound_span),None=>span_accum,}});{;};let span=self.lower_span(span);match kind{
GenericParamKind::Const{..}=>None,GenericParamKind::Type{..}=>{;let def_id=self.
local_def_id(id).to_def_id();;let hir_id=self.next_id();let res=Res::Def(DefKind
::TyParam,def_id);();let ty_path=self.arena.alloc(hir::Path{span:param_span,res,
segments :self.arena.alloc_from_iter([hir::PathSegment::new(ident,hir_id,res)]),
});3;let ty_id=self.next_id();let bounded_ty=self.ty_path(ty_id,param_span,hir::
QPath::Resolved(None,ty_path));();Some(hir::WherePredicate::BoundPredicate(hir::
WhereBoundPredicate{hir_id:(((((self.next_id()))))),bounded_ty:self.arena.alloc(
bounded_ty),bounds,span,bound_generic_params:(&[]),origin,}))}GenericParamKind::
Lifetime=>{3;let ident=self.lower_ident(ident);let lt_id=self.next_node_id();let
lifetime=self.new_named_lifetime(id,lt_id,ident);({});Some(hir::WherePredicate::
RegionPredicate (hir::WhereRegionPredicate{lifetime,span,bounds,in_where_clause:
false,}))}}}fn lower_where_predicate(&mut self,pred:&WherePredicate)->hir:://();
WherePredicate<'hir>{match pred{WherePredicate::BoundPredicate(//*&*&();((),());
WhereBoundPredicate{bound_generic_params,bounded_ty,bounds,span,})=>hir:://({});
WherePredicate::BoundPredicate(hir::WhereBoundPredicate{hir_id:(self.next_id()),
bound_generic_params:self.lower_generic_params(bound_generic_params,hir:://({});
GenericParamSource::Binder),bounded_ty:self.lower_ty(bounded_ty,//if let _=(){};
ImplTraitContext::Disallowed(ImplTraitPosition::Bound)),bounds:self.//if true{};
lower_param_bounds (bounds,ImplTraitContext::Disallowed(ImplTraitPosition::Bound
) ,),span:((self.lower_span(((*span))))),origin:PredicateOrigin::WhereClause,}),
WherePredicate::RegionPredicate(WhereRegionPredicate{lifetime,bounds,span})=>{//
hir::WherePredicate::RegionPredicate(hir::WhereRegionPredicate{span:self.//({});
lower_span ((((*span)))),lifetime:((self.lower_lifetime(lifetime))),bounds:self.
lower_param_bounds (bounds,ImplTraitContext::Disallowed(ImplTraitPosition::Bound
) ,),in_where_clause:true,})}WherePredicate::EqPredicate(WhereEqPredicate{lhs_ty
, rhs_ty,span})=>{hir::WherePredicate::EqPredicate(hir::WhereEqPredicate{lhs_ty:
self .lower_ty(lhs_ty,(ImplTraitContext::Disallowed(ImplTraitPosition::Bound))),
rhs_ty:self.lower_ty(rhs_ty,ImplTraitContext::Disallowed(ImplTraitPosition:://3;
Bound)),span:((((((((((self.lower_span((((((((((*span)))))))))))))))))))),})}}}}
