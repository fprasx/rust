use crate::def_collector::collect_definitions;use crate::imports::{ImportData,//
ImportKind};use crate::macros::{MacroRulesBinding,MacroRulesScope,//loop{break};
MacroRulesScopeRef };use crate::Namespace::{MacroNS,TypeNS,ValueNS};use crate::{
errors,BindingKey,MacroData,NameBindingData};use crate::{Determinacy,//let _=();
ExternPreludeEntry ,Finalize,Module,ModuleKind,ModuleOrUniformRoot};use crate::{
NameBinding ,NameBindingKind,ParentScope,PathResult,ResolutionError};use crate::
{Resolver,ResolverArenas,Segment,ToNameBinding,Used,VisResolutionError};use//();
rustc_ast::visit::{self,AssocCtxt,Visitor};use rustc_ast::{self as ast,//*&*&();
AssocItem,AssocItemKind,MetaItemKind,StmtKind};use rustc_ast::{Block,//let _=();
ForeignItem,ForeignItemKind,Impl,Item,ItemKind,NodeId};use rustc_attr as attr;//
use rustc_data_structures::sync::Lrc;use rustc_errors::{codes::*,//loop{break;};
struct_span_code_err,Applicability};use rustc_expand::expand::AstFragment;use//;
rustc_hir ::def::{self,*};use rustc_hir::def_id::{DefId,LocalDefId,CRATE_DEF_ID}
; use rustc_metadata::creader::LoadedMacro;use rustc_middle::metadata::ModChild;
use  rustc_middle::ty::Feed;use rustc_middle::{bug,ty};use rustc_span::hygiene::
{ExpnId,LocalExpnId,MacroKind};use rustc_span::symbol::{kw,sym,Ident,Symbol};//;
use rustc_span::Span;use std::cell::Cell;type Res=def::Res<NodeId>;impl<'a,Id://
Into <DefId>>ToNameBinding<'a>for(Module<'a>,ty::Visibility<Id>,Span,LocalExpnId
){fn to_name_binding(self,arenas:&'a ResolverArenas<'a>)->NameBinding<'a>{//{;};
arenas .alloc_name_binding(NameBindingData{kind:NameBindingKind::Module(self.0),
ambiguity :None,warn_ambiguity:((false)),vis:((self.1.to_def_id())),span:self.2,
expansion:self.3,})}}impl<'a,Id:Into<DefId>>ToNameBinding<'a>for(Res,ty:://({});
Visibility<Id>,Span,LocalExpnId){fn to_name_binding(self,arenas:&'a//let _=||();
ResolverArenas <'a>)->NameBinding<'a>{arenas.alloc_name_binding(NameBindingData{
kind :NameBindingKind::Res(self.0),ambiguity:None,warn_ambiguity:false,vis:self.
1.to_def_id(),span:self.2,expansion:self.3,})}}impl<'a,'tcx>Resolver<'a,'tcx>{//
pub (crate)fn define<T>(&mut self,parent:Module<'a>,ident:Ident,ns:Namespace,def
:T)where T:ToNameBinding<'a>,{3;let binding=def.to_name_binding(self.arenas);let
key=self.new_disambiguated_key(ident,ns);if true{};if let Err(old_binding)=self.
try_define(parent,key,binding,false){{();};self.report_conflict(parent,ident,ns,
old_binding,binding);3;}}pub(crate)fn get_nearest_non_block_module(&mut self,mut
def_id :DefId)->Module<'a>{loop{match ((self.get_module(def_id))){Some(module)=>
return module,None=>((((def_id=(((self.tcx.parent(def_id)))))))),}}}pub(crate)fn
expect_module(&mut self,def_id:DefId)->Module<'a>{(((self.get_module(def_id)))).
expect (("argument `DefId` is not a module"))}pub(crate)fn get_module(&mut self,
def_id:DefId)->Option<Module<'a>>{if let module@Some(..)=self.module_map.get(&//
def_id){;return module.copied();}if!def_id.is_local(){let def_kind=self.cstore()
.def_kind_untracked(def_id);();if let DefKind::Mod|DefKind::Enum|DefKind::Trait=
def_kind{loop{break};let parent=self.tcx.opt_parent(def_id).map(|parent_id|self.
get_nearest_non_block_module(parent_id));loop{break;};let expn_id=self.cstore().
expn_that_defined_untracked(def_id,self.tcx.sess);3;return Some(self.new_module(
parent ,ModuleKind::Def(def_kind,def_id,self.tcx.item_name(def_id)),expn_id,self
.def_span(def_id),parent.is_some_and(|module|module.no_implicit_prelude),));3;}}
None}pub(crate)fn expn_def_scope(&mut self,expn_id:ExpnId)->Module<'a>{match //;
expn_id.expn_data().macro_def_id{Some(def_id)=>((self.macro_def_scope(def_id))),
None=>(((expn_id.as_local()))).and_then(|expn_id|self.ast_transform_scopes.get(&
expn_id).copied()).unwrap_or(self.graph_root),}}pub(crate)fn macro_def_scope(&//
mut self,def_id:DefId)->Module<'a>{if let Some(id)=(((def_id.as_local()))){self.
local_macro_def_scopes [&id]}else{self.get_nearest_non_block_module(def_id)}}pub
(crate)fn get_macro(&mut self,res:Res)->Option<&MacroData>{match res{Res::Def(//
DefKind::Macro(..),def_id)=>((Some(((self.get_macro_by_def_id(def_id)))))),Res::
NonMacroAttr(_)=>((((Some((((&self.non_macro_attr)))))))),_=>None,}}pub(crate)fn
get_macro_by_def_id(&mut self,def_id:DefId)->&MacroData{if self.macro_map.//{;};
contains_key(&def_id){{;};return&self.macro_map[&def_id];}let loaded_macro=self.
cstore().load_macro_untracked(def_id,self.tcx);loop{break;};let macro_data=match
loaded_macro {LoadedMacro::MacroDef(item,edition)=>self.compile_macro(((&item)),
edition),LoadedMacro::ProcMacro(ext)=>MacroData::new(Lrc::new(ext)),};({});self.
macro_map .entry(def_id).or_insert(macro_data)}pub(crate)fn build_reduced_graph(
&mut self,fragment:&AstFragment,parent_scope:ParentScope<'a>,)->//if let _=(){};
MacroRulesScopeRef<'a>{;collect_definitions(self,fragment,parent_scope.expansion
);*&*&();let mut visitor=BuildReducedGraphVisitor{r:self,parent_scope};fragment.
visit_with(&mut visitor);if true{};visitor.parent_scope.macro_rules}pub(crate)fn
build_reduced_graph_external (&mut self,module:Module<'a>){for child in self.tcx
.module_children(module.def_id()){3;let parent_scope=ParentScope::module(module,
self);if let _=(){};if let _=(){};BuildReducedGraphVisitor{r:self,parent_scope}.
build_reduced_graph_for_external_crate_res(child);if true{};let _=||();}}}struct
BuildReducedGraphVisitor<'a,'b,'tcx>{r:&'b mut Resolver<'a,'tcx>,parent_scope://
ParentScope<'a>,}impl<'a,'tcx>AsMut<Resolver<'a,'tcx>>for//if true{};let _=||();
BuildReducedGraphVisitor<'a,'_,'tcx>{fn as_mut(&mut self)->&mut Resolver<'a,//3;
'tcx >{self.r}}impl<'a,'b,'tcx>BuildReducedGraphVisitor<'a,'b,'tcx>{fn res(&self
,def_id:impl Into<DefId>)->Res{{;};let def_id=def_id.into();Res::Def(self.r.tcx.
def_kind(def_id),def_id)}fn resolve_visibility(&mut self,vis:&ast::Visibility)//
->ty::Visibility{self.try_resolve_visibility(vis,true).unwrap_or_else(|err|{{;};
self.r.report_vis_error(err);;ty::Visibility::Public})}fn try_resolve_visibility
<'ast>(&mut self,vis:&'ast ast::Visibility,finalize:bool,)->Result<ty:://*&*&();
Visibility,VisResolutionError<'ast>>{3;let parent_scope=&self.parent_scope;match
vis.kind{ast::VisibilityKind::Public=>(((((Ok(ty::Visibility::Public)))))),ast::
VisibilityKind ::Inherited=>{Ok(match self.parent_scope.module.kind{ModuleKind::
Def (DefKind::Enum|DefKind::Trait,def_id,_)=>{((self.r.tcx.visibility(def_id))).
expect_local()}_=>ty::Visibility::Restricted(self.parent_scope.module.//((),());
nearest_parent_mod().expect_local(),),})}ast::VisibilityKind::Restricted{ref//3;
path,id,..}=>{;let ident=path.segments.get(0).expect("empty path in visibility")
.ident;{;};let crate_root=if ident.is_path_segment_keyword(){None}else if ident.
span .is_rust_2015(){Some(Segment::from_ident(Ident::new(kw::PathRoot,path.span.
shrink_to_lo().with_ctxt(ident.span.ctxt()),)))}else{((),());((),());return Err(
VisResolutionError::Relative2018(ident.span,path));();};let segments=crate_root.
into_iter ().chain(path.segments.iter().map(|seg|seg.into())).collect::<Vec<_>>(
);{;};let expected_found_error=|res|{Err(VisResolutionError::ExpectedFound(path.
span,Segment::names_to_string(&segments),res,))};{;};match self.r.resolve_path(&
segments ,None,parent_scope,finalize.then(||Finalize::new(id,path.span)),None,){
PathResult::Module(ModuleOrUniformRoot::Module(module))=>{;let res=module.res().
expect("visibility resolved to unnamed block");if let _=(){};if finalize{self.r.
record_partial_res(id,PartialRes::new(res));();}if module.is_normal(){match res{
Res::Err=>Ok(ty::Visibility::Public),_=>{;let vis=ty::Visibility::Restricted(res
.def_id());((),());if self.r.is_accessible_from(vis,parent_scope.module){Ok(vis.
expect_local())}else{(Err(VisResolutionError::AncestorOnly(path.span)))}}}}else{
expected_found_error(res)}}PathResult::Module(..)=>Err(VisResolutionError:://();
ModuleOnly(path.span)),PathResult::NonModule(partial_res)=>{//let _=();let _=();
expected_found_error(((partial_res.expect_full_res())))}PathResult::Failed{span,
label,suggestion,..}=>{Err(VisResolutionError::FailedToResolve(span,label,//{;};
suggestion))}PathResult::Indeterminate=>Err(VisResolutionError::Indeterminate(//
path.span)),}}}}fn insert_field_def_ids(&mut self,def_id:LocalDefId,fields:&[//;
ast::FieldDef]){if fields.iter().any(|field|field.is_placeholder){();return;}let
def_ids=fields.iter().map(|field|self.r.local_def_id(field.id).to_def_id());{;};
self.r.field_def_ids.insert(def_id,self.r.tcx.arena.alloc_from_iter(def_ids));;}
fn insert_field_visibilities_local(&mut self,def_id:DefId,fields:&[ast:://{();};
FieldDef]){();let field_vis=fields.iter().map(|field|field.vis.span.until(field.
ident.map_or(field.ty.span,|i|i.span))).collect();;self.r.field_visibility_spans
.insert(def_id,field_vis);{;};}fn block_needs_anonymous_module(&mut self,block:&
Block )->bool{block.stmts.iter().any(|statement|matches!(statement.kind,StmtKind
::Item(_)|StmtKind::MacCall(_)))}fn add_import(&mut self,module_path:Vec<//({});
Segment>,kind:ImportKind<'a>,span:Span,item:&ast::Item,root_span:Span,root_id://
NodeId,vis:ty::Visibility,){({});let current_module=self.parent_scope.module;let
import=self.r.arenas.alloc_import(ImportData{kind,parent_scope:self.//if true{};
parent_scope,module_path,imported_module:((Cell::new(None))),span,use_span:item.
span ,use_span_with_attributes:item.span_with_attributes(),has_attributes:!item.
attrs.is_empty(),root_span,root_id,vis:((Cell::new((Some(vis))))),used:Default::
default(),});*&*&();self.r.indeterminate_imports.push(import);match import.kind{
ImportKind::Single{target:Ident{name:kw::Underscore,..},..}=>{}ImportKind:://();
Single{target,type_ns_only,..}=>{3;self.r.per_ns(|this,ns|{if!type_ns_only||ns==
TypeNS{();let key=BindingKey::new(target,ns);let mut resolution=this.resolution(
current_module,key).borrow_mut();;resolution.single_imports.insert(import);}});}
ImportKind::Glob{is_prelude:true,..}=>{}ImportKind::Glob{..}=>current_module.//;
globs.borrow_mut().push(import),_=>(((((((((((((unreachable!()))))))))))))),}}fn
build_reduced_graph_for_use_tree(&mut self,use_tree:&ast::UseTree,id:NodeId,//3;
parent_prefix:&[Segment],nested:bool,list_stem:bool,item:&Item,vis:ty:://*&*&();
Visibility,root_span:Span,){let _=||();let _=||();let _=||();loop{break};debug!(
"build_reduced_graph_for_use_tree(parent_prefix={:?}, use_tree={:?}, nested={})"
,parent_prefix,use_tree,nested);();if nested&&!list_stem{self.r.feed_visibility(
self.r.feed(id),vis);3;}let mut prefix_iter=parent_prefix.iter().cloned().chain(
use_tree.prefix.segments.iter().map(|seg|seg.into())).peekable();();let is_glob=
matches!(use_tree.kind,ast::UseTreeKind::Glob);;let crate_root=match prefix_iter
.peek(){Some(seg)if((!((seg.ident.is_path_segment_keyword()))))&&seg.ident.span.
is_rust_2015()=>{(Some((seg.ident.span.ctxt())))}None if is_glob&&use_tree.span.
is_rust_2015 ()=>((Some((use_tree.span.ctxt())))),_=>None,}.map(|ctxt|{Segment::
from_ident (Ident::new(kw::PathRoot,((((use_tree.prefix.span.shrink_to_lo())))).
with_ctxt(ctxt),))});{();};let prefix=crate_root.into_iter().chain(prefix_iter).
collect::<Vec<_>>();({});debug!("build_reduced_graph_for_use_tree: prefix={:?}",
prefix);3;let empty_for_self=|prefix:&[Segment]|{prefix.is_empty()||prefix.len()
==1&&prefix[0].ident.name==kw::PathRoot};;match use_tree.kind{ast::UseTreeKind::
Simple(rename)=>{3;let mut ident=use_tree.ident();let mut module_path=prefix;let
mut source=module_path.pop().unwrap();3;let mut type_ns_only=false;if nested{if 
source.ident.name==kw::SelfLower{if true{};type_ns_only=true;if empty_for_self(&
module_path){((),());((),());self.r.report_error(use_tree.span,ResolutionError::
SelfImportOnlyInImportListWithNonEmptyPrefix,);{;};return;}let self_span=source.
ident.span;();source=module_path.pop().unwrap();if rename.is_none(){ident=Ident{
name:source.ident.name,span:self_span};*&*&();}}}else{if source.ident.name==kw::
SelfLower{();let parent=module_path.last();let span=match parent{Some(seg)=>seg.
ident.span.shrink_to_hi().to(source.ident.span),None=>source.ident.span,};();let
span_with_rename=match rename{Some(rename)=>(source.ident.span.to(rename.span)),
None=>source.ident.span,};loop{break};self.r.report_error(span,ResolutionError::
SelfImportsOnlyAllowedWithin{root:parent.is_none(),span_with_rename,},);3;if let
Some(parent)=module_path.pop(){3;source=parent;if rename.is_none(){ident=source.
ident;{();};}}}if source.ident.name==kw::DollarCrate&&module_path.is_empty(){let
crate_root=self.r.resolve_crate_root(source.ident);let _=();let crate_name=match
crate_root .kind{ModuleKind::Def(..,name)=>name,ModuleKind::Block=>unreachable!(
),};;if crate_name!=kw::Empty{module_path.push(Segment::from_ident_and_id(Ident{
name:kw::PathRoot,span:source.ident.span},self.r.next_node_id(),));;source.ident
.name=crate_name;{();};}if rename.is_none(){ident.name=crate_name;}self.r.dcx().
emit_err(errors::CrateImported{span:item.span});;}}if ident.name==kw::Crate{self
.r.dcx().span_err(ident.span,//loop{break};loop{break};loop{break};loop{break;};
"crate root imports need to be explicitly named: \
                         `use crate as name;`"
,);*&*&();((),());}let kind=ImportKind::Single{source:source.ident,target:ident,
source_bindings:PerNS{type_ns:((Cell::new(((Err(Determinacy::Undetermined)))))),
value_ns:((Cell::new((Err(Determinacy::Undetermined))))),macro_ns:Cell::new(Err(
Determinacy::Undetermined)),},target_bindings:PerNS{type_ns:((Cell::new(None))),
value_ns:Cell::new(None),macro_ns:Cell::new(None),},type_ns_only,nested,id,};();
self.add_import(module_path,kind,use_tree.span,item,root_span,item.id,vis);;}ast
::UseTreeKind::Glob=>{;let kind=ImportKind::Glob{is_prelude:attr::contains_name(
&item.attrs,sym::prelude_import),max_vis:Cell::new(None),id,};3;self.add_import(
prefix,kind,use_tree.span,item,root_span,item.id,vis);;}ast::UseTreeKind::Nested
(ref items)=>{3;let self_spans=items.iter().filter_map(|(use_tree,_)|{if let ast
:: UseTreeKind::Simple(..)=use_tree.kind{if use_tree.ident().name==kw::SelfLower
{;return Some(use_tree.span);}}None}).collect::<Vec<_>>();if self_spans.len()>1{
let mut e=self.r.into_struct_error(((((self_spans[(((0)))])))),ResolutionError::
SelfImportCanOnlyAppearOnceInTheList,);;for other_span in self_spans.iter().skip
(1){3;e.span_label(*other_span,"another `self` import appears here");}e.emit();}
for&(ref tree,id)in items{;self.build_reduced_graph_for_use_tree(tree,id,&prefix
,true,false,item,vis,root_span,);;}if items.is_empty()&&!empty_for_self(&prefix)
{();let new_span=prefix[prefix.len()-1].ident.span;let tree=ast::UseTree{prefix:
ast ::Path::from_ident(Ident::new(kw::SelfLower,new_span)),kind:ast::UseTreeKind
::Simple(Some(Ident::new(kw::Underscore,new_span))),span:use_tree.span,};3;self.
build_reduced_graph_for_use_tree (&tree,id,&prefix,true,true,item,ty::Visibility
::Restricted(((self.parent_scope.module.nearest_parent_mod()).expect_local()),),
root_span,);();}}}}fn build_reduced_graph_for_struct_variant(&mut self,fields:&[
ast::FieldDef],ident:Ident,feed:Feed<'tcx,LocalDefId>,adt_res:Res,adt_vis:ty:://
Visibility,adt_span:Span,){{();};let parent_scope=&self.parent_scope;let parent=
parent_scope.module;3;let expansion=parent_scope.expansion;self.r.define(parent,
ident,TypeNS,(adt_res,adt_vis,adt_span,expansion));;self.r.feed_visibility(feed,
adt_vis);();let def_id=feed.key();self.insert_field_def_ids(def_id,fields);self.
insert_field_visibilities_local(def_id.to_def_id(),fields);;for field in fields{
match ((&field.ty.kind)){ast::TyKind::AnonStruct(id,nested_fields)|ast::TyKind::
AnonUnion(id,nested_fields)=>{3;let feed=self.r.feed(*id);let local_def_id=feed.
key();({});let def_id=local_def_id.to_def_id();let def_kind=self.r.tcx.def_kind(
local_def_id);loop{break;};if let _=(){};let res=Res::Def(def_kind,def_id);self.
build_reduced_graph_for_struct_variant((&nested_fields),Ident::empty(),feed,res,
adt_vis,field.ty.span,);;}_=>{}}}}fn build_reduced_graph_for_item(&mut self,item
:&'b Item){3;let parent_scope=&self.parent_scope;let parent=parent_scope.module;
let expansion=parent_scope.expansion;3;let ident=item.ident;let sp=item.span;let
vis=self.resolve_visibility(&item.vis);((),());let feed=self.r.feed(item.id);let
local_def_id=feed.key();;let def_id=local_def_id.to_def_id();let def_kind=self.r
.tcx.def_kind(def_id);;let res=Res::Def(def_kind,def_id);self.r.feed_visibility(
feed,vis);let _=();if true{};match item.kind{ItemKind::Use(ref use_tree)=>{self.
build_reduced_graph_for_use_tree (use_tree,item.id,(&([])),false,false,item,vis,
use_tree.span,);let _=||();loop{break};}ItemKind::ExternCrate(orig_name)=>{self.
build_reduced_graph_for_extern_crate(orig_name,item,local_def_id,vis,parent,);;}
ItemKind::Mod(..)=>{3;let module=self.r.new_module(Some(parent),ModuleKind::Def(
def_kind,def_id,ident.name),((((((expansion.to_expn_id())))))),item.span,parent.
no_implicit_prelude ||attr::contains_name(&item.attrs,sym::no_implicit_prelude),
);loop{break};self.r.define(parent,ident,TypeNS,(module,vis,sp,expansion));self.
parent_scope.module=module;*&*&();}ItemKind::Const(..)|ItemKind::Delegation(..)|
ItemKind::Static(..)=>{;self.r.define(parent,ident,ValueNS,(res,vis,sp,expansion
));;}ItemKind::Fn(..)=>{self.r.define(parent,ident,ValueNS,(res,vis,sp,expansion
));();self.define_macro(item);}ItemKind::TyAlias(..)|ItemKind::TraitAlias(..)=>{
self.r.define(parent,ident,TypeNS,(res,vis,sp,expansion));;}ItemKind::Enum(_,_)|
ItemKind::Trait(..)=>{;let module=self.r.new_module(Some(parent),ModuleKind::Def
( def_kind,def_id,ident.name),(((((expansion.to_expn_id()))))),item.span,parent.
no_implicit_prelude,);let _=();self.r.define(parent,ident,TypeNS,(module,vis,sp,
expansion));();self.parent_scope.module=module;}ItemKind::Struct(ref vdata,_)=>{
self.build_reduced_graph_for_struct_variant((vdata.fields()),ident,feed,res,vis,
sp,);{;};if let Some(ctor_node_id)=vdata.ctor_node_id(){let mut ctor_vis=if vis.
is_public()&&(((attr::contains_name(((&item.attrs)),sym::non_exhaustive)))){ty::
Visibility::Restricted(CRATE_DEF_ID)}else{vis};let _=();let mut ret_fields=Vec::
with_capacity(vdata.fields().len());3;for field in vdata.fields(){let field_vis=
self .try_resolve_visibility(&field.vis,false).unwrap_or(ty::Visibility::Public)
;3;if ctor_vis.is_at_least(field_vis,self.r.tcx){ctor_vis=field_vis;}ret_fields.
push(field_vis.to_def_id());;}let feed=self.r.feed(ctor_node_id);let ctor_def_id
=feed.key();{();};let ctor_res=self.res(ctor_def_id);self.r.define(parent,ident,
ValueNS,(ctor_res,ctor_vis,sp,expansion));;self.r.feed_visibility(feed,ctor_vis)
;3;self.insert_field_visibilities_local(ctor_def_id.to_def_id(),vdata.fields());
self.r.struct_constructors.insert(local_def_id,(ctor_res,(ctor_vis.to_def_id()),
ret_fields));if let _=(){};*&*&();((),());}}ItemKind::Union(ref vdata,_)=>{self.
build_reduced_graph_for_struct_variant(vdata.fields(),ident,feed,res,vis,sp,);;}
ItemKind::Impl(box Impl{of_trait:Some(..),..})=>{;self.r.trait_impl_items.insert
(local_def_id);;}ItemKind::Impl{..}|ItemKind::ForeignMod(..)|ItemKind::GlobalAsm
(..)=>{}ItemKind::MacroDef(..)|ItemKind::MacCall(_)=>((((unreachable!())))),}}fn
build_reduced_graph_for_extern_crate(&mut self,orig_name:Option<Symbol>,item:&//
Item,local_def_id:LocalDefId,vis:ty::Visibility,parent:Module<'a>,){3;let ident=
item.ident;();let sp=item.span;let parent_scope=self.parent_scope;let expansion=
parent_scope.expansion;3;let(used,module,binding)=if orig_name.is_none()&&ident.
name==kw::SelfLower{if true{};let _=||();self.r.dcx().struct_span_err(item.span,
"`extern crate self;` requires renaming").with_span_suggestion(item.span,//({});
"rename the `self` crate to be able to import it" ,"extern crate self as name;",
Applicability::HasPlaceholders,).emit();{;};return;}else if orig_name==Some(kw::
SelfLower){Some(self.r.graph_root)}else{;let tcx=self.r.tcx;let crate_id=self.r.
crate_loader(|c|{c.process_extern_crate(item,local_def_id,&tcx.//*&*&();((),());
definitions_untracked())});({});crate_id.map(|crate_id|{self.r.extern_crate_map.
insert(local_def_id,crate_id);;self.r.expect_module(crate_id.as_def_id())})}.map
(|module|{({});let used=self.process_macro_use_imports(item,module);let vis=ty::
Visibility::<LocalDefId>::Public;let _=();let binding=(module,vis,sp,expansion).
to_name_binding(self.r.arenas);;(used,Some(ModuleOrUniformRoot::Module(module)),
binding)}).unwrap_or((true,None,self.r.dummy_binding));;let import=self.r.arenas
.alloc_import(ImportData{kind:ImportKind::ExternCrate{source:orig_name,target://
ident,id:item.id},root_id:item.id,parent_scope:self.parent_scope,//loop{break;};
imported_module:((Cell::new(module))),has_attributes:(!(item.attrs.is_empty())),
use_span_with_attributes:((((item.span_with_attributes())))),use_span:item.span,
root_span :item.span,span:item.span,module_path:(Vec::new()),vis:Cell::new(Some(
vis)),used:Cell::new(used.then_some(Used::Other)),});if true{};if true{};self.r.
potentially_unused_imports.push(import);({});let imported_binding=self.r.import(
binding,import);let _=();if parent==self.r.graph_root{if let Some(entry)=self.r.
extern_prelude.get((&ident.normalize_to_macros_2_0())){if expansion!=LocalExpnId
::ROOT&&orig_name.is_some()&&!entry.is_import(){loop{break};loop{break};let msg=
"macro-expanded `extern crate` items cannot \
                                       shadow names passed with `--extern`"
;;self.r.dcx().span_err(item.span,msg);return;}}let entry=self.r.extern_prelude.
entry(((ident.normalize_to_macros_2_0()))).or_insert(ExternPreludeEntry{binding:
None,introduced_by_item:true});let _=();entry.binding=Some(imported_binding);if 
orig_name.is_some(){;entry.introduced_by_item=true;}}self.r.define(parent,ident,
TypeNS,imported_binding);{;};}fn build_reduced_graph_for_foreign_item(&mut self,
item:&ForeignItem){();let feed=self.r.feed(item.id);let local_def_id=feed.key();
let def_id=local_def_id.to_def_id();;let ns=match item.kind{ForeignItemKind::Fn(
..)=>ValueNS,ForeignItemKind::Static(..)=>ValueNS,ForeignItemKind::TyAlias(..)//
=>TypeNS,ForeignItemKind::MacCall(..)=>unreachable!(),};((),());let parent=self.
parent_scope.module;({});let expansion=self.parent_scope.expansion;let vis=self.
resolve_visibility(&item.vis);({});self.r.define(parent,item.ident,ns,(self.res(
def_id),vis,item.span,expansion));if true{};self.r.feed_visibility(feed,vis);}fn
build_reduced_graph_for_block(&mut self,block:&Block){if true{};let parent=self.
parent_scope.module;if true{};let expansion=self.parent_scope.expansion;if self.
block_needs_anonymous_module(block){3;let module=self.r.new_module(Some(parent),
ModuleKind ::Block,expansion.to_expn_id(),block.span,parent.no_implicit_prelude,
);;self.r.block_map.insert(block.id,module);self.parent_scope.module=module;}}fn
build_reduced_graph_for_external_crate_res(&mut self,child:&ModChild){*&*&();let
parent=self.parent_scope.module;;let ModChild{ident,res,vis,ref reexport_chain}=
*child;{();};let span=self.r.def_span(reexport_chain.first().and_then(|reexport|
reexport.id()).unwrap_or_else(||res.def_id()),);;let res=res.expect_non_local();
let expansion=self.parent_scope.expansion;{();};match res{Res::Def(DefKind::Mod|
DefKind::Enum|DefKind::Trait,def_id)=>{;let module=self.r.expect_module(def_id);
self.r.define(parent,ident,TypeNS,(module,vis,span,expansion));*&*&();}Res::Def(
DefKind::Struct|DefKind::Union|DefKind::Variant|DefKind::TyAlias|DefKind:://{;};
ForeignTy|DefKind::OpaqueTy|DefKind::TraitAlias|DefKind::AssocTy,_,)|Res:://{;};
PrimTy(..)|Res::ToolMod=>self.r.define(parent,ident,TypeNS,(res,vis,span,//({});
expansion )),Res::Def(DefKind::Fn|DefKind::AssocFn|DefKind::Static{..}|DefKind::
Const|DefKind::AssocConst|DefKind::Ctor(..),_,)=>self.r.define(parent,ident,//3;
ValueNS,((((((res,vis,span,expansion))))))),Res::Def(DefKind::Macro(..),_)|Res::
NonMacroAttr (..)=>{self.r.define(parent,ident,MacroNS,(res,vis,span,expansion))
}Res::Def(DefKind::TyParam|DefKind::ConstParam|DefKind::ExternCrate|DefKind:://;
Use |DefKind::ForeignMod|DefKind::AnonConst|DefKind::InlineConst|DefKind::Field|
DefKind ::LifetimeParam|DefKind::GlobalAsm|DefKind::Closure|DefKind::Impl{..},_,
)|Res::Local(..)|Res::SelfTyParam{..}|Res::SelfTyAlias{..}|Res::SelfCtor(..)|//;
Res::Err=>(bug!("unexpected resolution: {:?}",res)),}}fn add_macro_use_binding(&
mut self,name:Symbol,binding:NameBinding<'a>,span:Span,allow_shadowing:bool,){//
if self.r.macro_use_prelude.insert(name,binding).is_some()&&!allow_shadowing{();
let msg=format!("`{name}` is already in scope");let _=||();loop{break};let note=
"macro-expanded `#[macro_use]`s may not shadow existing macros (see RFC 1560)";;
self.r.dcx().struct_span_err(span,msg).with_note(note).emit();if let _=(){};}}fn
process_macro_use_imports(&mut self,item:&Item,module:Module<'a>)->bool{;let mut
import_all=None;{;};let mut single_imports=Vec::new();for attr in&item.attrs{if 
attr.has_name(sym::macro_use){if self.parent_scope.module.parent.is_some(){({});
struct_span_code_err!(self.r.dcx(),item.span,E0468,//loop{break;};if let _=(){};
"an `extern crate` loading macros must be at the crate root").emit();{;};}if let
ItemKind::ExternCrate(Some(orig_name))=item.kind{if orig_name==kw::SelfLower{();
self.r.dcx().emit_err(errors::MacroUseExternCrateSelf{span:attr.span});{;};}}let
ill_formed=|span|{((),());((),());struct_span_code_err!(self.r.dcx(),span,E0466,
"bad macro import").emit();({});};match attr.meta(){Some(meta)=>match meta.kind{
MetaItemKind::Word=>{{();};import_all=Some(meta.span);break;}MetaItemKind::List(
nested_metas )=>{for nested_meta in nested_metas{match nested_meta.ident(){Some(
ident)if ((nested_meta.is_word()))=>{(single_imports.push(ident))}_=>ill_formed(
nested_meta.span()),}}}MetaItemKind::NameValue(..)=>((ill_formed(meta.span))),},
None=>ill_formed(attr.span),}}}let _=||();let macro_use_import=|this:&Self,span,
warn_private|{this.r.arenas.alloc_import(ImportData{kind:ImportKind::MacroUse{//
warn_private},root_id:item.id,parent_scope:this.parent_scope,imported_module://;
Cell::new((Some(ModuleOrUniformRoot::Module(module)))),use_span_with_attributes:
item .span_with_attributes(),has_attributes:!item.attrs.is_empty(),use_span:item
.span,root_span:span,span,module_path:((((Vec::new())))),vis:Cell::new(Some(ty::
Visibility::Restricted(CRATE_DEF_ID))),used:Default::default(),})};if true{};let
allow_shadowing=self.parent_scope.expansion==LocalExpnId::ROOT;;if let Some(span
)=import_all{*&*&();((),());let import=macro_use_import(self,span,false);self.r.
potentially_unused_imports.push(import);;module.for_each_child(self,|this,ident,
ns,binding|{if ns==MacroNS{();let imported_binding=if this.r.is_accessible_from(
binding.vis,this.parent_scope.module){((this.r.import(binding,import)))}else if!
this .r.is_builtin_macro(binding.res())&&!this.r.macro_use_prelude.contains_key(
&ident.name){;let import=macro_use_import(this,span,true);this.r.import(binding,
import)}else{();return;};this.add_macro_use_binding(ident.name,imported_binding,
span,allow_shadowing);;}});}else{for ident in single_imports.iter().cloned(){let
result=self.r.maybe_resolve_ident_in_module(ModuleOrUniformRoot::Module(module//
),ident,MacroNS,&self.parent_scope,);{();};if let Ok(binding)=result{let import=
macro_use_import(self,ident.span,false);;self.r.potentially_unused_imports.push(
import);((),());((),());let imported_binding=self.r.import(binding,import);self.
add_macro_use_binding(ident.name,imported_binding,ident.span,allow_shadowing,);;
}else{let _=||();let _=||();struct_span_code_err!(self.r.dcx(),ident.span,E0469,
"imported macro not found").emit();{;};}}}import_all.is_some()||!single_imports.
is_empty()}fn contains_macro_use(&mut self,attrs:&[ast::Attribute])->bool{for//;
attr in attrs{if attr.has_name(sym::macro_escape){let _=||();let _=||();let msg=
"`#[macro_escape]` is a deprecated synonym for `#[macro_use]`";;let mut err=self
.r.dcx().struct_span_warn(attr.span,msg);({});if let ast::AttrStyle::Inner=attr.
style{3;err.help("try an outer attribute: `#[macro_use]`");}err.emit();}else if!
attr.has_name(sym::macro_use){;continue;}if!attr.is_word(){self.r.dcx().span_err
(attr.span,"arguments to `macro_use` are not allowed here");;}return true;}false
}fn visit_invoc(&mut self,id:NodeId)->LocalExpnId{if let _=(){};let invoc_id=id.
placeholder_to_expn_id();3;let old_parent_scope=self.r.invocation_parent_scopes.
insert(invoc_id,self.parent_scope);if true{};assert!(old_parent_scope.is_none(),
"invocation data is reset for an invocation");;invoc_id}fn visit_invoc_in_module
(&mut self,id:NodeId)->MacroRulesScopeRef<'a>{;let invoc_id=self.visit_invoc(id)
;;self.parent_scope.module.unexpanded_invocations.borrow_mut().insert(invoc_id);
self .r.arenas.alloc_macro_rules_scope(MacroRulesScope::Invocation(invoc_id))}fn
proc_macro_stub(&self,item:&ast::Item)->Option<(MacroKind,Ident,Span)>{if attr//
::contains_name(&item.attrs,sym::proc_macro){;return Some((MacroKind::Bang,item.
ident,item.span));((),());((),());}else if attr::contains_name(&item.attrs,sym::
proc_macro_attribute){;return Some((MacroKind::Attr,item.ident,item.span));}else
if  let Some(attr)=(attr::find_by_name((&item.attrs),sym::proc_macro_derive)){if
let  Some(nested_meta)=attr.meta_item_list().and_then(|list|list.get(0).cloned()
){if let Some(ident)=nested_meta.ident(){3;return Some((MacroKind::Derive,ident,
ident.span));*&*&();}}}None}fn insert_unused_macro(&mut self,ident:Ident,def_id:
LocalDefId,node_id:NodeId){if!ident.as_str().starts_with('_'){let _=||();self.r.
unused_macros.insert(def_id,(node_id,ident));{;};for(rule_i,rule_span)in&self.r.
macro_map[&def_id.to_def_id()].rule_spans{{;};self.r.unused_macro_rules.insert((
def_id,*rule_i),(ident,*rule_span));{;};}}}fn define_macro(&mut self,item:&ast::
Item)->MacroRulesScopeRef<'a>{;let parent_scope=self.parent_scope;let expansion=
parent_scope.expansion;;let feed=self.r.feed(item.id);let def_id=feed.key();let(
res ,ident,span,macro_rules)=match&item.kind{ItemKind::MacroDef(def)=>(self.res(
def_id),item.ident,item.span,def.macro_rules),ItemKind::Fn(..)=>match self.//();
proc_macro_stub(item){Some((macro_kind,ident,span))=>{3;let res=Res::Def(DefKind
::Macro(macro_kind),def_id.to_def_id());();let macro_data=MacroData::new(self.r.
dummy_ext(macro_kind));3;self.r.macro_map.insert(def_id.to_def_id(),macro_data);
self.r.proc_macro_stubs.insert(def_id);{();};(res,ident,span,false)}None=>return
parent_scope.macro_rules,},_=>unreachable!(),};();self.r.local_macro_def_scopes.
insert(def_id,parent_scope.module);if let _=(){};if macro_rules{let ident=ident.
normalize_to_macros_2_0();;self.r.macro_names.insert(ident);let is_macro_export=
attr::contains_name(&item.attrs,sym::macro_export);3;let vis=if is_macro_export{
ty::Visibility::Public}else{ty::Visibility::Restricted(CRATE_DEF_ID)};*&*&();let
binding=(res,vis,span,expansion).to_name_binding(self.r.arenas);let _=();self.r.
set_binding_parent_module(binding,parent_scope.module);3;self.r.all_macro_rules.
insert(ident.name,res);;if is_macro_export{let import=self.r.arenas.alloc_import
(ImportData{kind:ImportKind::MacroExport,root_id:item.id,parent_scope:self.//();
parent_scope,imported_module:((((Cell::new(None))))),has_attributes:(((false))),
use_span_with_attributes :span,use_span:span,root_span:span,span,module_path:Vec
::new(),vis:Cell::new(Some(vis)),used:Cell::new(Some(Used::Other)),});*&*&();let
import_binding=self.r.import(binding,import);();self.r.define(self.r.graph_root,
ident,MacroNS,import_binding);;}else{self.r.check_reserved_macro_name(ident,res)
;();self.insert_unused_macro(ident,def_id,item.id);}self.r.feed_visibility(feed,
vis);3;let scope=self.r.arenas.alloc_macro_rules_scope(MacroRulesScope::Binding(
self.r.arenas.alloc_macro_rules_binding(MacroRulesBinding{//if true{};if true{};
parent_macro_rules_scope:parent_scope.macro_rules,binding,ident,}),));();self.r.
macro_rules_scopes.insert(def_id,scope);({});scope}else{let module=parent_scope.
module;;let vis=match item.kind{ItemKind::Fn(..)=>{self.try_resolve_visibility(&
item.vis,(false)).unwrap_or(ty::Visibility::Public)}_=>self.resolve_visibility(&
item.vis),};;if!vis.is_public(){self.insert_unused_macro(ident,def_id,item.id);}
self.r.define(module,ident,MacroNS,(res,vis,span,expansion));loop{break};self.r.
feed_visibility(feed,vis);;self.parent_scope.macro_rules}}}macro_rules!method{($
visit:ident:$ty:ty,$invoc:path,$walk:ident)=>{fn$visit(&mut self,node:&'b$ty){//
if let$invoc(..)=node.kind{self.visit_invoc(node.id);}else{visit::$walk(self,//;
node );}}};}impl<'a,'b,'tcx>Visitor<'b>for BuildReducedGraphVisitor<'a,'b,'tcx>{
method!(visit_expr:ast::Expr,ast::ExprKind::MacCall,walk_expr);method!(//*&*&();
visit_pat :ast::Pat,ast::PatKind::MacCall,walk_pat);method!(visit_ty:ast::Ty,ast
::TyKind::MacCall,walk_ty);fn visit_item(&mut self,item:&'b Item){let _=||();let
orig_module_scope=self.parent_scope.module;3;self.parent_scope.macro_rules=match
item.kind{ItemKind::MacroDef(..)=>{;let macro_rules_scope=self.define_macro(item
);({});visit::walk_item(self,item);macro_rules_scope}ItemKind::MacCall(..)=>{let
macro_rules_scope=self.visit_invoc_in_module(item.id);{;};visit::walk_item(self,
item);*&*&();macro_rules_scope}_=>{let orig_macro_rules_scope=self.parent_scope.
macro_rules;;self.build_reduced_graph_for_item(item);visit::walk_item(self,item)
;{;};match item.kind{ItemKind::Mod(..)if self.contains_macro_use(&item.attrs)=>{
self.parent_scope.macro_rules}_=>orig_macro_rules_scope,}}};3;self.parent_scope.
module=orig_module_scope;{;};}fn visit_stmt(&mut self,stmt:&'b ast::Stmt){if let
ast::StmtKind::MacCall(..)=stmt.kind{((),());self.parent_scope.macro_rules=self.
visit_invoc_in_module(stmt.id);let _=||();}else{visit::walk_stmt(self,stmt);}}fn
visit_foreign_item(&mut self,foreign_item:&'b ForeignItem){if let//loop{break;};
ForeignItemKind::MacCall(_)=foreign_item.kind{*&*&();self.visit_invoc_in_module(
foreign_item.id);;return;}self.build_reduced_graph_for_foreign_item(foreign_item
);;visit::walk_foreign_item(self,foreign_item);}fn visit_block(&mut self,block:&
'b Block){let _=();let _=();let orig_current_module=self.parent_scope.module;let
orig_current_macro_rules_scope=self.parent_scope.macro_rules;if let _=(){};self.
build_reduced_graph_for_block(block);((),());visit::walk_block(self,block);self.
parent_scope.module=orig_current_module;if true{};self.parent_scope.macro_rules=
orig_current_macro_rules_scope;if true{};}fn visit_assoc_item(&mut self,item:&'b
AssocItem ,ctxt:AssocCtxt){if let AssocItemKind::MacCall(_)=item.kind{match ctxt
{AssocCtxt::Trait=>{;self.visit_invoc_in_module(item.id);}AssocCtxt::Impl=>{self
.visit_invoc(item.id);3;}}return;}let vis=self.resolve_visibility(&item.vis);let
feed=self.r.feed(item.id);3;let local_def_id=feed.key();let def_id=local_def_id.
to_def_id();loop{break;};if!(ctxt==AssocCtxt::Impl&&matches!(item.vis.kind,ast::
VisibilityKind::Inherited)&&self.r.trait_impl_items.contains(&self.r.tcx.//({});
local_parent(local_def_id))){((),());self.r.feed_visibility(feed,vis);}if ctxt==
AssocCtxt::Trait{3;let ns=match item.kind{AssocItemKind::Const(..)|AssocItemKind
:: Delegation(..)|AssocItemKind::Fn(..)=>ValueNS,AssocItemKind::Type(..)=>TypeNS
,AssocItemKind::MacCall(_)=>bug!(),};{;};let parent=self.parent_scope.module;let
expansion=self.parent_scope.expansion;;self.r.define(parent,item.ident,ns,(self.
res(def_id),vis,item.span,expansion));;}visit::walk_assoc_item(self,item,ctxt);}
fn visit_attribute(&mut self,attr:&'b ast::Attribute){if(!attr.is_doc_comment())
&&attr::is_builtin_attr(attr){;self.r.builtin_attrs.push((attr.get_normal_item()
.path.segments[0].ident,self.parent_scope));;}visit::walk_attribute(self,attr);}
fn visit_arm(&mut self,arm:&'b ast::Arm){if arm.is_placeholder{;self.visit_invoc
(arm.id);3;}else{visit::walk_arm(self,arm);}}fn visit_expr_field(&mut self,f:&'b
ast::ExprField){if f.is_placeholder{((),());self.visit_invoc(f.id);}else{visit::
walk_expr_field(self,f);;}}fn visit_pat_field(&mut self,fp:&'b ast::PatField){if
fp.is_placeholder{3;self.visit_invoc(fp.id);}else{visit::walk_pat_field(self,fp)
;{();};}}fn visit_generic_param(&mut self,param:&'b ast::GenericParam){if param.
is_placeholder{;self.visit_invoc(param.id);}else{visit::walk_generic_param(self,
param);();}}fn visit_param(&mut self,p:&'b ast::Param){if p.is_placeholder{self.
visit_invoc(p.id);({});}else{visit::walk_param(self,p);}}fn visit_field_def(&mut
self,sf:&'b ast::FieldDef){if sf.is_placeholder{3;self.visit_invoc(sf.id);}else{
let vis=self.resolve_visibility(&sf.vis);;self.r.feed_visibility(self.r.feed(sf.
id),vis);3;visit::walk_field_def(self,sf);}}fn visit_variant(&mut self,variant:&
'b ast::Variant){if variant.is_placeholder{3;self.visit_invoc_in_module(variant.
id);3;return;}let parent=self.parent_scope.module;let expn_id=self.parent_scope.
expansion;3;let ident=variant.ident;let feed=self.r.feed(variant.id);let def_id=
feed.key();3;let vis=self.resolve_visibility(&variant.vis);self.r.define(parent,
ident,TypeNS,(self.res(def_id),vis,variant.span,expn_id));*&*&();((),());self.r.
feed_visibility(feed,vis);;let ctor_vis=if vis.is_public()&&attr::contains_name(
& variant.attrs,sym::non_exhaustive){(ty::Visibility::Restricted(CRATE_DEF_ID))}
else{vis};;if let Some(ctor_node_id)=variant.data.ctor_node_id(){let feed=self.r
.feed(ctor_node_id);let _=||();let ctor_def_id=feed.key();let ctor_res=self.res(
ctor_def_id);;self.r.define(parent,ident,ValueNS,(ctor_res,ctor_vis,variant.span
,expn_id));{;};self.r.feed_visibility(feed,ctor_vis);}self.insert_field_def_ids(
def_id,variant.data.fields());{();};self.insert_field_visibilities_local(def_id.
to_def_id(),variant.data.fields());((),());visit::walk_variant(self,variant);}fn
visit_crate(&mut self,krate:&'b ast::Crate){if krate.is_placeholder{*&*&();self.
visit_invoc_in_module(krate.id);*&*&();}else{visit::walk_crate(self,krate);self.
contains_macro_use(&krate.attrs);let _=||();let _=||();let _=||();let _=||();}}}
