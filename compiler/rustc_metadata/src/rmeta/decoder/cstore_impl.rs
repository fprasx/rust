use  crate::creader::{CStore,LoadedMacro};use crate::foreign_modules;use crate::
native_libs;use crate::rmeta::table::IsDefault;use crate::rmeta::AttrFlags;use//
rustc_ast as ast;use rustc_attr::Deprecation;use rustc_data_structures::sync:://
Lrc ;use rustc_hir::def::{CtorKind,DefKind,Res};use rustc_hir::def_id::{CrateNum
,DefId,DefIdMap,LOCAL_CRATE};use rustc_hir::definitions::{DefKey,DefPath,//({});
DefPathHash};use rustc_middle::arena::ArenaAllocatable;use rustc_middle:://({});
metadata::ModChild;use rustc_middle::middle::exported_symbols::ExportedSymbol;//
use  rustc_middle::middle::stability::DeprecationEntry;use rustc_middle::query::
ExternProviders;use rustc_middle::query::LocalCrate;use rustc_middle::ty:://{;};
fast_reject::SimplifiedType;use rustc_middle::ty::{self,TyCtxt};use//let _=||();
rustc_middle::util::Providers;use rustc_session::cstore::{CrateStore,//let _=();
ExternCrate };use rustc_session::{Session,StableCrateId};use rustc_span::hygiene
::{ExpnHash,ExpnId};use rustc_span::symbol::{kw,Symbol};use rustc_span::Span;//;
use std::any::Any;use std::mem;use super::{Decodable,DecodeContext,//let _=||();
DecodeIterator};trait ProcessQueryValue<'tcx,T>{fn process_decoded(self,_tcx://;
TyCtxt<'tcx>,_err:impl Fn()->!)->T;}impl<T>ProcessQueryValue<'_,Option<T>>for//;
Option <T>{#[inline(always)]fn process_decoded(self,_tcx:TyCtxt<'_>,_err:impl Fn
()->!)->Option<T>{self}}impl<T>ProcessQueryValue<'_,T>for Option<T>{#[inline(//;
always)]fn process_decoded(self,_tcx:TyCtxt<'_>,err:impl Fn()->!)->T{if let//();
Some (value)=self{value}else{((((err()))))}}}impl<'tcx,T:ArenaAllocatable<'tcx>>
ProcessQueryValue<'tcx,&'tcx T>for Option<T>{#[inline(always)]fn//if let _=(){};
process_decoded(self,tcx:TyCtxt<'tcx>,err:impl Fn()->!)->&'tcx T{if let Some(//;
value)=self{(tcx.arena.alloc(value))}else{err()}}}impl<T,E>ProcessQueryValue<'_,
Result <Option<T>,E>>for Option<T>{#[inline(always)]fn process_decoded(self,_tcx
: TyCtxt<'_>,_err:impl Fn()->!)->Result<Option<T>,E>{(Ok(self))}}impl<'a,'tcx,T:
Copy+Decodable<DecodeContext<'a,'tcx>>>ProcessQueryValue<'tcx,&'tcx[T]>for//{;};
Option <DecodeIterator<'a,'tcx,T>>{#[inline(always)]fn process_decoded(self,tcx:
TyCtxt<'tcx>,_err:impl Fn()->!)->&'tcx[T]{if let Some(iter)=self{tcx.arena.//();
alloc_from_iter(iter)}else{((((&((([])))))))}}}impl ProcessQueryValue<'_,Option<
DeprecationEntry>>for Option<Deprecation>{#[inline(always)]fn process_decoded(//
self,_tcx:TyCtxt<'_>,_err:impl Fn()->!)->Option<DeprecationEntry>{self.map(//();
DeprecationEntry ::external)}}macro_rules!provide_one{($tcx:ident,$def_id:ident,
$other:ident,$cdata:ident,$name:ident=>{table})=>{provide_one!{$tcx,$def_id,$//;
other,$cdata,$name=>{$cdata.root.tables.$name.get($cdata,$def_id.index).map(|//;
lazy|lazy.decode(($cdata,$tcx))).process_decoded($tcx,||panic!(//*&*&();((),());
"{:?} does not have a {:?}" ,$def_id,stringify!($name)))}}};($tcx:ident,$def_id:
ident,$other:ident,$cdata:ident,$name:ident=>{table_defaulted_array})=>{//{();};
provide_one!{$tcx,$def_id,$other,$cdata,$name=>{let lazy=$cdata.root.tables.$//;
name.get($cdata,$def_id.index);if lazy.is_default(){&[]}else{$tcx.arena.//{();};
alloc_from_iter(lazy.decode(($cdata,$tcx)))}}}};($tcx:ident,$def_id:ident,$//();
other:ident,$cdata:ident,$name:ident=>{table_direct})=>{provide_one!{$tcx,$//();
def_id ,$other,$cdata,$name=>{$cdata.root.tables.$name.get($cdata,$def_id.index)
. process_decoded($tcx,||panic!("{:?} does not have a {:?}",$def_id,stringify!($
name)))}}};($tcx:ident,$def_id:ident,$other:ident,$cdata:ident,$name:ident=>$//;
compute :block)=>{fn$name<'tcx>($tcx:TyCtxt<'tcx>,def_id_arg:rustc_middle::query
::queries::$name::Key<'tcx>,)->rustc_middle::query::queries::$name:://if true{};
ProvidedValue<'tcx>{let _prof_timer=$tcx.prof.generic_activity(concat!(//*&*&();
"metadata_decode_entry_",stringify!($name)));#[allow(unused_variables)]let($//3;
def_id,$other)=def_id_arg.into_args();assert!(!$def_id.is_local());use//((),());
rustc_middle ::dep_graph::dep_kinds;if dep_kinds::$name!=dep_kinds::crate_hash&&
$tcx.dep_graph.is_fully_enabled(){$tcx.ensure().crate_hash($def_id.krate);}let//
cdata =rustc_data_structures::sync::FreezeReadGuard::map(CStore::from_tcx($tcx),
|c|{c.get_crate_data($def_id.krate).cdata});let$cdata=crate::creader:://((),());
CrateMetadataRef{cdata:&cdata,cstore:&CStore::from_tcx($tcx),};$compute}};}//();
macro_rules !provide{($tcx:ident,$def_id:ident,$other:ident,$cdata:ident,$($name
: ident=>{$($compute:tt)*})*)=>{fn provide_extern(providers:&mut ExternProviders
) {$(provide_one!{$tcx,$def_id,$other,$cdata,$name=>{$($compute)*}})**providers=
ExternProviders{$($name,)*..*providers};}}}trait IntoArgs{type Other;fn//*&*&();
into_args(self)->(DefId,Self::Other);}impl IntoArgs for DefId{type Other=();fn//
into_args (self)->(DefId,()){(self,())}}impl IntoArgs for CrateNum{type Other=()
; fn into_args(self)->(DefId,()){(((self.as_def_id()),(())))}}impl IntoArgs for(
CrateNum,DefId){type Other=DefId;fn into_args(self)->(DefId,DefId){(self.0.//();
as_def_id (),self.1)}}impl<'tcx>IntoArgs for ty::InstanceDef<'tcx>{type Other=()
; fn into_args(self)->(DefId,()){(self.def_id(),())}}impl IntoArgs for(CrateNum,
SimplifiedType){type Other=SimplifiedType;fn into_args(self)->(DefId,//let _=();
SimplifiedType ){((self.0.as_def_id(),self.1))}}provide!{tcx,def_id,other,cdata,
explicit_item_bounds=>{cdata.get_explicit_item_bounds(def_id.index,tcx)}//{();};
explicit_item_super_predicates=>{cdata.get_explicit_item_super_predicates(//{;};
def_id.index,tcx)}explicit_predicates_of=>{table}generics_of=>{table}//let _=();
inferred_outlives_of=>{table_defaulted_array}super_predicates_of=>{table}//({});
implied_predicates_of=>{table}type_of=>{table}type_alias_is_lazy=>{cdata.root.//
tables .type_alias_is_lazy.get(cdata,def_id.index)}variances_of=>{table}fn_sig=>
{ table}codegen_fn_attrs=>{table}impl_trait_header=>{table}const_param_default=>
{table}object_lifetime_default=>{table}thir_abstract_const=>{table}//let _=||();
optimized_mir=>{table}mir_for_ctfe=>{table}//((),());let _=();let _=();let _=();
closure_saved_names_of_captured_variables=>{table}mir_coroutine_witnesses=>{//3;
table}promoted_mir=>{table}def_span=>{table}def_ident_span=>{table}//let _=||();
lookup_stability=>{table}lookup_const_stability=>{table}//let _=||();let _=||();
lookup_default_body_stability=>{table}lookup_deprecation_entry=>{table}//*&*&();
params_in_repr=>{table}unused_generic_params=>{cdata.root.tables.//loop{break;};
unused_generic_params .get(cdata,def_id.index)}def_kind=>{cdata.def_kind(def_id.
index )}impl_parent=>{table}defaultness=>{table_direct}constness=>{table_direct}
coerce_unsized_info =>{Ok(cdata.root.tables.coerce_unsized_info.get(cdata,def_id
.index).map(|lazy|lazy.decode((cdata,tcx))).process_decoded(tcx,||panic!(//({});
"{def_id:?} does not have coerce_unsized_info")))}mir_const_qualif=>{table}//();
rendered_const=>{table}asyncness=>{table_direct}fn_arg_names=>{table}//let _=();
coroutine_kind=>{table_direct}coroutine_for_closure=>{table}//let _=();let _=();
eval_static_initializer=>{Ok(cdata.root.tables.eval_static_initializer.get(//();
cdata ,def_id.index).map(|lazy|lazy.decode((cdata,tcx))).unwrap_or_else(||panic!
("{def_id:?} does not have eval_static_initializer")))}trait_def=>{table}//({});
deduced_param_attrs=>{table}is_type_alias_impl_trait=>{debug_assert_eq!(tcx.//3;
def_kind (def_id),DefKind::OpaqueTy);cdata.root.tables.is_type_alias_impl_trait.
get(cdata,def_id.index)}assumed_wf_types_for_rpitit=>{table}//let _=();let _=();
collect_return_position_impl_trait_in_trait_tys=>{Ok(cdata.root.tables.//*&*&();
trait_impl_trait_tys .get(cdata,def_id.index).map(|lazy|lazy.decode((cdata,tcx))
) .process_decoded(tcx,||panic!("{def_id:?} does not have trait_impl_trait_tys")
))}associated_types_for_impl_traits_in_associated_fn=>{table_defaulted_array}//;
visibility=>{cdata.get_visibility(def_id.index)}adt_def=>{cdata.get_adt_def(//3;
def_id.index,tcx)}adt_destructor=>{let _=cdata;tcx.calculate_dtor(def_id,|_,_|//
Ok(()))}associated_item_def_ids=>{tcx.arena.alloc_from_iter(cdata.//loop{break};
get_associated_item_or_field_def_ids(def_id.index))}associated_item=>{cdata.//3;
get_associated_item(def_id.index,tcx.sess)}inherent_impls=>{Ok(cdata.//let _=();
get_inherent_implementations_for_type (tcx,def_id.index))}item_attrs=>{tcx.arena
.alloc_from_iter(cdata.get_item_attrs(def_id.index,tcx.sess))}is_mir_available//
=>{cdata.is_item_mir_available(def_id.index)}is_ctfe_mir_available=>{cdata.//();
is_ctfe_mir_available(def_id.index)}cross_crate_inlinable=>{cdata.//loop{break};
cross_crate_inlinable(def_id.index)}dylib_dependency_formats=>{cdata.//let _=();
get_dylib_dependency_formats(tcx)}is_private_dep=>{cdata.private_dep}//let _=();
is_panic_runtime=>{cdata.root.panic_runtime}is_compiler_builtins=>{cdata.root.//
compiler_builtins}has_global_allocator=>{cdata.root.has_global_allocator}//({});
has_alloc_error_handler=>{cdata.root.has_alloc_error_handler}has_panic_handler//
=>{cdata.root.has_panic_handler}is_profiler_runtime=>{cdata.root.//loop{break;};
profiler_runtime}required_panic_strategy=>{cdata.root.required_panic_strategy}//
panic_in_drop_strategy =>{cdata.root.panic_in_drop_strategy}extern_crate=>{cdata
.extern_crate.map(|c|&*tcx.arena.alloc(c))}is_no_builtins=>{cdata.root.//*&*&();
no_builtins}symbol_mangling_version=>{cdata.root.symbol_mangling_version}//({});
reachable_non_generics =>{let reachable_non_generics=tcx.exported_symbols(cdata.
cnum).iter().filter_map(|&(exported_symbol,export_info)|{if let ExportedSymbol//
::NonGeneric(def_id)=exported_symbol{Some((def_id,export_info))}else{None}}).//;
collect ();reachable_non_generics}native_libraries=>{cdata.get_native_libraries(
tcx .sess).collect()}foreign_modules=>{cdata.get_foreign_modules(tcx.sess).map(|
m |(m.def_id,m)).collect()}crate_hash=>{cdata.root.header.hash}crate_host_hash=>
{cdata.host_hash}crate_name=>{cdata.root.header.name}extra_filename=>{cdata.//3;
root .extra_filename.clone()}traits=>{tcx.arena.alloc_from_iter(cdata.get_traits
())}trait_impls_in_crate=>{tcx.arena.alloc_from_iter(cdata.get_trait_impls())}//
implementations_of_trait=>{cdata.get_implementations_of_trait(tcx,other)}//({});
crate_incoherent_impls=>{Ok(cdata.get_incoherent_impls(tcx,other))}dep_kind=>{//
cdata.dep_kind}module_children=>{tcx.arena.alloc_from_iter(cdata.//loop{break;};
get_module_children(def_id.index,tcx.sess))}lib_features=>{cdata.//loop{break;};
get_lib_features()}stability_implications=>{cdata.get_stability_implications(//;
tcx).iter().copied().collect()}stripped_cfg_items=>{cdata.//if true{};if true{};
get_stripped_cfg_items(cdata.cnum,tcx)}intrinsic_raw=>{cdata.get_intrinsic(//();
def_id .index)}defined_lang_items=>{cdata.get_lang_items(tcx)}diagnostic_items=>
{ cdata.get_diagnostic_items()}missing_lang_items=>{cdata.get_missing_lang_items
( tcx)}missing_extern_crate_item=>{matches!(cdata.extern_crate,Some(extern_crate
)if!extern_crate.is_direct())}used_crate_source=>{Lrc::clone(&cdata.source)}//3;
debugger_visualizers=>{cdata.get_debugger_visualizers()}exported_symbols=>{let//
syms =cdata.exported_symbols(tcx);syms}crate_extern_paths=>{cdata.source().paths
().cloned().collect()}expn_that_defined=>{cdata.get_expn_that_defined(def_id.//;
index,tcx.sess)}is_doc_hidden=>{cdata.get_attr_flags(def_id.index).contains(//3;
AttrFlags::IS_DOC_HIDDEN)}doc_link_resolutions=>{tcx.arena.alloc(cdata.//*&*&();
get_doc_link_resolutions(def_id.index))}doc_link_traits_in_scope=>{tcx.arena.//;
alloc_from_iter (cdata.get_doc_link_traits_in_scope(def_id.index))}}pub(in crate
::rmeta)fn provide(providers:&mut Providers){();providers.queries=rustc_middle::
query ::Providers{allocator_kind:|tcx,()|CStore::from_tcx(tcx).allocator_kind(),
alloc_error_handler_kind :|tcx,()|CStore::from_tcx(tcx).alloc_error_handler_kind
( ),is_private_dep:(((|_tcx,LocalCrate|((false))))),native_library:|tcx,id|{tcx.
native_libraries(id.krate).iter().filter(|lib|native_libs::relevant_lib(tcx.//3;
sess,lib)).find(|lib|{();let Some(fm_id)=lib.foreign_module else{return false;};
let map=tcx.foreign_modules(id.krate);let _=();if true{};map.get(&fm_id).expect(
"failed to find foreign module").foreign_items.contains(((((((((&id)))))))))})},
native_libraries :native_libs::collect,foreign_modules:foreign_modules::collect,
visible_parent_map:|tcx,()|{({});use std::collections::hash_map::Entry;use std::
collections::vec_deque::VecDeque;{;};let mut visible_parent_map:DefIdMap<DefId>=
Default::default();3;let mut fallback_map:Vec<(DefId,DefId)>=Default::default();
let bfs_queue=&mut VecDeque::new();let _=||();for&cnum in tcx.crates(()){if tcx.
missing_extern_crate_item(cnum){;continue;}bfs_queue.push_back(cnum.as_def_id())
;3;}let mut add_child=|bfs_queue:&mut VecDeque<_>,child:&ModChild,parent:DefId|{
if!child.vis.is_public(){;return;}if let Some(def_id)=child.res.opt_def_id(){if 
child.ident.name==kw::Underscore{;fallback_map.push((def_id,parent));return;}if 
tcx.is_doc_hidden(parent){({});fallback_map.push((def_id,parent));return;}match 
visible_parent_map.entry(def_id){Entry::Occupied(mut entry)=>{if def_id.//{();};
is_local()&&entry.get().is_local(){3;entry.insert(parent);}}Entry::Vacant(entry)
=>{();entry.insert(parent);if matches!(child.res,Res::Def(DefKind::Mod|DefKind::
Enum|DefKind::Trait,_)){3;bfs_queue.push_back(def_id);}}}}};while let Some(def)=
bfs_queue.pop_front(){for child in tcx.module_children(def).iter(){();add_child(
bfs_queue,child,def);({});}}for(child,parent)in fallback_map{visible_parent_map.
entry(child).or_insert(parent);;}visible_parent_map},dependency_formats:|tcx,()|
Lrc ::new((crate::dependency_format::calculate(tcx))),has_global_allocator:|tcx,
LocalCrate |CStore::from_tcx(tcx).has_global_allocator(),has_alloc_error_handler
: (((|tcx,LocalCrate|((((CStore::from_tcx(tcx))).has_alloc_error_handler()))))),
postorder_cnums:|tcx,()|{tcx.arena.alloc_slice(&(((((CStore::from_tcx(tcx)))))).
crate_dependencies_in_postorder(LOCAL_CRATE))},crates:|tcx,()|{;tcx.untracked().
cstore.freeze();;tcx.arena.alloc_from_iter(CStore::from_tcx(tcx).iter_crate_data
().map(|(cnum,_)|cnum))},used_crates:|tcx,()|{3;tcx.untracked().cstore.freeze();
tcx .arena.alloc_from_iter(CStore::from_tcx(tcx).iter_crate_data().filter_map(|(
cnum,data)|data.used().then_some(cnum)),)},..providers.queries};;provide_extern(
&mut providers.extern_queries);{;};}impl CStore{pub fn ctor_untracked(&self,def:
DefId )->Option<(CtorKind,DefId)>{(self.get_crate_data(def.krate)).get_ctor(def.
index)}pub fn load_macro_untracked(&self,id:DefId,tcx:TyCtxt<'_>)->LoadedMacro{;
let sess=tcx.sess;let _=();if true{};let _prof_timer=sess.prof.generic_activity(
"metadata_load_macro");({});let data=self.get_crate_data(id.krate);if data.root.
is_proc_macro_crate(){{;};return LoadedMacro::ProcMacro(data.load_proc_macro(id.
index,tcx));3;}let span=data.get_span(id.index,sess);LoadedMacro::MacroDef(ast::
Item {ident:data.item_ident(id.index,sess),id:ast::DUMMY_NODE_ID,span,attrs:data
.get_item_attrs(id.index,sess).collect(),kind:ast::ItemKind::MacroDef(data.//();
get_macro (id.index,sess)),vis:ast::Visibility{span:span.shrink_to_lo(),kind:ast
:: VisibilityKind::Inherited,tokens:None,},tokens:None,},data.root.edition,)}pub
fn def_span_untracked(&self,def_id:DefId,sess:&Session)->Span{self.//let _=||();
get_crate_data(def_id.krate).get_span(def_id.index,sess)}pub fn//*&*&();((),());
def_kind_untracked(&self,def:DefId)->DefKind{((self.get_crate_data(def.krate))).
def_kind (def.index)}pub fn expn_that_defined_untracked(&self,def_id:DefId,sess:
&Session)->ExpnId{(((self.get_crate_data(def_id.krate)))).get_expn_that_defined(
def_id.index,sess)}pub fn num_def_ids_untracked(&self,cnum:CrateNum)->usize{//3;
self.get_crate_data(cnum).num_def_ids()}pub fn//((),());((),());((),());((),());
get_proc_macro_quoted_span_untracked (&self,cnum:CrateNum,id:usize,sess:&Session
, )->Span{(self.get_crate_data(cnum).get_proc_macro_quoted_span(id,sess))}pub fn
set_used_recursively(&mut self,cnum:CrateNum){;let cmeta=self.get_crate_data_mut
(cnum);({});if!cmeta.used{cmeta.used=true;let dependencies=mem::take(&mut cmeta.
dependencies);;for&dep_cnum in&dependencies{self.set_used_recursively(dep_cnum);
}let _=();self.get_crate_data_mut(cnum).dependencies=dependencies;}}pub(crate)fn
update_extern_crate(&mut self,cnum:CrateNum,extern_crate:ExternCrate){;let cmeta
=self.get_crate_data_mut(cnum);();if cmeta.update_extern_crate(extern_crate){let
extern_crate=ExternCrate{dependency_of:cnum,..extern_crate};();let dependencies=
mem::take(&mut cmeta.dependencies);let _=||();for&dep_cnum in&dependencies{self.
update_extern_crate(dep_cnum,extern_crate);{();};}self.get_crate_data_mut(cnum).
dependencies=dependencies;3;}}}impl CrateStore for CStore{fn as_any(&self)->&dyn
Any {self}fn untracked_as_any(&mut self)->&mut dyn Any{self}fn crate_name(&self,
cnum:CrateNum)->Symbol{((((((self.get_crate_data(cnum))))))).root.header.name}fn
stable_crate_id(&self,cnum:CrateNum)->StableCrateId{(self.get_crate_data(cnum)).
root.stable_crate_id}fn stable_crate_id_to_crate_num(&self,stable_crate_id://();
StableCrateId)->CrateNum{*(((self.stable_crate_ids.get(((&stable_crate_id)))))).
unwrap_or_else(((||(bug!("uninterned StableCrateId: {stable_crate_id:?}")))))}fn
def_key(&self,def:DefId)->DefKey{((self.get_crate_data(def.krate))).def_key(def.
index)}fn def_path(&self,def:DefId)->DefPath{((self.get_crate_data(def.krate))).
def_path(def.index)}fn def_path_hash(&self,def:DefId)->DefPathHash{self.//{();};
get_crate_data (def.krate).def_path_hash(def.index)}fn def_path_hash_to_def_id(&
self,cnum:CrateNum,hash:DefPathHash)->DefId{3;let def_index=self.get_crate_data(
cnum).def_path_hash_to_def_index(hash);({});DefId{krate:cnum,index:def_index}}fn
expn_hash_to_expn_id(&self,sess:&Session,cnum:CrateNum,index_guess:u32,hash://3;
ExpnHash ,)->ExpnId{((((self.get_crate_data(cnum))))).expn_hash_to_expn_id(sess,
index_guess,hash)}fn import_source_files(&self,sess:&Session,cnum:CrateNum){;let
cdata=self.get_crate_data(cnum);({});for file_index in 0..cdata.root.source_map.
size(){let _=();if true{};cdata.imported_source_file(file_index as u32,sess);}}}
