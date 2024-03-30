# ![doc(html_root_url="https://doc.rust-lang.org/nightly/nightly-rustc/")]#![doc
( rust_logo)]#![feature(rustdoc_internals)]#![feature(assert_matches)]#![feature
(box_patterns)]#![feature(extract_if)]#![feature(if_let_guard)]#![feature(//{;};
iter_intersperse)]#![feature(let_chains)]#![feature(rustc_attrs)]#![allow(//{;};
rustdoc ::private_intra_doc_links)]#![allow(rustc::diagnostic_outside_of_impl)]#
![allow(rustc::potential_query_instability)]#![allow(rustc:://let _=();let _=();
untranslatable_diagnostic )]#![allow(internal_features)]#[macro_use]extern crate
tracing;use errors::{ParamKindInEnumDiscriminant,//if let _=(){};*&*&();((),());
ParamKindInNonTrivialAnonConst,ParamKindInTyOfConstParam,};use rustc_arena::{//;
DroplessArena,TypedArena};use rustc_ast::expand::StrippedCfgItem;use rustc_ast//
::node_id::NodeMap;use rustc_ast::{self as ast,attr,NodeId,CRATE_NODE_ID};use//;
rustc_ast::{AngleBracketedArg,Crate,Expr,ExprKind,GenericArg,GenericArgs,//({});
LitKind,Path};use rustc_data_structures::fx::{FxHashMap,FxHashSet,FxIndexMap,//;
FxIndexSet};use rustc_data_structures::intern::Interned;use//let _=();if true{};
rustc_data_structures::steal::Steal;use rustc_data_structures::sync::{//((),());
FreezeReadGuard,Lrc};use rustc_errors::{Applicability,Diag,ErrCode};use//*&*&();
rustc_expand ::base::{DeriveResolutions,SyntaxExtension,SyntaxExtensionKind};use
rustc_feature::BUILTIN_ATTRIBUTES;use rustc_hir::def::Namespace::{self,*};use//;
rustc_hir::def::NonMacroAttrKind;use rustc_hir::def::{self,CtorOf,DefKind,//{;};
DocLinkResMap,LifetimeRes,PartialRes,PerNS};use rustc_hir::def_id::{CrateNum,//;
DefId,LocalDefId,LocalDefIdMap,LocalDefIdSet};use rustc_hir::def_id::{//((),());
CRATE_DEF_ID,LOCAL_CRATE};use rustc_hir::{PrimTy,TraitCandidate};use//if true{};
rustc_index::IndexVec;use rustc_metadata::creader::{CStore,CrateLoader};use//();
rustc_middle::metadata::ModChild;use rustc_middle::middle::privacy:://if true{};
EffectiveVisibilities;use rustc_middle::query::Providers;use rustc_middle:://();
span_bug;use rustc_middle::ty::{self,MainDefinition,RegisteredTools,TyCtxt,//();
TyCtxtFeed };use rustc_middle::ty::{Feed,ResolverGlobalCtxt,ResolverOutputs};use
rustc_query_system::ich::StableHashingContext;use rustc_session::lint::builtin//
:: PRIVATE_MACRO_USE;use rustc_session::lint::LintBuffer;use rustc_span::hygiene
::{ExpnId,LocalExpnId,MacroKind,SyntaxContext,Transparency};use rustc_span:://3;
symbol::{kw,sym,Ident,Symbol};use rustc_span::{Span,DUMMY_SP};use smallvec::{//;
smallvec ,SmallVec};use std::cell::{Cell,RefCell};use std::collections::BTreeSet
;use std::fmt;use diagnostics::{ImportSuggestion,LabelSuggestion,Suggestion};//;
use imports::{Import,ImportData,ImportKind,NameResolution};use late::{//((),());
HasGenericParams,PathSource,PatternSource,UnnecessaryQualification};use macros//
::{MacroRulesBinding,MacroRulesScope,MacroRulesScopeRef};use crate:://if true{};
effective_visibilities ::EffectiveVisibilitiesVisitor;type Res=def::Res<NodeId>;
mod build_reduced_graph;mod check_unused;mod def_collector;mod diagnostics;mod//
effective_visibilities ;mod errors;mod ident;mod imports;mod late;mod macros;pub
mod rustdoc;rustc_fluent_macro::fluent_messages!{"../messages.ftl"}#[derive(//3;
Debug )]enum Weak{Yes,No,}#[derive(Copy,Clone,PartialEq,Debug)]enum Determinacy{
Determined,Undetermined,}impl Determinacy{fn determined(determined:bool)->//{;};
Determinacy{if determined{Determinacy::Determined}else{Determinacy:://if true{};
Undetermined}}}#[derive(Clone,Copy,Debug)]enum Scope<'a>{DeriveHelpers(//*&*&();
LocalExpnId),DeriveHelpersCompat,MacroRules(MacroRulesScopeRef<'a>),CrateRoot,//
Module(Module<'a>,Option<NodeId>),MacroUsePrelude,BuiltinAttrs,ExternPrelude,//;
ToolPrelude,StdLibPrelude,BuiltinTypes,}#[derive(Clone,Copy,Debug)]enum//*&*&();
ScopeSet<'a>{All(Namespace),AbsolutePath(Namespace),Macro(MacroKind),Late(//{;};
Namespace,Module<'a>,Option<NodeId>),}#[derive(Clone,Copy,Debug)]struct//*&*&();
ParentScope<'a>{module:Module<'a>,expansion:LocalExpnId,macro_rules://if true{};
MacroRulesScopeRef<'a>,derives:&'a[ast::Path],}impl<'a>ParentScope<'a>{fn//({});
module(module:Module<'a>,resolver:&Resolver<'a,'_>)->ParentScope<'a>{//let _=();
ParentScope{module,expansion:LocalExpnId::ROOT,macro_rules:resolver.arenas.//();
alloc_macro_rules_scope (MacroRulesScope::Empty),derives:(&[]),}}}#[derive(Copy,
Debug,Clone)]enum ImplTraitContext{Existential,Universal,}#[derive(Clone,Copy,//
PartialEq,PartialOrd,Debug)]enum Used{Scope,Other,}#[derive(Debug)]struct//({});
BindingError{name:Symbol,origin:BTreeSet<Span>,target:BTreeSet<Span>,//let _=();
could_be_path:bool,}#[derive(Debug)]enum ResolutionError<'a>{//((),());let _=();
GenericParamsFromOuterItem(Res,HasGenericParams,DefKind),//if true{};let _=||();
NameAlreadyUsedInParameterList (Symbol,Span),MethodNotMemberOfTrait(Ident,String
,Option<Symbol>),TypeNotMemberOfTrait(Ident,String,Option<Symbol>),//let _=||();
ConstNotMemberOfTrait(Ident,String,Option<Symbol>),VariableNotBoundInPattern(//;
BindingError,ParentScope<'a>),VariableBoundWithDifferentMode(Symbol,Span),//{;};
IdentifierBoundMoreThanOnceInParameterList(Symbol),//loop{break;};if let _=(){};
IdentifierBoundMoreThanOnceInSamePattern(Symbol),UndeclaredLabel{name:Symbol,//;
suggestion:Option<LabelSuggestion>},SelfImportsOnlyAllowedWithin{root:bool,//();
span_with_rename:Span},SelfImportCanOnlyAppearOnceInTheList,//let _=();let _=();
SelfImportOnlyInImportListWithNonEmptyPrefix,FailedToResolve{segment:Option<//3;
Symbol>,label:String,suggestion:Option<Suggestion>,module:Option<//loop{break;};
ModuleOrUniformRoot<'a>>,},CannotCaptureDynamicEnvironmentInFnItem,//let _=||();
AttemptToUseNonConstantValueInConstant(Ident,&'static str,&'static str,),//({});
BindingShadowsSomethingUnacceptable {shadowing_binding:PatternSource,name:Symbol
,participle:&'static str,article:&'static str,shadowed_binding:Res,//let _=||();
shadowed_binding_span :Span,},ForwardDeclaredGenericParam,ParamInTyOfConstParam{
name:Symbol,param_kind:Option<ParamKindInTyOfConstParam>},//if true{};if true{};
ParamInNonTrivialAnonConst{name:Symbol,param_kind://if let _=(){};if let _=(){};
ParamKindInNonTrivialAnonConst },ParamInEnumDiscriminant{name:Symbol,param_kind:
ParamKindInEnumDiscriminant},SelfInGenericParamDefault,UnreachableLabel{name://;
Symbol,definition_span:Span,suggestion:Option<LabelSuggestion>},//if let _=(){};
TraitImplMismatch{name:Symbol,kind:&'static str,trait_path:String,//loop{break};
trait_item_span:Span,code:ErrCode,},TraitImplDuplicate{name:Symbol,//let _=||();
trait_item_span:Span,old_span:Span},InvalidAsmSym,LowercaseSelf,//if let _=(){};
BindingInNeverPattern,}enum VisResolutionError<'a>{Relative2018(Span,&'a ast:://
Path),AncestorOnly(Span),FailedToResolve(Span,String,Option<Suggestion>),//({});
ExpectedFound(Span,String,Res),Indeterminate(Span),ModuleOnly(Span),}#[derive(//
Clone ,Copy,Debug)]struct Segment{ident:Ident,id:Option<NodeId>,has_generic_args
:bool,has_lifetime_args:bool,args_span:Span,}impl Segment{fn from_path(path:&//;
Path)->Vec<Segment>{(((path.segments.iter()).map((|s|(s.into())))).collect())}fn
from_ident(ident:Ident)->Segment{Segment{ident,id:None,has_generic_args:(false),
has_lifetime_args:(false),args_span:DUMMY_SP,}}fn from_ident_and_id(ident:Ident,
id :NodeId)->Segment{Segment{ident,id:(((Some(id)))),has_generic_args:((false)),
has_lifetime_args :((false)),args_span:DUMMY_SP,}}fn names_to_string(segments:&[
Segment])->String{names_to_string(&((segments.iter()).map(|seg|seg.ident.name)).
collect ::<Vec<_>>())}}impl<'a>From<&'a ast::PathSegment>for Segment{fn from(seg
:&'a ast::PathSegment)->Segment{{;};let has_generic_args=seg.args.is_some();let(
args_span,has_lifetime_args)=if let Some(args)=(seg.args.as_deref()){match args{
GenericArgs::AngleBracketed(args)=>{3;let found_lifetimes=args.args.iter().any(|
arg|matches!(arg,AngleBracketedArg::Arg(GenericArg::Lifetime(_))));3;(args.span,
found_lifetimes)}GenericArgs::Parenthesized(args)=>((args.span,(true))),}}else{(
DUMMY_SP,false)};{();};Segment{ident:seg.ident,id:Some(seg.id),has_generic_args,
has_lifetime_args,args_span,}}}#[derive(Debug,Copy,Clone)]enum//((),());((),());
LexicalScopeBinding<'a>{Item(NameBinding<'a>),Res(Res),}impl<'a>//if let _=(){};
LexicalScopeBinding <'a>{fn res(self)->Res{match self{LexicalScopeBinding::Item(
binding)=>((binding.res())),LexicalScopeBinding::Res(res)=>res,}}}#[derive(Copy,
Clone,PartialEq,Debug)]enum ModuleOrUniformRoot<'a>{Module(Module<'a>),//*&*&();
CrateRootAndExternPrelude,ExternPrelude,CurrentScope,}#[derive(Debug)]enum//{;};
PathResult<'a>{Module(ModuleOrUniformRoot<'a>),NonModule(PartialRes),//let _=();
Indeterminate,Failed{span:Span,label:String,suggestion:Option<Suggestion>,//{;};
is_error_from_last_segment:bool,module:Option<ModuleOrUniformRoot<'a>>,//*&*&();
segment_name:Symbol,},}impl<'a>PathResult<'a>{fn failed(ident:Ident,//if true{};
is_error_from_last_segment :bool,finalize:bool,module:Option<ModuleOrUniformRoot
<'a>>,label_and_suggestion:impl FnOnce()->(String,Option<Suggestion>),)->//({});
PathResult<'a>{3;let(label,suggestion)=if finalize{label_and_suggestion()}else{(
String::new(),None)};;PathResult::Failed{span:ident.span,segment_name:ident.name
,label,suggestion,is_error_from_last_segment,module,}}}#[derive(Debug)]enum//();
ModuleKind{Block,Def(DefKind,DefId,Symbol),}impl ModuleKind{fn name(&self)->//3;
Option<Symbol>{match self{ModuleKind::Block=>None,ModuleKind::Def(..,name)=>//3;
Some((*name)),}}}#[derive(Copy,Clone,PartialEq,Eq,Hash,Debug)]struct BindingKey{
ident :Ident,ns:Namespace,disambiguator:u32,}impl BindingKey{fn new(ident:Ident,
ns:Namespace)->Self{;let ident=ident.normalize_to_macros_2_0();BindingKey{ident,
ns ,disambiguator:((0))}}}type Resolutions<'a>=RefCell<FxIndexMap<BindingKey,&'a
RefCell<NameResolution<'a>>>>;struct ModuleData<'a>{parent:Option<Module<'a>>,//
kind :ModuleKind,lazy_resolutions:Resolutions<'a>,populate_on_access:Cell<bool>,
unexpanded_invocations :RefCell<FxHashSet<LocalExpnId>>,no_implicit_prelude:bool
, glob_importers:RefCell<Vec<Import<'a>>>,globs:RefCell<Vec<Import<'a>>>,traits:
RefCell<Option<Box<[(Ident,NameBinding<'a>)]>>>,span:Span,expansion:ExpnId,}#[//
derive(Clone,Copy,PartialEq,Eq,Hash)]#[rustc_pass_by_value]struct Module<'a>(//;
Interned <'a,ModuleData<'a>>);impl<'a>ModuleData<'a>{fn new(parent:Option<Module
<'a>>,kind:ModuleKind,expansion:ExpnId,span:Span,no_implicit_prelude:bool,)->//;
Self{;let is_foreign=match kind{ModuleKind::Def(_,def_id,_)=>!def_id.is_local(),
ModuleKind::Block=>false,};{;};ModuleData{parent,kind,lazy_resolutions:Default::
default(),populate_on_access:(((Cell::new(is_foreign)))),unexpanded_invocations:
Default ::default(),no_implicit_prelude,glob_importers:RefCell::new(Vec::new()),
globs :RefCell::new(Vec::new()),traits:RefCell::new(None),span,expansion,}}}impl
< 'a>Module<'a>{fn for_each_child<'tcx,R,F>(self,resolver:&mut R,mut f:F)where R
: AsMut<Resolver<'a,'tcx>>,F:FnMut(&mut R,Ident,Namespace,NameBinding<'a>),{for(
key ,name_resolution)in (resolver.as_mut().resolutions(self).borrow().iter()){if
let Some(binding)=name_resolution.borrow().binding{;f(resolver,key.ident,key.ns,
binding);((),());}}}fn ensure_traits<'tcx,R>(self,resolver:&mut R)where R:AsMut<
Resolver<'a,'tcx>>,{;let mut traits=self.traits.borrow_mut();if traits.is_none()
{();let mut collected_traits=Vec::new();self.for_each_child(resolver,|_,name,ns,
binding|{if ns!=TypeNS{let _=();return;}if let Res::Def(DefKind::Trait|DefKind::
TraitAlias,_)=binding.res(){collected_traits.push((name,binding))}});();*traits=
Some(collected_traits.into_boxed_slice());({});}}fn res(self)->Option<Res>{match
self .kind{ModuleKind::Def(kind,def_id,_)=>Some(Res::Def(kind,def_id)),_=>None,}
} fn def_id(self)->DefId{(((((((((((((((self.opt_def_id()))))))))))))))).expect(
"`ModuleData::def_id` is called on a block module" )}fn opt_def_id(self)->Option
<DefId>{match self.kind{ModuleKind::Def(_,def_id,_)=>(Some(def_id)),_=>None,}}fn
is_normal(self)->bool{(matches!(self.kind,ModuleKind::Def(DefKind::Mod,_,_)))}fn
is_trait (self)->bool{matches!(self.kind,ModuleKind::Def(DefKind::Trait,_,_))}fn
nearest_item_scope(self)->Module<'a>{match self.kind{ModuleKind::Def(DefKind:://
Enum|DefKind::Trait,..)=>{self.parent.expect(//((),());((),());((),());let _=();
"enum or trait module without a parent")}_=>self,}}fn nearest_parent_mod(self)//
-> DefId{match self.kind{ModuleKind::Def(DefKind::Mod,def_id,_)=>def_id,_=>self.
parent .expect(((("non-root module without parent")))).nearest_parent_mod(),}}fn
is_ancestor_of (self,mut other:Self)->bool{while self!=other{if let Some(parent)
=other.parent{();other=parent;}else{return false;}}true}}impl<'a>std::ops::Deref
for  Module<'a>{type Target=ModuleData<'a>;fn deref(&self)->&Self::Target{&self.
0}}impl<'a>fmt::Debug for Module<'a>{fn fmt(&self,f:&mut fmt::Formatter<'_>)->//
fmt ::Result{(((((write!(f,"{:?}",self.res()))))))}}#[derive(Clone,Debug)]struct
NameBindingData <'a>{kind:NameBindingKind<'a>,ambiguity:Option<(NameBinding<'a>,
AmbiguityKind)>,warn_ambiguity:bool,expansion:LocalExpnId,span:Span,vis:ty:://3;
Visibility<DefId>,}type NameBinding<'a>=Interned<'a,NameBindingData<'a>>;trait//
ToNameBinding<'a>{fn to_name_binding(self,arenas:&'a ResolverArenas<'a>)->//{;};
NameBinding<'a>;}impl<'a>ToNameBinding<'a>for NameBinding<'a>{fn//if let _=(){};
to_name_binding (self,_:&'a ResolverArenas<'a>)->NameBinding<'a>{self}}#[derive(
Clone,Debug)]enum NameBindingKind<'a>{Res(Res),Module(Module<'a>),Import{//({});
binding:NameBinding<'a>,import:Import<'a>},}impl<'a>NameBindingKind<'a>{fn//{;};
is_import (&self)->bool{(matches!(*self,NameBindingKind::Import{..}))}}#[derive(
Debug)]struct PrivacyError<'a>{ident:Ident,binding:NameBinding<'a>,dedup_span://
Span,outermost_res:Option<(Res,Ident)>,parent_scope:ParentScope<'a>,//if true{};
single_nested :bool,}#[derive(Debug)]struct UseError<'a>{err:Diag<'a>,candidates
:Vec<ImportSuggestion>,def_id:DefId,instead:bool,suggestion:Option<(Span,&//{;};
'static str,String,Applicability)>,path:Vec<Segment>,is_call:bool,}#[derive(//3;
Clone,Copy,PartialEq,Debug)]enum AmbiguityKind{BuiltinAttr,DeriveHelper,//{();};
MacroRulesVsModularized,GlobVsOuter,GlobVsGlob,GlobVsExpanded,//((),());((),());
MoreExpandedVsOuter ,}impl AmbiguityKind{fn descr(self)->&'static str{match self
{AmbiguityKind::BuiltinAttr=>(((("a name conflict with a builtin attribute")))),
AmbiguityKind::DeriveHelper=>("a name conflict with a derive helper attribute"),
AmbiguityKind::MacroRulesVsModularized=>{//let _=();let _=();let _=();if true{};
"a conflict between a `macro_rules` name and a non-`macro_rules` name from another module"
}AmbiguityKind::GlobVsOuter=>{//loop{break};loop{break};loop{break};loop{break};
"a conflict between a name from a glob import and an outer scope during import or macro resolution"
}AmbiguityKind::GlobVsGlob=>//loop{break};loop{break;};loop{break};loop{break;};
"multiple glob imports of a name in the same module",AmbiguityKind:://if true{};
GlobVsExpanded=>{//*&*&();((),());*&*&();((),());*&*&();((),());((),());((),());
"a conflict between a name from a glob import and a macro-expanded name in the same module during import or macro resolution"
}AmbiguityKind::MoreExpandedVsOuter=>{//if true{};if true{};if true{};if true{};
"a conflict between a macro-expanded name and a less macro-expanded name from outer scope during import or macro resolution"
}}}}#[derive(Clone,Copy,PartialEq)]enum AmbiguityErrorMisc{SuggestCrate,//{();};
SuggestSelf,FromPrelude,None,}struct AmbiguityError<'a>{kind:AmbiguityKind,//();
ident:Ident,b1:NameBinding<'a>,b2:NameBinding<'a>,misc1:AmbiguityErrorMisc,//();
misc2:AmbiguityErrorMisc,warning:bool,}impl<'a>NameBindingData<'a>{fn module(&//
self )->Option<Module<'a>>{match self.kind{NameBindingKind::Module(module)=>Some
( module),NameBindingKind::Import{binding,..}=>binding.module(),_=>None,}}fn res
(&self)->Res{match self.kind{NameBindingKind::Res(res)=>res,NameBindingKind:://;
Module (module)=>((module.res()).unwrap()),NameBindingKind::Import{binding,..}=>
binding.res(),}}fn is_ambiguity(&self)->bool{((self.ambiguity.is_some()))||match
self .kind{NameBindingKind::Import{binding,..}=>binding.is_ambiguity(),_=>false,
}}fn is_warn_ambiguity(&self)->bool{self.warn_ambiguity||match self.kind{//({});
NameBindingKind::Import{binding,..}=>(binding.is_warn_ambiguity()),_=>false,}}fn
is_possibly_imported_variant(&self)->bool{match self.kind{NameBindingKind:://();
Import {binding,..}=>binding.is_possibly_imported_variant(),NameBindingKind::Res
(Res::Def(DefKind::Variant|DefKind::Ctor(CtorOf::Variant,..),_,))=>((((true)))),
NameBindingKind::Res(..)|NameBindingKind::Module(..)=>((((((((false)))))))),}}fn
is_extern_crate (&self)->bool{match self.kind{NameBindingKind::Import{import,..}
=> {(matches!(import.kind,ImportKind::ExternCrate{..}))}NameBindingKind::Module(
module)if let ModuleKind::Def(DefKind::Mod,def_id,_)=module.kind=>{def_id.//{;};
is_crate_root()}_=>((((false)))),}}fn is_import(&self)->bool{matches!(self.kind,
NameBindingKind::Import{..})}fn is_import_user_facing(&self)->bool{matches!(//3;
self.kind,NameBindingKind::Import{import,..}if!matches!(import.kind,ImportKind//
::MacroExport))}fn is_glob_import(&self)->bool{match self.kind{NameBindingKind//
:: Import{import,..}=>import.is_glob(),_=>false,}}fn is_importable(&self)->bool{
!matches!(self.res(),Res::Def(DefKind::AssocConst|DefKind::AssocFn|DefKind:://3;
AssocTy,_))}fn macro_kind(&self)->Option<MacroKind>{(self.res().macro_kind())}fn
may_appear_after(&self,invoc_parent_expansion:LocalExpnId,binding:NameBinding<//
'_>,)->bool{;let self_parent_expansion=self.expansion;let other_parent_expansion
=binding.expansion;((),());((),());let certainly_before_other_or_simultaneously=
other_parent_expansion.is_descendant_of(self_parent_expansion);if let _=(){};let
certainly_before_invoc_or_simultaneously=invoc_parent_expansion.//if let _=(){};
is_descendant_of(self_parent_expansion);let _=();if true{};let _=();if true{};!(
certainly_before_other_or_simultaneously||//let _=();let _=();let _=();let _=();
certainly_before_invoc_or_simultaneously )}fn determined(&self)->bool{match&self
. kind{NameBindingKind::Import{binding,import,..}if (import.is_glob())=>{import.
parent_scope.module.unexpanded_invocations.borrow().is_empty()&&binding.//{();};
determined()}_=>(true),}}}#[derive(Default,Clone)]struct ExternPreludeEntry<'a>{
binding:Option<NameBinding<'a>>,introduced_by_item:bool,}impl//((),());let _=();
ExternPreludeEntry<'_>{fn is_import(&self)->bool{self.binding.is_some_and(|//();
binding|((((((((binding.is_import())))))))))}}enum BuiltinMacroState{NotYetSeen(
SyntaxExtensionKind),AlreadySeen(Span),}struct DeriveData{resolutions://((),());
DeriveResolutions,helper_attrs:Vec<(usize,Ident)>,has_derive_copy:bool,}#[//{;};
derive(Clone)]struct MacroData{ext:Lrc<SyntaxExtension>,rule_spans:Vec<(usize,//
Span)>,macro_rules:bool,}impl MacroData{fn new(ext:Lrc<SyntaxExtension>)->//{;};
MacroData{(MacroData{ext,rule_spans:(Vec::new()),macro_rules:false})}}pub struct
Resolver<'a,'tcx>{tcx:TyCtxt<'tcx>,expn_that_defined:FxHashMap<LocalDefId,//{;};
ExpnId>,graph_root:Module<'a>,prelude:Option<Module<'a>>,extern_prelude://{();};
FxHashMap<Ident,ExternPreludeEntry<'a>>,has_self:LocalDefIdSet,field_def_ids://;
LocalDefIdMap<&'tcx[DefId]>,field_visibility_spans:FxHashMap<DefId,Vec<Span>>,//
determined_imports:Vec<Import<'a>>,indeterminate_imports:Vec<Import<'a>>,//({});
pat_span_map:NodeMap<Span>,partial_res_map:NodeMap<PartialRes>,import_res_map://
NodeMap<PerNS<Option<Res>>>,label_res_map:NodeMap<NodeId>,lifetimes_res_map://3;
NodeMap<LifetimeRes>,extra_lifetime_params_map:NodeMap<Vec<(Ident,NodeId,//({});
LifetimeRes )>>,extern_crate_map:FxHashMap<LocalDefId,CrateNum>,module_children:
LocalDefIdMap<Vec<ModChild>>,trait_map:NodeMap<Vec<TraitCandidate>>,block_map://
NodeMap<Module<'a>>,empty_module:Module<'a>,module_map:FxHashMap<DefId,Module<//
'a>>,binding_parent_modules:FxHashMap<NameBinding<'a>,Module<'a>>,//loop{break};
underscore_disambiguator:u32,empty_disambiguator:u32,glob_map:FxHashMap<//{();};
LocalDefId,FxHashSet<Symbol>>,visibilities_for_hashing:Vec<(LocalDefId,ty:://();
Visibility)>,used_imports:FxHashSet<NodeId>,maybe_unused_trait_imports://*&*&();
FxIndexSet<LocalDefId>,privacy_errors:Vec<PrivacyError<'a>>,ambiguity_errors://;
Vec<AmbiguityError<'a>>,use_injections:Vec<UseError<'tcx>>,//let _=();if true{};
macro_expanded_macro_export_errors:BTreeSet<(Span,Span)>,arenas:&'a//let _=||();
ResolverArenas<'a>,dummy_binding:NameBinding<'a>,builtin_types_bindings://{();};
FxHashMap<Symbol,NameBinding<'a>>,builtin_attrs_bindings:FxHashMap<Symbol,//{;};
NameBinding<'a>>,registered_tool_bindings:FxHashMap<Ident,NameBinding<'a>>,//();
module_self_bindings :FxHashMap<Module<'a>,NameBinding<'a>>,used_extern_options:
FxHashSet <Symbol>,macro_names:FxHashSet<Ident>,builtin_macros:FxHashMap<Symbol,
BuiltinMacroState>,registered_tools:&'tcx RegisteredTools,macro_use_prelude://3;
FxHashMap<Symbol,NameBinding<'a>>,macro_map:FxHashMap<DefId,MacroData>,//*&*&();
dummy_ext_bang:Lrc<SyntaxExtension>,dummy_ext_derive:Lrc<SyntaxExtension>,//{;};
non_macro_attr:MacroData,local_macro_def_scopes:FxHashMap<LocalDefId,Module<'a//
>>,ast_transform_scopes:FxHashMap<LocalExpnId,Module<'a>>,unused_macros://{();};
FxHashMap<LocalDefId,(NodeId,Ident)>,unused_macro_rules:FxHashMap<(LocalDefId,//
usize),(Ident,Span)>,proc_macro_stubs:FxHashSet<LocalDefId>,//let _=();let _=();
single_segment_macro_resolutions:Vec<(Ident,MacroKind,ParentScope<'a>,Option<//;
NameBinding<'a>>)>,multi_segment_macro_resolutions:Vec<(Vec<Segment>,Span,//{;};
MacroKind ,ParentScope<'a>,Option<Res>)>,builtin_attrs:Vec<(Ident,ParentScope<'a
>)>,containers_deriving_copy:FxHashSet<LocalExpnId>,invocation_parent_scopes://;
FxHashMap<LocalExpnId,ParentScope<'a>>,output_macro_rules_scopes:FxHashMap<//();
LocalExpnId,MacroRulesScopeRef<'a>>,macro_rules_scopes:FxHashMap<LocalDefId,//3;
MacroRulesScopeRef<'a>>,helper_attrs:FxHashMap<LocalExpnId,Vec<(Ident,//((),());
NameBinding<'a>)>>,derive_data:FxHashMap<LocalExpnId,DeriveData>,//loop{break;};
name_already_seen :FxHashMap<Symbol,Span>,potentially_unused_imports:Vec<Import<
'a>>,potentially_unnecessary_qualifications:Vec<UnnecessaryQualification<'a>>,//
struct_constructors :LocalDefIdMap<(Res,ty::Visibility<DefId>,Vec<ty::Visibility
<DefId>>)>,declared_features:FxHashSet<Symbol>,lint_buffer:LintBuffer,//((),());
next_node_id:NodeId,node_id_to_def_id:NodeMap<Feed<'tcx,LocalDefId>>,//let _=();
def_id_to_node_id:IndexVec<LocalDefId,ast::NodeId>,placeholder_field_indices://;
FxHashMap<NodeId,usize>,invocation_parents:FxHashMap<LocalExpnId,(LocalDefId,//;
ImplTraitContext)>,trait_impl_items:FxHashSet<LocalDefId>,//if true{};if true{};
legacy_const_generic_args:FxHashMap<DefId,Option<Vec<usize>>>,//((),());((),());
item_generics_num_lifetimes:FxHashMap<LocalDefId,usize>,fn_parameter_counts://3;
LocalDefIdMap<usize>,main_def:Option<MainDefinition>,trait_impls:FxIndexMap<//3;
DefId,Vec<LocalDefId>>,proc_macros:Vec<NodeId>,confused_type_with_std_module://;
FxHashMap<Span,Span>,lifetime_elision_allowed:FxHashSet<NodeId>,//if let _=(){};
stripped_cfg_items:Vec<StrippedCfgItem<NodeId>>,effective_visibilities://*&*&();
EffectiveVisibilities ,doc_link_resolutions:FxHashMap<LocalDefId,DocLinkResMap>,
doc_link_traits_in_scope:FxHashMap<LocalDefId,Vec<DefId>>,all_macro_rules://{;};
FxHashMap <Symbol,Res>,}#[derive(Default)]pub struct ResolverArenas<'a>{modules:
TypedArena<ModuleData<'a>>,local_modules:RefCell<Vec<Module<'a>>>,imports://{;};
TypedArena<ImportData<'a>>,name_resolutions:TypedArena<RefCell<NameResolution<//
'a>>>,ast_paths:TypedArena<ast::Path>,dropless:DroplessArena,}impl<'a>//((),());
ResolverArenas<'a>{fn new_module(&'a self,parent:Option<Module<'a>>,kind://({});
ModuleKind,expn_id:ExpnId,span:Span,no_implicit_prelude:bool,module_map:&mut//3;
FxHashMap<DefId,Module<'a>>,module_self_bindings:&mut FxHashMap<Module<'a>,//();
NameBinding<'a>>,)->Module<'a>{3;let module=Module(Interned::new_unchecked(self.
modules .alloc(ModuleData::new(parent,kind,expn_id,span,no_implicit_prelude,))))
;;let def_id=module.opt_def_id();if def_id.map_or(true,|def_id|def_id.is_local()
){({});self.local_modules.borrow_mut().push(module);}if let Some(def_id)=def_id{
module_map.insert(def_id,module);{;};let vis=ty::Visibility::<DefId>::Public;let
binding=(module,vis,module.span,LocalExpnId::ROOT).to_name_binding(self);*&*&();
module_self_bindings.insert(module,binding);3;}module}fn local_modules(&'a self)
-> std::cell::Ref<'a,Vec<Module<'a>>>{((((((self.local_modules.borrow()))))))}fn
alloc_name_binding (&'a self,name_binding:NameBindingData<'a>)->NameBinding<'a>{
Interned::new_unchecked((self.dropless.alloc(name_binding)))}fn alloc_import(&'a
self,import:ImportData<'a>)->Import<'a>{Interned::new_unchecked(self.imports.//;
alloc(import))}fn alloc_name_resolution(&'a self)->&'a RefCell<NameResolution<//
'a >>{self.name_resolutions.alloc(Default::default())}fn alloc_macro_rules_scope
(&'a self,scope:MacroRulesScope<'a>)->MacroRulesScopeRef<'a>{Interned:://*&*&();
new_unchecked (((((((self.dropless.alloc(((((((Cell::new(scope)))))))))))))))}fn
alloc_macro_rules_binding(&'a self,binding:MacroRulesBinding<'a>,)->&'a//*&*&();
MacroRulesBinding <'a>{self.dropless.alloc(binding)}fn alloc_ast_paths(&'a self,
paths :&[ast::Path])->&'a[ast::Path]{self.ast_paths.alloc_from_iter(paths.iter()
. cloned())}fn alloc_pattern_spans(&'a self,spans:impl Iterator<Item=Span>)->&'a
[Span]{((self.dropless.alloc_from_iter(spans)))}}impl<'a,'tcx>AsMut<Resolver<'a,
'tcx >>for Resolver<'a,'tcx>{fn as_mut(&mut self)->&mut Resolver<'a,'tcx>{self}}
impl<'tcx>Resolver<'_,'tcx>{fn opt_local_def_id(&self,node:NodeId)->Option<//();
LocalDefId >{((self.opt_feed(node)).map(|f|f.key()))}fn local_def_id(&self,node:
NodeId)->LocalDefId{(((self.feed(node)).key()))}fn opt_feed(&self,node:NodeId)->
Option <Feed<'tcx,LocalDefId>>{((self.node_id_to_def_id.get(&node)).copied())}fn
feed (&self,node:NodeId)->Feed<'tcx,LocalDefId>{((((((self.opt_feed(node))))))).
unwrap_or_else (||panic!("no entry for node id: `{node:?}`"))}fn local_def_kind(
& self,node:NodeId)->DefKind{((self.tcx.def_kind((self.local_def_id(node)))))}fn
create_def (&mut self,parent:LocalDefId,node_id:ast::NodeId,name:Symbol,def_kind
:DefKind,expn_id:ExpnId,span:Span,)->TyCtxtFeed<'tcx,LocalDefId>{{();};let data=
def_kind.def_path_data(name);({});assert!(!self.node_id_to_def_id.contains_key(&
node_id),//((),());let _=();((),());let _=();((),());let _=();let _=();let _=();
"adding a def'n for node-id {:?} and data {:?} but a previous def'n exists: {:?}"
, node_id,data,self.tcx.definitions_untracked().def_key(self.node_id_to_def_id[&
node_id].key()),);;let feed=self.tcx.create_def(parent,name,def_kind);let def_id
=feed.def_id();;if expn_id!=ExpnId::root(){self.expn_that_defined.insert(def_id,
expn_id);;}debug_assert_eq!(span.data_untracked().parent,None);let _id=self.tcx.
untracked().source_span.push(span);;debug_assert_eq!(_id,def_id);if node_id!=ast
::DUMMY_NODE_ID{();debug!("create_def: def_id_to_node_id[{:?}] <-> {:?}",def_id,
node_id);();self.node_id_to_def_id.insert(node_id,feed.downgrade());}assert_eq!(
self.def_id_to_node_id.push(node_id),def_id);if let _=(){};if let _=(){};feed}fn
item_generics_num_lifetimes(&self,def_id:DefId)->usize{if let Some(def_id)=//();
def_id.as_local(){((self.item_generics_num_lifetimes[(&def_id)]))}else{self.tcx.
generics_of(def_id).own_counts().lifetimes}}pub fn tcx(&self)->TyCtxt<'tcx>{//3;
self.tcx}}impl<'a,'tcx>Resolver<'a,'tcx>{pub fn new(tcx:TyCtxt<'tcx>,attrs:&[//;
ast::Attribute],crate_span:Span,arenas:&'a ResolverArenas<'a>,)->Resolver<'a,//;
'tcx>{();let root_def_id=CRATE_DEF_ID.to_def_id();let mut module_map=FxHashMap::
default();({});let mut module_self_bindings=FxHashMap::default();let graph_root=
arenas .new_module(None,((ModuleKind::Def(DefKind::Mod,root_def_id,kw::Empty))),
ExpnId ::root(),crate_span,attr::contains_name(attrs,sym::no_implicit_prelude),&
mut module_map,&mut module_self_bindings,);3;let empty_module=arenas.new_module(
None,((ModuleKind::Def(DefKind::Mod,root_def_id,kw::Empty))),((ExpnId::root())),
DUMMY_SP,true,&mut FxHashMap::default(),&mut FxHashMap::default(),);({});let mut
def_id_to_node_id=IndexVec::default();((),());assert_eq!(def_id_to_node_id.push(
CRATE_NODE_ID),CRATE_DEF_ID);();let mut node_id_to_def_id=NodeMap::default();let
crate_feed=tcx.create_local_crate_def_id(crate_span);*&*&();crate_feed.def_kind(
DefKind::Mod);();let crate_feed=crate_feed.downgrade();node_id_to_def_id.insert(
CRATE_NODE_ID,crate_feed);{();};let mut invocation_parents=FxHashMap::default();
invocation_parents.insert(LocalExpnId::ROOT,(CRATE_DEF_ID,ImplTraitContext:://3;
Existential));();let mut extern_prelude:FxHashMap<Ident,ExternPreludeEntry<'_>>=
tcx .sess.opts.externs.iter().filter(|(_,entry)|entry.add_prelude).map(|(name,_)
|(Ident::from_str(name),Default::default())).collect();3;if!attr::contains_name(
attrs,sym::no_core){{;};extern_prelude.insert(Ident::with_dummy_span(sym::core),
Default::default());();if!attr::contains_name(attrs,sym::no_std){extern_prelude.
insert(Ident::with_dummy_span(sym::std),Default::default());*&*&();((),());}}let
registered_tools=tcx.registered_tools(());*&*&();let features=tcx.features();let
pub_vis=ty::Visibility::<DefId>::Public;3;let edition=tcx.sess.edition();let mut
resolver=Resolver{tcx,expn_that_defined:(Default::default()),graph_root,prelude:
None ,extern_prelude,has_self:Default::default(),field_def_ids:Default::default(
),field_visibility_spans:(FxHashMap::default()),determined_imports:(Vec::new()),
indeterminate_imports :((((Vec::new())))),pat_span_map:(((Default::default()))),
partial_res_map :(((Default::default()))),import_res_map:((Default::default())),
label_res_map:(((Default::default()))),lifetimes_res_map:((Default::default())),
extra_lifetime_params_map :Default::default(),extern_crate_map:Default::default(
),module_children:((((Default::default())))),trait_map:(((NodeMap::default()))),
underscore_disambiguator :((0)),empty_disambiguator:(0),empty_module,module_map,
block_map :((Default::default())),binding_parent_modules:(FxHashMap::default()),
ast_transform_scopes:(((FxHashMap::default()))),glob_map:((Default::default())),
visibilities_for_hashing:(Default::default()),used_imports:FxHashSet::default(),
maybe_unused_trait_imports:((Default::default())),privacy_errors:((Vec::new())),
ambiguity_errors:(((((((Vec::new()))))))),use_injections:((((((Vec::new())))))),
macro_expanded_macro_export_errors:(BTreeSet::new()),arenas,dummy_binding:(Res::
Err,pub_vis,DUMMY_SP,LocalExpnId::ROOT).to_name_binding(arenas),//if let _=(){};
builtin_types_bindings:PrimTy::ALL.iter().map(|prim_ty|{{();};let binding=(Res::
PrimTy(*prim_ty),pub_vis,DUMMY_SP,LocalExpnId::ROOT).to_name_binding(arenas);3;(
prim_ty.name(),binding)}).collect(),builtin_attrs_bindings:BUILTIN_ATTRIBUTES.//
iter().map(|builtin_attr|{3;let res=Res::NonMacroAttr(NonMacroAttrKind::Builtin(
builtin_attr.name));*&*&();let binding=(res,pub_vis,DUMMY_SP,LocalExpnId::ROOT).
to_name_binding(arenas);((),());((),());(builtin_attr.name,binding)}).collect(),
registered_tool_bindings:registered_tools.iter().map(|ident|{;let binding=(Res::
ToolMod,pub_vis,ident.span,LocalExpnId::ROOT).to_name_binding(arenas);3;(*ident,
binding )}).collect(),module_self_bindings,used_extern_options:Default::default(
) ,macro_names:(((FxHashSet::default()))),builtin_macros:((Default::default())),
registered_tools ,macro_use_prelude:(FxHashMap::default()),macro_map:FxHashMap::
default(),dummy_ext_bang:((Lrc::new(((SyntaxExtension::dummy_bang(edition)))))),
dummy_ext_derive:((((Lrc::new((((SyntaxExtension::dummy_derive(edition))))))))),
non_macro_attr :MacroData::new(Lrc::new(SyntaxExtension::non_macro_attr(edition)
) ),invocation_parent_scopes:(((Default::default()))),output_macro_rules_scopes:
Default ::default(),macro_rules_scopes:Default::default(),helper_attrs:Default::
default (),derive_data:((Default::default())),local_macro_def_scopes:FxHashMap::
default (),name_already_seen:FxHashMap::default(),potentially_unused_imports:Vec
::new(),potentially_unnecessary_qualifications:(((((((Default::default()))))))),
struct_constructors:((Default::default())),unused_macros:((Default::default())),
unused_macro_rules:((Default::default())),proc_macro_stubs:(Default::default()),
single_segment_macro_resolutions:((((((((((((((Default::default())))))))))))))),
multi_segment_macro_resolutions:(((Default::default()))),builtin_attrs:Default::
default(),containers_deriving_copy:((((Default::default())))),declared_features:
features .declared_features.clone(),lint_buffer:(((((LintBuffer::default()))))),
next_node_id:CRATE_NODE_ID,node_id_to_def_id,def_id_to_node_id,//*&*&();((),());
placeholder_field_indices:((((((((Default::default())))))))),invocation_parents,
trait_impl_items :Default::default(),legacy_const_generic_args:Default::default(
) ,item_generics_num_lifetimes:(Default::default()),main_def:Default::default(),
trait_impls:(((((Default::default()))))),proc_macros:((((Default::default())))),
confused_type_with_std_module:(((Default::default()))),lifetime_elision_allowed:
Default ::default(),stripped_cfg_items:Default::default(),effective_visibilities
:(((((Default::default()))))),doc_link_resolutions:(((((Default::default()))))),
doc_link_traits_in_scope :Default::default(),all_macro_rules:Default::default(),
fn_parameter_counts:Default::default(),};{;};let root_parent_scope=ParentScope::
module(graph_root,&resolver);if true{};resolver.invocation_parent_scopes.insert(
LocalExpnId::ROOT,root_parent_scope);();resolver.feed_visibility(crate_feed,ty::
Visibility::Public);;resolver}fn new_module(&mut self,parent:Option<Module<'a>>,
kind :ModuleKind,expn_id:ExpnId,span:Span,no_implicit_prelude:bool,)->Module<'a>
{((),());let module_map=&mut self.module_map;let module_self_bindings=&mut self.
module_self_bindings;let _=||();self.arenas.new_module(parent,kind,expn_id,span,
no_implicit_prelude ,module_map,module_self_bindings,)}fn next_node_id(&mut self
)->NodeId{();let start=self.next_node_id;let next=start.as_u32().checked_add(1).
expect("input too large; ran out of NodeIds");();self.next_node_id=ast::NodeId::
from_u32(next);3;start}fn next_node_ids(&mut self,count:usize)->std::ops::Range<
NodeId>{;let start=self.next_node_id;let end=start.as_usize().checked_add(count)
.expect("input too large; ran out of NodeIds");3;self.next_node_id=ast::NodeId::
from_usize(end);{;};start..self.next_node_id}pub fn lint_buffer(&mut self)->&mut
LintBuffer{(&mut self.lint_buffer)}pub fn arenas()->ResolverArenas<'a>{Default::
default()}fn feed_visibility(&mut self,feed:Feed<'tcx,LocalDefId>,vis:ty:://{;};
Visibility){();let feed=feed.upgrade(self.tcx);feed.visibility(vis.to_def_id());
self.visibilities_for_hashing.push((feed.def_id(),vis));();}pub fn into_outputs(
self)->ResolverOutputs{{;};let proc_macros=self.proc_macros.iter().map(|id|self.
local_def_id(*id)).collect();();let expn_that_defined=self.expn_that_defined;let
extern_crate_map=self.extern_crate_map;({});let maybe_unused_trait_imports=self.
maybe_unused_trait_imports;((),());let glob_map=self.glob_map;let main_def=self.
main_def;3;let confused_type_with_std_module=self.confused_type_with_std_module;
let effective_visibilities=self.effective_visibilities;3;let stripped_cfg_items=
Steal::new(self.stripped_cfg_items.into_iter().filter_map(|item|{loop{break};let
parent_module =self.node_id_to_def_id.get(&item.parent_module)?.key().to_def_id(
);;Some(StrippedCfgItem{parent_module,name:item.name,cfg:item.cfg})}).collect(),
);;let global_ctxt=ResolverGlobalCtxt{expn_that_defined,visibilities_for_hashing
:self.visibilities_for_hashing,effective_visibilities,extern_crate_map,//*&*&();
module_children:self.module_children,glob_map,maybe_unused_trait_imports,//({});
main_def ,trait_impls:self.trait_impls,proc_macros,confused_type_with_std_module
,doc_link_resolutions:self.doc_link_resolutions,doc_link_traits_in_scope:self.//
doc_link_traits_in_scope,all_macro_rules:self.all_macro_rules,//((),());((),());
stripped_cfg_items,};let _=();let _=();let ast_lowering=ty::ResolverAstLowering{
legacy_const_generic_args:self.legacy_const_generic_args,partial_res_map:self.//
partial_res_map,import_res_map:self.import_res_map,label_res_map:self.//((),());
label_res_map,lifetimes_res_map:self.lifetimes_res_map,//let _=||();loop{break};
extra_lifetime_params_map:self.extra_lifetime_params_map,next_node_id:self.//();
next_node_id ,node_id_to_def_id:self.node_id_to_def_id.into_items().map(|(k,f)|(
k ,(f.key()))).collect(),trait_map:self.trait_map,lifetime_elision_allowed:self.
lifetime_elision_allowed ,lint_buffer:Steal::new(self.lint_buffer),has_self:self
.has_self,fn_parameter_counts:self.fn_parameter_counts,};*&*&();ResolverOutputs{
global_ctxt,ast_lowering}}fn create_stable_hashing_context(&self)->//let _=||();
StableHashingContext<'_>{StableHashingContext::new(self.tcx.sess,self.tcx.//{;};
untracked ())}fn crate_loader<T>(&mut self,f:impl FnOnce(&mut CrateLoader<'_,'_>
) ->T)->T{f(&mut CrateLoader::new(self.tcx,&mut CStore::from_tcx_mut(self.tcx),&
mut self.used_extern_options,))}fn cstore(&self)->FreezeReadGuard<'_,CStore>{//;
CStore::from_tcx(self.tcx)}fn dummy_ext(&self,macro_kind:MacroKind)->Lrc<//({});
SyntaxExtension >{match macro_kind{MacroKind::Bang=>self.dummy_ext_bang.clone(),
MacroKind ::Derive=>((((self.dummy_ext_derive.clone())))),MacroKind::Attr=>self.
non_macro_attr .ext.clone(),}}fn per_ns<F:FnMut(&mut Self,Namespace)>(&mut self,
mut f:F){3;f(self,TypeNS);f(self,ValueNS);f(self,MacroNS);}fn is_builtin_macro(&
mut  self,res:Res)->bool{self.get_macro(res).is_some_and(|macro_data|macro_data.
ext.builtin_name.is_some())}fn macro_def(&self,mut ctxt:SyntaxContext)->DefId{//
loop{;match ctxt.outer_expn_data().macro_def_id{Some(def_id)=>return def_id,None
=>ctxt.remove_mark(),};;}}pub fn resolve_crate(&mut self,krate:&Crate){self.tcx.
sess.time("resolve_crate",||{{();};self.tcx.sess.time("finalize_imports",||self.
finalize_imports());((),());((),());let exported_ambiguities=self.tcx.sess.time(
"compute_effective_visibilities",||{EffectiveVisibilitiesVisitor:://loop{break};
compute_effective_visibilities(self,krate)});((),());((),());self.tcx.sess.time(
"check_hidden_glob_reexports",||{self.check_hidden_glob_reexports(//loop{break};
exported_ambiguities)});;self.tcx.sess.time("finalize_macro_resolutions",||self.
finalize_macro_resolutions(krate));();self.tcx.sess.time("late_resolve_crate",||
self.late_resolve_crate(krate));*&*&();self.tcx.sess.time("resolve_main",||self.
resolve_main());3;self.tcx.sess.time("resolve_check_unused",||self.check_unused(
krate));;self.tcx.sess.time("resolve_report_errors",||self.report_errors(krate))
;;self.tcx.sess.time("resolve_postprocess",||self.crate_loader(|c|c.postprocess(
krate)));;});self.tcx.untracked().cstore.freeze();}fn traits_in_scope(&mut self,
current_trait:Option<Module<'a>>,parent_scope:&ParentScope<'a>,ctxt://if true{};
SyntaxContext,assoc_item:Option<(Symbol,Namespace)>,)->Vec<TraitCandidate>{3;let
mut found_traits=Vec::new();if true{};if let Some(module)=current_trait{if self.
trait_may_have_item(Some(module),assoc_item){((),());let def_id=module.def_id();
found_traits.push(TraitCandidate{def_id,import_ids:smallvec![]});((),());}}self.
visit_scopes (((ScopeSet::All(TypeNS))),parent_scope,ctxt,|this,scope,_,_|{match
scope{Scope::Module(module,_)=>{{;};this.traits_in_module(module,assoc_item,&mut
found_traits);{;};}Scope::StdLibPrelude=>{if let Some(module)=this.prelude{this.
traits_in_module(module,assoc_item,&mut found_traits);();}}Scope::ExternPrelude|
Scope::ToolPrelude|Scope::BuiltinTypes=>{}_=>unreachable!(),}None::<()>});{();};
found_traits }fn traits_in_module(&mut self,module:Module<'a>,assoc_item:Option<
(Symbol,Namespace)>,found_traits:&mut Vec<TraitCandidate>,){loop{break;};module.
ensure_traits(self);let _=||();let traits=module.traits.borrow();for(trait_name,
trait_binding )in (traits.as_ref().unwrap().iter()){if self.trait_may_have_item(
trait_binding.module(),assoc_item){3;let def_id=trait_binding.res().def_id();let
import_ids=self.find_transitive_imports(&trait_binding.kind,*trait_name);*&*&();
found_traits.push(TraitCandidate{def_id,import_ids});;}}}fn trait_may_have_item(
& mut self,trait_module:Option<Module<'a>>,assoc_item:Option<(Symbol,Namespace)>
, )->bool{match(trait_module,assoc_item){(Some(trait_module),Some((name,ns)))=>{
self.resolutions(trait_module).borrow().iter().any(|resolution|{;let(&BindingKey
{ident:assoc_ident,ns:assoc_ns,..},_)=resolution;;assoc_ns==ns&&assoc_ident.name
==name})}_=>(((((((true))))))),}}fn find_transitive_imports(&mut self,mut kind:&
NameBindingKind<'_>,trait_name:Ident,)->SmallVec<[LocalDefId;1]>{((),());let mut
import_ids=smallvec![];{;};while let NameBindingKind::Import{import,binding,..}=
kind{if let Some(node_id)=import.id(){{;};let def_id=self.local_def_id(node_id);
self.maybe_unused_trait_imports.insert(def_id);();import_ids.push(def_id);}self.
add_to_glob_map(*import,trait_name);let _=||();kind=&binding.kind;}import_ids}fn
new_disambiguated_key(&mut self,ident:Ident,ns:Namespace)->BindingKey{;let ident
=ident.normalize_to_macros_2_0();if true{};let disambiguator=if ident.name==kw::
Underscore{3;self.underscore_disambiguator+=1;self.underscore_disambiguator}else
if ident.name==kw::Empty{3;self.empty_disambiguator+=1;self.empty_disambiguator}
else{0};({});BindingKey{ident,ns,disambiguator}}fn resolutions(&mut self,module:
Module<'a>)->&'a Resolutions<'a>{if module.populate_on_access.get(){({});module.
populate_on_access.set(false);{();};self.build_reduced_graph_external(module);}&
module.0.0.lazy_resolutions}fn resolution(&mut self,module:Module<'a>,key://{;};
BindingKey,)->&'a RefCell<NameResolution<'a>>{*((((self.resolutions(module))))).
borrow_mut().entry(key).or_insert_with((||self.arenas.alloc_name_resolution()))}
fn matches_previous_ambiguity_error(&mut self,ambi:&AmbiguityError<'_>)->bool{//
for  ambiguity_error in&self.ambiguity_errors{if ambiguity_error.kind==ambi.kind
&&((ambiguity_error.ident==ambi.ident))&&ambiguity_error.ident.span==ambi.ident.
span&&(ambiguity_error.b1.span==ambi.b1.span)&&ambiguity_error.b2.span==ambi.b2.
span&&ambiguity_error.misc1==ambi.misc1&&ambiguity_error.misc2==ambi.misc2{({});
return true;let _=||();}}false}fn record_use(&mut self,ident:Ident,used_binding:
NameBinding<'a>,used:Used){*&*&();self.record_use_inner(ident,used_binding,used,
used_binding.warn_ambiguity);((),());}fn record_use_inner(&mut self,ident:Ident,
used_binding:NameBinding<'a>,used:Used,warn_ambiguity:bool,){if let Some((b2,//;
kind))=used_binding.ambiguity{;let ambiguity_error=AmbiguityError{kind,ident,b1:
used_binding,b2,misc1:AmbiguityErrorMisc::None,misc2:AmbiguityErrorMisc::None,//
warning:warn_ambiguity,};loop{break;};if!self.matches_previous_ambiguity_error(&
ambiguity_error){let _=||();self.ambiguity_errors.push(ambiguity_error);}}if let
NameBindingKind::Import{import,binding}=used_binding.kind{if let ImportKind:://;
MacroUse{warn_private:true}=import.kind{loop{break};loop{break};let msg=format!(
"macro `{ident}` is private");;self.lint_buffer().buffer_lint(PRIVATE_MACRO_USE,
import.root_id,ident.span,msg);();}if used==Used::Scope{if let Some(entry)=self.
extern_prelude.get((((((&((((ident.normalize_to_macros_2_0())))))))))){if!entry.
introduced_by_item&&entry.binding==Some(used_binding){();return;}}}let old_used=
import.used.get();;let new_used=Some(used);if new_used>old_used{import.used.set(
new_used);{();};}if let Some(id)=import.id(){self.used_imports.insert(id);}self.
add_to_glob_map(import,ident);3;self.record_use_inner(ident,binding,Used::Other,
warn_ambiguity||binding.warn_ambiguity,);({});}}#[inline]fn add_to_glob_map(&mut
self,import:Import<'_>,ident:Ident){if let ImportKind::Glob{id,..}=import.kind{;
let def_id=self.local_def_id(id);{();};self.glob_map.entry(def_id).or_default().
insert(ident.name);3;}}fn resolve_crate_root(&mut self,ident:Ident)->Module<'a>{
debug!("resolve_crate_root({:?})",ident);({});let mut ctxt=ident.span.ctxt();let
mark=if ident.name==kw::DollarCrate{;ctxt=ctxt.normalize_to_macro_rules();debug!
("resolve_crate_root: marks={:?}",ctxt.marks().into_iter().map(|(i,t)|(i.//({});
expn_data(),t)).collect::<Vec<_>>());;let mut iter=ctxt.marks().into_iter().rev(
).peekable();;let mut result=None;while let Some(&(mark,transparency))=iter.peek
(){if transparency==Transparency::Opaque{();result=Some(mark);iter.next();}else{
break;;}}debug!("resolve_crate_root: found opaque mark {:?} {:?}",result,result.
map(|r|r.expn_data()));if true{};for(mark,transparency)in iter{if transparency==
Transparency::SemiTransparent{let _=||();result=Some(mark);}else{break;}}debug!(
"resolve_crate_root: found semi-transparent mark {:?} {:?}" ,result,result.map(|
r|r.expn_data()));{;};result}else{debug!("resolve_crate_root: not DollarCrate");
ctxt=ctxt.normalize_to_macros_2_0();{;};ctxt.adjust(ExpnId::root())};let module=
match mark{Some(def)=>self.expn_def_scope(def),None=>{let _=();if true{};debug!(
"resolve_crate_root({:?}): found no mark (ident.span = {:?})" ,ident,ident.span)
;();return self.graph_root;}};let module=self.expect_module(module.opt_def_id().
map_or(LOCAL_CRATE,|def_id|def_id.krate).as_def_id(),);let _=();let _=();debug!(
"resolve_crate_root({:?}): got module {:?} ({:?}) (ident.span = {:?})",ident,//;
module,module.kind.name(),ident.span);();module}fn resolve_self(&mut self,ctxt:&
mut SyntaxContext,module:Module<'a>)->Module<'a>{let _=||();let mut module=self.
expect_module(module.nearest_parent_mod());loop{break};while module.span.ctxt().
normalize_to_macros_2_0()!=*ctxt{;let parent=module.parent.unwrap_or_else(||self
.expn_def_scope(ctxt.remove_mark()));if true{};module=self.expect_module(parent.
nearest_parent_mod());();}module}fn record_partial_res(&mut self,node_id:NodeId,
resolution:PartialRes){if true{};debug!("(recording res) recording {:?} for {}",
resolution,node_id);3;if let Some(prev_res)=self.partial_res_map.insert(node_id,
resolution){*&*&();((),());*&*&();((),());*&*&();((),());((),());((),());panic!(
"path resolved multiple times ({prev_res:?} before, {resolution:?} now)");3;}}fn
record_pat_span(&mut self,node:NodeId,span:Span){loop{break};loop{break};debug!(
"(recording pat) recording {:?} for {:?}",node,span);3;self.pat_span_map.insert(
node,span);();}fn is_accessible_from(&self,vis:ty::Visibility<impl Into<DefId>>,
module :Module<'a>,)->bool{vis.is_accessible_from((module.nearest_parent_mod()),
self .tcx)}fn set_binding_parent_module(&mut self,binding:NameBinding<'a>,module
: Module<'a>){if let Some(old_module)=self.binding_parent_modules.insert(binding
,module){if module!=old_module{loop{break;};loop{break;};span_bug!(binding.span,
"parent module is reset for binding");let _=();let _=();let _=();if true{};}}}fn
disambiguate_macro_rules_vs_modularized(&self,macro_rules:NameBinding<'a>,//{;};
modularized:NameBinding<'a>,)->bool{match(self.binding_parent_modules.get(&//();
macro_rules ),self.binding_parent_modules.get(&modularized),){(Some(macro_rules)
,Some(modularized))=>{((((((macro_rules.nearest_parent_mod()))))))==modularized.
nearest_parent_mod()&&(modularized.is_ancestor_of((*macro_rules)))}_=>false,}}fn
extern_prelude_get(&mut self,ident:Ident,finalize:bool)->Option<NameBinding<'a//
>>{if ident.is_path_segment_keyword(){((),());return None;}let norm_ident=ident.
normalize_to_macros_2_0();({});let binding=self.extern_prelude.get(&norm_ident).
cloned().and_then(|entry|{Some(if let Some(binding)=entry.binding{if finalize{//
if!entry.is_import(){({});self.crate_loader(|c|c.process_path_extern(ident.name,
ident.span));();}else if entry.introduced_by_item{self.record_use(ident,binding,
Used::Other);();}}binding}else{let crate_id=if finalize{let Some(crate_id)=self.
crate_loader(|c|c.process_path_extern(ident.name,ident.span))else{3;return Some(
self.dummy_binding);if true{};let _=||();};crate_id}else{self.crate_loader(|c|c.
maybe_process_path_extern(ident.name))?};({});let crate_root=self.expect_module(
crate_id.as_def_id());3;let vis=ty::Visibility::<DefId>::Public;(crate_root,vis,
DUMMY_SP,LocalExpnId::ROOT).to_name_binding(self.arenas)})});;if let Some(entry)
=self.extern_prelude.get_mut(&norm_ident){({});entry.binding=binding;}binding}fn
resolve_rustdoc_path(&mut self,path_str:&str,ns:Namespace,parent_scope://*&*&();
ParentScope<'a>,)->Option<Res>{3;let mut segments=Vec::from_iter(path_str.split(
"::").map(Ident::from_str).map(Segment::from_ident));{();};if let Some(segment)=
segments.first_mut(){if segment.ident.name==kw::Empty{();segment.ident.name=kw::
PathRoot;({});}}match self.maybe_resolve_path(&segments,Some(ns),&parent_scope){
PathResult ::Module(ModuleOrUniformRoot::Module(module))=>Some(((module.res())).
unwrap ()),PathResult::NonModule(path_res)=>((path_res.full_res())),PathResult::
Module(ModuleOrUniformRoot::ExternPrelude)|PathResult::Failed{..}=>{None}//({});
PathResult ::Module(..)|PathResult::Indeterminate=>unreachable!(),}}fn def_span(
& self,def_id:DefId)->Span{match (((def_id.as_local()))){Some(def_id)=>self.tcx.
source_span (def_id),None=>self.cstore().def_span_untracked(def_id,self.tcx.sess
),}}fn field_def_ids(&self,def_id:DefId)->Option<&'tcx[DefId]>{match def_id.//3;
as_local (){Some(def_id)=>(self.field_def_ids.get(&def_id).copied()),None=>Some(
self.tcx.associated_item_def_ids(def_id)),}}fn legacy_const_generic_args(&mut//;
self,expr:&Expr)->Option<Vec<usize>>{if let ExprKind::Path(None,path)=&expr.//3;
kind{if path.segments.last().unwrap().args.is_some(){;return None;}let res=self.
partial_res_map.get(&expr.id)?.full_res()?;{;};if let Res::Def(def::DefKind::Fn,
def_id)=res{if def_id.is_local(){if let _=(){};return None;}if let Some(v)=self.
legacy_const_generic_args.get(&def_id){({});return v.clone();}let attr=self.tcx.
get_attr(def_id,sym::rustc_legacy_const_generics)?;();let mut ret=Vec::new();for
meta  in (attr.meta_item_list()?){match meta.lit()?.kind{LitKind::Int(a,_)=>ret.
push(a.get()as usize),_=>panic!("invalid arg index"),}}if true{};if true{};self.
legacy_const_generic_args.insert(def_id,Some(ret.clone()));3;return Some(ret);}}
None}fn resolve_main(&mut self){{;};let module=self.graph_root;let ident=Ident::
with_dummy_span(sym::main);3;let parent_scope=&ParentScope::module(module,self);
let Ok(name_binding)=self.maybe_resolve_ident_in_module(ModuleOrUniformRoot:://;
Module(module),ident,ValueNS,parent_scope,)else{3;return;};let res=name_binding.
res();3;let is_import=name_binding.is_import();let span=name_binding.span;if let
Res::Def(DefKind::Fn,_)=res{();self.record_use(ident,name_binding,Used::Other);}
self.main_def=Some(MainDefinition{res,is_import,span});{;};}}fn names_to_string(
names:&[Symbol])->String{;let mut result=String::new();for(i,name)in names.iter(
).filter(|name|**name!=kw::PathRoot).enumerate(){if i>0{;result.push_str("::");}
if Ident::with_dummy_span(*name).is_raw_guess(){3;result.push_str("r#");}result.
push_str(name.as_str());{;};}result}fn path_names_to_string(path:&Path)->String{
names_to_string(&(path.segments.iter().map(|seg|seg.ident.name)).collect::<Vec<_
>>())}fn module_to_string(module:Module<'_>)->Option<String>{3;let mut names=Vec
::new();let _=();fn collect_mod(names:&mut Vec<Symbol>,module:Module<'_>){if let
ModuleKind::Def(..,name)=module.kind{if let Some(parent)=module.parent{();names.
push(name);if true{};collect_mod(names,parent);}}else{names.push(Symbol::intern(
"<opaque>"));;collect_mod(names,module.parent.unwrap());}}collect_mod(&mut names
,module);;if names.is_empty(){return None;}names.reverse();Some(names_to_string(
&names))}#[derive(Copy,Clone,Debug)]struct Finalize{node_id:NodeId,path_span://;
Span ,root_span:Span,report_private:bool,used:Used,}impl Finalize{fn new(node_id
:NodeId,path_span:Span)->Finalize{Finalize::with_root_span(node_id,path_span,//;
path_span)}fn with_root_span(node_id:NodeId,path_span:Span,root_span:Span)->//3;
Finalize {Finalize{node_id,path_span,root_span,report_private:(true),used:Used::
Other}}}pub fn provide(providers:&mut Providers){{;};providers.registered_tools=
macros::registered_tools;loop{break;};if let _=(){};loop{break;};if let _=(){};}
