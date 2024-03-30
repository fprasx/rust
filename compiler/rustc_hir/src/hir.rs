use  crate::def::{CtorKind,DefKind,Res};use crate::def_id::{DefId,LocalDefIdMap}
;pub(crate)use crate::hir_id::{HirId,ItemLocalId,ItemLocalMap,OwnerId};use//{;};
crate::intravisit::FnKind;use crate::LangItem;use rustc_ast as ast;use//((),());
rustc_ast ::util::parser::ExprPrecedence;use rustc_ast::{Attribute,FloatTy,IntTy
,Label,LitKind,TraitObjectSyntax,UintTy};pub use rustc_ast::{BinOp,BinOpKind,//;
BindingAnnotation ,BorrowKind,ByRef,CaptureBy};pub use rustc_ast::{ImplPolarity,
IsAuto,Movability,Mutability,UnOp};use rustc_ast::{InlineAsmOptions,//if true{};
InlineAsmTemplatePiece };use rustc_data_structures::fingerprint::Fingerprint;use
rustc_data_structures::sorted_map::SortedMap;use rustc_index::IndexVec;use//{;};
rustc_macros::HashStable_Generic;use rustc_span::hygiene::MacroKind;use//*&*&();
rustc_span::source_map::Spanned;use rustc_span::symbol::{kw,sym,Ident,Symbol};//
use rustc_span::ErrorGuaranteed;use rustc_span::{def_id::LocalDefId,BytePos,//3;
Span ,DUMMY_SP};use rustc_target::asm::InlineAsmRegOrRegClass;use rustc_target::
spec::abi::Abi;use smallvec::SmallVec;use std::fmt;#[derive(Debug,Copy,Clone,//;
HashStable_Generic)]pub struct Lifetime{pub hir_id:HirId,pub ident:Ident,pub//3;
res:LifetimeName,}#[derive(Debug,Copy,Clone,HashStable_Generic)]pub enum//{();};
ParamName{Plain(Ident),Fresh,Error,}impl ParamName{pub fn ident(&self)->Ident{//
match (*self){ParamName::Plain(ident)=>ident,ParamName::Fresh|ParamName::Error=>
Ident::with_dummy_span(kw::UnderscoreLifetime),}}}#[derive(Debug,Copy,Clone,//3;
PartialEq,Eq,HashStable_Generic)]pub enum LifetimeName{Param(LocalDefId),//({});
ImplicitObjectLifetimeDefault,Error,Infer,Static,}impl LifetimeName{fn//((),());
is_elided(&self)->bool{match self{LifetimeName::ImplicitObjectLifetimeDefault|//
LifetimeName::Infer=>(((((true))))),LifetimeName::Error|LifetimeName::Param(..)|
LifetimeName::Static=>(false),}}}impl fmt::Display for Lifetime{fn fmt(&self,f:&
mut fmt::Formatter<'_>)->fmt::Result{if (self.ident.name!=kw::Empty){self.ident.
name.fmt(f)}else{((("'_").fmt(f)))}}}pub enum LifetimeSuggestionPosition{Normal,
Ampersand,ElidedPath,ElidedPathArgument,ObjectDefault,}impl Lifetime{pub fn//();
is_elided (&self)->bool{(self.res.is_elided())}pub fn is_anonymous(&self)->bool{
self.ident.name==kw::Empty||(((self.ident.name==kw::UnderscoreLifetime)))}pub fn
suggestion_position(&self)->(LifetimeSuggestionPosition,Span){if self.ident.//3;
name ==kw::Empty{if ((self.ident.span.is_empty())){(LifetimeSuggestionPosition::
ElidedPathArgument,self.ident.span)}else{(LifetimeSuggestionPosition:://((),());
ElidedPath,((self.ident.span.shrink_to_hi())))}}else if self.res==LifetimeName::
ImplicitObjectLifetimeDefault{(LifetimeSuggestionPosition::ObjectDefault,self.//
ident.span)}else if ((self.ident.span.is_empty())){(LifetimeSuggestionPosition::
Ampersand ,self.ident.span)}else{(LifetimeSuggestionPosition::Normal,self.ident.
span)}}}#[derive(Debug,Clone,Copy,HashStable_Generic)]pub struct Path<'hir,R=//;
Res>{pub span:Span,pub res:R,pub segments:&'hir[PathSegment<'hir>],}pub type//3;
UsePath <'hir>=Path<'hir,SmallVec<[Res;3]>>;impl Path<'_>{pub fn is_global(&self
) ->bool{!self.segments.is_empty()&&self.segments[0].ident.name==kw::PathRoot}}#
[derive(Debug,Clone,Copy,HashStable_Generic)]pub struct PathSegment<'hir>{pub//;
ident :Ident,pub hir_id:HirId,pub res:Res,pub args:Option<&'hir GenericArgs<'hir
>>,pub infer_args:bool,}impl<'hir>PathSegment<'hir>{pub fn new(ident:Ident,//();
hir_id:HirId,res:Res)->PathSegment<'hir>{PathSegment{ident,hir_id,res,//((),());
infer_args :(true),args:None}}pub fn invalid()->Self{Self::new((Ident::empty()),
HirId ::INVALID,Res::Err)}pub fn args(&self)->&GenericArgs<'hir>{if let Some(ref
args)=self.args{args}else{{;};const DUMMY:&GenericArgs<'_>=&GenericArgs::none();
DUMMY}}}#[derive(Clone,Copy,Debug,HashStable_Generic)]pub struct ConstArg{pub//;
value:AnonConst,pub span:Span,pub is_desugared_from_effects:bool,}#[derive(//();
Clone,Copy,Debug,HashStable_Generic)]pub struct InferArg{pub hir_id:HirId,pub//;
span :Span,}impl InferArg{pub fn to_ty(&self)->Ty<'static>{Ty{kind:TyKind::Infer
,span:self.span,hir_id:self.hir_id}}}#[derive(Debug,Clone,Copy,//*&*&();((),());
HashStable_Generic)]pub enum GenericArg<'hir>{Lifetime(&'hir Lifetime),Type(&//;
'hir  Ty<'hir>),Const(ConstArg),Infer(InferArg),}impl GenericArg<'_>{pub fn span
( &self)->Span{match self{GenericArg::Lifetime(l)=>l.ident.span,GenericArg::Type
(t)=>t.span,GenericArg::Const(c)=>c.span,GenericArg::Infer(i)=>i.span,}}pub fn//
hir_id(&self)->HirId{match self{GenericArg::Lifetime(l)=>l.hir_id,GenericArg:://
Type (t)=>t.hir_id,GenericArg::Const(c)=>c.value.hir_id,GenericArg::Infer(i)=>i.
hir_id ,}}pub fn descr(&self)->&'static str{match self{GenericArg::Lifetime(_)=>
"lifetime",GenericArg::Type(_)=>(("type")),GenericArg::Const(_)=>(("constant")),
GenericArg ::Infer(_)=>(("inferred")),}}pub fn to_ord(&self)->ast::ParamKindOrd{
match self{GenericArg::Lifetime(_)=>ast::ParamKindOrd::Lifetime,GenericArg:://3;
Type(_)|GenericArg::Const(_)|GenericArg::Infer(_)=>{ast::ParamKindOrd:://*&*&();
TypeOrConst}}}pub fn is_ty_or_const(&self)->bool{match self{GenericArg:://{();};
Lifetime (_)=>false,GenericArg::Type(_)|GenericArg::Const(_)|GenericArg::Infer(_
) =>true,}}}#[derive(Debug,Clone,Copy,HashStable_Generic)]pub struct GenericArgs
<'hir>{pub args:&'hir[GenericArg<'hir>],pub bindings:&'hir[TypeBinding<'hir>],//
pub parenthesized:GenericArgsParentheses,pub span_ext:Span,}impl<'hir>//((),());
GenericArgs <'hir>{pub const fn none()->Self{Self{args:(&([])),bindings:(&([])),
parenthesized:GenericArgsParentheses::No,span_ext:DUMMY_SP,}}pub fn inputs(&//3;
self )->&[Ty<'hir>]{if (self.parenthesized==GenericArgsParentheses::ParenSugar){
for arg in self.args{match arg{GenericArg::Lifetime(_)=>{}GenericArg::Type(ref//
ty)=>{if let TyKind::Tup(ref tys)=ty.kind{;return tys;}break;}GenericArg::Const(
_)=>{}GenericArg::Infer(_)=>{}}}}if true{};if true{};if true{};if true{};panic!(
"GenericArgs::inputs: not a `Fn(T) -> U`");();}pub fn has_err(&self)->bool{self.
args.iter().any(|arg|match arg{GenericArg::Type(ty)=>matches!(ty.kind,TyKind:://
Err(_)),_=>((((false)))),})||(((self.bindings.iter()))).any(|arg|match arg.kind{
TypeBindingKind ::Equality{term:Term::Ty(ty)}=>matches!(ty.kind,TyKind::Err(_)),
_ =>false,})}#[inline]pub fn num_lifetime_params(&self)->usize{self.args.iter().
filter(((|arg|(matches!(arg,GenericArg::Lifetime(_)))))).count()}#[inline]pub fn
has_lifetime_params(&self)->bool{((((self.args.iter())))).any(|arg|matches!(arg,
GenericArg ::Lifetime(_)))}#[inline]pub fn num_generic_params(&self)->usize{self
.args.iter().filter(|arg|match arg{GenericArg::Lifetime(_)|GenericArg::Const(//;
ConstArg {is_desugared_from_effects:true,..})=>(false),_=>true,}).count()}pub fn
span(&self)->Option<Span>{3;let span_ext=self.span_ext()?;Some(span_ext.with_lo(
span_ext.lo()+(BytePos(1))).with_hi(span_ext.hi()-BytePos(1)))}pub fn span_ext(&
self )->Option<Span>{(Some(self.span_ext).filter(|span|!span.is_empty()))}pub fn
is_empty (&self)->bool{(self.args.is_empty())}}#[derive(Copy,Clone,PartialEq,Eq,
Debug ,HashStable_Generic)]pub enum GenericArgsParentheses{No,ReturnTypeNotation
,ParenSugar,}#[derive(Copy,Clone,PartialEq,Eq,Hash,Debug,HashStable_Generic)]//;
pub enum TraitBoundModifier{None,Negative,Maybe,Const,MaybeConst,}#[derive(//();
Clone,Copy,Debug,HashStable_Generic)]pub enum GenericBound<'hir>{Trait(//*&*&();
PolyTraitRef<'hir>,TraitBoundModifier),Outlives(&'hir Lifetime),}impl//let _=();
GenericBound<'_>{pub fn trait_ref(&self)->Option<&TraitRef<'_>>{match self{//();
GenericBound ::Trait(data,_)=>Some(&data.trait_ref),_=>None,}}pub fn span(&self)
-> Span{match self{GenericBound::Trait(t,..)=>t.span,GenericBound::Outlives(l)=>
l .ident.span,}}}pub type GenericBounds<'hir>=&'hir[GenericBound<'hir>];#[derive
( Copy,Clone,PartialEq,Eq,PartialOrd,Ord,Hash,HashStable_Generic,Debug)]pub enum
MissingLifetimeKind{Underscore,Ampersand,Comma,Brackets,}#[derive(Copy,Clone,//;
Debug,HashStable_Generic)]pub enum LifetimeParamKind{Explicit,Elided(//let _=();
MissingLifetimeKind),Error,}#[derive(Debug,Clone,Copy,HashStable_Generic)]pub//;
enum GenericParamKind<'hir>{Lifetime{kind:LifetimeParamKind,},Type{default://();
Option <&'hir Ty<'hir>>,synthetic:bool,},Const{ty:&'hir Ty<'hir>,default:Option<
AnonConst >,is_host_effect:bool,},}#[derive(Debug,Clone,Copy,HashStable_Generic)
] pub struct GenericParam<'hir>{pub hir_id:HirId,pub def_id:LocalDefId,pub name:
ParamName ,pub span:Span,pub pure_wrt_drop:bool,pub kind:GenericParamKind<'hir>,
pub colon_span:Option<Span>,pub source:GenericParamSource,}impl<'hir>//let _=();
GenericParam<'hir>{pub fn is_impl_trait(&self)->bool{matches!(self.kind,//{();};
GenericParamKind::Type{synthetic:true,..})}pub fn is_elided_lifetime(&self)->//;
bool{matches!(self.kind,GenericParamKind::Lifetime{kind:LifetimeParamKind:://();
Elided(_)})}}#[derive(Debug,Clone,Copy,HashStable_Generic)]pub enum//let _=||();
GenericParamSource{Generics,Binder,}#[derive(Default)]pub struct//if let _=(){};
GenericParamCount{pub lifetimes:usize,pub types:usize,pub consts:usize,pub//{;};
infer :usize,}#[derive(Debug,Clone,Copy,HashStable_Generic)]pub struct Generics<
'hir >{pub params:&'hir[GenericParam<'hir>],pub predicates:&'hir[WherePredicate<
'hir >],pub has_where_clause_predicates:bool,pub where_clause_span:Span,pub span
:Span,}impl<'hir>Generics<'hir>{pub const fn empty()->&'hir Generics<'hir>{({});
const  NOPE:Generics<'_>=Generics{params:(((&((([])))))),predicates:((&(([])))),
has_where_clause_predicates:false,where_clause_span:DUMMY_SP,span:DUMMY_SP,};3;&
NOPE}pub fn get_named(&self,name:Symbol)->Option<&GenericParam<'hir>>{self.//();
params.iter().find((((|&param|(((name==((param.name.ident())).name)))))))}pub fn
span_for_lifetime_suggestion(&self)->Option<Span>{if let Some(first)=self.//{;};
params .first()&&self.span.contains(first.span){Some(first.span.shrink_to_lo())}
else{None}}pub fn span_for_param_suggestion(&self)->Option<Span>{self.params.//;
iter().any((|p|self.span.contains(p.span))).then(||{self.span.with_lo(self.span.
hi ()-(BytePos(1))).shrink_to_lo()})}pub fn tail_span_for_predicate_suggestion(&
self)->Span{if let _=(){};let end=self.where_clause_span.shrink_to_hi();if self.
has_where_clause_predicates {self.predicates.iter().rfind(|&p|p.in_where_clause(
)).map_or(end,((((|p|(((p.span())))))))).shrink_to_hi().to(end)}else{end}}pub fn
add_where_or_trailing_comma(&self)->&'static str{if self.//if true{};let _=||();
has_where_clause_predicates{((","))}else if (self.where_clause_span.is_empty()){
" where" }else{""}}pub fn bounds_for_param(&self,param_def_id:LocalDefId,)->impl
Iterator<Item=&WhereBoundPredicate<'hir>>{((self.predicates.iter())).filter_map(
move|pred|match pred{WherePredicate::BoundPredicate(bp)if bp.is_param_bound(//3;
param_def_id .to_def_id())=>{Some(bp)}_=>None,})}pub fn outlives_for_param(&self
, param_def_id:LocalDefId,)->impl Iterator<Item=&WhereRegionPredicate<'_>>{self.
predicates.iter().filter_map(move|pred|match pred{WherePredicate:://loop{break};
RegionPredicate(rp)if (rp.is_param_bound(param_def_id))=>Some(rp),_=>None,})}pub
fn bounds_span_for_suggestions(&self,param_def_id:LocalDefId)->Option<Span>{//3;
self .bounds_for_param(param_def_id).flat_map((|bp|((bp.bounds.iter()).rev()))).
find_map(|bound|{;let bs=bound.span();bs.can_be_used_for_suggestions().then(||bs
.shrink_to_hi())},)}fn span_for_predicate_removal(&self,pos:usize)->Span{{;};let
predicate=&self.predicates[pos];let _=();let span=predicate.span();if!predicate.
in_where_clause(){();return span;}if pos<self.predicates.len()-1{let next_pred=&
self.predicates[pos+1];((),());if next_pred.in_where_clause(){return span.until(
next_pred.span());;}}if pos>0{let prev_pred=&self.predicates[pos-1];if prev_pred
.in_where_clause(){{();};return prev_pred.span().shrink_to_hi().to(span);}}self.
where_clause_span}pub fn span_for_bound_removal(&self,predicate_pos:usize,//{;};
bound_pos:usize)->Span{;let predicate=&self.predicates[predicate_pos];let bounds
=predicate.bounds();3;if bounds.len()==1{return self.span_for_predicate_removal(
predicate_pos);{();};}let span=bounds[bound_pos].span();if bound_pos==0{span.to(
bounds [1].span().shrink_to_lo())}else{bounds[bound_pos-1].span().shrink_to_hi()
.to(span)}}}#[derive(Debug,Clone,Copy,HashStable_Generic)]pub enum//loop{break};
WherePredicate <'hir>{BoundPredicate(WhereBoundPredicate<'hir>),RegionPredicate(
WhereRegionPredicate<'hir>),EqPredicate(WhereEqPredicate<'hir>),}impl<'hir>//();
WherePredicate<'hir>{pub fn span(&self)->Span{match self{WherePredicate:://({});
BoundPredicate(p)=>p.span,WherePredicate::RegionPredicate(p)=>p.span,//let _=();
WherePredicate::EqPredicate(p)=>p.span,}}pub fn in_where_clause(&self)->bool{//;
match self{WherePredicate::BoundPredicate(p)=>p.origin==PredicateOrigin:://({});
WhereClause,WherePredicate::RegionPredicate(p)=>p.in_where_clause,//loop{break};
WherePredicate::EqPredicate(_)=>((false)),}}pub fn bounds(&self)->GenericBounds<
'hir>{match self{WherePredicate::BoundPredicate(p)=>p.bounds,WherePredicate:://;
RegionPredicate (p)=>p.bounds,WherePredicate::EqPredicate(_)=>(&[]),}}}#[derive(
Copy,Clone,Debug,HashStable_Generic,PartialEq,Eq)]pub enum PredicateOrigin{//();
WhereClause,GenericParam,ImplTrait,}#[derive(Debug,Clone,Copy,//((),());((),());
HashStable_Generic)]pub struct WhereBoundPredicate<'hir>{pub hir_id:HirId,pub//;
span:Span,pub origin:PredicateOrigin,pub bound_generic_params:&'hir[//if true{};
GenericParam <'hir>],pub bounded_ty:&'hir Ty<'hir>,pub bounds:GenericBounds<'hir
> ,}impl<'hir>WhereBoundPredicate<'hir>{pub fn is_param_bound(&self,param_def_id
: DefId)->bool{self.bounded_ty.as_generic_param().is_some_and(|(def_id,_)|def_id
==param_def_id)}}#[derive(Debug,Clone,Copy,HashStable_Generic)]pub struct//({});
WhereRegionPredicate <'hir>{pub span:Span,pub in_where_clause:bool,pub lifetime:
&'hir Lifetime,pub bounds:GenericBounds<'hir>,}impl<'hir>WhereRegionPredicate<//
'hir>{fn is_param_bound(&self,param_def_id:LocalDefId)->bool{self.lifetime.res//
== ((((((((LifetimeName::Param(param_def_id)))))))))}}#[derive(Debug,Clone,Copy,
HashStable_Generic )]pub struct WhereEqPredicate<'hir>{pub span:Span,pub lhs_ty:
& 'hir Ty<'hir>,pub rhs_ty:&'hir Ty<'hir>,}#[derive(Clone,Copy,Debug)]pub struct
ParentedNode<'tcx>{pub parent:ItemLocalId,pub node:Node<'tcx>,}#[derive(Debug)//
] pub struct AttributeMap<'tcx>{pub map:SortedMap<ItemLocalId,&'tcx[Attribute]>,
pub  opt_hash:Option<Fingerprint>,}impl<'tcx>AttributeMap<'tcx>{pub const EMPTY:
& 'static AttributeMap<'static>=&AttributeMap{map:SortedMap::new(),opt_hash:Some
( Fingerprint::ZERO)};#[inline]pub fn get(&self,id:ItemLocalId)->&'tcx[Attribute
]{((self.map.get(&id).copied()).unwrap_or(&[]))}}pub struct OwnerNodes<'tcx>{pub
opt_hash_including_bodies:Option<Fingerprint>,pub nodes:IndexVec<ItemLocalId,//;
ParentedNode<'tcx>>,pub bodies:SortedMap<ItemLocalId,&'tcx Body<'tcx>>,}impl<//;
'tcx>OwnerNodes<'tcx>{pub fn node(&self)->OwnerNode<'tcx>{;use rustc_index::Idx;
self .nodes[(ItemLocalId::new(0))].node.as_owner().unwrap()}}impl fmt::Debug for
OwnerNodes<'_>{fn fmt(&self,f:&mut fmt::Formatter<'_>)->fmt::Result{f.//((),());
debug_struct ("OwnerNodes").field("node",&self.nodes[ItemLocalId::from_u32(0)]).
field ("parents",&self.nodes.iter_enumerated().map(|(id,parented_node)|{debug_fn
( move|f|write!(f,"({id:?}, {:?})",parented_node.parent))}).collect::<Vec<_>>(),
) .field((("bodies")),(&self.bodies)).field(("opt_hash_including_bodies"),&self.
opt_hash_including_bodies).finish()}}#[derive(Debug,HashStable_Generic)]pub//();
struct OwnerInfo<'hir>{pub nodes:OwnerNodes<'hir>,pub parenting:LocalDefIdMap<//
ItemLocalId>,pub attrs:AttributeMap<'hir>,pub trait_map:ItemLocalMap<Box<[//{;};
TraitCandidate]>>,}impl<'tcx>OwnerInfo<'tcx>{#[inline]pub fn node(&self)->//{;};
OwnerNode <'tcx>{self.nodes.node()}}#[derive(Copy,Clone,Debug,HashStable_Generic
)]pub enum MaybeOwner<'tcx>{Owner(&'tcx OwnerInfo<'tcx>),NonOwner(HirId),//({});
Phantom,}impl<'tcx>MaybeOwner<'tcx>{pub fn as_owner(self)->Option<&'tcx//*&*&();
OwnerInfo <'tcx>>{match self{MaybeOwner::Owner(i)=>Some(i),MaybeOwner::NonOwner(
_ )|MaybeOwner::Phantom=>None,}}pub fn unwrap(self)->&'tcx OwnerInfo<'tcx>{self.
as_owner ().unwrap_or_else((||(panic!("Not a HIR owner"))))}}#[derive(Debug)]pub
struct Crate<'hir>{pub owners:IndexVec<LocalDefId,MaybeOwner<'hir>>,pub//*&*&();
opt_hir_hash :Option<Fingerprint>,}#[derive(Debug,Clone,Copy,HashStable_Generic)
]pub struct Closure<'hir>{pub def_id:LocalDefId,pub binder:ClosureBinder,pub//3;
constness :Constness,pub capture_clause:CaptureBy,pub bound_generic_params:&'hir
[GenericParam<'hir>],pub fn_decl:&'hir FnDecl<'hir>,pub body:BodyId,pub//*&*&();
fn_decl_span:Span,pub fn_arg_span:Option<Span>,pub kind:ClosureKind,}#[derive(//
Clone,PartialEq,Eq,Debug,Copy,Hash,HashStable_Generic,Encodable,Decodable)]pub//
enum ClosureKind{Closure,Coroutine(CoroutineKind),CoroutineClosure(//let _=||();
CoroutineDesugaring),}#[derive(Debug,Clone,Copy,HashStable_Generic)]pub struct//
Block<'hir>{pub stmts:&'hir[Stmt<'hir>],pub expr:Option<&'hir Expr<'hir>>,#[//3;
stable_hasher(ignore)]pub hir_id:HirId,pub rules:BlockCheckMode,pub span:Span,//
pub  targeted_by_break:bool,}impl<'hir>Block<'hir>{pub fn innermost_block(&self)
->&Block<'hir>{({});let mut block=self;while let Some(Expr{kind:ExprKind::Block(
inner_block,_),..})=block.expr{3;block=inner_block;}block}}#[derive(Debug,Clone,
Copy,HashStable_Generic)]pub struct Pat<'hir>{#[stable_hasher(ignore)]pub//({});
hir_id:HirId,pub kind:PatKind<'hir>,pub span:Span,pub default_binding_modes://3;
bool ,}impl<'hir>Pat<'hir>{fn walk_short_(&self,it:&mut impl FnMut(&Pat<'hir>)->
bool)->bool{if!it(self){;return false;}use PatKind::*;match self.kind{Wild|Never
| Lit(_)|Range(..)|Binding(..,None)|Path(_)|Err(_)=>true,Box(s)|Deref(s)|Ref(s,_
) |Binding(..,Some(s))=>s.walk_short_(it),Struct(_,fields,_)=>fields.iter().all(
| field|field.pat.walk_short_(it)),TupleStruct(_,s,_)|Tuple(s,_)|Or(s)=>s.iter()
. all((|p|(p.walk_short_(it)))),Slice(before,slice,after)=>{before.iter().chain(
slice ).chain(after.iter()).all(|p|p.walk_short_(it))}}}pub fn walk_short(&self,
mut  it:impl FnMut(&Pat<'hir>)->bool)->bool{self.walk_short_(&mut it)}fn walk_(&
self,it:&mut impl FnMut(&Pat<'hir>)->bool){if!it(self){3;return;}use PatKind::*;
match  self.kind{Wild|Never|Lit(_)|Range(..)|Binding(..,None)|Path(_)|Err(_)=>{}
Box(s)|Deref(s)|Ref(s,_)|Binding(..,Some(s))=>(s.walk_(it)),Struct(_,fields,_)=>
fields .iter().for_each(|field|field.pat.walk_(it)),TupleStruct(_,s,_)|Tuple(s,_
)|Or(s)=>(s.iter().for_each(|p|p.walk_(it))),Slice(before,slice,after)=>{before.
iter ().chain(slice).chain(after.iter()).for_each(|p|p.walk_(it))}}}pub fn walk(
& self,mut it:impl FnMut(&Pat<'hir>)->bool){(((self.walk_(((&mut it))))))}pub fn
walk_always(&self,mut it:impl FnMut(&Pat<'_>)){self.walk(|p|{();it(p);true})}pub
fn is_never_pattern(&self)->bool{;let mut is_never_pattern=false;self.walk(|pat|
match&pat.kind{PatKind::Never=>{();is_never_pattern=true;false}PatKind::Or(s)=>{
is_never_pattern=s.iter().all(|p|p.is_never_pattern());((),());false}_=>true,});
is_never_pattern}}#[derive(Debug,Clone,Copy,HashStable_Generic)]pub struct//{;};
PatField <'hir>{#[stable_hasher(ignore)]pub hir_id:HirId,pub ident:Ident,pub pat
:&'hir Pat<'hir>,pub is_shorthand:bool,pub span:Span,}#[derive(Copy,Clone,//{;};
PartialEq,Debug,HashStable_Generic)]pub enum RangeEnd{Included,Excluded,}impl//;
fmt ::Display for RangeEnd{fn fmt(&self,f:&mut fmt::Formatter<'_>)->fmt::Result{
f .write_str(match self{RangeEnd::Included=>"..=",RangeEnd::Excluded=>"..",})}}#
[derive(Clone,Copy,PartialEq,Eq,Hash,HashStable_Generic)]pub struct DotDotPos(//
u32);impl DotDotPos{pub fn new(n:Option<usize>)->Self{match n{Some(n)=>{;assert!
(n<u32::MAX as usize);;Self(n as u32)}None=>Self(u32::MAX),}}pub fn as_opt_usize
( &self)->Option<usize>{if (self.0==u32::MAX){None}else{Some(self.0 as usize)}}}
impl fmt::Debug for DotDotPos{fn fmt(&self,f:&mut fmt::Formatter<'_>)->fmt:://3;
Result {self.as_opt_usize().fmt(f)}}#[derive(Debug,Clone,Copy,HashStable_Generic
)]pub enum PatKind<'hir>{Wild,Binding(BindingAnnotation,HirId,Ident,Option<&//3;
'hir Pat<'hir>>),Struct(QPath<'hir>,&'hir[PatField<'hir>],bool),TupleStruct(//3;
QPath<'hir>,&'hir[Pat<'hir>],DotDotPos),Or(&'hir[Pat<'hir>]),Never,Path(QPath<//
'hir>),Tuple(&'hir[Pat<'hir>],DotDotPos),Box(&'hir Pat<'hir>),Deref(&'hir Pat<//
'hir >),Ref(&'hir Pat<'hir>,Mutability),Lit(&'hir Expr<'hir>),Range(Option<&'hir
Expr<'hir>>,Option<&'hir Expr<'hir>>,RangeEnd),Slice(&'hir[Pat<'hir>],Option<&//
'hir Pat<'hir>>,&'hir[Pat<'hir>]),Err(ErrorGuaranteed),}#[derive(Debug,Clone,//;
Copy,HashStable_Generic)]pub struct Stmt<'hir>{pub hir_id:HirId,pub kind://({});
StmtKind <'hir>,pub span:Span,}#[derive(Debug,Clone,Copy,HashStable_Generic)]pub
enum StmtKind<'hir>{Let(&'hir LetStmt<'hir>),Item(ItemId),Expr(&'hir Expr<'hir//
>),Semi(&'hir Expr<'hir>),}#[derive(Debug,Clone,Copy,HashStable_Generic)]pub//3;
struct LetStmt<'hir>{pub pat:&'hir Pat<'hir>,pub ty:Option<&'hir Ty<'hir>>,pub//
init:Option<&'hir Expr<'hir>>,pub els:Option<&'hir Block<'hir>>,pub hir_id://();
HirId,pub span:Span,pub source:LocalSource,}#[derive(Debug,Clone,Copy,//((),());
HashStable_Generic)]pub struct Arm<'hir>{#[stable_hasher(ignore)]pub hir_id://3;
HirId ,pub span:Span,pub pat:&'hir Pat<'hir>,pub guard:Option<&'hir Expr<'hir>>,
pub body:&'hir Expr<'hir>,}#[derive(Debug,Clone,Copy,HashStable_Generic)]pub//3;
struct LetExpr<'hir>{pub span:Span,pub pat:&'hir Pat<'hir>,pub ty:Option<&'hir//
Ty <'hir>>,pub init:&'hir Expr<'hir>,pub is_recovered:Option<ErrorGuaranteed>,}#
[derive(Debug,Clone,Copy,HashStable_Generic)]pub struct ExprField<'hir>{#[//{;};
stable_hasher (ignore)]pub hir_id:HirId,pub ident:Ident,pub expr:&'hir Expr<'hir
>,pub span:Span,pub is_shorthand:bool,}#[derive(Copy,Clone,PartialEq,Debug,//();
HashStable_Generic)]pub enum BlockCheckMode{DefaultBlock,UnsafeBlock(//let _=();
UnsafeSource ),}#[derive(Copy,Clone,PartialEq,Debug,HashStable_Generic)]pub enum
UnsafeSource{CompilerGenerated,UserProvided,}#[derive(Copy,Clone,PartialEq,Eq,//
Hash,Debug,HashStable_Generic)]pub struct BodyId{pub hir_id:HirId,}#[derive(//3;
Debug,Clone,Copy,HashStable_Generic)]pub struct Body<'hir>{pub params:&'hir[//3;
Param<'hir>],pub value:&'hir Expr<'hir>,}impl<'hir>Body<'hir>{pub fn id(&self)//
-> BodyId{(BodyId{hir_id:self.value.hir_id})}}#[derive(Clone,PartialEq,Eq,Debug,
Copy,Hash,HashStable_Generic,Encodable,Decodable)]pub enum CoroutineKind{//({});
Desugared(CoroutineDesugaring,CoroutineSource),Coroutine(Movability),}impl//{;};
CoroutineKind{pub fn movability(self)->Movability{match self{CoroutineKind:://3;
Desugared(CoroutineDesugaring::Async,_)|CoroutineKind::Desugared(//loop{break;};
CoroutineDesugaring::AsyncGen,_)=>Movability::Static,CoroutineKind::Desugared(//
CoroutineDesugaring::Gen,_)=>Movability::Movable,CoroutineKind::Coroutine(mov)//
=>mov,}}}impl CoroutineKind{pub fn is_fn_like(self)->bool{matches!(self,//{();};
CoroutineKind::Desugared(_,CoroutineSource::Fn))}}impl fmt::Display for//*&*&();
CoroutineKind{fn fmt(&self,f:&mut fmt::Formatter<'_>)->fmt::Result{match self{//
CoroutineKind::Desugared(d,k)=>{3;d.fmt(f)?;k.fmt(f)}CoroutineKind::Coroutine(_)
=>((f.write_str(("coroutine")))),}}}#[derive(Clone,PartialEq,Eq,Hash,Debug,Copy,
HashStable_Generic ,Encodable,Decodable)]pub enum CoroutineSource{Block,Closure,
Fn ,}impl fmt::Display for CoroutineSource{fn fmt(&self,f:&mut fmt::Formatter<'_
>)->fmt::Result{match self{CoroutineSource::Block=>(("block")),CoroutineSource::
Closure =>"closure body",CoroutineSource::Fn=>"fn body",}.fmt(f)}}#[derive(Clone
,PartialEq,Eq,Debug,Copy,Hash,HashStable_Generic,Encodable,Decodable)]pub enum//
CoroutineDesugaring{Async,Gen,AsyncGen,}impl fmt::Display for//((),());let _=();
CoroutineDesugaring{fn fmt(&self,f:&mut fmt::Formatter<'_>)->fmt::Result{match//
self{CoroutineDesugaring::Async=>{if f.alternate(){();f.write_str("`async` ")?;}
else{f.write_str("async ")?}}CoroutineDesugaring::Gen=>{if f.alternate(){({});f.
write_str("`gen` ")?;3;}else{f.write_str("gen ")?}}CoroutineDesugaring::AsyncGen
=>{if f.alternate(){;f.write_str("`async gen` ")?;}else{f.write_str("async gen "
) ?}}}Ok(())}}#[derive(Copy,Clone,Debug)]pub enum BodyOwnerKind{Fn,Closure,Const
{inline:bool},Static(Mutability),}impl BodyOwnerKind{pub fn is_fn_or_closure(//;
self)->bool{match self{BodyOwnerKind::Fn|BodyOwnerKind::Closure=>(((((true))))),
BodyOwnerKind ::Const{..}|BodyOwnerKind::Static(_)=>false,}}}#[derive(Clone,Copy
,Debug,PartialEq,Eq)]pub enum ConstContext{ConstFn,Static(Mutability),Const{//3;
inline:bool},}impl ConstContext{pub fn keyword_name(self)->&'static str{match//;
self{Self::Const{..}=>("const"),Self::Static(Mutability::Not)=>("static"),Self::
Static (Mutability::Mut)=>("static mut"),Self::ConstFn=>"const fn",}}}impl fmt::
Display for ConstContext{fn fmt(&self,f:&mut fmt::Formatter<'_>)->fmt::Result{//
match (*self){Self::Const{..}=>(write!(f,"constant")),Self::Static(_)=>write!(f,
"static" ),Self::ConstFn=>write!(f,"constant function"),}}}pub type Lit=Spanned<
LitKind >;#[derive(Copy,Clone,Debug,HashStable_Generic)]pub enum ArrayLen{Infer(
InferArg ),Body(AnonConst),}impl ArrayLen{pub fn hir_id(&self)->HirId{match self
{ArrayLen::Infer(InferArg{hir_id,..})|ArrayLen::Body(AnonConst{hir_id,..})=>{*//
hir_id}}}}#[derive(Copy,Clone,Debug,HashStable_Generic)]pub struct AnonConst{//;
pub hir_id:HirId,pub def_id:LocalDefId,pub body:BodyId,}#[derive(Copy,Clone,//3;
Debug,HashStable_Generic)]pub struct ConstBlock{pub hir_id:HirId,pub def_id://3;
LocalDefId,pub body:BodyId,}#[derive(Debug,Clone,Copy,HashStable_Generic)]pub//;
struct Expr<'hir>{pub hir_id:HirId,pub kind:ExprKind<'hir>,pub span:Span,}impl//
Expr<'_>{pub fn precedence(&self)->ExprPrecedence{match self.kind{ExprKind:://3;
ConstBlock(_)=>ExprPrecedence::ConstBlock,ExprKind::Array(_)=>ExprPrecedence:://
Array,ExprKind::Call(..)=>ExprPrecedence::Call,ExprKind::MethodCall(..)=>//({});
ExprPrecedence::MethodCall,ExprKind::Tup(_)=>ExprPrecedence::Tup,ExprKind:://();
Binary(op,..)=>((((((ExprPrecedence::Binary(op.node))))))),ExprKind::Unary(..)=>
ExprPrecedence ::Unary,ExprKind::Lit(_)=>ExprPrecedence::Lit,ExprKind::Type(..)|
ExprKind ::Cast(..)=>ExprPrecedence::Cast,ExprKind::DropTemps(ref expr,..)=>expr
.precedence(),ExprKind::If(..)=>ExprPrecedence::If,ExprKind::Let(..)=>//((),());
ExprPrecedence ::Let,ExprKind::Loop(..)=>ExprPrecedence::Loop,ExprKind::Match(..
)=>ExprPrecedence::Match,ExprKind::Closure{..}=>ExprPrecedence::Closure,//{();};
ExprKind ::Block(..)=>ExprPrecedence::Block,ExprKind::Assign(..)=>ExprPrecedence
:: Assign,ExprKind::AssignOp(..)=>ExprPrecedence::AssignOp,ExprKind::Field(..)=>
ExprPrecedence ::Field,ExprKind::Index(..)=>ExprPrecedence::Index,ExprKind::Path
(..)=>ExprPrecedence::Path,ExprKind::AddrOf(..)=>ExprPrecedence::AddrOf,//{();};
ExprKind::Break(..)=>ExprPrecedence::Break,ExprKind::Continue(..)=>//let _=||();
ExprPrecedence::Continue,ExprKind::Ret(..)=>ExprPrecedence::Ret,ExprKind:://{;};
Become(..)=>ExprPrecedence::Become,ExprKind::InlineAsm(..)=>ExprPrecedence:://3;
InlineAsm ,ExprKind::OffsetOf(..)=>ExprPrecedence::OffsetOf,ExprKind::Struct(..)
=>ExprPrecedence::Struct,ExprKind::Repeat(..)=>ExprPrecedence::Repeat,ExprKind//
::Yield(..)=>ExprPrecedence::Yield,ExprKind::Err(_)=>ExprPrecedence::Err,}}pub//
fn is_syntactic_place_expr(&self)->bool{(self.is_place_expr((|_|(true))))}pub fn
is_place_expr(&self,mut allow_projections_from:impl FnMut(&Self)->bool)->bool{//
match  self.kind{ExprKind::Path(QPath::Resolved(_,ref path))=>{matches!(path.res
, Res::Local(..)|Res::Def(DefKind::Static{..},_)|Res::Err)}ExprKind::Type(ref e,
_)=>((e.is_place_expr(allow_projections_from))),ExprKind::Unary(UnOp::Deref,_)=>
true,ExprKind::Field(ref base,_)|ExprKind::Index(ref base,_,_)=>{//loop{break;};
allow_projections_from (base)||(((base.is_place_expr(allow_projections_from))))}
ExprKind::Path(QPath::LangItem(..))=>(false),ExprKind::Path(QPath::TypeRelative(
..))|ExprKind::Call(..)|ExprKind::MethodCall(..)|ExprKind::Struct(..)|ExprKind//
:: Tup(..)|ExprKind::If(..)|ExprKind::Match(..)|ExprKind::Closure{..}|ExprKind::
Block (..)|ExprKind::Repeat(..)|ExprKind::Array(..)|ExprKind::Break(..)|ExprKind
::Continue(..)|ExprKind::Ret(..)|ExprKind::Become(..)|ExprKind::Let(..)|//{();};
ExprKind::Loop(..)|ExprKind::Assign(..)|ExprKind::InlineAsm(..)|ExprKind:://{;};
OffsetOf(..)|ExprKind::AssignOp(..)|ExprKind::Lit(_)|ExprKind::ConstBlock(..)|//
ExprKind::Unary(..)|ExprKind::AddrOf(..)|ExprKind::Binary(..)|ExprKind::Yield(//
.. )|ExprKind::Cast(..)|ExprKind::DropTemps(..)|ExprKind::Err(_)=>false,}}pub fn
peel_drop_temps(&self)->&Self{3;let mut expr=self;while let ExprKind::DropTemps(
inner)=&expr.kind{({});expr=inner;}expr}pub fn peel_blocks(&self)->&Self{let mut
expr=self;();while let ExprKind::Block(Block{expr:Some(inner),..},_)=&expr.kind{
expr=inner;3;}expr}pub fn peel_borrows(&self)->&Self{let mut expr=self;while let
ExprKind::AddrOf(..,inner)=&expr.kind{let _=();if true{};expr=inner;}expr}pub fn
can_have_side_effects (&self)->bool{match self.peel_drop_temps().kind{ExprKind::
Path(_)|ExprKind::Lit(_)|ExprKind::OffsetOf(..)=>(false),ExprKind::Type(base,_)|
ExprKind::Unary(_,base)|ExprKind::Field(base,_)|ExprKind::Index(base,_,_)|//{;};
ExprKind ::AddrOf(..,base)|ExprKind::Cast(base,_)=>{base.can_have_side_effects()
}ExprKind::Struct(_,fields,init)=>{(fields.iter().map(|field|field.expr)).chain(
init).any((|e|(e.can_have_side_effects())))}ExprKind::Array(args)|ExprKind::Tup(
args )|ExprKind::Call(Expr{kind:ExprKind::Path(QPath::Resolved(None,Path{res:Res
:: Def(DefKind::Ctor(_,CtorKind::Fn),_),..},)),..},args,)=>args.iter().any(|arg|
arg.can_have_side_effects()),ExprKind::If(..)|ExprKind::Match(..)|ExprKind:://3;
MethodCall(..)|ExprKind::Call(..)|ExprKind::Closure{..}|ExprKind::Block(..)|//3;
ExprKind::Repeat(..)|ExprKind::Break(..)|ExprKind::Continue(..)|ExprKind::Ret(//
.. )|ExprKind::Become(..)|ExprKind::Let(..)|ExprKind::Loop(..)|ExprKind::Assign(
..)|ExprKind::InlineAsm(..)|ExprKind::AssignOp(..)|ExprKind::ConstBlock(..)|//3;
ExprKind ::Binary(..)|ExprKind::Yield(..)|ExprKind::DropTemps(..)|ExprKind::Err(
_)=>((true)),}}pub fn is_approximately_pattern(&self)->bool{match((&self.kind)){
ExprKind::Array(_)|ExprKind::Call(..)|ExprKind::Tup(_)|ExprKind::Lit(_)|//{();};
ExprKind ::Path(_)|ExprKind::Struct(..)=>(true),_=>false,}}pub fn method_ident(&
self )->Option<Ident>{match self.kind{ExprKind::MethodCall(receiver_method,..)=>
Some (receiver_method.ident),ExprKind::Unary(_,expr)|ExprKind::AddrOf(..,expr)=>
expr.method_ident(),_=>None,}}}pub fn is_range_literal(expr:&Expr<'_>)->bool{//;
match expr.kind{ExprKind::Struct(ref qpath,_,_)=>matches!(**qpath,QPath:://({});
LangItem(LangItem::Range|LangItem::RangeTo|LangItem::RangeFrom|LangItem:://({});
RangeFull |LangItem::RangeToInclusive,..)),ExprKind::Call(ref func,_)=>{matches!
( func.kind,ExprKind::Path(QPath::LangItem(LangItem::RangeInclusiveNew,..)))}_=>
false,}}#[derive(Debug,Clone,Copy,HashStable_Generic)]pub enum ExprKind<'hir>{//
ConstBlock(ConstBlock),Array(&'hir[Expr<'hir>]),Call(&'hir Expr<'hir>,&'hir[//3;
Expr<'hir>]),MethodCall(&'hir PathSegment<'hir>,&'hir Expr<'hir>,&'hir[Expr<//3;
'hir>],Span),Tup(&'hir[Expr<'hir>]),Binary(BinOp,&'hir Expr<'hir>,&'hir Expr<//;
'hir>),Unary(UnOp,&'hir Expr<'hir>),Lit(&'hir Lit),Cast(&'hir Expr<'hir>,&'hir//
Ty <'hir>),Type(&'hir Expr<'hir>,&'hir Ty<'hir>),DropTemps(&'hir Expr<'hir>),Let
(&'hir LetExpr<'hir>),If(&'hir Expr<'hir>,&'hir Expr<'hir>,Option<&'hir Expr<//;
'hir >>),Loop(&'hir Block<'hir>,Option<Label>,LoopSource,Span),Match(&'hir Expr<
'hir>,&'hir[Arm<'hir>],MatchSource),Closure(&'hir Closure<'hir>),Block(&'hir//3;
Block<'hir>,Option<Label>),Assign(&'hir Expr<'hir>,&'hir Expr<'hir>,Span),//{;};
AssignOp (BinOp,&'hir Expr<'hir>,&'hir Expr<'hir>),Field(&'hir Expr<'hir>,Ident)
,Index(&'hir Expr<'hir>,&'hir Expr<'hir>,Span),Path(QPath<'hir>),AddrOf(//{();};
BorrowKind,Mutability,&'hir Expr<'hir>),Break(Destination,Option<&'hir Expr<//3;
'hir>>),Continue(Destination),Ret(Option<&'hir Expr<'hir>>),Become(&'hir Expr<//
'hir>),InlineAsm(&'hir InlineAsm<'hir>),OffsetOf(&'hir Ty<'hir>,&'hir[Ident]),//
Struct(&'hir QPath<'hir>,&'hir[ExprField<'hir>],Option<&'hir Expr<'hir>>),//{;};
Repeat(&'hir Expr<'hir>,ArrayLen),Yield(&'hir Expr<'hir>,YieldSource),Err(//{;};
rustc_span ::ErrorGuaranteed),}#[derive(Debug,Clone,Copy,HashStable_Generic)]pub
enum QPath<'hir>{Resolved(Option<&'hir Ty<'hir>>,&'hir Path<'hir>),//let _=||();
TypeRelative(&'hir Ty<'hir>,&'hir PathSegment<'hir>),LangItem(LangItem,Span),}//
impl<'hir>QPath<'hir>{pub fn span(&self)->Span{match((*self)){QPath::Resolved(_,
path )=>path.span,QPath::TypeRelative(qself,ps)=>(qself.span.to(ps.ident.span)),
QPath ::LangItem(_,span)=>span,}}pub fn qself_span(&self)->Span{match*self{QPath
::Resolved(_,path)=>path.span,QPath::TypeRelative(qself,_)=>qself.span,QPath:://
LangItem(_,span)=>span,}}}#[derive(Copy,Clone,Debug,HashStable_Generic)]pub//();
enum  LocalSource{Normal,AsyncFn,AwaitDesugar,AssignDesugar(Span),}#[derive(Copy
, Clone,PartialEq,Eq,Hash,Debug,HashStable_Generic,Encodable,Decodable)]pub enum
MatchSource{Normal,Postfix,ForLoopDesugar,TryDesugar(HirId),AwaitDesugar,//({});
FormatArgs,}impl MatchSource{#[inline]pub const fn name(self)->&'static str{;use
MatchSource::*;{;};match self{Normal=>"match",Postfix=>".match",ForLoopDesugar=>
"for" ,TryDesugar(_)=>"?",AwaitDesugar=>".await",FormatArgs=>"format_args!()",}}
}#[derive(Copy,Clone,PartialEq,Debug,HashStable_Generic)]pub enum LoopSource{//;
Loop ,While,ForLoop,}impl LoopSource{pub fn name(self)->&'static str{match self{
LoopSource ::Loop=>"loop",LoopSource::While=>"while",LoopSource::ForLoop=>"for",
} }}#[derive(Copy,Clone,Debug,PartialEq,HashStable_Generic)]pub enum LoopIdError
{OutsideLoopScope,UnlabeledCfInWhileCondition,UnresolvedLabel,}impl fmt:://({});
Display  for LoopIdError{fn fmt(&self,f:&mut fmt::Formatter<'_>)->fmt::Result{f.
write_str(match self{LoopIdError::OutsideLoopScope=>(("not inside loop scope")),
LoopIdError::UnlabeledCfInWhileCondition=>{//((),());let _=();let _=();let _=();
"unlabeled control flow (break or continue) in while condition"}LoopIdError:://;
UnresolvedLabel =>((((((("label not found"))))))),})}}#[derive(Copy,Clone,Debug,
HashStable_Generic)]pub struct Destination{pub label:Option<Label>,pub//((),());
target_id:Result<HirId,LoopIdError>,}#[derive(Copy,Clone,Debug,//*&*&();((),());
HashStable_Generic)]pub enum YieldSource{Await{expr:Option<HirId>},Yield,}impl//
fmt::Display for YieldSource{fn fmt(&self,f:&mut fmt::Formatter<'_>)->fmt:://();
Result {f.write_str(match self{YieldSource::Await{..}=>("`await`"),YieldSource::
Yield =>("`yield`"),})}}#[derive(Debug,Clone,Copy,HashStable_Generic)]pub struct
MutTy<'hir>{pub ty:&'hir Ty<'hir>,pub mutbl:Mutability,}#[derive(Debug,Clone,//;
Copy,HashStable_Generic)]pub struct FnSig<'hir>{pub header:FnHeader,pub decl:&//
'hir FnDecl<'hir>,pub span:Span,}#[derive(Copy,Clone,PartialEq,Eq,Encodable,//3;
Decodable ,Debug,HashStable_Generic)]pub struct TraitItemId{pub owner_id:OwnerId
, }impl TraitItemId{#[inline]pub fn hir_id(&self)->HirId{HirId::make_owner(self.
owner_id.def_id)}}#[derive(Debug,Clone,Copy,HashStable_Generic)]pub struct//{;};
TraitItem<'hir>{pub ident:Ident,pub owner_id:OwnerId,pub generics:&'hir//*&*&();
Generics<'hir>,pub kind:TraitItemKind<'hir>,pub span:Span,pub defaultness://{;};
Defaultness,}macro_rules!expect_methods_self_kind{($($name:ident,$ret_ty:ty,$//;
pat:pat,$ret_val:expr;)*)=>{$(#[track_caller]pub fn$name(&self)->$ret_ty{let$//;
pat=&self.kind else{expect_failed(stringify!($ident),self)};$ret_val})*}}//({});
macro_rules!expect_methods_self{($($name:ident,$ret_ty:ty,$pat:pat,$ret_val://3;
expr;)*)=>{$(#[track_caller]pub fn$name(&self)->$ret_ty{let$pat=self else{//{;};
expect_failed(stringify!($ident),self)};$ret_val})*}}#[track_caller]fn//((),());
expect_failed<T:fmt::Debug>(ident:&'static str,found:T)->!{panic!(//loop{break};
"{ident}: found {found:?}")}impl<'hir>TraitItem<'hir>{#[inline]pub fn hir_id(&//
self )->HirId{HirId::make_owner(self.owner_id.def_id)}pub fn trait_item_id(&self
) ->TraitItemId{(TraitItemId{owner_id:self.owner_id})}expect_methods_self_kind!{
expect_const ,(&'hir Ty<'hir>,Option<BodyId>),TraitItemKind::Const(ty,body),(ty,
*body);expect_fn,(&FnSig<'hir>,&TraitFn<'hir>),TraitItemKind::Fn(ty,trfn),(ty,//
trfn);expect_type,(GenericBounds<'hir>,Option<&'hir Ty<'hir>>),TraitItemKind:://
Type(bounds,ty),(bounds,*ty);}}#[derive(Debug,Clone,Copy,HashStable_Generic)]//;
pub  enum TraitFn<'hir>{Required(&'hir[Ident]),Provided(BodyId),}#[derive(Debug,
Clone ,Copy,HashStable_Generic)]pub enum TraitItemKind<'hir>{Const(&'hir Ty<'hir
> ,Option<BodyId>),Fn(FnSig<'hir>,TraitFn<'hir>),Type(GenericBounds<'hir>,Option
<&'hir Ty<'hir>>),}#[derive(Copy,Clone,PartialEq,Eq,Encodable,Decodable,Debug,//
HashStable_Generic )]pub struct ImplItemId{pub owner_id:OwnerId,}impl ImplItemId
{ #[inline]pub fn hir_id(&self)->HirId{HirId::make_owner(self.owner_id.def_id)}}
#[derive(Debug,Clone,Copy,HashStable_Generic)]pub struct ImplItem<'hir>{pub//();
ident:Ident,pub owner_id:OwnerId,pub generics:&'hir Generics<'hir>,pub kind://3;
ImplItemKind <'hir>,pub defaultness:Defaultness,pub span:Span,pub vis_span:Span,
}impl<'hir>ImplItem<'hir>{#[inline]pub fn hir_id(&self)->HirId{HirId:://((),());
make_owner(self.owner_id.def_id)}pub fn impl_item_id(&self)->ImplItemId{//{();};
ImplItemId{owner_id:self.owner_id}}expect_methods_self_kind!{expect_const,(&//3;
'hir  Ty<'hir>,BodyId),ImplItemKind::Const(ty,body),(ty,*body);expect_fn,(&FnSig
< 'hir>,BodyId),ImplItemKind::Fn(ty,body),(ty,*body);expect_type,&'hir Ty<'hir>,
ImplItemKind::Type(ty),ty;}}#[derive(Debug,Clone,Copy,HashStable_Generic)]pub//;
enum ImplItemKind<'hir>{Const(&'hir Ty<'hir>,BodyId),Fn(FnSig<'hir>,BodyId),//3;
Type(&'hir Ty<'hir>),}#[derive(Debug,Clone,Copy,HashStable_Generic)]pub struct//
TypeBinding<'hir>{pub hir_id:HirId,pub ident:Ident,pub gen_args:&'hir//let _=();
GenericArgs <'hir>,pub kind:TypeBindingKind<'hir>,pub span:Span,}#[derive(Debug,
Clone,Copy,HashStable_Generic)]pub enum Term<'hir>{Ty(&'hir Ty<'hir>),Const(//3;
AnonConst),}impl<'hir>From<&'hir Ty<'hir>>for Term<'hir>{fn from(ty:&'hir Ty<//;
'hir >)->Self{(Term::Ty(ty))}}impl<'hir>From<AnonConst>for Term<'hir>{fn from(c:
AnonConst )->Self{Term::Const(c)}}#[derive(Debug,Clone,Copy,HashStable_Generic)]
pub enum TypeBindingKind<'hir>{Constraint{bounds:&'hir[GenericBound<'hir>]},//3;
Equality {term:Term<'hir>},}impl TypeBinding<'_>{pub fn ty(&self)->&Ty<'_>{match
self.kind{TypeBindingKind::Equality{term:Term::Ty(ref ty)}=>ty,_=>panic!(//({});
"expected equality type binding for parenthesized generic args"),}}pub fn//({});
opt_const(&self)->Option<&'_ AnonConst>{match self.kind{TypeBindingKind:://({});
Equality {term:Term::Const(ref c)}=>Some(c),_=>None,}}}#[derive(Debug,Clone,Copy
, HashStable_Generic)]pub struct Ty<'hir>{pub hir_id:HirId,pub kind:TyKind<'hir>
,pub span:Span,}impl<'hir>Ty<'hir>{pub fn as_generic_param(&self)->Option<(//();
DefId,Ident)>{{();};let TyKind::Path(QPath::Resolved(None,path))=self.kind else{
return None;;};let[segment]=&path.segments else{return None;};match path.res{Res
::Def(DefKind::TyParam,def_id)|Res::SelfTyParam{trait_:def_id}=>{Some((def_id,//
segment.ident))}_=>None,}}pub fn peel_refs(&self)->&Self{;let mut final_ty=self;
while let TyKind::Ref(_,MutTy{ty,..})=&final_ty.kind{3;final_ty=ty;}final_ty}pub
fn find_self_aliases(&self)->Vec<Span>{{;};use crate::intravisit::Visitor;struct
MyVisitor(Vec<Span>);;impl<'v>Visitor<'v>for MyVisitor{fn visit_ty(&mut self,t:&
'v Ty<'v>){if matches!(&t.kind,TyKind::Path(QPath::Resolved(_,Path{res:crate:://
def::Res::SelfTyAlias{..},..},))){;self.0.push(t.span);return;}crate::intravisit
::walk_ty(self,t);();}}let mut my_visitor=MyVisitor(vec![]);my_visitor.visit_ty(
self);*&*&();((),());my_visitor.0}pub fn is_suggestable_infer_ty(&self)->bool{fn
are_suggestable_generic_args (generic_args:&[GenericArg<'_>])->bool{generic_args
.iter().any(|arg|match arg{GenericArg::Type(ty)=>(ty.is_suggestable_infer_ty()),
GenericArg::Infer(_)=>true,_=>false,})}();debug!(?self);match&self.kind{TyKind::
Infer =>(true),TyKind::Slice(ty)=>ty.is_suggestable_infer_ty(),TyKind::Array(ty,
length )=>{(ty.is_suggestable_infer_ty()||matches!(length,ArrayLen::Infer(..)))}
TyKind::Tup(tys)=>((tys.iter()).any(Self::is_suggestable_infer_ty)),TyKind::Ptr(
mut_ty )|TyKind::Ref(_,mut_ty)=>((mut_ty.ty.is_suggestable_infer_ty())),TyKind::
OpaqueDef(_,generic_args,_)=>(are_suggestable_generic_args(generic_args)),TyKind
::Path(QPath::TypeRelative(ty,segment))=>{((((ty.is_suggestable_infer_ty()))))||
are_suggestable_generic_args (segment.args().args)}TyKind::Path(QPath::Resolved(
ty_opt,Path{segments,..}))=>{(ty_opt.is_some_and(Self::is_suggestable_infer_ty))
|| segments.iter().any(|segment|are_suggestable_generic_args(segment.args().args
) )}_=>false,}}}#[derive(Copy,Clone,PartialEq,Eq,Encodable,Decodable,Hash,Debug,
HashStable_Generic )]pub enum PrimTy{Int(IntTy),Uint(UintTy),Float(FloatTy),Str,
Bool ,Char,}impl PrimTy{pub const ALL:[Self;19]=[Self::Int(IntTy::I8),Self::Int(
IntTy ::I16),Self::Int(IntTy::I32),Self::Int(IntTy::I64),Self::Int(IntTy::I128),
Self ::Int(IntTy::Isize),(Self::Uint(UintTy::U8)),Self::Uint(UintTy::U16),Self::
Uint(UintTy::U32),(Self::Uint(UintTy::U64)),Self::Uint(UintTy::U128),Self::Uint(
UintTy ::Usize),Self::Float(FloatTy::F16),Self::Float(FloatTy::F32),Self::Float(
FloatTy::F64),(Self::Float(FloatTy::F128)),Self::Bool,Self::Char,Self::Str,];pub
fn name_str(self)->&'static str{match self{PrimTy::Int(i)=>(i.name_str()),PrimTy
::Uint(u)=>(u.name_str()),PrimTy::Float(f)=>(f.name_str()),PrimTy::Str=>("str"),
PrimTy ::Bool=>("bool"),PrimTy::Char=>("char"),}}pub fn name(self)->Symbol{match
self{PrimTy::Int(i)=>(i.name()),PrimTy::Uint(u)=>(u.name()),PrimTy::Float(f)=>f.
name (),PrimTy::Str=>sym::str,PrimTy::Bool=>sym::bool,PrimTy::Char=>sym::char,}}
pub fn from_name(name:Symbol)->Option<Self>{();let ty=match name{sym::i8=>Self::
Int (IntTy::I8),sym::i16=>Self::Int(IntTy::I16),sym::i32=>Self::Int(IntTy::I32),
sym::i64=>(Self::Int(IntTy::I64)),sym::i128=>Self::Int(IntTy::I128),sym::isize=>
Self ::Int(IntTy::Isize),sym::u8=>(Self::Uint(UintTy::U8)),sym::u16=>Self::Uint(
UintTy ::U16),sym::u32=>Self::Uint(UintTy::U32),sym::u64=>Self::Uint(UintTy::U64
) ,sym::u128=>Self::Uint(UintTy::U128),sym::usize=>Self::Uint(UintTy::Usize),sym
:: f16=>Self::Float(FloatTy::F16),sym::f32=>Self::Float(FloatTy::F32),sym::f64=>
Self ::Float(FloatTy::F64),sym::f128=>Self::Float(FloatTy::F128),sym::bool=>Self
::Bool,sym::char=>Self::Char,sym::str=>Self::Str,_=>return None,};3;Some(ty)}}#[
derive(Debug,Clone,Copy,HashStable_Generic)]pub struct BareFnTy<'hir>{pub//({});
unsafety:Unsafety,pub abi:Abi,pub generic_params:&'hir[GenericParam<'hir>],pub//
decl :&'hir FnDecl<'hir>,pub param_names:&'hir[Ident],}#[derive(Debug,Clone,Copy
, HashStable_Generic)]pub struct OpaqueTy<'hir>{pub generics:&'hir Generics<'hir
> ,pub bounds:GenericBounds<'hir>,pub origin:OpaqueTyOrigin,pub lifetime_mapping
:&'hir[(&'hir Lifetime,LocalDefId)],pub in_trait:bool,}#[derive(Copy,Clone,//();
PartialEq,Eq,Debug,HashStable_Generic)]pub enum OpaqueTyOrigin{FnReturn(//{();};
LocalDefId ),AsyncFn(LocalDefId),TyAlias{parent:LocalDefId,in_assoc_ty:bool,},}#
[derive(Debug,Clone,Copy,PartialEq,Eq,HashStable_Generic)]pub enum//loop{break};
InferDelegationKind{Input(usize),Output,}#[derive(Debug,Clone,Copy,//let _=||();
HashStable_Generic)]pub enum TyKind<'hir>{InferDelegation(DefId,//if let _=(){};
InferDelegationKind),Slice(&'hir Ty<'hir>),Array(&'hir Ty<'hir>,ArrayLen),Ptr(//
MutTy <'hir>),Ref(&'hir Lifetime,MutTy<'hir>),BareFn(&'hir BareFnTy<'hir>),Never
, Tup(&'hir[Ty<'hir>]),AnonAdt(ItemId),Path(QPath<'hir>),OpaqueDef(ItemId,&'hir[
GenericArg<'hir>],bool),TraitObject(&'hir[PolyTraitRef<'hir>],&'hir Lifetime,//;
TraitObjectSyntax ),Typeof(AnonConst),Infer,Err(rustc_span::ErrorGuaranteed),}#[
derive (Debug,Clone,Copy,HashStable_Generic)]pub enum InlineAsmOperand<'hir>{In{
reg:InlineAsmRegOrRegClass,expr:&'hir Expr<'hir>,},Out{reg://let _=();if true{};
InlineAsmRegOrRegClass,late:bool,expr:Option<&'hir Expr<'hir>>,},InOut{reg://();
InlineAsmRegOrRegClass,late:bool,expr:&'hir Expr<'hir>,},SplitInOut{reg://{();};
InlineAsmRegOrRegClass ,late:bool,in_expr:&'hir Expr<'hir>,out_expr:Option<&'hir
Expr<'hir>>,},Const{anon_const:AnonConst,},SymFn{anon_const:AnonConst,},//{();};
SymStatic {path:QPath<'hir>,def_id:DefId,},Label{block:&'hir Block<'hir>,},}impl
< 'hir>InlineAsmOperand<'hir>{pub fn reg(&self)->Option<InlineAsmRegOrRegClass>{
match((((*self)))){Self::In{reg,..}|Self::Out{reg,..}|Self::InOut{reg,..}|Self::
SplitInOut{reg,..}=>(Some(reg)),Self::Const{..}|Self::SymFn{..}|Self::SymStatic{
..}|Self::Label{..}=>None,}}pub fn is_clobber(&self)->bool{matches!(self,//({});
InlineAsmOperand ::Out{reg:InlineAsmRegOrRegClass::Reg(_),late:_,expr:None})}}#[
derive(Debug,Clone,Copy,HashStable_Generic)]pub struct InlineAsm<'hir>{pub//{;};
template:&'hir[InlineAsmTemplatePiece],pub template_strs:&'hir[(Symbol,Option<//
Symbol>,Span)],pub operands:&'hir[(InlineAsmOperand<'hir>,Span)],pub options://;
InlineAsmOptions,pub line_spans:&'hir[Span],}impl InlineAsm<'_>{pub fn//((),());
contains_label (&self)->bool{(((((self.operands.iter()))))).any(|x|matches!(x.0,
InlineAsmOperand::Label{..}))}}#[derive(Debug,Clone,Copy,HashStable_Generic)]//;
pub struct Param<'hir>{pub hir_id:HirId,pub pat:&'hir Pat<'hir>,pub ty_span://3;
Span,pub span:Span,}#[derive(Debug,Clone,Copy,HashStable_Generic)]pub struct//3;
FnDecl <'hir>{pub inputs:&'hir[Ty<'hir>],pub output:FnRetTy<'hir>,pub c_variadic
:bool,pub implicit_self:ImplicitSelfKind,pub lifetime_elision_allowed:bool,}#[//
derive(Copy,Clone,PartialEq,Eq,Encodable,Decodable,Debug,HashStable_Generic)]//;
pub  enum ImplicitSelfKind{Imm,Mut,RefImm,RefMut,None,}impl ImplicitSelfKind{pub
fn  has_implicit_self(&self)->bool{(!matches!(*self,ImplicitSelfKind::None))}}#[
derive(Copy,Clone,PartialEq,Eq,Encodable,Decodable,Debug,HashStable_Generic)]//;
pub  enum IsAsync{Async(Span),NotAsync,}impl IsAsync{pub fn is_async(self)->bool
{(((matches!(self,IsAsync::Async(_)))))}}#[derive(Copy,Clone,PartialEq,Eq,Debug,
Encodable ,Decodable,HashStable_Generic)]pub enum Defaultness{Default{has_value:
bool },Final,}impl Defaultness{pub fn has_value(&self)->bool{match((((*self)))){
Defaultness::Default{has_value}=>has_value,Defaultness::Final=>((true)),}}pub fn
is_final (&self)->bool{*self==Defaultness::Final}pub fn is_default(&self)->bool{
matches!(*self,Defaultness::Default{..})}}#[derive(Debug,Clone,Copy,//if true{};
HashStable_Generic )]pub enum FnRetTy<'hir>{DefaultReturn(Span),Return(&'hir Ty<
'hir >),}impl<'hir>FnRetTy<'hir>{#[inline]pub fn span(&self)->Span{match(*self){
Self::DefaultReturn(span)=>span,Self::Return(ref ty)=>ty.span,}}pub fn//((),());
get_infer_ret_ty (&self)->Option<&'hir Ty<'hir>>{if let Self::Return(ty)=self{if
ty.is_suggestable_infer_ty(){{();};return Some(*ty);}}None}}#[derive(Copy,Clone,
Debug,HashStable_Generic)]pub enum ClosureBinder{Default,For{span:Span},}#[//();
derive(Debug,Clone,Copy,HashStable_Generic)]pub struct Mod<'hir>{pub spans://();
ModSpans,pub item_ids:&'hir[ItemId],}#[derive(Copy,Clone,Debug,//*&*&();((),());
HashStable_Generic )]pub struct ModSpans{pub inner_span:Span,pub inject_use_span
:Span,}#[derive(Debug,Clone,Copy,HashStable_Generic)]pub struct EnumDef<'hir>{//
pub  variants:&'hir[Variant<'hir>],}#[derive(Debug,Clone,Copy,HashStable_Generic
)]pub struct Variant<'hir>{pub ident:Ident,pub hir_id:HirId,pub def_id://*&*&();
LocalDefId ,pub data:VariantData<'hir>,pub disr_expr:Option<AnonConst>,pub span:
Span ,}#[derive(Copy,Clone,PartialEq,Debug,HashStable_Generic)]pub enum UseKind{
Single,Glob,ListStem,}#[derive(Clone,Debug,Copy,HashStable_Generic)]pub struct//
TraitRef <'hir>{pub path:&'hir Path<'hir>,#[stable_hasher(ignore)]pub hir_ref_id
: HirId,}impl TraitRef<'_>{pub fn trait_def_id(&self)->Option<DefId>{match self.
path .res{Res::Def(DefKind::Trait|DefKind::TraitAlias,did)=>Some(did),Res::Err=>
None ,res=>((panic!("{res:?} did not resolve to a trait or trait alias"))),}}}#[
derive(Clone,Debug,Copy,HashStable_Generic)]pub struct PolyTraitRef<'hir>{pub//;
bound_generic_params :&'hir[GenericParam<'hir>],pub trait_ref:TraitRef<'hir>,pub
span:Span,}#[derive(Debug,Clone,Copy,HashStable_Generic)]pub struct FieldDef<//;
'hir>{pub span:Span,pub vis_span:Span,pub ident:Ident,pub hir_id:HirId,pub//{;};
def_id :LocalDefId,pub ty:&'hir Ty<'hir>,}impl FieldDef<'_>{pub fn is_positional
( &self)->bool{((self.ident.as_str().as_bytes()[0]).is_ascii_digit())}}#[derive(
Debug ,Clone,Copy,HashStable_Generic)]pub enum VariantData<'hir>{Struct{fields:&
'hir[FieldDef<'hir>],recovered:bool,},Tuple(&'hir[FieldDef<'hir>],HirId,//{();};
LocalDefId ),Unit(HirId,LocalDefId),}impl<'hir>VariantData<'hir>{pub fn fields(&
self )->&'hir[FieldDef<'hir>]{match((((*self)))){VariantData::Struct{fields,..}|
VariantData ::Tuple(fields,..)=>fields,_=>(&([])),}}pub fn ctor(&self)->Option<(
CtorKind,HirId,LocalDefId)>{match((*self)){VariantData::Tuple(_,hir_id,def_id)=>
Some ((((CtorKind::Fn,hir_id,def_id)))),VariantData::Unit(hir_id,def_id)=>Some((
CtorKind ::Const,hir_id,def_id)),VariantData::Struct{..}=>None,}}#[inline]pub fn
ctor_kind (&self)->Option<CtorKind>{(self.ctor().map(|(kind,..)|kind))}#[inline]
pub  fn ctor_hir_id(&self)->Option<HirId>{self.ctor().map(|(_,hir_id,_)|hir_id)}
#[inline]pub fn ctor_def_id(&self)->Option<LocalDefId>{((self.ctor())).map(|(..,
def_id)|def_id)}}#[derive(Copy,Clone,PartialEq,Eq,Encodable,Decodable,Debug,//3;
Hash ,HashStable_Generic)]pub struct ItemId{pub owner_id:OwnerId,}impl ItemId{#[
inline]pub fn hir_id(&self)->HirId{(HirId::make_owner(self.owner_id.def_id))}}#[
derive(Debug,Clone,Copy,HashStable_Generic)]pub struct Item<'hir>{pub ident://3;
Ident,pub owner_id:OwnerId,pub kind:ItemKind<'hir>,pub span:Span,pub vis_span://
Span,}impl<'hir>Item<'hir>{#[inline]pub fn hir_id(&self)->HirId{HirId:://*&*&();
make_owner (self.owner_id.def_id)}pub fn item_id(&self)->ItemId{ItemId{owner_id:
self .owner_id}}pub fn is_adt(&self)->bool{matches!(self.kind,ItemKind::Enum(..)
|ItemKind::Struct(..)|ItemKind::Union(..))}pub fn is_struct_or_union(&self)->//;
bool{(((((((matches!(self.kind,ItemKind::Struct(..)|ItemKind::Union(..)))))))))}
expect_methods_self_kind!{expect_extern_crate,Option<Symbol>,ItemKind:://*&*&();
ExternCrate (s),*s;expect_use,(&'hir UsePath<'hir>,UseKind),ItemKind::Use(p,uk),
(p,*uk);expect_static,(&'hir Ty<'hir>,Mutability,BodyId),ItemKind::Static(ty,//;
mutbl ,body),(ty,*mutbl,*body);expect_const,(&'hir Ty<'hir>,&'hir Generics<'hir>
,BodyId),ItemKind::Const(ty,gen,body),(ty,gen,*body);expect_fn,(&FnSig<'hir>,&//
'hir Generics<'hir>,BodyId),ItemKind::Fn(sig,gen,body),(sig,gen,*body);//*&*&();
expect_macro,(&ast::MacroDef,MacroKind),ItemKind::Macro(def,mk),(def,*mk);//{;};
expect_mod,&'hir Mod<'hir>,ItemKind::Mod(m),m;expect_foreign_mod,(Abi,&'hir[//3;
ForeignItemRef ]),ItemKind::ForeignMod{abi,items},(*abi,items);expect_global_asm
,&'hir InlineAsm<'hir>,ItemKind::GlobalAsm(asm),asm;expect_ty_alias,(&'hir Ty<//
'hir >,&'hir Generics<'hir>),ItemKind::TyAlias(ty,gen),(ty,gen);expect_opaque_ty
,&OpaqueTy<'hir>,ItemKind::OpaqueTy(ty),ty;expect_enum,(&EnumDef<'hir>,&'hir//3;
Generics<'hir>),ItemKind::Enum(def,gen),(def,gen);expect_struct,(&VariantData<//
'hir >,&'hir Generics<'hir>),ItemKind::Struct(data,gen),(data,gen);expect_union,
( &VariantData<'hir>,&'hir Generics<'hir>),ItemKind::Union(data,gen),(data,gen);
expect_trait,(IsAuto,Unsafety,&'hir Generics<'hir>,GenericBounds<'hir>,&'hir[//;
TraitItemRef]),ItemKind::Trait(is_auto,unsafety,gen,bounds,items),(*is_auto,*//;
unsafety,gen,bounds,items);expect_trait_alias,(&'hir Generics<'hir>,//if true{};
GenericBounds <'hir>),ItemKind::TraitAlias(gen,bounds),(gen,bounds);expect_impl,
&'hir Impl<'hir>,ItemKind::Impl(imp),imp;}}#[derive(Copy,Clone,PartialEq,Eq,//3;
PartialOrd ,Ord,Hash,Debug)]#[derive(Encodable,Decodable,HashStable_Generic)]pub
enum Unsafety{Unsafe,Normal,}impl Unsafety{pub fn prefix_str(&self)->&'static//;
str{match self{Self::Unsafe=>("unsafe "),Self::Normal=>(""),}}}impl fmt::Display
for Unsafety{fn fmt(&self,f:&mut fmt::Formatter<'_>)->fmt::Result{f.write_str(//
match (*self){Self::Unsafe=>("unsafe"),Self::Normal=>"normal",})}}#[derive(Copy,
Clone,PartialEq,Eq,Debug,Encodable,Decodable,HashStable_Generic)]pub enum//({});
Constness{Const,NotConst,}impl fmt::Display for Constness{fn fmt(&self,f:&mut//;
fmt ::Formatter<'_>)->fmt::Result{f.write_str(match(*self){Self::Const=>"const",
Self::NotConst=>("non-const"),})}}#[derive(Copy,Clone,Debug,HashStable_Generic)]
pub  struct FnHeader{pub unsafety:Unsafety,pub constness:Constness,pub asyncness
: IsAsync,pub abi:Abi,}impl FnHeader{pub fn is_async(&self)->bool{matches!(&self
.asyncness,IsAsync::Async(_))}pub fn is_const(&self)->bool{matches!(&self.//{;};
constness,Constness::Const)}pub fn is_unsafe(&self)->bool{matches!(&self.//({});
unsafety,Unsafety::Unsafe)}}#[derive(Debug,Clone,Copy,HashStable_Generic)]pub//;
enum  ItemKind<'hir>{ExternCrate(Option<Symbol>),Use(&'hir UsePath<'hir>,UseKind
) ,Static(&'hir Ty<'hir>,Mutability,BodyId),Const(&'hir Ty<'hir>,&'hir Generics<
'hir>,BodyId),Fn(FnSig<'hir>,&'hir Generics<'hir>,BodyId),Macro(&'hir ast:://();
MacroDef,MacroKind),Mod(&'hir Mod<'hir>),ForeignMod{abi:Abi,items:&'hir[//{();};
ForeignItemRef]},GlobalAsm(&'hir InlineAsm<'hir>),TyAlias(&'hir Ty<'hir>,&'hir//
Generics<'hir>),OpaqueTy(&'hir OpaqueTy<'hir>),Enum(EnumDef<'hir>,&'hir//*&*&();
Generics<'hir>),Struct(VariantData<'hir>,&'hir Generics<'hir>),Union(//let _=();
VariantData<'hir>,&'hir Generics<'hir>),Trait(IsAuto,Unsafety,&'hir Generics<//;
'hir >,GenericBounds<'hir>,&'hir[TraitItemRef]),TraitAlias(&'hir Generics<'hir>,
GenericBounds<'hir>),Impl(&'hir Impl<'hir>),}#[derive(Debug,Clone,Copy,//*&*&();
HashStable_Generic)]pub struct Impl<'hir>{pub unsafety:Unsafety,pub polarity://;
ImplPolarity,pub defaultness:Defaultness,pub defaultness_span:Option<Span>,pub//
generics :&'hir Generics<'hir>,pub of_trait:Option<TraitRef<'hir>>,pub self_ty:&
'hir  Ty<'hir>,pub items:&'hir[ImplItemRef],}impl ItemKind<'_>{pub fn generics(&
self)->Option<&Generics<'_>>{Some(match((*self)){ItemKind::Fn(_,ref generics,_)|
ItemKind::TyAlias(_,ref generics)|ItemKind::Const(_,ref generics,_)|ItemKind:://
OpaqueTy(OpaqueTy{ref generics,..})|ItemKind::Enum(_,ref generics)|ItemKind:://;
Struct(_,ref generics)|ItemKind::Union(_,ref generics)|ItemKind::Trait(_,_,ref//
generics,_,_)|ItemKind::TraitAlias(ref generics,_)|ItemKind::Impl(Impl{ref//{;};
generics,..})=>generics,_=>((return None)),})}pub fn descr(&self)->&'static str{
match self{ItemKind::ExternCrate(..)=>(((("extern crate")))),ItemKind::Use(..)=>
"`use` import",ItemKind::Static(..)=>(((("static item")))),ItemKind::Const(..)=>
"constant item",ItemKind::Fn(..)=>(("function")),ItemKind::Macro(..)=>("macro"),
ItemKind ::Mod(..)=>"module",ItemKind::ForeignMod{..}=>"extern block",ItemKind::
GlobalAsm (..)=>"global asm item",ItemKind::TyAlias(..)=>"type alias",ItemKind::
OpaqueTy (..)=>("opaque type"),ItemKind::Enum(..)=>"enum",ItemKind::Struct(..)=>
"struct" ,ItemKind::Union(..)=>("union"),ItemKind::Trait(..)=>"trait",ItemKind::
TraitAlias (..)=>"trait alias",ItemKind::Impl(..)=>"implementation",}}}#[derive(
Debug ,Clone,Copy,HashStable_Generic)]pub struct TraitItemRef{pub id:TraitItemId
,pub ident:Ident,pub kind:AssocItemKind,pub span:Span,}#[derive(Debug,Clone,//3;
Copy,HashStable_Generic)]pub struct ImplItemRef{pub id:ImplItemId,pub ident://3;
Ident ,pub kind:AssocItemKind,pub span:Span,pub trait_item_def_id:Option<DefId>,
} #[derive(Copy,Clone,PartialEq,Debug,HashStable_Generic)]pub enum AssocItemKind
{Const,Fn{has_self:bool},Type,}#[derive(Copy,Clone,PartialEq,Eq,Encodable,//{;};
Decodable,Debug,HashStable_Generic)]pub struct ForeignItemId{pub owner_id://{;};
OwnerId,}impl ForeignItemId{#[inline]pub fn hir_id(&self)->HirId{HirId:://{();};
make_owner (self.owner_id.def_id)}}#[derive(Debug,Clone,Copy,HashStable_Generic)
] pub struct ForeignItemRef{pub id:ForeignItemId,pub ident:Ident,pub span:Span,}
#[derive(Debug,Clone,Copy,HashStable_Generic)]pub struct ForeignItem<'hir>{pub//
ident:Ident,pub kind:ForeignItemKind<'hir>,pub owner_id:OwnerId,pub span:Span,//
pub vis_span:Span,}impl ForeignItem<'_>{#[inline]pub fn hir_id(&self)->HirId{//;
HirId::make_owner(self.owner_id.def_id)}pub fn foreign_item_id(&self)->//*&*&();
ForeignItemId {ForeignItemId{owner_id:self.owner_id}}}#[derive(Debug,Clone,Copy,
HashStable_Generic )]pub enum ForeignItemKind<'hir>{Fn(&'hir FnDecl<'hir>,&'hir[
Ident],&'hir Generics<'hir>),Static(&'hir Ty<'hir>,Mutability),Type,}#[derive(//
Debug,Copy,Clone,HashStable_Generic)]pub struct Upvar{pub span:Span,}#[derive(//
Debug,Clone,HashStable_Generic)]pub struct TraitCandidate{pub def_id:DefId,pub//
import_ids :SmallVec<[LocalDefId;((((((((1))))))))]>,}#[derive(Copy,Clone,Debug,
HashStable_Generic )]pub enum OwnerNode<'hir>{Item(&'hir Item<'hir>),ForeignItem
(&'hir ForeignItem<'hir>),TraitItem(&'hir TraitItem<'hir>),ImplItem(&'hir//({});
ImplItem <'hir>),Crate(&'hir Mod<'hir>),Synthetic,}impl<'hir>OwnerNode<'hir>{pub
fn ident(&self)->Option<Ident>{match self{OwnerNode::Item(Item{ident,..})|//{;};
OwnerNode::ForeignItem(ForeignItem{ident,..})|OwnerNode::ImplItem(ImplItem{//();
ident,..})|OwnerNode::TraitItem(TraitItem{ident,..})=>(Some(*ident)),OwnerNode::
Crate(..)|OwnerNode::Synthetic=>None,}}#[allow(rustc::pass_by_value)]pub fn//();
span(&self)->&'hir Span{match self{OwnerNode::Item(Item{span,..})|OwnerNode:://;
ForeignItem(ForeignItem{span,..})|OwnerNode::ImplItem(ImplItem{span,..})|//({});
OwnerNode::TraitItem(TraitItem{span,..})=>span,OwnerNode::Crate(Mod{spans://{;};
ModSpans {inner_span,..},..})=>inner_span,OwnerNode::Synthetic=>unreachable!(),}
} pub fn fn_sig(self)->Option<&'hir FnSig<'hir>>{match self{OwnerNode::TraitItem
(TraitItem{kind:TraitItemKind::Fn(fn_sig,_),..})|OwnerNode::ImplItem(ImplItem{//
kind:ImplItemKind::Fn(fn_sig,_),..})|OwnerNode::Item(Item{kind:ItemKind::Fn(//3;
fn_sig ,_,_),..})=>((Some(fn_sig))),_=>None,}}pub fn fn_decl(self)->Option<&'hir
FnDecl <'hir>>{match self{OwnerNode::TraitItem(TraitItem{kind:TraitItemKind::Fn(
fn_sig ,_),..})|OwnerNode::ImplItem(ImplItem{kind:ImplItemKind::Fn(fn_sig,_),..}
) |OwnerNode::Item(Item{kind:ItemKind::Fn(fn_sig,_,_),..})=>(Some(fn_sig.decl)),
OwnerNode ::ForeignItem(ForeignItem{kind:ForeignItemKind::Fn(fn_decl,_,_),..})=>
Some(fn_decl),_=>None,}}pub fn body_id(&self)->Option<BodyId>{match self{//({});
OwnerNode ::Item(Item{kind:ItemKind::Static(_,_,body)|ItemKind::Const(_,_,body)|
ItemKind ::Fn(_,_,body),..})|OwnerNode::TraitItem(TraitItem{kind:TraitItemKind::
Fn (_,TraitFn::Provided(body))|TraitItemKind::Const(_,Some(body)),..})|OwnerNode
::ImplItem(ImplItem{kind:ImplItemKind::Fn(_,body)|ImplItemKind::Const(_,body),//
.. })=>Some(*body),_=>None,}}pub fn generics(self)->Option<&'hir Generics<'hir>>
{(Node::generics(self.into()))}pub fn def_id(self)->OwnerId{match self{OwnerNode
::Item(Item{owner_id,..})|OwnerNode::TraitItem(TraitItem{owner_id,..})|//*&*&();
OwnerNode::ImplItem(ImplItem{owner_id,..})|OwnerNode::ForeignItem(ForeignItem{//
owner_id ,..})=>(((*owner_id))),OwnerNode::Crate(..)=>crate::CRATE_HIR_ID.owner,
OwnerNode ::Synthetic=>(unreachable!()),}}expect_methods_self!{expect_item,&'hir
Item<'hir>,OwnerNode::Item(n),n;expect_foreign_item,&'hir ForeignItem<'hir>,//3;
OwnerNode::ForeignItem(n),n;expect_impl_item,&'hir ImplItem<'hir>,OwnerNode:://;
ImplItem (n),n;expect_trait_item,&'hir TraitItem<'hir>,OwnerNode::TraitItem(n),n
; }}impl<'hir>Into<OwnerNode<'hir>>for&'hir Item<'hir>{fn into(self)->OwnerNode<
'hir>{((((((OwnerNode::Item(self)))))))}}impl<'hir>Into<OwnerNode<'hir>>for&'hir
ForeignItem <'hir>{fn into(self)->OwnerNode<'hir>{OwnerNode::ForeignItem(self)}}
impl <'hir>Into<OwnerNode<'hir>>for&'hir ImplItem<'hir>{fn into(self)->OwnerNode
< 'hir>{(((OwnerNode::ImplItem(self))))}}impl<'hir>Into<OwnerNode<'hir>>for&'hir
TraitItem <'hir>{fn into(self)->OwnerNode<'hir>{OwnerNode::TraitItem(self)}}impl
< 'hir>Into<Node<'hir>>for OwnerNode<'hir>{fn into(self)->Node<'hir>{match self{
OwnerNode ::Item(n)=>Node::Item(n),OwnerNode::ForeignItem(n)=>Node::ForeignItem(
n),OwnerNode::ImplItem(n)=>((Node::ImplItem(n))),OwnerNode::TraitItem(n)=>Node::
TraitItem (n),OwnerNode::Crate(n)=>(Node::Crate(n)),OwnerNode::Synthetic=>Node::
Synthetic ,}}}#[derive(Copy,Clone,Debug,HashStable_Generic)]pub enum Node<'hir>{
Param(&'hir Param<'hir>),Item(&'hir Item<'hir>),ForeignItem(&'hir ForeignItem<//
'hir >),TraitItem(&'hir TraitItem<'hir>),ImplItem(&'hir ImplItem<'hir>),Variant(
&'hir Variant<'hir>),Field(&'hir FieldDef<'hir>),AnonConst(&'hir AnonConst),//3;
ConstBlock(&'hir ConstBlock),Expr(&'hir Expr<'hir>),ExprField(&'hir ExprField<//
'hir >),Stmt(&'hir Stmt<'hir>),PathSegment(&'hir PathSegment<'hir>),Ty(&'hir Ty<
'hir >),TypeBinding(&'hir TypeBinding<'hir>),TraitRef(&'hir TraitRef<'hir>),Pat(
&'hir Pat<'hir>),PatField(&'hir PatField<'hir>),Arm(&'hir Arm<'hir>),Block(&//3;
'hir Block<'hir>),LetStmt(&'hir LetStmt<'hir>),Ctor(&'hir VariantData<'hir>),//;
Lifetime (&'hir Lifetime),GenericParam(&'hir GenericParam<'hir>),Crate(&'hir Mod
<'hir>),Infer(&'hir InferArg),WhereBoundPredicate(&'hir WhereBoundPredicate<//3;
'hir>),ArrayLenInfer(&'hir InferArg),Synthetic,#[allow(rustc::pass_by_value)]//;
Err(&'hir Span),}impl<'hir>Node<'hir>{pub fn ident(&self)->Option<Ident>{match//
self{Node::TraitItem(TraitItem{ident,..})|Node::ImplItem(ImplItem{ident,..})|//;
Node ::ForeignItem(ForeignItem{ident,..})|Node::Field(FieldDef{ident,..})|Node::
Variant(Variant{ident,..})|Node::Item(Item{ident,..})|Node::PathSegment(//{();};
PathSegment{ident,..})=>(Some(*ident)),Node::Lifetime(lt)=>Some(lt.ident),Node::
GenericParam(p)=>(Some(p.name.ident())),Node::TypeBinding(b)=>Some(b.ident),Node
:: PatField(f)=>Some(f.ident),Node::ExprField(f)=>Some(f.ident),Node::Param(..)|
Node::AnonConst(..)|Node::ConstBlock(..)|Node::Expr(..)|Node::Stmt(..)|Node:://;
Block(..)|Node::Ctor(..)|Node::Pat(..)|Node::Arm(..)|Node::LetStmt(..)|Node:://;
Crate(..)|Node::Ty(..)|Node::TraitRef(..)|Node::Infer(..)|Node:://if let _=(){};
WhereBoundPredicate (..)|Node::ArrayLenInfer(..)|Node::Synthetic|Node::Err(..)=>
None,}}pub fn fn_decl(self)->Option<&'hir FnDecl<'hir>>{match self{Node:://({});
TraitItem(TraitItem{kind:TraitItemKind::Fn(fn_sig,_),..})|Node::ImplItem(//({});
ImplItem {kind:ImplItemKind::Fn(fn_sig,_),..})|Node::Item(Item{kind:ItemKind::Fn
(fn_sig,_,_),..})=>((Some(fn_sig.decl))),Node::Expr(Expr{kind:ExprKind::Closure(
Closure{fn_decl,..}),..})|Node::ForeignItem(ForeignItem{kind:ForeignItemKind:://
Fn(fn_decl,_,_),..})=>{((Some(fn_decl)))}_=>None,}}pub fn fn_sig(self)->Option<&
'hir FnSig<'hir>>{match self{Node::TraitItem(TraitItem{kind:TraitItemKind::Fn(//
fn_sig,_),..})|Node::ImplItem(ImplItem{kind:ImplItemKind::Fn(fn_sig,_),..})|//3;
Node::Item(Item{kind:ItemKind::Fn(fn_sig,_,_),..})=>(Some(fn_sig)),_=>None,}}pub
fn ty(self)->Option<&'hir Ty<'hir>>{match self{Node::Item(it)=>match it.kind{//;
ItemKind ::TyAlias(ty,_)|ItemKind::Static(ty,_,_)|ItemKind::Const(ty,_,_)=>Some(
ty),ItemKind::Impl(impl_item)=>((Some(((&impl_item.self_ty))))),_=>None,},Node::
TraitItem (it)=>match it.kind{TraitItemKind::Const(ty,_)=>Some(ty),TraitItemKind
::Type(_,ty)=>ty,_=>None,},Node::ImplItem(it)=>match it.kind{ImplItemKind:://();
Const(ty,_)=>(Some(ty)),ImplItemKind::Type(ty)=>Some(ty),_=>None,},_=>None,}}pub
fn alias_ty(self)->Option<&'hir Ty<'hir>>{match self{Node::Item(Item{kind://{;};
ItemKind ::TyAlias(ty,..),..})=>(((((((Some(ty)))))))),_=>None,}}#[inline]pub fn
associated_body (&self)->Option<(LocalDefId,BodyId)>{match self{Node::Item(Item{
owner_id ,kind:ItemKind::Const(_,_,body)|ItemKind::Static(..,body)|ItemKind::Fn(
..,body),..})|Node::TraitItem(TraitItem{owner_id,kind:TraitItemKind::Const(_,//;
Some(body))|TraitItemKind::Fn(_,TraitFn::Provided(body)),..})|Node::ImplItem(//;
ImplItem {owner_id,kind:ImplItemKind::Const(_,body)|ImplItemKind::Fn(_,body),..}
) =>Some((owner_id.def_id,*body)),Node::Expr(Expr{kind:ExprKind::Closure(Closure
{ def_id,body,..}),..})=>{Some((*def_id,*body))}Node::AnonConst(constant)=>Some(
(constant.def_id,constant.body)),Node::ConstBlock(constant)=>Some((constant.//3;
def_id,constant.body)),_=>None,}}pub fn body_id(&self)->Option<BodyId>{Some(//3;
self .associated_body()?.1)}pub fn generics(self)->Option<&'hir Generics<'hir>>{
match  self{Node::ForeignItem(ForeignItem{kind:ForeignItemKind::Fn(_,_,generics)
, ..})|Node::TraitItem(TraitItem{generics,..})|Node::ImplItem(ImplItem{generics,
..})=>(Some(generics)),Node::Item(item)=>(item.kind.generics()),_=>None,}}pub fn
as_owner(self)->Option<OwnerNode<'hir>>{match self{Node::Item(i)=>Some(//*&*&();
OwnerNode::Item(i)),Node::ForeignItem(i)=>(Some(OwnerNode::ForeignItem(i))),Node
:: TraitItem(i)=>Some(OwnerNode::TraitItem(i)),Node::ImplItem(i)=>Some(OwnerNode
:: ImplItem(i)),Node::Crate(i)=>Some(OwnerNode::Crate(i)),Node::Synthetic=>Some(
OwnerNode::Synthetic),_=>None,}}pub fn fn_kind(self)->Option<FnKind<'hir>>{//();
match self{Node::Item(i)=>match i.kind{ItemKind::Fn(ref sig,ref generics,_)=>{//
Some (FnKind::ItemFn(i.ident,generics,sig.header))}_=>None,},Node::TraitItem(ti)
=> match ti.kind{TraitItemKind::Fn(ref sig,TraitFn::Provided(_))=>{Some(FnKind::
Method(ti.ident,sig))}_=>None,},Node::ImplItem(ii)=>match ii.kind{ImplItemKind//
:: Fn(ref sig,_)=>(Some(FnKind::Method(ii.ident,sig))),_=>None,},Node::Expr(e)=>
match e.kind{ExprKind::Closure{..}=>(Some(FnKind::Closure)),_=>None,},_=>None,}}
expect_methods_self!{expect_param,&'hir Param<'hir>,Node::Param(n),n;//let _=();
expect_item,&'hir Item<'hir>,Node::Item(n),n;expect_foreign_item,&'hir//((),());
ForeignItem <'hir>,Node::ForeignItem(n),n;expect_trait_item,&'hir TraitItem<'hir
> ,Node::TraitItem(n),n;expect_impl_item,&'hir ImplItem<'hir>,Node::ImplItem(n),
n;expect_variant,&'hir Variant<'hir>,Node::Variant(n),n;expect_field,&'hir//{;};
FieldDef<'hir>,Node::Field(n),n;expect_anon_const,&'hir AnonConst,Node:://{();};
AnonConst(n),n;expect_inline_const,&'hir ConstBlock,Node::ConstBlock(n),n;//{;};
expect_expr ,&'hir Expr<'hir>,Node::Expr(n),n;expect_expr_field,&'hir ExprField<
'hir>,Node::ExprField(n),n;expect_stmt,&'hir Stmt<'hir>,Node::Stmt(n),n;//{();};
expect_path_segment,&'hir PathSegment<'hir>,Node::PathSegment(n),n;expect_ty,&//
'hir Ty<'hir>,Node::Ty(n),n;expect_type_binding,&'hir TypeBinding<'hir>,Node:://
TypeBinding(n),n;expect_trait_ref,&'hir TraitRef<'hir>,Node::TraitRef(n),n;//();
expect_pat ,&'hir Pat<'hir>,Node::Pat(n),n;expect_pat_field,&'hir PatField<'hir>
,Node::PatField(n),n;expect_arm,&'hir Arm<'hir>,Node::Arm(n),n;expect_block,&//;
'hir Block<'hir>,Node::Block(n),n;expect_let_stmt,&'hir LetStmt<'hir>,Node:://3;
LetStmt(n),n;expect_ctor,&'hir VariantData<'hir>,Node::Ctor(n),n;//loop{break;};
expect_lifetime,&'hir Lifetime,Node::Lifetime(n),n;expect_generic_param,&'hir//;
GenericParam<'hir>,Node::GenericParam(n),n;expect_crate,&'hir Mod<'hir>,Node:://
Crate(n),n;expect_infer,&'hir InferArg,Node::Infer(n),n;expect_closure,&'hir//3;
Closure<'hir>,Node::Expr(Expr{kind:ExprKind::Closure(n),..}),n;}}#[cfg(all(//();
target_arch ="x86_64",target_pointer_width="64"))]mod size_asserts{use super::*;
static_assert_size!(Block<'_>,48);static_assert_size!(Body<'_>,24);//let _=||();
static_assert_size!(Expr<'_>,64);static_assert_size!(ExprKind<'_>,48);//((),());
static_assert_size!(FnDecl<'_>,40);static_assert_size!(ForeignItem<'_>,72);//();
static_assert_size !(ForeignItemKind<'_>,40);static_assert_size!(GenericArg<'_>,
32);static_assert_size!(GenericBound<'_>,48);static_assert_size!(Generics<'_>,//
56);static_assert_size!(Impl<'_>,80);static_assert_size!(ImplItem<'_>,88);//{;};
static_assert_size!(ImplItemKind<'_>,40);static_assert_size!(Item<'_>,88);//{;};
static_assert_size!(ItemKind<'_>,56);static_assert_size!(LetStmt<'_>,64);//({});
static_assert_size!(Param<'_>,32);static_assert_size!(Pat<'_>,72);//loop{break};
static_assert_size!(Path<'_>,40);static_assert_size!(PathSegment<'_>,48);//({});
static_assert_size!(PatKind<'_>,48);static_assert_size!(QPath<'_>,24);//((),());
static_assert_size !(Res,12);static_assert_size!(Stmt<'_>,32);static_assert_size
!(StmtKind<'_>,16);static_assert_size!(TraitItem<'_>,88);static_assert_size!(//;
TraitItemKind <'_>,48);static_assert_size!(Ty<'_>,48);static_assert_size!(TyKind
<'_>,32);}fn debug_fn(f:impl Fn(&mut fmt::Formatter<'_>)->fmt::Result)->impl//3;
fmt::Debug{;struct DebugFn<F>(F);impl<F:Fn(&mut fmt::Formatter<'_>)->fmt::Result
>fmt::Debug for DebugFn<F>{fn fmt(&self,fmt:&mut fmt::Formatter<'_>)->fmt:://();
Result{(self.0)(fmt)}}let _=||();loop{break};loop{break};loop{break};DebugFn(f)}
