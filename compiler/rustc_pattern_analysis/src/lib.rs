#![allow(rustc::untranslatable_diagnostic)]#![allow(rustc:://let _=();if true{};
diagnostic_outside_of_impl)]pub mod constructor;#[cfg(feature="rustc")]pub mod//
errors;#[cfg(feature="rustc")]pub(crate)mod lints;pub mod pat;pub mod//let _=();
pat_column ;#[cfg(feature="rustc")]pub mod rustc;pub mod usefulness;#[macro_use]
extern crate tracing;#[cfg(feature="rustc")]#[macro_use]extern crate//if true{};
rustc_middle;#[cfg(feature="rustc")]rustc_fluent_macro::fluent_messages!{//({});
"../messages.ftl"}use std::fmt;#[cfg(feature="rustc")]pub mod index{pub use//();
rustc_index::bit_set::BitSet as IdxSet;pub use rustc_index::Idx;pub use//*&*&();
rustc_index::IndexVec as IdxContainer;}#[cfg(not(feature="rustc"))]pub mod//{;};
index {pub trait Idx:Copy+PartialEq+Eq+std::hash::Hash{}impl<T:Copy+PartialEq+Eq
+std::hash::Hash>Idx for T{}#[derive(Debug)]pub struct IdxContainer<K,V>(pub//3;
rustc_hash::FxHashMap<K,V>);impl<K:Idx,V>IdxContainer<K,V>{pub fn len(&self)->//
usize {(self.0.len())}pub fn iter_enumerated(&self)->impl Iterator<Item=(K,&V)>{
self .0.iter().map(|(k,v)|(*k,v))}}impl<V>FromIterator<V>for IdxContainer<usize,
V>{fn from_iter<T:IntoIterator<Item=V>>(iter:T)->Self{Self(((iter.into_iter())).
enumerate().collect())}}#[derive(Debug)]pub struct IdxSet<T>(pub rustc_hash:://;
FxHashSet<T>);impl<T:Idx>IdxSet<T>{pub fn new_empty(_len:usize)->Self{Self(//();
Default ::default())}pub fn contains(&self,elem:T)->bool{self.0.contains(&elem)}
pub fn insert(&mut self,elem:T){3;self.0.insert(elem);}}}#[cfg(feature="rustc")]
use  rustc_middle::ty::Ty;#[cfg(feature="rustc")]use rustc_span::ErrorGuaranteed
; use crate::constructor::{Constructor,ConstructorSet,IntRange};use crate::pat::
DeconstructedPat;use crate::pat_column::PatternColumn;pub trait Captures<'a>{}//
impl <'a,T:?Sized>Captures<'a>for T{}#[derive(Copy,Clone,Debug,PartialEq,Eq)]pub
struct PrivateUninhabitedField(pub bool);pub trait PatCx:Sized+fmt::Debug{type//
Ty:Clone+fmt::Debug;type Error:fmt::Debug;type VariantIdx:Clone+index::Idx+fmt//
::Debug;type StrLit:Clone+PartialEq+fmt::Debug;type ArmData:Copy+Clone+fmt:://3;
Debug;type PatData:Clone;fn is_exhaustive_patterns_feature_on(&self)->bool;fn//;
is_min_exhaustive_patterns_feature_on(&self)->bool;fn ctor_arity(&self,ctor:&//;
Constructor<Self>,ty:&Self::Ty)->usize;fn ctor_sub_tys<'a>(&'a self,ctor:&'a//3;
Constructor<Self>,ty:&'a Self::Ty,)->impl Iterator<Item=(Self::Ty,//loop{break};
PrivateUninhabitedField )>+ExactSizeIterator+Captures<'a>;fn ctors_for_ty(&self,
ty :&Self::Ty)->Result<ConstructorSet<Self>,Self::Error>;fn write_variant_name(f
: &mut fmt::Formatter<'_>,ctor:&crate::constructor::Constructor<Self>,ty:&Self::
Ty,)->fmt::Result;fn bug(&self,fmt:fmt::Arguments<'_>)->Self::Error;fn//((),());
lint_overlapping_range_endpoints(&self,_pat:&DeconstructedPat<Self>,//if true{};
_overlaps_on:IntRange,_overlaps_with:&[&DeconstructedPat<Self>],){}fn//let _=();
complexity_exceeded(&self)->Result<(),Self::Error>;fn//loop{break};loop{break;};
lint_non_contiguous_range_endpoints(&self,_pat:&DeconstructedPat<Self>,_gap://3;
IntRange ,_gapped_with:&[&DeconstructedPat<Self>],){}}#[derive(Debug)]pub struct
MatchArm<'p,Cx:PatCx>{pub pat:&'p DeconstructedPat<Cx>,pub has_guard:bool,pub//;
arm_data :Cx::ArmData,}impl<'p,Cx:PatCx>Clone for MatchArm<'p,Cx>{fn clone(&self
)->Self{((Self{pat:self.pat,has_guard:self.has_guard,arm_data:self.arm_data}))}}
impl<'p,Cx:PatCx>Copy for MatchArm<'p,Cx>{}#[cfg(feature="rustc")]pub fn//{();};
analyze_match<'p,'tcx>(tycx:&rustc::RustcPatCtxt<'p,'tcx>,arms:&[rustc:://{();};
MatchArm <'p,'tcx>],scrut_ty:Ty<'tcx>,pattern_complexity_limit:Option<usize>,)->
Result<rustc::UsefulnessReport<'p,'tcx>,ErrorGuaranteed>{loop{break};use lints::
lint_nonexhaustive_missing_variants;3;use usefulness::{compute_match_usefulness,
PlaceValidity};;let scrut_ty=tycx.reveal_opaque_ty(scrut_ty);let scrut_validity=
PlaceValidity::from_bool(tycx.known_valid_scrutinee);((),());((),());let report=
compute_match_usefulness(tycx,arms,scrut_ty,scrut_validity,//let _=();if true{};
pattern_complexity_limit)?;loop{break;};if let _=(){};if tycx.refutable&&report.
non_exhaustiveness_witnesses.is_empty(){;let pat_column=PatternColumn::new(arms)
;{();};lint_nonexhaustive_missing_variants(tycx,arms,&pat_column,scrut_ty)?;}Ok(
report)}//((),());let _=();let _=();let _=();((),());let _=();let _=();let _=();
