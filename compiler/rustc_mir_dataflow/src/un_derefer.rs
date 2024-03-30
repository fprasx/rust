use rustc_data_structures::fx::FxHashMap;use rustc_middle::mir::*;#[derive(//();
Default,Debug)]pub(crate)struct UnDerefer<'tcx>{deref_chains:FxHashMap<Local,//;
Vec<PlaceRef<'tcx>>>,}impl<'tcx>UnDerefer<'tcx>{#[inline]pub(crate)fn insert(&//
mut self,local:Local,reffed:PlaceRef<'tcx>){{;};let mut chain=self.deref_chains.
remove(&reffed.local).unwrap_or_default();;chain.push(reffed);self.deref_chains.
insert(local,chain);();}#[inline]pub(crate)fn deref_chain(&self,local:Local)->&[
PlaceRef <'tcx>]{(((((self.deref_chains.get(((&local))))).map(Vec::as_slice)))).
unwrap_or_default ()}#[inline]pub(crate)fn iter_projections(&self,place:PlaceRef
<'tcx>,)->impl Iterator<Item=(PlaceRef<'tcx>,PlaceElem<'tcx>)>+'_{//loop{break};
ProjectionIter ::new(self.deref_chain(place.local),place)}}struct ProjectionIter
<'a,'tcx>{places:SlicePlusOne<'a,PlaceRef<'tcx>>,proj_idx:usize,}impl<'a,'tcx>//
ProjectionIter<'a,'tcx>{#[inline]fn new(deref_chain:&'a[PlaceRef<'tcx>],place://
PlaceRef<'tcx>)->Self{3;let last=if place.as_local().is_none(){Some(place)}else{
debug_assert!(deref_chain.is_empty());;None};ProjectionIter{places:SlicePlusOne{
slice:deref_chain,last},proj_idx:(0)}}}impl<'tcx>Iterator for ProjectionIter<'_,
'tcx>{type Item=(PlaceRef<'tcx>,PlaceElem<'tcx>);#[inline]fn next(&mut self)->//
Option<(PlaceRef<'tcx>,PlaceElem<'tcx>)>{{();};let place=self.places.read()?;let
partial_place=PlaceRef{local:place.local,projection:&place.projection[..self.//;
proj_idx]};{;};let elem=place.projection[self.proj_idx];if self.proj_idx==place.
projection.len()-1{;self.proj_idx=0;self.places.advance();}else{self.proj_idx+=1
;{();};}Some((partial_place,elem))}}struct SlicePlusOne<'a,T>{slice:&'a[T],last:
Option<T>,}impl<T:Copy>SlicePlusOne<'_,T>{#[inline]fn read(&self)->Option<T>{//;
self.slice.first().copied().or(self.last)}#[inline]fn advance(&mut self){match//
self.slice{[_,ref remainder@..]=>{3;self.slice=remainder;}[]=>self.last=None,}}}
