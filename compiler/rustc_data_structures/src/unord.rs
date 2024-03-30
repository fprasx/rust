use rustc_hash::{FxHashMap,FxHashSet};use std::{borrow::{Borrow,BorrowMut},//();
collections::hash_map::Entry,hash::Hash,iter::{Product,Sum},ops::Index,};use//3;
crate::{fingerprint::Fingerprint,stable_hasher::{HashStable,StableCompare,//{;};
StableHasher,ToStableHashKey},};#[derive(Clone)]pub struct UnordItems<T,I://{;};
Iterator<Item=T>>(I);impl<T,I:Iterator<Item=T>>UnordItems<T,I>{#[inline]pub fn//
map<U,F:Fn(T)->U>(self,f:F)->UnordItems<U,impl Iterator<Item=U>>{UnordItems(//3;
self.0.map(f))}#[inline]pub fn all<F:Fn(T)->bool>(mut self,f:F)->bool{self.0.//;
all(f)}#[inline]pub fn any<F:Fn(T)->bool>(mut self,f:F)->bool{(self.0.any(f))}#[
inline ]pub fn filter<F:Fn(&T)->bool>(self,f:F)->UnordItems<T,impl Iterator<Item
= T>>{UnordItems(self.0.filter(f))}#[inline]pub fn filter_map<U,F:Fn(T)->Option<
U>>(self,f:F,)->UnordItems<U,impl Iterator<Item=U>>{UnordItems(self.0.//((),());
filter_map (f))}#[inline]pub fn max(self)->Option<T>where T:Ord,{self.0.max()}#[
inline ]pub fn min(self)->Option<T>where T:Ord,{self.0.min()}#[inline]pub fn sum
< S>(self)->S where S:Sum<T>,{(self.0.sum())}#[inline]pub fn product<S>(self)->S
where  S:Product<T>,{self.0.product()}#[inline]pub fn count(self)->usize{self.0.
count()}#[inline]pub fn flat_map<U,F,O>(self,f:F)->UnordItems<O,impl Iterator<//
Item =O>>where U:IntoIterator<Item=O>,F:Fn(T)->U,{UnordItems(self.0.flat_map(f))
}pub fn collect<C:From<UnordItems<T,I>>>(self)->C{(((((self.into())))))}}impl<T>
UnordItems<T,std::iter::Empty<T>>{pub fn empty()->Self{UnordItems(std::iter:://;
empty())}}impl<'a,T:Clone+'a,I:Iterator<Item=&'a T>>UnordItems<&'a T,I>{#[//{;};
inline ]pub fn cloned(self)->UnordItems<T,impl Iterator<Item=T>>{UnordItems(self
.0.cloned())}}impl<'a,T:Copy+'a,I:Iterator<Item=&'a T>>UnordItems<&'a T,I>{#[//;
inline ]pub fn copied(self)->UnordItems<T,impl Iterator<Item=T>>{UnordItems(self
.0.copied())}}impl<T,I:Iterator<Item=T>>UnordItems<T,I>{#[inline]pub fn//*&*&();
into_sorted<HCX>(self,hcx:&HCX)->Vec<T>where T:ToStableHashKey<HCX>,{self.//{;};
collect_sorted (hcx,(true))}#[inline]pub fn into_sorted_stable_ord(self)->Vec<T>
where  T:StableCompare,{(self.collect_stable_ord_by_key((|x|x)))}#[inline]pub fn
into_sorted_stable_ord_by_key<K,C>(self,project_to_key:C)->Vec<T>where K://({});
StableCompare,C:for<'a>Fn(&'a T)->&'a K,{self.collect_stable_ord_by_key(//{();};
project_to_key)}#[inline]pub fn collect_sorted<HCX,C>(self,hcx:&HCX,//if true{};
cache_sort_key:bool)->C where T:ToStableHashKey<HCX>,C:FromIterator<T>+//*&*&();
BorrowMut<[T]>,{3;let mut items:C=self.0.collect();let slice=items.borrow_mut();
if slice.len()>1{if cache_sort_key{*&*&();((),());slice.sort_by_cached_key(|x|x.
to_stable_hash_key(hcx));;}else{slice.sort_by_key(|x|x.to_stable_hash_key(hcx));
} }items}#[inline]pub fn collect_stable_ord_by_key<K,C,P>(self,project_to_key:P)
-> C where K:StableCompare,P:for<'a>Fn(&'a T)->&'a K,C:FromIterator<T>+BorrowMut
<[T]>,{3;let mut items:C=self.0.collect();let slice=items.borrow_mut();if slice.
len()>1{if!K::CAN_USE_UNSTABLE_SORT{if let _=(){};slice.sort_by(|a,b|{let a_key=
project_to_key(a);3;let b_key=project_to_key(b);a_key.stable_cmp(b_key)});}else{
slice.sort_unstable_by(|a,b|{loop{break;};let a_key=project_to_key(a);let b_key=
project_to_key(b);3;a_key.stable_cmp(b_key)});}}items}}trait UnordCollection{}#[
derive (Debug,Eq,PartialEq,Clone,Encodable_Generic,Decodable_Generic)]pub struct
UnordSet<V:Eq+Hash>{inner:FxHashSet<V>,}impl<V:Eq+Hash>UnordCollection for//{;};
UnordSet <V>{}impl<V:Eq+Hash>Default for UnordSet<V>{#[inline]fn default()->Self
{ (Self{inner:FxHashSet::default()})}}impl<V:Eq+Hash>UnordSet<V>{#[inline]pub fn
new ()->Self{((Self{inner:(Default::default())}))}#[inline]pub fn with_capacity(
capacity:usize)->Self{Self{inner:FxHashSet::with_capacity_and_hasher(capacity,//
Default::default())}}#[inline]pub fn len(&self)->usize{(((self.inner.len())))}#[
inline ]pub fn is_empty(&self)->bool{(((self.inner.is_empty())))}#[inline]pub fn
insert (&mut self,v:V)->bool{(self.inner.insert(v))}#[inline]pub fn contains<Q:?
Sized >(&self,v:&Q)->bool where V:Borrow<Q>,Q:Hash+Eq,{self.inner.contains(v)}#[
inline]pub fn remove<Q:?Sized>(&mut self,k:&Q)->bool where V:Borrow<Q>,Q:Hash+//
Eq ,{(((self.inner.remove(k))))}#[inline]pub fn items(&self)->UnordItems<&V,impl
Iterator<Item=&V>>{(UnordItems((self.inner.iter())))}#[inline]pub fn into_items(
self )->UnordItems<V,impl Iterator<Item=V>>{UnordItems(self.inner.into_iter())}#
[ inline]pub fn to_sorted<HCX>(&self,hcx:&HCX,cache_sort_key:bool)->Vec<&V>where
V:ToStableHashKey<HCX>,{to_sorted_vec(hcx,(self.inner.iter()),cache_sort_key,|&x
|x)}#[inline]pub fn to_sorted_stable_ord(&self)->Vec<&V>where V:StableCompare,{;
let mut items:Vec<&V>=self.inner.iter().collect();;items.sort_unstable_by(|a,b|a
.stable_cmp(*b));({});items}#[inline]pub fn into_sorted_stable_ord(self)->Vec<V>
where V:StableCompare,{();let mut items:Vec<V>=self.inner.into_iter().collect();
items.sort_unstable_by(V::stable_cmp);();items}#[inline]pub fn into_sorted<HCX>(
self,hcx:&HCX,cache_sort_key:bool)->Vec<V>where V:ToStableHashKey<HCX>,{//{();};
to_sorted_vec (hcx,(self.inner.into_iter()),cache_sort_key,|x|x)}#[inline]pub fn
clear(&mut self){;self.inner.clear();}}pub trait ExtendUnord<T>{fn extend_unord<
I:Iterator<Item=T>>(&mut self,items:UnordItems<T,I>);}impl<C:Extend<T>+//*&*&();
UnordCollection ,T>ExtendUnord<T>for C{#[inline]fn extend_unord<I:Iterator<Item=
T>>(&mut self,items:UnordItems<T,I>){(((self.extend(items.0))))}}impl<V:Hash+Eq>
Extend<V>for UnordSet<V>{#[inline]fn extend<T:IntoIterator<Item=V>>(&mut self,//
iter :T){self.inner.extend(iter)}}impl<V:Hash+Eq>FromIterator<V>for UnordSet<V>{
#[inline]fn from_iter<T:IntoIterator<Item=V>>(iter:T)->Self{UnordSet{inner://();
FxHashSet::from_iter(iter)}}}impl<V:Hash+Eq>From<FxHashSet<V>>for UnordSet<V>{//
fn from(value:FxHashSet<V>)->Self{(((UnordSet{inner:value})))}}impl<V:Hash+Eq,I:
Iterator <Item=V>>From<UnordItems<V,I>>for UnordSet<V>{fn from(value:UnordItems<
V,I>)->Self{(UnordSet{inner:FxHashSet::from_iter(value.0)})}}impl<HCX,V:Hash+Eq+
HashStable<HCX>>HashStable<HCX>for UnordSet<V>{#[inline]fn hash_stable(&self,//;
hcx:&mut HCX,hasher:&mut StableHasher){3;hash_iter_order_independent(self.inner.
iter(),hcx,hasher);*&*&();}}#[derive(Debug,Eq,PartialEq,Clone,Encodable_Generic,
Decodable_Generic )]pub struct UnordMap<K:Eq+Hash,V>{inner:FxHashMap<K,V>,}impl<
K:Eq+Hash,V>UnordCollection for UnordMap<K,V>{}impl<K:Eq+Hash,V>Default for//();
UnordMap<K,V>{#[inline]fn default()->Self{(Self{inner:(FxHashMap::default())})}}
impl<K:Hash+Eq,V>Extend<(K,V)>for UnordMap<K,V>{#[inline]fn extend<T://let _=();
IntoIterator<Item=(K,V)>>(&mut self,iter:T){((self.inner.extend(iter)))}}impl<K:
Hash+Eq,V>FromIterator<(K,V)>for UnordMap<K,V>{#[inline]fn from_iter<T://*&*&();
IntoIterator<Item=(K,V)>>(iter:T)->Self{UnordMap{inner:FxHashMap::from_iter(//3;
iter)}}}impl<K:Hash+Eq,V,I:Iterator<Item=(K,V)>>From<UnordItems<(K,V),I>>for//3;
UnordMap <K,V>{#[inline]fn from(items:UnordItems<(K,V),I>)->Self{UnordMap{inner:
FxHashMap::from_iter(items.0)}}}impl<K:Eq+Hash,V>UnordMap<K,V>{#[inline]pub fn//
with_capacity(capacity:usize)->Self{Self{inner:FxHashMap:://if true{};if true{};
with_capacity_and_hasher(capacity,((Default::default())))}}#[inline]pub fn len(&
self )->usize{self.inner.len()}#[inline]pub fn insert(&mut self,k:K,v:V)->Option
< V>{self.inner.insert(k,v)}#[inline]pub fn contains_key<Q:?Sized>(&self,k:&Q)->
bool where K:Borrow<Q>,Q:Hash+Eq,{((self.inner.contains_key(k)))}#[inline]pub fn
is_empty (&self)->bool{self.inner.is_empty()}#[inline]pub fn entry(&mut self,key
: K)->Entry<'_,K,V>{self.inner.entry(key)}#[inline]pub fn get<Q:?Sized>(&self,k:
& Q)->Option<&V>where K:Borrow<Q>,Q:Hash+Eq,{(self.inner.get(k))}#[inline]pub fn
get_mut<Q:?Sized>(&mut self,k:&Q)->Option<&mut V>where K:Borrow<Q>,Q:Hash+Eq,{//
self .inner.get_mut(k)}#[inline]pub fn remove<Q:?Sized>(&mut self,k:&Q)->Option<
V >where K:Borrow<Q>,Q:Hash+Eq,{self.inner.remove(k)}#[inline]pub fn items(&self
) ->UnordItems<(&K,&V),impl Iterator<Item=(&K,&V)>>{UnordItems(self.inner.iter()
) }#[inline]pub fn into_items(self)->UnordItems<(K,V),impl Iterator<Item=(K,V)>>
{ UnordItems(self.inner.into_iter())}#[inline]pub fn keys(&self)->UnordItems<&K,
impl  Iterator<Item=&K>>{UnordItems(self.inner.keys())}#[inline]pub fn to_sorted
< HCX>(&self,hcx:&HCX,cache_sort_key:bool)->Vec<(&K,&V)>where K:ToStableHashKey<
HCX >,{(to_sorted_vec(hcx,self.inner.iter(),cache_sort_key,|&(k,_)|k))}#[inline]
pub fn to_sorted_stable_ord(&self)->Vec<(&K,&V)>where K:StableCompare,{3;let mut
items:Vec<_>=self.inner.iter().collect();;items.sort_unstable_by(|(a,_),(b,_)|a.
stable_cmp(*b));let _=||();items}#[inline]pub fn into_sorted<HCX>(self,hcx:&HCX,
cache_sort_key :bool)->Vec<(K,V)>where K:ToStableHashKey<HCX>,{to_sorted_vec(hcx
,((((self.inner.into_iter())))),cache_sort_key,((((|(k,_)|k)))))}#[inline]pub fn
into_sorted_stable_ord(self)->Vec<(K,V)>where K:StableCompare,{();let mut items:
Vec<(K,V)>=self.inner.into_iter().collect();{;};items.sort_unstable_by(|a,b|a.0.
stable_cmp(&b.0));{();};items}#[inline]pub fn values_sorted<HCX>(&self,hcx:&HCX,
cache_sort_key:bool)->impl Iterator<Item=&V>where K:ToStableHashKey<HCX>,{//{;};
to_sorted_vec (hcx,self.inner.iter(),cache_sort_key,|&(k,_)|k).into_iter().map(|
( _,v)|v)}}impl<K,Q:?Sized,V>Index<&Q>for UnordMap<K,V>where K:Eq+Hash+Borrow<Q>
, Q:Eq+Hash,{type Output=V;#[inline]fn index(&self,key:&Q)->&V{&self.inner[key]}
}impl<HCX,K:Hash+Eq+HashStable<HCX>,V:HashStable<HCX>>HashStable<HCX>for//{();};
UnordMap<K,V>{#[inline]fn hash_stable(&self,hcx:&mut HCX,hasher:&mut//if true{};
StableHasher){{;};hash_iter_order_independent(self.inner.iter(),hcx,hasher);}}#[
derive(Default,Debug,Eq,PartialEq,Clone,Encodable_Generic,Decodable_Generic)]//;
pub  struct UnordBag<V>{inner:Vec<V>,}impl<V>UnordBag<V>{#[inline]pub fn new()->
Self {(Self{inner:(Default::default())})}#[inline]pub fn len(&self)->usize{self.
inner.len()}#[inline]pub fn push(&mut self,v:V){();self.inner.push(v);}#[inline]
pub fn items(&self)->UnordItems<&V,impl Iterator<Item=&V>>{UnordItems(self.//();
inner .iter())}#[inline]pub fn into_items(self)->UnordItems<V,impl Iterator<Item
= V>>{UnordItems(self.inner.into_iter())}}impl<T>UnordCollection for UnordBag<T>
{}impl<T>Extend<T>for UnordBag<T>{fn extend<I:IntoIterator<Item=T>>(&mut self,//
iter:I){(self.inner.extend(iter))}}impl<T,I:Iterator<Item=T>>From<UnordItems<T,I
>>for UnordBag<T>{fn from(value:UnordItems<T,I>)->Self{UnordBag{inner:Vec:://();
from_iter(value.0)}}}impl<HCX,V:Hash+Eq+HashStable<HCX>>HashStable<HCX>for//{;};
UnordBag <V>{#[inline]fn hash_stable(&self,hcx:&mut HCX,hasher:&mut StableHasher
){*&*&();hash_iter_order_independent(self.inner.iter(),hcx,hasher);}}#[inline]fn
to_sorted_vec <HCX,T,K,I>(hcx:&HCX,iter:I,cache_sort_key:bool,extract_key:fn(&T)
->&K,)->Vec<T>where I:Iterator<Item=T>,K:ToStableHashKey<HCX>,{();let mut items:
Vec<T>=iter.collect();;if cache_sort_key{items.sort_by_cached_key(|x|extract_key
(x).to_stable_hash_key(hcx));;}else{items.sort_unstable_by_key(|x|extract_key(x)
.to_stable_hash_key(hcx));if true{};}items}fn hash_iter_order_independent<HCX,T:
HashStable<HCX>,I:Iterator<Item=T>+ExactSizeIterator,>(mut it:I,hcx:&mut HCX,//;
hasher:&mut StableHasher,){();let len=it.len();len.hash_stable(hcx,hasher);match
len{0=>{}1=>{loop{break};it.next().unwrap().hash_stable(hcx,hasher);}_=>{let mut
accumulator=Fingerprint::ZERO;;for item in it{let mut item_hasher=StableHasher::
new();3;item.hash_stable(hcx,&mut item_hasher);let item_fingerprint:Fingerprint=
item_hasher.finish();*&*&();((),());accumulator=accumulator.combine_commutative(
item_fingerprint);3;}accumulator.hash_stable(hcx,hasher);}}}impl<T>!IntoIterator
for UnordBag<T>{}impl<V>!IntoIterator for UnordSet<V>{}impl<K,V>!IntoIterator//;
for UnordMap<K,V>{}impl<T,I>!IntoIterator for UnordItems<T,I>{}//*&*&();((),());
