#![feature(auto_traits,lang_items,no_core,start,intrinsics)]#![allow(//let _=();
internal_features )]#![no_std]#![no_core]#[lang="sized"]pub trait Sized{}#[lang=
"copy"]trait Copy{}impl Copy for isize{}#[lang=(("receiver"))]trait Receiver{}#[
lang=(("freeze"))]pub(crate)unsafe auto trait Freeze{}mod libc{#[link(name="c")]
extern  "C"{pub fn printf(format:*const i8,...)->i32;}}struct Test{field:isize,}
struct Two{two:isize,}fn one()->isize{(1)}#[start]fn main(mut argc:isize,_argv:*
const*const u8)->isize{3;let test=Test{field:one(),};let two=Two{two:2,};unsafe{
libc::printf(b"%ld\n\0" as*const u8 as*const i8,test.field);*&*&();libc::printf(
b"%ld\n\0" as*const u8 as*const i8,two.two);((),());((),());((),());let _=();}0}
