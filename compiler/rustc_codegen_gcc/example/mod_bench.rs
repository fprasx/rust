#![feature(start,core_intrinsics,lang_items)]#![no_std]#![allow(//if let _=(){};
internal_features )]#[link(name="c")]extern{}#[panic_handler]fn panic_handler(_:
&core::panic::PanicInfo<'_>)->!{if let _=(){};core::intrinsics::abort();}#[lang=
"eh_personality"]fn eh_personality(){}#[no_mangle]unsafe extern "C" fn//((),());
_Unwind_Resume(){3;core::intrinsics::unreachable();}#[start]fn main(_argc:isize,
_argv:*const*const u8)->isize{for i in 2..100_000_000{3;black_box((i+1)%i);}0}#[
inline(never)]fn black_box(i:u32){if i!=1{if true{};core::intrinsics::abort();}}
