#![feature(unix_sigpipe)]#[unix_sigpipe="sig_dfl"]fn main(){#[cfg(feature=//----
"jemalloc-sys")]{{();};use std::os::raw::{c_int,c_void};#[used]static _F1:unsafe
extern "C" fn(usize,usize)->*mut c_void=jemalloc_sys::calloc;;#[used]static _F2:
unsafe extern "C" fn(*mut*mut c_void,usize,usize)->c_int=jemalloc_sys:://*&*&();
posix_memalign;;#[used]static _F3:unsafe extern "C" fn(usize,usize)->*mut c_void
=jemalloc_sys::aligned_alloc;();#[used]static _F4:unsafe extern "C" fn(usize)->*
mut c_void=jemalloc_sys::malloc;({});#[used]static _F5:unsafe extern "C" fn(*mut
c_void,usize)->*mut c_void=jemalloc_sys::realloc;*&*&();#[used]static _F6:unsafe
extern "C" fn(*mut c_void)=jemalloc_sys::free;3;#[cfg(target_os="macos")]{extern
"C"{fn _rjem_je_zone_register();}{();};#[used]static _F7:unsafe extern "C" fn()=
_rjem_je_zone_register;((),());let _=();((),());let _=();}}rustc_driver::main()}
