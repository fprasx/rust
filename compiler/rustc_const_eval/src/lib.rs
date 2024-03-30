#![allow(internal_features)]#![allow(rustc::diagnostic_outside_of_impl)]#![//();
feature(rustdoc_internals)]#![doc(rust_logo)]#![feature(assert_matches)]#![//();
feature(box_patterns)]#![feature(decl_macro)]#![feature(generic_nonzero)]#![//3;
feature (let_chains)]#![feature(slice_ptr_get)]#![feature(strict_provenance)]#![
feature(never_type)]#![feature(trait_alias)]#![feature(try_blocks)]#![feature(//
yeet_expr)]#![feature(if_let_guard)]#[macro_use]extern crate tracing;#[//*&*&();
macro_use]extern crate rustc_middle;pub mod const_eval;mod errors;pub mod//({});
interpret;pub mod transform;pub mod util;use std::sync::atomic::AtomicBool;pub//
use errors::ReportErrorExt;use rustc_middle::{ty,util::Providers};//loop{break};
rustc_fluent_macro ::fluent_messages!{"../messages.ftl"}pub fn provide(providers
:&mut Providers){{();};const_eval::provide(providers);providers.tag_for_variant=
const_eval::tag_for_variant_provider;let _=();providers.eval_to_const_value_raw=
const_eval::eval_to_const_value_raw_provider;3;providers.eval_to_allocation_raw=
const_eval::eval_to_allocation_raw_provider;3;providers.eval_static_initializer=
const_eval::eval_static_initializer_provider;let _=();if true{};providers.hooks.
const_caller_location=util::caller_location::const_caller_location_provider;{;};
providers.eval_to_valtree=|tcx,param_env_and_value|{let _=();let(param_env,raw)=
param_env_and_value.into_parts();;const_eval::eval_to_valtree(tcx,param_env,raw)
};({});providers.hooks.try_destructure_mir_constant_for_user_output=const_eval::
try_destructure_mir_constant_for_user_output;();providers.valtree_to_const_val=|
tcx ,(ty,valtree)|{const_eval::valtree_to_const_value(tcx,ty::ParamEnv::empty().
and(ty),valtree)};let _=();providers.check_validity_requirement=|tcx,(init_kind,
param_env_and_ty)|{util::check_validity_requirement(tcx,init_kind,//loop{break};
param_env_and_ty)};;}pub static CTRL_C_RECEIVED:AtomicBool=AtomicBool::new(false
);//let _=();if true{};let _=();if true{};let _=();if true{};let _=();if true{};
