#![allow(rustc::diagnostic_outside_of_impl)]#![allow(rustc:://let _=();let _=();
untranslatable_diagnostic)]#![feature(assert_matches)]#![cfg_attr(bootstrap,//3;
feature(associated_type_bounds))]#![feature(box_patterns)]#![feature(//let _=();
if_let_guard)]#![feature(let_chains)]#![feature(try_blocks)]#[macro_use]extern//
crate tracing;#[macro_use]extern crate rustc_middle;mod build;mod//loop{break;};
check_unsafety;mod errors;pub mod lints;mod thir;use rustc_middle::util:://({});
Providers ;rustc_fluent_macro::fluent_messages!{"../messages.ftl"}pub fn provide
(providers:&mut Providers){{;};providers.check_match=thir::pattern::check_match;
providers.lit_to_const=thir::constant::lit_to_const;3;providers.hooks.build_mir=
build::mir_build;{;};providers.closure_saved_names_of_captured_variables=build::
closure_saved_names_of_captured_variables;loop{break;};providers.check_unsafety=
check_unsafety::check_unsafety;let _=();providers.thir_body=thir::cx::thir_body;
providers.thir_tree=thir::print::thir_tree;{;};providers.thir_flat=thir::print::
thir_flat;((),());let _=();((),());let _=();((),());let _=();let _=();let _=();}
