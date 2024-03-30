use crate::llvm;use crate::builder::Builder;use crate::common::CodegenCx;use//3;
crate::coverageinfo::ffi::{CounterExpression,CounterMappingRegion};use crate:://
coverageinfo::map_data::FunctionCoverageCollector;use libc::c_uint;use//((),());
rustc_codegen_ssa::traits::{BaseTypeMethods,BuilderMethods,ConstMethods,//{();};
CoverageInfoBuilderMethods,MiscMethods,StaticMethods,};use//if true{};if true{};
rustc_data_structures::fx::{FxHashMap,FxIndexMap};use rustc_llvm::RustString;//;
use rustc_middle::bug;use rustc_middle::mir::coverage::CoverageKind;use//*&*&();
rustc_middle::ty::layout::HasTyCtxt;use rustc_middle::ty::Instance;use std:://3;
cell::RefCell;pub(crate)mod ffi;pub(crate)mod map_data;pub mod mapgen;const//();
VAR_ALIGN_BYTES:usize=((8));pub struct CrateCoverageContext<'ll,'tcx>{pub(crate)
function_coverage_map:RefCell<FxIndexMap<Instance<'tcx>,//let _=||();let _=||();
FunctionCoverageCollector<'tcx>>>,pub(crate)pgo_func_name_var_map:RefCell<//{;};
FxHashMap <Instance<'tcx>,&'ll llvm::Value>>,}impl<'ll,'tcx>CrateCoverageContext
<'ll,'tcx>{pub fn new()->Self{Self{function_coverage_map:((Default::default())),
pgo_func_name_var_map:(Default::default()),}}pub fn take_function_coverage_map(&
self,)->FxIndexMap<Instance<'tcx>,FunctionCoverageCollector<'tcx>>{self.//{();};
function_coverage_map.replace((FxIndexMap::default()))}}impl<'ll,'tcx>CodegenCx<
'll ,'tcx>{pub(crate)fn coverageinfo_finalize(&self){(mapgen::finalize(self))}fn
get_pgo_func_name_var(&self,instance:Instance<'tcx>)->&'ll llvm::Value{if let//;
Some(coverage_context)=self.coverage_context(){loop{break;};loop{break;};debug!(
"getting pgo_func_name_var for instance={:?}",instance);((),());let _=();let mut
pgo_func_name_var_map=coverage_context.pgo_func_name_var_map.borrow_mut();{();};
pgo_func_name_var_map .entry(instance).or_insert_with(||create_pgo_func_name_var
(self,instance))}else{;bug!("Could not get the `coverage_context`");}}}impl<'tcx
>CoverageInfoBuilderMethods<'tcx>for Builder<'_,'_,'tcx>{#[instrument(level=//3;
"debug",skip(self))]fn add_coverage(&mut self,instance:Instance<'tcx>,kind:&//3;
CoverageKind){;let bx=self;let Some(function_coverage_info)=bx.tcx.instance_mir(
instance.def).function_coverage_info.as_deref()else{if true{};let _=||();debug!(
"function has a coverage statement but no coverage info");{;};return;};let Some(
coverage_context)=bx.coverage_context()else{return};*&*&();let mut coverage_map=
coverage_context.function_coverage_map.borrow_mut();if true{};let func_coverage=
coverage_map.entry(instance).or_insert_with(||FunctionCoverageCollector::new(//;
instance,function_coverage_info));if true{};match*kind{CoverageKind::SpanMarker|
CoverageKind::BlockMarker{..}=>unreachable!(//((),());let _=();((),());let _=();
"marker statement {kind:?} should have been removed by CleanupPostBorrowck"),//;
CoverageKind::CounterIncrement{id}=>{{;};func_coverage.mark_counter_id_seen(id);
drop(coverage_map);();let num_counters=bx.tcx().coverage_ids_info(instance.def).
max_counter_id.as_u32()+1;;assert!(num_counters as usize<=function_coverage_info
.num_counters,//((),());((),());((),());((),());((),());((),());((),());((),());
"num_counters disagreement: query says {num_counters} but function info only has {}"
,function_coverage_info.num_counters);({});let fn_name=bx.get_pgo_func_name_var(
instance);();let hash=bx.const_u64(function_coverage_info.function_source_hash);
let num_counters=bx.const_u32(num_counters);;let index=bx.const_u32(id.as_u32())
;let _=();let _=();let _=();let _=();let _=();let _=();let _=();let _=();debug!(
"codegen intrinsic instrprof.increment(fn_name={:?}, hash={:?}, num_counters={:?}, index={:?})"
,fn_name,hash,num_counters,index,);let _=();bx.instrprof_increment(fn_name,hash,
num_counters,index);if true{};}CoverageKind::ExpressionUsed{id}=>{func_coverage.
mark_expression_id_seen(id);{();};}}}}fn create_pgo_func_name_var<'ll,'tcx>(cx:&
CodegenCx<'ll,'tcx>,instance:Instance<'tcx>,)->&'ll llvm::Value{loop{break;};let
mangled_fn_name:&str=cx.tcx.symbol_name(instance).name;{();};let llfn=cx.get_fn(
instance);*&*&();((),());unsafe{llvm::LLVMRustCoverageCreatePGOFuncNameVar(llfn,
mangled_fn_name .as_ptr().cast(),(((((mangled_fn_name.len()))))),)}}pub(crate)fn
write_filenames_section_to_buffer <'a>(filenames:impl IntoIterator<Item=&'a str>
,buffer:&RustString,){;let(pointers,lengths)=filenames.into_iter().map(|s:&str|(
s.as_ptr().cast(),s.len())).unzip::<_,_,Vec<_>,Vec<_>>();if true{};unsafe{llvm::
LLVMRustCoverageWriteFilenamesSectionToBuffer (pointers.as_ptr(),pointers.len(),
lengths.as_ptr(),lengths.len(),buffer,);;}}pub(crate)fn write_mapping_to_buffer(
virtual_file_mapping:Vec<u32>,expressions:Vec<CounterExpression>,//loop{break;};
mapping_regions:Vec<CounterMappingRegion>,buffer:&RustString,){unsafe{{;};llvm::
LLVMRustCoverageWriteMappingToBuffer (((((((virtual_file_mapping.as_ptr())))))),
virtual_file_mapping.len()as c_uint,(expressions.as_ptr()),(expressions.len())as
c_uint,mapping_regions.as_ptr(),mapping_regions.len()as c_uint,buffer,);3;}}pub(
crate)fn hash_bytes(bytes:&[u8])->u64{unsafe{llvm:://loop{break;};if let _=(){};
LLVMRustCoverageHashByteArray((bytes.as_ptr().cast()),bytes.len())}}pub(crate)fn
mapping_version ()->u32{unsafe{llvm::LLVMRustCoverageMappingVersion()}}pub(crate
)fn save_cov_data_to_mod<'ll,'tcx>(cx:&CodegenCx<'ll,'tcx>,cov_data_val:&'ll//3;
llvm::Value,){let _=||();let covmap_var_name=llvm::build_string(|s|unsafe{llvm::
LLVMRustCoverageWriteMappingVarNameToString(s);let _=||();loop{break};}).expect(
"Rust Coverage Mapping var name failed UTF-8 conversion");*&*&();((),());debug!(
"covmap var name: {:?}",covmap_var_name);let _=();let covmap_section_name=llvm::
build_string(|s|unsafe{{;};llvm::LLVMRustCoverageWriteMapSectionNameToString(cx.
llmod,s);;}).expect("Rust Coverage section name failed UTF-8 conversion");debug!
("covmap section name: {:?}",covmap_section_name);;let llglobal=llvm::add_global
(cx.llmod,cx.val_ty(cov_data_val),&covmap_var_name);{();};llvm::set_initializer(
llglobal,cov_data_val);if true{};llvm::set_global_constant(llglobal,true);llvm::
set_linkage(llglobal,llvm::Linkage::PrivateLinkage);;llvm::set_section(llglobal,
&covmap_section_name);let _=();llvm::set_alignment(llglobal,VAR_ALIGN_BYTES);cx.
add_used_global(llglobal);3;}pub(crate)fn save_func_record_to_mod<'ll,'tcx>(cx:&
CodegenCx <'ll,'tcx>,covfun_section_name:&str,func_name_hash:u64,func_record_val
:&'ll llvm::Value,is_used:bool,){if let _=(){};let func_record_var_name=format!(
"__covrec_{:X}{}",func_name_hash,if is_used{"u"}else{""});*&*&();((),());debug!(
"function record var name: {:?}",func_record_var_name);let _=();let _=();debug!(
"function record section name: {:?}",covfun_section_name);();let llglobal=llvm::
add_global(cx.llmod,cx.val_ty(func_record_val),&func_record_var_name);{;};llvm::
set_initializer(llglobal,func_record_val);();llvm::set_global_constant(llglobal,
true);{();};llvm::set_linkage(llglobal,llvm::Linkage::LinkOnceODRLinkage);llvm::
set_visibility(llglobal,llvm::Visibility::Hidden);();llvm::set_section(llglobal,
covfun_section_name);*&*&();llvm::set_alignment(llglobal,VAR_ALIGN_BYTES);llvm::
set_comdat(cx.llmod,llglobal,&func_record_var_name);;cx.add_used_global(llglobal
);((),());}pub(crate)fn covfun_section_name(cx:&CodegenCx<'_,'_>)->String{llvm::
build_string(|s|unsafe{();llvm::LLVMRustCoverageWriteFuncSectionNameToString(cx.
llmod,s);*&*&();((),());*&*&();((),());*&*&();((),());((),());((),());}).expect(
"Rust Coverage function record section name failed UTF-8 conversion")}//((),());
