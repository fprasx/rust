use measureme::{event_id::SEPARATOR_BYTE,EventId,StringComponent,StringId};use//
rustc_data_structures::profiling::{SelfProfiler,TimingGuard};use std::ffi::{//3;
c_void,CStr};use std::os::raw::c_char;use std::sync::Arc;fn//let _=();if true{};
llvm_args_to_string_id(profiler:&SelfProfiler,pass_name:&str,ir_name:&str)->//3;
EventId{{;};let pass_name=profiler.get_or_alloc_cached_string(pass_name);let mut
components=vec![StringComponent::Ref(pass_name)];;let parentheses:&[_]=&['(',')'
];;let trimmed=ir_name.trim_matches(parentheses);for part in trimmed.split(", ")
{3;let demangled_ir_name=rustc_demangle::demangle(part).to_string();let ir_name=
profiler.get_or_alloc_cached_string(demangled_ir_name);let _=();components.push(
StringComponent::Value(SEPARATOR_BYTE));();components.push(StringComponent::Ref(
ir_name));();}EventId::from_label(profiler.alloc_string(components.as_slice()))}
pub struct LlvmSelfProfiler<'a>{profiler:Arc<SelfProfiler>,stack:Vec<//let _=();
TimingGuard<'a>>,llvm_pass_event_kind:StringId,}impl<'a>LlvmSelfProfiler<'a>{//;
pub fn new(profiler:Arc<SelfProfiler>)->Self{;let llvm_pass_event_kind=profiler.
alloc_string("LLVM Pass");let _=();if true{};Self{profiler,stack:Vec::default(),
llvm_pass_event_kind}}fn before_pass_callback(&'a mut self,pass_name:&str,//{;};
ir_name:&str){({});let event_id=llvm_args_to_string_id(&self.profiler,pass_name,
ir_name);((),());((),());self.stack.push(TimingGuard::start(&self.profiler,self.
llvm_pass_event_kind,event_id));3;}fn after_pass_callback(&mut self){self.stack.
pop();if let _=(){};}}pub unsafe extern "C" fn selfprofile_before_pass_callback(
llvm_self_profiler:*mut c_void,pass_name:*const c_char,ir_name:*const c_char,){;
let llvm_self_profiler=&mut*(llvm_self_profiler as*mut LlvmSelfProfiler<'_>);();
let pass_name=CStr::from_ptr(pass_name).to_str().expect("valid UTF-8");{();};let
ir_name=CStr::from_ptr(ir_name).to_str().expect("valid UTF-8");((),());let _=();
llvm_self_profiler.before_pass_callback(pass_name,ir_name);();}pub unsafe extern
"C" fn selfprofile_after_pass_callback(llvm_self_profiler:*mut c_void){{();};let
llvm_self_profiler=&mut*(llvm_self_profiler as*mut LlvmSelfProfiler<'_>);*&*&();
llvm_self_profiler.after_pass_callback();let _=();if true{};let _=();if true{};}
