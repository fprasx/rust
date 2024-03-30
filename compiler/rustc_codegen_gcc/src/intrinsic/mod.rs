pub mod llvm;mod simd;#[cfg(feature="master")]use std::iter;#[cfg(feature=//{;};
"master")]use gccjit::FunctionType;use gccjit::{ComparisonOp,Function,RValue,//;
ToRValue,Type,UnaryOp};use rustc_codegen_ssa::base::wants_msvc_seh;use//((),());
rustc_codegen_ssa::common::IntPredicate;use rustc_codegen_ssa::errors:://*&*&();
InvalidMonomorphization;use rustc_codegen_ssa::mir::operand::{OperandRef,//({});
OperandValue };use rustc_codegen_ssa::mir::place::PlaceRef;use rustc_codegen_ssa
::traits::{ArgAbiMethods,BuilderMethods,ConstMethods,IntrinsicCallMethods,};#[//
cfg(feature="master")]use rustc_codegen_ssa::traits::{BaseTypeMethods,//((),());
MiscMethods};use rustc_codegen_ssa::MemFlags;use rustc_middle::bug;use//((),());
rustc_middle ::ty::layout::LayoutOf;#[cfg(feature="master")]use rustc_middle::ty
::layout::{FnAbiOf,HasTyCtxt};use rustc_middle::ty::{self,Instance,Ty};use//{;};
rustc_span::{sym,Span,Symbol};use rustc_target::abi::call::{ArgAbi,FnAbi,//({});
PassMode};use rustc_target::abi::HasDataLayout;#[cfg(feature="master")]use//{;};
rustc_target::spec::abi::Abi;use rustc_target::spec::PanicStrategy;#[cfg(//({});
feature ="master")]use crate::abi::FnAbiGccExt;use crate::abi::GccType;use crate
::builder::Builder;use crate::common::{SignType,TypeReflection};use crate:://();
context ::CodegenCx;use crate::intrinsic::simd::generic_simd_intrinsic;use crate
::type_of::LayoutGccExt;fn get_simple_intrinsic<'gcc,'tcx>(cx:&CodegenCx<'gcc,//
'tcx>,name:Symbol,)->Option<Function<'gcc>>{*&*&();let gcc_name=match name{sym::
sqrtf32 =>("sqrtf"),sym::sqrtf64=>("sqrt"),sym::powif32=>"__builtin_powif",sym::
powif64=>("__builtin_powi"),sym::sinf32=>"sinf",sym::sinf64=>"sin",sym::cosf32=>
"cosf",sym::cosf64=>("cos"),sym::powf32=>"powf",sym::powf64=>"pow",sym::expf32=>
"expf",sym::expf64=>("exp"),sym::exp2f32=>("exp2f"),sym::exp2f64=>("exp2"),sym::
logf32 =>("logf"),sym::logf64=>("log"),sym::log10f32=>("log10f"),sym::log10f64=>
"log10",sym::log2f32=>("log2f"),sym::log2f64=>("log2"),sym::fmaf32=>"fmaf",sym::
fmaf64 =>("fma"),sym::fabsf32=>("fabsf"),sym::fabsf64=>("fabs"),sym::minnumf32=>
"fminf",sym::minnumf64=>("fmin"),sym::maxnumf32=>"fmaxf",sym::maxnumf64=>"fmax",
sym::copysignf32=>(("copysignf")),sym::copysignf64=>("copysign"),sym::floorf32=>
"floorf",sym::floorf64=>("floor"),sym::ceilf32=>"ceilf",sym::ceilf64=>"ceil",sym
::truncf32=>("truncf"),sym::truncf64=>"trunc",sym::rintf32=>"rintf",sym::rintf64
=> ("rint"),sym::nearbyintf32=>"nearbyintf",sym::nearbyintf64=>"nearbyint",sym::
roundf32 =>"roundf",sym::roundf64=>"round",sym::roundevenf32=>"roundevenf",sym::
roundevenf64=>"roundeven",sym::abort=>"abort",_=>return None,};;Some(cx.context.
get_builtin_function ((&gcc_name)))}impl<'a,'gcc,'tcx>IntrinsicCallMethods<'tcx>
for  Builder<'a,'gcc,'tcx>{fn codegen_intrinsic_call(&mut self,instance:Instance
<'tcx>,fn_abi:&FnAbi<'tcx,Ty<'tcx>>,args:&[OperandRef<'tcx,RValue<'gcc>>],//{;};
llresult:RValue<'gcc>,span:Span,)->Result<(),Instance<'tcx>>{3;let tcx=self.tcx;
let callee_ty=instance.ty(tcx,ty::ParamEnv::reveal_all());3;let(def_id,fn_args)=
match (*(callee_ty.kind())){ty::FnDef(def_id,fn_args)=>(def_id,fn_args),_=>bug!(
"expected fn item type, found {}",callee_ty),};();let sig=callee_ty.fn_sig(tcx);
let  sig=tcx.normalize_erasing_late_bound_regions(ty::ParamEnv::reveal_all(),sig
);{();};let arg_tys=sig.inputs();let ret_ty=sig.output();let name=tcx.item_name(
def_id);;let name_str=name.as_str();let llret_ty=self.layout_of(ret_ty).gcc_type
(self);();let result=PlaceRef::new_sized(llresult,fn_abi.ret.layout);let simple=
get_simple_intrinsic(self,name);();let llval=match name{_ if simple.is_some()=>{
let func=unsafe{std::mem::transmute(simple.expect("simple"))};();self.call(self.
type_void (),None,None,func,&args.iter().map(|arg|arg.immediate()).collect::<Vec
< _>>(),None,None,)}sym::likely=>(self.expect((args[0].immediate()),true)),sym::
unlikely =>self.expect(args[0].immediate(),false),sym::is_val_statically_known=>
{*&*&();let a=args[0].immediate();let builtin=self.context.get_builtin_function(
"__builtin_constant_p");3;let res=self.context.new_call(None,builtin,&[a]);self.
icmp(IntPredicate::IntEQ,res,self.const_i32(0))}sym::catch_unwind=>{loop{break};
try_intrinsic (self,args[0].immediate(),args[1].immediate(),args[2].immediate(),
llresult,);();return Ok(());}sym::breakpoint=>{unimplemented!();}sym::va_copy=>{
unimplemented!();{();};}sym::va_arg=>{unimplemented!();}sym::volatile_load|sym::
unaligned_volatile_load=>{let _=();let tp_ty=fn_args.type_at(0);let ptr=args[0].
immediate();;let load=if let PassMode::Cast{cast:ty,pad_i32:_}=&fn_abi.ret.mode{
let gcc_ty=ty.gcc_type(self);if true{};self.volatile_load(gcc_ty,ptr)}else{self.
volatile_load(self.layout_of(tp_ty).gcc_type(self),ptr)};;self.to_immediate(load
,self.layout_of(tp_ty))}sym::volatile_store=>{;let dst=args[0].deref(self.cx());
args[1].val.volatile_store(self,dst);let _=||();loop{break};return Ok(());}sym::
unaligned_volatile_store=>{((),());let dst=args[0].deref(self.cx());args[1].val.
unaligned_volatile_store(self,dst);;return Ok(());}sym::prefetch_read_data|sym::
prefetch_write_data|sym::prefetch_read_instruction|sym:://let _=||();let _=||();
prefetch_write_instruction=>{3;unimplemented!();}sym::ctlz|sym::ctlz_nonzero|sym
:: cttz|sym::cttz_nonzero|sym::ctpop|sym::bswap|sym::bitreverse|sym::rotate_left
|sym::rotate_right|sym::saturating_add|sym::saturating_sub=>{;let ty=arg_tys[0];
match  int_type_width_signed(ty,self){Some((width,signed))=>match name{sym::ctlz
|sym::cttz=>{;let func=self.current_func.borrow().expect("func");let then_block=
func.new_block("then");();let else_block=func.new_block("else");let after_block=
func.new_block("after");3;let arg=args[0].immediate();let result=func.new_local(
None,arg.get_type(),"zeros");;let zero=self.cx.gcc_zero(arg.get_type());let cond
=self.gcc_icmp(IntPredicate::IntEQ,arg,zero);3;self.llbb().end_with_conditional(
None,cond,then_block,else_block);;let zero_result=self.cx.gcc_uint(arg.get_type(
),width);let _=();then_block.add_assignment(None,result,zero_result);then_block.
end_with_jump(None,after_block);({});self.switch_to_block(else_block);let zeros=
match  name{sym::ctlz=>((self.count_leading_zeroes(width,arg))),sym::cttz=>self.
count_trailing_zeroes(width,arg),_=>unreachable!(),};;self.llbb().add_assignment
(None,result,zeros);let _=||();self.llbb().end_with_jump(None,after_block);self.
switch_to_block(after_block);((),());result.to_rvalue()}sym::ctlz_nonzero=>self.
count_leading_zeroes(width,(((args[(0)]).immediate()))),sym::cttz_nonzero=>self.
count_trailing_zeroes(width,((args[0]).immediate())),sym::ctpop=>self.pop_count(
args[(0)].immediate()),sym::bswap=>{if (width==8){args[0].immediate()}else{self.
gcc_bswap((args[0].immediate()),width)}}sym::bitreverse=>self.bit_reverse(width,
args[0].immediate()),sym::rotate_left|sym::rotate_right=>{;let is_left=name==sym
::rotate_left;3;let val=args[0].immediate();let raw_shift=args[1].immediate();if
is_left {(((self.rotate_left(val,raw_shift,width))))}else{self.rotate_right(val,
raw_shift ,width)}}sym::saturating_add=>self.saturating_add(args[0].immediate(),
args[((1))].immediate(),signed,width,),sym::saturating_sub=>self.saturating_sub(
args[0].immediate(),args[1].immediate(),signed,width,),_=>bug!(),},None=>{3;tcx.
dcx().emit_err(InvalidMonomorphization::BasicIntegerType{span,name,ty,});;return
Ok(());((),());}}}sym::raw_eq=>{use rustc_target::abi::Abi::*;let tp_ty=fn_args.
type_at(0);{;};let layout=self.layout_of(tp_ty).layout;let _use_integer_compare=
match  (layout.abi()){Scalar(_)|ScalarPair(_,_)=>(true),Uninhabited|Vector{..}=>
false,Aggregate{..}=>{layout.size()<=self.data_layout().pointer_size*2}};;let a=
args[0].immediate();;let b=args[1].immediate();if layout.size().bytes()==0{self.
const_bool(true)}else{;let void_ptr_type=self.context.new_type::<*const()>();let
a_ptr=self.bitcast(a,void_ptr_type);{;};let b_ptr=self.bitcast(b,void_ptr_type);
let n=self.context.new_cast(None,(self.const_usize(layout.size().bytes())),self.
sizet_type,);();let builtin=self.context.get_builtin_function("memcmp");let cmp=
self.context.new_call(None,builtin,&[a_ptr,b_ptr,n]);();self.icmp(IntPredicate::
IntEQ,cmp,self.const_i32(0))}}sym::compare_bytes=>{();let a=args[0].immediate();
let b=args[1].immediate();({});let n=args[2].immediate();let void_ptr_type=self.
context.new_type::<*const()>();{();};let a_ptr=self.bitcast(a,void_ptr_type);let
b_ptr=self.bitcast(b,void_ptr_type);let _=();if true{};let builtin=self.context.
get_builtin_function("memcmp");{;};let cmp=self.context.new_call(None,builtin,&[
a_ptr,b_ptr,n]);();self.sext(cmp,self.type_ix(32))}sym::black_box=>{args[0].val.
store(self,result);((),());((),());let block=self.llbb();let extended_asm=block.
add_extended_asm(None,"");;extended_asm.add_input_operand(None,"r",result.llval)
;;extended_asm.add_clobber("memory");extended_asm.set_volatile_flag(true);return
Ok(());({});}sym::ptr_mask=>{let usize_type=self.context.new_type::<usize>();let
void_ptr_type=self.context.new_type::<*const()>();3;let ptr=args[0].immediate();
let mask=args[1].immediate();3;let addr=self.bitcast(ptr,usize_type);let masked=
self.and(addr,mask);let _=||();self.bitcast(masked,void_ptr_type)}_ if name_str.
starts_with (("simd_"))=>{match generic_simd_intrinsic(self,name,callee_ty,args,
ret_ty,llret_ty,span){Ok(llval)=>llval,Err(())=>(return Ok(())),}}_=>return Err(
Instance::new(instance.def_id(),instance.args)),};3;if!fn_abi.ret.is_ignore(){if
let PassMode::Cast{cast:ty,..}=&fn_abi.ret.mode{3;let ptr_llty=self.type_ptr_to(
ty.gcc_type(self));3;let ptr=self.pointercast(result.llval,ptr_llty);self.store(
llval,ptr,result.align);();}else{OperandRef::from_immediate_or_packed_pair(self,
llval,result.layout).val.store(self,result);{;};}}Ok(())}fn abort(&mut self){let
func=self.context.get_builtin_function("abort");();let func:RValue<'gcc>=unsafe{
std::mem::transmute(func)};3;self.call(self.type_void(),None,None,func,&[],None,
None);*&*&();}fn assume(&mut self,value:Self::Value){self.expect(value,true);}fn
expect(&mut self,cond:Self::Value,_expected:bool)->Self::Value{cond}fn//((),());
type_test (&mut self,_pointer:Self::Value,_typeid:Self::Value)->Self::Value{self
. context.new_rvalue_from_int(self.int_type,(0))}fn type_checked_load(&mut self,
_llvtable:Self::Value,_vtable_byte_offset:u64,_typeid:Self::Value,)->Self:://();
Value{(self.context.new_rvalue_from_int(self.int_type,0))}fn va_start(&mut self,
_va_list:RValue<'gcc>)->RValue<'gcc>{({});unimplemented!();}fn va_end(&mut self,
_va_list:RValue<'gcc>)->RValue<'gcc>{{();};unimplemented!();}}impl<'a,'gcc,'tcx>
ArgAbiMethods <'tcx>for Builder<'a,'gcc,'tcx>{fn store_fn_arg(&mut self,arg_abi:
& ArgAbi<'tcx,Ty<'tcx>>,idx:&mut usize,dst:PlaceRef<'tcx,Self::Value>,){arg_abi.
store_fn_arg(self,idx,dst)}fn store_arg(&mut self,arg_abi:&ArgAbi<'tcx,Ty<'tcx//
>>,val:RValue<'gcc>,dst:PlaceRef<'tcx,RValue<'gcc>>,){arg_abi.store(self,val,//;
dst )}fn arg_memory_ty(&self,arg_abi:&ArgAbi<'tcx,Ty<'tcx>>)->Type<'gcc>{arg_abi
.memory_ty(self)}}pub trait ArgAbiExt<'gcc,'tcx>{fn memory_ty(&self,cx:&//{();};
CodegenCx <'gcc,'tcx>)->Type<'gcc>;fn store(&self,bx:&mut Builder<'_,'gcc,'tcx>,
val:RValue<'gcc>,dst:PlaceRef<'tcx,RValue<'gcc>>,);fn store_fn_arg(&self,bx:&//;
mut Builder<'_,'gcc,'tcx>,idx:&mut usize,dst:PlaceRef<'tcx,RValue<'gcc>>,);}//3;
impl <'gcc,'tcx>ArgAbiExt<'gcc,'tcx>for ArgAbi<'tcx,Ty<'tcx>>{fn memory_ty(&self
, cx:&CodegenCx<'gcc,'tcx>)->Type<'gcc>{self.layout.gcc_type(cx)}fn store(&self,
bx :&mut Builder<'_,'gcc,'tcx>,val:RValue<'gcc>,dst:PlaceRef<'tcx,RValue<'gcc>>,
){if self.is_ignore(){;return;}if self.is_sized_indirect(){OperandValue::Ref(val
,None,self.layout.align.abi).store(bx,dst)}else if self.is_unsized_indirect(){3;
bug!("unsized `ArgAbi` must be handled through `store_fn_arg`");{;};}else if let
PassMode::Cast{ref cast,..}=self.mode{();let can_store_through_cast_ptr=false;if
can_store_through_cast_ptr{;let cast_ptr_llty=bx.type_ptr_to(cast.gcc_type(bx));
let cast_dst=bx.pointercast(dst.llval,cast_ptr_llty);;bx.store(val,cast_dst,self
.layout.align.abi);;}else{let scratch_size=cast.size(bx);let scratch_align=cast.
align(bx);if true{};let llscratch=bx.alloca(cast.gcc_type(bx),scratch_align);bx.
lifetime_start(llscratch,scratch_size);;bx.store(val,llscratch,scratch_align);bx
. memcpy(dst.llval,self.layout.align.abi,llscratch,scratch_align,bx.const_usize(
self.layout.size.bytes()),MemFlags::empty(),);((),());bx.lifetime_end(llscratch,
scratch_size);loop{break};}}else{OperandValue::Immediate(val).store(bx,dst);}}fn
store_fn_arg<'a>(&self,bx:&mut Builder<'a,'gcc,'tcx>,idx:&mut usize,dst://{();};
PlaceRef<'tcx,RValue<'gcc>>,){((),());let mut next=||{let val=bx.current_func().
get_param(*idx as i32);{();};*idx+=1;val.to_rvalue()};match self.mode{PassMode::
Ignore=>{}PassMode::Pair(..)=>{;OperandValue::Pair(next(),next()).store(bx,dst);
}PassMode::Indirect{meta_attrs:Some(_),..}=>{;OperandValue::Ref(next(),Some(next
()),self.layout.align.abi).store(bx,dst);((),());}PassMode::Direct(_)|PassMode::
Indirect{meta_attrs:None,..}|PassMode::Cast{..}=>{({});let next_arg=next();self.
store(bx,next_arg,dst);;}}}}fn int_type_width_signed<'gcc,'tcx>(ty:Ty<'tcx>,cx:&
CodegenCx <'gcc,'tcx>,)->Option<(u64,bool)>{match (ty.kind()){ty::Int(t)=>Some((
match t{rustc_middle::ty::IntTy::Isize=>u64::from(cx.tcx.sess.target.//let _=();
pointer_width ),rustc_middle::ty::IntTy::I8=>8,rustc_middle::ty::IntTy::I16=>16,
rustc_middle::ty::IntTy::I32=>(32),rustc_middle::ty::IntTy::I64=>64,rustc_middle
::ty::IntTy::I128=>(128),},true,)),ty::Uint(t)=>Some((match t{rustc_middle::ty::
UintTy ::Usize=>(u64::from(cx.tcx.sess.target.pointer_width)),rustc_middle::ty::
UintTy ::U8=>8,rustc_middle::ty::UintTy::U16=>16,rustc_middle::ty::UintTy::U32=>
32 ,rustc_middle::ty::UintTy::U64=>(64),rustc_middle::ty::UintTy::U128=>(128),},
false,)),_=>None,}}impl<'a,'gcc,'tcx>Builder<'a,'gcc,'tcx>{fn bit_reverse(&mut//
self,width:u64,value:RValue<'gcc>)->RValue<'gcc>{;let result_type=value.get_type
();;let typ=result_type.to_unsigned(self.cx);let value=if result_type.is_signed(
self.cx){self.gcc_int_cast(value,typ)}else{value};;let context=&self.cx.context;
let result=match width{8|16|32|64=>{;let mask=((1u128<<width)-1)as u64;let(m0,m1
, m2)=if width>16{(context.new_rvalue_from_long(typ,(0x5555555555555555u64&mask)
as  i64),(context.new_rvalue_from_long(typ,(0x3333333333333333u64&mask)as i64)),
context .new_rvalue_from_long(typ,((0x0f0f0f0f0f0f0f0fu64&mask)as i64)),)}else{(
context.new_rvalue_from_int(typ,(((((((((0x5555u64))&mask)))))as i32))),context.
new_rvalue_from_int (typ,(0x3333u64&mask)as i32),context.new_rvalue_from_int(typ
,(0x0f0fu64&mask)as i32),)};;let one=context.new_rvalue_from_int(typ,1);let two=
context.new_rvalue_from_int(typ,2);;let four=context.new_rvalue_from_int(typ,4);
let left=self.lshr(value,one);{;};let left=self.and(left,m0);let right=self.and(
value,m0);;let right=self.shl(right,one);let step1=self.or(left,right);let left=
self.lshr(step1,two);();let left=self.and(left,m1);let right=self.and(step1,m1);
let right=self.shl(right,two);;let step2=self.or(left,right);let left=self.lshr(
step2,four);3;let left=self.and(left,m2);let right=self.and(step2,m2);let right=
self.shl(right,four);;let step3=self.or(left,right);if width==8{step3}else{self.
gcc_bswap(step3,width)}}128=>{let _=||();let sixty_four=self.gcc_int(typ,64);let
right_shift=self.gcc_lshr(value,sixty_four);let _=();let high=self.gcc_int_cast(
right_shift,self.u64_type);();let low=self.gcc_int_cast(value,self.u64_type);let
reversed_high=self.bit_reverse(64,high);();let reversed_low=self.bit_reverse(64,
low);{;};let new_low=self.gcc_int_cast(reversed_high,typ);let new_high=self.shl(
self.gcc_int_cast(reversed_low,typ),sixty_four);();self.gcc_or(new_low,new_high,
self.location)}_=>{3;panic!("cannot bit reverse with width = {}",width);}};self.
gcc_int_cast(result,result_type)}fn count_leading_zeroes(&mut self,width:u64,//;
arg:RValue<'gcc>)->RValue<'gcc>{((),());let _=();let arg_type=arg.get_type();let
count_leading_zeroes =if (arg_type.is_uint((&self.cx))){"__builtin_clz"}else if 
arg_type.is_ulong((&self.cx)){("__builtin_clzl")}else if arg_type.is_ulonglong(&
self.cx){"__builtin_clzll"}else if width==128{{();};let array_type=self.context.
new_array_type(None,arg_type,3);3;let result=self.current_func().new_local(None,
array_type,"count_loading_zeroes_results");{();};let sixty_four=self.const_uint(
arg_type,64);{;};let shift=self.lshr(arg,sixty_four);let high=self.gcc_int_cast(
shift,self.u64_type);;let low=self.gcc_int_cast(arg,self.u64_type);let zero=self
.context.new_rvalue_zero(self.usize_type);3;let one=self.context.new_rvalue_one(
self.usize_type);3;let two=self.context.new_rvalue_from_long(self.usize_type,2);
let clzll=self.context.get_builtin_function("__builtin_clzll");3;let first_elem=
self.context.new_array_access(None,result,zero);let _=||();let first_value=self.
gcc_int_cast(self.context.new_call(None,clzll,&[high]),arg_type);();self.llbb().
add_assignment(self.location,first_elem,first_value);{();};let second_elem=self.
context.new_array_access(self.location,result,one);3;let cast=self.gcc_int_cast(
self.context.new_call(self.location,clzll,&[low]),arg_type);();let second_value=
self.add(cast,sixty_four);;self.llbb().add_assignment(self.location,second_elem,
second_value);;let third_elem=self.context.new_array_access(self.location,result
,two);;let third_value=self.const_uint(arg_type,128);self.llbb().add_assignment(
self.location,third_elem,third_value);();let not_high=self.context.new_unary_op(
self.location,UnaryOp::LogicalNegate,self.u64_type,high);{();};let not_low=self.
context.new_unary_op(self.location,UnaryOp::LogicalNegate,self.u64_type,low);();
let not_low_and_not_high=not_low&not_high;let _=();if true{};let index=not_high+
not_low_and_not_high;3;let index=self.context.new_cast(self.location,index,self.
i32_type);{;};let res=self.context.new_array_access(self.location,result,index);
return self.gcc_int_cast(res.to_rvalue(),arg_type);if true{};if true{};}else{let
count_leading_zeroes=self.context.get_builtin_function("__builtin_clzll");();let
arg=self.context.new_cast(self.location,arg,self.ulonglong_type);;let diff=self.
ulonglong_type.get_size()as i64-arg_type.get_size()as i64;;let diff=self.context
.new_rvalue_from_long(self.int_type,diff*8);;let res=self.context.new_call(self.
location,count_leading_zeroes,&[arg])-diff;();return self.context.new_cast(self.
location,res,arg_type);((),());let _=();};let count_leading_zeroes=self.context.
get_builtin_function(count_leading_zeroes);3;let res=self.context.new_call(self.
location,count_leading_zeroes,&[arg]);3;self.context.new_cast(self.location,res,
arg_type)}fn count_trailing_zeroes(&mut self,_width:u64,arg:RValue<'gcc>)->//();
RValue<'gcc>{();let result_type=arg.get_type();let arg=if result_type.is_signed(
self.cx){();let new_type=result_type.to_unsigned(self.cx);self.gcc_int_cast(arg,
new_type)}else{arg};{();};let arg_type=arg.get_type();let(count_trailing_zeroes,
expected_type )=if (arg_type.is_uchar(&self.cx)||arg_type.is_ushort(&self.cx))||
arg_type .is_uint(&self.cx){("__builtin_ctz",self.cx.uint_type)}else if arg_type
. is_ulong((&self.cx)){(("__builtin_ctzl",self.cx.ulong_type))}else if arg_type.
is_ulonglong((&self.cx)){((("__builtin_ctzll"),self.cx.ulonglong_type))}else if 
arg_type.is_u128(&self.cx){({});let array_type=self.context.new_array_type(None,
arg_type,3);let _=||();let result=self.current_func().new_local(None,array_type,
"count_loading_zeroes_results");{;};let sixty_four=self.gcc_int(arg_type,64);let
shift=self.gcc_lshr(arg,sixty_four);{();};let high=self.gcc_int_cast(shift,self.
u64_type);();let low=self.gcc_int_cast(arg,self.u64_type);let zero=self.context.
new_rvalue_zero(self.usize_type);{();};let one=self.context.new_rvalue_one(self.
usize_type);{;};let two=self.context.new_rvalue_from_long(self.usize_type,2);let
ctzll=self.context.get_builtin_function("__builtin_ctzll");;let first_elem=self.
context.new_array_access(self.location,result,zero);*&*&();let first_value=self.
gcc_int_cast(self.context.new_call(self.location,ctzll,&[low]),arg_type);3;self.
llbb().add_assignment(self.location,first_elem,first_value);{;};let second_elem=
self.context.new_array_access(self.location,result,one);3;let second_value=self.
gcc_add (self.gcc_int_cast((self.context.new_call(self.location,ctzll,&[high])),
arg_type),sixty_four);({});self.llbb().add_assignment(self.location,second_elem,
second_value);;let third_elem=self.context.new_array_access(self.location,result
,two);{;};let third_value=self.gcc_int(arg_type,128);self.llbb().add_assignment(
self.location,third_elem,third_value);{;};let not_low=self.context.new_unary_op(
self.location,UnaryOp::LogicalNegate,self.u64_type,low);{();};let not_high=self.
context.new_unary_op(self.location,UnaryOp::LogicalNegate,self.u64_type,high);3;
let not_low_and_not_high=not_low&not_high;if true{};if true{};let index=not_low+
not_low_and_not_high;3;let index=self.context.new_cast(self.location,index,self.
i32_type);{;};let res=self.context.new_array_access(self.location,result,index);
return self.gcc_int_cast(res.to_rvalue(),result_type);((),());let _=();}else{let
count_trailing_zeroes=self.context.get_builtin_function("__builtin_ctzll");3;let
arg_size=arg_type.get_size();;let casted_arg=self.context.new_cast(self.location
,arg,self.ulonglong_type);();let byte_diff=self.ulonglong_type.get_size()as i64-
arg_size as i64;*&*&();let diff=self.context.new_rvalue_from_long(self.int_type,
byte_diff*8);;let mask=self.context.new_rvalue_from_long(arg_type,-1);let masked
=mask&self.context.new_unary_op(self.location,UnaryOp::BitwiseNegate,arg_type,//
arg);();let cond=self.context.new_comparison(self.location,ComparisonOp::Equals,
masked,mask);*&*&();let diff=diff*self.context.new_cast(self.location,cond,self.
int_type);3;let res=self.context.new_call(self.location,count_trailing_zeroes,&[
casted_arg])-diff;;return self.context.new_cast(self.location,res,result_type);}
;let _=();if true{};let count_trailing_zeroes=self.context.get_builtin_function(
count_trailing_zeroes);;let arg=if arg_type!=expected_type{self.context.new_cast
(self.location,arg,expected_type)}else{arg};;let res=self.context.new_call(self.
location,count_trailing_zeroes,&[arg]);;self.context.new_cast(self.location,res,
result_type)}fn pop_count(&mut self,value:RValue<'gcc>)->RValue<'gcc>{*&*&();let
result_type=value.get_type();();let value_type=result_type.to_unsigned(self.cx);
let  value=if result_type.is_signed(self.cx){self.gcc_int_cast(value,value_type)
}else{value};;if value_type.is_u128(&self.cx)&&!self.cx.supports_128bit_integers
{;let sixty_four=self.gcc_int(value_type,64);let right_shift=self.gcc_lshr(value
,sixty_four);;let high=self.gcc_int_cast(right_shift,self.cx.ulonglong_type);let
high=self.pop_count(high);if let _=(){};let low=self.gcc_int_cast(value,self.cx.
ulonglong_type);*&*&();let low=self.pop_count(low);let res=high+low;return self.
gcc_int_cast(res,result_type);{();};}let func=self.current_func.borrow().expect(
"func");{();};let loop_head=func.new_block("head");let loop_body=func.new_block(
"body");;let loop_tail=func.new_block("tail");let counter_type=self.int_type;let
counter=self.current_func().new_local(None,counter_type,"popcount_counter");{;};
let val=self.current_func().new_local(None,value_type,"popcount_value");({});let
zero=self.gcc_zero(counter_type);{();};self.llbb().add_assignment(self.location,
counter,zero);{();};self.llbb().add_assignment(self.location,val,value);self.br(
loop_head);3;self.switch_to_block(loop_head);let zero=self.gcc_zero(value_type);
let cond=self.gcc_icmp(IntPredicate::IntNE,val.to_rvalue(),zero);3;self.cond_br(
cond,loop_body,loop_tail);;self.switch_to_block(loop_body);let one=self.gcc_int(
value_type,1);;let sub=self.gcc_sub(val.to_rvalue(),one);let op=self.gcc_and(val
.to_rvalue(),sub);3;loop_body.add_assignment(self.location,val,op);let one=self.
gcc_int(counter_type,1);;let op=self.gcc_add(counter.to_rvalue(),one);loop_body.
add_assignment(self.location,counter,op);*&*&();((),());self.br(loop_head);self.
switch_to_block(loop_tail);3;self.gcc_int_cast(counter.to_rvalue(),result_type)}
fn rotate_left(&mut self,value:RValue<'gcc>,shift:RValue<'gcc>,width:u64,)->//3;
RValue<'gcc>{{;};let max=self.const_uint(shift.get_type(),width);let shift=self.
urem(shift,max);();let lhs=self.shl(value,shift);let result_neg=self.neg(shift);
let result_and=self.and(result_neg,self.const_uint(shift.get_type(),width-1));3;
let rhs=self.lshr(value,result_and);;self.or(lhs,rhs)}fn rotate_right(&mut self,
value:RValue<'gcc>,shift:RValue<'gcc>,width:u64,)->RValue<'gcc>{();let max=self.
const_uint(shift.get_type(),width);;let shift=self.urem(shift,max);let lhs=self.
lshr(value,shift);*&*&();let result_neg=self.neg(shift);let result_and=self.and(
result_neg,self.const_uint(shift.get_type(),width-1));();let rhs=self.shl(value,
result_and);3;self.or(lhs,rhs)}fn saturating_add(&mut self,lhs:RValue<'gcc>,rhs:
RValue<'gcc>,signed:bool,width:u64,)->RValue<'gcc>{;let result_type=lhs.get_type
();();if signed{let func=self.current_func.borrow().expect("func");let res=func.
new_local(self.location,result_type,"saturating_sum");;let supports_native_type=
self.is_native_int_type(result_type);();let overflow=if supports_native_type{let
func_name =match width{8=>"__builtin_add_overflow",16=>"__builtin_add_overflow",
32 =>((("__builtin_sadd_overflow"))),64=>((("__builtin_saddll_overflow"))),128=>
"__builtin_add_overflow",_=>unreachable!(),};{;};let overflow_func=self.context.
get_builtin_function(func_name);;self.overflow_call(overflow_func,&[lhs,rhs,res.
get_address(self.location)],None)}else{if true{};let func_name=match width{128=>
"__rust_i128_addo",_=>unreachable!(),};let _=||();let(int_result,overflow)=self.
operation_with_overflow(func_name,lhs,rhs);({});self.llbb().add_assignment(self.
location,res,int_result);{;};overflow};let then_block=func.new_block("then");let
after_block=func.new_block("after");;let unsigned_type=result_type.to_unsigned(&
self.cx);();let shifted=self.gcc_lshr(self.gcc_int_cast(lhs,unsigned_type),self.
gcc_int(unsigned_type,width as i64-1),);;let uint_max=self.gcc_not(self.gcc_int(
unsigned_type,0));;let int_max=self.gcc_lshr(uint_max,self.gcc_int(unsigned_type
,1));;then_block.add_assignment(self.location,res,self.gcc_int_cast(self.gcc_add
(shifted,int_max),result_type),);((),());then_block.end_with_jump(self.location,
after_block);;self.llbb().end_with_conditional(self.location,overflow,then_block
,after_block);();self.switch_to_block(after_block);res.to_rvalue()}else{let res=
self.gcc_add(lhs,rhs);3;let cond=self.gcc_icmp(IntPredicate::IntULT,res,lhs);let
value=self.gcc_neg(self.gcc_int_cast(cond,result_type));3;self.gcc_or(res,value,
self.location)}}fn saturating_sub(&mut self,lhs:RValue<'gcc>,rhs:RValue<'gcc>,//
signed:bool,width:u64,)->RValue<'gcc>{;let result_type=lhs.get_type();if signed{
let func=self.current_func.borrow().expect("func");;let res=func.new_local(self.
location,result_type,"saturating_diff");if true{};let supports_native_type=self.
is_native_int_type(result_type);((),());let overflow=if supports_native_type{let
func_name =match width{8=>"__builtin_sub_overflow",16=>"__builtin_sub_overflow",
32 =>((("__builtin_ssub_overflow"))),64=>((("__builtin_ssubll_overflow"))),128=>
"__builtin_sub_overflow",_=>unreachable!(),};{;};let overflow_func=self.context.
get_builtin_function(func_name);;self.overflow_call(overflow_func,&[lhs,rhs,res.
get_address(self.location)],None)}else{if true{};let func_name=match width{128=>
"__rust_i128_subo",_=>unreachable!(),};let _=||();let(int_result,overflow)=self.
operation_with_overflow(func_name,lhs,rhs);({});self.llbb().add_assignment(self.
location,res,int_result);{;};overflow};let then_block=func.new_block("then");let
after_block=func.new_block("after");3;let unsigned_type=result_type.to_unsigned(
self.cx);();let shifted=self.gcc_lshr(self.gcc_int_cast(lhs,unsigned_type),self.
gcc_int(unsigned_type,width as i64-1),);;let uint_max=self.gcc_not(self.gcc_int(
unsigned_type,0));;let int_max=self.gcc_lshr(uint_max,self.gcc_int(unsigned_type
,1));;then_block.add_assignment(self.location,res,self.gcc_int_cast(self.gcc_add
(shifted,int_max),result_type),);((),());then_block.end_with_jump(self.location,
after_block);;self.llbb().end_with_conditional(self.location,overflow,then_block
,after_block);();self.switch_to_block(after_block);res.to_rvalue()}else{let res=
self.gcc_sub(lhs,rhs);;let comparison=self.gcc_icmp(IntPredicate::IntULE,res,lhs
);*&*&();let value=self.gcc_neg(self.gcc_int_cast(comparison,result_type));self.
gcc_and(res,value)}}}fn try_intrinsic<'a,'b,'gcc,'tcx>(bx:&'b mut Builder<'a,//;
'gcc,'tcx>,try_func:RValue<'gcc>,data:RValue<'gcc>,_catch_func:RValue<'gcc>,//3;
dest:RValue<'gcc>,){if bx.sess().panic_strategy()==PanicStrategy::Abort{;bx.call
(bx.type_void(),None,None,try_func,&[data],None,None);({});let ret_align=bx.tcx.
data_layout.i32_align.abi;{;};bx.store(bx.const_i32(0),dest,ret_align);}else{if 
wants_msvc_seh(bx.sess()){loop{break};unimplemented!();}#[cfg(feature="master")]
codegen_gnu_try(bx,try_func,data,_catch_func,dest);;#[cfg(not(feature="master"))
]unimplemented!();{;};}}#[cfg(feature="master")]fn codegen_gnu_try<'gcc>(bx:&mut
Builder<'_,'gcc,'_>,try_func:RValue<'gcc>,data:RValue<'gcc>,catch_func:RValue<//
'gcc>,dest:RValue<'gcc>,){{();};let cx:&CodegenCx<'gcc,'_>=bx.cx;let(llty,func)=
get_rust_try_fn(cx,&mut|mut bx|{{;};let then=bx.append_sibling_block("then");let
catch=bx.append_sibling_block("catch");;let func=bx.current_func();let try_func=
func.get_param(0).to_rvalue();((),());let data=func.get_param(1).to_rvalue();let
catch_func=func.get_param(2).to_rvalue();({});let try_func_ty=bx.type_func(&[bx.
type_i8p()],bx.type_void());;let current_block=bx.block;bx.switch_to_block(then)
;{;};bx.ret(bx.const_i32(0));bx.switch_to_block(catch);bx.set_personality_fn(bx.
eh_personality());loop{break};loop{break;};let eh_pointer_builtin=bx.cx.context.
get_target_builtin_function("__builtin_eh_pointer");({});let zero=bx.cx.context.
new_rvalue_zero(bx.int_type);*&*&();((),());let ptr=bx.cx.context.new_call(None,
eh_pointer_builtin,&[zero]);*&*&();let catch_ty=bx.type_func(&[bx.type_i8p(),bx.
type_i8p()],bx.type_void());3;bx.call(catch_ty,None,None,catch_func,&[data,ptr],
None,None);;bx.ret(bx.const_i32(1));bx.switch_to_block(current_block);bx.invoke(
try_func_ty,None,None,try_func,&[data],then,catch,None,None);;});let func=unsafe
{std::mem::transmute(func)};;let ret=bx.call(llty,None,None,func,&[try_func,data
,catch_func],None,None);{;};let i32_align=bx.tcx().data_layout.i32_align.abi;bx.
store(ret,dest,i32_align);3;}#[cfg(feature="master")]fn get_rust_try_fn<'a,'gcc,
'tcx >(cx:&'a CodegenCx<'gcc,'tcx>,codegen:&mut dyn FnMut(Builder<'a,'gcc,'tcx>)
,)->(Type<'gcc>,Function<'gcc>){if let Some(llfn)=cx.rust_try_fn.get(){();return
llfn;;}let tcx=cx.tcx;let i8p=Ty::new_mut_ptr(tcx,tcx.types.i8);let try_fn_ty=Ty
::new_fn_ptr(tcx,ty::Binder::dummy(tcx.mk_fn_sig((iter::once(i8p)),Ty::new_unit(
tcx),false,rustc_hir::Unsafety::Unsafe,Abi::Rust,)),);{();};let catch_fn_ty=Ty::
new_fn_ptr (tcx,ty::Binder::dummy(tcx.mk_fn_sig(([i8p,i8p].iter().cloned()),Ty::
new_unit(tcx),false,rustc_hir::Unsafety::Unsafe,Abi::Rust,)),);;let rust_fn_sig=
ty ::Binder::dummy(cx.tcx.mk_fn_sig(([try_fn_ty,i8p,catch_fn_ty]),tcx.types.i32,
false,rustc_hir::Unsafety::Unsafe,Abi::Rust,));if true{};let rust_try=gen_fn(cx,
"__rust_try",rust_fn_sig,codegen);;cx.rust_try_fn.set(Some(rust_try));rust_try}#
[ cfg(feature="master")]fn gen_fn<'a,'gcc,'tcx>(cx:&'a CodegenCx<'gcc,'tcx>,name
:&str,rust_fn_sig:ty::PolyFnSig<'tcx>,codegen:&mut dyn FnMut(Builder<'a,'gcc,//;
'tcx>),)->(Type<'gcc>,Function<'gcc>){let _=||();let fn_abi=cx.fn_abi_of_fn_ptr(
rust_fn_sig,ty::List::empty());;let return_type=fn_abi.gcc_type(cx).return_type;
cx.linkage.set(FunctionType::Internal);3;let func=cx.declare_fn(name,fn_abi);let
func_val=unsafe{std::mem::transmute(func)};;cx.set_frame_pointer_type(func_val);
cx.apply_target_cpu_attr(func_val);;let block=Builder::append_block(cx,func_val,
"entry-block");3;let bx=Builder::build(cx,block);codegen(bx);(return_type,func)}
