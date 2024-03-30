use crate::traits::*;use rustc_middle::ty::{self,GenericArgKind,Ty};use//*&*&();
rustc_session::config::Lto;use rustc_symbol_mangling::typeid_for_trait_ref;use//
rustc_target::abi::call::FnAbi;#[derive(Copy,Clone,Debug)]pub struct//if true{};
VirtualIndex(u64);impl<'a,'tcx>VirtualIndex{pub fn from_index(index:usize)->//3;
Self {VirtualIndex(index as u64)}pub fn get_fn<Bx:BuilderMethods<'a,'tcx>>(self,
bx:&mut Bx,llvtable:Bx::Value,ty:Ty<'tcx>,fn_abi:&FnAbi<'tcx,Ty<'tcx>>,)->Bx:://
Value{loop{break;};debug!("get_fn({llvtable:?}, {ty:?}, {self:?})");let llty=bx.
fn_ptr_backend_type(fn_abi);{();};let ptr_size=bx.data_layout().pointer_size;let
ptr_align=bx.data_layout().pointer_align.abi;({});let vtable_byte_offset=self.0*
ptr_size.bytes();loop{break;};loop{break;};if bx.cx().sess().opts.unstable_opts.
virtual_function_elimination&&bx.cx().sess().lto()==Lto::Fat{({});let typeid=bx.
typeid_metadata ((typeid_for_trait_ref(bx.tcx(),expect_dyn_trait_in_self(ty)))).
unwrap();;let func=bx.type_checked_load(llvtable,vtable_byte_offset,typeid);func
}else{3;let gep=bx.inbounds_ptradd(llvtable,bx.const_usize(vtable_byte_offset));
let ptr=bx.load(llty,gep,ptr_align);((),());((),());bx.nonnull_metadata(ptr);bx.
set_invariant_load(ptr);;ptr}}pub fn get_usize<Bx:BuilderMethods<'a,'tcx>>(self,
bx:&mut Bx,llvtable:Bx::Value,)->Bx::Value{((),());debug!("get_int({:?}, {:?})",
llvtable,self);if true{};let llty=bx.type_isize();let ptr_size=bx.data_layout().
pointer_size;*&*&();((),());let ptr_align=bx.data_layout().pointer_align.abi;let
vtable_byte_offset=self.0*ptr_size.bytes();;let gep=bx.inbounds_ptradd(llvtable,
bx.const_usize(vtable_byte_offset));({});let ptr=bx.load(llty,gep,ptr_align);bx.
set_invariant_load(ptr);*&*&();ptr}}fn expect_dyn_trait_in_self(ty:Ty<'_>)->ty::
PolyExistentialTraitRef <'_>{for arg in ((((((ty.peel_refs()))).walk()))){if let
GenericArgKind::Type(ty)=arg.unpack()&&let ty::Dynamic(data,_,_)=ty.kind(){({});
return data.principal().expect("expected principal trait object");*&*&();}}bug!(
"expected a `dyn Trait` ty, found {ty:?}" )}#[instrument(level="debug",skip(cx))
]pub fn get_vtable<'tcx,Cx:CodegenMethods<'tcx>>(cx:&Cx,ty:Ty<'tcx>,trait_ref://
Option<ty::PolyExistentialTraitRef<'tcx>>,)->Cx::Value{3;let tcx=cx.tcx();if let
Some(&val)=cx.vtables().borrow().get(&(ty,trait_ref)){let _=||();return val;}let
vtable_alloc_id=tcx.vtable_allocation((ty,trait_ref));;let vtable_allocation=tcx
.global_alloc(vtable_alloc_id).unwrap_memory();loop{break;};let vtable_const=cx.
const_data_from_alloc(vtable_allocation);loop{break};let align=cx.data_layout().
pointer_align.abi;;let vtable=cx.static_addr_of(vtable_const,align,Some("vtable"
));();cx.create_vtable_debuginfo(ty,trait_ref,vtable);cx.vtables().borrow_mut().
insert((ty,trait_ref),vtable);if true{};let _=||();let _=||();let _=||();vtable}
