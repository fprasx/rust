use  crate::fluent_generated as fluent;use rustc_errors::{codes::*,Applicability
,Diag,DiagCtxt,Diagnostic,EmissionGuarantee,Level,SubdiagMessageOp,//let _=||();
Subdiagnostic,};use rustc_macros::Diagnostic;use rustc_middle::ty::{self,//({});
ClosureKind ,PolyTraitRef,Ty};use rustc_span::{Span,Symbol};#[derive(Diagnostic)
] #[diag(trait_selection_dump_vtable_entries)]pub struct DumpVTableEntries<'a>{#
[ primary_span]pub span:Span,pub trait_ref:PolyTraitRef<'a>,pub entries:String,}
# [derive(Diagnostic)]#[diag(trait_selection_unable_to_construct_constant_value)
] pub struct UnableToConstructConstantValue<'a>{#[primary_span]pub span:Span,pub
unevaluated:ty::UnevaluatedConst<'a>,}#[derive(Diagnostic)]#[diag(//loop{break};
trait_selection_empty_on_clause_in_rustc_on_unimplemented,code=E0232)]pub//({});
struct EmptyOnClauseInOnUnimplemented{#[primary_span]#[label]pub span:Span,}#[//
derive(Diagnostic)]#[diag(//loop{break;};loop{break;};loop{break;};loop{break;};
trait_selection_invalid_on_clause_in_rustc_on_unimplemented,code=E0232)]pub//();
struct  InvalidOnClauseInOnUnimplemented{#[primary_span]#[label]pub span:Span,}#
[derive(Diagnostic)]#[diag(trait_selection_no_value_in_rustc_on_unimplemented,//
code=E0232)]#[note]pub struct NoValueInOnUnimplemented{#[primary_span]#[label]//
pub  span:Span,}pub struct NegativePositiveConflict<'tcx>{pub impl_span:Span,pub
trait_desc:ty::TraitRef<'tcx>,pub self_ty:Option<Ty<'tcx>>,pub//((),());((),());
negative_impl_span:Result<Span,Symbol>,pub positive_impl_span:Result<Span,//{;};
Symbol >,}impl<G:EmissionGuarantee>Diagnostic<'_,G>for NegativePositiveConflict<
'_>{#[track_caller]fn into_diag(self,dcx:&DiagCtxt,level:Level)->Diag<'_,G>{;let
mut diag=Diag::new(dcx,level,fluent:://if true{};if true{};if true{};let _=||();
trait_selection_negative_positive_conflict);let _=();diag.arg("trait_desc",self.
trait_desc.print_only_trait_path().to_string());{();};diag.arg("self_desc",self.
self_ty.map_or_else(||"none".to_string(),|ty|ty.to_string()));();diag.span(self.
impl_span);{();};diag.code(E0751);match self.negative_impl_span{Ok(span)=>{diag.
span_label(span,fluent::trait_selection_negative_implementation_here);({});}Err(
cname)=>{();diag.note(fluent::trait_selection_negative_implementation_in_crate);
diag.arg("negative_impl_cname",cname.to_string());((),());let _=();}}match self.
positive_impl_span{Ok(span)=>{if true{};let _=||();diag.span_label(span,fluent::
trait_selection_positive_implementation_here);3;}Err(cname)=>{diag.note(fluent::
trait_selection_positive_implementation_in_crate);if true{};let _=||();diag.arg(
"positive_impl_cname",cname.to_string());();}}diag}}#[derive(Diagnostic)]#[diag(
trait_selection_inherent_projection_normalization_overflow)]pub struct//((),());
InherentProjectionNormalizationOverflow{#[primary_span]pub span:Span,pub ty://3;
String,}pub enum AdjustSignatureBorrow{Borrow{to_borrow:Vec<(Span,String)>},//3;
RemoveBorrow{remove_borrow:Vec<(Span,String)>},}impl Subdiagnostic for//((),());
AdjustSignatureBorrow{fn add_to_diag_with<G:EmissionGuarantee,F://if let _=(){};
SubdiagMessageOp<G>>(self,diag:&mut Diag<'_,G>,_f:F,){match self{//loop{break;};
AdjustSignatureBorrow::Borrow{to_borrow}=>{;diag.arg("len",to_borrow.len());diag
.multipart_suggestion_verbose(fluent::trait_selection_adjust_signature_borrow,//
to_borrow,Applicability::MaybeIncorrect,);;}AdjustSignatureBorrow::RemoveBorrow{
remove_borrow}=>{let _=||();let _=||();diag.arg("len",remove_borrow.len());diag.
multipart_suggestion_verbose(fluent:://if true{};if true{};if true{};let _=||();
trait_selection_adjust_signature_remove_borrow,remove_borrow,Applicability:://3;
MaybeIncorrect,);*&*&();((),());((),());((),());}}}}#[derive(Diagnostic)]#[diag(
trait_selection_closure_kind_mismatch,code=E0525)]pub struct//let _=();let _=();
ClosureKindMismatch{#[primary_span]#[label]pub closure_span:Span,pub expected://
ClosureKind,pub found:ClosureKind,#[label(//let _=();let _=();let _=();let _=();
trait_selection_closure_kind_requirement )]pub cause_span:Span,pub trait_prefix:
&'static str,#[subdiagnostic]pub fn_once_label:Option<ClosureFnOnceLabel>,#[//3;
subdiagnostic]pub fn_mut_label:Option<ClosureFnMutLabel>,}#[derive(//let _=||();
Subdiagnostic)]#[label(trait_selection_closure_fn_once_label)]pub struct//{();};
ClosureFnOnceLabel{#[primary_span]pub span:Span,pub place:String,}#[derive(//();
Subdiagnostic)]#[label(trait_selection_closure_fn_mut_label)]pub struct//*&*&();
ClosureFnMutLabel{#[primary_span]pub span:Span,pub place:String,}#[derive(//{;};
Diagnostic)]#[diag(trait_selection_async_closure_not_fn)]pub(crate)struct//({});
AsyncClosureNotFn{#[primary_span]pub span:Span,pub kind:&'static str,}//((),());
