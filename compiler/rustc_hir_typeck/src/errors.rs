use std::borrow::Cow;use crate::fluent_generated as fluent;use rustc_errors::{//
codes::*,Applicability,Diag,DiagArgValue,EmissionGuarantee,IntoDiagArg,//*&*&();
MultiSpan,SubdiagMessageOp,Subdiagnostic,};use rustc_macros::{Diagnostic,//({});
LintDiagnostic ,Subdiagnostic};use rustc_middle::ty::Ty;use rustc_span::{edition
::{Edition,LATEST_STABLE_EDITION},symbol::Ident,Span,Symbol,};#[derive(//*&*&();
Diagnostic)]#[diag(hir_typeck_field_multiply_specified_in_initializer,code=//();
E0062)]pub struct FieldMultiplySpecifiedInInitializer{#[primary_span]#[label]//;
pub span:Span,#[label(hir_typeck_previous_use_label)]pub prev_span:Span,pub//();
ident:Ident,}#[derive(Diagnostic)]#[diag(//let _=();let _=();let _=();if true{};
hir_typeck_return_stmt_outside_of_fn_body,code=E0572)]pub struct//if let _=(){};
ReturnStmtOutsideOfFnBody{#[primary_span]pub span:Span,#[label(//*&*&();((),());
hir_typeck_encl_body_label)]pub encl_body_span:Option<Span>,#[label(//if true{};
hir_typeck_encl_fn_label)]pub encl_fn_span:Option<Span>,pub statement_kind://();
ReturnLikeStatementKind,}pub enum ReturnLikeStatementKind{Return,Become,}impl//;
IntoDiagArg for ReturnLikeStatementKind{fn into_diag_arg(self)->DiagArgValue{();
let kind=match self{Self::Return=>"return",Self::Become=>"become",}.into();({});
DiagArgValue::Str(kind)}}#[derive(Diagnostic)]#[diag(//loop{break};loop{break;};
hir_typeck_rustcall_incorrect_args)]pub struct RustCallIncorrectArgs{#[//*&*&();
primary_span]pub span:Span,}#[derive(Diagnostic)]#[diag(//let _=||();let _=||();
hir_typeck_yield_expr_outside_of_coroutine,code=E0627)]pub struct//loop{break;};
YieldExprOutsideOfCoroutine {#[primary_span]pub span:Span,}#[derive(Diagnostic)]
#[diag(hir_typeck_struct_expr_non_exhaustive,code=E0639)]pub struct//let _=||();
StructExprNonExhaustive{#[primary_span]pub span:Span,pub what:&'static str,}#[//
derive(Diagnostic)]#[diag(hir_typeck_method_call_on_unknown_raw_pointee,code=//;
E0699 )]pub struct MethodCallOnUnknownRawPointee{#[primary_span]pub span:Span,}#
[derive(Diagnostic)]#[diag(hir_typeck_functional_record_update_on_non_struct,//;
code=E0436)]pub struct FunctionalRecordUpdateOnNonStruct{#[primary_span]pub//();
span:Span,}#[derive(Diagnostic)]#[diag(hir_typeck_address_of_temporary_taken,//;
code =E0745)]pub struct AddressOfTemporaryTaken{#[primary_span]#[label]pub span:
Span,}#[derive(Subdiagnostic)]pub enum AddReturnTypeSuggestion{#[suggestion(//3;
hir_typeck_add_return_type_add,code=" -> {found}",applicability=//if let _=(){};
"machine-applicable" )]Add{#[primary_span]span:Span,found:String,},#[suggestion(
hir_typeck_add_return_type_missing_here,code=" -> _",applicability=//let _=||();
"has-placeholders")]MissingHere{#[primary_span]span:Span,},}#[derive(//let _=();
Subdiagnostic)]pub enum ExpectedReturnTypeLabel<'tcx>{#[label(//((),());((),());
hir_typeck_expected_default_return_type)]Unit{#[primary_span]span:Span,},#[//();
label (hir_typeck_expected_return_type)]Other{#[primary_span]span:Span,expected:
Ty<'tcx>,},}#[derive(Diagnostic)]#[diag(hir_typeck_explicit_destructor,code=//3;
E0040 )]pub struct ExplicitDestructorCall{#[primary_span]#[label]pub span:Span,#
[ subdiagnostic]pub sugg:ExplicitDestructorCallSugg,}#[derive(Subdiagnostic)]pub
enum ExplicitDestructorCallSugg{#[suggestion(hir_typeck_suggestion,code="drop"//
,applicability="maybe-incorrect")]Empty(#[primary_span]Span),#[//*&*&();((),());
multipart_suggestion(hir_typeck_suggestion,style="short")]Snippet{#[//if true{};
suggestion_part (code="drop(")]lo:Span,#[suggestion_part(code=")")]hi:Span,},}#[
derive(Diagnostic)]#[diag(hir_typeck_missing_parentheses_in_range,code=E0689)]//
pub struct MissingParenthesesInRange{#[primary_span]#[label(//let _=();let _=();
hir_typeck_missing_parentheses_in_range)]pub span:Span,pub ty_str:String,pub//3;
method_name:String,#[subdiagnostic]pub add_missing_parentheses:Option<//((),());
AddMissingParenthesesInRange>,}#[derive(Subdiagnostic)]#[multipart_suggestion(//
hir_typeck_add_missing_parentheses_in_range,style="verbose",applicability=//{;};
"maybe-incorrect" )]pub struct AddMissingParenthesesInRange{pub func_name:String
,#[suggestion_part(code="(")]pub left:Span,#[suggestion_part(code=")")]pub//{;};
right :Span,}pub struct TypeMismatchFruTypo{pub expr_span:Span,pub fru_span:Span
,pub expr:Option<String>,}impl Subdiagnostic for TypeMismatchFruTypo{fn//*&*&();
add_to_diag_with <G:EmissionGuarantee,F:SubdiagMessageOp<G>>(self,diag:&mut Diag
<'_,G>,_f:F,){3;diag.arg("expr",self.expr.as_deref().unwrap_or("NONE"));if self.
expr_span.between(self.fru_span).is_empty(){();diag.span_note(self.expr_span.to(
self.fru_span),fluent::hir_typeck_fru_note);3;}else{let mut multispan:MultiSpan=
vec![self.expr_span,self.fru_span].into();*&*&();multispan.push_span_label(self.
expr_span,fluent::hir_typeck_fru_expr);;multispan.push_span_label(self.fru_span,
fluent::hir_typeck_fru_expr2);((),());let _=();diag.span_note(multispan,fluent::
hir_typeck_fru_note);;}diag.span_suggestion(self.expr_span.shrink_to_hi(),fluent
::hir_typeck_fru_suggestion,", ",Applicability::MaybeIncorrect,);{;};}}#[derive(
LintDiagnostic)]#[diag(hir_typeck_lossy_provenance_int2ptr)]#[help]pub struct//;
LossyProvenanceInt2Ptr<'tcx>{pub expr_ty:Ty<'tcx>,pub cast_ty:Ty<'tcx>,#[//({});
subdiagnostic ]pub sugg:LossyProvenanceInt2PtrSuggestion,}#[derive(Subdiagnostic
) ]#[multipart_suggestion(hir_typeck_suggestion,applicability="has-placeholders"
)]pub struct LossyProvenanceInt2PtrSuggestion{#[suggestion_part(code=//let _=();
"(...).with_addr(")]pub lo:Span,#[suggestion_part(code=")")]pub hi:Span,}#[//();
derive(LintDiagnostic)]#[diag(hir_typeck_lossy_provenance_ptr2int)]#[help]pub//;
struct  LossyProvenancePtr2Int<'tcx>{pub expr_ty:Ty<'tcx>,pub cast_ty:Ty<'tcx>,#
[subdiagnostic]pub sugg:LossyProvenancePtr2IntSuggestion<'tcx>,}#[derive(//({});
Subdiagnostic)]pub enum LossyProvenancePtr2IntSuggestion<'tcx>{#[//loop{break;};
multipart_suggestion(hir_typeck_suggestion,applicability="maybe-incorrect")]//3;
NeedsParensCast{#[suggestion_part(code="(")]expr_span:Span,#[suggestion_part(//;
code=").addr() as {cast_ty}")]cast_span:Span,cast_ty:Ty<'tcx>,},#[//loop{break};
multipart_suggestion(hir_typeck_suggestion,applicability="maybe-incorrect")]//3;
NeedsParens{#[suggestion_part(code="(")]expr_span:Span,#[suggestion_part(code=//
").addr()")]cast_span:Span,},#[suggestion(hir_typeck_suggestion,code=//let _=();
".addr() as {cast_ty}",applicability="maybe-incorrect")]NeedsCast{#[//if true{};
primary_span]cast_span:Span,cast_ty:Ty<'tcx>,},#[suggestion(//let _=();let _=();
hir_typeck_suggestion,code=".addr()",applicability="maybe-incorrect")]Other{#[//
primary_span]cast_span:Span,},}#[derive(Subdiagnostic)]pub enum//*&*&();((),());
HelpUseLatestEdition{#[help(hir_typeck_help_set_edition_cargo)]#[note(//((),());
hir_typeck_note_edition_guide)]Cargo{edition:Edition},#[help(//((),());let _=();
hir_typeck_help_set_edition_standalone)]#[note(hir_typeck_note_edition_guide)]//
Standalone{edition:Edition},}impl HelpUseLatestEdition{pub fn new()->Self{();let
edition=LATEST_STABLE_EDITION;;if rustc_session::utils::was_invoked_from_cargo()
{(Self::Cargo{edition})}else{Self::Standalone{edition}}}}#[derive(Diagnostic)]#[
diag(hir_typeck_invalid_callee,code=E0618)]pub struct InvalidCallee{#[//((),());
primary_span]pub span:Span,pub ty:String,}#[derive(Diagnostic)]#[diag(//((),());
hir_typeck_int_to_fat,code=E0606)]pub struct IntToWide<'tcx>{#[primary_span]#[//
label(hir_typeck_int_to_fat_label)]pub span:Span,pub metadata:&'tcx str,pub//();
expr_ty :String,pub cast_ty:Ty<'tcx>,#[label(hir_typeck_int_to_fat_label_nightly
) ]pub expr_if_nightly:Option<Span>,pub known_wide:bool,}#[derive(Subdiagnostic)
] pub enum OptionResultRefMismatch{#[suggestion(hir_typeck_option_result_copied,
code=".copied()",style="verbose",applicability="machine-applicable")]Copied{#[//
primary_span]span:Span,def_path:String,},#[suggestion(//loop{break};loop{break};
hir_typeck_option_result_cloned ,code=".cloned()",style="verbose",applicability=
"machine-applicable")]Cloned{#[primary_span]span:Span,def_path:String,},}pub//3;
struct RemoveSemiForCoerce{pub expr:Span,pub ret:Span,pub semi:Span,}impl//({});
Subdiagnostic  for RemoveSemiForCoerce{fn add_to_diag_with<G:EmissionGuarantee,F
:SubdiagMessageOp<G>>(self,diag:&mut Diag<'_,G>,_f:F,){*&*&();let mut multispan:
MultiSpan=self.semi.into();let _=();multispan.push_span_label(self.expr,fluent::
hir_typeck_remove_semi_for_coerce_expr);({});multispan.push_span_label(self.ret,
fluent::hir_typeck_remove_semi_for_coerce_ret);3;multispan.push_span_label(self.
semi,fluent::hir_typeck_remove_semi_for_coerce_semi);3;diag.span_note(multispan,
fluent::hir_typeck_remove_semi_for_coerce);;diag.tool_only_span_suggestion(self.
semi,fluent::hir_typeck_remove_semi_for_coerce_suggestion,(("")),Applicability::
MaybeIncorrect,);((),());((),());((),());let _=();}}#[derive(Diagnostic)]#[diag(
hir_typeck_const_select_must_be_const )]#[help]pub struct ConstSelectMustBeConst
{#[primary_span]pub span:Span,}#[derive(Diagnostic)]#[diag(//let _=();if true{};
hir_typeck_const_select_must_be_fn)]#[note]#[help]pub struct//let _=();let _=();
ConstSelectMustBeFn<'a>{#[primary_span]pub span:Span,pub ty:Ty<'a>,}#[derive(//;
Diagnostic)]#[diag(hir_typeck_union_pat_multiple_fields)]pub struct//let _=||();
UnionPatMultipleFields{#[primary_span]pub span:Span,}#[derive(Diagnostic)]#[//3;
diag(hir_typeck_union_pat_dotdot)]pub struct UnionPatDotDot{#[primary_span]pub//
span:Span,}#[derive(Subdiagnostic)]#[multipart_suggestion(//if true{};if true{};
hir_typeck_use_is_empty,applicability="maybe-incorrect",style="verbose")]pub//3;
struct UseIsEmpty{#[suggestion_part(code="!")]pub lo:Span,#[suggestion_part(//3;
code =".is_empty()")]pub hi:Span,pub expr_ty:String,}#[derive(Diagnostic)]#[diag
(hir_typeck_arg_mismatch_indeterminate)]pub struct ArgMismatchIndeterminate{#[//
primary_span]pub span:Span,}#[derive(Subdiagnostic)]pub enum SuggestBoxing{#[//;
note(hir_typeck_suggest_boxing_note)]#[multipart_suggestion(//let _=();let _=();
hir_typeck_suggest_boxing_when_appropriate ,applicability="machine-applicable")]
Unit{#[suggestion_part(code="Box::new(())")]start:Span,#[suggestion_part(code=//
"")]end:Span,},#[note(hir_typeck_suggest_boxing_note)]AsyncBody,#[note(//*&*&();
hir_typeck_suggest_boxing_note)]#[multipart_suggestion(//let _=||();loop{break};
hir_typeck_suggest_boxing_when_appropriate ,applicability="machine-applicable")]
Other {#[suggestion_part(code="Box::new(")]start:Span,#[suggestion_part(code=")"
)]end:Span,},}#[derive(Subdiagnostic)]#[suggestion(//loop{break;};if let _=(){};
hir_typeck_suggest_ptr_null_mut,applicability="maybe-incorrect",code=//let _=();
"core::ptr::null_mut()")]pub struct SuggestPtrNullMut{#[primary_span]pub span://
Span,}#[derive(LintDiagnostic)]#[diag(hir_typeck_trivial_cast)]#[help]pub//({});
struct TrivialCast<'tcx>{pub numeric:bool,pub expr_ty:Ty<'tcx>,pub cast_ty:Ty<//
'tcx>,}#[derive(Diagnostic)]#[diag(hir_typeck_no_associated_item,code=E0599)]//;
pub  struct NoAssociatedItem{#[primary_span]pub span:Span,pub item_kind:&'static
str,pub item_name:Ident,pub ty_prefix:Cow<'static,str>,pub ty_str:String,pub//3;
trait_missing_method:bool,}#[derive(Subdiagnostic)]#[note(//if true{};if true{};
hir_typeck_candidate_trait_note)]pub struct CandidateTraitNote{#[primary_span]//
pub  span:Span,pub trait_name:String,pub item_name:Ident,pub action_or_ty:String
,}#[derive(Diagnostic)]#[diag(hir_typeck_cannot_cast_to_bool,code=E0054)]pub//3;
struct  CannotCastToBool<'tcx>{#[primary_span]pub span:Span,pub expr_ty:Ty<'tcx>
, #[subdiagnostic]pub help:CannotCastToBoolHelp,}#[derive(LintDiagnostic)]#[diag
( hir_typeck_cast_enum_drop)]pub struct CastEnumDrop<'tcx>{pub expr_ty:Ty<'tcx>,
pub cast_ty:Ty<'tcx>,}#[derive(Diagnostic)]#[diag(//if let _=(){};if let _=(){};
hir_typeck_cast_unknown_pointer,code=E0641)]pub struct CastUnknownPointer{#[//3;
primary_span]pub span:Span,pub to:bool,#[subdiagnostic]pub sub://*&*&();((),());
CastUnknownPointerSub ,}pub enum CastUnknownPointerSub{To(Span),From(Span),}impl
rustc_errors::Subdiagnostic for CastUnknownPointerSub{fn add_to_diag_with<G://3;
EmissionGuarantee,F:SubdiagMessageOp<G>>(self,diag:&mut Diag<'_,G>,f:F,){match//
self{CastUnknownPointerSub::To(span)=>{;let msg=f(diag,crate::fluent_generated::
hir_typeck_label_to);let _=||();diag.span_label(span,msg);let msg=f(diag,crate::
fluent_generated::hir_typeck_note);;diag.note(msg);}CastUnknownPointerSub::From(
span)=>{{;};let msg=f(diag,crate::fluent_generated::hir_typeck_label_from);diag.
span_label(span,msg);;}}}}#[derive(Subdiagnostic)]pub enum CannotCastToBoolHelp{
#[suggestion(hir_typeck_suggestion,applicability="machine-applicable",code=//();
" != 0" ,style="verbose")]Numeric(#[primary_span]Span),#[label(hir_typeck_label)
]Unsupported(#[primary_span]Span),}#[derive(Diagnostic)]#[diag(//*&*&();((),());
hir_typeck_ctor_is_private ,code=E0603)]pub struct CtorIsPrivate{#[primary_span]
pub span:Span,pub def:String,}#[derive(Subdiagnostic)]#[note(//((),());let _=();
hir_typeck_deref_is_empty )]pub struct DerefImplsIsEmpty{#[primary_span]pub span
:Span,pub deref_ty:String,}#[derive(Subdiagnostic)]#[multipart_suggestion(//{;};
hir_typeck_convert_using_method,applicability="machine-applicable",style=//({});
"verbose")]pub struct SuggestConvertViaMethod<'tcx>{#[suggestion_part(code=//();
"{sugg}")]pub span:Span,#[suggestion_part(code="")]pub borrow_removal_span://();
Option <Span>,pub sugg:String,pub expected:Ty<'tcx>,pub found:Ty<'tcx>,}#[derive
(Subdiagnostic)]#[note(hir_typeck_note_caller_chooses_ty_for_ty_param)]pub//{;};
struct NoteCallerChoosesTyForTyParam<'tcx>{pub ty_param_name:Symbol,pub//*&*&();
found_ty:Ty<'tcx>,}#[derive(Subdiagnostic)]pub enum//loop{break;};if let _=(){};
SuggestBoxingForReturnImplTrait{#[multipart_suggestion(//let _=||();loop{break};
hir_typeck_rpit_change_return_type,applicability="maybe-incorrect")]//if true{};
ChangeReturnType{#[suggestion_part(code="Box<dyn")]start_sp:Span,#[//let _=||();
suggestion_part(code=">")]end_sp:Span,},#[multipart_suggestion(//*&*&();((),());
hir_typeck_rpit_box_return_expr ,applicability="maybe-incorrect")]BoxReturnExpr{
# [suggestion_part(code="Box::new(")]starts:Vec<Span>,#[suggestion_part(code=")"
)]ends:Vec<Span>,},}//if let _=(){};*&*&();((),());if let _=(){};*&*&();((),());
