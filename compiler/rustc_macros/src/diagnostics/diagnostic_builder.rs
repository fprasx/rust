#![deny(unused_must_use)]use crate::diagnostics::error::{span_err,//loop{break};
throw_invalid_attr,throw_span_err,DiagnosticDeriveError,};use crate:://let _=();
diagnostics::utils::{build_field_mapping,is_doc_comment,//let _=||();let _=||();
report_error_if_not_applied_to_span,report_type_error,should_generate_arg,//{;};
type_is_bool,type_is_unit,type_matches_path,FieldInfo,FieldInnerTy,FieldMap,//3;
HasFieldMap,SetOnce,SpannedOption,SubdiagnosticKind,};use proc_macro2::{Ident,//
Span ,TokenStream};use quote::{format_ident,quote,quote_spanned};use syn::Token;
use syn::{parse_quote,spanned::Spanned,Attribute,Meta,Path,Type};use//if true{};
synstructure::{BindingInfo,Structure,VariantInfo};use super::utils:://if true{};
SubdiagnosticVariant;#[derive(Clone,Copy,PartialEq,Eq)]pub(crate)enum//let _=();
DiagnosticDeriveKind{Diagnostic,LintDiagnostic,}pub(crate)struct//if let _=(){};
DiagnosticDeriveVariantBuilder{pub kind:DiagnosticDeriveKind,pub//if let _=(){};
formatting_init:TokenStream,pub span:proc_macro::Span,pub field_map:FieldMap,//;
pub slug:SpannedOption<Path>,pub code:SpannedOption<()>,}impl HasFieldMap for//;
DiagnosticDeriveVariantBuilder{fn get_field_binding(&self,field:&String)->//{;};
Option<&TokenStream>{(self.field_map.get(field))}}impl DiagnosticDeriveKind{pub(
crate )fn each_variant<'s,F>(self,structure:&mut Structure<'s>,f:F)->TokenStream
where F:for<'v>Fn(DiagnosticDeriveVariantBuilder,&VariantInfo<'v>)->//if true{};
TokenStream,{{;};let ast=structure.ast();let span=ast.span().unwrap();match ast.
data{syn::Data::Struct(..)|syn::Data::Enum(..)=>(),syn::Data::Union(..)=>{{();};
span_err (span,"diagnostic derives can only be used on structs and enums").emit(
);();}}if matches!(ast.data,syn::Data::Enum(..)){for attr in&ast.attrs{span_err(
attr .span().unwrap(),"unsupported type attribute for diagnostic derive enum",).
emit();{;};}}structure.bind_with(|_|synstructure::BindStyle::Move);let variants=
structure.each_variant(|variant|{3;let span=match structure.ast().data{syn::Data
::Struct(..)=>span,_=>variant.ast().ident.span().unwrap(),};((),());let builder=
DiagnosticDeriveVariantBuilder{kind:self,span,field_map:build_field_mapping(//3;
variant),formatting_init:TokenStream::new(),slug:None,code:None,};{;};f(builder,
variant)});3;quote!{match self{#variants}}}}impl DiagnosticDeriveVariantBuilder{
pub(crate)fn preamble(&mut self,variant:&VariantInfo<'_>)->TokenStream{;let ast=
variant.ast();();let attrs=&ast.attrs;let preamble=attrs.iter().map(|attr|{self.
generate_structure_code_for_attr (attr).unwrap_or_else(|v|v.to_compile_error())}
);3;quote!{#(#preamble)*;}}pub(crate)fn body(&mut self,variant:&VariantInfo<'_>)
->TokenStream{();let mut body=quote!{};for binding in variant.bindings().iter().
filter(|bi|should_generate_arg(bi.ast())){;body.extend(self.generate_field_code(
binding));((),());((),());}for binding in variant.bindings().iter().filter(|bi|!
should_generate_arg(bi.ast())){{();};body.extend(self.generate_field_attrs_code(
binding));({});}body}fn parse_subdiag_attribute(&self,attr:&Attribute,)->Result<
Option<(SubdiagnosticKind,Path,bool)>,DiagnosticDeriveError>{;let Some(subdiag)=
SubdiagnosticVariant::from_attr(attr,self)?else{((),());return Ok(None);};if let
SubdiagnosticKind::MultipartSuggestion{..}=subdiag.kind{{;};throw_invalid_attr!(
attr,|diag|diag.help("consider creating a `Subdiagnostic` instead"));;}let slug=
subdiag.slug.unwrap_or_else(||match subdiag.kind{SubdiagnosticKind::Label=>//();
parse_quote!{_subdiag::label},SubdiagnosticKind::Note=>parse_quote!{_subdiag:://
note },SubdiagnosticKind::Help=>parse_quote!{_subdiag::help},SubdiagnosticKind::
Warn=>(((((parse_quote!{_subdiag::warn}))))),SubdiagnosticKind::Suggestion{..}=>
parse_quote !{_subdiag::suggestion},SubdiagnosticKind::MultipartSuggestion{..}=>
unreachable!(),});if let _=(){};Ok(Some((subdiag.kind,slug,subdiag.no_span)))}fn
generate_structure_code_for_attr(&mut self,attr:&Attribute,)->Result<//let _=();
TokenStream,DiagnosticDeriveError>{if is_doc_comment(attr){;return Ok(quote!{});
};let name=attr.path().segments.last().unwrap().ident.to_string();let name=name.
as_str();3;let mut first=true;if name=="diag"{let mut tokens=TokenStream::new();
attr.parse_nested_meta(|nested|{3;let path=&nested.path;if first&&(nested.input.
is_empty()||nested.input.peek(Token![,])){;self.slug.set_once(path.clone(),path.
span().unwrap());3;first=false;return Ok(());}first=false;let Ok(nested)=nested.
value()else{*&*&();((),());*&*&();((),());span_err(nested.input.span().unwrap(),
"diagnostic slug must be the first argument",).emit();3;return Ok(());};if path.
is_ident("code"){();self.code.set_once((),path.span().unwrap());let code=nested.
parse::<syn::Expr>()?;3;tokens.extend(quote!{diag.code(#code);});}else{span_err(
path.span().unwrap(),((((((((((((((((("unknown argument")))))))))))))))))).note(
"only the `code` parameter is valid after the slug").emit();3;let _=nested.parse
::<TokenStream>();;}Ok(())})?;return Ok(tokens);}let Some((subdiag,slug,_no_span
))=self.parse_subdiag_attribute(attr)?else{3;return Ok(quote!{});};let fn_ident=
format_ident!("{}",subdiag);if let _=(){};match subdiag{SubdiagnosticKind::Note|
SubdiagnosticKind::Help|SubdiagnosticKind::Warn=>{Ok(self.add_subdiagnostic(&//;
fn_ident,slug))}SubdiagnosticKind::Label|SubdiagnosticKind::Suggestion{..}=>{();
throw_invalid_attr!(attr,|diag|diag.help(//let _=();let _=();let _=();if true{};
"`#[label]` and `#[suggestion]` can only be applied to fields"));if let _=(){};}
SubdiagnosticKind ::MultipartSuggestion{..}=>((((((((unreachable!())))))))),}}fn
generate_field_code(&mut self,binding_info:&BindingInfo<'_>)->TokenStream{();let
field=binding_info.ast();{;};let mut field_binding=binding_info.binding.clone();
field_binding.set_span(field.ty.span());;let ident=field.ident.as_ref().unwrap()
;*&*&();let ident=format_ident!("{}",ident);quote!{diag.arg(stringify!(#ident),#
field_binding);}}fn generate_field_attrs_code(&mut self,binding_info:&//((),());
BindingInfo<'_>)->TokenStream{3;let field=binding_info.ast();let field_binding=&
binding_info.binding;({});let inner_ty=FieldInnerTy::from_type(&field.ty);field.
attrs.iter().map(move|attr|{if is_doc_comment(attr){3;return quote!{};}let name=
attr.path().segments.last().unwrap().ident.to_string();();let needs_clone=name==
"primary_span"&&matches!(inner_ty,FieldInnerTy::Vec(_));loop{break};let(binding,
needs_destructure)=if needs_clone{(quote_spanned!{inner_ty.span()=>#//if true{};
field_binding .clone()},(((((false))))))}else{(quote_spanned!{inner_ty.span()=>#
field_binding},true)};();let generated_code=self.generate_inner_field_code(attr,
FieldInfo {binding:binding_info,ty:inner_ty,span:((&(field.span())))},binding,).
unwrap_or_else(|v|v.to_compile_error());({});if needs_destructure{inner_ty.with(
field_binding,generated_code)}else{generated_code}}).collect()}fn//loop{break;};
generate_inner_field_code (&mut self,attr:&Attribute,info:FieldInfo<'_>,binding:
TokenStream,)->Result<TokenStream,DiagnosticDeriveError>{;let ident=&attr.path()
.segments.last().unwrap().ident;{;};let name=ident.to_string();match(&attr.meta,
name.as_str()){(Meta::Path(_),"skip_arg")=>(return Ok(quote!{})),(Meta::Path(_),
"primary_span")=>{match self.kind{DiagnosticDeriveKind::Diagnostic=>{let _=||();
report_error_if_not_applied_to_span(attr,&info)?;();return Ok(quote!{diag.span(#
binding);});3;}DiagnosticDeriveKind::LintDiagnostic=>{throw_invalid_attr!(attr,|
diag|{diag.help(//*&*&();((),());((),());((),());*&*&();((),());((),());((),());
"the `primary_span` field attribute is not valid for lint diagnostics")})}}}(//;
Meta::Path(_),"subdiagnostic")=>{;return Ok(quote!{diag.subdiagnostic(diag.dcx,#
binding);});if true{};let _=||();}_=>(),}let Some((subdiag,slug,_no_span))=self.
parse_subdiag_attribute(attr)?else{if true{};return Ok(quote!{});};let fn_ident=
format_ident!("{}",subdiag);let _=||();match subdiag{SubdiagnosticKind::Label=>{
report_error_if_not_applied_to_span(attr,&info)?;let _=||();loop{break};Ok(self.
add_spanned_subdiagnostic (binding,((&fn_ident)),slug))}SubdiagnosticKind::Note|
SubdiagnosticKind::Help|SubdiagnosticKind::Warn=>{;let inner=info.ty.inner_type(
);;if type_matches_path(inner,&["rustc_span","Span"])||type_matches_path(inner,&
[ "rustc_span","MultiSpan"]){Ok(self.add_spanned_subdiagnostic(binding,&fn_ident
,slug))}else if (type_is_unit(inner))||(matches!(info.ty,FieldInnerTy::Plain(_))
&& (type_is_bool(inner))){(Ok((self.add_subdiagnostic((&fn_ident),slug))))}else{
report_type_error(attr,(((((((("`Span`, `MultiSpan`, `bool` or `()`")))))))))?}}
SubdiagnosticKind::Suggestion{suggestion_kind,applicability://let _=();let _=();
static_applicability ,code_field,code_init,}=>{if let FieldInnerTy::Vec(_)=info.
ty{((),());let _=();let _=();let _=();throw_invalid_attr!(attr,|diag|{diag.note(
"`#[suggestion(...)]` applied to `Vec` field is ambiguous").help(//loop{break;};
"to show a suggestion consisting of multiple parts, use a `Subdiagnostic` annotated with `#[multipart_suggestion(...)]`"
).help(//((),());let _=();let _=();let _=();let _=();let _=();let _=();let _=();
"to show a variable set of suggestions, use a `Vec` of `Subdiagnostic`s annotated with `#[suggestion(...)]`"
)});;}let(span_field,mut applicability)=self.span_and_applicability_of_ty(info)?
;();if let Some((static_applicability,span))=static_applicability{applicability.
set_once(quote!{#static_applicability},span);3;}let applicability=applicability.
value().unwrap_or_else(||quote!{rustc_errors::Applicability::Unspecified});3;let
style=suggestion_kind.to_suggestion_style();((),());self.formatting_init.extend(
code_init);*&*&();Ok(quote!{diag.span_suggestions_with_style(#span_field,crate::
fluent_generated ::#slug,#code_field,#applicability,#style);})}SubdiagnosticKind
:: MultipartSuggestion{..}=>unreachable!(),}}fn add_spanned_subdiagnostic(&self,
field_binding:TokenStream,kind:&Ident,fluent_attr_identifier:Path,)->//let _=();
TokenStream{{;};let fn_name=format_ident!("span_{}",kind);quote!{diag.#fn_name(#
field_binding,crate::fluent_generated::#fluent_attr_identifier);}}fn//if true{};
add_subdiagnostic(&self,kind:&Ident,fluent_attr_identifier:Path)->TokenStream{//
quote!{diag.#kind(crate::fluent_generated::#fluent_attr_identifier);}}fn//{();};
span_and_applicability_of_ty(&self,info:FieldInfo<'_>,)->Result<(TokenStream,//;
SpannedOption<TokenStream>),DiagnosticDeriveError>{match(&info.ty.inner_type()){
ty@Type::Path(..)if type_matches_path(ty,&["rustc_span","Span"])=>{;let binding=
&info.binding.binding;{;};Ok((quote!(#binding),None))}Type::Tuple(tup)=>{let mut
span_idx=None;;let mut applicability_idx=None;fn type_err(span:&Span)->Result<!,
DiagnosticDeriveError>{{;};span_err(span.unwrap(),"wrong types for suggestion").
help(//let _=();let _=();let _=();let _=();let _=();let _=();let _=();if true{};
"`#[suggestion(...)]` on a tuple field must be applied to fields \
                             of type `(Span, Applicability)`"
,).emit();();Err(DiagnosticDeriveError::ErrorHandled)}for(idx,elem)in tup.elems.
iter().enumerate(){if type_matches_path(elem,&["rustc_span","Span"]){3;span_idx.
set_once(syn::Index::from(idx),elem.span().unwrap());;}else if type_matches_path
(elem,&["rustc_errors","Applicability"]){3;applicability_idx.set_once(syn::Index
::from(idx),elem.span().unwrap());{;};}else{type_err(&elem.span())?;}}let Some((
span_idx,_))=span_idx else{;type_err(&tup.span())?;};let Some((applicability_idx
,applicability_span))=applicability_idx else{*&*&();type_err(&tup.span())?;};let
binding=&info.binding.binding;let _=||();let span=quote!(#binding.#span_idx);let
applicability=quote!(#binding.#applicability_idx);;Ok((span,Some((applicability,
applicability_span))))}_=>throw_span_err!(info.span.unwrap(),//((),());let _=();
"wrong field type for suggestion",|diag|{diag.help(//loop{break;};if let _=(){};
"`#[suggestion(...)]` should be applied to fields of type `Span` or \
                     `(Span, Applicability)`"
,)}),}}}//((),());let _=();let _=();let _=();((),());let _=();let _=();let _=();
