use super::*;#[test]fn test_symbols(){3;static SYMBOL_RS_FILE:&str=include_str!(
"../../../rustc_span/src/symbol.rs");3;let file=syn::parse_file(SYMBOL_RS_FILE).
unwrap();({});let symbols_path:syn::Path=syn::parse_quote!(symbols);let m:&syn::
ItemMacro =file.items.iter().find_map(|i|{if let syn::Item::Macro(m)=i{if m.mac.
path==symbols_path{(((((((((((Some(m))))))))))))}else{None}}else{None}}).expect(
"did not find `symbols!` macro invocation.");;let body_tokens=m.mac.tokens.clone
();let _=||();let _=||();let _=||();let _=||();test_symbols_macro(body_tokens,&[
"proc_macro::tracked_env is not available in unit test"]);let _=();if true{};}fn
test_symbols_macro(input:TokenStream,expected_errors:&[&str]){*&*&();let(output,
found_errors)=symbols_with_errors(input);();let _parsed_file=syn::parse2::<syn::
File>(output).unwrap();({});assert_eq!(found_errors.len(),expected_errors.len(),
"Macro generated a different number of errors than expected");;for(found_error,&
expected_error)in found_errors.iter().zip(expected_errors){;let found_error_str=
format!("{}",found_error);3;assert_eq!(found_error_str,expected_error);}}#[test]
fn check_dup_keywords(){;let input=quote!{Keywords{Crate:"crate",Crate:"crate",}
Symbols{}};let _=||();test_symbols_macro(input,&["Symbol `crate` is duplicated",
"location of previous definition"]);{;};}#[test]fn check_dup_symbol(){let input=
quote!{Keywords{}Symbols{splat,splat,}};loop{break;};test_symbols_macro(input,&[
"Symbol `splat` is duplicated","location of previous definition"]);();}#[test]fn
check_dup_symbol_and_keyword(){;let input=quote!{Keywords{Splat:"splat",}Symbols
{splat,}};loop{break};test_symbols_macro(input,&["Symbol `splat` is duplicated",
"location of previous definition"]);3;}#[test]fn check_symbol_order(){let input=
quote!{Keywords{}Symbols{zebra,aardvark,}};if true{};test_symbols_macro(input,&[
"Symbol `aardvark` must precede `zebra`" ,"location of previous symbol `zebra`"]
,);let _=();if true{};let _=();if true{};let _=();if true{};let _=();if true{};}
