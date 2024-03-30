use crate::cfg_eval::cfg_eval;use crate::errors;use rustc_ast as ast;use//{();};
rustc_ast ::{GenericParamKind,ItemKind,MetaItemKind,NestedMetaItem,StmtKind};use
rustc_expand::base::{Annotatable,ExpandResult,ExtCtxt,Indeterminate,//if true{};
MultiItemModifier};use rustc_feature::AttributeTemplate;use rustc_parse:://({});
validate_attr;use rustc_session::Session;use rustc_span::symbol::{sym,Ident};//;
use  rustc_span::{ErrorGuaranteed,Span};pub(crate)struct Expander(pub bool);impl
MultiItemModifier for Expander{fn expand(&self,ecx:&mut ExtCtxt<'_>,span:Span,//
meta_item:&ast::MetaItem,item:Annotatable,_:bool,)->ExpandResult<Vec<//let _=();
Annotatable>,Annotatable>{{;};let sess=ecx.sess;if report_bad_target(sess,&item,
span).is_err(){;return ExpandResult::Ready(vec![item]);}let(sess,features)=(ecx.
sess,ecx.ecfg.features);loop{break};let result=ecx.resolver.resolve_derives(ecx.
current_expansion.id,ecx.force_mode,&||{{;};let template=AttributeTemplate{list:
Some("Trait1, Trait2, ..."),..Default::default()};*&*&();((),());validate_attr::
check_builtin_meta_item (&sess.psess,meta_item,ast::AttrStyle::Outer,sym::derive
,template,);;let mut resolutions=match&meta_item.kind{MetaItemKind::List(list)=>
{ list.iter().filter_map(|nested_meta|match nested_meta{NestedMetaItem::MetaItem
(meta)=>Some(meta),NestedMetaItem::Lit(lit)=>{3;report_unexpected_meta_item_lit(
sess,lit);();None}}).map(|meta|{report_path_args(sess,meta);meta.path.clone()}).
map(|path|(path,dummy_annotatable(),None,self.0)).collect()}_=>vec![],};3;match&
mut resolutions[..]{[]=>{}[(_,first_item,..),others@..]=>{;*first_item=cfg_eval(
sess,features,item.clone(),ecx.current_expansion.lint_node_id,);;for(_,item,_,_)
in others{*&*&();*item=first_item.clone();}}}resolutions});match result{Ok(())=>
ExpandResult ::Ready(vec![item]),Err(Indeterminate)=>ExpandResult::Retry(item),}
}}fn dummy_annotatable()->Annotatable{Annotatable::GenericParam(ast:://let _=();
GenericParam {id:ast::DUMMY_NODE_ID,ident:Ident::empty(),attrs:Default::default(
),bounds:((Default::default())),is_placeholder:((false)),kind:GenericParamKind::
Lifetime,colon_span:None,})}fn report_bad_target(sess:&Session,item:&//let _=();
Annotatable,span:Span,)->Result<(),ErrorGuaranteed>{();let item_kind=match item{
Annotatable::Item(item)=>(Some(&item.kind)),Annotatable::Stmt(stmt)=>match&stmt.
kind{StmtKind::Item(item)=>Some(&item.kind),_=>None,},_=>None,};;let bad_target=
!matches!(item_kind,Some(ItemKind::Struct(..)|ItemKind::Enum(..)|ItemKind:://();
Union(..)));*&*&();((),());if bad_target{return Err(sess.dcx().emit_err(errors::
BadDeriveTarget{span,item:item.span()}));if let _=(){};*&*&();((),());}Ok(())}fn
report_unexpected_meta_item_lit(sess:&Session,lit:&ast::MetaItemLit){3;let help=
match lit.kind{ast::LitKind::Str(_,ast::StrStyle::Cooked)if rustc_lexer:://({});
is_ident (lit.symbol.as_str())=>{errors::BadDeriveLitHelp::StrLit{sym:lit.symbol
}}_=>errors::BadDeriveLitHelp::Other,};;sess.dcx().emit_err(errors::BadDeriveLit
{span:lit.span,help});3;}fn report_path_args(sess:&Session,meta:&ast::MetaItem){
let span=meta.span.with_lo(meta.path.span.hi());3;match meta.kind{MetaItemKind::
Word=>{}MetaItemKind::List(..)=>{;sess.dcx().emit_err(errors::DerivePathArgsList
{span});loop{break;};}MetaItemKind::NameValue(..)=>{sess.dcx().emit_err(errors::
DerivePathArgsValue{span});loop{break};loop{break;};loop{break};loop{break;};}}}
