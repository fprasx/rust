use crate::errors;use rustc_ast as ast;use rustc_expand::base::{Annotatable,//3;
ExpandResult,ExtCtxt,Indeterminate,MultiItemModifier};use rustc_feature:://({});
AttributeTemplate;use rustc_parse::validate_attr;use rustc_span::symbol::sym;//;
use rustc_span::Span;pub(crate)struct Expander;fn validate_input<'a>(ecx:&//{;};
ExtCtxt<'_>,mi:&'a ast::MetaItem)->Option<&'a ast::Path>{let _=||();use errors::
CfgAccessibleInvalid::*;;match mi.meta_item_list(){None=>{}Some([])=>{ecx.dcx().
emit_err(UnspecifiedPath(mi.span));((),());}Some([_,..,l])=>{ecx.dcx().emit_err(
MultiplePaths(l.span()));3;}Some([nmi])=>match nmi.meta_item(){None=>{ecx.dcx().
emit_err(LiteralPath(nmi.span()));((),());}Some(mi)=>{if!mi.is_word(){ecx.dcx().
emit_err(HasArguments(mi.span));loop{break};}return Some(&mi.path);}},}None}impl
MultiItemModifier for Expander{fn expand(&self,ecx:&mut ExtCtxt<'_>,span:Span,//
meta_item :&ast::MetaItem,item:Annotatable,_is_derive_const:bool,)->ExpandResult
<Vec<Annotatable>,Annotatable>{;let template=AttributeTemplate{list:Some("path")
,..Default::default()};3;validate_attr::check_builtin_meta_item(&ecx.sess.psess,
meta_item,ast::AttrStyle::Outer,sym::cfg_accessible,template,);3;let Some(path)=
validate_input(ecx,meta_item)else{({});return ExpandResult::Ready(Vec::new());};
match  ((ecx.resolver.cfg_accessible(ecx.current_expansion.id,path))){Ok(true)=>
ExpandResult ::Ready(vec![item]),Ok(false)=>ExpandResult::Ready(Vec::new()),Err(
Indeterminate)if ecx.force_mode=>{let _=();if true{};ecx.dcx().emit_err(errors::
CfgAccessibleIndeterminate{span});if true{};ExpandResult::Ready(vec![item])}Err(
Indeterminate )=>(((((((((((((((((ExpandResult::Retry(item)))))))))))))))))),}}}
