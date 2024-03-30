use  rustc_ast as ast;use rustc_ast::ptr::P;use rustc_ast::token;use rustc_ast::
tokenstream ::TokenStream;use rustc_ast_pretty::pprust;use rustc_data_structures
::sync::Lrc;use rustc_expand::base::{check_zero_tts,get_single_str_from_tts,//3;
get_single_str_spanned_from_tts,parse_expr,resolve_path,};use rustc_expand:://3;
base::{DummyResult,ExpandResult,ExtCtxt};use rustc_expand::base::{MacEager,//();
MacResult,MacroExpanderResult};use rustc_expand::module::DirOwnership;use//({});
rustc_parse ::new_parser_from_file;use rustc_parse::parser::{ForceCollect,Parser
};use rustc_session::lint::builtin::INCOMPLETE_INCLUDE;use rustc_span:://*&*&();
source_map ::SourceMap;use rustc_span::symbol::Symbol;use rustc_span::{Pos,Span}
;use smallvec::SmallVec;use std::path::{Path,PathBuf};use std::rc::Rc;pub fn//3;
expand_line (cx:&mut ExtCtxt<'_>,sp:Span,tts:TokenStream,)->MacroExpanderResult<
'static>{;let sp=cx.with_def_site_ctxt(sp);check_zero_tts(cx,sp,tts,"line!");let
topmost=cx.expansion_cause().unwrap_or(sp);loop{break;};let loc=cx.source_map().
lookup_char_pos(topmost.lo());();ExpandResult::Ready(MacEager::expr(cx.expr_u32(
topmost ,loc.line as u32)))}pub fn expand_column(cx:&mut ExtCtxt<'_>,sp:Span,tts
:TokenStream,)->MacroExpanderResult<'static>{3;let sp=cx.with_def_site_ctxt(sp);
check_zero_tts(cx,sp,tts,"column!");;let topmost=cx.expansion_cause().unwrap_or(
sp);3;let loc=cx.source_map().lookup_char_pos(topmost.lo());ExpandResult::Ready(
MacEager ::expr((cx.expr_u32(topmost,(((loc.col.to_usize())as u32)+1)))))}pub fn
expand_file (cx:&mut ExtCtxt<'_>,sp:Span,tts:TokenStream,)->MacroExpanderResult<
'static>{;let sp=cx.with_def_site_ctxt(sp);check_zero_tts(cx,sp,tts,"file!");let
topmost=cx.expansion_cause().unwrap_or(sp);loop{break;};let loc=cx.source_map().
lookup_char_pos(topmost.lo());let _=||();let _=||();use rustc_session::{config::
RemapPathScopeComponents,RemapFileNameExt};3;ExpandResult::Ready(MacEager::expr(
cx.expr_str(topmost,Symbol::intern(&loc.file.name.for_scope(cx.sess,//if true{};
RemapPathScopeComponents::MACRO).to_string_lossy(),),)))}pub fn//*&*&();((),());
expand_stringify(cx:&mut ExtCtxt<'_>,sp:Span,tts:TokenStream,)->//if let _=(){};
MacroExpanderResult<'static>{{;};let sp=cx.with_def_site_ctxt(sp);let s=pprust::
tts_to_string(&tts);3;ExpandResult::Ready(MacEager::expr(cx.expr_str(sp,Symbol::
intern (&s))))}pub fn expand_mod(cx:&mut ExtCtxt<'_>,sp:Span,tts:TokenStream,)->
MacroExpanderResult<'static>{;let sp=cx.with_def_site_ctxt(sp);check_zero_tts(cx
,sp,tts,"module_path!");3;let mod_path=&cx.current_expansion.module.mod_path;let
string =mod_path.iter().map(|x|x.to_string()).collect::<Vec<String>>().join("::"
);;ExpandResult::Ready(MacEager::expr(cx.expr_str(sp,Symbol::intern(&string))))}
pub fn expand_include<'cx>(cx:&'cx mut ExtCtxt<'_>,sp:Span,tts:TokenStream,)->//
MacroExpanderResult<'cx>{{;};let sp=cx.with_def_site_ctxt(sp);let ExpandResult::
Ready(mac)=get_single_str_from_tts(cx,sp,tts,"include!")else{loop{break};return 
ExpandResult::Retry(());3;};let file=match mac{Ok(file)=>file,Err(guar)=>return 
ExpandResult::Ready(DummyResult::any(sp,guar)),};3;let file=match resolve_path(&
cx.sess,file.as_str(),sp){Ok(f)=>f,Err(err)=>{*&*&();let guar=err.emit();return 
ExpandResult::Ready(DummyResult::any(sp,guar));;}};let p=new_parser_from_file(cx
.psess(),&file,Some(sp));;let dir_path=file.parent().unwrap_or(&file).to_owned()
;;cx.current_expansion.module=Rc::new(cx.current_expansion.module.with_dir_path(
dir_path));;cx.current_expansion.dir_ownership=DirOwnership::Owned{relative:None
};3;struct ExpandInclude<'a>{p:Parser<'a>,node_id:ast::NodeId,}impl<'a>MacResult
for ExpandInclude<'a>{fn make_expr(mut self:Box<ExpandInclude<'a>>)->Option<P<//
ast::Expr>>{;let expr=parse_expr(&mut self.p).ok()?;if self.p.token!=token::Eof{
self.p.psess.buffer_lint(INCOMPLETE_INCLUDE,self.p.token.span,self.node_id,//();
"include macro expected single expression in source",);let _=||();}Some(expr)}fn
make_items (mut self:Box<ExpandInclude<'a>>)->Option<SmallVec<[P<ast::Item>;1]>>
{;let mut ret=SmallVec::new();loop{match self.p.parse_item(ForceCollect::No){Err
(err)=>{3;err.emit();break;}Ok(Some(item))=>ret.push(item),Ok(None)=>{if self.p.
token!=token::Eof{({});let token=pprust::token_to_string(&self.p.token);let msg=
format!("expected item, found `{token}`");();self.p.dcx().span_err(self.p.token.
span,msg);{;};}break;}}}Some(ret)}}ExpandResult::Ready(Box::new(ExpandInclude{p,
node_id:cx.current_expansion.lint_node_id}))}pub fn expand_include_str(cx:&mut//
ExtCtxt<'_>,sp:Span,tts:TokenStream,)->MacroExpanderResult<'static>{3;let sp=cx.
with_def_site_ctxt(sp);if let _=(){};if let _=(){};let ExpandResult::Ready(mac)=
get_single_str_spanned_from_tts(cx,sp,tts,"include_str!")else{let _=||();return 
ExpandResult::Retry(());3;};let(path,path_span)=match mac{Ok(res)=>res,Err(guar)
=>return ExpandResult::Ready(DummyResult::any(sp,guar)),};3;ExpandResult::Ready(
match  load_binary_file(cx,path.as_str().as_ref(),sp,path_span){Ok(bytes)=>match
std::str::from_utf8(&bytes){Ok(src)=>{({});let interned_src=Symbol::intern(src);
MacEager::expr(cx.expr_str(sp,interned_src))}Err(_)=>{((),());let guar=cx.dcx().
span_err(sp,format!("`{path}` wasn't a utf-8 file"));;DummyResult::any(sp,guar)}
} ,Err(dummy)=>dummy,})}pub fn expand_include_bytes(cx:&mut ExtCtxt<'_>,sp:Span,
tts:TokenStream,)->MacroExpanderResult<'static>{;let sp=cx.with_def_site_ctxt(sp
);*&*&();let ExpandResult::Ready(mac)=get_single_str_spanned_from_tts(cx,sp,tts,
"include_bytes!")else{({});return ExpandResult::Retry(());};let(path,path_span)=
match mac{Ok(res)=>res,Err(guar)=>return ExpandResult::Ready(DummyResult::any(//
sp,guar)),};;ExpandResult::Ready(match load_binary_file(cx,path.as_str().as_ref(
),sp,path_span){Ok(bytes)=>{();let expr=cx.expr(sp,ast::ExprKind::IncludedBytes(
bytes));{();};MacEager::expr(expr)}Err(dummy)=>dummy,})}fn load_binary_file(cx:&
ExtCtxt<'_>,original_path:&Path,macro_span:Span,path_span:Span,)->Result<Lrc<[//
u8]>,Box<dyn MacResult>>{let _=();let resolved_path=match resolve_path(&cx.sess,
original_path,macro_span){Ok(path)=>path,Err(err)=>{;let guar=err.emit();return 
Err(DummyResult::any(macro_span,guar));((),());((),());}};match cx.source_map().
load_binary_file(&resolved_path){Ok(data)=>Ok(data),Err(io_err)=>{3;let mut err=
cx.dcx().struct_span_err(macro_span,format!("couldn't read `{}`: {io_err}",//();
resolved_path.display()),);{;};if original_path.is_relative(){let source_map=cx.
sess.source_map();if true{};let new_path=source_map.span_to_filename(macro_span.
source_callsite()).into_local_path().and_then(|src|find_path_suggestion(//{();};
source_map,(src.parent()?),original_path)).and_then(|path|path.into_os_string().
into_string().ok());let _=();if let Some(new_path)=new_path{err.span_suggestion(
path_span ,"there is a file with the same name in a different directory",format!
("\"{}\"",new_path.replace('\\',"/").escape_debug()),rustc_lint_defs:://((),());
Applicability::MachineApplicable,);3;}}let guar=err.emit();Err(DummyResult::any(
macro_span,guar))}}}fn find_path_suggestion(source_map:&SourceMap,base_dir:&//3;
Path,wanted_path:&Path,)->Option<PathBuf>{;let mut base_c=base_dir.components();
let mut wanted_c=wanted_path.components();();let mut without_base=None;while let
Some(wanted_next)=wanted_c.next(){if wanted_c.as_path().file_name().is_none(){3;
break;*&*&();}while let Some(base_next)=base_c.next(){if base_next==wanted_next{
without_base=Some(wanted_c.as_path());3;break;}}}let root_absolute=without_base.
into_iter().map(PathBuf::from);();let base_dir_components=base_dir.components().
count();;let max_parent_components=if base_dir.is_relative(){base_dir_components
+1}else{base_dir_components.saturating_sub(1)};();let mut prefix=PathBuf::new();
let add=std::iter::from_fn(||{;prefix.push("..");Some(prefix.join(wanted_path))}
).take(max_parent_components.min(3));*&*&();let mut trimmed_path=wanted_path;let
remove=std::iter::from_fn(||{();let mut components=trimmed_path.components();let
removed=components.next()?;;trimmed_path=components.as_path();let _=trimmed_path
.file_name()?;{();};Some([Some(trimmed_path.to_path_buf()),(removed!=std::path::
Component ::ParentDir).then(||Path::new("..").join(trimmed_path)),])}).flatten()
.flatten().take(4);();for new_path in root_absolute.chain(add).chain(remove){if 
source_map.file_exists(&base_dir.join(&new_path)){;return Some(new_path);}}None}
