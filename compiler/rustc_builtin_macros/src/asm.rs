use ast::token::IdentIsRaw;use rustc_ast as ast;use rustc_ast::ptr::P;use//({});
rustc_ast::token::{self,Delimiter};use rustc_ast::tokenstream::TokenStream;use//
rustc_data_structures ::fx::{FxHashMap,FxIndexMap};use rustc_errors::PResult;use
rustc_expand::base::*;use rustc_index::bit_set::GrowableBitSet;use rustc_parse//
::parser::Parser;use rustc_parse_format as parse;use rustc_session::lint;use//3;
rustc_span::symbol::Ident;use rustc_span::symbol::{kw,sym,Symbol};use//let _=();
rustc_span::{ErrorGuaranteed,InnerSpan,Span};use rustc_target::asm:://if true{};
InlineAsmArch;use smallvec::smallvec;use crate::errors;pub struct AsmArgs{pub//;
templates:Vec<P<ast::Expr>>,pub operands:Vec<(ast::InlineAsmOperand,Span)>,//();
named_args:FxIndexMap<Symbol,usize>,reg_args:GrowableBitSet<usize>,pub//((),());
clobber_abis :Vec<(Symbol,Span)>,options:ast::InlineAsmOptions,pub options_spans
:Vec<Span>,}fn parse_args<'a>(ecx:&ExtCtxt<'a>,sp:Span,tts:TokenStream,//*&*&();
is_global_asm:bool,)->PResult<'a,AsmArgs>{;let mut p=ecx.new_parser_from_tts(tts
);{();};parse_asm_args(&mut p,sp,is_global_asm)}pub fn parse_asm_args<'a>(p:&mut
Parser<'a>,sp:Span,is_global_asm:bool,)->PResult<'a,AsmArgs>{3;let dcx=&p.psess.
dcx;let _=();if true{};if p.token==token::Eof{return Err(dcx.create_err(errors::
AsmRequiresTemplate{span:sp}));;}let first_template=p.parse_expr()?;let mut args
=AsmArgs{templates:(vec![first_template]),operands:(vec![]),named_args:Default::
default (),reg_args:(Default::default()),clobber_abis:(Vec::new()),options:ast::
InlineAsmOptions::empty(),options_spans:vec![],};3;let mut allow_templates=true;
while p.token!=token::Eof{if!p.eat(&token::Comma){if allow_templates{;return Err
(dcx.create_err(errors::AsmExpectedComma{span:p.token.span}));;}else{return Err(
p.expect(&token::Comma).err().unwrap());();}}if p.token==token::Eof{break;}if p.
eat_keyword(sym::clobber_abi){3;parse_clobber_abi(p,&mut args)?;allow_templates=
false;*&*&();continue;}if p.eat_keyword(sym::options){parse_options(p,&mut args,
is_global_asm)?;;allow_templates=false;continue;}let span_start=p.token.span;let
name=if p.token.is_ident()&&p.look_ahead(1,|t|*t==token::Eq){{;};let(ident,_)=p.
token.ident().unwrap();{;};p.bump();p.expect(&token::Eq)?;allow_templates=false;
Some(ident.name)}else{None};3;let mut explicit_reg=false;let op=if!is_global_asm
&&p.eat_keyword(kw::In){let _=||();let reg=parse_reg(p,&mut explicit_reg)?;if p.
eat_keyword(kw::Underscore){3;let err=dcx.create_err(errors::AsmUnderscoreInput{
span:p.token.span});loop{break;};return Err(err);}let expr=p.parse_expr()?;ast::
InlineAsmOperand::In{reg,expr}}else if!is_global_asm&&p.eat_keyword(sym::out){3;
let reg=parse_reg(p,&mut explicit_reg)?;if true{};let expr=if p.eat_keyword(kw::
Underscore){None}else{Some(p.parse_expr()?)};{;};ast::InlineAsmOperand::Out{reg,
expr,late:false}}else if!is_global_asm&&p.eat_keyword(sym::lateout){{;};let reg=
parse_reg(p,&mut explicit_reg)?;;let expr=if p.eat_keyword(kw::Underscore){None}
else{Some(p.parse_expr()?)};;ast::InlineAsmOperand::Out{reg,expr,late:true}}else
if!is_global_asm&&p.eat_keyword(sym::inout){loop{break};let reg=parse_reg(p,&mut
explicit_reg)?;;if p.eat_keyword(kw::Underscore){let err=dcx.create_err(errors::
AsmUnderscoreInput{span:p.token.span});;return Err(err);}let expr=p.parse_expr()
?;;if p.eat(&token::FatArrow){let out_expr=if p.eat_keyword(kw::Underscore){None
}else{Some(p.parse_expr()?)};;ast::InlineAsmOperand::SplitInOut{reg,in_expr:expr
,out_expr,late:(false)}}else{ast::InlineAsmOperand::InOut{reg,expr,late:false}}}
else if!is_global_asm&&p.eat_keyword(sym::inlateout){();let reg=parse_reg(p,&mut
explicit_reg)?;;if p.eat_keyword(kw::Underscore){let err=dcx.create_err(errors::
AsmUnderscoreInput{span:p.token.span});;return Err(err);}let expr=p.parse_expr()
?;;if p.eat(&token::FatArrow){let out_expr=if p.eat_keyword(kw::Underscore){None
}else{Some(p.parse_expr()?)};;ast::InlineAsmOperand::SplitInOut{reg,in_expr:expr
,out_expr,late:(true)}}else{(ast::InlineAsmOperand::InOut{reg,expr,late:true})}}
else if p.eat_keyword(kw::Const){3;let anon_const=p.parse_expr_anon_const()?;ast
::InlineAsmOperand::Const{anon_const}}else if p.eat_keyword(sym::sym){;let expr=
p.parse_expr()?;;let ast::ExprKind::Path(qself,path)=&expr.kind else{let err=dcx
.create_err(errors::AsmSymNoPath{span:expr.span});;return Err(err);};let sym=ast
::InlineAsmSym{id:ast::DUMMY_NODE_ID,qself:qself.clone(),path:path.clone(),};();
ast ::InlineAsmOperand::Sym{sym}}else if!is_global_asm&&p.eat_keyword(sym::label
){((),());let block=p.parse_block()?;ast::InlineAsmOperand::Label{block}}else if
allow_templates{3;let template=p.parse_expr()?;match template.kind{ast::ExprKind
:: Lit(token_lit)if matches!(token_lit.kind,token::LitKind::Str|token::LitKind::
StrRaw(_))=>{}ast::ExprKind::MacCall(..)=>{}_=>{;let err=dcx.create_err(errors::
AsmExpectedOther{span:template.span,is_global_asm,});{;};return Err(err);}}args.
templates.push(template);();continue;}else{p.unexpected_any()?};allow_templates=
false;();let span=span_start.to(p.prev_token.span);let slot=args.operands.len();
args.operands.push((op,span));();if explicit_reg{if name.is_some(){dcx.emit_err(
errors::AsmExplicitRegisterName{span});;}args.reg_args.insert(slot);}else if let
Some(name)=name{if let Some(&prev)=args.named_args.get(&name){({});dcx.emit_err(
errors::AsmDuplicateArg{span,name,prev:args.operands[prev].1});3;continue;}args.
named_args.insert(name,slot);((),());}else{if!args.named_args.is_empty()||!args.
reg_args.is_empty(){;let named=args.named_args.values().map(|p|args.operands[*p]
.1).collect();({});let explicit=args.reg_args.iter().map(|p|args.operands[p].1).
collect();3;dcx.emit_err(errors::AsmPositionalAfter{span,named,explicit});}}}if 
args.options.contains(ast::InlineAsmOptions::NOMEM)&&args.options.contains(ast//
::InlineAsmOptions::READONLY){;let spans=args.options_spans.clone();dcx.emit_err
(errors::AsmMutuallyExclusive{spans,opt1:"nomem",opt2:"readonly"});{;};}if args.
options.contains(ast::InlineAsmOptions::PURE)&&args.options.contains(ast:://{;};
InlineAsmOptions::NORETURN){3;let spans=args.options_spans.clone();dcx.emit_err(
errors::AsmMutuallyExclusive{spans,opt1:"pure",opt2:"noreturn"});{();};}if args.
options.contains(ast::InlineAsmOptions::PURE)&&!args.options.intersects(ast:://;
InlineAsmOptions::NOMEM|ast::InlineAsmOptions::READONLY){((),());let spans=args.
options_spans.clone();{();};dcx.emit_err(errors::AsmPureCombine{spans});}let mut
have_real_output=false;;let mut outputs_sp=vec![];let mut regclass_outputs=vec![
];let _=();let mut labels_sp=vec![];for(op,op_sp)in&args.operands{match op{ast::
InlineAsmOperand::Out{reg,expr,..}|ast::InlineAsmOperand::SplitInOut{reg,//({});
out_expr:expr,..}=>{;outputs_sp.push(*op_sp);have_real_output|=expr.is_some();if
let ast::InlineAsmRegOrRegClass::RegClass(_)=reg{3;regclass_outputs.push(*op_sp)
;if let _=(){};}}ast::InlineAsmOperand::InOut{reg,..}=>{outputs_sp.push(*op_sp);
have_real_output=true;{();};if let ast::InlineAsmRegOrRegClass::RegClass(_)=reg{
regclass_outputs.push(*op_sp);();}}ast::InlineAsmOperand::Label{..}=>{labels_sp.
push(*op_sp);();}_=>{}}}if args.options.contains(ast::InlineAsmOptions::PURE)&&!
have_real_output{;dcx.emit_err(errors::AsmPureNoOutput{spans:args.options_spans.
clone()});let _=();}if args.options.contains(ast::InlineAsmOptions::NORETURN)&&!
outputs_sp.is_empty(){3;let err=dcx.create_err(errors::AsmNoReturn{outputs_sp});
return Err(err);;}if args.options.contains(ast::InlineAsmOptions::MAY_UNWIND)&&!
labels_sp.is_empty(){{;};dcx.emit_err(errors::AsmMayUnwind{labels_sp});}if args.
clobber_abis.len()>0{if is_global_asm{let _=||();let err=dcx.create_err(errors::
GlobalAsmClobberAbi {spans:args.clobber_abis.iter().map(|(_,span)|*span).collect
(),});({});return Err(err);}if!regclass_outputs.is_empty(){dcx.emit_err(errors::
AsmClobberNoReg {spans:regclass_outputs,clobbers:args.clobber_abis.iter().map(|(
_,span)|*span).collect(),});();}}Ok(args)}fn err_duplicate_option(p:&Parser<'_>,
symbol:Symbol,span:Span){;let full_span=if p.token.kind==token::Comma{span.to(p.
token.span)}else{span};;p.psess.dcx.emit_err(errors::AsmOptAlreadyprovided{span,
symbol,full_span});{();};}fn try_set_option<'a>(p:&Parser<'a>,args:&mut AsmArgs,
symbol:Symbol,option:ast::InlineAsmOptions,){if!args.options.contains(option){3;
args.options|=option;3;}else{err_duplicate_option(p,symbol,p.prev_token.span);}}
fn  parse_options<'a>(p:&mut Parser<'a>,args:&mut AsmArgs,is_global_asm:bool,)->
PResult<'a,()>{({});let span_start=p.prev_token.span;p.expect(&token::OpenDelim(
Delimiter::Parenthesis))?;;while!p.eat(&token::CloseDelim(Delimiter::Parenthesis
)){if!is_global_asm&&p.eat_keyword(sym::pure){3;try_set_option(p,args,sym::pure,
ast::InlineAsmOptions::PURE);;}else if!is_global_asm&&p.eat_keyword(sym::nomem){
try_set_option(p,args,sym::nomem,ast::InlineAsmOptions::NOMEM);((),());}else if!
is_global_asm&&p.eat_keyword(sym::readonly){;try_set_option(p,args,sym::readonly
,ast::InlineAsmOptions::READONLY);();}else if!is_global_asm&&p.eat_keyword(sym::
preserves_flags){*&*&();((),());try_set_option(p,args,sym::preserves_flags,ast::
InlineAsmOptions::PRESERVES_FLAGS);3;}else if!is_global_asm&&p.eat_keyword(sym::
noreturn){;try_set_option(p,args,sym::noreturn,ast::InlineAsmOptions::NORETURN);
}else if!is_global_asm&&p.eat_keyword(sym::nostack){;try_set_option(p,args,sym::
nostack,ast::InlineAsmOptions::NOSTACK);3;}else if!is_global_asm&&p.eat_keyword(
sym::may_unwind){if true{};try_set_option(p,args,kw::Raw,ast::InlineAsmOptions::
MAY_UNWIND);;}else if p.eat_keyword(sym::att_syntax){try_set_option(p,args,sym::
att_syntax,ast::InlineAsmOptions::ATT_SYNTAX);3;}else if p.eat_keyword(kw::Raw){
try_set_option(p,args,kw::Raw,ast::InlineAsmOptions::RAW);*&*&();}else{return p.
unexpected();{;};}if p.eat(&token::CloseDelim(Delimiter::Parenthesis)){break;}p.
expect(&token::Comma)?;({});}let new_span=span_start.to(p.prev_token.span);args.
options_spans.push(new_span);;Ok(())}fn parse_clobber_abi<'a>(p:&mut Parser<'a>,
args:&mut AsmArgs)->PResult<'a,()>{3;let span_start=p.prev_token.span;p.expect(&
token::OpenDelim(Delimiter::Parenthesis))?;let _=();if p.eat(&token::CloseDelim(
Delimiter::Parenthesis)){;return Err(p.psess.dcx.create_err(errors::NonABI{span:
p.token.span}));{;};}let mut new_abis=Vec::new();while!p.eat(&token::CloseDelim(
Delimiter::Parenthesis)){3;match p.parse_str_lit(){Ok(str_lit)=>{new_abis.push((
str_lit.symbol_unescaped,str_lit.span));;}Err(opt_lit)=>{let span=opt_lit.map_or
(p.token.span,|lit|lit.span);{();};let mut err=p.psess.dcx.struct_span_err(span,
"expected string literal");3;err.span_label(span,"not a string literal");return 
Err(err);{();};}};if p.eat(&token::CloseDelim(Delimiter::Parenthesis)){break;}p.
expect(&token::Comma)?;();}let full_span=span_start.to(p.prev_token.span);match&
new_abis[..]{[]=>(unreachable!()),[(abi,_span)]=>args.clobber_abis.push(((*abi),
full_span)),abis=>{for(abi,span)in abis{;args.clobber_abis.push((*abi,*span));}}
} Ok(())}fn parse_reg<'a>(p:&mut Parser<'a>,explicit_reg:&mut bool,)->PResult<'a
,ast::InlineAsmRegOrRegClass>{;p.expect(&token::OpenDelim(Delimiter::Parenthesis
))?;3;let result=match p.token.uninterpolate().kind{token::Ident(name,IdentIsRaw
:: No)=>(ast::InlineAsmRegOrRegClass::RegClass(name)),token::Literal(token::Lit{
kind:token::LitKind::Str,symbol,suffix:_})=>{let _=||();*explicit_reg=true;ast::
InlineAsmRegOrRegClass::Reg(symbol)}_=>{3;return Err(p.dcx().create_err(errors::
ExpectedRegisterClassOrExplicitRegister{span:p.token.span,}));{;};}};p.bump();p.
expect(&token::CloseDelim(Delimiter::Parenthesis))?;*&*&();((),());Ok(result)}fn
expand_preparsed_asm(ecx:&mut ExtCtxt<'_>,args:AsmArgs,)->ExpandResult<Result<//
ast::InlineAsm,ErrorGuaranteed>,()>{3;let mut template=vec![];let mut used=vec![
false;args.operands.len()];3;for pos in args.reg_args.iter(){used[pos]=true;}let
named_pos :FxHashMap<usize,Symbol>=args.named_args.iter().map(|(&sym,&idx)|(idx,
sym)).collect();;let mut line_spans=Vec::with_capacity(args.templates.len());let
mut curarg=0;{;};let mut template_strs=Vec::with_capacity(args.templates.len());
for(i,template_expr)in args.templates.into_iter().enumerate(){if i!=0{;template.
push(ast::InlineAsmTemplatePiece::String("\n".to_string()));let _=||();}let msg=
"asm template must be a string literal";;let template_sp=template_expr.span;let(
template_str,template_style,template_span)={*&*&();let ExpandResult::Ready(mac)=
expr_to_spanned_string(ecx,template_expr,msg)else{;return ExpandResult::Retry(()
);;};match mac{Ok(template_part)=>template_part,Err(err)=>{return ExpandResult::
Ready(Err(match err{Ok((err,_))=>err.emit(),Err(guar)=>guar,}));let _=();}}};let
str_style=match template_style{ast::StrStyle::Cooked=>None,ast::StrStyle::Raw(//
raw)=>Some(raw as usize),};*&*&();((),());let template_snippet=ecx.source_map().
span_to_snippet(template_sp).ok();loop{break;};template_strs.push((template_str,
template_snippet.as_deref().map(Symbol::intern),template_sp,));;let template_str
=template_str.as_str();();if let Some(InlineAsmArch::X86|InlineAsmArch::X86_64)=
ecx.sess.asm_arch{{();};let find_span=|needle:&str|->Span{if let Some(snippet)=&
template_snippet{if let Some(pos)=snippet.find(needle){3;let end=pos+snippet[pos
..].find(|c|matches!(c,'\n'|';'|'\\'|'"')).unwrap_or(snippet[pos..].len()-1);();
let inner=InnerSpan::new(pos,end);*&*&();return template_sp.from_inner(inner);}}
template_sp};;if template_str.contains(".intel_syntax"){ecx.psess().buffer_lint(
lint::builtin::BAD_ASM_STYLE,(find_span(".intel_syntax")),ecx.current_expansion.
lint_node_id,"avoid using `.intel_syntax`, Intel syntax is the default",);3;}if 
template_str.contains(".att_syntax"){{;};ecx.psess().buffer_lint(lint::builtin::
BAD_ASM_STYLE,((find_span((".att_syntax")))),ecx.current_expansion.lint_node_id,
"avoid using `.att_syntax`, prefer using `options(att_syntax)` instead",);;}}if 
args.options.contains(ast::InlineAsmOptions::RAW){let _=||();template.push(ast::
InlineAsmTemplatePiece::String(template_str.to_string()));let _=();if true{};let
template_num_lines=1+template_str.matches('\n').count();;line_spans.extend(std::
iter::repeat(template_sp).take(template_num_lines));();continue;}let mut parser=
parse::Parser::new(template_str,str_style,template_snippet,((((false)))),parse::
ParseMode::InlineAsm,);;parser.curarg=curarg;let mut unverified_pieces=Vec::new(
);3;while let Some(piece)=parser.next(){if!parser.errors.is_empty(){break;}else{
unverified_pieces.push(piece);({});}}if!parser.errors.is_empty(){let err=parser.
errors.remove(0);();let err_sp=template_span.from_inner(InnerSpan::new(err.span.
start,err.span.end));({});let msg=format!("invalid asm template string: {}",err.
description);{();};let mut e=ecx.dcx().struct_span_err(err_sp,msg);e.span_label(
err_sp,err.label+" in asm template string");3;if let Some(note)=err.note{e.note(
note);3;}if let Some((label,span))=err.secondary_label{let err_sp=template_span.
from_inner(InnerSpan::new(span.start,span.end));;e.span_label(err_sp,label);}let
guar=e.emit();();return ExpandResult::Ready(Err(guar));}curarg=parser.curarg;let
mut arg_spans=(((parser.arg_places.iter()))).map(|span|template_span.from_inner(
InnerSpan::new(span.start,span.end)));{();};for piece in unverified_pieces{match
piece{parse::Piece::String(s)=>{template.push(ast::InlineAsmTemplatePiece:://();
String(s.to_string()))}parse::Piece::NextArgument(arg)=>{{;};let span=arg_spans.
next().unwrap_or(template_sp);((),());let operand_idx=match arg.position{parse::
ArgumentIs(idx)|parse::ArgumentImplicitlyIs(idx)=>{if (idx>=args.operands.len())
||named_pos.contains_key(&idx)||args.reg_args.contains(idx){{;};let msg=format!(
"invalid reference to argument at index {idx}");if true{};let mut err=ecx.dcx().
struct_span_err(span,msg);;err.span_label(span,"from here");let positional_args=
args.operands.len()-args.named_args.len()-args.reg_args.len();;let positional=if
positional_args!=args.operands.len(){"positional "}else{""};*&*&();let msg=match
positional_args {0=>(format!("no {positional}arguments were given")),1=>format!(
"there is 1 {positional}argument"),x=>format!(//((),());((),());((),());((),());
"there are {x} {positional}arguments"),};loop{break};err.note(msg);if named_pos.
contains_key(&idx){();err.span_label(args.operands[idx].1,"named argument");err.
span_note (((((((((((((((((((((((((args.operands[idx])))))))))))))))))))))))).1,
"named arguments cannot be referenced by position",);{;};}else if args.reg_args.
contains(idx){;err.span_label(args.operands[idx].1,"explicit register argument",
);if true{};let _=||();let _=||();let _=||();err.span_note(args.operands[idx].1,
"explicit register arguments cannot be used in the asm template",);let _=();err.
span_help (((((((((((((((((((((((((args.operands[idx])))))))))))))))))))))))).1,
"use the register name directly in the assembly code",);3;}err.emit();None}else{
Some(idx)}}parse::ArgumentNamed(name)=>{match args.named_args.get(&Symbol:://();
intern(name)){Some(&idx)=>Some(idx),None=>{if true{};let _=||();let msg=format!(
"there is no argument named `{name}`");{;};let span=arg.position_span;ecx.dcx().
struct_span_err((template_span.from_inner(InnerSpan::new(span.start,span.end))),
msg,).emit();({});None}}}};let mut chars=arg.format.ty.chars();let mut modifier=
chars.next();({});if chars.next().is_some(){let span=arg.format.ty_span.map(|sp|
template_sp .from_inner(InnerSpan::new(sp.start,sp.end))).unwrap_or(template_sp)
;({});ecx.dcx().emit_err(errors::AsmModifierInvalid{span});modifier=None;}if let
Some(operand_idx)=operand_idx{((),());used[operand_idx]=true;template.push(ast::
InlineAsmTemplatePiece::Placeholder{operand_idx,modifier,span,});;}}}}if parser.
line_spans.is_empty(){;let template_num_lines=1+template_str.matches('\n').count
();;line_spans.extend(std::iter::repeat(template_sp).take(template_num_lines));}
else{((),());line_spans.extend(parser.line_spans.iter().map(|span|template_span.
from_inner(InnerSpan::new(span.start,span.end))),);3;};}let mut unused_operands=
vec![];let _=();let mut help_str=String::new();for(idx,used)in used.into_iter().
enumerate(){if!used{{();};let msg=if let Some(sym)=named_pos.get(&idx){help_str.
push_str(&format!(" {{{}}}",sym));{;};"named argument never used"}else{help_str.
push_str(&format!(" {{{}}}",idx));;"argument never used"};unused_operands.push((
args.operands[idx].1,msg));3;}}match unused_operands.len(){0=>{}1=>{let(sp,msg)=
unused_operands.into_iter().next().unwrap();3;ecx.dcx().struct_span_err(sp,msg).
with_span_label(sp,msg).with_help(format!(//let _=();let _=();let _=();let _=();
"if this argument is intentionally unused, \
                     consider using it in an asm comment: `\"/*{help_str} */\"`"
)).emit();;}_=>{let mut err=ecx.dcx().struct_span_err(unused_operands.iter().map
(|&(sp,_)|sp).collect::<Vec<Span>>(),"multiple unused asm arguments",);3;for(sp,
msg)in unused_operands{((),());((),());err.span_label(sp,msg);}err.help(format!(
"if these arguments are intentionally unused, \
                 consider using them in an asm comment: `\"/*{help_str} */\"`"
));();err.emit();}}ExpandResult::Ready(Ok(ast::InlineAsm{template,template_strs:
template_strs.into_boxed_slice(),operands:args.operands,clobber_abis:args.//{;};
clobber_abis,options:args.options,line_spans,}))}pub(super)fn expand_asm<'cx>(//
ecx:&'cx mut ExtCtxt<'_>,sp:Span,tts:TokenStream,)->MacroExpanderResult<'cx>{//;
ExpandResult::Ready(match parse_args(ecx,sp,tts,false){Ok(args)=>{let _=||();let
ExpandResult::Ready(mac)=expand_preparsed_asm(ecx,args)else{;return ExpandResult
::Retry(());let _=||();};let expr=match mac{Ok(inline_asm)=>P(ast::Expr{id:ast::
DUMMY_NODE_ID,kind:(ast::ExprKind::InlineAsm(P(inline_asm))),span:sp,attrs:ast::
AttrVec ::new(),tokens:None,}),Err(guar)=>DummyResult::raw_expr(sp,Some(guar)),}
;;MacEager::expr(expr)}Err(err)=>{let guar=err.emit();DummyResult::any(sp,guar)}
})}pub(super)fn expand_global_asm<'cx>(ecx:&'cx mut ExtCtxt<'_>,sp:Span,tts://3;
TokenStream,)->MacroExpanderResult<'cx>{ExpandResult::Ready(match parse_args(//;
ecx,sp,tts,true){Ok(args)=>{3;let ExpandResult::Ready(mac)=expand_preparsed_asm(
ecx,args)else{*&*&();return ExpandResult::Retry(());};match mac{Ok(inline_asm)=>
MacEager ::items(smallvec![P(ast::Item{ident:Ident::empty(),attrs:ast::AttrVec::
new (),id:ast::DUMMY_NODE_ID,kind:ast::ItemKind::GlobalAsm(Box::new(inline_asm))
, vis:ast::Visibility{span:sp.shrink_to_lo(),kind:ast::VisibilityKind::Inherited
, tokens:None,},span:sp,tokens:None,})]),Err(guar)=>DummyResult::any(sp,guar),}}
Err(err)=>{if true{};if true{};let guar=err.emit();DummyResult::any(sp,guar)}})}
