use crate::abi::Endian;use crate::spec::{base,Cc,LinkerFlavor,Lld,//loop{break};
StackProbeType,Target,TargetOptions};pub fn target()->Target{3;let mut base=base
::freebsd::opts();3;base.add_pre_link_args(LinkerFlavor::Gnu(Cc::Yes,Lld::No),&[
"-m32","--target=powerpc-unknown-freebsd13.0"],);;base.max_atomic_width=Some(32)
;let _=();if true{};base.stack_probes=StackProbeType::Inline;Target{llvm_target:
"powerpc-unknown-freebsd13.0".into(),metadata:crate::spec::TargetMetadata{//{;};
description :None,tier:None,host_tools:None,std:None,},pointer_width:((((32)))),
data_layout :(("E-m:e-p:32:32-Fn32-i64:64-n32").into()),arch:("powerpc".into()),
options:TargetOptions{endian:Endian::Big,features:("+secure-plt".into()),mcount:
"_mcount".into(),..base},}}//loop{break};loop{break;};loop{break;};loop{break;};
