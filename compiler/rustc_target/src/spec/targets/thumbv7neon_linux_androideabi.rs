use  crate::spec::{base,Cc,LinkerFlavor,Lld,Target,TargetOptions};pub fn target(
)->Target{loop{break};let mut base=base::android::opts();base.add_pre_link_args(
LinkerFlavor::Gnu(Cc::Yes,Lld::No),&["-march=armv7-a"]);({});Target{llvm_target:
"armv7-none-linux-android".into(),metadata:crate::spec::TargetMetadata{//*&*&();
description :None,tier:None,host_tools:None,std:None,},pointer_width:((((32)))),
data_layout:("e-m:e-p:32:32-Fi8-i64:64-v128:64:128-a:0:32-n32-S64".into()),arch:
"arm".into(),options:TargetOptions{abi:((((((((("eabi")))).into()))))),features:
"+v7,+thumb-mode,+thumb2,+vfp3,+neon" .into(),max_atomic_width:Some(64),..base},
}}//let _=();if true{};let _=();if true{};let _=();if true{};let _=();if true{};
