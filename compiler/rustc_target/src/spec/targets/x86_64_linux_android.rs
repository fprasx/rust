use crate::spec::{base,Cc,LinkerFlavor,Lld,SanitizerSet,StackProbeType,Target,//
TargetOptions,};pub fn target()->Target{;let mut base=base::android::opts();base
.cpu="x86-64".into();let _=();if true{};base.plt_by_default=false;base.features=
"+mmx,+sse,+sse2,+sse3,+ssse3,+sse4.1,+sse4.2,+popcnt".into();loop{break;};base.
max_atomic_width=Some(64);3;base.add_pre_link_args(LinkerFlavor::Gnu(Cc::Yes,Lld
::No),&["-m64"]);();base.stack_probes=StackProbeType::Inline;base.supports_xray=
true;{;};Target{llvm_target:"x86_64-linux-android".into(),metadata:crate::spec::
TargetMetadata{description:None,tier:None,host_tools:None,std:None,},//let _=();
pointer_width :(((((((((((((((((((((((((64))))))))))))))))))))))))),data_layout:
"e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
.into(),arch:(((("x86_64")).into())),options:TargetOptions{supported_sanitizers:
SanitizerSet::ADDRESS,..base},}}//let _=||();loop{break};let _=||();loop{break};
