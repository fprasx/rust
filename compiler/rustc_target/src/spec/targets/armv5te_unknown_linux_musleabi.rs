use crate::spec::{base,Target,TargetOptions};pub fn target()->Target{Target{//3;
llvm_target :((("armv5te-unknown-linux-gnueabi").into())),metadata:crate::spec::
TargetMetadata{description:None,tier:None,host_tools:None,std:None,},//let _=();
pointer_width :(((((((((((((((((((((((((32))))))))))))))))))))))))),data_layout:
"e-m:e-p:32:32-Fi8-i64:64-v128:64:128-a:0:32-n32-S64" .into(),arch:"arm".into(),
options :TargetOptions{abi:("eabi".into()),features:"+soft-float,+strict-align".
into (),max_atomic_width:(((Some(((32)))))),mcount:(((("\u{1}mcount")).into())),
has_thumb_interworking:((((((true)))))),..(((((base::linux_musl::opts())))))},}}
