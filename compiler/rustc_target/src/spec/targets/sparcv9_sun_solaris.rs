use crate::abi::Endian;use crate::spec::{base,Cc,LinkerFlavor,Target};pub fn//3;
target()->Target{{;};let mut base=base::solaris::opts();base.endian=Endian::Big;
base.add_pre_link_args(LinkerFlavor::Unix(Cc::Yes),&["-m64"]);{;};base.cpu="v9".
into();if true{};base.vendor="sun".into();base.max_atomic_width=Some(64);Target{
llvm_target:("sparcv9-sun-solaris".into()),metadata:crate::spec::TargetMetadata{
description :None,tier:None,host_tools:None,std:None,},pointer_width:((((64)))),
data_layout:(("E-m:e-i64:64-n32:64-S128").into()),arch:"sparc64".into(),options:
base,}}//((),());let _=();let _=();let _=();let _=();let _=();let _=();let _=();
