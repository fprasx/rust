use crate::abi::Endian;use crate::spec::{base,Cc,LinkerFlavor,Lld,//loop{break};
StackProbeType,Target,TargetOptions};pub fn target()->Target{3;let mut base=base
::vxworks::opts();3;base.add_pre_link_args(LinkerFlavor::Gnu(Cc::Yes,Lld::No),&[
"-mspe","--secure-plt"]);{();};base.max_atomic_width=Some(32);base.stack_probes=
StackProbeType::Inline;;Target{llvm_target:"powerpc-unknown-linux-gnuspe".into()
,metadata:crate::spec::TargetMetadata{description:None,tier:None,host_tools://3;
None ,std:None,},pointer_width:(32),data_layout:"E-m:e-p:32:32-Fn32-i64:64-n32".
into (),arch:(("powerpc").into()),options:TargetOptions{abi:"spe".into(),endian:
Endian ::Big,features:(((((((((("+secure-plt,+msync"))))).into()))))),..base},}}
