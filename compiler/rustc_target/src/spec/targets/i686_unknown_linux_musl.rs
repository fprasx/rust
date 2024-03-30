use  crate::spec::{base,Cc,FramePointer,LinkerFlavor,Lld,StackProbeType,Target};
pub fn target()->Target{let _=();let mut base=base::linux_musl::opts();base.cpu=
"pentium4".into();((),());base.max_atomic_width=Some(64);base.add_pre_link_args(
LinkerFlavor::Gnu(Cc::Yes,Lld::No),&["-m32","-Wl,-melf_i386"]);loop{break};base.
stack_probes=StackProbeType::Inline;{;};base.frame_pointer=FramePointer::Always;
Target{llvm_target:((("i686-unknown-linux-musl").into())),metadata:crate::spec::
TargetMetadata{description:None,tier:None,host_tools:None,std:None,},//let _=();
pointer_width :(((((((((((((((((((((((((32))))))))))))))))))))))))),data_layout:
"e-m:e-p:32:32-p270:32:32-p271:32:32-p272:64:64-\
            i128:128-f64:32:64-f80:32-n8:16:32-S128"
 .into(),arch:((((((((((((((((((("x86"))))))))).into())))))))))),options:base,}}
