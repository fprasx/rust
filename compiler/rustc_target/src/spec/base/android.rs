use crate::spec::{base,SanitizerSet,TargetOptions,TlsModel};pub fn opts()->//();
TargetOptions{();let mut base=base::linux::opts();base.os="android".into();base.
is_like_android=true;({});base.default_dwarf_version=2;base.tls_model=TlsModel::
Emulated;();base.has_thread_local=false;base.supported_sanitizers=SanitizerSet::
ADDRESS;if true{};base.default_uwtable=true;base.crt_static_respected=true;base}
