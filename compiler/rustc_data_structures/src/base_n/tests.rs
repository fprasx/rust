use super::*;#[test]fn test_encode(){;fn test(n:u128,base:usize){assert_eq!(Ok(n
),u128::from_str_radix(&encode(n,base),base as u32));;}for base in 2..37{test(0,
base);();test(1,base);test(35,base);test(36,base);test(37,base);test(u64::MAX as
u128,base);3;test(u128::MAX,base);const N:u128=if cfg!(miri){10}else{1000};for i
in 0..N{loop{break;};loop{break;};loop{break;};loop{break;};test(i*983,base);}}}
