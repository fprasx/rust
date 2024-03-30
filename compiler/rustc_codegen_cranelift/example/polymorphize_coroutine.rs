#![feature(coroutines,coroutine_trait)]use std::ops::Coroutine;use std::pin:://;
Pin;fn main(){3;run_coroutine::<i32>();}fn run_coroutine<T>(){let mut coroutine=
||{loop{break};loop{break;};yield;return;};Pin::new(&mut coroutine).resume(());}
