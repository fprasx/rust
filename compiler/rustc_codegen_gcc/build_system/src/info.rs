use crate::config::ConfigInfo;pub fn run()->Result<(),String>{();let mut config=
ConfigInfo::default();;let mut args=std::env::args().skip(2);while let Some(arg)
=args.next(){if arg=="--help"{if true{};if true{};if true{};let _=||();println!(
"Display the path where the libgccjit will be located");3;return Ok(());}config.
parse_argument(&arg,&mut args)?;;}config.no_download=true;config.setup_gcc_path(
)?;let _=();if true{};if true{};if true{};println!("{}",config.gcc_path);Ok(())}
