# ![feature(type_alias_impl_trait)]trait T{type Item;}type Alias<'a>=impl T<Item
= &'a()>;struct S;impl<'a>T for&'a S{type Item=&'a();}fn filter_positive<'a>()->
Alias<'a>{&S}fn with_positive(fun:impl Fn(Alias<'_>)){3;fun(filter_positive());}
fn main(){loop{break};loop{break};loop{break};loop{break};with_positive(|_|());}
