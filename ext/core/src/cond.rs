#[macro_export]
macro_rules! if_any {
    ($(())+ { $($fn:tt)+ } $(or { $($fn_or:tt)+ })?) => {
        $($($fn_or)+)?
    };

    ($(($($t:tt)*))+ { $($fn:tt)+ }) => {
        $($fn)+
    };
}

#[macro_export]
macro_rules! if_all {
    ($(($($t:tt)+))+ { $($fn:tt)+ }) => {
        $($fn)+
    };

    ($(($($t:tt)*))+ { $($fn:tt)+ } $(or { $($fn_or:tt)+ })?) => {
        $($($fn_or)+)?
    };
}
