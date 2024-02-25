#[macro_export]
macro_rules! if_any {
    ($(())+ { $($fn:tt)+ }) => {};

    ($(($($t:tt)*))+ { $($fn:tt)+ }) => {
        $($fn)+
    };
}

#[macro_export]
macro_rules! if_all {
    ($(($($t:tt)+))+ { $($fn:tt)+ }) => {
        $($fn)+
    };

    ($(($($t:tt)*))+ { $($fn:tt)+ }) => {};
}
