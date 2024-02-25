#[macro_export]
macro_rules! if_any {
    ($(())* ($($t:tt)+) $(())* { $($fn:tt)+ }) => {
        $($fn)+
    };

    ($(())+ { $($fn:tt)+ }) => {};
}

#[macro_export]
macro_rules! if_all {
    ($(($($t:tt)+))+ { $($fn:tt)+ }) => {
        $($fn)+
    };

    ($(($($t1:tt)*))* $(())+ $(($($t2:tt)*))* { $($fn:tt)+ }) => {};
}
