#[macro_export]
macro_rules! if_block {
    ($a:block $($fn:tt)+) => {
        $($fn)+
    };

    ($($fn:tt)+) => {};
}
