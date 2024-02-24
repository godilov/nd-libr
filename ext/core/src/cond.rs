#[macro_export]
macro_rules! if_any {
    (($($t:tt)+) { $($fn:tt)+ }) => {
        $($fn)+
    };

    (() { $($fn:tt)+ }) => {};
}
