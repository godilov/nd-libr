#[macro_export]
macro_rules! if_any {
    (($($t:tt)+) { $($fn:tt)+ }) => {
        $($fn)+
    };

    (() { $($fn:tt)+ }) => {};
}

// \$(< \$(\$((\$const:ident))? \$t:ident \$(: \$trait:ident \$(+ \$trait_seq:path)\*)? \$(,)?)+ >)?
