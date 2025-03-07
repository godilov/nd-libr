pub struct Bytes(Vec<u8>);

pub struct BytesFixed<const L: usize>([u8; L]);
