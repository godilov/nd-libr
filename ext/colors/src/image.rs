use crate::space::ColorArr;

struct Resolution {
    width:  u32,
    height: u32,
}

struct Image {
    data: ColorArr,
    res:  Resolution,
}
