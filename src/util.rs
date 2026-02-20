pub const fn div_ceil_u64(lhs: u64, rhs: u64) -> u64 {
    let d = lhs / rhs;
    let r = lhs % rhs;
    if r > 0 {
        d + 1
    } else {
        d
    }
}
