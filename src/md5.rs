extern crate byteorder;

use std::iter;
use std::io::Cursor;
use std::ops::Add;
use std::ops::Not;
use std::ops::Shl;
use self::byteorder::{LittleEndian, WriteBytesExt, ReadBytesExt};

pub fn hash(input_vec: Vec<u8>, output_vec: &mut Vec<u8>) {
    let mut vec = &mut input_vec.clone();

    let bit_len = vec.len() * 8;
    pad_vec(vec);
    add_len(vec, bit_len as u64);

    let res = perform_rounds(initial_md_buffer(), vec);

    output_vec.write_u32::<LittleEndian>(res.a.0).unwrap();
    output_vec.write_u32::<LittleEndian>(res.b.0).unwrap();
    output_vec.write_u32::<LittleEndian>(res.c.0).unwrap();
    output_vec.write_u32::<LittleEndian>(res.d.0).unwrap();
}

fn pad_vec(vec: &mut Vec<u8>) {
    vec.push(0x80 as u8); // i.e. only the MSB is set.

    // Number of additional bytes needed to make the len (in bits) respect:
    // (vec.len() * 8) == 448 (mod 512) i.e. vec.len() == 56 (mod 64)
    let mut diff = 56 - (vec.len() % 64) as i8;

    // We can't pad a negative number of bits, so pad up to the next multiple
    // of 64.
    if diff < 0 {
        diff += 64;
    }

    vec.extend(iter::repeat(0).take(diff as usize));

    assert_eq!(vec.len() % 64, 56)
}

fn add_len(vec: &mut Vec<u8>, bit_len: u64) {
    // TODO: what if bit_len of the input is > 2^64?
    let lword_mask = (!0 as u32) as u64;
    let hword_mask = !lword_mask;

    let lword = (bit_len & lword_mask) as u32;
    let hword = ((bit_len & hword_mask) >> 32) as u32;

    vec.write_u32::<LittleEndian>(lword).unwrap();
    vec.write_u32::<LittleEndian>(hword).unwrap();

    assert_eq!(vec.len() % 64, 0)
}

custom_derive! {
    #[derive(NewtypeNot, NewtypeBitAnd, NewtypeBitOr, NewtypeBitXor)]
    #[derive(Clone, Copy)]
    struct WrappingRotating(pub u32);
}

#[derive(Clone)]
struct DigestBuffer {
    a: WrappingRotating,
    b: WrappingRotating,
    c: WrappingRotating,
    d: WrappingRotating,
}

// Let us use + syntax for component-wise addition as per the spec.
impl Add for DigestBuffer {
    type Output = DigestBuffer;

    fn add(self, rhs: DigestBuffer) -> DigestBuffer {
        DigestBuffer {
            a: self.a + rhs.a,
            b: self.b + rhs.b,
            c: self.c + rhs.c,
            d: self.d + rhs.d,
        }
    }
}

// Let us use a + b syntax for wrapping add as per the spec.
impl Add for WrappingRotating {
    type Output = WrappingRotating;

    fn add(self, rhs: WrappingRotating) -> WrappingRotating {
        WrappingRotating(self.0.wrapping_add(rhs.0))
    }
}

// Let us use << syntax for rotate left as per the spec.
impl Shl<u32> for WrappingRotating {
    type Output = WrappingRotating;

    fn shl(self, rhs: u32) -> WrappingRotating {
        WrappingRotating(self.0.rotate_left(rhs))
    }
}

fn initial_md_buffer() -> DigestBuffer {
    DigestBuffer {
        a: WrappingRotating(0x67452301),
        b: WrappingRotating(0xefcdab89),
        c: WrappingRotating(0x98badcfe),
        d: WrappingRotating(0x10325476),
    }
}

fn f(x: WrappingRotating, y: WrappingRotating, z: WrappingRotating) -> WrappingRotating {
    (x & y) | (!x & z)
}

fn g(x: WrappingRotating, y: WrappingRotating, z: WrappingRotating) -> WrappingRotating {
    (x & z) | (y & !z)
}

fn h(x: WrappingRotating, y: WrappingRotating, z: WrappingRotating) -> WrappingRotating {
    x ^ y ^ z
}

fn i(x: WrappingRotating, y: WrappingRotating, z: WrappingRotating) -> WrappingRotating {
    y ^ (x | !z)
}

fn build_table() -> Vec<WrappingRotating> {
    //   This step uses a 64-element table T[1 ... 64] constructed from the
    //   sine function. Let T[i] denote the i-th element of the table, which
    //   is equal to the integer part of 4294967296 times abs(sin(i)), where i
    //   is in radians. The elements of the table are given in the appendix.

    let mut vec = &mut Vec::new();

    for i in 1..65 {
        let x = (2f64.powi(32) * (i as f64).sin().abs()) as u32;

        vec.push(WrappingRotating(x));
    }

    vec.clone()
}

// All rounds are of the form
// a = b + ((a + F(b,c,d) + X[k] + T[i]) <<< s). */
// except with F replaced by one of f, g, h, i
macro_rules! round {
    ($buf:expr, $x:expr, $t:expr,
     $a:ident, $b:ident, $c:ident, $d:ident,
     $k:expr, $s:expr, $i:expr, $func:ident
    ) => ($buf.$a =
    $buf.$b + (($buf.$a + $func($buf.$b, $buf.$c, $buf.$d) + $x[$k] + $t[$i - 1]) << $s););
}

macro_rules! round1 {
    ($($x:tt)*) => (round!($($x)*, f));
}

macro_rules! round2 {
    ($($x:tt)*) => (round!($($x)*, g));
}

macro_rules! round3 {
    ($($x:tt)*) => (round!($($x)*, h));
}

macro_rules! round4 {
    ($($x:tt)*) => (round!($($x)*, i));
}

fn perform_rounds(buffer: DigestBuffer, vec: &mut Vec<u8>) -> DigestBuffer {
    let mut buf = buffer.clone();
    let t = build_table();

    for chunk in vec.chunks(64) {
        let prev_buf = buf.clone();

        let mut x = Vec::new();

        for four_bytes in chunk.chunks(4) {
            let mut c = Cursor::new(four_bytes);
            x.push(WrappingRotating(c.read_u32::<LittleEndian>().unwrap()));
        }

        round1!(buf, x, t, a, b, c, d, 0, 7, 1);
        round1!(buf, x, t, d, a, b, c, 1, 12, 2);
        round1!(buf, x, t, c, d, a, b, 2, 17, 3);
        round1!(buf, x, t, b, c, d, a, 3, 22, 4);

        round1!(buf, x, t, a, b, c, d, 4, 7, 5);
        round1!(buf, x, t, d, a, b, c, 5, 12, 6);
        round1!(buf, x, t, c, d, a, b, 6, 17, 7);
        round1!(buf, x, t, b, c, d, a, 7, 22, 8);

        round1!(buf, x, t, a, b, c, d, 8, 7, 9);
        round1!(buf, x, t, d, a, b, c, 9, 12, 10);
        round1!(buf, x, t, c, d, a, b, 10, 17, 11);
        round1!(buf, x, t, b, c, d, a, 11, 22, 12);

        round1!(buf, x, t, a, b, c, d, 12, 7, 13);
        round1!(buf, x, t, d, a, b, c, 13, 12, 14);
        round1!(buf, x, t, c, d, a, b, 14, 17, 15);
        round1!(buf, x, t, b, c, d, a, 15, 22, 16);

        round2!(buf, x, t, a, b, c, d, 1, 5, 17);
        round2!(buf, x, t, d, a, b, c, 6, 9, 18);
        round2!(buf, x, t, c, d, a, b, 11, 14, 19);
        round2!(buf, x, t, b, c, d, a, 0, 20, 20);

        round2!(buf, x, t, a, b, c, d, 5, 5, 21);
        round2!(buf, x, t, d, a, b, c, 10, 9, 22);
        round2!(buf, x, t, c, d, a, b, 15, 14, 23);
        round2!(buf, x, t, b, c, d, a, 4, 20, 24);

        round2!(buf, x, t, a, b, c, d, 9, 5, 25);
        round2!(buf, x, t, d, a, b, c, 14, 9, 26);
        round2!(buf, x, t, c, d, a, b, 3, 14, 27);
        round2!(buf, x, t, b, c, d, a, 8, 20, 28);

        round2!(buf, x, t, a, b, c, d, 13, 5, 29);
        round2!(buf, x, t, d, a, b, c, 2, 9, 30);
        round2!(buf, x, t, c, d, a, b, 7, 14, 31);
        round2!(buf, x, t, b, c, d, a, 12, 20, 32);

        round3!(buf, x, t, a, b, c, d, 5, 4, 33);
        round3!(buf, x, t, d, a, b, c, 8, 11, 34);
        round3!(buf, x, t, c, d, a, b, 11, 16, 35);
        round3!(buf, x, t, b, c, d, a, 14, 23, 36);

        round3!(buf, x, t, a, b, c, d, 1, 4, 37);
        round3!(buf, x, t, d, a, b, c, 4, 11, 38);
        round3!(buf, x, t, c, d, a, b, 7, 16, 39);
        round3!(buf, x, t, b, c, d, a, 10, 23, 40);

        round3!(buf, x, t, a, b, c, d, 13, 4, 41);
        round3!(buf, x, t, d, a, b, c, 0, 11, 42);
        round3!(buf, x, t, c, d, a, b, 3, 16, 43);
        round3!(buf, x, t, b, c, d, a, 6, 23, 44);

        round3!(buf, x, t, a, b, c, d, 9, 4, 45);
        round3!(buf, x, t, d, a, b, c, 12, 11, 46);
        round3!(buf, x, t, c, d, a, b, 15, 16, 47);
        round3!(buf, x, t, b, c, d, a, 2, 23, 48);

        round4!(buf, x, t, a, b, c, d, 0, 6, 49);
        round4!(buf, x, t, d, a, b, c, 7, 10, 50);
        round4!(buf, x, t, c, d, a, b, 14, 15, 51);
        round4!(buf, x, t, b, c, d, a, 5, 21, 52);

        round4!(buf, x, t, a, b, c, d, 12, 6, 53);
        round4!(buf, x, t, d, a, b, c, 3, 10, 54);
        round4!(buf, x, t, c, d, a, b, 10, 15, 55);
        round4!(buf, x, t, b, c, d, a, 1, 21, 56);

        round4!(buf, x, t, a, b, c, d, 8, 6, 57);
        round4!(buf, x, t, d, a, b, c, 15, 10, 58);
        round4!(buf, x, t, c, d, a, b, 6, 15, 59);
        round4!(buf, x, t, b, c, d, a, 13, 21, 60);

        round4!(buf, x, t, a, b, c, d, 4, 6, 61);
        round4!(buf, x, t, d, a, b, c, 11, 10, 62);
        round4!(buf, x, t, c, d, a, b, 2, 15, 63);
        round4!(buf, x, t, b, c, d, a, 9, 21, 64);

        buf = buf + prev_buf;
    }

    return buf.clone();
}

#[cfg(test)]
mod test {
    use super::*;
    use util::*;

    fn test_string_hash(input: &str, expected: &str) {
        let vec = input.as_bytes().to_vec();
        let mut output = &mut Vec::new();

        hash(vec, output);

        assert_eq!(to_hex_string(output), expected);
    }

    #[test]
    fn test_spec_testcases() {
        test_string_hash("", "d41d8cd98f00b204e9800998ecf8427e");
        test_string_hash("a", "0cc175b9c0f1b6a831c399e269772661");
        test_string_hash("abc", "900150983cd24fb0d6963f7d28e17f72");
        test_string_hash("message digest", "f96b697d7cb7938d525a2f31aaf161d0");
        test_string_hash("abcdefghijklmnopqrstuvwxyz",
                         "c3fcd3d76192e4007dfb496cca67e13b");
        test_string_hash("ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789",
                         "d174ab98d277d9f5a5611c2c9f419d9f");
        test_string_hash("1234567890\
                          1234567890\
                          1234567890\
                          1234567890\
                          1234567890\
                          1234567890\
                          1234567890\
                          1234567890",
                         "57edf4a22be3c955ac49da2e2107b67a");
    }
}
