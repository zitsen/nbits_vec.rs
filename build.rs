use std::env;
use std::fs::File;
use std::io::Write;
use std::path::Path;

fn main() {
    let out_dir = env::var("OUT_DIR").unwrap();
    let dest = Path::new(&out_dir).join("consts.rs");
    let mut f = File::create(&dest).unwrap();

    writeln!(f, "use super::value::{{Value, ValueExt, OneBit, Aligned}};").unwrap();

    for i in 1..64u32 {
        if i == 8 || i == 16 || i == 32 {
            continue;
        }
        for j in vec![8, 16, 32, 64] {
            if i < j {
                let ty = format!("N{}B{}", i, j);
                writeln!(f,
                         "pub enum {ty} {{ }}
impl Value for {ty} {{
    type Block = u{block};
    #[inline]
    fn nbits() -> usize {{ {n} }}
}}
impl ValueExt for {ty} {{}}",
                         ty = ty,
                         n = i,
                         block = j)
                    .unwrap();

                if i == 1 {
                    writeln!(f, "impl OneBit for {} {{}}", ty).unwrap();
                }
                if j % i == 0 {
                    writeln!(f, "impl Aligned for {} {{}}", ty).unwrap();
                }
            }
        }
    }
}
