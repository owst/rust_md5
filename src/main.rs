#[macro_use]
extern crate custom_derive;
#[macro_use]
extern crate newtype_derive;

use std::env;
use std::fs::File;
use std::io;
use std::io::prelude::*;

mod md5;
mod util;

fn process_input<R>(filename: &String, input: R)
    where R: Read
{
    let mut input = input;
    let mut data = Vec::new();

    if let Err(x) = input.read_to_end(&mut data) {
        panic!("Can't read: {}", x);
    }

    let mut hash_vec = &mut Vec::new();
    md5::hash(data, hash_vec);

    let mut out = io::stdout();
    out.write(&util::to_hex_string(hash_vec).into_bytes()).unwrap();
    out.write(&format!(" {}\n", filename).into_bytes()).unwrap();
    out.flush().unwrap();
}

fn main() {
    let mut args: Vec<_> = env::args().collect();

    if args.len() == 1 {
        process_input(&"-".to_string(), io::stdin());
    } else {
        let filename = args.remove(1);

        if filename == "-" {
            process_input(&filename, io::stdin());
        } else {
            process_input(&filename, File::open(&filename).unwrap());
        };
    }
}
