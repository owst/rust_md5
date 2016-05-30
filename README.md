`rust_md5`
===============

This is a very simple implementation of the [md5 specification - RFC 1321][md5]
used to begin learning Rust. In particular, it makes no attempt to be
efficient, e.g., it reads all the input data before starting processing, rather
than streaming.

## Usage

First, build the project with `cargo build`. It mimics the usage of `md5sum`
thusly:

```
> echo 'hi there' | ./target/debug/rust_md5
12f6bb1941df66b8f138a446d4e8670c -
```

or

```
> echo 'unicode, ok ✔' > file.txt
> ./target/debug/rust_md5 file.txt
34a7fafe48ccb9d3f18f09949cbfa96f file.txt
```

There are some simple test cases taken from the specification, which can be
executed with `cargo test`.

[md5]: https://www.ietf.org/rfc/rfc1321.txt 
