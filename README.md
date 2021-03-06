[![Cargo](https://img.shields.io/crates/v/read-restrict.svg)][crate]
[![Documentation](https://docs.rs/read-restrict/badge.svg)][docs]
[![CI](https://github.com/Freaky/read-restrict/workflows/build/badge.svg)][ci]

# read-restrict

Enforce a strict limit on the number of bytes read from a `Read` with an error
when exceeded.

## Synopsis

```rust
pub fn read<P: AsRef<Path>>(path: P, restriction: usize) -> io::Result<Vec<u8>>;
pub fn read_to_string<P: AsRef<Path>>(path: P, restriction: usize) -> io::Result<String>;

pub trait ReadExt {
    fn restrict(self, restriction: u64) -> Restrict<Self>;
}

impl<R: Read> ReadExt for R {}

impl<T> Restrict<T> {
    pub fn restriction(&self) -> u64;
    pub fn set_restriction(&mut self, restriction: u64);
    pub fn into_inner(self) -> T;
    pub fn get_ref(&self) -> &T;
    pub fn get_mut(&mut self) -> &mut T;
}

impl<T: Read> Read for Restrict<T> {}
impl<T: BufRead> BufRead for Restrict<T> {}
```

## Description

An adaptor around Rust's standard [`io::Take`] which instead of returning
`Ok(0)` when the read limit is exceeded, instead returns an error of of the kind
[`ErrorKind::InvalidData`].

This is intended for enforcing explicit input limits when simply truncating with
`take` could result in incorrect behaviour.

`read_restrict` also offers restricted variants of [`std::fs::read`] and
[`std::fs::read_to_string`], to conveniently prevent unbounded reads of
overly-large files.

## Example

```rust
use std::io::{Read, Result, ErrorKind};
use read_restrict::ReadExt;

fn main() -> Result<()> {
    let f = std::fs::File::open("foo.txt")?;
    let mut handle = f.restrict(5);
    let mut buf = [0; 8];
    assert_eq!(5, handle.read(&mut buf)?); // reads at most 5 bytes
    assert_eq!(0, handle.restriction()); // is now exhausted
    assert_eq!(ErrorKind::InvalidData, handle.read(&mut buf).unwrap_err().kind());
    Ok(())
}
```

Or more realistically:

```rust
use read_restrict::ReadExt;

fn main() -> std::io::Result<()> {
    let input = std::fs::File::open("foo.json")?;
    let input = std::io::BufReader::new(input); // buffer for performance
    let input = input.restrict(640 * 1024); // 640k should be enough JSON for anyone
    let _data = serde_json::from_reader(input)?;
    Ok(())
}
```

Or even better:

```rust
fn main() -> std::io::Result<()> {
    let input = read_restrict::read_to_string("foo.json", 640 * 1024)?;
    let _data = serde_json::from_str(input)?;
    Ok(())
}
```

[crate]: https://crates.io/crates/read-restrict
[docs]: https://docs.rs/read-restrict
[ci]: https://github.com/Freaky/read-restrict/actions?query=workflow%3Abuild
[`io::Take`]: https://doc.rust-lang.org/std/io/struct.Take.html
[`ErrorKind::InvalidData`]: https://doc.rust-lang.org/std/io/enum.ErrorKind.html#variant.InvalidData
[`std::fs::read`]: https://doc.rust-lang.org/std/fs/fn.read.html
[`std::fs::read_to_string`]: https://doc.rust-lang.org/std/fs/fn.read_to_string.html