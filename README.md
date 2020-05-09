[![Cargo](https://img.shields.io/crates/v/read-restrict.svg)][crate]
[![Documentation](https://docs.rs/read-restrict/badge.svg)][docs]
[![CI](https://github.com/Freaky/read-restrict/workflows/build/badge.svg)][ci]

# read-restrict

Enforce a strict limit on the number of bytes read from a `Read` with an error
when exceeded.

## Synopsis

```rust
pub trait ReadExt {
    fn restrict(self, restriction: u64) -> Restrict<Self>
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

This is a thin wrapper around `Read::take` which which returns an error when its
limit is exceeded.  Reads operate as normal, bound strictly to the read limit,
following which `io::ErrorKind::InvalidData` will be returned.

# Example

```rust
use std::io::{self, ErrorKind, Result};
use std::io::prelude::*;
use std::fs::File;
use read_restrict::ReadExt;

fn main() -> io::Result<()> {
    let f = File::open("foo.txt")?.restrict(5);
    let mut handle = f.restrict(5);
    let mut buf = [0; 8];
    assert_eq!(5, handle.read(&mut buf)?); // reads at most 5 bytes
    assert_eq!(0, handle.restriction()); // is now exhausted
    assert_eq!(ErrorKind::InvalidData, handle.read(&mut buf).unwrap_err().kind());
    Ok(())
}
```

[crate]: https://crates.io/crates/read-restrict
[docs]: https://docs.rs/read-restrict
[ci]: https://github.com/Freaky/read-restrict/actions?query=workflow%3Abuild
