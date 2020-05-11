//! # read-restrict
//!
//! An adaptor around Rust's standard [`io::Take`] which returns an error of
//! of the kind [`ErrorKind::InvalidData`]  when the limit is exceeded.
//!
//! This may be useful for enforcing resource limits while not silently
//! truncating when they are exceeded.
//!
//! # Example
//!
//! ```no_run
//! use std::io::{self, ErrorKind, Result};
//! use std::io::prelude::*;
//! use std::fs::File;
//! use read_restrict::ReadExt;
//!
//! fn main() -> io::Result<()> {
//!     let f = File::open("foo.txt")?.restrict(5);
//!     let mut handle = f.restrict(5);
//!
//!     let mut buf = [0; 8];
//!     assert_eq!(5, handle.read(&mut buf)?); // reads at most 5 bytes
//!     assert_eq!(0, handle.restriction()); // is now exhausted
//!     assert_eq!(ErrorKind::InvalidData, handle.read(&mut buf).unwrap_err().kind());
//!     Ok(())
//! }
//! ```
//!
//! [`io::Take`]: https://doc.rust-lang.org/std/io/struct.Take.html
//! [`ErrorKind::InvalidData`]: https://doc.rust-lang.org/std/io/enum.ErrorKind.html#variant.InvalidData

use std::io::{self, BufRead, Read, Result, Take};

pub trait ReadExt {
    fn restrict(self, restriction: u64) -> Restrict<Self>
    where
        Self: Sized + Read,
    {
        Restrict {
            inner: self.take(restriction),
        }
    }
}

impl<R: Read> ReadExt for R {}

/// Reader adaptor which restricts the bytes read from an underlying reader,
/// returning an IO error of the kind [`ErrorKind::InvalidData`] when it is exceeded.
///
/// This struct is generally created by calling [`restrict`] on a reader.
/// Please see the documentation of [`restrict`] for more details.
///
/// [`restrict`]: trait.ReadExt.html#method.restrict
/// [`ErrorKind::InvalidData`]: https://doc.rust-lang.org/std/io/enum.ErrorKind.html#variant.InvalidData
#[derive(Debug)]
pub struct Restrict<T> {
    inner: Take<T>,
}

impl<T> Restrict<T> {
    /// Returns the number of bytes that can be read before this instance will
    /// return an error.
    ///
    /// # Examples
    ///
    /// ```no_run
    /// use std::io;
    /// use std::io::prelude::*;
    /// use read_restrict::ReadExt;
    /// use std::fs::File;
    ///
    /// fn main() -> io::Result<()> {
    ///     let f = File::open("foo.txt")?;
    ///
    ///     // read at most five bytes
    ///     let handle = f.restrict(5);
    ///
    ///     println!("restriction: {}", handle.restriction());
    ///     Ok(())
    /// }
    /// ```
    pub fn restriction(&self) -> u64 {
        self.inner.limit()
    }

    /// Sets the number of bytes that can be read before this instance will
    /// return an error. This is the same as constructing a new `Restrict` instance, so
    /// the amount of bytes read and the previous restriction value don't matter when
    /// calling this method.
    ///
    /// # Examples
    ///
    /// ```no_run
    /// use std::io;
    /// use std::io::prelude::*;
    /// use std::fs::File;
    /// use read_restrict::ReadExt;
    ///
    /// fn main() -> io::Result<()> {
    ///     let f = File::open("foo.txt")?;
    ///
    ///     // read at most five bytes
    ///     let mut handle = f.restrict(5);
    ///     handle.set_restriction(10);
    ///
    ///     assert_eq!(handle.restriction(), 10);
    ///     Ok(())
    /// }
    /// ```
    pub fn set_restriction(&mut self, restriction: u64) {
        self.inner.set_limit(restriction);
    }

    /// Consumes the `Restrict`, returning the wrapped reader.
    ///
    /// # Examples
    ///
    /// ```no_run
    /// use std::io;
    /// use std::io::prelude::*;
    /// use std::fs::File;
    /// use read_restrict::ReadExt;
    ///
    /// fn main() -> io::Result<()> {
    ///     let mut file = File::open("foo.txt")?;
    ///
    ///     let mut buffer = [0; 5];
    ///     let mut handle = file.restrict(5);
    ///     handle.read(&mut buffer)?;
    ///
    ///     let file = handle.into_inner();
    ///     Ok(())
    /// }
    /// ```
    pub fn into_inner(self) -> T {
        self.inner.into_inner()
    }

    /// Gets a reference to the underlying reader.
    ///
    /// # Examples
    ///
    /// ```no_run
    /// use std::io;
    /// use std::io::prelude::*;
    /// use std::fs::File;
    /// use read_restrict::ReadExt;
    ///
    /// fn main() -> io::Result<()> {
    ///     let mut file = File::open("foo.txt")?;
    ///
    ///     let mut buffer = [0; 5];
    ///     let mut handle = file.restrict(5);
    ///     handle.read(&mut buffer)?;
    ///
    ///     let file = handle.get_ref();
    ///     Ok(())
    /// }
    /// ```
    pub fn get_ref(&self) -> &T {
        self.inner.get_ref()
    }

    /// Gets a mutable reference to the underlying reader.
    ///
    /// Care should be taken to avoid modifying the internal I/O state of the
    /// underlying reader as doing so may corrupt the internal restrict of this
    /// `Restrict`.
    ///
    /// # Examples
    ///
    /// ```no_run
    /// use std::io;
    /// use std::io::prelude::*;
    /// use std::fs::File;
    /// use read_restrict::ReadExt;
    ///
    /// fn main() -> io::Result<()> {
    ///     let mut file = File::open("foo.txt")?;
    ///
    ///     let mut buffer = [0; 5];
    ///     let mut handle = file.restrict(5);
    ///     handle.read(&mut buffer)?;
    ///
    ///     let file = handle.get_mut();
    ///     Ok(())
    /// }
    /// ```
    pub fn get_mut(&mut self) -> &mut T {
        self.inner.get_mut()
    }
}

impl<T: Read> Read for Restrict<T> {
    fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
        if self.restriction() == 0 {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "Read restriction exceeded",
            ));
        }

        self.inner.read(&mut buf[..])
    }
}

impl<T: BufRead> BufRead for Restrict<T> {
    fn fill_buf(&mut self) -> Result<&[u8]> {
        if self.restriction() == 0 {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "Read restriction exceeded",
            ));
        }

        self.inner.fill_buf()
    }

    fn consume(&mut self, amt: usize) {
        self.inner.consume(amt);
    }
}

#[cfg(test)]
mod tests {
    use super::ReadExt;
    use std::io::{self, BufRead, BufReader, Read};

    #[test]
    fn restrict() {
        let mut f = std::fs::File::open("Cargo.toml").unwrap().restrict(4);

        let mut buf = [0; 5];
        assert_eq!(4, f.read(&mut buf).unwrap());
        assert_eq!(b"[pac", &buf[0..4]);
        assert_eq!(
            io::ErrorKind::InvalidData,
            f.read(&mut buf).unwrap_err().kind()
        );

        let mut f = BufReader::new(f.into_inner()).restrict(4);
        assert_eq!(b"kage", f.fill_buf().unwrap());
        f.consume(4);
        assert_eq!(io::ErrorKind::InvalidData, f.fill_buf().unwrap_err().kind());
    }

    #[test]
    fn restrict_err() {
        struct R;

        impl Read for R {
            fn read(&mut self, _: &mut [u8]) -> io::Result<usize> {
                Err(io::Error::new(io::ErrorKind::Other, ""))
            }
        }
        impl BufRead for R {
            fn fill_buf(&mut self) -> io::Result<&[u8]> {
                Err(io::Error::new(io::ErrorKind::Other, ""))
            }
            fn consume(&mut self, _amt: usize) {}
        }

        let mut buf = [0; 1];
        assert_eq!(
            io::ErrorKind::InvalidData,
            R.restrict(0).read(&mut buf).unwrap_err().kind()
        );
        assert_eq!(
            io::ErrorKind::InvalidData,
            R.restrict(0).fill_buf().unwrap_err().kind()
        );
    }
}
