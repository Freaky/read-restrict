//! # read-restrict
//!
//! An adaptor around Rust's standard [`io::Take`] which instead of returning
//! `Ok(0)` when the read limit is exceeded, instead returns an error of of the kind
//! [`ErrorKind::InvalidData`].
//!
//! This is intended for enforcing explicit input limits when simply truncating with
//! `take` could result in incorrect behaviour.
//!
//! `read_restrict` also offers restricted variants of
//! [`std::fs::read`](std::fs::read) and
//! [`std::fs::read_to_string`](std::fs::read_to_string), to conveniently
//! prevent unbounded reads of overly-large files.
//!
//! # Examples
//!
//! ```no_run
//! use std::io::{self, Read, ErrorKind};
//!
//! use read_restrict::ReadExt;
//!
//! fn main() -> io::Result<()> {
//!     let f = std::fs::File::open("foo.txt")?;
//!     let mut handle = f.restrict(5);
//!     let mut buf = [0; 8];
//!     assert_eq!(5, handle.read(&mut buf)?); // reads at most 5 bytes
//!     assert_eq!(0, handle.restriction()); // is now exhausted
//!     assert_eq!(ErrorKind::InvalidData, handle.read(&mut buf).unwrap_err().kind());
//!     Ok(())
//! }
//! ```
//!
//! ```no_run
//! fn load_config(path: &std::path::Path) -> std::io::Result<String> {
//!     // No sensible configuration is going to exceed 640 KiB
//!     let conf = read_restrict::read_to_string(&path, 640 * 1024)?;
//!     // probably want to parse it here
//!     Ok(conf)
//! }
//! ```
//!
//! [`io::Take`]: https://doc.rust-lang.org/std/io/struct.Take.html
//! [`ErrorKind::InvalidData`]: https://doc.rust-lang.org/std/io/enum.ErrorKind.html#variant.InvalidData

use std::fs::File;
use std::io::{self, BufRead, Read, Result, Take};
use std::path::Path;

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
    /// underlying reader as doing so may corrupt the internal limit of this
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
        if !buf.is_empty() && self.restriction() == 0 {
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

/// Provided the file at `path` fits within the specified limit, pass a
/// restricted read handle and a suitable initial buffer size to the closure
/// and return its result.
fn open_with_restriction<F, T>(path: &Path, restriction: usize, f: F) -> io::Result<T>
where
    F: FnOnce(Restrict<File>, usize) -> io::Result<T>,
{
    let file = File::open(path)?;
    let size = match file.metadata().map(|m| m.len()) {
        Ok(size) if size > restriction as u64 => {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "File exceeds size restriction",
            ))
        }
        Ok(size) => (size as usize).saturating_add(1),
        Err(_) => 0,
    };
    f(file.restrict(restriction as u64 + 1), size)
}

/// Read the entire contents of a file into a bytes vector, provided it fits
/// within a specified size limit.
///
/// This is a restricted alternative to [`std::fs::read`](std::fs::read)
/// with otherwise identical semantics.
///
/// # Examples
///
/// ```no_run
/// fn main() -> std::io::Result<()> {
///     let vec_at_most_64_bytes = read_restrict::read("foo.txt", 64)?;
///     Ok(())
/// }
/// ```
pub fn read<P: AsRef<Path>>(path: P, restriction: usize) -> io::Result<Vec<u8>> {
    open_with_restriction(path.as_ref(), restriction, |mut file, size| {
        let mut bytes = Vec::with_capacity(size);
        file.read_to_end(&mut bytes)?;
        Ok(bytes)
    })
}

/// Read the entire contents of a file into a string, provided it fits within a
/// specified size limit.
///
/// This is a restricted alternative to [`std::fs::read_to_string`](std::fs::read_to_string)
/// with otherwise identical semantics.
///
/// # Examples
///
/// ```no_run
/// fn main() -> std::io::Result<()> {
///     let string_at_most_64_bytes = read_restrict::read_to_string("foo.txt", 64)?;
///     Ok(())
/// }
/// ```
pub fn read_to_string<P: AsRef<Path>>(path: P, restriction: usize) -> io::Result<String> {
    open_with_restriction(path.as_ref(), restriction, |mut file, size| {
        let mut string = String::with_capacity(size);
        file.read_to_string(&mut string)?;
        Ok(string)
    })
}

#[cfg(test)]
mod tests {
    use super::{read, read_to_string, ReadExt};
    use std::io::{self, BufRead, BufReader, Cursor, Read};

    #[test]
    fn test_read() {
        let path = "Cargo.toml";
        let size = std::fs::metadata(&path).unwrap().len() as usize;

        assert_eq!(size, read(&path, size).unwrap().len());

        assert_eq!(
            io::ErrorKind::InvalidData,
            read(&path, size - 1).unwrap_err().kind()
        );
    }

    #[test]
    fn test_read_to_string() {
        let path = "Cargo.toml";
        let size = std::fs::metadata(&path).unwrap().len() as usize;

        assert_eq!(size, read_to_string(&path, size).unwrap().len());

        assert_eq!(
            io::ErrorKind::InvalidData,
            read_to_string(&path, size - 1).unwrap_err().kind()
        );
    }

    #[test]
    fn restrict() {
        let data = b"Stupidity is the same as evil if you judge by the results";
        let mut f = Cursor::new(&data[..]).restrict(0);

        // empty reads always succeed
        let mut buf = [0; 0];
        assert_eq!(0, f.read(&mut buf).unwrap());

        let mut buf = [0; 1];
        assert_eq!(
            io::ErrorKind::InvalidData,
            f.read(&mut buf).unwrap_err().kind()
        );

        // restriction can be dynamically adjusted
        f.set_restriction(6);
        let mut buf = [0; 8];
        assert_eq!(6, f.read(&mut buf).unwrap());
        assert_eq!(b"Stupid", &buf[..6]);
        assert_eq!(
            io::ErrorKind::InvalidData,
            f.read(&mut buf).unwrap_err().kind()
        );

        // and leaves the reader in a consistent position
        let mut f = BufReader::new(f.into_inner()).restrict(3);
        assert_eq!(b"ity", f.fill_buf().unwrap());
        f.consume(3);
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
