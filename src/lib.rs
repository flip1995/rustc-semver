#![no_std]
use core::{cmp::Ordering, convert::TryFrom, fmt::Display, num::ParseIntError};

/// `Error` represents an Error during parsing of a [`RustcVersion`].
#[derive(Debug, Eq, PartialEq, Copy, Clone)]
pub enum Error {
    /// A version was passed that has too many elements seperated by `'.'`.
    TooManyElements,
    /// A version was passed that neither is a [`SpecialVersion`], nor a
    /// normal [`RustcVersion`].
    NotASpecialVersion,
    /// A version was passed that has unallowed chracters.
    ParseIntError,
}

impl From<ParseIntError> for Error {
    fn from(_: ParseIntError) -> Self {
        Self::ParseIntError
    }
}

/// Result type for this crate
pub type Result<T> = core::result::Result<T, Error>;

/// `RustcVersion` represents a version of the Rust Compiler.
///
/// This struct only supports the version format
/// ```ignore
/// major.minor.patch
/// ```
/// and 3 special formats represented by the [`SpecialVersion`] enum.
///
/// A version can be created with one of the functions [`RustcVersion::new`] or
/// [`RustcVersion::parse`]. The [`RustcVersion::new`] method only supports the
/// normal version format.
#[derive(Debug, Eq, PartialEq, Copy, Clone)]
pub enum RustcVersion {
    Normal { major: u32, minor: u32, patch: u32 },
    Special(SpecialVersion),
}

/// `SpecialVersion` represents a special version from the first releases.
///
/// Before Rust 1.0.0, there were two alpha and one beta release, namely
///
/// - `1.0.0-alpha`
/// - `1.0.0-alpha.2`
/// - `1.0.0-beta`
///
/// This enum represents those releases.
#[derive(Debug, Eq, PartialEq, Copy, Clone)]
pub enum SpecialVersion {
    Alpha,
    Alpha2,
    Beta,
}

impl PartialOrd for RustcVersion {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for RustcVersion {
    fn cmp(&self, other: &Self) -> Ordering {
        match (self, other) {
            (
                Self::Normal {
                    major,
                    minor,
                    patch,
                },
                Self::Normal {
                    major: o_major,
                    minor: o_minor,
                    patch: o_patch,
                },
            ) => match major.cmp(&o_major) {
                Ordering::Equal => match minor.cmp(&o_minor) {
                    Ordering::Equal => patch.cmp(&o_patch),
                    ord => ord,
                },
                ord => ord,
            },
            (Self::Normal { major, .. }, Self::Special(_)) => {
                if *major >= 1 {
                    Ordering::Greater
                } else {
                    Ordering::Less
                }
            }
            (Self::Special(_), Self::Normal { major, .. }) => {
                if *major >= 1 {
                    Ordering::Less
                } else {
                    Ordering::Greater
                }
            }
            (Self::Special(s_ver), Self::Special(o_s_ver)) => s_ver.cmp(o_s_ver),
        }
    }
}

impl PartialOrd for SpecialVersion {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for SpecialVersion {
    fn cmp(&self, other: &Self) -> Ordering {
        match (self, other) {
            (Self::Alpha, Self::Alpha)
            | (Self::Alpha2, Self::Alpha2)
            | (Self::Beta, Self::Beta) => Ordering::Equal,
            (Self::Alpha, _) | (Self::Alpha2, Self::Beta) => Ordering::Less,
            (Self::Beta, _) | (Self::Alpha2, Self::Alpha) => Ordering::Greater,
        }
    }
}

impl Display for RustcVersion {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::Normal {
                major,
                minor,
                patch,
            } => write!(f, "{}.{}.{}", major, minor, patch)?,
            Self::Special(special) => write!(f, "{}", special)?,
        }

        Ok(())
    }
}

impl Display for SpecialVersion {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::Alpha => write!(f, "1.0.0-alpha")?,
            Self::Alpha2 => write!(f, "1.0.0-alpha.2")?,
            Self::Beta => write!(f, "1.0.0-beta")?,
        }

        Ok(())
    }
}

impl TryFrom<[u32; 3]> for RustcVersion {
    type Error = Error;

    fn try_from(vec: [u32; 3]) -> Result<Self> {
        if vec.len() > 3 {
            Err(Error::TooManyElements)
        } else {
            Ok(Self::Normal {
                major: vec.get(0).copied().unwrap_or_default(),
                minor: vec.get(1).copied().unwrap_or_default(),
                patch: vec.get(2).copied().unwrap_or_default(),
            })
        }
    }
}

const ACCEPTED_SPECIAL_VERSIONS: [(&str, SpecialVersion); 3] = [
    ("1.0.0-alpha", SpecialVersion::Alpha),
    ("1.0.0-alpha.2", SpecialVersion::Alpha2),
    ("1.0.0-beta", SpecialVersion::Beta),
];

impl RustcVersion {
    /// `RustcVersion::new` is a `const` constructor for a `RustcVersion`.
    ///
    /// This function is primarily used to construct constants, for everything
    /// else use [`RustcVersion::parse`].
    ///
    /// This function only allows to construct normal versions. For special
    /// versions, construct them directly from the [`SpecialVersion`] enum.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustc_semver::RustcVersion;
    ///
    /// const MY_FAVORITE_RUST: RustcVersion = RustcVersion::new(1, 48, 0);
    ///
    /// assert!(MY_FAVORITE_RUST > RustcVersion::new(1, 0, 0))
    /// ```
    pub const fn new(major: u32, minor: u32, patch: u32) -> Self {
        Self::Normal {
            major,
            minor,
            patch,
        }
    }

    /// `RustcVersion::parse` parses a [`RustcVersion`].
    ///
    /// This function can parse all normal and special versions. It is possbile
    /// to omit parts of the version, like the patch or minor version part. So
    /// `1`, `1.0`, and `1.0.0` are all valid inputs and will result in the
    /// same version.
    ///
    /// # Errors
    ///
    /// This function returns an [`Error`], if the passed string is not a valid
    /// [`RustcVersion`]
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustc_semver::{SpecialVersion, RustcVersion};
    ///
    /// let ver = RustcVersion::new(1, 0, 0);
    ///
    /// assert_eq!(RustcVersion::parse("1").unwrap(), ver);
    /// assert_eq!(RustcVersion::parse("1.0").unwrap(), ver);
    /// assert_eq!(RustcVersion::parse("1.0.0").unwrap(), ver);
    /// assert_eq!(
    ///     RustcVersion::parse("1.0.0-alpha").unwrap(),
    ///     RustcVersion::Special(SpecialVersion::Alpha)
    /// );
    /// ```
    pub fn parse(version: &str) -> Result<Self> {
        let special_version = ACCEPTED_SPECIAL_VERSIONS.iter().find_map(|sv| {
            if version == sv.0 {
                Some(sv.1)
            } else {
                None
            }
        });
        if let Some(special_version) = special_version {
            return Ok(RustcVersion::Special(special_version));
        }

        let mut rustc_version = [0_u32; 3];
        for (i, part) in version.split('.').enumerate() {
            let part = part.trim();
            if part.is_empty() {
                break;
            }
            if i == 3 {
                return Err(Error::TooManyElements);
            }
            match str::parse(part) {
                Ok(part) => rustc_version[i] = part,
                Err(e) => {
                    if i == 2 {
                        return Err(Error::NotASpecialVersion);
                    } else {
                        return Err(e.into());
                    }
                }
            }
        }
        RustcVersion::try_from(rustc_version)
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn omitted_parts() {
        assert_eq!(
            RustcVersion::parse("1.0.0").unwrap(),
            RustcVersion::new(1, 0, 0)
        );
        assert_eq!(
            RustcVersion::parse("1.0").unwrap(),
            RustcVersion::new(1, 0, 0)
        );
        assert_eq!(
            RustcVersion::parse("1").unwrap(),
            RustcVersion::new(1, 0, 0)
        );
    }

    #[test]
    fn special_versions() {
        assert_eq!(
            RustcVersion::parse("1.0.0-alpha").unwrap(),
            RustcVersion::Special(SpecialVersion::Alpha)
        );
        assert_eq!(
            RustcVersion::parse("1.0.0-alpha.2").unwrap(),
            RustcVersion::Special(SpecialVersion::Alpha2)
        );
        assert_eq!(
            RustcVersion::parse("1.0.0-beta").unwrap(),
            RustcVersion::Special(SpecialVersion::Beta)
        );
        assert_eq!(
            RustcVersion::parse("1.0.0-sigma"),
            Err(Error::NotASpecialVersion)
        );
        assert_eq!(
            RustcVersion::parse("1.0.0beta"),
            Err(Error::NotASpecialVersion)
        );
        assert_eq!(
            RustcVersion::parse("1.1.0-beta"),
            Err(Error::NotASpecialVersion)
        );
    }

    #[test]
    fn less_than() {
        let bigger = RustcVersion::new(1, 30, 1);
        assert!(RustcVersion::parse("1.0.0").unwrap() < bigger);
        assert!(RustcVersion::parse("1.0").unwrap() < bigger);
        assert!(RustcVersion::parse("1").unwrap() < bigger);
        assert!(RustcVersion::parse("1.30").unwrap() < bigger);
        assert!(RustcVersion::parse("1.0.0-beta").unwrap() < bigger);
        assert!(RustcVersion::parse("0.9").unwrap() < RustcVersion::Special(SpecialVersion::Alpha));
        assert!(
            RustcVersion::parse("1.0.0-alpha").unwrap()
                < RustcVersion::Special(SpecialVersion::Alpha2)
        );
        assert!(
            RustcVersion::parse("1.0.0-alpha").unwrap()
                < RustcVersion::Special(SpecialVersion::Beta)
        );
        assert!(
            RustcVersion::parse("1.0.0-alpha.2").unwrap()
                < RustcVersion::Special(SpecialVersion::Beta)
        );
    }

    #[test]
    fn equal() {
        assert_eq!(
            RustcVersion::parse("1.22.0").unwrap(),
            RustcVersion::new(1, 22, 0)
        );
        assert_eq!(
            RustcVersion::parse("1.22").unwrap(),
            RustcVersion::new(1, 22, 0)
        );
        assert_eq!(
            RustcVersion::parse("1.48.1").unwrap(),
            RustcVersion::new(1, 48, 1)
        );
    }

    #[test]
    fn greater_than() {
        let less = RustcVersion::new(1, 15, 1);
        assert!(RustcVersion::parse("1.16.0").unwrap() > less);
        assert!(RustcVersion::parse("1.16").unwrap() > less);
        assert!(RustcVersion::parse("2").unwrap() > less);
        assert!(RustcVersion::parse("1.15.2").unwrap() > less);
        assert!(
            RustcVersion::parse("1.0.0-beta").unwrap()
                > RustcVersion::Special(SpecialVersion::Alpha2)
        );
        assert!(
            RustcVersion::parse("1.0.0-beta").unwrap()
                > RustcVersion::Special(SpecialVersion::Alpha)
        );
        assert!(
            RustcVersion::parse("1.0.0-alpha.2").unwrap()
                > RustcVersion::Special(SpecialVersion::Alpha)
        );
    }

    #[test]
    fn edge_cases() {
        assert_eq!(RustcVersion::parse("").unwrap(), RustcVersion::new(0, 0, 0));
        assert_eq!(
            RustcVersion::parse(" ").unwrap(),
            RustcVersion::new(0, 0, 0)
        );
        assert_eq!(
            RustcVersion::parse("\t").unwrap(),
            RustcVersion::new(0, 0, 0)
        );
        assert_eq!(
            RustcVersion::parse(" 1  . \t 3.\r 5").unwrap(),
            RustcVersion::new(1, 3, 5)
        );
    }
}
