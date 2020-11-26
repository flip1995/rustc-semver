#![no_std]
use core::{cmp::Ordering, convert::TryFrom, fmt::Display, num::ParseIntError};

#[derive(Debug, Eq, PartialEq, Copy, Clone)]
pub enum Error {
    TooManyElements,
    NotASpecialVersion,
    ParseIntError,
}

impl From<ParseIntError> for Error {
    fn from(_: ParseIntError) -> Self {
        Self::ParseIntError
    }
}

type Result<T> = core::result::Result<T, Error>;

#[derive(Debug, Eq, PartialEq, Copy, Clone)]
pub enum RustVersion {
    Normal { major: u32, minor: u32, patch: u32 },
    Special(SpecialVersion),
}

#[derive(Debug, Eq, PartialEq, Copy, Clone)]
pub enum SpecialVersion {
    Alpha,
    Alpha2,
    Beta,
}

impl PartialOrd for RustVersion {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for RustVersion {
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

impl Display for RustVersion {
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

impl TryFrom<[u32; 3]> for RustVersion {
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

impl RustVersion {
    pub const fn new(major: u32, minor: u32, patch: u32) -> Self {
        Self::Normal {
            major,
            minor,
            patch,
        }
    }

    pub fn parse(version: &str) -> Result<Self> {
        let special_version = ACCEPTED_SPECIAL_VERSIONS.iter().find_map(|sv| {
            if version == sv.0 {
                Some(sv.1)
            } else {
                None
            }
        });
        if let Some(special_version) = special_version {
            return Ok(RustVersion::Special(special_version));
        }

        let mut rust_version = [0_u32; 3];
        for (i, part) in version.split('.').enumerate() {
            if i == 3 {
                return Err(Error::TooManyElements);
            }
            match str::parse(part) {
                Ok(part) => rust_version[i] = part,
                Err(e) => {
                    if i == 2 {
                        return Err(Error::NotASpecialVersion);
                    } else {
                        return Err(e.into());
                    }
                }
            }
        }
        RustVersion::try_from(rust_version)
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn omitted_parts() {
        assert_eq!(
            RustVersion::parse("1.0.0").unwrap(),
            RustVersion::new(1, 0, 0)
        );
        assert_eq!(
            RustVersion::parse("1.0").unwrap(),
            RustVersion::new(1, 0, 0)
        );
        assert_eq!(RustVersion::parse("1").unwrap(), RustVersion::new(1, 0, 0));
    }

    #[test]
    fn special_versions() {
        assert_eq!(
            RustVersion::parse("1.0.0-alpha").unwrap(),
            RustVersion::Special(SpecialVersion::Alpha)
        );
        assert_eq!(
            RustVersion::parse("1.0.0-alpha.2").unwrap(),
            RustVersion::Special(SpecialVersion::Alpha2)
        );
        assert_eq!(
            RustVersion::parse("1.0.0-beta").unwrap(),
            RustVersion::Special(SpecialVersion::Beta)
        );
        assert_eq!(
            RustVersion::parse("1.0.0-sigma"),
            Err(Error::NotASpecialVersion)
        );
        assert_eq!(
            RustVersion::parse("1.0.0beta"),
            Err(Error::NotASpecialVersion)
        );
    }
}
