use core::{
    cmp::Ordering,
    convert::{TryFrom, TryInto},
    fmt::Display,
    num::ParseIntError,
};

#[derive(Debug)]
pub enum Error {
    TooManyElements,
    TooFewElements,
    TooManyElementsInRest,
    RestOnNonZeroPatch,
    ParseIntError,
}

impl From<ParseIntError> for Error {
    fn from(_: ParseIntError) -> Self {
        Self::ParseIntError
    }
}

type Result<T> = core::result::Result<T, Error>;

#[derive(Debug, Default, Eq, PartialEq)]
pub struct RustVersion<'a> {
    major: u32,
    minor: Option<u32>,
    patch: Option<u32>,
    rest: Option<&'a str>,
}

impl PartialOrd for RustVersion<'_> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for RustVersion<'_> {
    fn cmp(&self, other: &Self) -> Ordering {
        match self.major.cmp(&other.major) {
            Ordering::Equal => match (self.minor, other.minor) {
                (Some(minor), Some(o_minor)) => match minor.cmp(&o_minor) {
                    Ordering::Equal => match (self.patch, other.patch) {
                        (Some(patch), Some(o_patch)) => match patch.cmp(&o_patch) {
                            Ordering::Equal if patch == 0 => match (self.rest, other.rest) {
                                (Some(rest), Some(o_rest)) if rest == o_rest => Ordering::Equal,
                                (Some(rest), Some(o_rest)) => match (rest, o_rest) {
                                    ("alpha", _) | ("alpha.2", "beta") => Ordering::Less,
                                    ("beta", _) | ("alpha.2", "alpha") => Ordering::Greater,
                                    _ => {
                                        unreachable!("This was already checked in the constructors")
                                    }
                                },
                                (Some(_), None) => Ordering::Less,
                                (None, Some(_)) => Ordering::Greater,
                                (None, None) => Ordering::Equal,
                            },
                            o @ _ => o,
                        },
                        (Some(patch), None) => patch.cmp(&0),
                        (None, Some(patch)) => 0.cmp(&patch),
                        (None, None) => Ordering::Equal,
                    },
                    o @ _ => o,
                },
                (Some(minor), None) => minor.cmp(&0),
                (None, Some(minor)) => 0.cmp(&minor),
                (None, None) => Ordering::Equal,
            },
            o @ _ => o,
        }
    }
}

impl Display for RustVersion<'_> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        if let Some(rest) = self.rest {
            write!(
                f,
                "{}.{}.{}-{}",
                self.major,
                self.minor.unwrap_or(0),
                self.patch.unwrap_or(0),
                rest
            )?;
        } else {
            write!(
                f,
                "{}.{}.{}",
                self.major,
                self.minor.unwrap_or(0),
                self.patch.unwrap_or(0)
            )?;
        }
        Ok(())
    }
}

impl TryFrom<Vec<u32>> for RustVersion<'_> {
    type Error = Error;

    fn try_from(arr: Vec<u32>) -> Result<Self> {
        if arr.len() > 3 {
            Err(Error::TooManyElements)
        } else if arr.is_empty() {
            Err(Error::TooFewElements)
        } else {
            Ok(Self {
                major: arr[0],
                minor: arr.get(1).copied(),
                patch: arr.get(2).copied(),
                rest: None,
            })
        }
    }
}

const ACCEPTED_REST: [&str; 3] = ["alpha", "alpha.2", "beta"];

impl<'a> RustVersion<'a> {
    pub const fn new(major: u32, minor: u32, patch: u32) -> Self {
        Self {
            major,
            minor: Some(minor),
            patch: Some(patch),
            rest: None,
        }
    }

    pub fn new_with_rest(major: u32, minor: u32, patch: u32, rest: &'a str) -> Result<Self> {
        if !ACCEPTED_REST.contains(&rest) || patch != 0 {
            return Err(Error::RestOnNonZeroPatch);
        }
        Ok(Self {
            major,
            minor: Some(minor),
            patch: Some(patch),
            rest: Some(rest),
        })
    }

    pub fn parse(version: &'a str) -> Result<Self> {
        let mut rust_version = vec![];
        let mut version_rest = None;
        for (i, part) in version.split('.').enumerate() {
            if i == 3 {
                return Err(Error::TooManyElements);
            }
            if i == 2 {
                let mut patch_and_rest = part.split('-');
                let patch = patch_and_rest.next();
                let rest = patch_and_rest.next();
                if patch_and_rest.next().is_some() {
                    return Err(Error::TooManyElementsInRest);
                }
                if let Some(patch) = patch {
                    let patch = str::parse(patch)?;
                    rust_version.push(patch);
                    if let Some(rest) = rest {
                        if !ACCEPTED_REST.contains(&rest) || patch != 0 {
                            return Err(Error::RestOnNonZeroPatch);
                        }
                        version_rest = Some(rest);
                    }
                }
            } else {
                rust_version.push(str::parse(part)?);
            }
        }
        let mut rust_version: Self = rust_version.try_into()?;
        rust_version.rest = version_rest;
        Ok(rust_version)
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test() {
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
}
