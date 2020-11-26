# Rust Version

This crate provides a parser for Rust versions.

## Description

The parser will only accept Versions in the form
```
<major>.<minor>.<patch>
```
and 3 special versions:

- `1.0.0-alpha`
- `1.0.0-alpha.2`
- `1.0.0-beta`

## Usage

There are only 2 functions to create a `RustVersion`:

1. `const RustVersion::new(u32, u32, u32)`: This is mainly used to create
   constants
2. `RustVersion::parse(&str)`: Usually you want to parse a version with this
   function

If you have a `RustVersion` you can compare them, like you would expect:

```
assert!(RustVersion::parse("1.42.0")? < RustVersion::parse("1.43")?);
```

## Code of Conduct

This repository adopts the [Contributor Covenant Code of
Conduct](https://www.contributor-covenant.org/version/1/4/code-of-conduct/)

## License

Copyright 2020 Philipp Krones

Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
https://www.apache.org/licenses/LICENSE-2.0> or the MIT license <LICENSE-MIT or
https://opensource.org/licenses/MIT>, at your option. Files in the project may
not be copied, modified, or distributed except according to those terms.
