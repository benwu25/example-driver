# Usage
- Clone repo
- Install nightly Rust toolchain via `rustup toolchain install nightly`
- Build the driver binary via `cargo +nightly build`, it will be stored in target/debug

Use the driver to build a Rust crate via the command:

`RUSTC=/path/to/example-driver/target/debug/example-driver cargo +nightly build`
