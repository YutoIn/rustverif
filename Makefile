RUST_LIB_PATH = $(shell rustc --print target-libdir)

file = "./src/main.rs"

all:
	cargo run $(file) -L $(RUST_LIB_PATH)
