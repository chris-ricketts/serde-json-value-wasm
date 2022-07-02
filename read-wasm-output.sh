#!/bin/bash

if ! command -v rustfilt &> /dev/null
then
    echo "Installing rustfilt..."
    cargo install rustfilt
    exit
fi

if ! command -v twiggy &> /dev/null
then
    echo "Installing twiggy..."
    cargo install twiggy
    exit
fi

echo "Building example wasm..."

cargo clean

cargo build --example pg --target wasm32-unknown-unknown --release

WASM=$(find target/ -iname "pg-*.wasm")

echo "Creating human readable wasm text from ${WASM}..."

rm -f target/pg.unmangle.wat

wasm-opt --print ${WASM} | rustfilt -o target/pg.unmangle.wat

echo "Human readable wasm text: target/pg.unmangle.wat"

twiggy paths ${WASM} > target/pg-call-paths.txt

echo "Call Path Analysis: target/pg-call-paths.txt"
