#!/usr/bin/env bash
# Fail if a Wasm binary links Lean's libuv stubs, which abort when called in the browser.
set -euo pipefail

# Assertion text of every stub, e.g.
# https://github.com/leanprover/lean4/blob/v4.35.0/src/runtime/uv/tcp.cpp#L768-L778
STUB='Please build a version of Lean4 with libuv'

if (($# != 1)); then
    echo "usage: $0 WASM" >&2
    exit 2
fi
wasm=$1
if [[ ! -f $wasm ]]; then
    echo "$wasm: no such file" >&2
    exit 2
fi

if grep -qaF "$STUB" "$wasm"; then
    echo "$wasm links libuv stubs that abort in the browser:" >&2
    grep -aoE 'runtime/uv/[a-z_]+\.cpp' "$wasm" | sort -u >&2 || true
    exit 1
fi
