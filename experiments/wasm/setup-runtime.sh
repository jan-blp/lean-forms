#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/../.."

# Downloads roughly 470 MB; everything stays under the ignored .lake directory.
# Pinned to this experiment's compiler/runtime and Emscripten versions.
cache=.lake/wasm/toolchains
mkdir -p "$cache"
fetch() {
  local archive=$1 url=$2 digest=$3 directory=$4
  if [[ ! -f "$archive" ]]; then
    curl -fL "$url" -o "$archive.part"
    mv "$archive.part" "$archive"
  fi
  printf '%s  %s\n' "$digest" "$archive" | sha256sum --check
  if [[ ! -d "$cache/$directory" ]]; then
    tar -xzf "$archive" -C "$cache"
  fi
}
fetch "$cache/emsdk.tar.gz" \
  https://github.com/emscripten-core/emsdk/archive/refs/tags/4.0.23.tar.gz \
  a91a4c1f42dbb0345faac093161e27d43e9b6964840d8c8d80976ab8d3eaf2d3 emsdk-4.0.23
fetch "$cache/lean-4.35.0.tar.gz" \
  https://github.com/leanprover/lean4/archive/refs/tags/v4.35.0.tar.gz \
  6747b099d03d3675f2716e7cf5924a16bfbf75822b13a3d36f51f933ffcc307b lean4-4.35.0
# Fix runtime FFI signatures and the layout of static scalar data on wasm32.
if patch --dry-run --forward --batch -s -d "$cache/lean4-4.35.0" -p1 < experiments/wasm/lean-4.35.0.patch; then
  patch --forward --batch -s -d "$cache/lean4-4.35.0" -p1 < experiments/wasm/lean-4.35.0.patch
else
  patch --dry-run -R --batch -s -d "$cache/lean4-4.35.0" -p1 < experiments/wasm/lean-4.35.0.patch
fi
"$cache/emsdk-4.0.23/emsdk" install 4.0.23
"$cache/emsdk-4.0.23/emsdk" activate 4.0.23
