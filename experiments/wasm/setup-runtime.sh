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
fetch "$cache/lean.tar.gz" \
  https://github.com/leanprover/lean4/archive/refs/tags/v4.34.1.tar.gz \
  9bb0bed7bae752a281e9923163d50da4193e36480cf5f639658e2e1502294056 lean4-4.34.1
"$cache/emsdk-4.0.23/emsdk" install 4.0.23
"$cache/emsdk-4.0.23/emsdk" activate 4.0.23
