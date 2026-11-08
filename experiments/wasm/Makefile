# Run from the repository root: make -f experiments/wasm/Makefile [all|test|setup|size|size-gzip|size-brotli|ts-lines]
.DEFAULT_GOAL := all
.DELETE_ON_ERROR:

LEAN_VERSION := 4.35.0
LEAN_SHA256 := 6747b099d03d3675f2716e7cf5924a16bfbf75822b13a3d36f51f933ffcc307b
EMSDK_VERSION := 7.0.0
EMSDK_SHA256 := b2d153874f97b3c41f76b91239407d124c8d22f60a5e1a3f0a4ebc92a44479e4

OUT := .lake/wasm
WORK := $(OUT)/browser-build-$(EMSDK_VERSION)
TOOLCHAINS := $(OUT)/toolchains
PREFIX := $(shell lean --print-prefix)
LEAN_TREE := $(TOOLCHAINS)/lean4-$(LEAN_VERSION)
SOURCE := $(LEAN_TREE)/src
EMSDK := $(TOOLCHAINS)/emsdk-$(EMSDK_VERSION)
SDK := $(EMSDK)/upstream/emscripten
PATCH := experiments/wasm/lean-$(LEAN_VERSION).patch
RUNTIME := $(OUT)/full-runtime-$(EMSDK_VERSION)
MAKEFILE := experiments/wasm/Makefile
JOBS ?= 8
FLAGS := -O2 -DNDEBUG -DLEAN_EMSCRIPTEN -I$(RUNTIME)/include -pthread -fwasm-exceptions
LEAN_SOURCES := $(patsubst $(CURDIR)/%,%,$(shell cat .lake/build/browser-sources.txt 2>/dev/null))
LEAN_OBJECTS := $(addprefix $(WORK)/objects/,$(LEAN_SOURCES:.c=.o))
LIBRARIES := $(addprefix $(RUNTIME)/lib/lean/,libInit.a libStd.a libLean.a libleancpp.a libleanrt.a) $(RUNTIME)/libuv/src/libuv/libuv.a
# Upstream's lean_initialize without initialize_Lean; linked first so it wins over libleancpp's.
MINIMAL_INIT := $(RUNTIME)/lib/lean/libinitialize_minimal.a

.PHONY: all setup runtime-imports link test size size-gzip size-brotli ts-lines FORCE
# Lake writes the source list, so linking runs in a second pass that reads it.
all: runtime-imports $(MINIMAL_INIT) $(LIBRARIES)
	lake build browserSources
	$(MAKE) -f $(MAKEFILE) -j$(JOBS) link
	install -d web/dist/wasm
	install -m 644 $(OUT)/forms.mjs $(OUT)/forms.wasm web/dist/wasm/

runtime-imports:
	python3 experiments/wasm/prepare-runtime-imports.py

# Downloads roughly 470 MB; everything stays under the ignored .lake directory.
setup: $(LEAN_TREE)/.patched $(EMSDK)/.activated

$(TOOLCHAINS)/lean-$(LEAN_VERSION).tar.gz:
	@mkdir -p $(@D)
	curl -fL https://github.com/leanprover/lean4/archive/refs/tags/v$(LEAN_VERSION).tar.gz -o $@.part
	echo '$(LEAN_SHA256)  $@.part' | sha256sum --check
	mv $@.part $@

$(TOOLCHAINS)/emsdk-$(EMSDK_VERSION).tar.gz:
	@mkdir -p $(@D)
	curl -fL https://github.com/emscripten-core/emsdk/archive/refs/tags/$(EMSDK_VERSION).tar.gz -o $@.part
	echo '$(EMSDK_SHA256)  $@.part' | sha256sum --check
	mv $@.part $@

# Fix runtime FFI signatures and the layout of static scalar data on wasm32.
# The stamp holds the applied patch: checkouts reset the patch's mtime, so compare contents.
PATCH_CHANGED := $(shell cmp -s $(PATCH) $(LEAN_TREE)/.patched || echo FORCE)
$(LEAN_TREE)/.patched: $(TOOLCHAINS)/lean-$(LEAN_VERSION).tar.gz $(PATCH_CHANGED)
	rm -rf $(LEAN_TREE) $(LEAN_TREE).tmp
	mkdir $(LEAN_TREE).tmp
	tar -mxzf $< -C $(LEAN_TREE).tmp
	patch --batch -s -d $(LEAN_TREE).tmp/lean4-$(LEAN_VERSION) -p1 < $(PATCH)
	mv $(LEAN_TREE).tmp/lean4-$(LEAN_VERSION) $(LEAN_TREE)
	rmdir $(LEAN_TREE).tmp
	cp $(PATCH) $@

$(EMSDK)/.activated: $(TOOLCHAINS)/emsdk-$(EMSDK_VERSION).tar.gz
	tar -xzf $< -C $(TOOLCHAINS)
	$(EMSDK)/emsdk install $(EMSDK_VERSION)
	$(EMSDK)/emsdk activate $(EMSDK_VERSION)
	touch $@

# The upstream build owns the complete runtime and standard libraries.
$(MINIMAL_INIT) $(LIBRARIES) &: $(LEAN_TREE)/.patched $(EMSDK)/.activated
	@grep -q '^#define LEAN_VERSION_STRING "$(LEAN_VERSION)"' $(PREFIX)/include/lean/version.h || { echo 'This build requires Lean $(LEAN_VERSION).'; exit 1; }
	$(SDK)/emcmake cmake -S $(SOURCE) -B $(RUNTIME) -DSTAGE=1 -DPREV_STAGE=$(PREFIX) -DPREV_STAGE_CMAKE_EXECUTABLE_SUFFIX= -DUSE_GMP=OFF -DUSE_MIMALLOC=OFF -DMMAP=OFF -DUSE_LAKE=OFF -DUSE_GITHASH=OFF -DCMAKE_BUILD_TYPE=Release -DCCACHE=OFF
	cmake --build $(RUNTIME) --target leanrt leancpp initialize_minimal -j$(JOBS)
	$(MAKE) -C $(SOURCE) -f $(abspath $(RUNTIME))/stdlib.make -j$(JOBS) Lean
	touch $(MINIMAL_INIT) $(LIBRARIES)

$(WORK)/objects/%.o: %.c $(MAKEFILE)
	@mkdir -p $(@D)
	$(SDK)/emcc $(FLAGS) -MMD -MP -c $< -o $@

$(WORK)/forms-bridge.o: experiments/wasm/forms-bridge.cpp $(MAKEFILE)
	@mkdir -p $(@D)
	$(SDK)/em++ -std=c++20 $(FLAGS) -MMD -MP -c $< -o $@

-include $(LEAN_OBJECTS:.o=.d) $(WORK)/forms-bridge.d

FORCE:

link: $(OUT)/forms.mjs $(OUT)/forms.wasm
$(OUT)/forms.mjs $(OUT)/forms.wasm &: $(WORK)/forms-bridge.o $(LEAN_OBJECTS) $(MINIMAL_INIT) $(LIBRARIES) .lake/build/browser-sources.txt $(MAKEFILE)
	$(SDK)/em++ $(FLAGS) $(WORK)/forms-bridge.o $(LEAN_OBJECTS) $(MINIMAL_INIT) -Wl,--start-group $(LIBRARIES) -Wl,--end-group --no-entry -Wl,--fatal-warnings -sMODULARIZE -sEXPORT_ES6 -sENVIRONMENT=node,web,worker -sALLOW_MEMORY_GROWTH -sSTACK_SIZE=8388608 -sSTACK_OVERFLOW_CHECK=2 '-sEXPORTED_FUNCTIONS=["_forms_init","_forms_request","_forms_allocated_bytes"]' '-sEXPORTED_RUNTIME_METHODS=["ccall"]' -o $(OUT)/forms.mjs

test: all
	npm --prefix web test

# Report the existing binary without rebuilding it.
size:
	@python3 -c 'from pathlib import Path; import sys; p = Path("$(OUT)/forms.wasm"); p.is_file() or sys.exit("Wasm binary missing; run make -f $(MAKEFILE) first."); n = p.stat().st_size; print(f"{p}: {n / 1024:.2f} KiB ({n / 1048576:.2f} MiB)")'

# Measure deterministic gzip level 9 compression without writing an archive.
size-gzip:
	@python3 -c 'from pathlib import Path; import gzip, sys; p = Path("$(OUT)/forms.wasm"); p.is_file() or sys.exit("Wasm binary missing; run make -f $(MAKEFILE) first."); n = len(gzip.compress(p.read_bytes(), compresslevel=9, mtime=0)); print(f"{p} (gzip -9): {n / 1024:.2f} KiB ({n / 1048576:.2f} MiB)")'

# Measure Brotli quality 11 using Node.js without writing an archive.
size-brotli:
	@node --input-type=commonjs -e 'const fs = require("node:fs"), z = require("node:zlib"), p = "$(OUT)/forms.wasm"; if (!fs.existsSync(p)) { console.error("Wasm binary missing; run make -f $(MAKEFILE) first."); process.exit(1); } const n = z.brotliCompressSync(fs.readFileSync(p), { params: { [z.constants.BROTLI_PARAM_QUALITY]: 11 } }).length; console.log(p + " (Brotli quality 11): " + (n / 1024).toFixed(2) + " KiB (" + (n / 1048576).toFixed(2) + " MiB)");'

# Count physical source lines, including comments and blank lines.
ts-lines:
	@python3 -c 'from pathlib import Path; files = sorted(p for p in Path("web").rglob("*") if p.suffix in {".ts", ".tsx"} and not {"node_modules", "dist", "tests", "__tests__"}.intersection(p.parts) and not p.stem.endswith((".test", ".spec"))); counts = [(p, len(p.read_text().splitlines())) for p in files]; [print(f"{n:6} {p}") for p, n in counts]; print(f"{sum(n for _, n in counts):6} total")'
