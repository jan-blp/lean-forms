# Toolchains and the Wasm Lean runtime. CI caches their output keyed on this file, so keep anything else out.

LEAN_VERSION := 4.35.0
LEAN_SHA256 := 6747b099d03d3675f2716e7cf5924a16bfbf75822b13a3d36f51f933ffcc307b
EMSDK_VERSION := 7.0.0
EMSDK_SHA256 := b2d153874f97b3c41f76b91239407d124c8d22f60a5e1a3f0a4ebc92a44479e4

OUT := .lake/wasm
TOOLCHAINS := $(OUT)/toolchains
PREFIX := $(shell lean --print-prefix)
LEAN_TREE := $(TOOLCHAINS)/lean4-$(LEAN_VERSION)
SOURCE := $(LEAN_TREE)/src
EMSDK := $(TOOLCHAINS)/emsdk-$(EMSDK_VERSION)
SDK := $(EMSDK)/upstream/emscripten
PATCH := wasm/lean-$(LEAN_VERSION).patch
RUNTIME := $(OUT)/full-runtime-lean-$(LEAN_VERSION)-emsdk-$(EMSDK_VERSION)
LIBRARIES := $(addprefix $(RUNTIME)/lib/lean/,libInit.a libStd.a libLean.a libleancpp.a libleanrt.a) $(RUNTIME)/libuv/src/libuv/libuv.a

# Upstream's lean_initialize without initialize_Lean; linked first so it wins over libleancpp's.
MINIMAL_INIT := $(RUNTIME)/lib/lean/libinitialize_minimal.a

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
