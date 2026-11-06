# Run from the repository root: make -f experiments/wasm/Makefile [all|test|setup]
.DEFAULT_GOAL := all
.DELETE_ON_ERROR:

LEAN_VERSION := 4.35.0
LEAN_SHA256 := 6747b099d03d3675f2716e7cf5924a16bfbf75822b13a3d36f51f933ffcc307b
EMSDK_VERSION := 4.0.23
EMSDK_SHA256 := a91a4c1f42dbb0345faac093161e27d43e9b6964840d8c8d80976ab8d3eaf2d3

OUT := .lake/wasm
WORK := $(OUT)/browser-build
TOOLCHAINS := $(OUT)/toolchains
PREFIX := $(shell lean --print-prefix)
LEAN_TREE := $(TOOLCHAINS)/lean4-$(LEAN_VERSION)
SOURCE := $(LEAN_TREE)/src
EMSDK := $(TOOLCHAINS)/emsdk-$(EMSDK_VERSION)
SDK := $(EMSDK)/upstream/emscripten
PATCH := experiments/wasm/lean-$(LEAN_VERSION).patch
RUNTIME := $(OUT)/full-runtime
MAKEFILE := experiments/wasm/Makefile
JOBS ?= 8
FLAGS := -O2 -DNDEBUG -DLEAN_EMSCRIPTEN -I$(RUNTIME)/include -pthread -fwasm-exceptions
LEAN_SOURCES := $(patsubst $(CURDIR)/%,%,$(shell cat .lake/build/browser-sources.txt 2>/dev/null))
LEAN_OBJECTS := $(addprefix $(WORK)/objects/,$(LEAN_SOURCES:.c=.o))
LIBRARIES := $(addprefix $(RUNTIME)/lib/lean/,libInit.a libStd.a libLean.a libleancpp.a libleanrt.a) $(RUNTIME)/libuv/src/libuv/libuv.a

.PHONY: all setup link test
# Lake writes the source list, so linking runs in a second pass that reads it.
all: $(LIBRARIES)
	lake build browserSources
	$(MAKE) -f $(MAKEFILE) -j$(JOBS) link
	install -d web/dist/wasm
	install -m 644 $(OUT)/json.mjs $(OUT)/json.wasm web/dist/wasm/

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
$(LEAN_TREE)/.patched: $(TOOLCHAINS)/lean-$(LEAN_VERSION).tar.gz $(PATCH)
	rm -rf $(LEAN_TREE) $(LEAN_TREE).tmp
	mkdir $(LEAN_TREE).tmp
	tar -xzf $< -C $(LEAN_TREE).tmp
	patch --batch -s -d $(LEAN_TREE).tmp/lean4-$(LEAN_VERSION) -p1 < $(PATCH)
	mv $(LEAN_TREE).tmp/lean4-$(LEAN_VERSION) $(LEAN_TREE)
	rmdir $(LEAN_TREE).tmp
	touch $@

$(EMSDK)/.activated: $(TOOLCHAINS)/emsdk-$(EMSDK_VERSION).tar.gz
	tar -xzf $< -C $(TOOLCHAINS)
	$(EMSDK)/emsdk install $(EMSDK_VERSION)
	$(EMSDK)/emsdk activate $(EMSDK_VERSION)
	touch $@

# The upstream build owns the complete runtime and standard libraries.
$(LIBRARIES) &: $(LEAN_TREE)/.patched $(EMSDK)/.activated
	@grep -q '^#define LEAN_VERSION_STRING "$(LEAN_VERSION)"' $(PREFIX)/include/lean/version.h || { echo 'This build requires Lean $(LEAN_VERSION).'; exit 1; }
	$(SDK)/emcmake cmake -S $(SOURCE) -B $(RUNTIME) -DSTAGE=1 -DPREV_STAGE=$(PREFIX) -DPREV_STAGE_CMAKE_EXECUTABLE_SUFFIX= -DUSE_GMP=OFF -DUSE_MIMALLOC=OFF -DMMAP=OFF -DUSE_LAKE=OFF -DUSE_GITHASH=OFF -DCMAKE_BUILD_TYPE=Release -DCCACHE=OFF
	cmake --build $(RUNTIME) --target leanrt leancpp -j$(JOBS)
	$(MAKE) -C $(SOURCE) -f $(abspath $(RUNTIME))/stdlib.make -j$(JOBS) Lean
	touch $(LIBRARIES)

$(WORK)/objects/%.o: %.c $(MAKEFILE)
	@mkdir -p $(@D)
	$(SDK)/emcc $(FLAGS) -MMD -MP -c $< -o $@

$(WORK)/json-bridge.o: experiments/wasm/json-bridge.cpp $(MAKEFILE)
	@mkdir -p $(@D)
	$(SDK)/em++ -std=c++20 $(FLAGS) -MMD -MP -c $< -o $@

-include $(LEAN_OBJECTS:.o=.d) $(WORK)/json-bridge.d

link: $(OUT)/json.mjs $(OUT)/json.wasm
$(OUT)/json.mjs $(OUT)/json.wasm &: $(WORK)/json-bridge.o $(LEAN_OBJECTS) $(LIBRARIES) .lake/build/browser-sources.txt $(MAKEFILE)
	$(SDK)/em++ $(FLAGS) $(WORK)/json-bridge.o $(LEAN_OBJECTS) -Wl,--start-group $(LIBRARIES) -Wl,--end-group --no-entry -Wl,--fatal-warnings -sMODULARIZE -sEXPORT_ES6 -sENVIRONMENT=node,web,worker -sALLOW_MEMORY_GROWTH -sSTACK_SIZE=8388608 -sSTACK_OVERFLOW_CHECK=2 '-sEXPORTED_FUNCTIONS=["_json_init","_json_run_typed","_json_run_checker","_wasm_allocated_bytes"]' '-sEXPORTED_RUNTIME_METHODS=["ccall"]' -o $(OUT)/json.mjs

test: all
	lake build Tests.ExpressionProtocol
	lake env lean --run experiments/wasm/ExportJsonCases.lean > $(OUT)/json-cases.jsonl
	node experiments/wasm/json-test.mjs
	npm --prefix web run build
	FORMS_WASM_TEST=1 node --test web/wasm.test.mjs web/validation.test.mjs
