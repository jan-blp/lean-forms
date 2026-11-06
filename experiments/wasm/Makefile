# Run from the repository root: make -f experiments/wasm/Makefile [all|test|setup]
.DEFAULT_GOAL := all
.DELETE_ON_ERROR:

OUT := .lake/wasm
WORK := $(OUT)/browser-build
PREFIX := $(shell lean --print-prefix)
SOURCE := $(OUT)/toolchains/lean4-4.35.0/src
SDK := $(OUT)/toolchains/emsdk-4.0.23/upstream/emscripten
RUNTIME := $(OUT)/full-runtime
MAKEFILE := experiments/wasm/Makefile
JOBS ?= 8
FLAGS := -O2 -DNDEBUG -DLEAN_EMSCRIPTEN -I$(RUNTIME)/include -pthread -fwasm-exceptions
LEAN_SOURCES := $(patsubst $(CURDIR)/%,%,$(shell cat .lake/build/browser-sources.txt 2>/dev/null))
LEAN_OBJECTS := $(addprefix $(WORK)/objects/,$(LEAN_SOURCES:.c=.o))
LIBRARIES := $(RUNTIME)/lib/lean/libInit.a $(RUNTIME)/lib/lean/libStd.a $(RUNTIME)/lib/lean/libLean.a $(RUNTIME)/lib/lean/libleancpp.a $(RUNTIME)/lib/lean/libleanrt.a $(RUNTIME)/libuv/src/libuv/libuv.a

.PHONY: all setup prepare runtime objects link test size
all: prepare
	$(MAKE) -f $(MAKEFILE) -j$(JOBS) link
	install -d web/dist/wasm
	install -m 644 $(OUT)/json.mjs $(OUT)/json.wasm web/dist/wasm/

setup:
	bash experiments/wasm/setup-runtime.sh

# The upstream build owns the complete runtime and standard libraries.
runtime:
	@test -x $(SDK)/emcc -a -d $(SOURCE) || { echo 'Run make -f $(MAKEFILE) setup first.'; exit 1; }
	@grep -q '^#define LEAN_VERSION_STRING "4.35.0"' $(PREFIX)/include/lean/version.h || { echo 'This build requires Lean 4.35.0.'; exit 1; }
	$(SDK)/emcmake cmake -S $(SOURCE) -B $(RUNTIME) -DSTAGE=1 -DPREV_STAGE=$(PREFIX) -DPREV_STAGE_CMAKE_EXECUTABLE_SUFFIX= -DUSE_GMP=OFF -DUSE_MIMALLOC=OFF -DMMAP=OFF -DUSE_LAKE=OFF -DUSE_GITHASH=OFF -DCMAKE_BUILD_TYPE=Release -DCCACHE=OFF
	cmake --build $(RUNTIME) --target leanrt leancpp -j$(JOBS)
	$(MAKE) -C $(SOURCE) -f $(abspath $(RUNTIME))/stdlib.make -j$(JOBS) Lean

prepare: runtime
	lake build browserSources

$(WORK)/objects/%.o: %.c $(MAKEFILE)
	@mkdir -p $(@D)
	$(SDK)/emcc $(FLAGS) -MMD -MP -c $< -o $@

$(WORK)/json-bridge.o: experiments/wasm/json-bridge.cpp $(MAKEFILE)
	@mkdir -p $(@D)
	$(SDK)/em++ -std=c++20 $(FLAGS) -MMD -MP -c $< -o $@

-include $(LEAN_OBJECTS:.o=.d) $(WORK)/json-bridge.d

objects: $(WORK)/json-bridge.o $(LEAN_OBJECTS)
link: $(OUT)/json.mjs $(OUT)/json.wasm
$(OUT)/json.mjs $(OUT)/json.wasm &: $(WORK)/json-bridge.o $(LEAN_OBJECTS) $(LIBRARIES) .lake/build/browser-sources.txt $(MAKEFILE)
	$(SDK)/em++ $(FLAGS) $(WORK)/json-bridge.o $(LEAN_OBJECTS) -Wl,--start-group $(LIBRARIES) -Wl,--end-group --no-entry -Wl,--fatal-warnings -sMODULARIZE -sEXPORT_ES6 -sENVIRONMENT=node,web,worker -sALLOW_MEMORY_GROWTH -sSTACK_SIZE=8388608 -sSTACK_OVERFLOW_CHECK=2 '-sEXPORTED_FUNCTIONS=["_json_init","_json_run","_json_run_typed","_json_run_checker","_wasm_allocated_bytes"]' '-sEXPORTED_RUNTIME_METHODS=["ccall"]' -o $(OUT)/json.mjs

test: all
	lake build Tests.ExpressionProtocol
	lake env lean --run experiments/wasm/ExportJsonCases.lean > $(OUT)/json-cases.jsonl
	node experiments/wasm/json-test.mjs
	npm --prefix web run build
	FORMS_WASM_TEST=1 node --test web/wasm.test.mjs web/validation.test.mjs

size: all
	wc -c $(OUT)/json.wasm $(OUT)/json.mjs
