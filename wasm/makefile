# Run from the repository root:
.DEFAULT_GOAL := all
.DELETE_ON_ERROR:

JOBS ?= 8
include wasm/runtime.mk

WORK := $(OUT)/browser-build-$(EMSDK_VERSION)
MAKEFILE := wasm/makefile
FLAGS := -O2 -DNDEBUG -DLEAN_EMSCRIPTEN -I$(RUNTIME)/include -pthread -fwasm-exceptions
LEAN_SOURCES := $(patsubst $(CURDIR)/%,%,$(shell cat .lake/build/browser-sources.txt 2>/dev/null))
LEAN_OBJECTS := $(addprefix $(WORK)/objects/,$(LEAN_SOURCES:.c=.o))
LINK_FLAGS = $(MINIMAL_INIT) -Wl,--start-group $(LIBRARIES) -Wl,--end-group --no-entry -Wl,--fatal-warnings -sMODULARIZE -sEXPORT_ES6 -sENVIRONMENT=node,web,worker -sALLOW_MEMORY_GROWTH -sSTACK_SIZE=8388608 -sSTACK_OVERFLOW_CHECK=2 '-sEXPORTED_RUNTIME_METHODS=["ccall"]'

.PHONY: all setup link test test-libuv-check size size-gzip size-brotli ts-lines FORCE
# Lake writes the source list, so linking runs in a second pass that reads it.
all: $(MINIMAL_INIT) $(LIBRARIES)
	lake build browserSources
	$(MAKE) -f $(MAKEFILE) -j$(JOBS) link
	install -d web/dist/wasm
	install -m 644 $(OUT)/forms.mjs $(OUT)/forms.wasm web/dist/wasm/

$(WORK)/objects/%.o: %.c $(MAKEFILE)
	@mkdir -p $(@D)
	$(SDK)/emcc $(FLAGS) -MMD -MP -c $< -o $@

$(WORK)/forms-bridge.o: wasm/forms-bridge.cpp $(MAKEFILE)
	@mkdir -p $(@D)
	$(SDK)/em++ -std=c++20 $(FLAGS) -MMD -MP -c $< -o $@

-include $(LEAN_OBJECTS:.o=.d) $(WORK)/forms-bridge.d

FORCE:

link: $(OUT)/forms.mjs $(OUT)/forms.wasm
# Lean replaces most libuv-backed functions on wasm with stubs that abort; fail if any survive DCE.
$(OUT)/forms.mjs $(OUT)/forms.wasm &: $(WORK)/forms-bridge.o $(LEAN_OBJECTS) $(MINIMAL_INIT) $(LIBRARIES) .lake/build/browser-sources.txt $(MAKEFILE)
	$(SDK)/em++ $(FLAGS) $(WORK)/forms-bridge.o $(LEAN_OBJECTS) $(LINK_FLAGS) '-sEXPORTED_FUNCTIONS=["_forms_init","_forms_request"]' -o $(OUT)/forms.mjs
	@tools/check_libuv_stubs.sh $(OUT)/forms.wasm

test: all
	npm --prefix web test

# Links a TCP server through the same pipeline, so the check must reject it.
FIXTURE := $(WORK)/libuv-fixture
$(FIXTURE)/LibuvFixture.c: tools/fixtures/LibuvFixture.lean
	@mkdir -p $(@D)
	lean -c $@ $<

$(FIXTURE)/LibuvFixture.o: $(FIXTURE)/LibuvFixture.c $(MAKEFILE)
	$(SDK)/emcc $(FLAGS) -c $< -o $@

$(FIXTURE)/fixture.mjs $(FIXTURE)/fixture.wasm &: $(FIXTURE)/LibuvFixture.o $(MINIMAL_INIT) $(LIBRARIES) $(MAKEFILE)
	$(SDK)/em++ $(FLAGS) $< $(LINK_FLAGS) '-sEXPORTED_FUNCTIONS=["_libuv_fixture"]' -o $(FIXTURE)/fixture.mjs

test-libuv-check: $(FIXTURE)/fixture.wasm
	@tools/check_libuv_stubs.sh $< 2>/dev/null; test $$? -eq 1 || { echo 'check_libuv_stubs.sh missed libuv stubs in $<' >&2; exit 1; }

# Report the existing binary without rebuilding it.
size:
	@test -f $(OUT)/forms.wasm || { echo 'Wasm binary missing; run make -f $(MAKEFILE) first.' >&2; exit 1; }
	@wc -c < $(OUT)/forms.wasm | awk '{ printf "$(OUT)/forms.wasm: %.2f KiB (%.2f MiB)\n", $$1 / 1024, $$1 / 1048576 }'

# Measure deterministic gzip level 9 compression.
size-gzip:
	@tmp=$$(mktemp); trap 'rm -f "$$tmp"' EXIT HUP INT TERM; \
	gzip -n -9 -c $(OUT)/forms.wasm > "$$tmp" && \
	wc -c < "$$tmp" | awk '{ printf "$(OUT)/forms.wasm (gzip -9): %.2f KiB (%.2f MiB)\n", $$1 / 1024, $$1 / 1048576 }'

# Measure Brotli quality 11 (requires the brotli CLI).
size-brotli:
	@tmp=$$(mktemp); trap 'rm -f "$$tmp"' EXIT HUP INT TERM; \
	brotli -q 11 -c $(OUT)/forms.wasm > "$$tmp" && \
	wc -c < "$$tmp" | awk '{ printf "$(OUT)/forms.wasm (Brotli quality 11): %.2f KiB (%.2f MiB)\n", $$1 / 1024, $$1 / 1048576 }'

# Count physical source lines, including comments and blank lines.
ts-lines:
	@find web packages -type d \( -name node_modules -o -name dist -o -name tests -o -name __tests__ \) -prune -o \
	-type f \( -name '*.ts' -o -name '*.tsx' \) ! -name '*.test.*' ! -name '*.spec.*' \
	-exec wc -l {} +
