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

.PHONY: all setup link test size size-gzip size-brotli ts-lines FORCE
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
$(OUT)/forms.mjs $(OUT)/forms.wasm &: $(WORK)/forms-bridge.o $(LEAN_OBJECTS) $(MINIMAL_INIT) $(LIBRARIES) .lake/build/browser-sources.txt $(MAKEFILE)
	$(SDK)/em++ $(FLAGS) $(WORK)/forms-bridge.o $(LEAN_OBJECTS) $(MINIMAL_INIT) -Wl,--start-group $(LIBRARIES) -Wl,--end-group --no-entry -Wl,--fatal-warnings -sMODULARIZE -sEXPORT_ES6 -sENVIRONMENT=node,web,worker -sALLOW_MEMORY_GROWTH -sSTACK_SIZE=8388608 -sSTACK_OVERFLOW_CHECK=2 '-sEXPORTED_FUNCTIONS=["_forms_init","_forms_request"]' '-sEXPORTED_RUNTIME_METHODS=["ccall"]' -o $(OUT)/forms.mjs

test: all
	npm --prefix web test

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
