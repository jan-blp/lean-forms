# Run from the repository root: make -f experiments/wasm/Makefile [all|test|setup]
.DEFAULT_GOAL := all
.DELETE_ON_ERROR:

OUT := .lake/wasm
WORK := $(OUT)/json-build
PREFIX := $(shell lean --print-prefix)
SOURCE := $(OUT)/toolchains/lean4-4.34.1/src
SDK := $(OUT)/toolchains/emsdk-4.0.23/upstream/emscripten
INCLUDE := $(WORK)/include
MAKEFILE := experiments/wasm/Makefile
FLAGS := -O2 -DNDEBUG -DLEAN_EMSCRIPTEN -I$(INCLUDE) -I$(SOURCE)/include -I$(SOURCE) -ffunction-sections -fdata-sections -fwasm-exceptions
RUNTIME := object alloc debug thread mpz mpn utf8 hash memory exception interrupt stackinfo apply platform
BASE_OBJECTS := $(addprefix $(WORK)/runtime/,$(addsuffix .o,$(RUNTIME))) $(WORK)/runtime.o $(WORK)/json-bridge.o

-include $(WORK)/modules.mk
-include $(wildcard $(WORK)/*.d $(WORK)/runtime/*.d)

.PHONY: all setup prepare discover link test size
all: discover
	install -d web/dist/wasm
	install -m 644 $(OUT)/json.mjs $(OUT)/json.wasm web/dist/wasm/

setup:
	bash experiments/wasm/setup-runtime.sh

# Lake tracks Lean dependencies; discovery then follows the generated C symbols.
prepare:
	@test -x $(SDK)/emcc -a -d $(SOURCE) || { echo 'Run make -f $(MAKEFILE) setup first.'; exit 1; }
	@grep -q '^#define LEAN_VERSION_STRING "4.34.1"' $(PREFIX)/include/lean/version.h || { echo 'This build requires Lean 4.34.1.'; exit 1; }
	lake build Forms.Runtime.CheckerProtocol:c Forms.Runtime.ExpressionProtocol:c Forms.Runtime.ExpressionProtocol.Schema:c Forms.Runtime.JsonProtocol:c

discover: prepare
	$(MAKE) -f $(MAKEFILE) $(OUT)/JsonEval.c $(INCLUDE)/config.stamp
	python3 experiments/wasm/discover-json.py

$(OUT)/JsonEval.c: experiments/wasm/JsonEval.lean .lake/build/lib/lean/Forms/Runtime/CheckerProtocol.olean .lake/build/lib/lean/Forms/Runtime/ExpressionProtocol.olean $(MAKEFILE)
	@mkdir -p $(@D)
	lake env lean -c $@ $<

$(INCLUDE)/config.stamp: $(PREFIX)/include/lean/version.h $(MAKEFILE)
	@mkdir -p $(INCLUDE)/lean
	printf '#pragma once\n#include <lean/version.h>\n#define LEAN_IS_STAGE0 0\n' > $(INCLUDE)/lean/config.h
	cp $(PREFIX)/include/lean/version.h $(INCLUDE)/lean/version.h
	printf '#define LEAN_GITHASH "%s"\n' "$$(lean --githash)" > $(INCLUDE)/githash.h
	touch $@

$(WORK)/core/%.c: $(PREFIX)/src/lean/%.lean $(MAKEFILE)
	@mkdir -p $(@D)
	lean -R $(PREFIX)/src/lean -c $@ $<

$(WORK)/runtime/%.o: $(SOURCE)/runtime/%.cpp $(INCLUDE)/config.stamp $(MAKEFILE)
	@mkdir -p $(@D)
	$(SDK)/em++ -std=c++20 $(FLAGS) -MMD -MP -c $< -o $@

$(WORK)/%.o: experiments/wasm/%.cpp $(INCLUDE)/config.stamp $(MAKEFILE)
	$(SDK)/em++ -std=c++20 $(FLAGS) -MMD -MP -c $< -o $@

$(WORK)/%.o: $(WORK)/%.c $(INCLUDE)/config.stamp $(MAKEFILE)
	$(SDK)/emcc $(FLAGS) -MMD -MP -c $< -o $@

# Discovery writes modules.mk, then asks Make to compile/link each candidate.
link: $(OUT)/json.mjs $(OUT)/json.wasm
$(OUT)/json.mjs $(OUT)/json.wasm &: $(BASE_OBJECTS) $(LEAN_OBJECTS) $(WORK)/modules.mk $(MAKEFILE)
	$(SDK)/em++ $(FLAGS) $(BASE_OBJECTS) $(LEAN_OBJECTS) --no-entry -Wl,--error-limit=0 -Wl,-Map=$(WORK)/link.map -sMODULARIZE -sEXPORT_ES6 -sENVIRONMENT=node,web -sALLOW_MEMORY_GROWTH -sSTACK_SIZE=1048576 -sSTACK_OVERFLOW_CHECK=2 '-sEXPORTED_FUNCTIONS=["_json_init","_json_run","_json_run_typed","_json_run_checker","_wasm_allocated_bytes"]' '-sEXPORTED_RUNTIME_METHODS=["ccall"]' -o $(OUT)/json.mjs

# Tests are explicit: producing browser assets does not require test sources.
test: all
	lake build Tests.ExpressionProtocol
	lake env lean --run experiments/wasm/ExportJsonCases.lean > $(OUT)/json-cases.jsonl
	node experiments/wasm/json-test.mjs
	npm --prefix web run build
	FORMS_WASM_TEST=1 node --test web/wasm.test.mjs web/validation.test.mjs

# Decimal kilobytes: 1 KB = 1,000 bytes.
size: all
	@wc -c < $(OUT)/json.wasm | awk '{ printf "Wasm binary: %.1f KB\n", $$1 / 1000 }'
	@gzip -nc $(OUT)/json.wasm | wc -c | awk '{ printf "Wasm binary, gzip: %.1f KB\n", $$1 / 1000 }'
	@wc -c < $(OUT)/json.mjs | awk '{ printf "JavaScript loader: %.1f KB\n", $$1 / 1000 }'
	@gzip -nc $(OUT)/json.mjs | wc -c | awk '{ printf "JavaScript loader, gzip: %.1f KB\n", $$1 / 1000 }'
