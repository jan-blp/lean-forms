DOT := dot
SOURCES := $(wildcard *.dot)
PDFS := $(SOURCES:%.dot=build/%.pdf)

.PHONY: all clean
all: $(PDFS)

build/%.pdf: %.dot makefile | build
	$(DOT) -Tpdf $< -o $@

build:
	mkdir -p $@

clean:
	rm -rf build
