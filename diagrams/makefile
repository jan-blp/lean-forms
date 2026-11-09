DOT := dot
SOURCES := $(wildcard *.dot)
PDFS := $(SOURCES:%.dot=build/%.pdf)
SVGS := $(SOURCES:%.dot=build/%.svg)

.PHONY: all pdf svg clean
all: pdf svg

pdf: $(PDFS)
svg: $(SVGS)

build/%.pdf: %.dot makefile | build
	$(DOT) -Tpdf $< -o $@

build/%.svg: %.dot makefile | build
	$(DOT) -Tsvg $< -o $@

build:
	mkdir -p $@

clean:
	rm -rf build
