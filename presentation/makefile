EMACS ?= emacs
LATEXMK ?= latexmk
DOT ?= dot
GVPR ?= gvpr
SHELL := /bin/bash
.SHELLFLAGS := -eu -o pipefail -c
export EMACS DOT

DIAGRAMS := assets/architecture.pdf assets/architecture-step1.pdf assets/architecture-step2.pdf assets/architecture-step3.pdf assets/architecture-step4.pdf assets/architecture-step5.pdf

.PHONY: build watch clean distclean

build: slides.tex $(DIAGRAMS)
	$(LATEXMK) slides.tex

slides.tex: slides.org
	$(EMACS) --batch -Q --load ox-beamer --eval "(setq org-latex-src-block-backend 'listings)" --eval "(add-to-list 'org-latex-listings-langs '(lean \"Lean\"))" --visit "$<" --funcall org-beamer-export-to-latex

$(DIAGRAMS) &: assets/architecture.dot makefile
	$(DOT) -Tpdf "$<" -o assets/architecture.pdf
	for step in 1:describe 2:specification 3:client 4:submission 5:validate; do \
		node=$${step#*:}; number=$${step%%:*}; \
		$(GVPR) -c -a "$$node" \
			'N[$$.name == ARGV[0]] { color="#c62828"; fillcolor="#ffebee"; fontcolor="#b71c1c"; penwidth="3"; }' "$<" \
			| $(DOT) -Tpdf -o "assets/architecture-step$$number.pdf"; \
	done

assets/%.pdf: assets/%.dot
	$(DOT) -Tpdf "$<" -o "$@"

watch: slides.tex $(DIAGRAMS)
	$(LATEXMK) -pvc -view=none slides.tex

clean:
	$(LATEXMK) -c slides.tex

distclean:
	$(LATEXMK) -C slides.tex
	rm -f slides.tex $(DIAGRAMS)
