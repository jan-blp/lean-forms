EMACS ?= emacs
LATEXMK ?= latexmk
SHELL := /bin/bash
.SHELLFLAGS := -eu -o pipefail -c
export EMACS

.PHONY: build watch clean distclean

build: slides.tex
	$(LATEXMK) slides.tex

slides.tex: slides.org
	$(EMACS) --batch -Q --load ox-beamer --eval "(setq org-latex-src-block-backend 'listings)" --eval "(add-to-list 'org-latex-listings-langs '(lean \"Lean\"))" --visit "$<" --funcall org-beamer-export-to-latex

watch: slides.tex
	$(LATEXMK) -pvc -view=none slides.tex

clean:
	$(LATEXMK) -c slides.tex

distclean:
	$(LATEXMK) -C slides.tex
	rm -f slides.tex
