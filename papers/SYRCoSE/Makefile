.SUFFIXES: .tex .pdf .dia .eps
.PHONY: default all clean distclean view FORCE

#export TEXINPUTS := .:./Styles//:${TEXINPUTS}
#export BSTINPUTS := .:./Styles//:${BSTINPUTS}
export SHELL := /bin/bash

PAPERS=main.pdf
SOURCES=*.tex *.bib *.cls

all: $(PAPERS)

main.pdf: $(SOURCES)
	latexmk -pdf -f main.tex

continuous:
	latexmk -pdf -pvc -f main.tex

clean:
	@$(RM) *.aux *.lof *.log *.lot *.out *.toc *.nav *.snm *.bbl *.blg
	@$(RM) *~ \#*\# *.spl *.fls *.fdb_latexmk

distclean: clean
	@$(RM) $(PAPERS)
