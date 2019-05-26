# ----------------------------------------------------------------------------
# Set any paper-specific variables.

include Makefile.local

# ----------------------------------------------------------------------------
# Definitions.

SOURCES  := \
  $(wildcard *.tex) \
  $(wildcard *.sty) \
  $(wildcard *.bib) \
  $(wildcard *.cls) \

# ----------------------------------------------------------------------------
# Generic rules.

%.pdf: $(SOURCES) tactics_reference.tex
	xelatex $(DOC).tex
	bibtex $(DOC)
	xelatex $(DOC).tex
	xelatex $(DOC).tex

# ----------------------------------------------------------------------------
# Targets.

.PHONY: pdf loop clean log export

pdf: $(DOC).pdf

tactics_reference.tex: ../TacticsReference.md
	pandoc -o $@ $<

loop: tactics_reference.tex
	latexmk -pdfxe -pvc $(DOC)

clean::
	rm -f `cat .gitignore`
