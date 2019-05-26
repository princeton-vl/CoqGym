## Makefile for paper

OTT_SOURCE = ett
OTT_LOC    = .

OTTFILES  = $(foreach i, $(OTT_SOURCE), $(OTT_LOC)/$(i).ott)
OTTIFLAGS = $(foreach i, $(OTT_SOURCE), -i $(OTT_LOC)/$(i).ott)
RULESFILE = ett-rules.tex

TOP=paper
PDFS=paper.pdf

all: $(TOP).pdf
paper: $(TOP).pdf

%.tex: $(RULESFILE) %.mng Makefile
	ott $(OTTIFLAGS) \
                    -tex_wrap false \
                    -tex_show_meta false \
                    -tex_filter $*.mng $*.tex

ett-rules.tex: $(OTTFILES)
	ott $(OTTIFLAGS) -o $(RULESFILE) \
          -tex_wrap false \
          -tex_show_meta false

%.pdf : paper.tex Makefile
	latexmk -bibtex -pdf paper.tex

paperclean:
	rm -if *-rules.tex $(TOP).tex *.log ./*~ *.aux $(PDFS) *.bbl *.blg *.fdb_latexmk *.fls *.out

clean: paperclean
