RULESFILE = stlc-rules.tex

GENCOQ = Stlc.v Stlc_inf.v Lec1_sol.v Lec1_full.v  Lec2_sol.v Lec2_full.v Nominal_full.v Nominal_sol.v Connect_full.v Connect_sol.v

FULL    = Lec1 Lec2 Nominal Connect
EXTRA   = Stlc.v Stlc_inf.v stlc.ott stlc.mng ottalt.sty listproc.sty stlc.pdf gen.mk
DISTRIB = Definitions.v Lemmas.v README.md ../LICENSE

ZIPNAME = DSSS.zip

all: coq

html: coq
	make -f Stlc.mk html

zip: $(DISTRIB) Stlc.mk stlc.pdf $(EXTRA) $(SOLS)
	rm -f $(ZIPNAME)
	mkdir -p Stlc
	mkdir -p Stlc/sol
	mkdir -p Stlc/extra
	for f in $(FULL) ; do cp $${f}_full.v Stlc/$${f}.v ; done
	for f in $(FULL) ; do cp $${f}_sol.v Stlc/sol/$${f}_sol.v ; done
	cp $(DISTRIB) Stlc
	cp $(EXTRA) Stlc/extra
	(cd Stlc; echo "-R . Stlc" > _CoqProject ; ls *.v >> _CoqProject)
	(cd Stlc; coq_makefile -f _CoqProject > Makefile)
	ln -s ../Metalib .
	zip $(ZIPNAME) Stlc/* Stlc/extra/* Stlc/sol/* Metalib/*
	rm Metalib

zipclean:
	rm -f Stlc.zip
	rm -rf Stlc

clean: Stlc.mk paperclean zipclean
	make -f Stlc.mk clean
	rm -f Stlc.mk
	rm -f *.cmi *.cmo coqsplit


coq: $(GENCOQ) Stlc.mk
	rm -rf Stlc
	make -f Stlc.mk

Stlc.mk:
	coq_makefile -f _CoqProject -o Stlc.mk

%.pdf : %.tex Makefile
	latexmk -bibtex -pdf $*.tex


$(RULESFILE): stlc.ott
	ott -i stlc.ott -o $(RULESFILE) \
          -tex_wrap false \
          -tex_show_meta false


%.tex: $(RULESFILE) %.mng Makefile
	ott -i stlc.ott \
                    -tex_wrap false \
                    -tex_show_meta false \
                    -tex_filter $*.mng $*.tex



Stlc.v: stlc.ott Makefile
	ott -i stlc.ott -o Stlc.v -coq_lngen true -coq_expand_list_types true
	make METALIB.FIX_Stlc

Stlc_inf.v: stlc.ott Makefile
	lngen --coq Stlc_inf.v --coq-ott Stlc stlc.ott
	make METALIB.FIX_Stlc_inf

%.vo : %.v
	coqc $*.v

# Target to be called with some filename appended to it
# It is a quick hack to fix the imports to metalib
METALIB.FIX_%:
	sed -i -e 's/Metatheory/Metalib.Metatheory/g' $*.v
	sed -i -e 's/LibLNgen/Metalib.LibLNgen/g' $*.v
	sed '1d' $*.v > __TMP__; mv __TMP__ $*.v

paperclean:
	rm -if *-rules.tex $(TOP).tex *.log ./*~ *.aux $(PDFS) *.bbl *.blg *.fdb_latexmk *.fls *.out *.nav

coqsplit: coqsplit.ml
	ocamlc.opt coqsplit.ml -o coqsplit

%_full.v: %.v coqsplit
	./coqsplit < $< > $@

%_short.v: %.v coqsplit
	./coqsplit -terse < $< > $@

%_sol.v: %.v coqsplit
	./coqsplit -solutions < $< > $@
