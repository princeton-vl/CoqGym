QC=quickChick -color -ocamlbuild '-use-ocamlfind'
TMP_DIR=../_qc_pyml.tmp
EXTR_BIN=extract.cmxs
V=@

all: Makefile.coq $(EXTR_BIN)
	$V$(MAKE) -f $<

test:
	time $(QC)

Makefile.coq: _CoqProject
	$Vcoq_makefile -o $@ -f $<

%.cmxs: %.ml
	$Vocamlopt -shared -o $@

clean:
	$Vif [ -e Makefile.coq ]; then $(MAKE) -f Makefile.coq clean; fi
	$V$(RM) -r *~ .*.aux Makefile.coq* *.pyc __pycache__ \
		$(TMP_DIR) $(EXTR_BIN)
