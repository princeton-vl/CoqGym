QC=quickChick -color -ocamlbuild '-lib unix'

all: Makefile.coq foo.py extract.cmxs
	@$(MAKE) -f $<

test:
	time $(QC)

lesstest:
	time $(QC) -N 100

Makefile.coq: _CoqProject
	@coq_makefile -o $@ -f $<

%.cmxs: %.ml
	ocamlopt -shared -o $@
