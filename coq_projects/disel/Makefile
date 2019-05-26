ifeq "$(COQBIN)" ""
COQBIN=$(dir $(shell which coqtop))/
endif

default: Makefile.coq
	$(MAKE) -f Makefile.coq

install: Makefile.coq
	$(MAKE) -f Makefile.coq install

clean: Makefile.coq
	$(MAKE) -f Makefile.coq cleanall
	rm -f Makefile.coq Makefile.coq.conf

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq

TPCMain.d.byte: default
	ocamlbuild -tag safe_string -libs unix -I extraction/TPC -I shims shims/TPCMain.d.byte

CalculatorMain.d.byte: default
	ocamlbuild -tag safe_string -libs unix -I extraction/calculator -I shims shims/CalculatorMain.d.byte

.PHONY: default clean install
