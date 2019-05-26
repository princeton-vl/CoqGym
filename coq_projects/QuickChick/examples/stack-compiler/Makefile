all: Makefile.coq 
	$(MAKE) -f Makefile.coq 

Makefile.coq: 
	coq_makefile -f _CoqProject -o Makefile.coq

clean: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -rf ../_qc_$(shell basename $(CURDIR)).tmp *.bak Makefile.coq*

test: clean
	quickChick -color -top Stack
