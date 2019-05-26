QC=quickChick -color $(QCFLAGS)

all: Makefile.coq 
	$(MAKE) -f Makefile.coq 

Makefile.coq: 
	coq_makefile -f _CoqProject -o Makefile.coq

clean: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -rf ../_qc_multifile-mutation.tmp *.bak

test: clean
	time $(QC)

testinclude:
	$(QC) -m 0 -include _CoqProject
