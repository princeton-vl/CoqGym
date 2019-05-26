
.PHONY: all clean

all: Makefile.coq
	$(MAKE) -f Makefile.coq

clean: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	$(RM) -r ../_qc_RedBlack.tmp Makefile.coq*

Makefile.coq: _CoqProject
	$(COQBIN)coq_makefile -f _CoqProject -o Makefile.coq

test: clean
	time quickChick -color -top "QuickChick.RedBlack"
