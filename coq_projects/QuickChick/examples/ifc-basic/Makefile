
.PHONY: all clean

all: Makefile.coq
	$(MAKE) -f Makefile.coq

clean:
	if [ -e Makefile.coq ]; then $(MAKE) -f Makefile.coq clean; fi
	$(RM) Makefile.coq*

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq
