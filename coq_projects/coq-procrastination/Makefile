%: Makefile.coq
	+make -f Makefile.coq $@

all: Makefile.coq
	+make -f Makefile.coq all

examples: all
	@ $(MAKE) -C examples

manual:
	@ $(MAKE) -C manual

clean: Makefile.coq
	+make -f Makefile.coq clean
	rm -f Makefile.coq
	rm -f Makefile.coq.conf
	@ $(MAKE) -C manual clean
	@ $(MAKE) -C examples clean

Makefile.coq: _CoqProject Makefile
	coq_makefile -f _CoqProject -o Makefile.coq

_CoqProject: ;

Makefile: ;

.PHONY: all clean manual
