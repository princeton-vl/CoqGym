all: Makefile.coq Makefile.coq.local
	$(MAKE) -f Makefile.coq

install: Makefile.coq Makefile.coq.local
	$(MAKE) -f Makefile.coq install

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq

tests:
	cd tests && $(MAKE) -B

clean: Makefile.coq Makefile.coq.local
	$(MAKE) -f Makefile.coq cleanall
	rm -f Makefile.coq Makefile.coq.conf

.PHONY: all install clean tests
