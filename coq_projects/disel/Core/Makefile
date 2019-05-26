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

Makefile.coq: Make
	coq_makefile -f Make -o Makefile.coq

.PHONY: default clean install
