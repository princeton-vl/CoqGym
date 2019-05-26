# sets COQVERSION
include Makefile.detect-coq-version

# sets MLTREE, etc.
include Makefile.ml-files

ifeq (,$(filter $(COQVERSION),8.6 8.7 8.8 8.9 8.10 dev))
$(error "Cheerios is only compatible with Coq version 8.6.1 or later")
endif

COQPROJECT_EXISTS := $(wildcard _CoqProject)

ifeq "$(COQPROJECT_EXISTS)" ""
$(error "Run ./configure before running make")
endif

CHECKPATH := $(shell ./script/checkpaths.sh)
ifneq ("$(CHECKPATH)","")
$(info $(CHECKPATH))
$(warning checkpath reported an error)
endif

default: Makefile.coq
	$(MAKE) -f Makefile.coq

quick: Makefile.coq
	$(MAKE) -f Makefile.coq quick

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq

$(MLPOSITIVE) $(MLTREE): Makefile.coq
	$(MAKE) -f Makefile.coq $@

install: Makefile.coq
	$(MAKE) -f Makefile.coq install

clean: Makefile.coq
	$(MAKE) -f Makefile.coq cleanall
	rm -f Makefile.coq Makefile.coq.conf
	$(MAKE) -C runtime clean

distclean: clean
	rm -f _CoqProject

.PHONY: default clean install distclean quick
.PHONY: $(MLPOSITIVE) $(MLTREE)

.NOTPARALLEL: $(MLPOSITIVE)
.NOTPARALLEL: $(MLTREE)
