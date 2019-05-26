LIBDIR      := src/Cecoa
EXAMPLESDIR := src/Cecoa/Examples

SOURCES := $(foreach dir, $(LIBDIR) $(EXAMPLESDIR), $(wildcard $(dir)/*.v))

all: Makefile.coq
	+$(MAKE) -f Makefile.coq all

clean: Makefile.coq
	+$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq Makefile.coq.conf

Makefile.coq: _CoqProject
	$(COQBIN)coq_makefile -f _CoqProject -o Makefile.coq $(SOURCES)

%: Makefile.coq
	+$(MAKE) -f Makefile.coq $@

.PHONY: all clean _CoqProject Makefile
