V=@
.PHONY: plugin install install-plugin clean quickChickTool

QCTOOL_DIR=quickChickTool
QCTOOL_EXE=quickChickTool.byte
QCTOOL_SRC=$(QCTOOL_DIR)/quickChickTool.ml \
		   $(QCTOOL_DIR)/quickChickToolTypes.ml \
		   $(QCTOOL_DIR)/quickChickToolLexer.mll \
		   $(QCTOOL_DIR)/quickChickToolParser.mly

# Here is a hack to make $(eval $(shell work
# (copied from coq_makefile generated stuff):
define donewline


endef

includecmdwithout@ = $(eval $(subst @,$(donewline),$(shell { $(1) | tr -d '\r' | tr '\n' '@'; })))
$(call includecmdwithout@,$(COQBIN)coqtop -config)

all: quickChickTool plugin documentation-check

plugin: Makefile.coq 
	$(MAKE) -f Makefile.coq 

documentation-check: plugin
	coqc -R src QuickChick -I src QuickChickInterface.v
	coqc -R src QuickChick -I src DocumentationCheck.v

TEMPFILE := $(shell mktemp)

install: all
	$(V)$(MAKE) -f Makefile.coq install > $(TEMPFILE)
# Manually copying the remaining files
	$(V)cp $(QCTOOL_DIR)/$(QCTOOL_EXE) $(shell opam config var bin)/quickChick
#	 $(V)cp src/quickChickLib.cmx $(COQLIB)/user-contrib/QuickChick
#	 $(V)cp src/quickChickLib.o $(COQLIB)/user-contrib/QuickChick

install-plugin: Makefile.coq
	$(V)$(MAKE) -f Makefile.coq install | tee $(TEMPFILE)

uninstall:
	$(V)if [ -e Makefile.coq ]; then $(MAKE) -f Makefile.coq uninstall; fi
	$(RM) $(shell opam config var bin)/quickChick

src/%.cmo : src/%.ml
	ocamlc -I src -c $<

quickChickTool: $(QCTOOL_DIR)/$(QCTOOL_EXE)

$(QCTOOL_DIR)/$(QCTOOL_EXE): $(QCTOOL_SRC)
	cd $(QCTOOL_DIR); ocamlbuild -use-ocamlfind $(QCTOOL_EXE)

tests:
#	$(MAKE) -C examples/ifc-basic test
	$(MAKE) -C examples/RedBlack test
#	cd examples/stlc; make clean && make
	$(MAKE) -C examples/multifile-mutation test
# This takes too long. 
#	$(MAKE) -C examples/c-mutation test
#	coqc examples/BSTTest.v
	coqc examples/DependentTest.v

Makefile.coq: _CoqProject
	$(V)coq_makefile -f _CoqProject -o Makefile.coq

clean:
	$Vif [ -e Makefile.coq ]; then $(MAKE) -f Makefile.coq clean; fi
	$Vocamlbuild -clean
         # This might not work on macs
	find . -name '*.vo' -print -delete
	find . -name '*.glob' -print -delete
	find . -name *.d -print -delete
	find . -name *.o -print -delete
	find . -name *.cmi -print -delete
	find . -name *.cmx -print -delete
	find . -name *.cmxs -print -delete
	find . -name *.cmo -print -delete
	find . -name *.bak -print -delete
	find . -name *~ -print -delete
	find . -name *.conflicts -print -delete
	find . -name *.output -print -delete
	find . -name *.aux -print -delete
	rm -f Makefile.coq*

bc:
	coqwc src/*.v
	coqwc examples/RedBlack/*.v
	coqwc ../ifc/*.v

.merlin: Makefile.coq
	make -f Makefile.coq .merlin
