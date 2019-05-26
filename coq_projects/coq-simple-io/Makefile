NAME=coq-simple-io
OCAMLBUILD = ocamlbuild

MAKEFILE_COQ = Makefile.coq
MAKE_COQ = $(MAKE) -f $(MAKEFILE_COQ)

.PHONY: all build install clean example depgraph

build: $(MAKEFILE_COQ)
	$(MAKE_COQ)

doc: $(MAKEFILE_COQ)
	$(MAKE_COQ) html

install: build
	$(MAKE_COQ) install

uninstall: $(MAKEFILE_COQ)
	$(MAKE_COQ) uninstall

$(MAKEFILE_COQ): _CoqProject
	coq_makefile -f $< -o $@

# With local source files
test: build
	sh test.sh Example
	sh test.sh TestPervasives

# With installed library (check proper installation)
install-test: build
	sh test.sh Example -i ""

clean:
	if [ -e Makefile.coq ]; then $(MAKE) -f Makefile.coq clean; fi
	$(RM) -f Makefile.coq* *.cmxs
	$(RM) -rf _build/ build/
	$(RM) {./,*/,*/*/}{*.{v.d,vo,glob},.*.aux}
	$(RM) $(DEPS_DOT) $(DEPS_OUT)
	$(RM) test/*.ml{i,}

COQDEP=coqdep
DEPS_DOT=deps.dot
DEPS_OUT=deps.jpg

depgraph:
	$(COQDEP) -dumpgraph $(DEPS_DOT) -Q src/ SimpleIO src > /dev/null 2>&1
	sed 's%\("\([^"]*\)/\([^"/]*\)"\[label="\)%\1\2/\n%' -i deps.dot
	dot $(DEPS_DOT) -Tjpg -o$(DEPS_OUT)
