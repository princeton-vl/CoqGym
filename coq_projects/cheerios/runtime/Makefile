OCAMLBUILD = ocamlbuild -tags safe_string -I ocaml -cflag -g -lflag -g
OCAMLBUILDTEST = $(OCAMLBUILD) -pkg oUnit -I test/tree -I test

MLPOSITIVE = test/positive_serializer.ml test/positive_serializer.mli
MLTREE = test/tree_serializer.ml test/tree_serializer.mli

MLFILES = ocaml/bit_vector.ml ocaml/bit_vector.mli ocaml/serializer_primitives.ml ocaml/serializer_primitives.mli

default: cheerios-runtime

$(MLPOSITIVE) $(MLTREE):
	+$(MAKE) -C .. runtime/$@


# positive
positive_test.native: $(MLPOSITIVE) $(MLFILES) script/remove_module.pl test/positive_test.ml
	perl script/remove_module.pl test/positive_serializer
	$(OCAMLBUILDTEST) positive_test.native

positive_bench.native: test/positive_test.ml test/positive_bench.ml 
	$(OCAMLBUILDTEST) positive_bench.native

test/positive_bench.dat: positive_bench.native
	./positive_bench.native > test/positive_bench.dat

positive_bench.pdf: test/positive_bench.dat test/positive.gpi
	gnuplot test/positive.gpi > positive_bench.pdf

# tree
tree_test.native: $(MLTREE) $(MLFILES) script/remove_module.pl test/tree_test.ml
	perl script/remove_module.pl test/tree_serializer
	$(OCAMLBUILDTEST) tree_test.native

tree_bench.native: test/tree_test.ml test/tree_bench.ml 
	$(OCAMLBUILDTEST) tree_bench.native

test/tree_bench.dat: tree_bench.native
	./tree_bench.native > test/tree_bench.dat

tree_bench.pdf: test/tree_bench.dat test/tree.gpi
	gnuplot test/tree.gpi > tree_bench.pdf

# misc

cheerios-runtime: $(MLFILES) ocaml/cheerios_runtime.mllib
	$(OCAMLBUILD) cheerios_runtime.cma cheerios_runtime.cmxa cheerios_runtime.cmxs

test: positive_test.native tree_test.native
	./positive_test.native
	./tree_test.native

.PHONY: default test clean cheerios-runtime $(MLPOSITIVE) $(MLTREE)

clean:
	ocamlbuild -clean
	rm -f *.pdf test/*.dat

.NOTPARALLEL: $(MLPOSITIVE)
.NOTPARALLEL: $(MLTREE)
