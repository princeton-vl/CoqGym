PYTHON=python2.7

OCAMLBUILD = ocamlbuild -tag safe_string -package verdi-runtime -tag thread -I ml -cflag -g
OCAMLBUILD_TEST = $(OCAMLBUILD) -package oUnit -I test

VARDRAFT = ml/VarDRaftDebug.ml ml/VarDRaftDebug.mli
VARD = ml/VarDDebugArrangement.ml ml/varddebug.ml ml/VarDDebugSerialization.ml

default: varddebug.native

varddebug.native: $(VARD) $(VARDRAFT)
	$(OCAMLBUILD) varddebug.native

$(VARDRAFT):
	+$(MAKE) -C ../.. extraction/vard-debug/$@

clean:
	$(OCAMLBUILD) -clean

.PHONY: default clean $(VARDRAFT)

.NOTPARALLEL: varddebug.native
.NOTPARALLEL: $(VARDRAFT)
