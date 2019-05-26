PYTHON=python2.7

OCAMLBUILD = ocamlbuild -tag safe_string -pkgs 'verdi-runtime cheerios-runtime' -I ml -cflag -g
OCAMLBUILD_TEST := $(OCAMLBUILD) -package oUnit -I test

VARDRAFTSERLOG = ml/VarDRaftSerializedLog.ml ml/VarDRaftSerializedLog.mli
VARDSERLOG = ml/vardserlog.ml ml/VarDSerializedLogSerialization.ml ml/VarDSerializedLogArrangement.ml

default: vardserlog.native

vardserlog.native: $(VARDSERLOG) $(VARDRAFTSERLOG) scripts/remove_module.pl
	perl scripts/remove_module.pl ml/VarDRaftSerializedLog
	$(OCAMLBUILD) vardserlog.native

$(VARDRAFTSERLOG):
	+$(MAKE) -C ../.. extraction/vard-serialized-log/$@

test: vardserlog.native test/integration.py
	$(PYTHON) test/integration.py

clean:
	ocamlbuild -clean

.PHONY: default test clean $(VARDRAFTSERLOG)

.NOTPARALLEL: $(VARDRAFTSERLOG)
