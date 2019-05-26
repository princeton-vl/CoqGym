PYTHON=python2.7

OCAMLBUILD = ocamlbuild -tag safe_string -package verdi-runtime -I ml -cflag -g
OCAMLBUILD_TEST = $(OCAMLBUILD) -package oUnit -I test

VARDRAFT = ml/VarDRaft.ml ml/VarDRaft.mli
VARD = ml/VarDArrangement.ml ml/vard.ml ml/VarDSerialization.ml
VARD_TEST = test/OptsTest.ml test/VarDSerializationTest.ml test/VarDTest.ml

default: vard.native

vard.native: $(VARD) $(VARDRAFT)
	$(OCAMLBUILD) vard.native

$(VARDRAFT):
	+$(MAKE) -C ../.. extraction/vard/$@

VarDTest.native: $(VARD) $(VARDRAFT) $(VARD_TEST)
	$(OCAMLBUILD_TEST) VarDTest.native

test-units: VarDTest.native
	./VarDTest.native

test-integration: vard.native test/integration.py
	$(PYTHON) test/integration.py

test: test-units test-integration

clean:
	$(OCAMLBUILD) -clean

clear-data:
	./scripts/clear-vard.sh

run: vard.native
	./scripts/start-tmux.sh

debug: vard.native
	./scripts/start-tmux-debug.sh

bench-vard: vard.native
	./scripts/bench-vard.sh
	./scripts/clear-vard.sh

bench-etcd: vard.native
	./scripts/bench-etcd.sh
	./scripts/clear-etcd.sh

.PHONY: default test-units test-integration test clean clear-data run debug bench-vard bench-etcd $(VARDRAFT)

.NOTPARALLEL: vard.native VarDTest.native
.NOTPARALLEL: $(VARDRAFT)
