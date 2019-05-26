PYTHON=python2.7

OCAMLBUILD = ocamlbuild -tag safe_string -pkgs 'verdi-runtime cheerios-runtime' -I ml -cflag -g
OCAMLBUILD_TEST := $(OCAMLBUILD) -package oUnit -I test

VARDRAFTSERIALIZED = ml/VarDRaftSerialized.ml ml/VarDRaftSerialized.mli
VARDSERIALIZED = ml/VarDSerializedArrangement.ml ml/vardserialized.ml ml/VarDSerializedSerialization.ml
VARDSERIALIZED_TEST = test/OptsTest.ml test/VarDSerializedSerializationTest.ml test/VarDSerializedTest.ml

default: vardserialized.native

vardserialized.native: $(VARDSERIALIZED) $(VARDRAFTSERIALIZED) scripts/remove_module.pl
	perl scripts/remove_module.pl ml/VarDRaftSerialized
	$(OCAMLBUILD) vardserialized.native

$(VARDRAFTSERIALIZED):
	+$(MAKE) -C ../.. extraction/vard-serialized/$@

VarDSerializedTest.native: $(VARDSERIALIZED) $(VARDRAFTSERIALIZED) $(VARDSERIALIZED_TEST) scripts/remove_module.pl
	perl scripts/remove_module.pl ml/VarDRaftSerialized
	$(OCAMLBUILD_TEST) VarDSerializedTest.native

test-units: VarDSerializedTest.native
	./VarDSerializedTest.native

test-integration: vardserialized.native test/integration.py
	$(PYTHON) test/integration.py

test: test-units test-integration

clean:
	ocamlbuild -clean

clear-data:
	./scripts/clear-vard.sh

run: vardserialized.native
	./scripts/start-tmux.sh

debug: vardserialized.native
	./scripts/start-tmux-debug.sh

bench-vard: vardserialized.native
	./scripts/bench-vard.sh
	./scripts/clear-vard.sh

bench-etcd: vardserialized.native
	./scripts/bench-etcd.sh
	./scripts/clear-etcd.sh

.PHONY: default test-units test-integration test clean clear-data run debug bench-vard bench-etcd $(VARDRAFTSERIALIZED)

.NOTPARALLEL: vardserialized.native VarDSerializedTest.native
.NOTPARALLEL: $(VARDRAFTSERIALIZED)
