all: fake_maple

fake_maple: fake_maple.ml
	$(CAMLBIN)ocamlc -o fake_maple str.cma fake_maple.ml

clean:
	rm -f fake_maple fake_maple.cmo fake_maple.cmi

.PHONY: all
