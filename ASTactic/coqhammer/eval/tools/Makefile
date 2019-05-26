
all: stat coqnames rmcomments
	rm -f *.cm* *.o

stat: utils.ml stat.ml
	ocamlopt -inline 100 -unsafe unix.cmxa str.cmxa $^ -o $@

coqnames: utils.ml coqnames.ml
	ocamlopt -inline 100 -unsafe unix.cmxa str.cmxa $^ -o $@

rmcomments: rmcomments.c
	gcc $^ -o $@

clean:
	-rm -f rmcomments coqnames stat *.cmo *.cmi *.cmx *.o
