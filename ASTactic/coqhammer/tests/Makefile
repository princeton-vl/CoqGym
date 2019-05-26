COQC=coqc

all: basic.vo hashing.vo arith.vo

basic.vo : basic.v
	$(COQC) basic.v

hashing.vo : hashing.v
	$(COQC) hashing.v

arith.vo : arith.v
	$(COQC) arith.v

clean:
	-rm -f *.vo *.glob .*.aux
