PROJS_TO_INSTALL = Categories CompCert math-comp coq-error-handlers coq-list-plus coq-cunit coq-list-string corespec fcsl-pcm InfSeqExt verdi VST UnifySL coquelicot algebra bellantonicook coq-ext-lib pocklington int-map coq-function-ninjas coq-iterable lin-alg coq-simple-io bigenough zorns-lemma finmap
PROJS_ONLY_COMPILE = GeoCoq GeometricAlgebra bdds concat euler-formula ruler-compass-geometry twoSquare zfc shuffle hardware coq2html three-gap regexp automata izf lemma-overloading railroad-crossing idxassoc hoare-tut lesniewski-mereology additions checker domain-theory propcalc circuits zsearch-trees bbv ails dep-map markov rsa goedel generic-environments disel ctltctl lazy-pcf weak-up-to groups mini-compiler exceptions higman-s rem tree-automata coq-procrastination higman-cf coqoban ieee754 jordan-curve-theorem huffman zf pigeons hedges functions-in-zfc tortoise-hare-algorithm mod-red traversable-fincontainer buchberger constructive-geometry tarski-geometry float functional-algebra zchinese smc pts param-pi axiomatic-abp lambda maths quicksort-complexity fssec-model ipc chinese cours-de-coq graphs dictionaries dblib cecoa free-groups ramsey qarith amm11262 angles orb-stab qarith-stern-brocot group-theory demos distributed-reference-counting subst miniml fermat4 otway-rees SCEV-coq PolTac fundamental-arithmetics system ChargeCore QuickChick coqrel topology search-trees schroeder verdi-raft area-method coq-library-undecidability maple-mode

.DEFAULT_GOAL := all
.PHONY : all clean install compile $(PROJS_TO_INSTALL) $(PROJS_ONLY_COMPILE) math-comp metalib StructTact cheerios

all :
	$(MAKE) core-dependencies
	$(MAKE) install
	$(MAKE) compile

install : | $(PROJS_TO_INSTALL)
compile : | $(PROJS_ONLY_COMPILE)

core-dependencies : 
	$(MAKE) math-comp
	$(MAKE) metalib
	$(MAKE) StructTact 
	$(MAKE) cheerios

LBITS = $(shell getconf LONG_BIT)
OS = $(shell uname)

Categories : 
	cd Categories && ./configure.sh && make

ifeq ($(OS), Darwin)
COMPCERT_ARCH = x86_$(LBITS)-macosx
endif
ifeq ($(OS), Linux)
COMPCERT_ARCH = x86_$(LBITS)-linux
endif

CompCert : 
	opam install --yes menhir=20181113 && eval $(opam env)
	cd CompCert/ && ./configure $(COMPCERT_ARCH) && make

math-comp : 
	cd math-comp/mathcomp/ && make && make install

metalib :
	cd metalib/Metalib/ && make && make install

coq-error-handlers : 
	cd coq-error-handlers/ && ./configure.sh && make && make install

coq-list-plus : 
	cd coq-list-plus/ && ./configure.sh && make && make install

coq-cunit : 
	cd coq-cunit/ && ./configure.sh && make && make install

coq-list-string : 
	cd coq-list-string/ && ./configure.sh && make && make install

corespec :
	cd corespec/src/FcEtt/ && make

fcsl-pcm : 
	cd fcsl-pcm/ && make && make install

StructTact : 
	cd StructTact/ && ./configure && make && make install

cheerios :
	cd cheerios/ && ./configure && make && make install

InfSeqExt : 
	cd InfSeqExt/ && ./configure && make && make install

verdi : | cheerios
	cd verdi/ && ./configure && make && make install

VST : 
	cd VST/ && make

UnifySL : 
	cd UnifySL/ && make

coquelicot : 
	cd coquelicot/ && ./configure && ./remake && ./remake install

algebra : 
	cd algebra/ && make && make install

bellantonicook : 
	cd bellantonicook/ && make && make install

coq-ext-lib : 
	cd coq-ext-lib/ && make && make install

pocklington : 
	cd pocklington/ && make && make install

int-map : 
	cd int-map/ && make && make install

coq-function-ninjas : 
	cd coq-function-ninjas/ && ./configure.sh && make && make install

coq-iterable : 
	cd coq-iterable/ && ./configure.sh && make && make install

lin-alg : 
	cd lin-alg/ && make && make install

coq-simple-io : 
	cd coq-simple-io && make && make install

bigenough : 
	cd bigenough/ && make && make install

finmap :
	cd finmap/ && make && make install

zorns-lemma : 
	cd zorns-lemma/ && make && make install

GeoCoq : 
	cd GeoCoq/ && ./configure.sh && make

GeometricAlgebra : 
	cd GeometricAlgebra/ && make

bdds : 
	cd bdds/ && make

concat : 
	cd concat/ && make

euler-formula : 
	cd euler-formula/ && make

ruler-compass-geometry : 
	cd ruler-compass-geometry/ && make

twoSquare : 
	cd twoSquare/ && make

zfc : 
	cd zfc/ && make

shuffle : 
	cd shuffle/ && make

hardware : 
	cd hardware/ && make

coq2html : 
	cd coq2html/ && make

three-gap : 
	cd three-gap/ && make

regexp : 
	cd regexp/ && make

automata : 
	cd automata/ && make

izf : 
	cd izf/ && make

lemma-overloading : 
	cd lemma-overloading/ && make

railroad-crossing : 
	cd railroad-crossing/ && make

idxassoc : 
	cd idxassoc/ && make

hoare-tut : 
	cd hoare-tut/ && make

lesniewski-mereology : 
	cd lesniewski-mereology/ && make

additions : 
	cd additions/ && make

checker : 
	cd checker/ && make

domain-theory : 
	cd domain-theory/ && make

propcalc : 
	cd propcalc/ && make

circuits : 
	cd circuits/ && make

zsearch-trees : 
	cd zsearch-trees/ && make

bbv : 
	cd bbv/ && make

ails : 
	cd ails/ && make

dep-map : 
	cd dep-map/ && make

markov : 
	cd markov/ && make

rsa : 
	cd rsa/ && make

goedel : 
	cd goedel/ && make

generic-environments : 
	cd generic-environments/ && make

disel : 
	cd disel/ && make

ctltctl : 
	cd ctltctl/ && make

lazy-pcf : 
	cd lazy-pcf/ && make

weak-up-to : 
	cd weak-up-to/ && make

groups : 
	cd groups/ && make

mini-compiler : 
	cd mini-compiler/ && make

exceptions : 
	cd exceptions/ && make

higman-s : 
	cd higman-s/ && make

rem : 
	cd rem/ && make

tree-automata : 
	cd tree-automata/ && make

coq-procrastination : 
	cd coq-procrastination/ && make

higman-cf : 
	cd higman-cf/ && make

coqoban : 
	cd coqoban/ && make

ieee754 : 
	cd ieee754/ && make

jordan-curve-theorem : 
	cd jordan-curve-theorem/ && make

huffman : 
	cd huffman/ && make

zf : 
	cd zf/ && make

pigeons : 
	cd pigeons/ && make

hedges : 
	cd hedges/ && make

functions-in-zfc : 
	cd functions-in-zfc/ && make

tortoise-hare-algorithm : 
	cd tortoise-hare-algorithm/ && make

mod-red : 
	cd mod-red/ && make

traversable-fincontainer : 
	cd traversable-fincontainer/ && make

buchberger : 
	cd buchberger/ && make

constructive-geometry : 
	cd constructive-geometry/ && make

tarski-geometry : 
	cd tarski-geometry/ && make

float : 
	cd float/ && make

functional-algebra : 
	cd functional-algebra/ && make

zchinese : 
	cd zchinese/ && make

smc : 
	cd smc/ && make

pts : 
	cd pts/ && make

param-pi : 
	cd param-pi/ && make

axiomatic-abp : 
	cd axiomatic-abp/ && make

lambda : 
	cd lambda/ && make

maths : 
	cd maths/ && make

quicksort-complexity : 
	cd quicksort-complexity/ && make

fssec-model : 
	cd fssec-model/ && make

ipc : 
	cd ipc/ && make

chinese : 
	cd chinese/ && make

cours-de-coq : 
	cd cours-de-coq/ && make

graphs : 
	cd graphs/ && make

dictionaries : 
	cd dictionaries/ && make

dblib : 
	cd dblib/ && make

cecoa : 
	cd cecoa/ && make

free-groups : 
	cd free-groups/ && make

ramsey : 
	cd ramsey/ && make

qarith : 
	cd qarith/ && make

amm11262 : 
	cd amm11262/ && make

angles : 
	cd angles/ && make

orb-stab : 
	cd orb-stab/ && make

qarith-stern-brocot : 
	cd qarith-stern-brocot/ && make

group-theory : 
	cd group-theory/ && make

demos : 
	cd demos/ && make

distributed-reference-counting : 
	cd distributed-reference-counting/ && make

subst : 
	cd subst/ && make

miniml : 
	cd miniml/ && make

fermat4 : 
	cd fermat4/ && make

otway-rees : 
	cd otway-rees/ && make

SCEV-coq : 
	cd SCEV-coq/ && make

PolTac : 
	cd PolTac/ && make

fundamental-arithmetics : 
	cd fundamental-arithmetics/ && make

system : 
	cd system/ && ./configure.sh && make

ChargeCore : 
	cd ChargeCore/ChargeCore/ && make

QuickChick : 
	cd QuickChick/ && make

area-method : 
	cd area-method/ && make

coq-library-undecidability : 
	cd coq-library-undecidability/ && make

coqrel : 
	cd coqrel/ && ./configure && make

topology : 
	cd topology/ && make

search-trees : 
	cd search-trees/ && make

schroeder : 
	cd schroeder/ && make

verdi-raft : 
	cd verdi-raft/ && ./configure && make

maple-mode : 
	cd maple-mode/ && make

clean : 
	(cd Categories && make clean) || true
	(cd CompCert/ && make clean) || true
	(cd math-comp/mathcomp/ && make clean) || true
	(cd metalib/Metalib/ && make clean) || true
	(cd coq-error-handlers/ && make clean) || true
	(cd coq-list-plus/ && make clean) || true
	(cd coq-cunit/ && make clean) || true
	(cd coq-list-string/ && make clean) || true
	(cd corespec/src/FcEtt/ && make clean) || true
	(cd fcsl-pcm/ && make clean) || true
	(cd StructTact/ && make clean) || true
	(cd cheerios/ && make clean) || true
	(cd InfSeqExt/ && make clean) || true
	(cd verdi/ && make clean) || true
	(cd VST/ && make clean) || true
	(cd UnifySL/ && make) || true
	(cd coquelicot/ && ./remake clean) || true
	(cd algebra/ && make clean) || true
	(cd bellantonicook/ && make clean) || true
	(cd coq-ext-lib/ && make clean) || true
	(cd pocklington/ && make clean) || true
	(cd int-map/ && make clean) || true
	(cd coq-function-ninjas/ && make clean) || true
	(cd coq-iterable/ && make clean) || true
	(cd lin-alg/ && make clean) || true
	(cd coq-simple-io && make clean) || true
	(cd bigenough/ && make clean) || true
	(cd finmap/ && make clean) || true
	(cd zorns-lemma/ && make clean) || true
	(cd GeoCoq/ && make clean) || true
	(cd GeometricAlgebra/ && make clean) || true
	(cd bdds/ && make clean) || true
	(cd concat/ && make clean) || true
	(cd euler-formula/ && make clean) || true
	(cd ruler-compass-geometry/ && make clean) || true
	(cd twoSquare/ && make clean) || true
	(cd zfc/ && make clean) || true
	(cd shuffle/ && make clean) || true
	(cd hardware/ && make clean) || true
	(cd coq2html/ && make clean) || true
	(cd three-gap/ && make clean) || true
	(cd regexp/ && make clean) || true
	(cd automata/ && make clean) || true
	(cd izf/ && make clean) || true
	(cd lemma-overloading/ && make clean) || true
	(cd railroad-crossing/ && make clean) || true
	(cd idxassoc/ && make clean) || true
	(cd hoare-tut/ && make clean) || true
	(cd lesniewski-mereology/ && make clean) || true
	(cd additions/ && make clean) || true
	(cd checker/ && make clean) || true
	(cd domain-theory/ && make clean) || true
	(cd propcalc/ && make clean) || true
	(cd circuits/ && make clean) || true
	(cd zsearch-trees/ && make clean) || true
	(cd bbv/ && make clean) || true
	(cd ails/ && make clean) || true
	(cd dep-map/ && make clean) || true
	(cd markov/ && make clean) || true
	(cd rsa/ && make clean) || true
	(cd goedel/ && make clean) || true
	(cd generic-environments/ && make clean) || true
	(cd disel/ && make clean) || true
	(cd ctltctl/ && make clean) || true
	(cd lazy-pcf/ && make clean) || true
	(cd weak-up-to/ && make clean) || true
	(cd groups/ && make clean) || true
	(cd mini-compiler/ && make clean) || true
	(cd exceptions/ && make clean) || true
	(cd higman-s/ && make clean) || true
	(cd rem/ && make clean) || true
	(cd tree-automata/ && make clean) || true
	(cd coq-procrastination/ && make clean) || true
	(cd higman-cf/ && make clean) || true
	(cd coqoban/ && make clean) || true
	(cd ieee754/ && make clean) || true
	(cd jordan-curve-theorem/ && make clean) || true
	(cd huffman/ && make clean) || true
	(cd zf/ && make clean) || true
	(cd pigeons/ && make clean) || true
	(cd hedges/ && make clean) || true
	(cd functions-in-zfc/ && make clean) || true
	(cd tortoise-hare-algorithm/ && make clean) || true
	(cd mod-red/ && make clean) || true
	(cd traversable-fincontainer/ && make clean) || true
	(cd buchberger/ && make clean) || true
	(cd constructive-geometry/ && make clean) || true
	(cd tarski-geometry/ && make clean) || true
	(cd float/ && make clean) || true
	(cd functional-algebra/ && make clean) || true
	(cd zchinese/ && make clean) || true
	(cd smc/ && make clean) || true
	(cd pts/ && make clean) || true
	(cd param-pi/ && make clean) || true
	(cd axiomatic-abp/ && make clean) || true
	(cd lambda/ && make clean) || true
	(cd maths/ && make clean) || true
	(cd quicksort-complexity/ && make clean) || true
	(cd fssec-model/ && make clean) || true
	(cd ipc/ && make clean) || true
	(cd chinese/ && make clean) || true
	(cd cours-de-coq/ && make clean) || true
	(cd graphs/ && make clean) || true
	(cd dictionaries/ && make clean) || true
	(cd dblib/ && make clean) || true
	(cd cecoa/ && make clean) || true
	(cd free-groups/ && make clean) || true
	(cd ramsey/ && make clean) || true
	(cd qarith/ && make clean) || true
	(cd amm11262/ && make clean) || true
	(cd angles/ && make clean) || true
	(cd orb-stab/ && make clean) || true
	(cd qarith-stern-brocot/ && make clean) || true
	(cd group-theory/ && make clean) || true
	(cd demos/ && make clean) || true
	(cd distributed-reference-counting/ && make clean) || true
	(cd subst/ && make clean) || true
	(cd miniml/ && make clean) || true
	(cd fermat4/ && make clean) || true
	(cd otway-rees/ && make clean) || true
	(cd SCEV-coq/ && make clean) || true
	(cd PolTac/ && make clean) || true
	(cd fundamental-arithmetics/ && make clean) || true
	(cd system/ && make clean) || true
	(cd ChargeCore/ChargeCore/ && make clean) || true
	(cd QuickChick/ && make clean) || true
	(cd area-method/ && make clean) || true
	(cd coqrel/ && make clean) || true
	(cd topology/ && make clean) || true
	(cd search-trees/ && make clean) || true
	(cd schroeder/ && make clean) || true
	(cd verdi-raft/ && make clean) || true
	(cd coq-library-undecidability/ && make clean) || true
	(cd maple-mode/ && make clean) || true
