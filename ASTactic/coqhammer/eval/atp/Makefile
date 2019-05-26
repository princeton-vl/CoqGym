#
# ATP evaluation
#
# See README for details.
#

# input files
FFILES=$(shell find i/f/ -type f | sort -R)

# timeout (in seconds)
TIM=30

all: eprover vampire z3 cvc4

eprover: $(patsubst i/f/%,o/eprover/%,$(FFILES))
o/eprover/%: i/f/%
	@mkdir -p `dirname "$@"`
	@eprover -s --cpu-limit=$(TIM) --auto-schedule -R --print-statistics -p --tstp-format "$<"  | grep "file[(]'\|# SZS" > "$@"

vampire: $(patsubst i/f/%,o/vampire/%,$(FFILES))
o/vampire/%: i/f/%
	@mkdir -p `dirname "$@"`
	@htimeout $(TIM) vampire --mode casc -t $(TIM) --proof tptp --output_axiom_names on "$<" | grep "file[(]'\|% SZS" > "$@"

z3: $(patsubst i/f/%,o/z3/%,$(FFILES))
o/z3/%: i/f/%
	@mkdir -p `dirname "$@"`
	@htimeout $(TIM) z3_tptp -c -t:$(TIM) "-file:$<" > "$@"

cvc4: $(patsubst i/f/%,o/cvc4/%,$(FFILES))
o/cvc4/%: i/f/%
	@mkdir -p `dirname "$@"`
	@htimeout $(TIM) cvc4 --tlimit $(TIM) --dump-unsat-cores-full "$<" > "$@"
