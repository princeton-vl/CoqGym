# input files
FFILES=$(shell find problems/ -name "*.v" | sort -R)
OFILES=$(patsubst problems/%.v,problems/%.vo,$(FFILES))

all:
	@echo "See README on how to invoke make."

init: $(OFILES)
problems/%.vo: problems/%.v
	@mkdir -p logs/init
	coqc "$<" > logs/init/`basename "$@" .vo`.log 2>&1

check: $(patsubst problems/%.v,logs/check/%.log,$(FFILES))
logs/check/%.log: problems/%.v
	@mkdir -p `dirname "$@"`
	coqc "$<" > "$@" 2>&1

atp: $(patsubst problems/%.v,logs/atp/%.log,$(FFILES))
logs/atp/%.log: problems/%.v
	@mkdir -p `dirname "$@"`
	coqc "$<" > "$@" 2>&1

reconstr: $(patsubst problems/%.v,logs/reconstr/%.log,$(FFILES))
logs/reconstr/%.log: problems/%.v
	@mkdir -p `dirname "$@"`
	coqc "$<" > "$@" 2>&1

clean-vo:
	rm -f $(OFILES)

clean: clean-vo
	rm -rf logs coqhammer.opt check.log gen_atp.log
	cd tools && $(MAKE) clean

clean-problems: clean-vo
	rm -f $(patsubst problems/%.v,problems/.%.aux,$(FFILES))
	rm -f $(patsubst problems/%.v,problems/%.v.bak,$(FFILES))
	rm -f $(patsubst problems/%.v,problems/%.glob,$(FFILES))

.PHONY: clean
