##############################################################################
# To specify the location of the Coq binaries, create a file called
# settings.sh and define the variable COQBIN (with trailing slash),
# e.g.
#   COQBIN=/var/tmp/coq/bin/
# If this file is absent, then COQBIN is empty and "coqc" is used.

-include settings.sh

##############################################################################
# Define COQINCLUDE.

PWD := $(shell pwd)
PROCRASTINATION := $(shell cd ../src && pwd)

COQINCLUDE := \
  -R $(PWD) Examples \
  -R $(PROCRASTINATION) Procrastination \

##############################################################################
# Define V and VD.

# The variable V specifies which files should be (ultimately) processed by Coq.
# It is computed late, after CFML has produced the files %_ml.v in $(CF). Note
# that V is assigned using = instead of :=.

# The variable V_AUX specifies which extra dependencies Coq should see.
# We leave it empty unless ARTHUR is defined.

# These variables are used by Makefile.coq.

V = $(shell find $(PWD) -name "*.v" | grep -vw _output)

##############################################################################

# Export every variable to every sub-make.
export

##############################################################################
# Compilation.

.PHONY: all clean

all:
	@ $(MAKE) --no-print-directory -C .. $@
	@ $(MAKE) --no-print-directory -f Makefile.coq _CoqProject $@

clean:
	@ $(MAKE) --no-print-directory -f Makefile.coq $@
