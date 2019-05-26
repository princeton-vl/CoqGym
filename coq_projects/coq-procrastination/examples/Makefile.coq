############################################################################
# Requirements.

# We need bash. We use the pipefail option to control the exit code of a
# pipeline.

SHELL := /usr/bin/env bash

############################################################################
# Configuration
#
#
# This Makefile relies on the following variables:
# COQBIN     (default: empty)
# COQINCLUDE (default: empty)
# V          (default: *.v)
# V_AUX      (default: undefined/empty)
# SERIOUS    (default: 1)
#            (if 0, we produce .vio files)
#            (if 1, we produce .vo files in the old way)
# VERBOSE    (default: undefined)
#            (if defined, commands are displayed)

# We usually refer to the .v files using relative paths (such as Foo.v)
# but [coqdep -R] produces dependencies that refer to absolute paths
# (such as /bar/Foo.v). This confuses [make], which does not recognize
# that these files are the same. As a result, [make] does not respect
# the dependencies.

# We fix this by using ABSOLUTE PATHS EVERYWHERE. The paths used in targets,
# in -R options, etc., must be absolute paths.

ifndef V
	PWD := $(shell pwd)
	V := $(wildcard $(PWD)/*.v)
endif

# Typically, $(V) should list only the .v files that we are ultimately
# interested in checking. $(V_AUX) should list every other .v file in the
# project. $(VD) is obtained from $(V) and $(V_AUX), so [make] sees all
# dependencies and can rebuild files anywhere in the project, if needed, and
# only if needed.

ifndef VD
	VD  := $(patsubst %.v,%.v.d,$(V) $(V_AUX))
endif

VIO := $(patsubst %.v,%.vio,$(V))
VQ  := $(patsubst %.v,%.vq,$(V))
VO  := $(patsubst %.v,%.vo,$(V))

SERIOUS := 1

############################################################################
# Binaries

COQC   := $(COQBIN)coqc
COQDEP := $(COQBIN)coqdep
COQIDE := $(COQBIN)coqide
COQCHK := $(COQBIN)coqchk

############################################################################
# Targets

.PHONY: all proof depend quick proof_vo proof_vq

all: proof
ifeq ($(SERIOUS),0)
proof: proof_vq
else
proof: proof_vo
endif
proof_vq: $(VQ)
depend: $(VD)
quick: $(VIO)
proof_vo: $(VO)

############################################################################
# Verbosity control.

# Our commands are pretty long (due, among other things, to the use of
# absolute paths everywhere). So, we hide them by default, and echo a short
# message instead. However, sometimes one wants to see the command.

# By default, VERBOSE is undefined, so the .SILENT directive is read, so no
# commands are echoed. If VERBOSE is defined by the user, then the .SILENT
# directive is ignored, so commands are echoed, unless they begin with an
# explicit @.

ifndef VERBOSE
.SILENT:
endif

############################################################################
# Verbosity filter.

# Coq is way too verbose when using one of the -schedule-* commands.
# So, we grep its output and remove any line that contains 'Checking task'.

# We need a pipe that keeps the exit code of the *first* process. In
# bash, when the pipefail option is set, the exit code is the logical
# conjunction of the exit codes of the two processes. If we make sure
# that the second process always succeeds, then we get the exit code
# of the first process, as desired.

############################################################################
# Rules

# If B uses A, then the dependencies produced by coqdep are:
# B.vo:  B.v A.vo
# B.vio: B.v A.vio

%.v.d: %.v
	$(COQDEP) $(COQINCLUDE) $< > $@

ifeq ($(SERIOUS),0)

%.vo: %.vio
	@echo "Compiling `basename $*`..."
	set -o pipefail; ( \
	  $(COQC) $(COQINCLUDE) -schedule-vio2vo 1 $* \
	  2>&1 | (grep -v 'Checking task' || true))

# The recipe for producing %.vio destroys %.vo. In other words, we do not
# allow a young .vio file to co-exist with an old (possibly out-of-date) .vo
# file, because this seems to lead Coq into various kinds of problems
# ("inconsistent assumption" errors, "undefined universe" errors, warnings
# about the existence of both files, and so on). Destroying %.vo should be OK
# as long as the user does not try to build a mixture of .vo and .vio files in
# one invocation of make.
%.vio: %.v
	@echo "Digesting `basename $*`..."
	rm -f $*.vo
	$(COQC) $(COQINCLUDE) -quick $<

%.vq: %.vio
	@echo "Checking `basename $*`..."
	set -o pipefail; ( \
	  $(COQC) $(COQINCLUDE) -schedule-vio-checking 1 $< \
	  2>&1 | (grep -v 'Checking task' || true))
	touch $@

endif

ifeq ($(SERIOUS),1)

%.vo: %.v
	@echo "Compiling `basename $*`..."
	$(COQC) $(COQINCLUDE) $<

endif

_CoqProject: .FORCE
	@echo $(COQINCLUDE) > $@

.FORCE:

############################################################################
# Dependencies

ifeq ($(findstring $(MAKECMDGOALS),depend clean),)
-include $(VD)
endif

############################################################################
# IDE

.PHONY: ide

.coqide:
	@echo '$(COQIDE) $(COQINCLUDE) $$*' > .coqide
	@chmod +x .coqide

ide: _CoqProject
	$(COQIDE) $(COQINCLUDE)

############################################################################
# Clean

.PHONY: clean

clean::
	rm -f *~
	rm -f $(patsubst %.v,%.v.d,$(V)) # not $(VD)
	rm -f $(VIO) $(VO) $(VQ)
	rm -f *.aux .*.aux *.glob *.cache *.crashcoqide
	rm -rf .coq-native .coqide
	rm -f _CoqProject
# TEMPORARY *~, *.aux, etc. do not make sense in a multi-directory setting
