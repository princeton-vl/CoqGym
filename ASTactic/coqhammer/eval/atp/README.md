ATP performance evaluation
--------------------------

Given a set of ATP problems, the Makefile in this directory runs ATPs
to determine which problems ATPs are able to solve within a given time.

The input files need to be in subdirectories of `i`:

* `i/f` should contain all the FOF files to evaluate.
* `i/h` may contain all the THF files to evaluate.
* `i/w` may contain all the Why3 files to evaluate.

The outputs are written to `o/$prover_name/...`

To run, use `make -j 47 -k` (where 47 is the number of CPUs). The parameter `-k`
resumes evaluation in case of errors. The timeout can be set in the Makefile.
Optionally only particular provers may be specified, e.g. `make eprover`.

Warning: Rerun `make` to ensure that all problems were treated.
