**(OPTIONAL) To set up a separate Opam "universe" -- useful if you want
   multiple versions of Coq -- do:**

  1. `opam switch install coq8.5 --alias-of system`
  2. `` eval `opam config env` ``

**To install Coq 8.6 and MathComp (which now includes SSReflect):**

  1. `opam repo add coq-released https://coq.inria.fr/opam/released` (for
     SSReflect and MathComp)
  2. `opam update`
  3. `opam install coq.8.6 coq-mathcomp-ssreflect.1.6.1`

**install `metalib`:**

  1. See [instructions](https://github.com/plclub/metalib)

**(OPTIONAL) To install `lngen`:**

  1. `git clone https://github.com/plclub/lngen.git` in the same directory as
     `src` (so `src` and `lngen` are siblings).
  2. In the `lngen` directory, compile lngen
       `cabal sandbox init`
	   `cabal install`
  3. Makefile will look here
