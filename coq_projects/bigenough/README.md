[![Build Status](https://travis-ci.org/math-comp/bigenough.svg?branch=master)](https://travis-ci.org/math-comp/bigenough)

# A small library to do epsilon - N reasonning.

The repository contains a package to reasoning with big enough objects (mostly natural numbers).

This repository is essentially for archiving purposes as `bigenough` will be subsumed by the [near tactics](https://github.com/math-comp/analysis/blob/9bfd5a1971c6989f51d9c44341bb71b2fd5e3c76/topology.v#L93).

The formalization is based on the [Mathematical Components](https://github.com/math-comp/math-comp) library for the [Coq](https://coq.inria.fr) proof assistant, although it requires only the ssreflect package.

## Installation

If you already have OPAM installed:

```
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq-mathcomp-bigenough
```
