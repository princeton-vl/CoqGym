# The PCM library

The PCM library provides a formalisation of Partial Commutative Monoids (PCMs),
a common algebraic structure used in separation logic for verification of
pointer-manipulating sequential and concurrent programs.

The library provides lemmas for mechanised and automated reasoning about PCMs
in the abstract, but also supports concrete common PCM instances, such as heaps,
histories, and mutexes.

It is based on the [Coq](https://coq.inria.fr) proof assistant,
[SSReflect](https://coq.inria.fr/distrib/current/refman/ssreflect.html)
proof language, and [Mathcomp](https://github.com/math-comp/math-comp) library.

## Installation

The PCM library can be installed via [OPAM](https://opam.ocaml.org) package manager:

```
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq-fcsl-pcm
```

## Getting help

If you need assistance or would like to report a bug, drop us an email:
<fcsl@software.imdea.org>
or open an [issue](https://github.com/imdea-software/fcsl-pcm/issues).

## More Information

More information can be obtained via the [FCSL web page](https://software.imdea.org/fcsl/).
An earlier version of this library was developed as part of [Hoare type theory](https://software.imdea.org/~aleks/htt/).
