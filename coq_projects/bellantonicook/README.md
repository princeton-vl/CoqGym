# BellantoniCook

The source code is covered by CeCILL-A licence (see the `LICENSE` file).
It was developed by Sylvain Heraud and David Nowak.

This a deep embedding of Bellantoni and Cook's syntactic characterization of polytime functions. We prove formally that it is correct and complete with respect to the original characterization by Cobham that required a bound to be proved manually. Compared to the paper proof by Bellantoni and Cook, we have been careful in making our proof fully contructive so that we obtain more precise bounding polynomials and more efficient translations between the two characterizations. Another difference is that we consider functions on bitstrings instead of functions on positive integers. This formalization is described in:

Sylvain Heraud and David Nowak.
_A formalization of polytime functions._
In Interactive Theorem Proving - Second International Conference, ITP 2011, Berg en Dal, The Netherlands, August 22-25, 2011. Proceedings, volume 6898 of Lecture Notes in Computer Science, pages 119--134.
Springer, 2011.

## Building

### By hand

This library builds with Coq between (at least) v8.6.0 and v8.8.1.

To build and install this library, run:

```
make
make install
```

### Using [OPAM]

You can also get and install this library using [OPAM] and the
[coq-released](https://coq.inria.fr/opam/released) repository (see the
[official documentation](https://coq.inria.fr/opam/www/using.html)):

```
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq-bellantonicook
```

[OPAM]: https://opam.ocaml.org/
