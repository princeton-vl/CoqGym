# Cecoa

The source code is covered by CeCILL-A licence (see the `LICENSE` file).
It was developed by:

-   Hugo Férée,
-   Samuel Hym,
-   Micaela Mayero,
-   Jean-Yves Moyen,
-   David Nowak.

This work is based on quasi-interpretations as described in
Sections 2 and 3 of:  
P. Baillot, U. Dal Lago, and J. Y. Moyen.  
_On quasi-interpretations, blind abstractions and implicit complexity._  
Mathematical Structures in Computer Science, 22(04), 549-580.  
Cambridge University Press, 2012.

It is a tool to write programs and to prove that they are computing
polytime functions.
It consists of:

-   a formalization in Coq of quasi-interpretations,
-   some tooling to write a program in that formalism and prove that
    it has the required properties, so that the theorem bounding the
    complexity applies.


##  Building

### By hand

Cecoa builds with Coq between (at least) v8.6.0 and v8.8.1.

It requires the Coq library
[BellantoniCook](https://github.com/davidnowak/bellantonicook)
that provides a formalization in Coq of Bellantoni and Cook’s
characterization of polytime functions.
So you will have to download and build that library first.
Then you can either `make install` it or add to your `COQPATH` the directory
`path/to/bellantonicook/src`.

Then, you can simply run `make` to build this library and the examples.

### Using [OPAM]

You can also get and install Cecoa using [OPAM] and the
[coq-released](https://coq.inria.fr/opam/released) repository (see the
[official documentation](https://coq.inria.fr/opam/www/using.html)):

```
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq-cecoa
```

[OPAM]: https://opam.ocaml.org/


##  Contents

The `src/Cecoa` directory contains our library, in particular the
`Interface.v` provided to use its results easily.

The `src/Cecoa/Examples/` directory contains a few examples of
programs, the proofs that they admit a quasi-interpretation and so
that they are polytime.
