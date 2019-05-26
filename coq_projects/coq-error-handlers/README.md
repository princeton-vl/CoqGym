# ![Logo](https://raw.githubusercontent.com/clarus/icons/master/castle-48.png) Error Handlers
Simple. Robust. Ubiquitous.

## Install
### With OPAM
Add the [Coq repository](http://coq.io/opam/):

    opam repo add coq-released https://coq.inria.fr/opam/released

and run:

    opam install -j4 coq-error-handlers

### From the sources
Do a classic:

    ./configure.sh
    make
    make install

## Use
Add:

    Require Import ErrorHandlers.All.

at the beginning of your source files. It will import the following functions:

* `Option.bind : forall {A B}, option A -> (A -> option B) -> option B`
* `Option.map : forall {A B}, option A -> (A -> B) -> option B`
* `Option.default : forall {A}, option A -> A -> A`
* `Sum.bind : forall {E A B}, A + E -> (A -> B + E) -> B + E`
* `Sum.map : forall {E A B}, A + E -> (A -> B) -> B + E`
* `Sum.default : forall {E A}, A + E -> A -> A`
