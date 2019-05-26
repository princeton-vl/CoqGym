# ![Logo](https://raw.githubusercontent.com/clarus/icons/master/list-48.png) ListPlus
More functions on lists.

## Install
### With OPAM
Add the [Coq repository](coq.io/opam/):

    opam repo add coq-released https://coq.inria.fr/opam/released

and run:

    opam install coq-list-plus

### From the sources
Run:

    ./configure.sh
    make
    make install

## Use
Add:

    Require Import ListPlus.All.

at the beginning of your source files.
