# ![Logo](https://raw.githubusercontent.com/clarus/icons/master/shield-48.png) CUnit
Convenience functions for unit testing in Coq.

    Require Import Coq.Lists.List.
    Require Import CUnit.All.

    Import ListNotations.

    Definition test_plus : List.map_pair plus
      [(0, 0); (0, 3); (4, 0); (4, 3)] =
      [0; 3; 4; 7] :=
      eq_refl.

## Install
### With OPAM
Install the [Coq repository](http://coq.io/opam/):

    opam repo add coq-released https://coq.inria.fr/opam/released

and run:

    opam install coq-cunit

### From the sources
Run:

    ./configure.sh
    make
    make install

## Reference
### List
* `List.map_pair {A B C} (f : A -> B -> C) (l : list (A * B)) : list C`
* `List.map_triple {A B C D} (f : A -> B -> C -> D) (l : list (A * B * C)) : list D`
* `List.map_quad {A B C D E} (f : A -> B -> C -> D -> E) (l : list (A * B * C * D)) : list E`
