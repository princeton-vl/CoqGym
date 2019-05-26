ChargeCore
==========

A library for embedded logics.

Install with OPAM
-----------------
Add the Coq repository:

    opam repo add coq-released https://coq.inria.fr/opam/released

and run:

    opam install coq-charge-core

To get the beta versions of Coq, activate the repository:

    opam repo add coq-core-dev https://coq.inria.fr/opam/core-dev

Bugs
----

If you find a bug, please report it on github: https://github.com/jesper-bengtson/ChargeCore/issues




Build Instructions
------------------

*Dependencies*
This library depends on [ExtLib](http://github.com/coq-ext-lib/coq-ext-lib).
If you have it installed then you don't need to do anything else. If you would
like to have a local copy that is not installed, download the project, to
../coq-ext-lib and build it.

If you are going to use dependencies that are *not* installed, you can add them
to the _CoqPaths file (not included). These paths will be copied to your
_CoqProject file and used for building.

*Installation*
Simply run ```make``` in this directory.
