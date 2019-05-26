Cheerios
========

[![Build Status](https://api.travis-ci.org/uwplse/cheerios.svg?branch=master)](https://travis-ci.org/uwplse/cheerios)

Cheerios is a formally verified serialization library for Coq. It
defines a typeclass for serializable types and defines instances for
many built-in types. The specification of a serializable type requires
that serializing followed by deserializing is the identity.

By linking extracted code with the Cheerios OCaml runtime support library,
verified serializable types can be used in executable programs.

Requirements
------------

Definitions and proofs:

- [`Coq`](https://coq.inria.fr) (8.6.1, 8.7, 8.8, or 8.9)
- [`StructTact`](https://github.com/uwplse/StructTact)

Runtime:

- [`OCaml 4.02.3`](https://ocaml.org/docs/install.html) (or later)
- [`OCamlbuild`](https://github.com/ocaml/ocamlbuild)

Building
--------

The easiest way to install Cheerios is via [OPAM](http://opam.ocaml.org/doc/Install.html):

```
opam repo add distributedcomponents-dev http://opam-dev.distributedcomponents.net
opam install cheerios
```

To build Cheerios manually, first run `./configure` in the root directory, and then run `make`.

Runtime Library
---------------

To use serializable types in executable programs, code must be extracted to OCaml and
linked with the Cheerios runtime library. The connection between the Coq definitions
and the runtime library primitives is established in `ExtractOCamlCheeriosBasic.v`
in the `extraction` directory, which must be imported before extraction of serializable
types.

Note that if a Coq type is extracted to a custom OCaml type (e.g., `string` to `char list`),
extraction for serialization functions must be adjusted accordingly. Several files with such
extraction directives for serialization can be found in the `extraction` directory.

To install the runtime library via OPAM, make sure the `distributedcomponents-dev`
repo has been added as above and use the following command:

```
opam install cheerios-runtime
```

To compile the runtime library manually, go to the `runtime` directory and run `make`.

Projects using Cheerios
-----------------------

- [Verdi Raft](https://github.com/uwplse/verdi-raft)
- [Verdi LockServ](https://github.com/DistributedComponents/verdi-lockserv)
- [Verdi Chord](https://github.com/DistributedComponents/verdi-chord)
