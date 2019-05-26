# Purely functional IO for Coq [![Build Status](https://travis-ci.org/Lysxia/coq-simple-io.svg?branch=master)](https://travis-ci.org/Lysxia/coq-simple-io)

An IO monad with user-definable primitive operations.

This library provides tools to implement IO programs directly in Coq, in a
similar style to Haskell.

Facilities for formal verification are not included.
There is no canonical way to describe the effects of the arbitrary foreign
constructs that this library allows, so this library commits to none.

## Installation

### From OPAM

```
opam install coq-simple-io
```

### From this repository as a local package

```
# Clone this repository
git clone https://github.com/Lysxia/coq-simple-io

# Register it with opam (the last argument is the path to the repo)
opam pin add coq-simple-io ./coq-simple-io
```

## Interface

To use this library:

```coq
Require Import SimpleIO.SimpleIO.
```

Combinators for IO actions.

```coq
Parameter IO : Type -> Type.

Module IO.

Parameter ret : forall {a}, a -> IO a.
Parameter bind : forall {a b}, IO a -> (a -> IO b) -> IO b.
Parameter fix_io : forall {a b}, ((a -> IO b) -> (a -> IO b)) -> a -> IO b.
(* etc. *)

End IO.
```

## Defining IO actions

The `IO` type extracts to the following definition in OCaml:

```ocaml
(* Implicitly [forall r, (a -> r) -> r]. *)
type 'a coq_IO = ('a -> Obj.t) -> Obj.t
```

So an effectful function `f : t -> u -> v` in OCaml can be wrapped
as a Coq function `f : t -> u -> IO v` in the following way:

```coq
Parameter f : t -> u -> IO v.
Extract Constant f => "fun a b k -> k (f a b)".
```

Basically, add an extra parameter `k` and apply it to the OCaml function call.

## Library organization

The source code can be found under `src/`.

- `SimpleIO.SimpleIO`: Reexports default modules.

The following modules are imported with `SimpleIO.SimpleIO`.

- `SimpleIO.IO_Monad`: Definition of `IO` and basic combinators.
- `SimpleIO.IO_Pervasives`: Wrappers around `Pervasives` from OCaml's standard library.
- `SimpleIO.IO_PervasivesAxioms`: Theory for `IO_Pervasives`
- `SimpleIO.IO_Exceptions`: Catch common exceptions.
- `SimpleIO.IO_RawChar`: Utilities that rely on `ExtrOcamlString`.
- `SimpleIO.IO_String`: Operations on OCaml strings.

The following module can be imported separately.

- `SimpleIO.IO_Unsafe`: Unsafe operations.
- `SimpleIO.IO_UnsafeNat`: `Pervasives` functions adapted to `nat`.

## Organization

Regular development happens on the `master` branch. I will synchronize the `dev`
branch regularly to publish changes to Coq CI and coq-extra-dev.

## Related

- [Ynot](https://github.com/ynot-harvard/ynot)
- [Coq.io](http://coq.io)
