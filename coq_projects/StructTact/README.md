StructTact
==========

[![Build Status](https://api.travis-ci.org/uwplse/StructTact.svg?branch=master)](https://travis-ci.org/uwplse/StructTact)

StructTact is a Coq library of "structural tactics" (`StructTactics.v`) as well as
libraries containing lemmas about lists (`Util.v`), finite types (`Fin.v`),
and orders on strings (`StringOrders.v`) that use the tactics library.

These files were originally developed in the context of [Verdi](https://github.com/uwplse/verdi),
but have since been factored out to make them easier to use in other projects.

If you are interested in using StructTact in a project that does not already
manage its dependencies, we recommend using [`coqproject.sh`](https://github.com/dwoos/coqproject).

Requirements
------------

- [`Coq`](https://coq.inria.fr) (8.5, 8.6, 8.7, 8.8, or 8.9)

Building
--------

The easiest way to install StructTact is via [OPAM](http://opam.ocaml.org/doc/Install.html):

```
opam repo add distributedcomponents-dev http://opam-dev.distributedcomponents.net
opam install StructTact
```

To build StructTact manually, first run `./configure` in the root directory, and then run `make`.

Usage
-----

The default namespace for the library files is `StructTact`. Hence, a Coq development
using structural tactics typically includes:

```coq
Require Import StructTact.StructTactics.
```

For tactic documentation, see the inline comments in [`StructTactics.v`](StructTactics.v).

The optional utility and finite type definitions and lemmas described below must be included
separately if needed:

```coq
Require Import StructTact.Util.
Require Import StructTact.Fin.
Require Import StructTact.StringOrders.
```

Structural Tactics
------------------

Structural tactics are named by analogy to the structural properties of
simple type systems: weakening, exchange, and contraction.
In the context of proof assistants, these are analogous to the ability to add
new hypotheses in the context, reorder existing hypotheses, and delete
unused hypotheses. Theoretically, Coq inherits these properties from the
underlying type system, but in practice, automatically generated hypothesis
names cause proof scripts to break when the context is adjusted in seemingly
irrelevant ways.

Structural tactics restore these properties at the level of Ltac by enabling a
style of proof where hypothesis names are never mentioned. When automatically
generated names change during proof development, structural tactics still work.

Util
----

This file collects definitions, lemmas, and tactics about lists, booleans, propositions, and
functions that were useful in other projects. Notably, the following files are exported:

* `BoolUtil.v`: general boolean lemmas, tactics, and definitions
* `PropUtil.v`: general lemmas about propositions and sum types
* `Update.v`: function `update` that modifies a function to return a new value for a specific argument
* `Update2.v`: function `update2` that modifies a function to return a new value for specific pair of arguments
* `ListTactics.v`: tactics operating on contexts with `map`, `NoDup`, and `In`
* `ListUtil.v`: general list lemmas, involving, e.g., `NoDup`, `map`, `filter`, and `firstn`
* `Assoc.v`: association lists with get, set, and delete functions
* `Before.v`: relation `before` capturing when an element appears before another in a list
* `Dedup.v`: function `dedup` remove duplicates from a list using decidable equality
* `FilterMap.v`: function `filterMap` that maps a partial function on a list and ignores failures
* `Nth.v`: relation `Nth` capturing the element at some position in a list
* `Prefix.v`: relation `Prefix` capturing when one list is a prefix of another
* `RemoveAll.v`: function `remove_all` which removes all elements of one list from another; set subtraction
* `Subseq.v`: relation `subseq` capturing when one list is a subsequence of another

Fin
---

This file contains an definitions and lemmas related to `fin n`, a type with `n` elements,
isomorphic to `Fin.t n` from the standard library, but with a slightly different
definition that is more convenient to work with.

The following constructions are defined on `fin`:

* `fin_eq_dec`: decidable equality
* `all_fin n`: list of all elements of `fin n`
* `fin_to_nat`: convert a `fin n` to a `nat`
* `fin_lt`: an ordering on `fin n`, implemented using `fin_to_nat`
* `fin_OT_compat`: legacy `OrderedType` module for `fin n` (for use with `FMap`)
* `fin_OT`: modern `OrderedType` module for `fin n` (for use with `MSet`)
* `fin_of_nat`: convert a `nat` to a `fin n`, when possible

String Orders
-------------

This file contains some order relations on strings, in particular a total lexicographic order.

The following modules are defined:

* `string_lex_as_OT_compat`: legacy `OrderedType` module for `string` (for use with `FMap`)
* `string_lex_as_OT`: modern `OrderedType` module for `string` (for use with `MSet`)
