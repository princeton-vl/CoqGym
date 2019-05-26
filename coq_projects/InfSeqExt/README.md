InfSeqExt
=========

[![Build Status](https://api.travis-ci.org/DistributedComponents/InfSeqExt.svg?branch=master)](https://travis-ci.org/DistributedComponents/InfSeqExt)

InfSeqExt is a Coq library for reasoning inductively and coinductively on infinite sequences, using modal operators similar to those in linear temporal logic (LTL).

InfSeqExt is based on an [earlier library](http://ieeexplore.ieee.org/xpls/abs_all.jsp?arnumber=5198503) by Deng and Monin. It is intended as a more comprehensive alternative to [`Streams`](https://coq.inria.fr/library/Coq.Lists.Streams.html) in the Coq standard library. In particular, InfSeqExt provides machinery commonly used when reasoning about temporal properties of system execution traces, and follows the modal operator [name conventions](http://spinroot.com/spin/Man/ltl.html) used in the Spin model checker. 

Requirements
------------

- [`Coq`](https://coq.inria.fr) (8.5, 8.6, 8.7, 8.8, or 8.9)

Building
--------

The easiest way to install InfSeqExt is via [OPAM](http://opam.ocaml.org/doc/Install.html):

```
opam repo add distributedcomponents-dev http://opam-dev.distributedcomponents.net
opam install InfSeqExt
```

To build InfSeqExt manually, first run `./configure` in the root directory, and then run `make`. The default namespace is `InfSeqExt`, so Coq files that rely on the libraries will typically include `Require Import InfSeqExt.infseq.`

Files
-----

- `infseq.v`: main definitions and results.
    * coinductive definition of infinite sequences
    * definitions and notations for modal operators and connectors
        - basic modal operators: `now`, `next`, `consecutive`, `always1`, `always`, `weak_until`, `until`, `release`, `eventually`
        - composite modal operators: `inf_often`, `continuously`
        - modal connectors: `impl_tl` (`->_`), `and_tl` (`/\_`), `or_tl` (`\/_`), `not_tl` (`~_`)
    * lemmas about modal operators and connectors
    * tactics
- `map.v`: corecursive definitions of the `map` and `zip` functions for use on infinite sequences, and related lemmas.
- `exteq.v`: coinductive definition of extensional equality (`exteq`) for infinite sequences, and related lemmas.
- `subseq.v`: coinductive definitions of infinite subsequences and related lemmas.
- `classical.v`: lemmas about modal operators and connectors when assuming classical logic (excluded middle).

Related Libraries
-----------------

InfSeqExt has some overlap with the less exhaustive [CTLTCTL](https://github.com/coq-contribs/ctltctl) and [LTL](https://github.com/coq-contribs/ltl) Coq contributions, which provide similar machinery. In contrast to CTLTCTL and LTL, InfSeqExt does not provide a definition of traces following some labeled reduction relation, nor an explicit notion of time. Fairness is also left up to library users to define.
