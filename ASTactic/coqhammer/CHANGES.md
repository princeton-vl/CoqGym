
CoqHammer v. 1.1
================

Coq versions compatibility: 8.8.

Overview of changes
-------------------
* CVC4 integration.
* Minimization of dependencies.
* Parallel invocation of proof tactics.
* More reliable timeout mechanism based on `fork` and `wait`.
* Improvements in the reconstruction tactics, more rewrite hints for `sauto`.
* Change in reconstruction tactics interface. Tactics no longer need a
list of hypotheses, and a different set of tactics is used.
* Improvements in the translation.
* Messages now more user-friendly.
* `predict` tactic.
* Added `opam` support.
* More consistent removal of temporary files.
* Debugging commands.
* Tests (`make tests`).

Technical details of improvements to the translation
----------------------------------------------------
* Hashing of lifted-out terms.
* Type lifting (`opt_type_lifting`): hashing of types and lifting them out, e.g.,

```coq
forall f : nat -> nat, g : (nat -> nat) -> nat -> nat, ...
```

is translated to

```coq
forall f, T1(f) -> forall g, T2(g) -> ...
```

with axioms

```coq
forall f, T1(f) <-> forall x, nat(x) -> nat(f x)
forall g, T2(g) <-> forall h, T1(h) -> forall x, nat(x) -> nat(g h x)
```

instead of translating this to

```coq
forall f, (forall x, nat(x) -> nat(f x)) -> forall g, (forall h,
(forall x, nat(x) -> nat(h x))) -> forall x, nat(x) -> nat(g h x)) ->
...
```

* `Set` now collapsed to `Type`

CoqHammer v. 1.0
================

Coq versions compatibility: 8.6.

First complete CoqHammer version.
