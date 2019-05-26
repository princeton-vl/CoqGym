Require Import ExtLib.Structures.Monoid.

Set Implicit Arguments.
Set Strict Implicit.

Section Sets.
  Variable S : Type.
  Variable T : Type.

  Class DSet : Type :=
  { contains   : T -> S -> bool
  ; empty      : S
  ; singleton  : T -> S 
  ; union      : S -> S -> S
  ; filter     : (T -> bool) -> S -> S
  ; intersect  : S -> S -> S
  ; difference : S -> S -> S
  ; subset     : S -> S -> bool
    (** point-wise **)
  ; add        : T -> S -> S
  ; remove     : T -> S -> S
  }.

  Variable DS : DSet.
  Variable eqT : T -> T -> Prop.

  Class DSet_Laws : Type :=
  { DSet_WF : S -> Prop
  ; empty_WF : DSet_WF empty
  ; singleton_WF : forall x, DSet_WF (singleton x)
  ; union_WF : forall s s', DSet_WF s -> DSet_WF s' -> DSet_WF (union s s')
  ; filter_WF : forall s f, DSet_WF s -> DSet_WF (filter f s)
  ; intersect_WF : forall s s', DSet_WF s -> DSet_WF s' -> DSet_WF (intersect s s')
  ; difference_WF : forall s s', DSet_WF s -> DSet_WF s' -> DSet_WF (difference s s')
  ; add_WF : forall s x, DSet_WF s -> DSet_WF (add x s)
  ; remove_WF : forall s x, DSet_WF s -> DSet_WF (remove x s)

  ; empty_not_contains : forall t, contains t empty = false
  ; singleton_contains : forall t u, 
    contains t (singleton u) = true <-> eqT t u
  ; union_contains     : forall s s',
    DSet_WF s -> DSet_WF s' ->
    forall x, orb (contains x s) (contains x s') = contains x (union s s')
  ; intersect_contains : forall s s',
    DSet_WF s -> DSet_WF s' ->
    forall x, andb (contains x s) (contains x s') = contains x (intersect s s')
  ; difference_contains : forall s s',
    DSet_WF s -> DSet_WF s' ->
    forall x, andb (contains x s) (negb (contains x s')) = contains x (difference s s')
  ; subset_contains    : forall s s', 
    DSet_WF s -> DSet_WF s' ->
    subset s s' = true <-> 
    (forall x, contains x s = true -> contains x s' = true)

  ; add_contains       : forall s x, DSet_WF s -> 
    contains x (add x s) = true
  ; add_contains_not   : forall s x y, DSet_WF s -> 
    ~eqT x y -> contains x (add y s) = contains x s 
  ; remove_contains    : forall s x, DSet_WF s -> 
    contains x (remove x s) = false
  ; remove_contains_not : forall s x y, DSet_WF s -> 
    ~eqT x y -> contains x (remove y s) = contains x s
  }.

End Sets.

Arguments contains {S} {T} {_} _ _.
Arguments empty {S} {T} {_}.
Arguments singleton {S} {T} {_} _.
Arguments union {S} {T} {_} _ _.
Arguments intersect {S} {T} {_} _ _.
Arguments difference {S} {T} {_} _ _.
Arguments subset {S} {T} {_} _ _.
Arguments add {S} {T} {_} _ _.
Arguments remove {S} {T} {_} _ _.
Arguments filter {S} {T} {_} _ _.

Section monoid.
  Variable S : Type.
  Context {T : Type}.
  Context {set : DSet S T}.

  Definition Monoid_set_union : Monoid S :=
  {| monoid_plus := union
   ; monoid_unit := empty
  |}.
End monoid.
