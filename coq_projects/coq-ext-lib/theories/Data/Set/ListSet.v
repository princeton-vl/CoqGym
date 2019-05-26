Require Import List.
Require Import ExtLib.Structures.Sets.
Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Data.List.
Require Import ExtLib.Structures.Reducible.

Set Implicit Arguments.
Set Strict Implicit.


Section ListSet.

  Definition lset (T : Type) : Type :=
    list T.

  Variable T : Type.
  Variable R_dec : T -> T -> bool.

  Fixpoint lset_contains (v : T) (ls : lset T) : bool :=
    match ls with
      | nil => false
      | l :: ls => if R_dec v l then true else lset_contains v ls
    end.

  Definition lset_empty : lset T := nil.

  Definition lset_add (v : T) (ls : lset T) : lset T :=
    if lset_contains v ls then ls else v :: ls.

  Definition lset_remove (v : T) : lset T -> lset T :=
    List.filter (fun x => negb (R_dec v x)).

  Definition lset_union (l r : lset T) : lset T :=
    fold_left (fun x y => lset_add y x) l r.

  Definition lset_difference (l r : lset T) : lset T :=
    List.filter (fun x => negb (lset_contains x r)) l.

  Definition lset_intersect (l r : lset T) : lset T :=
    List.filter (fun x => lset_contains x r) l.

  Definition lset_subset (l r : lset T) : bool :=
    allb (fun x => lset_contains x r) l.

End ListSet.

Global Instance DSet_weak_listset {T} (R : T -> T -> Prop)
  (R_dec : RelDec R) : DSet (@lset T) T :=
{ contains  := lset_contains rel_dec
; empty     := lset_empty T
; add       := lset_add rel_dec
; singleton := fun x => lset_add rel_dec x (lset_empty T)
; remove    := lset_remove rel_dec
; union     := lset_union rel_dec
; intersect := lset_intersect rel_dec
; difference := lset_difference rel_dec
; subset     := lset_subset rel_dec
; filter     := @List.filter _
}.

Global Instance Foldable_listset {T} (R : T -> T -> Prop)
  : Foldable (lset T) T :=
  fun _ f a t => List.fold_left (fun x y => f y x) t a.

Require Import ExtLib.Structures.Functor.
Require Import ExtLib.Programming.Eqv.

Global Instance PFunctor_listset : PFunctor lset :=
{ FunP := fun t => { eqT : Eqv t & RelDec eqv }
; pfmap := fun _ B eqv_dec f s => 
  List.fold_left (fun acc x => lset_add (@rel_dec B (@eqv B (projT1 eqv_dec)) (projT2 eqv_dec)) (f x) acc) s (@lset_empty _)
}.
