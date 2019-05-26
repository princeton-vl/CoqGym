(* This file is distributed under the terms of the MIT License, also
   known as the X11 Licence.  A copy of this license is in the README
   file that accompanied the original distribution of this file.

   Based on code written by:
     Brian Aydemir
     Arthur Charg\'eraud *)

Require Import Coq.Arith.Arith.
Require Import Coq.Arith.Max.
Require Import Coq.Classes.EquivDec.
Require Import Coq.Lists.List.
Require Import Coq.Structures.Equalities.

Require Import Coq.FSets.FSets.
Require Import Metalib.CoqListFacts.
Require Import Metalib.FSetExtra.
Require Import Metalib.FSetWeakNotin.
Require Import Metalib.LibTactics.

Require Import Omega.

(* ********************************************************************** *)
(** * Defining atoms *)

(** Atoms are structureless objects such that we can always generate
    one fresh from a finite collection.  Equality on atoms is [eq] and
    decidable.  We use Coq's module system to make abstract the
    implementation of atoms. *)

Module Type ATOM <: UsualDecidableType.

  Parameter atom : Set.
  Definition t := atom.

  Parameter eq_dec : forall x y : atom, {x = y} + {x <> y}.

  Parameter atom_fresh_for_list :
    forall (xs : list t), {x : atom | ~ List.In x xs}.

  Parameter fresh : list atom -> atom.

  Parameter fresh_not_in : forall l, ~ In (fresh l) l.

  Parameter nat_of : atom -> nat.

  Hint Resolve eq_dec.

  Include HasUsualEq <+ UsualIsEq <+ UsualIsEqOrig.


End ATOM.

(** The implementation of the above interface is hidden for
    documentation purposes. *)

Module Atom : ATOM.

  (* begin hide *)
  Definition atom := nat.
  Definition t := atom.

  Definition eq_dec := eq_nat_dec.

  Lemma max_lt_r : forall x y z,
    x <= z -> x <= max y z.
  Proof.
    induction x. auto with arith.
    induction y. auto with arith.
      simpl. induction z. omega. auto with arith.
  Qed.

  Lemma nat_list_max : forall (xs : list nat),
    { n : nat | forall x, List.In x xs -> x <= n }.
  Proof.
    induction xs as [ | x xs [y H] ].
    (* case: nil *)
    exists 0. inversion 1.
    (* case: cons x xs *)
    exists (max x y). intros z J. simpl in J. destruct J as [K | K].
      subst. auto with arith.
      auto using max_lt_r.
  Qed.

  Lemma atom_fresh_for_list :
    forall (xs : list nat), { n : nat | ~ List.In n xs }.
  Proof.
    intros xs. destruct (nat_list_max xs) as [x H].
    exists (S x). intros J. lapply (H (S x)). omega. trivial.
  Qed.

  Definition fresh (l : list atom) :=
    match atom_fresh_for_list l with
      (exist _ x _) => x
    end.

  Lemma fresh_not_in : forall l, ~ In (fresh l) l.
  Proof.
    intro l. unfold fresh.
    destruct atom_fresh_for_list. auto.
  Qed.

  Definition nat_of := fun (x : atom) => x.

  Include HasUsualEq <+ UsualIsEq <+ UsualIsEqOrig.

  (* end hide *)

End Atom.

(** We make [atom], [fresh], [fresh_not_in] and [atom_fresh_for_list] available
    without qualification. *)

Notation atom := Atom.atom.
Notation fresh := Atom.fresh.
Notation fresh_not_in := Atom.fresh_not_in.
Notation atom_fresh_for_list := Atom.atom_fresh_for_list.

(* Automatically unfold Atom.eq *)
Global Arguments Atom.eq /.

(** It is trivial to declare an instance of [EqDec] for [atom]. *)

Instance EqDec_atom : @EqDec atom eq eq_equivalence.
Proof. exact Atom.eq_dec. Defined.


(* ********************************************************************** *)
(** * Finite sets of atoms *)

(** We use our implementation of atoms to obtain an implementation of
    finite sets of atoms.  We give the resulting type an intuitive
    name, as well as import names of set operations for use within
    this library.  In order to avoid polluting Coq's namespace, we do
    not use [Module Export]. *)

Module Import AtomSetImpl : FSetExtra.WSfun Atom :=
  FSetExtra.Make Atom.

Notation atoms :=
  AtomSetImpl.t.

(** The [AtomSetDecide] module provides the [fsetdec] tactic for
    solving facts about finite sets of atoms. *)

Module Export AtomSetDecide := Coq.FSets.FSetDecide.WDecide_fun Atom AtomSetImpl.

(** The [AtomSetNotin] module provides the [destruct_notin] and
    [solve_notin] for reasoning about non-membership in finite sets of
    atoms, as well as a variety of lemmas about non-membership. *)

Module Export AtomSetNotin := FSetWeakNotin.Notin_fun Atom AtomSetImpl.

(** Given the [fsetdec] tactic, we typically do not need to refer to
    specific lemmas about finite sets.  However, instantiating
    functors from the FSets library makes a number of setoid rewrites
    available.  These rewrites are crucial to developments since they
    allow us to replace a set with an extensionally equal set (see the
    [Equal] relation on finite sets) in propositions about finite
    sets. *)

Module AtomSetFacts := FSetFacts.WFacts_fun Atom AtomSetImpl.
Module AtomSetProperties := FSetProperties.WProperties_fun Atom AtomSetImpl.

Export AtomSetFacts.

(* ********************************************************************** *)
(** * Properties *)

(** For any given finite set of atoms, we can generate an atom fresh
    for it. *)

Lemma atom_fresh : forall L : atoms, { x : atom | ~ In x L }.
Proof.
  intros L. destruct (atom_fresh_for_list (elements L)) as [a H].
  exists a. intros J. contradiction H.
  rewrite <- CoqListFacts.InA_iff_In. auto using elements_1.
Qed.


(* ********************************************************************** *)
(** * Tactic support for picking fresh atoms *)

(* begin hide *)

(** The auxiliary tactic [simplify_list_of_atom_sets] takes a list of
    finite sets of atoms and unions everything together, returning the
    resulting single finite set. *)

Ltac simplify_list_of_atom_sets L :=
  let L := eval simpl in L in
  let L := ltac_remove_dups L in
  let L := eval simpl in (List.fold_right union empty L) in
  match L with
    | context C [union ?E empty] => context C [ E ]
  end.

(* end hide *)

(** [gather_atoms_with F] returns the union of all the finite sets
    [F x] where [x] is a variable from the context such that [F x]
    type checks. *)

Ltac gather_atoms_with F :=
  let apply_arg x :=
    match type of F with
      | _ -> _ -> _ -> _ => constr:(@F _ _ x)
      | _ -> _ -> _ => constr:(@F _ x)
      | _ -> _ => constr:(@F x)
    end in
  let rec gather V :=
    match goal with
      | H : _ |- _ =>
        let FH := apply_arg H in
        match V with
          | context [FH] => fail 1
          | _ => gather (union FH V)
        end
      | _ => V
    end in
  let L := gather empty in eval simpl in L.

(** [beautify_fset V] assumes that [V] is built as a union of finite
    sets and returns the same set cleaned up: empty sets are removed
    and items are laid out in a nicely parenthesized way. *)

Ltac beautify_fset V :=
  let rec go Acc E :=
     match E with
     | union ?E1 ?E2 => let Acc2 := go Acc E2 in go Acc2 E1
     | empty => Acc
     | ?E1 => match Acc with
                | empty => E1
                | _ => constr:(union E1 Acc)
              end
     end
  in go empty V.

(** The tactic [pick fresh Y for L] takes a finite set of atoms [L]
    and a fresh name [Y], and adds to the context an atom with name
    [Y] and a proof that [~ In Y L], i.e., that [Y] is fresh for [L].
    The tactic will fail if [Y] is already declared in the context.

    The variant [pick fresh Y] is similar, except that [Y] is fresh
    for "all atoms in the context."  This version depends on the
    tactic [gather_atoms], which is responsible for returning the set
    of "all atoms in the context."  By default, it returns the empty
    set, but users are free (and expected) to redefine it. *)

Ltac gather_atoms :=
  constr:(empty).

Tactic Notation "pick" "fresh" ident(Y) "for" constr(L) :=
  let Fr := fresh "Fr" in
  let L := beautify_fset L in
  (destruct (atom_fresh L) as [Y Fr]).

Tactic Notation "pick" "fresh" ident(Y) :=
  let L := gather_atoms in
  pick fresh Y for L.

Ltac pick_fresh y :=
  pick fresh y.

(** Example: We can redefine [gather_atoms] to return all the
    "obvious" atoms in the context using the [gather_atoms_with] thus
    giving us a "useful" version of the "[pick fresh]" tactic. *)

Ltac gather_atoms ::=
  let A := gather_atoms_with (fun x : atoms => x) in
  let B := gather_atoms_with (fun x : atom => singleton x) in
  constr:(union A B).

Lemma example_pick_fresh_use : forall (x y z : atom) (L1 L2 L3: atoms), True.
(* begin show *)
Proof.
  intros x y z L1 L2 L3.
  pick fresh k.

  (** At this point in the proof, we have a new atom [k] and a
      hypothesis [Fr] that [k] is fresh for [x], [y], [z], [L1], [L2],
      and [L3]. *)

  trivial.
Qed.
(* end show *)
