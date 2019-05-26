(* This program is free software; you can redistribute it and/or      *)
(* modify it under the terms of the GNU Lesser General Public License *)
(* as published by the Free Software Foundation; either version 2.1   *)
(* of the License, or (at your option) any later version.             *)
(*                                                                    *)
(* This program is distributed in the hope that it will be useful,    *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of     *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the      *)
(* GNU General Public License for more details.                       *)
(*                                                                    *)
(* You should have received a copy of the GNU Lesser General Public   *)
(* License along with this program; if not, write to the Free         *)
(* Software Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA *)
(* 02110-1301 USA                                                     *)


Require Import IZF_logic.
Require Import IZF_base.
Require Import IZF_nat.

(*************)
(** * Zero   *)
(*************)

(** In set theory, zero is implemented as the empty set.  As a
    pointed graph, we can take any (non-empty) carrier and any
    root, with an empty edge relation: *)

Definition unit : Typ1 := forall X : Typ0, X -> X.
Definition id : unit := fun X x => x.
Definition ZERO : Rel unit := fun _ _ => bot.

Lemma ZERO_elim :
 forall (X : Typ1) (A : Rel X) (a : X), ELT X A a unit ZERO id -> bot.

Proof.
intros X A a H; apply H.
intros b' H1 H2; exact H1.
Qed.

(*******************************)
(** * The successor function   *)
(*******************************)

(** In set theory, the successor of von Neumann numeral n is encoded
    as the set  n U {n}, whose existence follows from the pairing
    axiom (used twice) and the union axiom, that have been already
    derived in the files "IZF_pair.v"  and "IZF_union.v".

    However, it is simpler to give here a direct implementation of the
    successor as follows.  Formally, the successor of a given pointed
    graph (X, A, a) is represented as the pointed graph

        ((opt X), (SUCC X A a), (none X))

    whose edge relation is defined by the following three clauses:

    1. Delocate A in the new graph via (some X):

         if (A x' x), then (SUCC X A a (some X x') (some X x))

    2. Connect the image of any direct element of the old root a:X
       to the new root:

         if (A x a), then (SUCC X A a (some X x) (none X))

    3. Connect the old root to the new root:

         (SUCC X A a (some X a) (none X)).

    As usual, we use a second-order encoding to define this relation. *)

Definition SUCC (X : Typ1) (A : Rel X) (a : X) : Rel (opt X) :=
  fun z' z =>
  forall E : Prop,
  (forall x x' : X,
   eq (opt X) z (some X x) -> eq (opt X) z' (some X x') -> A x' x -> E) ->
  (forall x' : X,
   eq (opt X) z (none X) -> eq (opt X) z' (some X x') -> A x' a -> E) ->
  (eq (opt X) z (none X) -> eq (opt X) z' (some X a) -> E) -> E.

Lemma SUCC_in :
 forall (X : Typ1) (A : Rel X) (a x x' : X),
 A x' x -> SUCC X A a (some X x') (some X x).

Proof
  fun X A a x x' H E H1 _ _ =>
  H1 x x' (eq_refl (opt X) (some X x)) (eq_refl (opt X) (some X x')) H.

Lemma SUCC_rt1 :
 forall (X : Typ1) (A : Rel X) (a x' : X),
 A x' a -> SUCC X A a (some X x') (none X).

Proof
  fun X A a x' H E _ H2 _ =>
  H2 x' (eq_refl (opt X) (none X)) (eq_refl (opt X) (some X x')) H.

Lemma SUCC_rt2 :
 forall (X : Typ1) (A : Rel X) (a : X), SUCC X A a (some X a) (none X).

Proof
  fun X A a E _ _ H3 =>
  H3 (eq_refl (opt X) (none X)) (eq_refl (opt X) (some X a)).

Lemma SUCC_deloc :
 forall (X : Typ1) (A : Rel X) (a : X),
 deloc X A (opt X) (SUCC X A a) (some X).

Proof.
intros X A a; unfold deloc in |- *; apply and_intro.
(* Deloc 1 *)
intros; apply SUCC_in; assumption.
(* Deloc 2 *)
intros x y' H; apply H; clear H.
(* Deloc 2, case 1 *)
intros x0 x' H1 H2 H3; apply ex2_intro with x'.
apply (eq_sym _ _ _ (eq_some_some X x x0 H1)); assumption.
assumption.
(* Deloc 2, case 2 (absurd) *)
intros x' H1 H2 H3; apply (eq_some_none _ _ H1).
(* Deloc 2, case 3 (absurd) *)
intros H1 H2; apply (eq_some_none _ _ H1).
Qed.

Lemma SUCC_eqv :
 forall (X : Typ1) (A : Rel X) (a x : X),
 EQV X A x (opt X) (SUCC X A a) (some X x).

Proof.
intros X A a x; apply EQV_deloc; apply SUCC_deloc.
Qed.

Lemma SUCC_intro1 :
 forall (X : Typ1) (A : Rel X) (a : X) (Y : Typ1) (B : Rel Y) (b : Y),
 ELT Y B b X A a -> ELT Y B b (opt X) (SUCC X A a) (none X).

Proof.
intros X A a Y B b H; apply H; clear H; intros a' H1 H2.
apply ELT_intro with (some X a'). apply SUCC_rt1; assumption.
apply EQV_trans with X A a'. assumption. apply SUCC_eqv.
Qed.

Lemma SUCC_intro2 :
 forall (X : Typ1) (A : Rel X) (a : X),
 ELT X A a (opt X) (SUCC X A a) (none X).

Proof.
intros X A a; apply ELT_intro with (some X a).
apply SUCC_rt2. apply SUCC_eqv.
Qed.

Lemma SUCC_elim :
 forall (X : Typ1) (A : Rel X) (a : X) (Y : Typ1) (B : Rel Y) (b : Y),
 ELT Y B b (opt X) (SUCC X A a) (none X) ->
 or (ELT Y B b X A a) (EQV Y B b X A a).

Proof.
intros X A a Y B b H; apply H; clear H.
intros z' H H1; apply H; clear H.
(* Case 1 (absurd) *)
intros x x' H2 H3 H4; apply (eq_none_some _ _ H2).
(* Case 2 *)
intros x' H2 H3 H4; apply or_inl; apply ELT_intro with x'.
assumption.
apply EQV_trans with (opt X) (SUCC X A a) (some X x').
apply H3; assumption. apply EQV_sym; apply SUCC_eqv.
(* Case 3 *)
intros H2 H3; apply or_inr.
apply EQV_trans with (opt X) (SUCC X A a) (some X a).
apply H3; assumption. apply EQV_sym; apply SUCC_eqv.
Qed.

Lemma successor :
 forall (X : Typ1) (A : Rel X) (a : X) (Y : Typ1) (B : Rel Y) (b : Y),
 iff (ELT Y B b (opt X) (SUCC X A a) (none X))
   (or (ELT Y B b X A a) (EQV Y B b X A a)).

Proof.
intros X A a Y B b; unfold iff in |- *.
apply and_intro; intro H.
(* Direct implication (elim) *)
apply SUCC_elim; assumption.
(* Converse implication (intro1,2) *)
apply H; clear H; intro H.
apply SUCC_intro1; assumption.
apply ELT_compat_l with X A a.
assumption. apply SUCC_intro2.
Qed.

Lemma SUCC_compat :
 forall (X : Typ1) (A : Rel X) (a : X) (Y : Typ1) (B : Rel Y) (b : Y),
 EQV X A a Y B b ->
 EQV (opt X) (SUCC X A a) (none X) (opt Y) (SUCC Y B b) (none Y).

Proof.
cut
 (forall (X : Typ1) (A : Rel X) (a : X) (Y : Typ1) (B : Rel Y) (b : Y),
  EQV X A a Y B b ->
  SUB (opt X) (SUCC X A a) (none X) (opt Y) (SUCC Y B b) (none Y)).
intros H X A a Y B b H1; apply extensionality.
apply H; assumption. apply H; apply EQV_sym; assumption.
unfold SUB in |- *; intros X A a Y B b H Z C c H1.
apply (SUCC_elim X A a Z C c H1); clear H1; intro H1.
apply SUCC_intro1; apply ELT_compat_r with X A a; assumption.
apply ELT_compat_l with Y B b.
apply EQV_trans with X A a; assumption.
apply SUCC_intro2.
Qed.

(**************************************)
(** * The set of von Neuman numerals  *)
(**************************************)

(** The set omega of von Neumann numerals is represented as the
    pointed graph ((opt nat), OMEGA, (none nat)) whose edge
    relation OMEGA : (Rel (opt nat)) is defined by the following
    two clauses:

    1. Delocation of the strict ordering "lt"

         if (wf_nat n), (wf_nat m) and (lt n m),
         then (OMEGA (some nat n) (some nat m))

    2. Connecting wf_nat's to the new root:

         if (wf_nat n), then (OMEGA (some nat n) (none nat)).

    As usual, we define it via a second-order encoding: *)

Definition OMEGA : Rel (opt nat) :=
  fun z' z =>
  forall E : Prop,
  (forall n n' : nat,
   eq (opt nat) z (some nat n) ->
   eq (opt nat) z' (some nat n') -> wf_nat n -> wf_nat n' -> lt n' n -> E) ->
  (forall n' : nat,
   eq (opt nat) z (none nat) ->
   eq (opt nat) z' (some nat n') -> wf_nat n' -> E) -> E.

(** The corresponding constructors are the following: *)

Lemma OMEGA_in :
 forall n : nat,
 wf_nat n ->
 forall m : nat, wf_nat m -> lt n m -> OMEGA (some nat n) (some nat m).

Proof
  fun n Hn m Hm H E H1 _ =>
  H1 m n (eq_refl (opt nat) (some nat m)) (eq_refl (opt nat) (some nat n)) Hm
    Hn H.

Lemma OMEGA_rt : forall n : nat, wf_nat n -> OMEGA (some nat n) (none nat).

Proof
  fun n Hn E _ H2 =>
  H2 n (eq_refl (opt nat) (none nat)) (eq_refl (opt nat) (some nat n)) Hn.

(** The pointed graph ((opt nat), OMEGA, (some nat O)) is bisimilar
    to the pointed graph (unit ZERO id) that represents the empty set.
    This is done by extensionality. *)

Lemma OMEGA_ZERO : EQV (opt nat) OMEGA (some nat O) unit ZERO id.

Proof.
apply extensionality; unfold SUB in |- *; intros X A a H.
(* Direct inclusion *)
apply H; clear H; intros z H H1; apply H; clear H.
(* Case 1 (absurd) *)
intros n m H2 H3 Hn Hm H4.
generalize (eq_sym _ _ _ (eq_some_some _ _ _ H2)); intro H5.
apply (lt_n_O m (H5 (lt m) H4)).
(* Case 2 (absurd) *)
intros n H2 H3 Hn; apply (eq_some_none _ _ H2).
(* Converse inclusion *)
apply H; clear H; intros u H H1; apply H.
Qed.

(** Inductive case: for any n:nat such that (wf_nat n), the pointed
    graph ((opt nat), OMEGA, (some nat (S n))) is bisimilar to the
    successor of the pointed graph ((opt nat), OMEGA, (some nat n)).
    Again, this is done by extensionality. *)

Lemma OMEGA_SUCC :
 forall n : nat,
 wf_nat n ->
 EQV (opt nat) OMEGA (some nat (S n)) (opt (opt nat))
   (SUCC (opt nat) OMEGA (some nat n)) (none (opt nat)).

Proof.
intros n Hn; apply extensionality; unfold SUB in |- *; intros X A a H.
(* Direct inclusion *)
apply H; clear H; intros z H H1; apply H; clear H.
(* Case 1 *)
intros n0 m H H2 Hn0 Hm H3.
generalize (eq_sym _ _ _ (eq_some_some _ _ _ H)); clear H; intro H.
generalize (H (lt m) H3); clear H H3 Hn0 n0; intro H3.
(* Case 1: Case disjunction on (lt m (S n)) *)
apply (lt_n_Sm m Hm n Hn H3); clear H3; intro H3.
(* Case 1a: (lt m n) *)
apply SUCC_intro1; apply ELT_intro with (some nat m).
exact (OMEGA_in m Hm n Hn H3).  apply H2; assumption.
(* Case 1b: (eq nat m n) *)
apply ELT_compat_l with (opt nat) OMEGA (some nat n).
apply H3; apply H2; assumption.  apply SUCC_intro2.
(* Case 2 (absurd) *)
intros m H H2 Hm; apply (eq_some_none _ _ H).
(* Converse inclusion *)
apply (SUCC_elim _ _ _ _ _ _ H); clear H; intro H.
(* Case 1 *)
apply H; clear H; intros z H H1; apply H; clear H.
(* Case 1a *)
intros n0 m H H2 Hn0 Hm H3.
generalize (eq_sym _ _ _ (eq_some_some _ _ _ H)); clear H; intro H.
generalize (H (lt m) H3); clear H H3 Hn0 n0; intro H3.
apply ELT_intro with (some nat m).
exact (OMEGA_in m Hm (S n) (wf_nat_S n Hn) (lt_S m n H3)).
apply H2; assumption.
(* Case 1b (absurd) *)
intros m H H2 Hm; apply (eq_some_none _ _ H).
(* Case 2 *)
apply ELT_intro with (some nat n).
exact (OMEGA_in n Hn (S n) (wf_nat_S n Hn) (lt_n_Sn n)).
assumption.
Qed.

(** ** The axiom of infinity **)

(** The set denoted by the pointed graph ((opt nat), OMEGA, (none nat))
    contains zero (i.e. the empty set)... *)

Theorem omega_zero : ELT unit ZERO id (opt nat) OMEGA (none nat).

Proof.
apply ELT_intro with (some nat O).
exact (OMEGA_rt O wf_nat_O).
apply EQV_sym; exact OMEGA_ZERO.
Qed.

(** ... and is closed under successor: *)

Theorem omega_succ :
 forall (X : Typ1) (A : Rel X) (a : X),
 ELT X A a (opt nat) OMEGA (none nat) ->
 ELT (opt X) (SUCC X A a) (none X) (opt nat) OMEGA (none nat).

Proof.
intros X A a H; apply H; clear H; intros z H H1; apply H; clear H.
(* Case 1 (absurd) *)
intros n m H H2 Hn Hm H3; apply (eq_none_some _ _ H).
(* Case 2 *)
intros n H0 H Hn; apply ELT_intro with (some nat (S n)).
exact (OMEGA_rt (S n) (wf_nat_S n Hn)).
apply
 EQV_trans
  with (opt (opt nat)) (SUCC (opt nat) OMEGA (some nat n)) (none (opt nat)).
apply SUCC_compat; apply H; assumption.
apply EQV_sym; apply OMEGA_SUCC; assumption.
Qed.

(** And we now check the induction principle on omega: *)

Require Import IZF_select.  (* For PRED and Compat *)

Theorem omega_ind
 :
 (* If P is a compatible predicate such that: *)
 forall P : PRED,
 Compat P ->
 (* 1. P holds for zero *)
 P unit ZERO id ->
 (* 2. If P holds for an element of omega, then
         P holds for the successor of this element *)
 (forall (X : Typ1) (A : Rel X) (a : X),
  ELT X A a (opt nat) OMEGA (none nat) ->
  P X A a -> P (opt X) (SUCC X A a) (none X)) ->
 (* Then: P holds for any element of omega *)
 forall (X : Typ1) (A : Rel X) (a : X),
 ELT X A a (opt nat) OMEGA (none nat) -> P X A a.

Proof.
intros P HP HO HS X A a H; apply H; clear H.
intros z H H1; apply H; clear H.
(* Case 1 (absurd) *)
intros n m H H2 Hn Hm H3; apply (eq_none_some _ _ H).
(* Case 2 *)
intros n H0 H Hn; clear H0.
apply (HP _ _ _ _ _ _ (EQV_sym _ _ _ _ _ _ H1)).
apply (eq_sym _ _ _ H); clear H H1 a A X z.
(* Perform induction on n:nat *)
apply (nat_ind' n Hn); clear Hn n.
(* Basic case *)
apply HP with unit ZERO id.
apply EQV_sym; exact OMEGA_ZERO. assumption.
(* Inductive case *)
intros n Hn Hind.
apply
 HP with (opt (opt nat)) (SUCC (opt nat) OMEGA (some nat n)) (none (opt nat)).
apply EQV_sym; apply OMEGA_SUCC; assumption.
apply HS. apply ELT_direct; apply OMEGA_rt; assumption.
assumption.
Qed.
