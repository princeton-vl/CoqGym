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

Definition PRED := forall X : Typ1, Rel X -> X -> Prop.

Definition Compat (P : PRED) : Prop :=
  forall (X : Typ1) (A : Rel X) (a : X) (Y : Typ1) (B : Rel Y) (b : Y),
  EQV X A a Y B b -> P X A a -> P Y B b.

Definition SELECT (X : Typ1) (A : Rel X) (a : X) (P : PRED) : 
  Rel (opt X) :=
  fun z' z : opt X =>
  forall E : Prop,
  (forall x x' : X,
   eq (opt X) z (some X x) -> eq (opt X) z' (some X x') -> A x' x -> E) ->
  (forall x' : X,
   eq (opt X) z' (some X x') ->
   eq (opt X) z (none X) -> A x' a -> P X A x' -> E) -> E.

Lemma SELECT_in :
 forall (X : Typ1) (A : Rel X) (a : X) (P : PRED) (x x' : X),
 A x' x -> SELECT X A a P (some X x') (some X x).

Proof
  fun X A a P x x' H E e _ =>
  e x x' (eq_refl (opt X) (some X x)) (eq_refl (opt X) (some X x')) H.

Lemma SELECT_rt :
 forall (X : Typ1) (A : Rel X) (a : X) (P : PRED) (x' : X),
 A x' a -> P X A x' -> SELECT X A a P (some X x') (none X).

Proof
  fun X A a P x' H1 H2 E _ e =>
  e x' (eq_refl (opt X) (some X x')) (eq_refl (opt X) (none X)) H1 H2.

Lemma SELECT_deloc :
 forall (X : Typ1) (A : Rel X) (a : X) (P : PRED),
 deloc X A (opt X) (SELECT X A a P) (some X).

Proof.
intros X A a P; unfold deloc in |- *; apply and_intro.
(* Deloc 1 *)
exact (SELECT_in X A a P).
(* Deloc 2 (case distinction *)
intros x z' H; apply H; clear H.
(* Deloc 2, case 1 *)
intros x0 x' H1 H2 H3; apply ex2_intro with x'.
apply (eq_sym _ _ _ (eq_some_some X x x0 H1)); assumption.
assumption.
(* Deloc 2, case 2 (absurd) *)
intros x' H1 H2 H3 H4; apply (eq_some_none X x H2).
Qed.

Lemma SELECT_eqv :
 forall (X : Typ1) (A : Rel X) (a : X) (P : PRED) (x : X),
 EQV X A x (opt X) (SELECT X A a P) (some X x).

Proof.
intros X A a P x; apply EQV_deloc; apply SELECT_deloc.
Qed.

Lemma selection_intro :
 forall (X : Typ1) (A : Rel X) (a : X) (P : PRED),
 Compat P ->
 forall (Y : Typ1) (B : Rel Y) (b : Y),
 ELT Y B b X A a -> P Y B b -> ELT Y B b (opt X) (SELECT X A a P) (none X).

Proof.
intros X A a P H1 Y B b H H2; apply H; clear H; intros x' H3 H4.
apply ELT_intro with (some X x').
apply SELECT_rt; [ assumption | exact (H1 _ _ _ _ _ _ H4 H2) ].
apply EQV_trans with X A x'; [ assumption | apply SELECT_eqv ].
Qed.

Lemma selection_elim :
 forall (X : Typ1) (A : Rel X) (a : X) (P : PRED),
 Compat P ->
 forall (Y : Typ1) (B : Rel Y) (b : Y),
 ELT Y B b (opt X) (SELECT X A a P) (none X) ->
 and (ELT Y B b X A a) (P Y B b).

Proof.
intros X A a P H1 Y B b H; apply H; clear H.
intros z' H H2; apply H; clear H.
(* Case 1 (absurd) *)
intros x x' H3 H4 H5; apply (eq_none_some X x H3).
(* Case 2 *)
intros x' H3 H4 H5 H6; apply and_intro.
(* Case 2, first conclusion *)
apply ELT_intro with x'. assumption.
apply EQV_trans with (opt X) (SELECT X A a P) z'. assumption.
apply (eq_sym _ _ _ H3); apply EQV_sym; apply SELECT_eqv.
(* Case 2, second conclusion *)
apply H1 with X A x'.
apply EQV_trans with (opt X) (SELECT X A a P) z'.
apply (eq_sym _ _ _ H3); apply SELECT_eqv.
apply EQV_sym; assumption. assumption.
Qed.

Theorem selection :
 forall (X : Typ1) (A : Rel X) (a : X) (P : PRED),
 Compat P ->
 forall (Y : Typ1) (B : Rel Y) (b : Y),
 iff (ELT Y B b (opt X) (SELECT X A a P) (none X))
   (and (ELT Y B b X A a) (P Y B b)).

Proof.
intros X A a P H1 Y B b; unfold iff in |- *; apply and_intro.
intro; apply selection_elim; assumption.
intro H; apply H; intros; apply selection_intro; assumption.
Qed.