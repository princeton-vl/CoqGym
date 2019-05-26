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

(** Let (X, A, a) and (Y, B, b) be two pointed graphs (with X,Y : Typ1).
    The unordered pair formed by the sets represented by these pointed
    graphs is itself represented by the pointed graph

      ((sum X Y), (PAIR X A a Y B b), (out X Y))

    whose edge relation (PAIR X A a Y B b) : (Rel (sum X Y)) is
    defined by the following four clauses :

    1. Delocate A in the new graph via (inl X Y):

         if (A x' x), then (PAIR X A a Y B b (inl X Y x') (inl X Y x))

    2. Delocate B in the new graph via (inr X Y):

         if (B y' y), then (PAIR X A a Y B b (inr X Y y') (inr X Y y))

    3. Connect the (image of the) root a to the new root (out X Y):

         (PAIR X A a Y B b (inl X Y a) (out X Y))

    4. Connect the (image of the) root b to the new root (out X Y):

         (PAIR X A a Y B b (inr X Y b) (out X Y))

   As usual, we define this relation by a direct impredicative encoding: *)

Definition PAIR (X : Typ1) (A : Rel X) (a : X) (Y : Typ1) 
  (B : Rel Y) (b : Y) (z' z : sum X Y) :=
  forall E : Prop,
  (forall x x' : X,
   eq (sum X Y) z (inl X Y x) -> eq (sum X Y) z' (inl X Y x') -> A x' x -> E) ->
  (forall y y' : Y,
   eq (sum X Y) z (inr X Y y) -> eq (sum X Y) z' (inr X Y y') -> B y' y -> E) ->
  (eq (sum X Y) z' (inl X Y a) -> eq (sum X Y) z (out X Y) -> E) ->
  (eq (sum X Y) z' (inr X Y b) -> eq (sum X Y) z (out X Y) -> E) -> E.

(** The introduction rules corresponding to the 4 clauses of the
    definition of (PAIR X A a Y B b) are the following: *)

Lemma PAIR_in1 :
 forall (X : Typ1) (A : Rel X) (a : X) (Y : Typ1) (B : Rel Y) 
   (b : Y) (x x' : X), A x' x -> PAIR X A a Y B b (inl X Y x') (inl X Y x).

Proof
  fun X A a Y B b x x' H E H1 H2 H3 H4 =>
  H1 x x' (eq_refl (sum X Y) (inl X Y x)) (eq_refl (sum X Y) (inl X Y x')) H.
Lemma PAIR_in2 :
 forall (X : Typ1) (A : Rel X) (a : X) (Y : Typ1) (B : Rel Y) (b y y' : Y),
 B y' y -> PAIR X A a Y B b (inr X Y y') (inr X Y y).

Proof
  fun X A a Y B b y y' H E H1 H2 H3 H4 =>
  H2 y y' (eq_refl (sum X Y) (inr X Y y)) (eq_refl (sum X Y) (inr X Y y')) H.

Lemma PAIR_rt1 :
 forall (X : Typ1) (A : Rel X) (a : X) (Y : Typ1) (B : Rel Y) (b : Y),
 PAIR X A a Y B b (inl X Y a) (out X Y).

Proof
  fun X A a Y B b E H1 H2 H3 H4 =>
  H3 (eq_refl (sum X Y) (inl X Y a)) (eq_refl (sum X Y) (out X Y)).

Lemma PAIR_rt2 :
 forall (X : Typ1) (A : Rel X) (a : X) (Y : Typ1) (B : Rel Y) (b : Y),
 PAIR X A a Y B b (inr X Y b) (out X Y).

Proof
  fun X A a Y B b E H1 H2 H3 H4 =>
  H4 (eq_refl (sum X Y) (inr X Y b)) (eq_refl (sum X Y) (out X Y)).

(** We first check that the left injection (inl X Y) : X -> (sum X Y)
    is a delocation, and deduce that the pointed graphs (X, A, a) and
    ((sum X Y), (PAIR X A a Y B b), (inl X Y a)) are bisimilar. *)

Lemma PAIR_deloc1 :
 forall (X : Typ1) (A : Rel X) (a : X) (Y : Typ1) (B : Rel Y) (b : Y),
 deloc X A (sum X Y) (PAIR X A a Y B b) (inl X Y).

Proof.
intros X A a Y B b; unfold deloc in |- *; apply and_intro.
(* Deloc 1 *)
exact (PAIR_in1 X A a Y B b).
(* Deloc 2 (case distinction) *)
intros x z' H; apply H; clear H.
(* Deloc 2, case 1 *)
intros x0 x' H1 H2 H3; apply ex2_intro with x'.
apply (eq_sym _ _ _ (eq_inl_inl X Y x x0 H1)); assumption.
assumption.
(* Deloc 2, case 2 (absurd) *)
intros y y' H1 H2 H3.
apply (eq_inl_inr X Y x y H1).
(* Deloc 2, case 3 (absurd) *)
intros H1 H2; apply (eq_inl_out X Y x H2).
(* Deloc 2, case 4 (absurd) *)
intros H1 H2; apply (eq_inl_out X Y x H2).
Qed.

Lemma PAIR_eqv1 :
 forall (X : Typ1) (A : Rel X) (a : X) (Y : Typ1) (B : Rel Y) (b : Y),
 EQV X A a (sum X Y) (PAIR X A a Y B b) (inl X Y a).

Proof.
intros; apply EQV_deloc; apply PAIR_deloc1.
Qed.

(** The same for the right injection (inr X Y) : Y -> (sum X Y). *)

Lemma PAIR_deloc2 :
 forall (X : Typ1) (A : Rel X) (a : X) (Y : Typ1) (B : Rel Y) (b : Y),
 deloc Y B (sum X Y) (PAIR X A a Y B b) (inr X Y).

Proof.
intros X A a Y B b; unfold deloc in |- *; apply and_intro.
(* Deloc 1 *)
exact (PAIR_in2 X A a Y B b).
(* Deloc 2 (case distinction) *)
intros y z' H; apply H; clear H.
(* Deloc 2, case 1 (absurd) *)
intros x x' H1 H2 H3; apply (eq_inr_inl X Y x y H1).
(* Deloc 2, case 2 *)
intros y0 y' H1 H2 H3; apply ex2_intro with y'.
apply (eq_sym _ _ _ (eq_inr_inr X Y y y0 H1)); assumption.
assumption.
(* Deloc 2, case 3 (absurd) *)
intros H1 H2; apply (eq_inr_out X Y y H2).
(* Deloc 2, case 4 (absurd) *)
intros H1 H2; apply (eq_inr_out X Y y H2).
Qed.

Lemma PAIR_eqv2 :
 forall (X : Typ1) (A : Rel X) (a : X) (Y : Typ1) (B : Rel Y) (b : Y),
 EQV Y B b (sum X Y) (PAIR X A a Y B b) (inr X Y b).

Proof.
intros; apply EQV_deloc; apply PAIR_deloc2.
Qed.

(** From PAIR_eqv1 and PAIR_eqv2, we easily get that the pointed graphs
    (X, A, a) and (Y, B, b) are elements of the unordered pair. *)

Lemma pairing_intro1 :
 forall (X : Typ1) (A : Rel X) (a : X) (Y : Typ1) (B : Rel Y) (b : Y),
 ELT X A a (sum X Y) (PAIR X A a Y B b) (out X Y).

Proof.
intros X A a Y B b; apply ELT_intro with (inl X Y a).
apply PAIR_rt1.  apply PAIR_eqv1.
Qed.


Lemma pairing_intro2 :
 forall (X : Typ1) (A : Rel X) (a : X) (Y : Typ1) (B : Rel Y) (b : Y),
 ELT Y B b (sum X Y) (PAIR X A a Y B b) (out X Y).

Proof.
intros X A a Y B b; apply ELT_intro with (inr X Y b).
apply PAIR_rt2.  apply PAIR_eqv2.
Qed.

(** And conversely, (X, A, a) and (Y, B, b) are the only elements of
    the pair, up to bisimulation. *)

Lemma pairing_elim :
 forall (X : Typ1) (A : Rel X) (a : X) (Y : Typ1) (B : Rel Y) 
   (b : Y) (Z : Typ1) (C : Rel Z) (c : Z),
 ELT Z C c (sum X Y) (PAIR X A a Y B b) (out X Y) ->
 or (EQV Z C c X A a) (EQV Z C c Y B b).

Proof.
intros X A a Y B b Z C c H.
apply H; clear H; intros c' H H1.
apply H; clear H.
(* Case 1 (absurd) *)
intros x x' H2 H3 H4; apply (eq_out_inl X Y x H2).
(* Case 2 (absurd) *)
intros y y' H2 H3 H4; apply (eq_out_inr X Y y H2).
(* Case 3 *)
intros H2 H3; apply or_inl.
apply EQV_trans with (sum X Y) (PAIR X A a Y B b) (inl X Y a).
apply H2; assumption. apply EQV_sym; apply PAIR_eqv1.
(* Case 4 *)
intros H2 H3; apply or_inr.
apply EQV_trans with (sum X Y) (PAIR X A a Y B b) (inr X Y b).
apply H2; assumption. apply EQV_sym; apply PAIR_eqv2.
Qed.

(** By collecting the last three lemmas, we obtain the desired result: *)

Theorem pairing :
 forall (X : Typ1) (A : Rel X) (a : X) (Y : Typ1) (B : Rel Y) 
   (b : Y) (Z : Typ1) (C : Rel Z) (c : Z),
 iff (ELT Z C c (sum X Y) (PAIR X A a Y B b) (out X Y))
   (or (EQV Z C c X A a) (EQV Z C c Y B b)).

Proof.
intros; unfold iff in |- *; apply and_intro.
(* Forward implication *)
intro; apply pairing_elim; assumption.
(* Backward implication: case distinction *)
intro H; apply H; clear H; intro H.
(* First case *)
apply ELT_compat_l with X A a.
assumption. apply pairing_intro1.
(* Second case *)
apply ELT_compat_l with Y B b.
assumption. apply pairing_intro2.
Qed.
