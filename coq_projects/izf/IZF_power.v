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

(** Let (X, A, a) be a pointed graph.  The powerset of the set represented
    by this pointed graph is itself represented by the pointed graph

      ((sum X X->Prop), (POWER X A a), (out X X->Prop))

    whose edge relation (POWER X A a) : (Rel (sum X X->Prop)) is defined
    by the following 3 clauses:

    1. Delocating A into the powerset:

         if (A x' x),
         then (POWER X A a (inl X X->Prop x') (inl X X->Prop x))

    2. Connecting each vertex x':X such that (A x' a) to all the
       predicates p : X->Prop such that (p x'):

         if (A x' a) and (p x'),
         then (POWER X A a (inl X X->Prop x') (inr X X->Prop p))

    3. Connecting all the predicates p : X->Prop to the new root:

         (POWER X A a (inr X X->Prop p) (out X X->Prop)).

    This relation is impredicatively encoded as follows: *)

Definition POWER (X : Typ1) (A : Rel X) (a : X) (z' z : sum X (X -> Prop)) :=
  forall E : Prop,
  (forall x x' : X,
   eq (sum X (X -> Prop)) z' (inl X (X -> Prop) x') ->
   eq (sum X (X -> Prop)) z (inl X (X -> Prop) x) -> A x' x -> E) ->
  (forall (x' : X) (p : X -> Prop),
   eq (sum X (X -> Prop)) z' (inl X (X -> Prop) x') ->
   eq (sum X (X -> Prop)) z (inr X (X -> Prop) p) -> A x' a -> p x' -> E) ->
  (forall p : X -> Prop,
   eq (sum X (X -> Prop)) z' (inr X (X -> Prop) p) ->
   eq (sum X (X -> Prop)) z (out X (X -> Prop)) -> E) -> E.

(** Introduction rules corresponding to the clauses: *)

Lemma POWER_in1 :
 forall (X : Typ1) (A : Rel X) (a x x' : X),
 A x' x -> POWER X A a (inl X (X -> Prop) x') (inl X (X -> Prop) x).

Proof
  fun X A a x x' H E e _ _ =>
  e x x' (eq_refl (sum X (X -> Prop)) (inl X (X -> Prop) x'))
    (eq_refl (sum X (X -> Prop)) (inl X (X -> Prop) x)) H.

Lemma POWER_in2 :
 forall (X : Typ1) (A : Rel X) (a x' : X) (p : X -> Prop),
 A x' a -> p x' -> POWER X A a (inl X (X -> Prop) x') (inr X (X -> Prop) p).

Proof
  fun X A a x' p H1 H2 E _ e _ =>
  e x' p (eq_refl (sum X (X -> Prop)) (inl X (X -> Prop) x'))
    (eq_refl (sum X (X -> Prop)) (inr X (X -> Prop) p)) H1 H2.

Lemma POWER_rt :
 forall (X : Typ1) (A : Rel X) (a : X) (p : X -> Prop),
 POWER X A a (inr X (X -> Prop) p) (out X (X -> Prop)).

Proof
  fun X A a p E _ _ e =>
  e p (eq_refl (sum X (X -> Prop)) (inr X (X -> Prop) p))
    (eq_refl (sum X (X -> Prop)) (out X (X -> Prop))).

(** We now prove that the left injection (inl X X->Prop) is a delocation
    from (X, A) to ((sum X X->Prop), (POWER X A a)), and deduce the
    expected property of bisimilarity. *)

Lemma POWER_deloc :
 forall (X : Typ1) (A : Rel X) (a : X),
 deloc X A (sum X (X -> Prop)) (POWER X A a) (inl X (X -> Prop)).

Proof.
intros X A a; unfold deloc in |- *; apply and_intro.
(* Deloc 1 *)
exact (POWER_in1 X A a).
(* Deloc 2 (case distinction) *)
intros x y' H; apply H; clear H.
(* Deloc 2, case 1 *)
intros x0 x' H1 H2 H3; apply ex2_intro with x'.
apply (eq_sym _ _ _ (eq_inl_inl X (X -> Prop) x x0 H2)); assumption.
assumption.
(* Deloc 2, case 2 (absurd) *)
intros x' p H1 H2 H3 H4; apply (eq_inl_inr X (X -> Prop) x p H2).
(* Deloc 2, case 3 (absurd) *)
intros p H1 H2; apply (eq_inl_out X (X -> Prop) x H2).
Qed.

Lemma POWER_eqv :
 forall (X : Typ1) (A : Rel X) (a x : X),
 EQV X A x (sum X (X -> Prop)) (POWER X A a) (inl X (X -> Prop) x).

Proof.
intros X A a x; apply EQV_deloc; apply POWER_deloc.
Qed.

(** Moreover, any subset of (X, A, a) is bisimilar to a pointed graph
    of the form ((sum X X->Prop), (POWER X A a), (inr X X->Prop) p)
    for a suitable predicate p : X->Prop. *)

Lemma POWER_subset_eqv :
 forall (X : Typ1) (A : Rel X) (a : X) (Y : Typ1) (B : Rel Y) (b : Y),
 SUB Y B b X A a ->
 EQV Y B b (sum X (X -> Prop)) (POWER X A a)
   (inr X (X -> Prop) (fun x' => and (A x' a) (ELT X A x' Y B b))).

Proof.
(* We reason by extensionality: *)
intros X A a Y B b H1; apply extensionality.
(* Inclusion (SUB Y B b (sum ...) (POWER ...) (inr ... p)) *)
unfold SUB in |- *; intros Z C c H2.
apply (H1 Z C c H2); intros x' H3 H4.
apply ELT_intro with (inl X (X -> Prop) x').
apply POWER_in2.  assumption.
apply and_intro. assumption.
apply ELT_compat_l with Z C c.
apply EQV_sym; assumption. assumption.
apply EQV_trans with X A x'.
assumption. apply POWER_eqv; assumption.
(* Inclusion (SUB (sum ...) (POWER ...) (inr ... p) Y B b) *)
unfold SUB in |- *; intros Z C c H2; apply H2; clear H2.
intros z H2 H3; apply H2; clear H2. (* Case distinction *)
(* Case 1 (absurd) *)
intros x x' H4 H5 H6; apply (eq_inr_inl _ _ _ _ H5).
(* Case 2 *)
intros x' p H4 H5 H6 H7; generalize (eq_inr_inr _ _ _ _ H5); intro H8.
generalize (eq_sym _ _ _ H8 (fun q => q x') H7); clear H8; intro H8.
apply H8; clear H8; intros H8 H9; apply ELT_compat_l with X A x'.
apply EQV_trans with (sum X (X -> Prop)) (POWER X A a) (inl X (X -> Prop) x').
apply H4; assumption. apply EQV_sym; apply POWER_eqv. assumption.
(* Case 3 (absurd) *)
intros p H4 H5; apply (eq_inr_out _ _ _ H5).
Qed.

(** From this, we deduce the introduction rule of the powerset: *)

Lemma powerset_intro :
 forall (X : Typ1) (A : Rel X) (a : X) (Y : Typ1) (B : Rel Y) (b : Y),
 SUB Y B b X A a ->
 ELT Y B b (sum X (X -> Prop)) (POWER X A a) (out X (X -> Prop)).

Proof.
intros X A a Y B b H;
 apply
  ELT_intro
   with (inr X (X -> Prop) (fun x' => and (A x' a) (ELT X A x' Y B b))).
apply POWER_rt.  apply POWER_subset_eqv; assumption.
Qed.

(** And the elimination rule comes easily: *)

Lemma powerset_elim :
 forall (X : Typ1) (A : Rel X) (a : X) (Y : Typ1) (B : Rel Y) (b : Y),
 ELT Y B b (sum X (X -> Prop)) (POWER X A a) (out X (X -> Prop)) ->
 SUB Y B b X A a.

Proof.
intros X A a Y B b H; apply H; clear H.
intros z H1 H2; apply H1; clear H1. (* Case distinction *)
(* Case 1 (absurd) *)
intros x x' H3 H4 H5; apply (eq_out_inl _ _ _ H4).
(* Case 2 (absurd) *)
intros x' p H3 H4 H5 H6; apply (eq_out_inr _ _ _ H4).
(* Case 3 *)
unfold SUB in |- *; intros p H3 H4 Z C c H5.
apply (ELT_compat_r _ _ _ _ _ _ _ _ _ H5 H2).
intros z' H6 H7; apply H6; clear H6.
(* Case 3-1 (absurd) *)
intros x x' H8 H9 H10.
apply (eq_inl_inr _ _ _ _ (eq_trans _ _ _ _ (eq_sym _ _ _ H9) H3)).
(* Case 3-2 *)
intros x' p0 H8 H9 H10 H11; apply ELT_intro with x'.  assumption.
apply EQV_trans with (sum X (X -> Prop)) (POWER X A a) (inl X (X -> Prop) x').
apply H8; assumption.  apply EQV_sym; apply POWER_eqv.
(* Case 3-3 (absurd) *)
intros p0 H8 H9.
apply (eq_inr_out _ _ _ (eq_trans _ _ _ _ (eq_sym _ _ _ H3) H9)).
Qed.

(** From this, we can conclude: *)

Theorem powerset :
 forall (X : Typ1) (A : Rel X) (a : X) (Y : Typ1) (B : Rel Y) (b : Y),
 iff (ELT Y B b (sum X (X -> Prop)) (POWER X A a) (out X (X -> Prop)))
   (SUB Y B b X A a).

Proof.
intros X A a Y B b; unfold iff in |- *; apply and_intro.
intro; apply powerset_elim; assumption.
intro; apply powerset_intro; assumption.
Qed.
