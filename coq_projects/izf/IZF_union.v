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

Definition UNION (X : Typ1) (A : Rel X) (a : X) (z' z : opt X) :=
  forall E : Prop,
  (forall x x' : X,
   eq (opt X) z' (some X x') -> eq (opt X) z (some X x) -> A x' x -> E) ->
  (forall x x' : X,
   eq (opt X) z' (some X x') -> eq (opt X) z (none X) -> A x' x -> A x a -> E) ->
  E.

Lemma UNION_in :
 forall (X : Typ1) (A : Rel X) (a x x' : X),
 A x' x -> UNION X A a (some X x') (some X x).

Proof
  fun X A a x x' H E e _ =>
  e x x' (eq_refl (opt X) (some X x')) (eq_refl (opt X) (some X x)) H.

Lemma UNION_rt :
 forall (X : Typ1) (A : Rel X) (a x x' : X),
 A x' x -> A x a -> UNION X A a (some X x') (none X).

Proof
  fun X A a x x' H1 H2 E _ e =>
  e x x' (eq_refl (opt X) (some X x')) (eq_refl (opt X) (none X)) H1 H2.

Lemma UNION_deloc :
 forall (X : Typ1) (A : Rel X) (a : X),
 deloc X A (opt X) (UNION X A a) (some X).

Proof.
intros X A a; unfold deloc in |- *; apply and_intro.
(* Deloc 1 *)
exact (UNION_in X A a).
(* Deloc 2 *)
intros x y' H; apply H; clear H. (* Case distinction *)
(* Deloc 2, case 1 *)
intros x0 x' H1 H2 H3; apply ex2_intro with x'.
apply (eq_sym _ _ _ (eq_some_some _ _ _ H2)); assumption.
assumption.
(* Deloc 2, case 2 (absurd) *)
intros x0 x' H1 H2 H3 H4; apply (eq_some_none _ _ H2).
Qed.

Lemma UNION_eqv :
 forall (X : Typ1) (A : Rel X) (a x : X),
 EQV X A x (opt X) (UNION X A a) (some X x).

Proof.
intros X A a x; apply EQV_deloc; apply UNION_deloc.
Qed.

Lemma union_intro :
 forall (X : Typ1) (A : Rel X) (a : X) (Y : Typ1) (B : Rel Y) 
   (b : Y) (Z : Typ1) (C : Rel Z) (c : Z),
 ELT Y B b Z C c ->
 ELT Z C c X A a -> ELT Y B b (opt X) (UNION X A a) (none X).

Proof.
intros X A a Y B b Z C c H H'.
apply H'; clear H'; intros x H1 H2.
apply (ELT_compat_r _ _ _ _ _ _ _ _ _ H H2); clear H; intros x' H3 H4.
apply ELT_intro with (some X x').  apply UNION_rt with x; assumption.
apply EQV_trans with X A x'; [ assumption | apply UNION_eqv ].
Qed.

Lemma union_elim :
 forall (X : Typ1) (A : Rel X) (a : X) (Y : Typ1) (B : Rel Y) (b : Y),
 ELT Y B b (opt X) (UNION X A a) (none X) ->
 exG (fun Z C c => and (ELT Y B b Z C c) (ELT Z C c X A a)).

Proof.
intros X A a Y B b H; apply H; clear H; intros z H H1.
apply H; clear H.  (* Case distinction *)
(* Case 1 (absurd) *)
intros x x' H2 H3 H4; apply (eq_none_some _ _ H3).
(* Case 2 *)
intros x x' H2 H3 H4 H5.
apply exG_intro with (opt X) (UNION X A a) (some X x).
apply and_intro. apply ELT_intro with (some X x').
apply UNION_in; assumption. apply H2; assumption.
apply ELT_compat_l with X A x. apply EQV_sym; apply UNION_eqv.
apply ELT_direct; assumption.
Qed.

Lemma union :
 forall (X : Typ1) (A : Rel X) (a : X) (Y : Typ1) (B : Rel Y) (b : Y),
 iff (ELT Y B b (opt X) (UNION X A a) (none X))
   (exG (fun Z C c => and (ELT Y B b Z C c) (ELT Z C c X A a))).

Proof.
intros X A a Y B b; unfold iff in |- *; apply and_intro.
(* Direct implication *)
intro; apply union_elim; assumption.
(* Converse implication *)
intro H; apply H; clear H; intros Z C c H.
apply H; clear H; intros H1 H2.
apply union_intro with Z C c; assumption.
Qed.