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


(*****************************************************************************)
(*          Projet Formel - Calculus of Inductive Constructions V5.10        *)
(*****************************************************************************)
(*									     *)
(*	               Free Monoid (Kleene Closure)                          *)
(*									     *)
(*****************************************************************************)
(*									     *)
(*                     A. SAIBI	  May 95                  		     *)
(*									     *)
(*****************************************************************************)

Require Export Monoid.

Set Implicit Arguments.
Unset Strict Implicit.

Section freem_def.

Variable A : Setoid.

Inductive Tlist : Type :=
  | Empty : Tlist
  | Concat1 : A -> Tlist -> Tlist.

Fixpoint Equal_Tlist (l : Tlist) : Tlist -> Prop :=
  fun m : Tlist =>
  match l, m with
  | Empty, Empty => True
  | Empty, _ => False
  | Concat1 a l1, Concat1 b m1 => a =_S b /\ Equal_Tlist l1 m1
  | _, _ => False
  end.

Lemma Equal_Tlist_equiv : Equivalence Equal_Tlist.
Proof.
apply Build_Equivalence.
unfold Reflexive in |- *; intro l; elim l; simpl in |- *.
auto.
intros; split; [ apply Refl | auto ].
apply Build_Partial_equivalence.
unfold Transitive in |- *; intros l1; elim l1.
intro l2; elim l2.
intro l3; elim l3; simpl in |- *; trivial.
intros c t H z H1; elim H1.
intros c t H y; elim y.
intros z H1 H2; elim H1.
intros c0 t0 H0 z; elim z.
intros H1 H2; elim H2.
intros c1 t1 H1 H2 H3.
elim H2; intros H4 H5.
elim H3; intros H6 H7.
simpl in |- *; split.
apply Trans with c0; trivial.
apply (H t0 t1); trivial.
unfold Symmetric in |- *; intro l1; elim l1.
intro l2; elim l2.
trivial.
intros c t H H1; elim H1.
intros c t H l2; elim l2.
simpl in |- *; trivial.
intros c0 t0 H0 H1.
elim H1; intros H2 H3.
simpl in |- *; split.
apply Sym; trivial.
apply H; trivial.
Qed.

Canonical Structure Tlist_setoid : Setoid := Equal_Tlist_equiv.

Fixpoint Concat (l : Tlist_setoid) : Tlist_setoid -> Tlist_setoid :=
  fun m : Tlist_setoid =>
  match l with
  | Empty => m
  | Concat1 a l1 => Concat1 a (Concat l1 m)
  end.

Lemma Diff_Concat1_Empty :
 forall (a : A) (l : Tlist), ~ Equal_Tlist (Concat1 a l) Empty.
Proof.
unfold not in |- *; intros a l; simpl in |- *; trivial.
Qed.

Lemma Concat_congl : Map2_congl_law Concat.
Proof.
unfold Map2_congl_law in |- *; intros l1 l2 l3.
elim l3; simpl in |- *.
trivial.
intros c t H H0; split.
apply Refl.
auto.
Qed.

Lemma Concat_congr : Map2_congr_law Concat.
Proof.
unfold Map2_congr_law in |- *; intro l1; elim l1.
intro l2; elim l2.
intros l H; apply Refl.
intros c t H l3 H1; elim H1.
intros c t H l2; elim l2.
intros l H1; absurd (Equal_Tlist (Concat1 c t) Empty).
apply Diff_Concat1_Empty.
trivial.
intros c0 t0 H0 l H1; elim H1; intros H2 H3.
simpl in |- *; split.
trivial.
apply (H t0 l); trivial.
Qed.

Definition Concat_map2 := Build_Map2 Concat_congl Concat_congr.

Lemma Mass_FreeMonoid : Monoid_ass Concat_map2.
Proof.
unfold Monoid_ass in |- *; intros l m n; elim l.
apply Refl.
intros; split.
apply Refl.
trivial.
Qed.

Lemma Midl_FreeMonoid : Monoid_idl Concat_map2 Empty.
Proof.
unfold Monoid_idl in |- *; intro l; elim l.
apply Refl.
intros; split.
apply Refl.
trivial.
Qed.

Lemma Midr_FreeMonoid : Monoid_idr Concat_map2 Empty.
Proof.
unfold Monoid_idr in |- *; intro l; elim l; simpl in |- *.
trivial.
intros; split.
apply Refl.
trivial.
Qed.

Canonical Structure FreeMonoid :=
  Build_Monoid Mass_FreeMonoid Midl_FreeMonoid Midr_FreeMonoid.

End freem_def.

Coercion FreeMonoid : Setoid >-> Monoid.