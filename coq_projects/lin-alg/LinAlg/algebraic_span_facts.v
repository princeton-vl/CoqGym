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


(** * algebraic_span_facts.v *)
Set Implicit Arguments.
Unset Strict Implicit.
Require Export spans.
From Algebra Require Export Inter.

Section MAIN.
Variable F : field.
Variable V : vectorspace F.

Lemma span_idempotent :
 forall S : part_set V, span S =' span (span S) in part_set V.
simpl in |- *.
red in |- *.
split; intro.
apply in_part_comp_r with (span_ind (span S):part_set V); auto with algebra.
change (Pred_fun (span S) x) in H.
simpl in |- *.
exists (Immediately (Build_subtype H)).
simpl in |- *.
apply Refl.
apply Trans with (span (span S):part_set V); auto with algebra.

assert (in_part x (span_ind (span S))).
apply in_part_comp_r with (span (span S):part_set V); auto with algebra.
elim H0.
intro.
generalize x.
elim x0.
simpl in |- *.
intros.
red in |- *.
exists 0.
exists (empty_seq F).
exists (empty_seq S).
simpl in |- *.
auto.

simpl in |- *.
intro.
elim c.
intros c0 cp.
elim cp.
intros x1 H1.
inversion H1.
inversion H2.
intros.
red in |- *.
exists x1.
exists x2.
exists x3.
apply Trans with c0; auto with algebra.

intros.
clear H0 H x x0.
simpl in H3.
simpl in |- *.
red in |- *.
generalize (H1 (span_ind_injection s) (Refl _)).
generalize (H2 (span_ind_injection s0) (Refl _)).
intros.
clear H1 H2.
simpl in H, H0.
red in H, H0.
inversion H.
inversion H0.
exists (x0 + x).
inversion H1.
inversion H2.
exists (x3 ++ x2).
inversion H4.
inversion H5.
exists (x5 ++ x4).
apply
 Trans
  with
    (sum (mult_by_scalars x3 (Map_embed x5)) +'
     sum (mult_by_scalars x2 (Map_embed x4))).
apply Trans with (span_ind_injection s +' span_ind_injection s0);
 auto with algebra.
apply
 Trans
  with
    (sum
       (mult_by_scalars x3 (Map_embed x5) ++
        mult_by_scalars x2 (Map_embed x4))).
apply Sym.
apply sum_concat; auto with algebra.
apply
 Trans with (sum (mult_by_scalars (x3 ++ x2) (Map_embed x5 ++ Map_embed x4))).
unfold mult_by_scalars in |- *.
apply sum_comp; auto with algebra.
unfold mult_by_scalars in |- *.
apply sum_comp.
apply toMap.
apply pointwise_comp; auto with algebra.
intros.
clear x0 H0 H x.
simpl in H2.
generalize (H1 (span_ind_injection s) (Refl _)).
simpl in |- *. 
unfold is_lin_comb in |- *.
intro.
inversion H.
inversion H0.
inversion H3.
exists x.
exists (pointwise (uncurry (RING_comp (R:=F))) (const_seq x c) x0).
exists x2.
apply Trans with (c mX span_ind_injection s); auto with algebra.
apply Trans with (c mX sum (mult_by_scalars x0 (Map_embed x2)));
 auto with algebra.
apply
 Trans
  with
    (sum
       (mult_by_scalars (const_seq x c) (mult_by_scalars x0 (Map_embed x2))));
 auto with algebra.
Qed.

Lemma span_preserves_inclusion :
 forall S S' : part_set V, included S S' -> included (span S) (span S').
intros.
red in |- *.
intros.
simpl in H0.
red in H0.
elim H0; intros.
elim H1; intros.
elim H2; intro.
simpl in |- *.
red in |- *.
exists x0.
exists x1.
exists (Map_include_map _ H x2).
apply Trans with (sum (mult_by_scalars x1 (Map_embed x2))); auto with algebra.
Qed.

Hint Resolve span_preserves_inclusion: algebra.

Lemma span_of_union :
 forall S S' : part_set V,
 span (union S S') =' span (union (span S) (span S')) in part_set V.
intros.
apply included_antisym.
apply span_smallest_subspace_containing_subset; auto with algebra.
apply included2_union; auto with algebra.
apply included_trans with (union (span S) (span S')); auto with algebra.
apply included_trans with (span S:part_set V); auto with algebra.
apply included_trans with (union (span S) (span S')); auto with algebra.
apply included_trans with (span S':part_set V); auto with algebra.
apply span_smallest_subspace_containing_subset; auto with algebra.
Qed.

Lemma inclusion_generates :
 forall S S' : part_set V,
 included S S' -> generates S (full V) -> generates S' (full V).
intros.
red in H0.
red in |- *.
apply Trans with (span S:part_set _); auto with algebra.
apply included_antisym; auto with algebra.
apply included_trans with (full V); auto with algebra.
Qed.

Lemma subspace_span_characterisation :
 forall W : part_set V, is_subspace W <-> span W =' W in part_set V.
intro.
split.

intros.
apply Trans with (span_ind W:part_set V); auto with algebra.
simpl in |- *.
red in |- *.
split.
intro.
red in H.
inversion_clear H.
inversion_clear H2.
simpl in H0.
inversion_clear H0.
generalize H2.
generalize x.
clear H2.
induction x0 as [| c| x1 IHx1 x2 IHx2| c x0 IHx0].
simpl in |- *.
intros.
apply in_part_comp_l with (zero V); auto with algebra.
simpl in |- *.
intros.
apply in_part_comp_l with (subtype_elt c); auto with algebra.
simpl in |- *.
intros.
apply in_part_comp_l with (span_ind_injection x1 +' span_ind_injection x2);
 auto with algebra.
intros.
simpl in H2.
apply in_part_comp_l with (c mX span_ind_injection x0); auto with algebra.

intro.
simpl in |- *.
red in H0.
exists (Immediately (Build_subtype H0)).
simpl in |- *.
apply Refl.

intro.
apply is_subspace_comp with (span W:part_set V); auto with algebra.
apply span_is_subspace; auto with algebra.
Qed.

Lemma subspace_contains_all_lin_combs :
 forall (W : subspace V) (x : V), is_lin_comb x W -> in_part x W.
intros.
assert (in_part x (span W)).
simpl in |- *.
auto.
apply in_part_comp_r with (span W:part_set V).
auto.
elim (subspace_span_characterisation W).
intros.
apply H1.
apply is_subspace_OK.
Qed.

Lemma span_intersect :
 forall S S' : part_set V,
 included (span (inter S S')) (inter (span S) (span S')).
intros.
red in |- *.
intros.
simpl in H.
red in H.
inversion_clear H.
inversion_clear H0.
inversion_clear H.
simpl in |- *.
split.
red in |- *.
exists x0.
exists x1.
assert (included (inter S S') S); auto with algebra.
exists (Map_include_map _ H x2).
apply Trans with (sum (mult_by_scalars x1 (Map_embed x2))); auto with algebra.
red in |- *.
exists x0.
exists x1.
assert (included (inter S S') S'); auto with algebra.
exists (Map_include_map _ H x2).
apply Trans with (sum (mult_by_scalars x1 (Map_embed x2))); auto with algebra.
Qed.

End MAIN.
