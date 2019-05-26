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


(** * lin_dependence.v *)
Set Implicit Arguments.
Unset Strict Implicit.
Section MAIN.
From Algebra Require Export Union.
Require Export subspaces.
Require Export cast_between_subsets.
Require Export mult_by_scalars.
Require Export sums.
Require Export seq_set_seq.
Require Export distinct.
Require Export const.

Section defs.
Variable F : field.
Variable V : vectorspace F.

(** %\tocdef{lin\_{\em[in]}dep}% *)
Definition lin_dep (X : part_set V) :=
  exists n : Nat,
    (exists a : seq (S n) F,
       (exists v : seq (S n) X,
          distinct v /\
          ~ a =' const_seq (S n) (zero F) in _ /\
          sum (mult_by_scalars a (Map_embed v)) =' (zero V) in _)).

Definition lin_indep (X : part_set V) := ~ lin_dep X.

Definition lin_indep' (X : part_set V) :=
  forall (n : Nat) (a : seq (S n) F) (v : seq (S n) X),
  distinct v ->
  ~ a =' const_seq (S n) (zero F) in _ ->
  ~ sum (mult_by_scalars a (Map_embed v)) =' (zero V) in _.

Lemma lin_dep_comp :
 forall X Y : part_set V, X =' Y in _ -> lin_dep X -> lin_dep Y.
intros.
red in |- *.
red in H0.
inversion_clear H0.
exists x.
inversion_clear H1.
exists x0.
inversion_clear H0.
exists (Map_to_equal_subsets H x1).
split.
inversion_clear H1.
repeat red in H0.
repeat red in |- *.
intros.
apply (H0 i j); auto with algebra.
simpl in |- *.
red in |- *.
simpl in H3.
red in H3.
apply Trans with (subtype_elt (x1 i)); auto with algebra.
apply Trans with (subtype_elt (Map_to_equal_subsets H x1 i));
 auto with algebra. 
apply Trans with (subtype_elt (x1 j)); auto with algebra.
apply Trans with (subtype_elt (Map_to_equal_subsets H x1 j));
 auto with algebra. 
split.
inversion_clear H1.
inversion_clear H2.
auto.
inversion_clear H1.
inversion_clear H2.
apply Trans with (sum (mult_by_scalars x0 (Map_embed x1))); auto with algebra. 
Qed.

Lemma lin_indep_comp :
 forall X Y : part_set V, X =' Y in _ -> lin_indep X -> lin_indep Y.
intros.
red in |- *.
red in |- *.
red in H0.
red in H0.
intro.
apply H0.
apply lin_dep_comp with Y; auto with algebra.
Qed.

Lemma lin_dep_defs_eqv : forall X : part_set V, lin_indep X <-> lin_indep' X.
unfold lin_indep in |- *.
unfold lin_indep' in |- *.
unfold lin_dep in |- *.
split.
unfold not in |- *.
intros.
apply H.
exists n.
exists a.
exists v.
split.
assumption.
split.
assumption.
assumption.
unfold not in |- *.
intros.
inversion_clear H0.
inversion_clear H1.
inversion_clear H0.
apply (H x x0 x1).
inversion_clear H1.
assumption.
inversion_clear H1.
inversion_clear H2.
assumption.
inversion_clear H1.
inversion_clear H2.
assumption.
Qed.
End defs.

Section unexpected_true_results.

Lemma zero_imp_lin_dep :
 forall (F : field) (V : vectorspace F) (X : part_set V),
 in_part (zero V) X -> lin_dep X.
intros.
unfold lin_dep in |- *.
exists 0.
exists (const_seq 1 (ring_unit F)).
red in H.
exists (const_seq 1 (Build_subtype H:X)).
split.
red in |- *.
intros i j.
generalize fin_S_O_unique.
intros.
absurd (i =' j in _); auto.
split.
cut (~ one =' (zero F) in _).
unfold not in |- *.
intros.
apply H0.
simpl in H1.
red in H1.
simpl in H1.
apply H1.
exact (Build_finiteT (lt_O_Sn 0)).
exact (field_unit_non_zero F).
simpl in |- *.
apply Trans with ((zero V) +' (zero V)); auto with algebra.
Qed.

Lemma empty_lin_indep :
 forall (F : field) (V : vectorspace F), lin_indep (empty V).
intros.
unfold empty in |- *.
red in |- *.
red in |- *.
unfold lin_dep in |- *.
intro.
inversion_clear H.
inversion_clear H0.
inversion_clear H.
set (h := head x1) in *.
case h.
simpl in |- *.
auto.
Qed.
End unexpected_true_results.

Section more.
Variable F : field.
Variable V : vectorspace F.

(** - %\intoc{\bf Theorem 1.6}% *)
Lemma lin_dep_include :
 forall S1 S2 : part_set V, included S1 S2 -> lin_dep S1 -> lin_dep S2.
unfold lin_dep in |- *.
intros.
inversion_clear H0.
exists x.
inversion_clear H1.
exists x0.
inversion_clear H0.
exists (Map_include_map _ H x1).
split.
red in |- *.
inversion_clear H1.
inversion_clear H2.
red in H0.
unfold not in |- *.
intros.
unfold not in H0.
apply (H0 i j); auto with algebra.
split.
inversion_clear H1.
inversion_clear H2.
assumption.
inversion_clear H1.
inversion_clear H2.
apply Trans with (sum (mult_by_scalars x0 (Map_embed x1))); auto with algebra.
Qed.

(** - %\intoc{Corollary to theorem 1.6}% *)
Lemma lin_indep_include :
 forall S1 S2 : part_set V, included S1 S2 -> lin_indep S2 -> lin_indep S1.
intros S1 S2 H.
unfold lin_indep in |- *.
unfold not in |- *.
intros.
apply H0.
apply (lin_dep_include H).
assumption.
Qed.

(** For this we need $\neg\neg P\to P$: *)
Lemma lin_indep_prop :
 forall (n : Nat) (a : seq n F) (v : seq n V),
 distinct v ->
 lin_indep (seq_set v) ->
 sum (mult_by_scalars a v) =' (zero V) in _ -> a =' const_seq n (zero F) in _.
intro n; case n.
intros.
simpl in |- *.
red in |- *.
intro.
inversion x.
inversion in_range_prf.
intros.
elim (lin_dep_defs_eqv (seq_set v)).
intros.
generalize (H2 H0); clear H3 H2 H0.
intro.
unfold lin_indep' in H0.
generalize (H0 _ a (seq_set_seq v)).
intro; clear H0.
cut (distinct (seq_set_seq v)); auto.
intro.
generalize (H2 H0).
clear H2 H0.
intro.
apply NNPP.
unfold not in |- *; intros.
unfold not in H0.
apply H0.
auto.
apply Trans with (sum (mult_by_scalars a v)); auto with algebra.
Qed.

Lemma lin_indep_doesn't_contain_zero :
 forall X : part_set V, lin_indep X -> ~ in_part (zero V) X.
intros; red in |- *; red in H; intro.
red in H; (apply H; auto with algebra).
apply zero_imp_lin_dep; auto with algebra.
Qed.

Lemma inject_subsets_lin_dep :
 forall (W : subspace V) (X : part_set W),
 lin_dep X <-> lin_dep (inject_subsets X).
split; intros.
red in |- *; red in H.
inversion_clear H; inversion_clear H0; inversion_clear H; inversion_clear H0;
 inversion_clear H1.
exists x; exists x0.
exists (comp_map_map (Build_Map (inject_subsetsify_comp (C:=X)):MAP _ _) x1).
split; try split.
2: auto.
red in |- *; red in H.
intros.
simpl in |- *.
intro; red in H3.
red in H; (apply (H _ _ H1); auto with algebra).
clear H0 H.
apply Trans with (subtype_elt (zero W)); auto with algebra.
apply Trans with (subtype_elt (sum (mult_by_scalars x0 (Map_embed x1))));
 auto with algebra.
apply Trans with (sum (Map_embed (mult_by_scalars x0 (Map_embed x1))));
 auto with algebra.
generalize (mult_by_scalars x0 (Map_embed x1)).
generalize (S x).
intros.
induction n.
simpl in |- *.
auto with algebra.
apply Trans with (head (Map_embed c) +' sum (Seqtl (Map_embed c)));
 auto with algebra.
apply Trans with (subtype_elt (head c +' sum (Seqtl c))).
apply Trans with (subtype_elt (head c) +' subtype_elt (sum (Seqtl c)));
 auto with algebra.
apply Trans with (head (Map_embed c) +' sum (Map_embed (Seqtl c)));
 auto with algebra.
apply SGROUP_comp; auto with algebra.
apply sum_comp; auto with algebra.
apply Sym; auto with algebra.
generalize Map_embed_Seqtl.
intro p.
apply (p _ _ _ (c:seq _ _)).
apply subtype_elt_comp.
apply Sym; auto with algebra.

red in |- *; red in H.
inversion_clear H; inversion_clear H0; inversion_clear H; inversion_clear H0;
 inversion_clear H1.
exists x; exists x0.
exists
 (comp_map_map (Build_Map (uninject_subsetsify_comp (C:=X)):MAP _ _) x1).
split; try split.
2: auto.
red in |- *; red in H.
intros.
simpl in |- *.
generalize (H _ _ H1).
case (x1 i); case (x1 j).
simpl in |- *.
unfold subtype_image_equal in |- *.
simpl in |- *.
auto with algebra.
clear H0 H.
simpl in |- *.
red in |- *.
apply Trans with (zero V); auto with algebra.
apply
 Trans
  with
    (subtype_elt
       (sum
          (mult_by_scalars x0
             (Map_embed
                (comp_map_map
                   (Build_Map (uninject_subsetsify_comp (A:=V) (B:=W) (C:=X))
                    :Map _ _) x1)
              :Map _ W)))).

simpl in |- *.
apply SGROUP_comp; auto with algebra.
apply Trans with (sum (mult_by_scalars x0 (Map_embed x1))); auto with algebra. 
apply
 Trans
  with
    (sum
       (Map_embed
          (mult_by_scalars x0
             (Map_embed
                (comp_map_map
                   (Build_Map (uninject_subsetsify_comp (A:=V) (B:=W) (C:=X))
                    :Map _ _) x1)
              :Map _ W)))).
generalize
 (mult_by_scalars x0
    (Map_embed
       (comp_map_map
          (Build_Map (uninject_subsetsify_comp (A:=V) (B:=W) (C:=X))) x1)
     :Map _ W)).
generalize (S x).
intros.
apply Sym; auto with algebra.
induction n.
simpl in |- *.
auto with algebra.
apply Trans with (head (Map_embed c) +' sum (Seqtl (Map_embed c)));
 auto with algebra.
apply Trans with (subtype_elt (head c +' sum (Seqtl c))).
apply Trans with (subtype_elt (head c) +' subtype_elt (sum (Seqtl c)));
 auto with algebra.
apply Trans with (head (Map_embed c) +' sum (Map_embed (Seqtl c)));
 auto with algebra.
apply SGROUP_comp; auto with algebra.
apply sum_comp; auto with algebra.
apply Sym; auto with algebra.
generalize Map_embed_Seqtl.
intro p.
apply (p _ _ _ (c:seq _ _)).
apply subtype_elt_comp.
apply Sym; auto with algebra.
apply sum_comp.
simpl in |- *; red in |- *; simpl in |- *.
intro.
apply MODULE_comp; auto with algebra.
unfold uninject_subsetsify in |- *.
case (x1 x2).
simpl in |- *.
auto with algebra.
Qed.
End more.

(** - The following definition is a reformulation of the book's definition on page 50 *)
(** %\tocdef{max\_lin\_indep}% *)
Definition max_lin_indep (F : field) (V : vectorspace F)
  (X Y : part_set V) :=
  included X Y /\
  lin_indep X /\
  (forall y : V, in_part y Y -> ~ in_part y X -> lin_dep (union X (single y))).

End MAIN.
