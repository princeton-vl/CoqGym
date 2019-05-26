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


(** %\subsection*{ support :  finite\_subsets.v }%*)
Set Implicit Arguments.
Unset Strict Implicit.
From Algebra Require Export Diff.
From Algebra Require Export Singleton.
Require Export cast_between_subsets.
Require Export empty.
Require Export Classical_Prop.

(** - A set is finite if we can list its elements (possibly with duplicates in the list)

 %\label{isfiniteset}% *)

Definition is_finite_set (A : Setoid) :=
  exists n : Nat, (exists v : seq n A, full A =' seq_set v in _).

(** - For subsets, the following notion is more useful as it removes one
   one layer of taking subsets: *)
Definition is_finite_subset (A : Setoid) (B : part_set A) :=
  exists n : Nat, (exists v : seq n A, B =' seq_set v in _).


Lemma is_finite_subset_comp :
 forall (A : Setoid) (B C : part_set A),
 B =' C in _ -> is_finite_subset B -> is_finite_subset C.
red in |- *.
intros.
red in H0.
inversion H0.
inversion H1.
exists x.
exists x0.
apply Trans with B; auto with algebra.
Qed.

(** - There is no corresponding is_finite_set_comp, for there is no 'master' setoid 
 wherein two Setoids can be compared. *)

Hint Resolve is_finite_subset_comp: algebra.


Lemma is_finite_subset_then_is_finite :
 forall (A : Setoid) (B : part_set A), is_finite_subset B -> is_finite_set B.
intros.
red in |- *; red in H.
inversion_clear H; inversion_clear H0.
exists x.
assert (forall i : fin x, in_part (x0 i) B).
simpl in H; red in H; simpl in H.
intros.
elim (H (x0 i)).
intros p q; (apply q; auto with algebra).
exists i; auto with algebra.
exists (cast_map_to_subset H0).
simpl in |- *; red in |- *; simpl in |- *; split; intro; auto.
unfold subtype_image_equal in |- *.
simpl in H; red in H; simpl in H.
elim (H (subtype_elt x1)).
intros.
assert (in_part (subtype_elt x1) B).
auto with algebra.
elim (H2 H4).
intros.
exists x2.
apply Trans with (x0 x2); auto with algebra.
Qed.

Lemma is_finite_set_then_is_finite_subset :
 forall (A : Setoid) (B : part_set A), is_finite_set B -> is_finite_subset B.
intros; red in |- *; red in H.
inversion_clear H; inversion_clear H0.
exists x; exists (Map_embed x0).
destruct x0; simpl in H; red in H; simpl in H; simpl in |- *; red in |- *;
 simpl in |- *.
split; intros.
red in H0; elim (H (Build_subtype H0)).
intros p _; generalize (p I); clear p; intro.
inversion_clear H1.
red in H2.
exists x1.
simpl in H2.
auto.
inversion_clear H0.
apply in_part_comp_l with (subtype_elt (Ap x1)); auto with algebra.
Qed.

Lemma seq_set_is_finite_subset :
 forall (A : Setoid) (n : Nat) (v : seq n A), is_finite_subset (seq_set v).
intros.
red in |- *.
exists n.
exists v.
auto with algebra.
Qed.

(** - This one is surprisingly hard to prove (or did I not think hard enough?) *)

Lemma included_reflects_is_finite_subset :
 forall (A : Setoid) (B C : part_set A),
 is_finite_subset C -> included B C -> is_finite_subset B.
intros.
red in H.
inversion_clear H.
generalize B C H0 H1.
clear H1 H0 C B.
induction  x as [| x Hrecx].
intros.
inversion_clear H1.
assert (C =' empty A in _).
apply Trans with (seq_set x); auto with algebra.
clear H x.
assert (included B (empty A)).
apply included_comp with B C; auto with algebra.
red in H.
red in |- *.
exists 0; exists (empty_seq A).
apply Trans with (empty A); auto with algebra.
split.
intro; auto.
intro p; simpl in p; contradiction.

intros.
inversion_clear H1.
assert (in_part (head x0) B \/ ~ in_part (head x0) B); try apply classic.
inversion_clear H1.
assert (included (diff B (single (head x0))) (seq_set (Seqtl x0))).
red in |- *.
intros.
simpl in H1.
inversion_clear H1.
red in H0.
generalize (H0 x1 H3).
intro.
assert (in_part x1 (seq_set x0)).
apply in_part_comp_r with C; auto with algebra.
simpl in H5.
inversion_clear H5.
assert (~ x2 =' Build_finiteT (lt_O_Sn x) in fin (S x)).
unfold head in H4.
red in |- *; red in H4; intro; apply H4.
apply Trans with (x0 x2); auto with algebra.
assert
 (exists i : fin x,
    x2 ='
    match i with
    | Build_finiteT n Hn => Build_finiteT (lt_n_S _ _ Hn)
    end in fin (S x)).
clear H6 H1 H4 H3 x1 H2 H x0 H0 C B Hrecx A.
destruct x2.
simpl in H5.
simpl in |- *.
assert (exists n : Nat, index = S n).
destruct index as [| n].
absurd (0 = 0); auto.
exists n.
auto.
inversion_clear H.
rewrite H0 in in_range_prf.
exists (Build_finiteT (lt_S_n _ _ in_range_prf)).
simpl in |- *.
auto.
inversion_clear H7.
destruct x3.
apply in_part_comp_l with (x0 (Build_finiteT (lt_n_S _ _ in_range_prf)));
 auto with algebra.
simpl in |- *.
exists (Build_finiteT in_range_prf).
auto with algebra.
apply Trans with (x0 x2); auto with algebra.

generalize (Hrecx _ _ H1).
intros.
assert (exists v : seq x A, seq_set (Seqtl x0) =' seq_set v in _).
exists (Seqtl x0).
auto with algebra.
generalize (H3 H4); clear H4 H3; intros.
red in H3.
inversion_clear H3.
inversion_clear H4.
red in |- *.
exists (S x1).
exists (head x0;; x2).
assert
 (forall x : A,
  in_part x B -> x =' head x0 in _ \/ in_part x (diff B (single (head x0)))).
simpl in |- *.
intros.
case (classic (x3 =' head x0 in _)); intro.
left; auto.
right; auto.
simpl in |- *.
red in |- *.
intros.
split.
intro.
generalize (H4 x3 H5); clear H4; intros.
simpl in |- *.
case H4; clear H4; intros.
exists (Build_finiteT (lt_O_Sn x1)).
auto.
simpl in H3; red in H3.
generalize (H3 x3); clear H3; intros.
inversion_clear H3.
generalize (H6 H4); clear H6; intros.
simpl in H3.
inversion_clear H3.
destruct x4.
exists (Build_finiteT (lt_n_S _ _ in_range_prf)).
apply Trans with (x2 (Build_finiteT in_range_prf)); auto with algebra. 
intros.
simpl in H5.
inversion_clear H5.
destruct x4.
destruct index as [| n].
apply in_part_comp_l with (head x0); auto with algebra.
assert (included (diff B (single (head x0))) B).
red in |- *.
intros.
simpl in H5.
inversion_clear H5; auto.
red in H5.
apply H5; auto with algebra.
apply in_part_comp_r with (seq_set x2); auto with algebra.
simpl in |- *.
exists (Build_finiteT (lt_S_n n x1 in_range_prf)).
auto.

assert (included B (seq_set (Seqtl x0))).
red in |- *.
intros.
red in H0.
generalize (H0 _ H1).
intro.
assert (in_part x1 (seq_set x0)).
apply in_part_comp_r with C; auto with algebra.
clear H3; simpl in H4.
inversion_clear H4.
assert (~ x2 =' Build_finiteT (lt_O_Sn x) in fin (S x)).
red in |- *; red in H2; intro; apply H2.
apply in_part_comp_l with x1; auto with algebra.
apply Trans with (x0 x2); auto with algebra.
simpl in |- *.
assert
 (exists i : fin x,
    x2 ='
    match i with
    | Build_finiteT n Hn => Build_finiteT (lt_n_S _ _ Hn)
    end in fin (S x)).
destruct x2.
destruct index as [| n].
simpl in H4.
absurd (0 = 0); auto.
clear H4.
exists (Build_finiteT (lt_S_n _ _ in_range_prf)).
simpl in |- *.
auto.
inversion_clear H5.
exists x3.
destruct x3.
apply Trans with (x0 x2); auto with algebra.
apply (Hrecx _ _ H1); auto with algebra.
exists (Seqtl x0); auto with algebra.
Qed.

