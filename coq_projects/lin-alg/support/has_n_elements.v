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


(** %\subsection*{ support :  has\_n\_elements.v }%*)
Set Implicit Arguments.
Unset Strict Implicit.
Require Export cast_between_subsets.
Require Export distinct_facts.

(** - There are n elements in a set whenever we can make a seq of n elements
 of that set, being all different, which form the full set

 %\label{hasnelements}% *)

Definition has_n_elements (n : Nat) (A : Setoid) :=
  exists v : seq n A, full A =' seq_set v in _ /\ distinct v.

Lemma has_n_elements_comp :
 forall (A : Setoid) (n m : Nat) (B C : part_set A),
 has_n_elements n B -> B =' C in _ -> n =' m in _ -> has_n_elements m C.
intros.
generalize H0; generalize H1; clear H1 H0; intros H0 H1.
red in |- *.
rewrite H0 in H.
red in H.
inversion_clear H.
exists (Map_to_equal_subsets H1 x).
inversion_clear H2.
split.
simpl in |- *.
red in |- *.
split; intros.
simpl in |- *.
unfold subtype_image_equal in |- *.
simpl in H1.
red in H1.
destruct x0.
rename subtype_elt into a.
rename subtype_prf into sp.
generalize (H1 a).
intro.
inversion_clear H4.
generalize (H6 sp).
intro.
set (a' := Build_subtype H4) in *.
simpl in H; red in H.
generalize (H a').
intro.
inversion_clear H7.
generalize (H8 I); intro.
simpl in H7.
inversion_clear H7.
rename x0 into i.
exists i.
apply Trans with (subtype_elt a'); auto with algebra.
simpl in |- *.
red in H10.
apply Trans with (subtype_elt (x i)); auto with algebra.
simpl in |- *.
auto.
red in |- *.
intros.
red in H3; intro; (apply (H3 i j); auto with algebra).
simpl in |- *.
simpl in H4.
red in |- *.
red in H4.
apply Trans with (subtype_elt (Map_to_equal_subsets H1 x i));
 auto with algebra.
apply Trans with (subtype_elt (Map_to_equal_subsets H1 x j));
 auto with algebra.
Qed.

(** - These are trivial results but for the one level of subset-ness: *)

Lemma n_element_subset_sequence :
 forall (A : Setoid) (n : Nat) (B : part_set A),
 has_n_elements n B -> exists v : seq n A, B =' seq_set v in _ /\ distinct v.
intros.
red in H.
inversion_clear H.
inversion_clear H0.
exists (Map_embed x).
simpl in H.
red in H.
simpl in H.
split; simpl in |- *.
red in |- *.
simpl in |- *.
intro a; split; intros.
generalize (H (Build_subtype H0)); clear H; intros (p, q); generalize (p I);
 clear p q; intro.
inversion_clear H.
red in H2.
exists x0.
simpl in H2.
auto.
inversion_clear H0.
apply in_part_comp_l with (subtype_elt (x x0)); auto with algebra.
apply Map_embed_preserves_distinct; auto with algebra.
Qed.

Lemma seq_set_n_element_subset :
 forall (A : Setoid) (n : Nat) (B : part_set A),
 (exists v : seq n A, B =' seq_set v in _ /\ distinct v) ->
 has_n_elements n B.
intros.
red in |- *.
inversion_clear H.
inversion_clear H0.
assert (forall i : fin n, in_part (x i) B).
intro.
simpl in H.
red in H.
generalize (H (x i)).
intros (p, q).
apply q.
simpl in |- *.
exists i; apply Refl.
exists (cast_map_to_subset H0).
split.
simpl in |- *.
red in |- *.
split; intro.
simpl in |- *.
unfold subtype_image_equal in |- *.
simpl in H; red in H; simpl in H.
generalize (H (subtype_elt x0)).
intros (p, q).
assert (in_part (subtype_elt x0) B); auto with algebra.
generalize (p H3); intro.
inversion_clear H4.
exists x1.
apply Trans with (x x1); auto with algebra.
simpl in |- *.
auto with algebra.
red in |- *; intros; red in H1; red in H1.
intro.
apply (H1 _ _ H2).
simpl in H3.
red in H3; simpl in H3.
destruct x.
simpl in H3.
simpl in |- *.
auto.
Qed.

Lemma has_zero_elements_then_empty :
 forall (A : Setoid) (B : part_set A),
 has_n_elements 0 B -> B =' empty A in _.
intros.
generalize (n_element_subset_sequence H).
intros (v, (E, D)).
apply Trans with (seq_set v); auto with algebra.
Qed.

Lemma empty_then_has_zero_elements :
 forall (A : Setoid) (B : part_set A),
 B =' empty A in _ -> has_n_elements 0 B.
intros.
apply seq_set_n_element_subset; auto with algebra.
exists (empty_seq A).
split.
apply Trans with (empty A); auto with algebra.
red in |- *.
intros.
apply False_ind; auto with algebra.
Qed.

Hint Resolve has_zero_elements_then_empty empty_then_has_zero_elements:
  algebra.

Lemma full_preserves_has_n_elements :
 forall (A : Setoid) (n : Nat),
 has_n_elements n A -> has_n_elements n (full A).
intros.
inversion_clear H.
inversion_clear H0.
apply seq_set_n_element_subset; auto with algebra.
exists x.
tauto.
Qed.

Lemma has_n_elements_inj :
 forall (A : Setoid) (n : Nat) (B : part_set A),
 has_n_elements n B ->
 forall (m : Nat) (C : part_set A),
 has_n_elements m C -> B =' C in _ -> n =' m in _.

induction n.
intros.
destruct m as [| n]; simpl in |- *.
auto.

inversion_clear H0.
set (c := head x) in *.
assert (B =' empty A in _).
generalize (n_element_subset_sequence H); intro p.
inversion_clear p.
inversion_clear H0.
apply Trans with (seq_set x0); auto with algebra.
simpl in H1; red in H1.
elim (H1 (C c)).
intros.
assert (in_part (subtype_elt c) C); auto with algebra.
generalize (H4 H5).
intros.
assert (in_part (C c) (empty A)).
apply in_part_comp_r with B; auto with algebra.
simpl in H7.
contradiction.

intros B HB.
induction m.
intros.
inversion_clear HB.
set (b := head x) in *.
assert (C =' empty A in _).
generalize (n_element_subset_sequence H); intro p.
inversion_clear p.
inversion_clear H2.
apply Trans with (seq_set x0); auto with algebra.
simpl in H0; red in H0.
elim (H0 (B b)).
intros.
assert (in_part (subtype_elt b) B); auto with algebra.
generalize (H3 H5).
intros.
assert (in_part (B b) (empty A)).
apply in_part_comp_r with C; auto with algebra.
simpl in H7.
contradiction.

generalize (n_element_subset_sequence HB); intro p.
inversion_clear p.
set (B' := seq_set (Seqtl x)) in *.
assert (distinct (Seqtl x)).
inversion_clear H.
apply Seqtl_preserves_distinct; auto with algebra.

assert (has_n_elements n B').
apply seq_set_n_element_subset.
exists (Seqtl x); auto with algebra.
intros.
simpl in H3.
red in H3.
elim (H3 (head x)).
intros.
assert (in_part (head x) B).
clear H3 H4 H5; inversion_clear H.
simpl in H3.
red in H3.
simpl in H3.
elim (H3 (head x)); intros.
unfold head in |- *.
apply H5; auto with algebra.
exists (Build_finiteT (lt_O_Sn n)).
unfold head in |- *; auto with algebra.
generalize (H4 H6).
intro.
clear H4 H5 H6.
rename H3 into HBC.
generalize (n_element_subset_sequence H2).
intro p; inversion_clear p.
inversion_clear H3.
assert (in_part (head x) (seq_set x0)).
apply in_part_comp_r with C; auto with algebra.
simpl in H3.
inversion_clear H3.
set (C' := seq_set (omit x0 x1)) in *.
assert (has_n_elements m C').
apply seq_set_n_element_subset.
exists (omit x0 x1); split; auto with algebra.
generalize omit_preserves_distinct.
intro p.
apply (p _ _ x0 H5 x1).
simpl in |- *.
apply f_equal with (f := S); auto with algebra.
apply (IHn _ H1 _ _ H3).

assert (seq_set x =' seq_set x0 in _).
inversion_clear H.
apply Trans with B; auto with algebra.
apply Trans with C; auto with algebra.
unfold B', C' in |- *.
inversion_clear H.
clear H3 C' H4 HBC H7 H2 C H1 H0 B' H9 IHm HB B IHn.
move H10 after x1.
rename x1 into i.

change (eq_part (seq_set (Seqtl x)) (seq_set (omit x0 i))) in |- *.
red in |- *.
intro a; split; intros.
assert (~ a =' x0 i in _).
assert (~ a =' head x in _).
simpl in H.
inversion_clear H.
destruct x1.
intro.
unfold head in H.
assert
 (x (Build_finiteT (lt_O_Sn n)) ='
  x (Build_finiteT (lt_n_S index n in_range_prf)) in _).
apply Trans with a; auto with algebra.
red in H10.
red in H10.
apply
 H10
  with
    (Build_finiteT (lt_O_Sn n))
    (Build_finiteT (lt_n_S index n in_range_prf)); 
 auto with algebra.
simpl in |- *.
auto.
intro; red in H0; (apply H0; auto with algebra).
apply Trans with (x0 i); auto with algebra.

assert (in_part a (seq_set x0)).
assert (in_part a (seq_set x)).
simpl in H.
inversion_clear H.
destruct x1.
apply in_part_comp_l with (x (Build_finiteT (lt_n_S index n in_range_prf)));
 auto with algebra.
simpl in |- *.
exists (Build_finiteT (lt_n_S index n in_range_prf)); auto with algebra.
apply in_part_comp_r with (seq_set x); auto with algebra.
simpl in H1.
inversion_clear H1.
rename x1 into q.
assert (~ i =' q in fin _).
intro; red in H0; apply H0.
apply Trans with (x0 q); auto with algebra.
elim (omit_removes' x0 H1).
intros.
apply in_part_comp_l with (x0 q); auto with algebra.
apply in_part_comp_l with (omit x0 i x1); auto with algebra.
simpl in |- *; exists x1; auto with algebra.

Opaque omit.
simpl in H.
inversion_clear H.
rename x1 into q.
assert (~ a =' x0 i in _).
intro.
generalize (distinct_omit_removes_all H5 (i:=i) (j:=q)); intro p; red in p.
apply p.
apply Trans with a; auto with algebra.
assert (~ a =' head x in _).
red in H; intro; apply H.
apply Trans with (head x); auto with algebra.
assert (in_part a (seq_set x0)).
apply in_part_comp_l with (omit x0 i q); auto with algebra.
apply omit_seq_in_seq_set; auto with algebra.
assert (in_part a (seq_set x)).
apply in_part_comp_r with (seq_set x0); auto with algebra.
simpl in H3; simpl in |- *.
inversion_clear H3.
destruct x1.
destruct index as [| n0].
apply False_ind; auto with algebra.
red in H1; apply H1.
unfold head in |- *;
 (apply Trans with (x (Build_finiteT in_range_prf)); auto with algebra);
 simpl in |- *.
exists (Build_finiteT (lt_S_n _ _ in_range_prf)).
apply Trans with (x (Build_finiteT in_range_prf)); auto with algebra.
Qed.

Lemma has_extra_element :
 forall (A : Setoid) (B C : part_set A) (m n : Nat),
 has_n_elements n B ->
 has_n_elements m C -> m < n -> exists a : A, in_part a B /\ ~ in_part a C.
intros.
assert (exists i : Nat, n =' S i + m in _).
clear H H0.
induction  H1 as [| m0 H1 HrecH1].
exists 0; simpl in |- *; auto.
inversion_clear HrecH1.
exists (S x).
simpl in |- *.
apply f_equal with (f := S).
auto.
inversion_clear H2.
rename x into d.
generalize B C n H H0 H1 d H3.
clear H3 d H1 H0 H n C B.
induction m.
intros.
destruct n.
inversion_clear H1.
generalize (n_element_subset_sequence H); intro p; inversion_clear p.
exists (x (Build_finiteT H1)).
inversion_clear H2.
split.
apply in_part_comp_r with (seq_set x); auto with algebra.
simpl in |- *.
exists (Build_finiteT H1); auto with algebra.
generalize (n_element_subset_sequence H0); intro p; inversion_clear p.
inversion_clear H2.
intro.
assert (in_part (x (Build_finiteT H1)) (empty A)).
apply in_part_comp_r with (seq_set x0); auto with algebra.
apply in_part_comp_r with C; auto with algebra.
simpl in H8.
auto.
intros.
generalize (n_element_subset_sequence H0); intro p; inversion_clear p.
inversion_clear H2.
case (classic (in_part (head x) B)).
destruct n.
inversion_clear H1.
generalize (n_element_subset_sequence H); intro p; inversion_clear p.
inversion_clear H2.
intro.
assert (in_part (head x) (seq_set x0)).
apply in_part_comp_r with B; auto with algebra.
simpl in H8.
inversion_clear H8.
rename x1 into i.
rename x0 into Bseq.
set (B' := seq_set (omit Bseq i)) in *.
set (C' := seq_set (Seqtl x)) in *.
generalize (IHm B' C' n).
assert (has_n_elements n B').
apply seq_set_n_element_subset; auto with algebra.
exists (omit Bseq i).
split; auto with algebra.
apply omit_preserves_distinct with (i := i); auto with algebra.
intro q; generalize (q H8); clear H8 q; intro.
assert (has_n_elements m C').
apply seq_set_n_element_subset; auto with algebra.
exists (Seqtl x); split; auto with algebra.
apply Seqtl_preserves_distinct with (v := x); auto with algebra.
assert (m < n); auto with arith.
assert (n = S d + m).
apply eq_add_S; auto with algebra.
transitivity (S d + S m).
auto.
symmetry  in |- *.
transitivity (S (S d) + m); auto.
apply plus_Snm_nSm.
generalize (H8 H10 H11 d H12); clear H12 H11 H10 H8; intro.
inversion_clear H8.
rename x0 into a; exists a.
inversion_clear H10.
split.
unfold B' in H8.
change (exists j : fin _, a =' omit Bseq i j in _) in H8.
inversion_clear H8.
rename x0 into j.
apply in_part_comp_l with (omit Bseq i j); auto with algebra.
apply in_part_comp_r with (seq_set Bseq); auto with algebra.
apply omit_seq_in_seq_set; auto with algebra.
apply not_inpart_comp_r with (seq_set x); auto with algebra.
simpl in |- *.
intro.
inversion_clear H10.
destruct x0.
rename index into xi.
destruct xi as [| n0].
assert (a =' head x in _).
apply Trans with (x (Build_finiteT in_range_prf)); auto with algebra;
 unfold head in |- *; simpl in |- *.
generalize distinct_omit_removes_all; intro q; red in q.
unfold B' in H8.
change (exists j : fin _, a =' omit Bseq i j in _) in H8.
inversion_clear H8.
rename x0 into j.
apply (q _ _ _ H7 i j).
apply Trans with a; auto with algebra.
apply Trans with (head x); auto with algebra.
assert (in_part a C').
simpl in |- *.
exists (Build_finiteT (lt_S_n _ _ in_range_prf)).
apply Trans with (x (Build_finiteT in_range_prf)); auto with algebra.
apply H11; auto with algebra.

(***********)

intro.
set (C' := seq_set (Seqtl x)) in *.
generalize (IHm B C' n H).
assert (has_n_elements m C').
apply seq_set_n_element_subset; auto with algebra.
exists (Seqtl x); split; auto with algebra.
apply Seqtl_preserves_distinct with (v := x); auto with algebra.
assert (m < n); auto with arith.
intro.
generalize (H8 H6 H7); clear H8; intro.
simpl in n; assert (n = S (S d) + m).
simpl in |- *; transitivity (S d + S m); auto.
symmetry  in |- *.
replace (S (S (d + m))) with (S (S d) + m); auto with arith.
apply plus_Snm_nSm.
generalize (H8 _ H9); clear H9 H8 H7; intro.
inversion_clear H7.
rename x0 into a.
inversion_clear H8.
exists a; split; auto.
apply not_inpart_comp_r with (seq_set x); auto with algebra.
simpl in |- *.
intro.
inversion_clear H8.
destruct x0.
rename index into xi.
destruct xi as [| n0].
assert (a =' head x in _).
apply Trans with (x (Build_finiteT in_range_prf)); auto with algebra;
 unfold head in |- *; simpl in |- *.
apply H2; auto with algebra.
apply in_part_comp_l with a; auto with algebra.
apply H9; auto with algebra.
simpl in |- *.
exists (Build_finiteT (lt_S_n _ _ in_range_prf)).
apply Trans with (x (Build_finiteT in_range_prf)); auto with algebra.
Qed.

Lemma inject_subsets_preserves_has_n_elements :
 forall (A : Setoid) (B : part_set A) (C : part_set B) (n : Nat),
 has_n_elements n C -> has_n_elements n (inject_subsets C).
intros.
red in H.
inversion_clear H.
rename x into cseq.
inversion_clear H0.
red in |- *.
exists (comp_map_map (Build_Map (inject_subsetsify_comp (C:=C))) cseq).
split.
simpl in |- *.
red in |- *.
intro c; split; intros.
simpl in |- *.
unfold subtype_image_equal in |- *.
simpl in |- *.
simpl in H; red in H; simpl in H.
destruct c.
rename subtype_elt into c''.
rename subtype_prf into Hc''.
simpl in Hc''.
elim Hc''.
intros c' Hc'.
elim (H c').
intros.
generalize (H2 I); clear H2 H3; intros.
inversion_clear H2.
rename x into i.
exists i.
simpl in |- *; red in H3.
apply Trans with (subtype_elt (subtype_elt c')); auto with algebra.
simpl in |- *.
auto.

simpl in |- *.
unfold subtype_image_equal in |- *.
simpl in |- *.
red in |- *; intros; intro.
red in H1; (apply (H1 i j); auto with algebra).
Qed.

Lemma inject_subsets_respects_has_n_elements :
 forall (A : Setoid) (B : part_set A) (C : part_set B) (n : Nat),
 has_n_elements n (inject_subsets C) -> has_n_elements n C.
intros.
red in |- *; red in H.
inversion_clear H.
inversion_clear H0.
rename x into isCseq.
exists (comp_map_map (Build_Map (uninject_subsetsify_comp (C:=C))) isCseq).
split.
simpl in |- *.
red in |- *.
intros.
simpl in |- *.
intuition.
unfold subtype_image_equal in |- *.
clear H0; simpl in H; red in H; simpl in H.
elim (H (inject_subsetsify x)).
intros.
generalize (H0 I); clear H0 H2; intro.
inversion_clear H0.
rename x into c.
rename x0 into i.
exists i.
red in H2.
simpl in H2.
apply Trans with (subtype_elt (isCseq i)); auto with algebra.
unfold uninject_subsetsify in |- *.
case (isCseq i).
simpl in |- *.
auto with algebra.
red in |- *.
simpl in |- *.
unfold subtype_image_equal in |- *.
unfold uninject_subsetsify in |- *.
intros.
generalize (H1 i j H0); clear H1.
case (isCseq i); case (isCseq j).
simpl in |- *.
unfold subtype_image_equal in |- *.
simpl in |- *.
auto with algebra.
Qed.