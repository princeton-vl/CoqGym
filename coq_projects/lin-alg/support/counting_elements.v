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


(** %\subsection*{ support :  counting\_elements.v }%*)
Set Implicit Arguments.
Unset Strict Implicit.
From Algebra Require Export Diff.
From Algebra Require Export Singleton.
Require Export has_n_elements.
From Algebra Require Export Union.
Require Export const.
(** - Once we have has_n_elements, it would seem to be easy to define
 has_at_least_n_elements and has_at_most_n_elements. But one has to take a little
 care. We could not just say, e.g. [
 
Definition has_at_least_n_elements := ]
[    [n:nat;A:Setoid](EXT m:nat | (le n m) /\ (has_n_elements m A)).

 ] since the set may be infinite, and then there is no such m to be found.

 - But we may adapt the definition of has_n_elements slightly. It said that we can
 make a sequence [v] of length [n] with all elements distinct---[(distinct v)];
 covering the whole set---[(seq_set v)='(full v)]. Now we just drop this last
 requirement so we only need to point out a sequence of $n$ different elements:

 %\label{hasatleastnelements}% *)

Definition has_at_least_n_elements (n : Nat) (A : Setoid) :=
  exists v : seq n A, distinct v.

(** - Note that, contrarily, we may not just drop the other requirement to obtain 

[Definition has_at_most_n_elements_wrong := 
    [n:nat;A:Setoid](EXT v:(seq n A) | (full A)='(seq_set v)).]

 since this doesn't work out well for empty sets: it has at most n elements for any n,
 but with this definition we'd need to exhibit an n-length sequence, which we can't do
 for $n>0$.*)

Definition has_at_most_n_elements (n : Nat) (A : Setoid) :=
  exists m : nat, m <= n /\ has_n_elements m A.

Lemma has_at_most_n_elements_comp :
 forall (A : Setoid) (n m : Nat) (B C : part_set A),
 has_at_most_n_elements n B ->
 B =' C in _ -> n =' m in _ -> has_at_most_n_elements m C.
intros.
red in |- *.
red in H.
inversion_clear H.
rename x into Bsize.
inversion_clear H2.
exists Bsize.
split.
generalize (eq_ind _ (fun n => Bsize <= n) H _ H1).
auto.
apply has_n_elements_comp with Bsize B; auto with algebra.
Qed.

Lemma has_at_least_n_elements_comp :
 forall (A : Setoid) (n m : Nat) (B C : part_set A),
 has_at_least_n_elements n B ->
 B =' C in _ -> n =' m in _ -> has_at_least_n_elements m C.
intros.
rewrite <- H1.
red in |- *.
red in H.
inversion_clear H.
rename x into Bseq.
exists (Map_to_equal_subsets H0 Bseq).
red in |- *; intros; intro; red in H2; (apply (H2 i j); auto with algebra).
simpl in |- *.
red in |- *.
apply Trans with (subtype_elt (Bseq i)); auto with algebra.
apply Trans with (subtype_elt (Bseq j)); auto with algebra.
apply Trans with (subtype_elt (Map_to_equal_subsets H0 Bseq i));
 auto with algebra.
apply Trans with (subtype_elt (Map_to_equal_subsets H0 Bseq j));
 auto with algebra.
Qed.

Lemma has_n_elements_then_has_at_least_n_elements :
 forall (A : Setoid) (n : Nat),
 has_n_elements n A -> has_at_least_n_elements n A.
intros.
inversion_clear H.
exists x.
inversion_clear H0; auto.
Qed.

Lemma has_n_elements_then_has_at_most_n_elements :
 forall (A : Setoid) (n : Nat),
 has_n_elements n A -> forall m : Nat, n <= m -> has_at_most_n_elements m A.
intros.
exists n.
split; auto with arith.
Qed.

Lemma subset_has_at_least_n_elements :
 forall (A : Setoid) (n : Nat) (B : part_set A),
 has_at_least_n_elements n B -> has_at_least_n_elements n A.
intros.
red in |- *; red in H.
inversion_clear H.
exists (Map_embed x).
fold (distinct (Map_embed x)) in |- *.
fold (distinct x) in H0.
apply Map_embed_preserves_distinct; auto with algebra.
Qed.

Lemma subset_bounds_set_size_from_below :
 forall (A : Setoid) (B : part_set A) (n : Nat),
 has_n_elements n B -> has_at_least_n_elements n A.
intros.
apply subset_has_at_least_n_elements with B; auto with algebra.
apply has_n_elements_then_has_at_least_n_elements; auto with algebra.
Qed.


Lemma has_extra_element_strong :
 forall (A : Setoid) (B C : part_set A) (m n : Nat),
 has_at_least_n_elements n B ->
 has_n_elements m C -> m < n -> exists a : A, in_part a B /\ ~ in_part a C.
intros.
inversion H.
set (B' := seq_set (Map_embed x)) in *.
assert (has_n_elements n B').
red in |- *.
exists (seq_set_seq (Map_embed x)).
split.
unfold B' in |- *.
simpl in |- *.
red in |- *; simpl in |- *.
split; intro; auto.
clear H3.
unfold subtype_image_equal in |- *.
simpl in |- *.
destruct x0.
simpl in subtype_prf.
rename subtype_elt into a.
inversion_clear subtype_prf.
exists x0.
simpl in |- *.
auto.
red in |- *.
intros.
simpl in |- *.
unfold subtype_image_equal in |- *.
simpl in |- *.
intro; (apply (H2 i j); auto with algebra).
assert (exists a : A, in_part a B' /\ ~ in_part a C).
apply has_extra_element with m n; auto with algebra.
assert (included B' B).
red in |- *.
intros a Ha.
simpl in Ha.
inversion_clear Ha.
apply in_part_comp_l with (subtype_elt (x x0)); auto with algebra.
inversion_clear H4.
rename x0 into a.
exists a.
inversion_clear H6.
split; auto.
Qed.

Lemma not_at_least_then_at_most :
 forall (A : Setoid) (n : Nat),
 ~ has_at_least_n_elements (S n) A -> has_at_most_n_elements n A.
intros.
unfold has_at_least_n_elements in H.
unfold has_at_most_n_elements in |- *.
induction n.
exists 0; split; auto.
red in |- *.
exists (empty_seq A).
split.
simpl in |- *.
red in |- *.
intro a; split; simpl in |- *; auto.
intros _.
apply False_ind; auto with algebra.
apply H.
exists (const_seq 1 a).
intros; intro.
auto with algebra.
red in |- *.
intros.
auto with algebra.
case
 (classic
    (exists v : seq (S n) A,
       (forall i j : fin (S n), ~ i =' j in _ -> ~ v i =' v j in _))).
intro; exists (S n).
split; auto.
red in |- *.
inversion_clear H0.
rename x into aa.
exists aa.
split; auto.
simpl in |- *; red in |- *; simpl in |- *.
intro a; split; auto; intros _.
apply NNPP; intro; apply H.
exists (a;; aa).
red in |- *.
destruct i; destruct j.
destruct index as [| n0];
 [ destruct index0 as [| n0] | destruct index0 as [| n1] ].
simpl in |- *.
intuition.
simpl in |- *.
intros _.
intro; apply H0.
exists (Build_finiteT (lt_S_n n0 (S n) in_range_prf0)); auto with algebra.
simpl in |- *.
intros _.
intro; apply H0.
exists (Build_finiteT (lt_S_n n0 (S n) in_range_prf)).
apply Sym; auto with algebra.
simpl in |- *.
intro.
apply
 (H1 (Build_finiteT (lt_S_n n0 (S n) in_range_prf))
    (Build_finiteT (lt_S_n n1 (S n) in_range_prf0))); 
 auto with algebra.

intro.
generalize (IHn H0); intro p; inversion_clear p.
exists x.
inversion_clear H1; split; auto.
Qed.

Lemma has_n_elements_by_at_least_at_most :
 forall (A : Setoid) (n : Nat),
 has_at_least_n_elements n A ->
 has_at_most_n_elements n A -> has_n_elements n A.
intros.
red in H, H0.
inversion_clear H; inversion_clear H0.
inversion_clear H.
rename x0 into m.
red in |- *; red in H2.
inversion_clear H2.
inversion_clear H.
rename x into aas.
rename x0 into Aseq.
exists aas.
split; auto.
apply Trans with (seq_set Aseq); auto with algebra.

simpl in |- *; red in |- *; simpl in |- *.
intro a; split; simpl in |- *.

2: simpl in H2; red in H2; simpl in H2.
2: elim (H2 a); auto.

intro.
inversion_clear H.
rename x into i.
cut (exists j : fin n, aas j =' Aseq i in _).
intros.
inversion_clear H.
exists x.
apply Trans with (Aseq i); auto with algebra.
clear H4 a.

generalize (exists_difference H0).
intro; inversion_clear H.
rename x into d.
cut (exists j : fin (m + d), cast_seq aas H4 j =' Aseq i in _).
intro.
inversion_clear H.
rename x into j.
exists (cast_fin j (sym_eq H4)).
apply Trans with (cast_seq aas H4 j); auto with algebra.

set (aas' := cast_seq aas H4) in *.
assert (distinct aas').
unfold aas' in |- *.
apply cast_seq_preserves_distinct; auto with algebra.

assert (included (seq_set aas') (seq_set Aseq)).
simpl in H2; red in H2; simpl in H2.
red in |- *.
simpl in |- *; intros.
inversion_clear H5.
elim (H2 x); auto with algebra.

clearbody aas'.
clear H4 H2 H0 H1 aas n.
move d after m.
fold (distinct Aseq) in H3.

induction m.
apply False_ind; auto with algebra.

case (classic (head aas' =' Aseq i in _)).
intros.
exists (Build_finiteT (lt_O_Sn (m + d))).
apply Trans with (head aas'); auto with algebra.

intros.
elim (H5 (head aas')).
2: unfold head in |- *; simpl in |- *.
2: fold (m + d) in |- *.
2: exists (Build_finiteT (lt_O_Sn (m + d))).
2: apply Refl.

intros j Hj.

assert (distinct (omit Aseq j)).
apply omit_preserves_distinct; auto with algebra.

assert (~ j =' i in fin _).
assert (~ Aseq i =' Aseq j in _).
intro.
apply H0; auto with algebra.
apply Trans with (Aseq j); auto with algebra.
intro; apply H2.
apply (Map_compatible_prf Aseq); auto with algebra.

elim (omit_removes' Aseq H2).
intros i' HAseqi'.

assert (distinct (Seqtl aas')).
apply Seqtl_preserves_distinct; auto with algebra.
generalize (IHm (omit Aseq j) H1 i' (Seqtl aas') H4).
intros.

assert (included (seq_set (Seqtl aas')) (seq_set (omit Aseq j))).

2: specialize (H6 H7).
2: inversion_clear H6.
2: destruct x.
2: exists (Build_finiteT (lt_n_S _ _ in_range_prf)).
2: apply Trans with (Seqtl aas' (Build_finiteT in_range_prf));
    auto with algebra.
2: apply Trans with (omit Aseq j i'); auto with algebra.

clear H6.

clear IHm HAseqi' i' H2 H0 i.
cut
 (forall p : fin (m + d),
  exists q : fin m, Seqtl aas' p =' omit Aseq j q in _).
intro.
red in |- *.
simpl in |- *.
intros a Ha.
inversion_clear Ha.
generalize (H0 x); intro p; inversion_clear p.
exists x0.
apply Trans with (Seqtl aas' x); auto with algebra.

intro.
simpl in |- *.
destruct p.
set (p' := Build_finiteT (lt_n_S index (m + d) in_range_prf)) in *.

assert (~ p' =' Build_finiteT (lt_O_Sn (m + d)) in fin _).
unfold p' in |- *; simpl in |- *.
auto with arith.

assert
 (forall k : fin (S m + d), exists l : fin (S m), aas' k =' Aseq l in _).
red in H5.
simpl in H5.
intro.
generalize (H5 (aas' k)); intro.
assert (exists i : finiteT (S (m + d)), aas' k =' aas' i in _).
exists k.
apply Refl.
generalize (H2 H6).
intro.
inversion_clear H7.
exists x.
auto.

generalize (H2 p'); intro.
inversion_clear H6.
rename x into q.

cut (exists q0 : finiteT m, Aseq q =' omit Aseq j q0 in _).
intro.
inversion_clear H6.
exists x.
apply Trans with (Aseq q); auto with algebra.

cut (~ j =' q in _).
intro.
elim (omit_removes' Aseq H6).
intros; exists x; auto.

assert (~ aas' p' =' head aas' in _).
unfold head in |- *.
fold (m + d) in |- *.
apply H; auto with algebra.
assert (~ Aseq q =' head aas' in _).
intro; (apply H6; auto with algebra).
apply Trans with (Aseq q); auto with algebra.
assert (~ Aseq q =' Aseq j in _).
intro; (apply H8; auto with algebra).
apply Trans with (Aseq j); auto with algebra.
intro; (apply H9; auto with algebra).
Qed.

Lemma inclusion_bounds_elements_from_below :
 forall (A : Setoid) (B C : part_set A) (n : Nat),
 has_n_elements n B -> included B C -> has_at_least_n_elements n C.
intros; red in |- *.
red in H, H0.
inversion_clear H.
inversion_clear H1.
assert (forall i : fin n, in_part (Map_embed x i) C).
intro.
simpl in |- *.
apply H0; auto with algebra.
exists (cast_map_to_subset H1).
red in |- *; intros.
red in H2; (apply (H2 i j); auto with algebra).
Qed.

Lemma has_n_elements_doesn't_have_more :
 forall (A : Setoid) (n : Nat),
 has_n_elements n A -> forall m : Nat, n < m -> ~ has_at_least_n_elements m A.
red in |- *; intros.
assert (has_at_most_n_elements m A).
exists n.
split; auto with arith.
generalize (has_n_elements_by_at_least_at_most H1 H2).
intro.
assert (n =' m in _).
assert (has_n_elements n (full A)).
apply full_preserves_has_n_elements; auto with algebra.
assert (has_n_elements m (full A)).
apply full_preserves_has_n_elements; auto with algebra.
apply (has_n_elements_inj H4 H5); auto with algebra.
rewrite H4 in H0.
generalize lt_irrefl; intro p; red in p.
apply p with m; auto with algebra.
Qed.

Lemma union_has_at_most_n_plus_m_elements :
 forall (A : Setoid) (B C : part_set A) (n m : Nat),
 has_n_elements n B ->
 has_n_elements m C -> has_at_most_n_elements (n + m) (union B C).
intros.
red in |- *.
generalize dependent B.
induction n.
intros.
exists m.
split; auto with arith.
apply has_n_elements_comp with m C; auto with algebra.
apply Trans with (union (empty A) C); auto with algebra.
apply union_comp; auto with algebra.
apply Sym; auto with algebra.

intros.
red in H.
inversion_clear H.
rename x into Bs.
inversion_clear H1.
red in H2.
assert (has_n_elements n (seq_set (Map_embed (Seqtl Bs)))).
red in |- *.
exists (seq_set_seq (Map_embed (Seqtl Bs))).
split.
change
  (eq_part (full (seq_set (Map_embed (Seqtl Bs))))
     (seq_set (seq_set_seq (Map_embed (Seqtl Bs))))) 
 in |- *.
red in |- *.
intro.
simpl in |- *.
split; auto.
intros _.
unfold subtype_image_equal in |- *.
destruct x.
simpl in subtype_prf.
inversion_clear subtype_prf.
exists x.
simpl in |- *.
auto.
red in |- *; red in |- *; intros.
simpl in H3.
red in H3.
destruct i; destruct j.
apply
 (H2 (Build_finiteT (lt_n_S _ _ in_range_prf))
    (Build_finiteT (lt_n_S _ _ in_range_prf0))); auto with algebra.
simpl in |- *.
simpl in H1.
auto with arith.
generalize (IHn (seq_set (Map_embed (Seqtl Bs))) H1); intro p.
inversion_clear p.
rename x into m'.
inversion_clear H3.

case (classic (in_part (B (head Bs)) C)).
intro.
exists m'.
split.
simpl in |- *; auto with algebra.
apply has_n_elements_comp with m' (union (seq_set (Map_embed (Seqtl Bs))) C);
 auto with algebra.
apply Trans with (union (inject_subsets (seq_set Bs)) C); auto with algebra.
2: apply union_comp; auto with algebra.
2: apply Trans with (inject_subsets (full B)); auto with algebra.
apply
 Trans
  with
    (union (union (single (B (head Bs))) (seq_set (Map_embed (Seqtl Bs)))) C).
change
  (eq_part (union (seq_set (Map_embed (Seqtl Bs))) C)
     (union (union (single (B (head Bs))) (seq_set (Map_embed (Seqtl Bs)))) C))
 in |- *.
red in |- *.
intro a; split; intro.
simpl in H6.
inversion_clear H6.
simpl in |- *.
left.
right.
auto.
simpl in |- *.
right.
auto.
simpl in H6.
inversion_clear H6.
inversion_clear H7.
simpl in |- *.
right.
apply in_part_comp_l with (B (head Bs)); auto with algebra.
simpl in |- *.
left; auto.
simpl in |- *.
right; auto.

simpl in |- *; red in |- *; simpl in |- *.
intro a; split; intros.
inversion_clear H6.
inversion_clear H7.
right.
apply in_part_comp_l with (B (head Bs)); auto with algebra.
left.
inversion_clear H6.
destruct x.
assert (in_part (Bs (Build_finiteT (lt_n_S _ _ in_range_prf))) (seq_set Bs)).
simpl in |- *.
exists (Build_finiteT (lt_n_S index n in_range_prf)).
red in |- *; apply Refl.
red in H6; exists (Build_subtype H6).
simpl in |- *.
auto.
right; auto.

inversion_clear H6.
2: right; auto.
left.
inversion_clear H7.
destruct x.
rename subtype_elt into a'.
rename subtype_prf into Ha'.
simpl in Ha'.
inversion_clear Ha'.
red in H7.
destruct x.
destruct index as [| n0].
left.
simpl in H6.
apply Trans with (B a'); auto with algebra.
apply Trans with (subtype_elt (Bs (Build_finiteT in_range_prf)));
 auto with algebra.
right.
exists (Build_finiteT (lt_S_n _ _ in_range_prf)).
simpl in H6.
apply Trans with (subtype_elt a'); auto with algebra.
apply Trans with (subtype_elt (Bs (Build_finiteT in_range_prf)));
 auto with algebra.

intro.
exists (S m').
split.
simpl in |- *.
auto with arith.

inversion_clear H5.
rename x into BCs.
inversion_clear H6.
assert (forall i, in_part (Map_embed BCs i) (union B C)).
intro.
simpl in |- *.
set (bc := BCs i) in *.
change (in_part (subtype_elt bc) B \/ in_part (subtype_elt bc) C) in |- *.
case bc.
intros a Ha.
simpl in Ha.
inversion_clear Ha.
2: simpl in |- *; right; auto.
left.
inversion_clear H6.
destruct x.
apply
 in_part_comp_l
  with (subtype_elt (Bs (Build_finiteT (lt_n_S index n in_range_prf))));
 auto with algebra.

set (BCs' := cast_map_to_subset H6:seq _ _) in *.
set (b0 := B (head Bs)) in *.
assert (in_part b0 (union B C)).
simpl in |- *.
left.
unfold b0 in |- *.
simpl in |- *.
auto with algebra.
red in H8.
red in |- *.
set (bc0 := Build_subtype H8:union B C) in *.
exists (bc0;; BCs').
split.
simpl in |- *; red in |- *; simpl in |- *.
intro bc; (split; auto); intros _.
unfold subtype_image_equal in |- *.
case (classic (bc =' bc0 in union B C)).
intro.
exists (Build_finiteT (lt_O_Sn m')).
auto with algebra.
intro.
cut (exists i : _, subtype_elt bc =' subtype_elt (BCs i) in A).
intro.
inversion_clear H10.
destruct x.
exists (Build_finiteT (lt_n_S _ _ in_range_prf)).
apply Trans with (subtype_elt (BCs (Build_finiteT in_range_prf)));
 auto with algebra.
simpl in |- *.
apply subtype_elt_comp; auto with algebra.

cut (union B C =' seq_set (subtype_elt bc0;; Map_embed BCs) in _).
intro.
simpl in H10.
red in H10.
elim (H10 (subtype_elt bc)).
intros.
clear H10 H12.
assert (in_part (subtype_elt bc) (union B C)); auto with algebra.
generalize (H11 H10); clear H10 H11; intro p.
assert (in_part (subtype_elt bc) (seq_set (Map_embed BCs))).
simpl in p.
inversion_clear p.
destruct x.
destruct index as [| n0].
apply False_ind; auto with algebra.
apply
 in_part_comp_l
  with (subtype_elt (BCs (Build_finiteT (lt_S_n n0 m' in_range_prf))));
 auto with algebra.
simpl in |- *.
exists (Build_finiteT (lt_S_n n0 m' in_range_prf)).
apply Refl.
simpl in H10.
auto.

clear H9 bc BCs' H7 H4 H1 H2 IHn H0 m.
simpl in |- *; red in |- *; simpl in |- *.
intro a; split; intro.
inversion_clear H0.
case (classic (a =' b0 in _)).
intro; exists (Build_finiteT (lt_O_Sn m')); auto.
intro.
cut (in_part a (union (seq_set (Map_embed (Seqtl Bs))) C)).
intro p.
red in p.
assert
 (in_part (Build_subtype p:union (seq_set (Map_embed (Seqtl Bs))) C)
    (seq_set BCs)).
apply in_part_comp_r with (full (union (seq_set (Map_embed (Seqtl Bs))) C));
 auto with algebra.
simpl in H2.
inversion_clear H2.
destruct x.
exists (Build_finiteT (lt_n_S _ _ in_range_prf)).
red in H4; simpl in H4.
apply Trans with (subtype_elt (BCs (Build_finiteT in_range_prf)));
 auto with algebra.

simpl in |- *.
left.
red in H1.
set (a' := Build_subtype H1:B) in *.
elim (H a').
simpl in |- *; intros.
generalize (H2 I); clear H2 H4; intro.
inversion_clear H2.
destruct x.
destruct index as [| n0].
apply False_ind; auto with algebra.
apply H0.
red in H4.
apply Trans with (subtype_elt a'); auto with algebra.
apply Trans with (subtype_elt (Bs (Build_finiteT in_range_prf)));
 auto with algebra.
unfold b0 in |- *.
simpl in |- *.
apply subtype_elt_comp; auto with algebra.
unfold head in |- *.
exists (Build_finiteT (lt_S_n _ _ in_range_prf)).
red in H4.
apply Trans with (subtype_elt a'); auto with algebra.
apply Trans with (subtype_elt (Bs (Build_finiteT in_range_prf)));
 auto with algebra.

assert (in_part a (union (seq_set (Map_embed (Seqtl Bs))) C)).
simpl in |- *; right; auto.
red in H0.
elim (H5 (Build_subtype H0)).
simpl in |- *; intros.
generalize (H2 I); clear H4 H2; intro.
inversion_clear H2.
destruct x.
exists (Build_finiteT (lt_n_S _ _ in_range_prf)).
red in H4; simpl in H4.
apply Trans with (subtype_elt (BCs (Build_finiteT in_range_prf)));
 auto with algebra.

inversion_clear H0.
destruct x.
destruct index as [| n0].
left.
apply in_part_comp_l with b0; auto with algebra.
unfold b0 in |- *.
simpl in |- *.
auto with algebra.
set (a'' := BCs (Build_finiteT (lt_S_n n0 m' in_range_prf))) in *.
cut (in_part (subtype_elt a'') B \/ in_part (subtype_elt a'') C).
intros.
inversion_clear H0.
left.
apply in_part_comp_l with (subtype_elt a''); auto with algebra.
right.
apply in_part_comp_l with (subtype_elt a''); auto with algebra.
case a''.
simpl in |- *.
intros.
inversion_clear subtype_prf.
left.
inversion_clear H0.
destruct x.
rename subtype_elt into a'.
apply
 in_part_comp_l
  with (subtype_elt (Bs (Build_finiteT (lt_n_S index n in_range_prf0))));
 auto with algebra.
right; auto.

apply distinct_cons; auto with algebra.
intro.
unfold bc0, BCs' in |- *.
simpl in |- *.
unfold subtype_image_equal in |- *.
simpl in |- *.
unfold b0 in |- *.
simpl in |- *.
set (b := BCs i) in *.
change (~ subtype_elt (head Bs) =' subtype_elt b in _) in |- *.
case b.
intros a Ha; simpl in |- *.
simpl in Ha.
inversion_clear Ha.
inversion_clear H9.
destruct x.
intro; red in H2;
 (apply
   (H2 (Build_finiteT (lt_O_Sn n)) (Build_finiteT (lt_n_S _ _ in_range_prf)));
   auto with algebra).
simpl in |- *.
auto with arith.
simpl in |- *.
red in |- *.
apply Trans with (subtype_elt (head Bs)); auto with algebra.
apply Trans with a; auto with algebra.
intro; apply H3.
unfold b0 in |- *.
apply in_part_comp_l with a; auto with algebra.
Qed.

Lemma subset_also_has_n_elements_then_it_is_full :
 forall (n : Nat) (A : Setoid) (B : part_set A),
 has_n_elements n A -> has_n_elements n B -> B =' full A in _.

(* By contradiction: suppose x in A and not x in B. Then B is also a subset of A\{x}. But the first has n elements and the latter n-1, contradicting the above result.*)

intros.
apply Sym.
apply NNPP; intro.
assert (exists x : A, ~ in_part x B).
assert (~ (forall x : A, in_part x B)).
intro; red in H1; apply H1.
simpl in |- *; red in |- *; simpl in |- *.
split; auto.
apply NNPP; intro; apply H2.
intro a.
apply NNPP; intro; apply H3.
exists a; auto.

inversion_clear H2.
rename x into a.
assert (has_n_elements n (full A)).
apply full_preserves_has_n_elements; auto with algebra.

destruct n.
red in H.
inversion_clear H.
inversion_clear H4.
assert (in_part a (empty A)).
apply in_part_comp_r with (full A); auto with algebra.
simpl in H4.
auto.
(* ie. the case n=0 cannot happen; n->(S n)*)

assert (included B (diff (full A) (single a))).
red in |- *; simpl in |- *.
split; auto.
intro; (apply H3; auto with algebra).
apply in_part_comp_l with x; auto with algebra.

cut (has_n_elements n (diff (full A) (single a))).
intro.
absurd (has_at_least_n_elements (S n) (diff (full A) (single a))).
apply has_n_elements_doesn't_have_more with n; auto with algebra.
apply inclusion_bounds_elements_from_below with B; auto with algebra.

clear H4 H3 H H1 H0 B.
generalize (n_element_subset_sequence H2).
intro.
inversion_clear H.
inversion_clear H0.
assert (exists i : _, a =' x i in _).
simpl in H; red in H; simpl in H.
generalize (H a); intros.
inversion_clear H0.
auto.

inversion_clear H0.
rename x into As; rename x0 into i.
apply has_n_elements_comp with n (seq_set (omit As i)); auto with algebra.
assert (forall j, in_part (omit As i j) (seq_set (omit As i))).
intros.
Opaque omit.
simpl in |- *.
exists j.
apply Refl.
exists (cast_map_to_subset H0).
split.
simpl in |- *.
red in |- *.
simpl in |- *.
split; simpl in |- *; auto.
intros _.
unfold subtype_image_equal in |- *.
destruct x.
simpl in subtype_prf.
inversion_clear subtype_prf.
exists x.
simpl in |- *.
apply Trans with (omit As i x); auto with algebra.
red in |- *.
intros.
rename i0 into i'.
assert (~ omit As i i' =' omit As i j in _).
generalize (omit_preserves_distinct H1).
intro p; generalize (p i); clear p; intro p; red in p.
apply p; auto with algebra.
intro; red in H5; apply H5.
apply Trans with (subtype_elt (cast_map_to_subset H0 i')); auto with algebra.
apply Trans with (subtype_elt (cast_map_to_subset H0 j)); auto with algebra.

simpl in |- *.
red in |- *.
simpl in |- *.
split.
intuition.
inversion_clear H0.
generalize distinct_omit_removes_all.
intro p; generalize (p _ _ _ H1 i x0).
intro q; red in q; (apply q; auto with algebra).
apply Trans with a; auto with algebra.
apply Trans with x; auto with algebra.

intuition.
elim (H x).
simpl in |- *.
intros p _; generalize (p I); clear p; intro p.
inversion_clear p.
rename x0 into i'.
assert (~ i =' i' in _).
intro; apply H5.
apply Trans with (As i'); auto with algebra.
apply Trans with (As i); auto with algebra.

elim (omit_removes' As H6).
intro j; intro.
exists j; (apply Trans with (As i'); auto with algebra).
Qed.
