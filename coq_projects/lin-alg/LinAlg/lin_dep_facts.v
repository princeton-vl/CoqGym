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


(** * lin_dep_facts.v *)
Set Implicit Arguments.
Unset Strict Implicit.
Require Export lin_dependence.
Require Export lin_comb_facts.
Require Export subseqs.
Require Export seq_set_facts.
Require Export distinct_facts.

(** - If $a_i\neq0$ and $\sum_ka_kv_k=0$, then $v_i=-a_i^{-1}\sum_{k\neq i}a_kv_k$ *)

Lemma rewrite_lin_comb_term :
 forall (F : field) (V : vectorspace F) (n : Nat) (a : seq (S n) F)
   (v : seq (S n) V) (i : fin (S n)),
 ~ a i =' (zero F) in _ ->
 sum (mult_by_scalars a v) =' (zero V) in _ ->
 v i =' field_inverse (a i) mX (min sum (omit (mult_by_scalars a v) i)) in _.
intros.
assert
 (a i mX v i ='
  a i mX field_inverse (a i) mX (min sum (omit (mult_by_scalars a v) i)) in _).

apply Trans with (mult_by_scalars a v i); auto with algebra.
apply
 Trans
  with
    ((a i rX field_inverse (a i)) mX (min sum (omit (mult_by_scalars a v) i)));
 auto with algebra.
apply Trans with (one mX (min sum (omit (mult_by_scalars a v) i)));
 auto with algebra.

apply Trans with (min sum (omit (mult_by_scalars a v) i)); auto with algebra.
assert
 (mult_by_scalars a v i +' sum (omit (mult_by_scalars a v) i) =' 
  (zero V) in _).

apply Trans with (sum (mult_by_scalars a v)); auto with algebra.
apply Sym.
apply
 (seqsum_is_elt_plus_omitseq (M:=V:abelian_monoid) (mult_by_scalars a v)).

2: apply MODULE_comp; auto with algebra.
2: apply Sym.
2: apply FIELD_inverse_r; auto with algebra.

apply Sym.
apply GROUP_law_inverse.
apply Trans with (sum (mult_by_scalars a v)); auto with algebra.
apply
 Trans with (mult_by_scalars a v i +' sum (omit (mult_by_scalars a v) i));
 auto with algebra.
apply Sym.
apply
 (seqsum_is_elt_plus_omitseq (M:=V:abelian_monoid) (mult_by_scalars a v));
 auto with algebra.

set (expr := field_inverse (a i) mX (min sum (omit (mult_by_scalars a v) i)))
 in *.

cut (one mX v i =' one mX expr in _).
intro.
apply Trans with (one mX expr); auto with algebra.
apply Trans with (one mX v i); auto with algebra.
apply Trans with ((field_inverse (a i) rX a i) mX v i).
apply MODULE_comp; auto with algebra.
apply Sym.
auto with algebra.
apply Trans with ((field_inverse (a i) rX a i) mX expr); auto with algebra.
apply Trans with (field_inverse (a i) mX a i mX expr); auto with algebra.
apply Trans with (field_inverse (a i) mX a i mX v i); auto with algebra.
Qed.

(** - If $y\in W\cup\{x\}$ but $y\neq x$ then $y\in W$ *)
Lemma another_small_lemma :
 forall (V : Setoid) (W : part_set V) (x : V),
 let Wx := union W (single x) in
 forall y : Wx, ~ subtype_elt y =' x in _ -> in_part (subtype_elt y) W.
simpl in |- *.
intros.
generalize H; elim y.
intros yv yp Hy.
simpl in yp.
simpl in Hy.
simpl in |- *.
unfold not in Hy.
case yp; auto.
tauto.
Qed.

(** - %\intoc{\bf Theorem 1.8}%: If $S\subset V$ is linearly independent and $x\not\in S$
 then $S\cup\{x\}$ is linearly dependent iff $x\in span(S)$

 (By the by - this innocent-looking lemma was extremely hard to prove) *)
Lemma lin_dep_vs_span_lemma :
 forall (F : field) (V : vectorspace F) (s : part_set V),
 lin_indep s ->
 forall x : V,
 ~ in_part x s -> (lin_dep (union s (single x)) <-> in_part x (span s)).  
intros.
set (Sx := union s (single x)) in *.
split.
intro.
unfold lin_dep in H1.
elim H1; clear H1; intros.
elim H1; clear H1; intros.
elim H1; clear H1; intros.
elim H1; clear H1; intros.
elim H2; clear H2; intros.
generalize x0 x1 x2 H1 H2 H3.
clear H3 H2 H1 x2 x1 x0; intros n a x' Hx' Ha Hlc.
assert (~ (forall i : fin (S n), in_part (Map_embed x' i) s)).
red in |- *; intro.
assert (exists y : seq (S n) s, Map_embed y =' Map_embed x' in _).
unfold seq in |- *.
apply subset_seq_castable; auto with algebra.
inversion H2.
repeat red in H; apply H.
red in |- *.
exists n.
exists a.
exists x0.
split.
assert (distinct (Map_embed x')).
apply Map_embed_preserves_distinct; auto with algebra.
assert (distinct (Map_embed x0)).
apply distinct_comp with (Map_embed x'); auto with algebra.
apply Map_embed_reflects_distinct; auto with algebra.
split.
auto.
apply Trans with (sum (mult_by_scalars a (Map_embed x'))); auto with algebra.
assert (exists i : fin (S n), ~ in_part (Map_embed x' i) s).
apply NNPP.
red in |- *; red in H1.
intro; apply H1.
intro.
red in H2.
apply NNPP.
red in |- *.
intro.
apply H2.
exists i; auto.
elim H2; intros.
generalize x0 H3; clear H3 x0; intros i Hi.
assert (in_part (Map_embed x' i) Sx).
apply Map_embed_prop; auto with algebra.
assert (in_part (Map_embed x' i) (single x)).
apply union_not_in_l with s; auto with algebra.
assert (Map_embed x' i =' x in _).
apply single_prop_rev; auto with algebra.
cut (~ a i =' (zero F) in _).
intro.
assert
 (Map_embed x' i ='
  field_inverse (a i)
  mX (min sum (omit (mult_by_scalars a (Map_embed x'):seq _ _) i)) in _).
apply rewrite_lin_comb_term; auto with algebra.
assert (forall j : fin n, in_part (omit (Map_embed x') i j) s).
intro.
assert (distinct (Map_embed x')).
apply Map_embed_preserves_distinct; auto with algebra.
assert (~ omit (Map_embed x') i j =' Map_embed x' i in _).
apply distinct_omit_removes_all; auto with algebra.
assert (~ omit (Map_embed x') i j =' x in _). 
red in |- *; red in H9; intro; apply H9.
apply Trans with x; auto with algebra.
assert (~ in_part (omit (Map_embed x') i j) (single x)).
red in |- *; red in H10; intro; apply H10.
apply single_prop_rev; auto with algebra.
assert (in_part (omit (Map_embed x') i j) Sx).
apply in_part_comp_l with (Map_embed (omit x' i) j); auto with algebra.
apply Map_embed_prop; auto with algebra.
assert (in_part (omit (Map_embed x') i j) (union (single x) s)).
apply in_part_comp_r with Sx; auto with algebra.
simpl in |- *.
red in |- *.
simpl in |- *.
split.
tauto.
tauto.
apply union_not_in_l with (single x); auto with algebra.
assert
 (x ='
  sum
    (mult_by_scalars
       (pointwise (uncurry (RING_comp (R:=F)))
          (const_seq n (min field_inverse (a i))) (omit a i))
       (omit (Map_embed x') i)) in _).
apply Trans with (Map_embed x' i); auto with algebra.
cut
 (field_inverse (a i)
  mX (min sum (omit (mult_by_scalars a (Map_embed x'):seq (S n) V) i)) ='
  sum
    (mult_by_scalars
       (pointwise (uncurry (RING_comp (R:=F)))
          (const_seq n (min field_inverse (a i))) (omit a i))
       (omit (Map_embed x') i)) in _).
intro.
apply
 Trans
  with
    (field_inverse (a i)
     mX (min sum (omit (mult_by_scalars a (Map_embed x')) i)));
 auto with algebra.
apply
 Trans
  with
    (sum
       (mult_by_scalars (const_seq n (min field_inverse (a i)))
          (mult_by_scalars (omit a i) (omit (Map_embed x') i)))).

2: apply sum_comp; auto with algebra.
apply
 Trans
  with
    ((min field_inverse (a i))
     mX sum (mult_by_scalars (omit a i) (omit (Map_embed x') i)));
 auto with algebra.
apply Sym; auto with algebra.
apply
 Trans
  with
    ((min field_inverse (a i))
     mX sum (omit (mult_by_scalars a (Map_embed x')) i)); 
 auto with algebra.
assert (exists y : seq n s, Map_embed y =' omit (Map_embed x') i in _).
unfold seq in |- *.
apply seq_castable; auto with algebra.
elim H10; intros.
assert
 (x ='
  sum
    (mult_by_scalars
       (pointwise (uncurry (RING_comp (R:=F)))
          (const_seq n (min field_inverse (a i))) (omit a i)) 
       (Map_embed x0)) in _).
apply
 Trans
  with
    (sum
       (mult_by_scalars
          (pointwise (uncurry (RING_comp (R:=F)))
             (const_seq n (min field_inverse (a i))) 
             (omit a i)) (omit (Map_embed x') i))); 
 auto with algebra.
simpl in |- *.
red in |- *.
exists n.
exists
 (pointwise (uncurry (RING_comp (R:=F)))
    (const_seq n (min field_inverse (a i))) (omit a i)).
exists x0.
auto.

generalize a x' Hx' Ha Hlc i H5; clear H5 H4 H3 Hi i H2 H1 Hlc Ha Hx' x' a;
 case n.
intros.
red in |- *; red in Ha; intro; apply Ha.
assert (head a =' (zero F) in _).
apply Trans with (a i); auto with algebra.
apply Sym; auto with algebra.

intros.
red in |- *; intro.
assert
 (sum (mult_by_scalars (omit a i) (omit (Map_embed x') i)) =' (zero V) in _).
apply Trans with (sum (omit (mult_by_scalars a (Map_embed x')) i));
 auto with algebra.
apply Trans with (sum (mult_by_scalars a (Map_embed x'))); auto with algebra.
apply Sym.
apply sum_omit_zeros; auto with algebra.
simpl in |- *.
apply Trans with ((zero F) mX subtype_elt (x' i)); auto with algebra.
assert (exists y : seq (S n0) s, Map_embed y =' omit (Map_embed x') i in _).
(* copy'n'paste *)
assert (forall j : fin (S n0), in_part (omit (Map_embed x') i j) s).
intro.
assert (distinct (Map_embed x')).
apply Map_embed_preserves_distinct; auto with algebra.
assert (~ omit (Map_embed x') i j =' Map_embed x' i in _).
apply distinct_omit_removes_all; auto with algebra.
assert (~ omit (Map_embed x') i j =' x in _). 
red in |- *; red in H4; intro; apply H4.
apply Trans with x; auto with algebra.
assert (~ in_part (omit (Map_embed x') i j) (single x)).
red in |- *; red in H6; intro; apply H6.
apply single_prop_rev; auto with algebra.
assert (in_part (omit (Map_embed x') i j) Sx).
apply in_part_comp_l with (Map_embed (omit x' i) j); auto with algebra.
apply Map_embed_prop; auto with algebra.
assert (in_part (omit (Map_embed x') i j) (union (single x) s)).
apply in_part_comp_r with Sx; auto with algebra.
simpl in |- *.
red in |- *.
simpl in |- *.
split.
tauto.
tauto.
apply union_not_in_l with (single x); auto with algebra.
unfold seq in |- *.
apply seq_castable; auto with algebra.
elim H3; intros.
assert (sum (mult_by_scalars (omit a i) (Map_embed x0)) =' (zero V) in _).
apply Trans with (sum (mult_by_scalars (omit a i) (omit (Map_embed x') i)));
 auto with algebra.
red in H.
red in H.
apply H; auto with algebra.
red in |- *.
exists n0.
exists (omit a i).
exists x0.
split.
apply Map_embed_reflects_distinct; auto with algebra.
apply distinct_comp with (omit (Map_embed x') i); auto with algebra.
split.
red in |- *; red in Ha; intro; apply Ha.
2: auto.
clear H6 H4 x0 H3 H2 H5 Hlc Hx' x' n Sx H0 x H s V.
simpl in |- *; red in |- *.
simpl in |- *.
intro j.
elim (fin_decidable i j).
intro.
apply Trans with (a i); auto with algebra.
change (Map_eq (omit a i) (const_seq (S n0) (zero F))) in H7.
red in H7.
intro.
generalize omit_removes'.
intro p.
case (p _ _ a _ _ H).
intros.
apply Trans with (omit a i x); auto with algebra.
apply Trans with (const_seq (S n0) (zero F) x); auto with algebra.
(* My gods that was painful *)

(* Now the other direction *)
intro.
simpl in H1.
generalize (lin_comb_with_distinct_vectors H1).
clear H1.
intro H1.
elim H1; clear H1; intros.
elim H1; clear H1; intros.
elim H1; clear H1; intros.
elim H1; clear H1; intros.
rename H2 into Dx2.
assert (exists v : seq x0 Sx, Map_embed v =' Map_embed x2 in _).
unfold seq in |- *.
apply subset_seq_castable; auto with algebra.
intro.
assert (in_part (Map_embed x2 i) s).
apply Map_embed_prop; auto with algebra.
unfold Sx in |- *.
apply in_part_union_l; auto with algebra.
elim H2; clear H2; intros.
assert (x =' sum (mult_by_scalars x1 (Map_embed x3)) in _).
apply Trans with (sum (mult_by_scalars x1 (Map_embed x2))); auto with algebra.
assert (exists x' : Sx, Sx x' =' x in _).
simpl in |- *.
assert (in_part x Sx).
simpl in |- *.
right; auto with algebra.
assert (Pred_fun Sx x); auto with algebra.
exists (Build_subtype H5).
simpl in |- *.
auto with algebra.
elim H4; clear H4; intros.
assert
 (sum (mult_by_scalars ((min one);; x1) (Map_embed (x4;; x3))) =' 
  (zero V) in _).
apply
 Trans with (sum (mult_by_scalars ((min one);; x1) (Sx x4;; Map_embed x3))).
apply sum_comp; auto with algebra.
unfold mult_by_scalars in |- *.
apply
 Trans
  with
    (sum
       (uncurry (MODULE_comp (Mod:=V)) (couple (min one) (Sx x4));;
        mult_by_scalars x1 (Map_embed x3))).
unfold mult_by_scalars in |- *.
apply sum_comp; auto with algebra.
apply
 Trans
  with
    (uncurry (MODULE_comp (R:=F) (Mod:=V)) (couple (min one) (Sx x4)) +'
     sum (mult_by_scalars x1 (Map_embed x3))); auto with algebra.
simpl in |- *.
apply
 Trans with ((min one mX Sx x4) +' sum (mult_by_scalars x1 (Map_embed x3)));
 auto with algebra.
apply Trans with ((min one mX Sx x4) +' x); auto with algebra.
apply Trans with ((min Sx x4) +' x); auto with algebra.
apply Trans with ((min x) +' x); auto with algebra.
red in |- *.
exists x0.
exists ((min one);; x1).
exists (x4;; x3).
split.
red in |- *.

assert (distinct x3).
apply Map_embed_reflects_distinct.
apply distinct_comp with (Map_embed x2); auto with algebra.
intros i j; case i; case j.
intros ni Hi nj Hj; generalize Hi Hj; clear Hj Hi; case ni; case nj.
simpl in |- *.
intros; absurd (0 = 0); auto.
3: intros.
3: simpl in |- *.
3: red in H6.
3: simpl in H6.
3: apply H6; auto with algebra.
simpl in |- *.
intros.
change (~ x3 (Build_finiteT (lt_S_n _ _ Hj)) =' x4 in _) in |- *.
red in |- *; intro.
assert (in_part (Sx (x3 (Build_finiteT (lt_S_n _ _ Hj)))) s).
apply in_part_comp_l with (Map_embed x3 (Build_finiteT (lt_S_n _ _ Hj)));
 auto with algebra.
apply in_part_comp_l with (Map_embed x2 (Build_finiteT (lt_S_n _ _ Hj)));
 auto with algebra.
apply Map_embed_prop; auto with algebra.
assert (~ in_part (Sx x4) s).
red in |- *; intro.
assert (in_part x s).
apply in_part_comp_l with (Sx x4); auto with algebra.
absurd (in_part x s); auto.
red in H10; (apply H10; auto with algebra).
apply in_part_comp_l with (Sx (x3 (Build_finiteT (lt_S_n _ _ Hj))));
 auto with algebra.
simpl in |- *.
intros.
change (~ x4 =' x3 (Build_finiteT (lt_S_n _ _ Hi)) in _) in |- *.
red in |- *; intro.
assert (in_part (Sx (x3 (Build_finiteT (lt_S_n _ _ Hi)))) s).
apply in_part_comp_l with (Map_embed x3 (Build_finiteT (lt_S_n _ _ Hi)));
 auto with algebra.
apply in_part_comp_l with (Map_embed x2 (Build_finiteT (lt_S_n _ _ Hi)));
 auto with algebra.
apply Map_embed_prop; auto with algebra.
assert (~ in_part (Sx x4) s).
red in |- *; intro.
assert (in_part x s).
apply in_part_comp_l with (Sx x4); auto with algebra.
absurd (in_part x s); auto.
red in H10; (apply H10; auto with algebra).
apply in_part_comp_l with (Sx (x3 (Build_finiteT (lt_S_n _ _ Hi))));
 auto with algebra.

split.
simpl in |- *.
red in |- *; intro.
red in H6.
generalize (H6 (Build_finiteT (lt_O_Sn x0))).
simpl in |- *.
intro.
absurd (one =' (zero F) in _); auto with algebra.
apply Trans with (min (zero F)); auto with algebra.
apply Trans with ((min (min one)):F); auto with algebra.
auto.
Qed.

(** - Remember how max_lin_dep was defined with respect to arbitrary sets instead of
 just subspaces. So (max_lin_indep W' W) need not mean span(W')=W *)

Lemma max_lin_indep_subset_generates_set :
 forall (F : field) (V : vectorspace F) (W W' : part_set V),
 max_lin_indep W' W -> forall w : W, is_lin_comb (subtype_elt w) W'.
intros.
red in H.
elim H; clear H; intros.
elim H0; clear H0; intros.
case (classic (in_part (subtype_elt w) W')).
intro; red in |- *.
exists 1.
exists (const_seq (A:=F) 1 one).
exists (const_seq (A:=W') 1 (Build_subtype H2)).
simpl in |- *.
apply Trans with (one mX subtype_elt w); auto with algebra.
intro.
generalize (lin_dep_vs_span_lemma (F:=F) (V:=V) (s:=W')).
intros.
generalize (H3 H0 (subtype_elt w) H2).
intro.
clear H3; inversion_clear H4.
apply H3; auto with algebra.
Qed.

(** - But of course we do have span(W')=span(W): *)
Lemma max_lin_indep_subset_has_same_span :
 forall (F : field) (V : vectorspace F) (W W' : part_set V),
 max_lin_indep W' W -> span W =' span W' in part_set V.
intros.
simpl in |- *.
red in |- *.
simpl in |- *.
split; intros.
apply lin_comb_casting with W; auto with algebra.
apply max_lin_indep_subset_generates_set; auto with algebra.
red in H.
inversion_clear H.
assert (included (span W') (span W)).
apply span_preserves_inclusion; auto with algebra.
change (in_part x (span W)) in |- *.
change (in_part x (span W')) in H0.
red in H.
apply H; auto with algebra.
Qed.

(** - The seq_set in this lemma is needed to transform seqs into sets: *)
Lemma seq_has_max_lin_indep_subseq :
 forall (F : field) (V : vectorspace F) (n : Nat) (v : seq n V),
 exists k : Nat,
   (exists w : seq k V,
      is_subseq w v /\ max_lin_indep (seq_set w) (seq_set v)).
simple induction n.
intro.
exists 0.
exists v.
split.
eapply is_subseq_comp.
apply is_subseq_empty; auto with algebra.
auto with algebra.
apply Refl.
split.
auto with algebra.
split.
apply lin_indep_comp with (seq_set (empty_seq V)); auto with algebra.

apply lin_indep_comp with (empty V); auto with algebra.
apply empty_lin_indep; auto with algebra.
intros; (apply False_ind; auto with algebra).

clear n.
intros.
generalize (H (Seqtl v)).
intro.
clear H.
inversion_clear H0.
inversion_clear H.
inversion_clear H0.
assert (lin_dep (seq_set (head v;; x0)) \/ lin_indep (seq_set (head v;; x0))).
unfold lin_indep in |- *.
apply classic; auto with algebra.
case H0; clear H0.
intro.
exists x.
exists x0.
split.
apply is_subseq_comp with x0 (hdtl v); auto with algebra; unfold hdtl in |- *.
apply is_subseq_of_tail; auto with algebra.
split.
inversion_clear H1.
red in H2.
red in |- *; intros.
generalize (H2 x1 H1); clear H2; intro; simpl in H2.
inversion_clear H2.
destruct x2.
simpl in |- *.
exists (Build_finiteT (lt_n_S index n in_range_prf)).
auto.
split.
inversion_clear H1.
inversion_clear H3.
apply H1; auto with algebra.
intro.
intro.
case (classic (y =' head v in _)).
intros.
apply lin_dep_comp with (seq_set (y;; x0)); auto with algebra.
apply lin_dep_comp with (seq_set (head v;; x0)); auto with algebra.
intros.
assert (in_part y (seq_set (Seqtl v))).
auto with algebra.
inversion_clear H1.
inversion_clear H7.
apply H8; auto with algebra.

intro.
exists (S x).
exists (head v;; x0).
split; try split.
apply is_subseq_comp with (head v;; x0) (hdtl v); auto with algebra.
unfold hdtl in |- *.
apply is_subseq_cons; auto with algebra.
red in |- *.
intros.
simpl in H2.
inversion_clear H2.
destruct x2.
destruct index as [| n0].
simpl in |- *.
exists (Build_finiteT (lt_O_Sn n)).
apply Trans with (head v); auto with algebra.
generalize
 (subseq_has_right_elements H (Build_finiteT (lt_S_n n0 x in_range_prf))).
intro.
inversion_clear H2.
simpl in |- *.
destruct x2.
exists (Build_finiteT (lt_n_S _ _ in_range_prf0)).
apply Trans with (x0 (Build_finiteT (lt_S_n n0 x in_range_prf)));
 auto with algebra.
split.
auto.
intro.
case (classic (y =' head v in _)).
intros.
absurd (in_part y (seq_set (head v;; x0))); auto.
simpl in |- *.
exists (Build_finiteT (lt_O_Sn x)).
auto.
intros.
inversion_clear H1.
apply lin_dep_include with (union (seq_set x0) (single y)); auto with algebra.
red in |- *.
intros.
simpl in H1.
simpl in |- *.
inversion_clear H1.
inversion_clear H7.
destruct x2.
left.
exists (Build_finiteT (lt_n_S _ _ in_range_prf)).
apply Trans with (x0 (Build_finiteT in_range_prf)); auto with algebra;
 (apply Ap_comp; auto with algebra); simpl in |- *; 
 auto.
right; auto.
inversion_clear H6.
apply H7; auto with algebra.
change (in_part y (seq_set (Seqtl v))) in |- *.
apply seq_set_head_or_tail; auto with algebra. 
red in |- *; red in H4; intro; (apply H4; auto with algebra).
apply in_part_included with (seq_set x0); auto with algebra.
red in |- *.
simpl in |- *.
intros.
inversion_clear H8.
destruct x2.
exists (Build_finiteT (lt_n_S _ _ in_range_prf)).
apply Trans with (x0 (Build_finiteT in_range_prf)); auto with algebra;
 (apply Ap_comp; auto with algebra); simpl in |- *; 
 auto.
Qed.