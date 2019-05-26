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


(** %\subsection*{ support :  omit\_facts.v }%*)
Set Implicit Arguments.
Unset Strict Implicit.
Require Export seq_equality_facts.
Require Export sums.
Require Export mult_by_scalars.

Lemma omit_head_is_seqtl :
 forall (n : Nat) (M : Setoid) (s : seq n M) (H0 : 0 < n),
 omit s (Build_finiteT H0) =' Seqtl s in _.
destruct n.
simpl in |- *.
red in |- *; auto with algebra.
destruct n.
intros; (apply Trans with (empty_seq M); auto with algebra).
auto with algebra.
Qed.

Hint Resolve omit_head_is_seqtl: algebra.


Lemma omit_tlelt :
 forall (n : Nat) (A : Setoid) (v : seq (S (S n)) A) 
   (m : Nat) (HS : S m < S (S n)) (H : m < S n),
 omit v (Build_finiteT HS) =' head v;; omit (Seqtl v) (Build_finiteT H) in _.
simple induction n.
intros A v m.
case m.
intros.
apply Trans with (head v;; empty_seq A); auto with algebra.
intros.
inversion H.
inversion H1.
intros.
apply Trans with (head v;; omit (Seqtl v) (Build_finiteT (lt_S_n _ _ HS)));
 auto with algebra.
change
  (head v;; omit (Seqtl v) (Build_finiteT (lt_S_n m (S (S n0)) HS)) ='
   head v;; omit (Seqtl v) (Build_finiteT H0) in seq (S (S n0)) A) 
 in |- *.
apply cons_comp; auto with algebra.
Qed.

Hint Resolve omit_tlelt: algebra.

(** - The above also holds for seqs of length (S n), but since the types
 become non-convertible then, we have to do a cast_seq or use seq_equal. *)

Lemma omit_tlelt' :
 forall (n : Nat) (A : Setoid) (v : seq (S n) A) (m : Nat) 
   (HS : S m < S n) (H : m < n) (Heq : S (pred n) = n),
 omit v (Build_finiteT HS) ='
 cast_seq (head v;; omit (Seqtl v) (Build_finiteT H)) Heq in _.
destruct n.
intros; inversion_clear Heq.
intros.
apply Trans with (head v;; omit (Seqtl v) (Build_finiteT H));
 auto with algebra.
Qed.

Hint Resolve omit_tlelt': algebra.

Lemma omit_tlelt'' :
 forall (n : Nat) (A : Setoid) (v : seq (S n) A) (m : Nat) 
   (HS : S m < S n) (H : m < n) (Heq : S (pred n) = n),
 seq_equal (omit v (Build_finiteT HS))
   (head v;; omit (Seqtl v) (Build_finiteT H)).
intros.
apply
 seq_equal_trans
  with
    (pred (S n))
    (cast_seq (head v;; omit (Seqtl v) (Build_finiteT H)) Heq);
 auto with algebra.
apply Map_eq_seq_equal; auto with algebra.
Qed.

Hint Resolve omit_tlelt'': algebra.

Lemma omit_concat_first_part :
 forall (n m : Nat) (A : Setoid) (v : seq (S n) A) 
   (w : seq m A) (i : Nat) (Hi : i < S n) (Hi' : i < S n + m),
 omit (v ++ w) (Build_finiteT Hi') =' omit v (Build_finiteT Hi) ++ w in _.
induction n.
intros.
destruct i as [| n].
2: inversion_clear Hi.
2: inversion_clear H.
apply Trans with (Seqtl (v ++ w)); auto with algebra.
apply Trans with (Seqtl v ++ w); auto with algebra.
intros.
destruct i as [| n0].
apply Trans with (Seqtl (v ++ w)); auto with algebra.
apply Trans with (Seqtl v ++ w); auto with algebra.
apply
 Trans
  with
    (head (v ++ w);;
     omit (Seqtl (v ++ w)) (Build_finiteT (lt_S_n _ (S (n + m)) Hi')));
 auto with algebra.
apply
 Trans with ((head v;; omit (Seqtl v) (Build_finiteT (lt_S_n _ _ Hi))) ++ w);
 auto with algebra.
apply
 Trans
  with
    (head v;;
     omit (Seqtl (v ++ w)) (Build_finiteT (lt_S_n _ (S (n + m)) Hi')));
 auto with algebra.
apply
 Trans
  with (head v;; omit (Seqtl v) (Build_finiteT (lt_S_n n0 (S n) Hi)) ++ w).
2: change
     (head v;; omit (Seqtl v) (Build_finiteT (lt_S_n n0 (S n) Hi)) ++ w ='
      (head v;; omit (Seqtl v) (Build_finiteT (lt_S_n n0 (S n) Hi))) ++ w
      in seq (S (n + m)) A) in |- *.
2: apply cons_concat_special.
change
  (head v;; omit (Seqtl (v ++ w)) (Build_finiteT (lt_S_n n0 (S (n + m)) Hi')) ='
   head v;; omit (Seqtl v) (Build_finiteT (lt_S_n n0 (S n) Hi)) ++ w
   in seq (S (n + m)) A) in |- *.
apply cons_comp; auto with algebra.
apply
 Trans with (omit (Seqtl v ++ w) (Build_finiteT (lt_S_n n0 (S (n + m)) Hi'))).
change
  (omit (Seqtl (v ++ w)) (Build_finiteT (lt_S_n n0 (S (n + m)) Hi')) ='
   omit (Seqtl v ++ w) (Build_finiteT (lt_S_n n0 (S (n + m)) Hi'))
   in seq (pred (S (n + m))) A) in |- *.
apply omit_comp; auto with algebra.
change
  (omit (Seqtl v ++ w) (Build_finiteT (lt_S_n n0 (S (n + m)) Hi')) ='
   omit (Seqtl v) (Build_finiteT (lt_S_n n0 (S n) Hi)) ++ w
   in seq (pred (S n + m)) A) in |- *.
apply (IHn m A (Seqtl v) w).
Qed.

Hint Resolve omit_concat_first_part: algebra.

(** - The following also comes in two guises. It is again an equation between two
 sequences of equal but non-convertible length. The first formulation uses the
 external (not inherited from any setoid) equality seq_equal, the second does a
 cast_seq in the appropriate places *)

Lemma omit_concat_second_part' :
 forall (n m : Nat) (A : Setoid) (v : seq n A) (w : seq m A) 
   (i : Nat) (Hi : i < m) (Hi' : n + i < n + m)
   (H : n + pred m = pred (n + m)),
 seq_equal (omit (v ++ w) (Build_finiteT Hi'))
   (v ++ omit w (Build_finiteT Hi)).
intros.

induction n.
intro j.
generalize (le_or_lt (pred (0 + m)) j).
intro p; inversion_clear p.
right; split; auto.

left.
exists H0.
exists (lt_comp H0 (sym_eq H)).
simpl in Hi', H, H0.
simpl in |- *.
apply Ap_comp; auto with algebra.
intro j.
generalize (le_or_lt (pred (S n + m)) j).
intro p; inversion_clear p.
right; split; auto.
rewrite H.
auto.
left.
exists H0.
exists (lt_comp H0 (sym_eq H)).

apply Trans with (omit (hdtl v ++ w) (Build_finiteT Hi') (Build_finiteT H0));
 auto with algebra.
apply
 Trans
  with
    ((hdtl v ++ omit w (Build_finiteT Hi))
       (Build_finiteT (lt_comp H0 (sym_eq H)))); auto with algebra.
unfold hdtl in |- *.
apply
 Trans
  with (omit (head v;; Seqtl v ++ w) (Build_finiteT Hi') (Build_finiteT H0));
 auto with algebra.
apply
 Trans
  with
    ((head v;; Seqtl v ++ omit w (Build_finiteT Hi))
       (Build_finiteT (lt_comp H0 (sym_eq H)))).
2: apply Ap_comp; auto with algebra.
2: apply toSeq; auto with algebra.
2: apply (cons_concat_special (head v) (Seqtl v) (omit w (Build_finiteT Hi))).
assert (n + m = S (pred (n + m))).
clear H0 j IHn w v A.
transitivity (S n + pred m); auto with arith.
transitivity (pred (S n + m)); auto with arith.
simpl in |- *.
apply S_pred with (n + i).
auto with arith.

apply
 Trans
  with
    (cast_seq (head v;; omit (Seqtl v ++ w) (Build_finiteT (lt_S_n _ _ Hi')))
       (sym_eq H1) (Build_finiteT H0)); fold (n + i) (n + m) in |- *.
apply Ap_comp; auto with algebra.
apply toSeq.
apply
 Trans
  with
    (cast_seq
       (head (head v;; Seqtl v ++ w);;
        omit (Seqtl (head v;; Seqtl v ++ w))
          (Build_finiteT (lt_S_n (n + i) (n + m) Hi'))) 
       (sym_eq H1)).
apply (omit_tlelt' (head v;; Seqtl v ++ w) Hi' (lt_S_n _ _ Hi') (sym_eq H1));
 auto with algebra.
apply cast_seq_comp; auto with algebra.
apply cons_comp; auto with algebra.
apply omit_comp; auto with algebra.
apply (Seqtl_cons_inv (head v) (Seqtl v ++ w)).

apply seq_equal_equal_elements; auto with algebra.
apply
 seq_equal_trans
  with
    (w := head v;;
          omit (Seqtl v ++ w) (Build_finiteT (lt_S_n (n + i) (n + m) Hi'))).
apply seq_equal_symm.
apply cast_seq_preserves_seq_equal.
apply seq_equal_cons; auto with algebra.
generalize (IHn (Seqtl v) (lt_S_n (n + i) (n + m) Hi')).
clear IHn; intro.
apply H2.
clear H2.
simpl in H.
transitivity (pred (S (n + pred m))); auto with arith.
Qed.

Lemma omit_concat_second_part :
 forall (n m : Nat) (A : Setoid) (v : seq n A) (w : seq m A) 
   (i : Nat) (Hi : i < m) (Hi' : n + i < n + m)
   (H : n + pred m = pred (n + m)),
 omit (v ++ w) (Build_finiteT Hi') ='
 cast_seq (v ++ omit w (Build_finiteT Hi)) H in _.
intros.
apply seq_equal_map_equal.
apply seq_equal_trans with (w := v ++ omit w (Build_finiteT Hi)).
apply omit_concat_second_part'; auto with algebra.
apply cast_seq_preserves_seq_equal.
Qed.

Lemma omit_seq_in_seq_set :
 forall (n : Nat) (A : Setoid) (v : seq n A) (i : fin n) (j : fin (pred n)),
 in_part (omit v i j) (seq_set v).
intros.
simpl in |- *.
elim (omit_removes v i j).
intros.
exists x; auto with algebra.
Qed.

Lemma seqsum_is_elt_plus_omitseq :
 forall (n : Nat) (M : abelian_monoid) (s : seq n M) (i : fin n),
 sum s =' s i +' sum (omit s i) in _.
destruct n.
intros.
apply False_ind; auto with algebra.

induction  n as [| n Hrecn].
simpl in |- *.
unfold head in |- *.
intros.
elim i.
intros.
apply SGROUP_comp; auto with algebra.

intros M.
generalize (Hrecn M); clear Hrecn; intros.
case i.
intro x; case x.
intro.
apply Trans with (head s +' sum (Seqtl s)); auto with algebra.
intros n0 l.
apply
 Trans
  with
    (Seqtl s (Build_finiteT (lt_S_n _ _ l)) +' sum (omit s (Build_finiteT l))).
2: apply SGROUP_comp; auto with algebra.

apply
 Trans
  with
    (Seqtl s (Build_finiteT (lt_S_n _ _ l)) +'
     sum (head s;; omit (Seqtl s) (Build_finiteT (lt_S_n _ _ l))));
 auto with algebra.
apply
 Trans
  with
    (Seqtl s (Build_finiteT (lt_S_n _ _ l)) +'
     (head s +' sum (omit (Seqtl s) (Build_finiteT (lt_S_n _ _ l)))));
 auto with algebra.
apply
 Trans
  with
    (head s +'
     (Seqtl s (Build_finiteT (lt_S_n _ _ l)) +'
      sum (omit (Seqtl s) (Build_finiteT (lt_S_n _ _ l)))));
 auto with algebra.
apply Trans with (head s +' sum (Seqtl s)); auto with algebra.
Qed.

Lemma seqsum_min_elt_is_omitseq :
 forall (n : Nat) (AG : abelian_group) (s : seq n AG) (i : fin n),
 sum s +' (min s i) =' sum (omit s i) in _.
intros.
apply GROUP_reg_right with (s i); auto with algebra.
apply Trans with (sum s +' ((min s i) +' s i)); auto with algebra.
apply Trans with (sum s +' (zero AG)); auto with algebra.
apply Trans with (sum s); auto with algebra.
apply Trans with (s i +' sum (omit s i)); auto with algebra.
generalize seqsum_is_elt_plus_omitseq.
intro p.
apply (p n AG s i).
Qed.

Hint Resolve omit_head_is_seqtl omit_tlelt seqsum_is_elt_plus_omitseq
  seqsum_min_elt_is_omitseq: algebra.


Lemma omit_mult_by_scalars :
 forall (n : Nat) (F : ring) (V : module F) (a : seq n F) 
   (v : seq n V) (i : fin n),
 omit (mult_by_scalars a v) i =' mult_by_scalars (omit a i) (omit v i) in _.
destruct n.
intros; (apply False_ind; auto with algebra).

induction  n as [| n Hrecn].
intros.
unfold omit in |- *.
unfold nat_rect in |- *.
unfold mult_by_scalars in |- *.
unfold pointwise in |- *.
simpl in |- *.
red in |- *.
intro.
apply False_ind; auto with algebra.
rename n into n'; intros.
case i.
intro x; case x.
intro l.
apply Trans with (Seqtl (mult_by_scalars a v)); auto with algebra.
apply Trans with (mult_by_scalars (Seqtl a) (Seqtl v)); auto with algebra.
intros n0 l.
apply
 Trans
  with
    (head (mult_by_scalars a v:seq _ _);;
     omit (Seqtl (mult_by_scalars a v))
       (Build_finiteT (lt_S_n _ _ l):fin (pred (S (S n')))));
 auto with algebra.
apply
 Trans
  with
    (mult_by_scalars (head a;; omit (Seqtl a) (Build_finiteT (lt_S_n _ _ l)))
       (head v;; omit (Seqtl v) (Build_finiteT (lt_S_n _ _ l))));
 auto with algebra.
unfold mult_by_scalars in |- *.
apply
 Trans
  with
    (uncurry (MODULE_comp (R:=F) (Mod:=V)) (couple (head a) (head v));;
     pointwise (uncurry (MODULE_comp (R:=F) (Mod:=V)))
       (omit (Seqtl a) (Build_finiteT (lt_S_n n0 (S n') l)))
       (omit (Seqtl v) (Build_finiteT (lt_S_n n0 (S n') l)))).
change
  (head (pointwise (uncurry (MODULE_comp (R:=F) (Mod:=V))) a v);;
   omit (Seqtl (pointwise (uncurry (MODULE_comp (R:=F) (Mod:=V))) a v))
     (Build_finiteT (lt_S_n n0 (S n') l)) ='
   uncurry (MODULE_comp (R:=F) (Mod:=V)) (couple (head a) (head v));;
   pointwise (uncurry (MODULE_comp (R:=F) (Mod:=V)))
     (omit (Seqtl a) (Build_finiteT (lt_S_n n0 (S n') l)))
     (omit (Seqtl v) (Build_finiteT (lt_S_n n0 (S n') l))) in _) 
 in |- *.
apply cons_comp; auto with algebra.
unfold mult_by_scalars in Hrecn.
apply
 Trans
  with
    (omit
       (pointwise (uncurry (MODULE_comp (R:=F) (Mod:=V))) (Seqtl a) (Seqtl v))
       (Build_finiteT (lt_S_n n0 (S n') l))); auto with algebra.
change
  (uncurry (MODULE_comp (R:=F) (Mod:=V)) (couple (head a) (head v));;
   pointwise (uncurry (MODULE_comp (R:=F) (Mod:=V)))
     (omit (Seqtl a) (Build_finiteT (lt_S_n n0 (S n') l)))
     (omit (Seqtl v) (Build_finiteT (lt_S_n n0 (S n') l))) ='
   pointwise (uncurry (MODULE_comp (R:=F) (Mod:=V)))
     (head a;; omit (Seqtl a) (Build_finiteT (lt_S_n n0 (S n') l)))
     (head v;; omit (Seqtl v) (Build_finiteT (lt_S_n n0 (S n') l))) in _)
 in |- *.
auto with algebra.
Qed.

Hint Resolve omit_mult_by_scalars: algebra.

Lemma omit_Map_embed :
 forall (n : Nat) (F : ring) (V : module F) (s : part_set V) 
   (v : seq n s) (i : fin n),
 omit (Map_embed v) i =' Map_embed (omit v i) in _.
destruct n.
intros.
apply False_ind; auto with algebra.

induction  n as [| n Hrecn].
intros.
unfold Map_embed, omit, nat_rect in |- *.
simpl in |- *.
red in |- *.
intros.
apply False_ind; auto with algebra.

intros.
case i.
intro x.
case x.
intro l.
apply Trans with (Seqtl (Map_embed v)); auto with algebra.
apply Trans with (Map_embed (Seqtl v)); auto with algebra.

intros n1 l.
apply
 Trans
  with
    (head (Map_embed v);;
     omit (Seqtl (Map_embed v)) (Build_finiteT (lt_S_n _ _ l)));
 auto with algebra.
apply
 Trans
  with (Map_embed (head v;; omit (Seqtl v) (Build_finiteT (lt_S_n _ _ l))));
 auto with algebra.
apply
 Trans
  with
    (s (head v);; Map_embed (omit (Seqtl v) (Build_finiteT (lt_S_n _ _ l))));
 auto with algebra.
change
  (head (Map_embed v);;
   omit (Seqtl (Map_embed v)) (Build_finiteT (lt_S_n n1 (S n) l)) ='
   s (head v);;
   Map_embed (omit (Seqtl v) (Build_finiteT (lt_S_n n1 (S n) l))) in _)
 in |- *.
apply cons_comp; auto with algebra.
apply Trans with (omit (Map_embed (Seqtl v)) (Build_finiteT (lt_S_n _ _ l)));
 auto with algebra.
change
  (s (head v);;
   Map_embed (omit (Seqtl v) (Build_finiteT (lt_S_n n1 (S n) l))) ='
   Map_embed (head v;; omit (Seqtl v) (Build_finiteT (lt_S_n n1 (S n) l)))
   in _) in |- *.
auto with algebra.
Qed.
Hint Resolve omit_Map_embed: algebra.
