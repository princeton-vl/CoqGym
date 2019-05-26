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


(** %\subsection*{ support :  random\_facts.v }%*)
Set Implicit Arguments.
Unset Strict Implicit.
Section MAIN.
Require Export concat_facts.
Require Export sums2.
Require Export mult_by_scalars.
Require Export vecspace_Fn.

Lemma inject_map_embed_seq_set :
 forall (A : Setoid) (B : part_set A) (n : Nat) (v : seq n B),
 inject_subsets (seq_set v) =' seq_set (Map_embed v) in _.
simpl in |- *.
red in |- *.
split; intros.
rename x into a.
simpl in |- *.
simpl in H.
inversion_clear H.
destruct x.
rename subtype_elt into b.
rename subtype_prf into Hb.
simpl in Hb.
inversion_clear Hb.
rename x into i.
exists i.
red in H.
simpl in H0.
apply Trans with (subtype_elt b); auto with algebra.

simpl in |- *.
rename x into a.
assert (in_part a B).
simpl in H.
inversion_clear H.
apply in_part_comp_l with (subtype_elt (v x)); auto with algebra.
red in H0.
set (b := Build_subtype H0:B) in *.
assert (in_part b (seq_set v)).
simpl in |- *.
simpl in H.
inversion_clear H.
rename x into i.
exists i.
red in |- *.
apply Trans with a; auto with algebra.
red in H1.
exists (Build_subtype H1).
simpl in |- *.
auto with algebra.
Qed.

Section concat_const_seq.
Variable A : Setoid.
Let eqa : forall a : A, Predicate A.
intro; apply Build_Predicate with (fun a' => a' =' a in _).
red in |- *; simpl in |- *.
intros; apply Trans with x; auto with algebra.
Defined.

Lemma concat_const_seq :
 forall (n m : Nat) (a a' a'' : A),
 a =' a' in _ ->
 a' =' a'' in _ ->
 const_seq n a ++ const_seq m a' =' const_seq (n + m) a'' in _.
intros.
intro.
apply Trans with a; auto with algebra.
2: simpl in |- *.
2: apply Trans with a'; auto with algebra.
generalize
 (concat_prop_per_part (A:=A) (n:=n) (m:=m) (v:=const_seq n a)
    (w:=const_seq m a') (P:=eqa a)); intro.
simpl in H1.
destruct x.
apply H1; auto with algebra.
Qed.
End concat_const_seq.

Section mult_facts.
Variable F : field.
Variable V : vectorspace F.
Lemma mult_const_Zero :
 forall (n : Nat) (v : seq n V),
 mult_by_scalars (const_seq n (zero F)) v =' const_seq n (zero V) in seq _ _.
simple induction n.
simpl in |- *.
red in |- *.
intros.
inversion x.
inversion in_range_prf.
intros.
simpl in |- *.
red in |- *.
intro x; elim x; intro i; case i.
simpl in |- *.
intro.
apply Zero_times_a_vector_gives_zero; auto with algebra.
simpl in |- *.
intros.
apply Zero_times_a_vector_gives_zero; auto with algebra.
Qed.

Lemma mult_const_zero :
 forall (n : Nat) (a : seq n F),
 mult_by_scalars a (const_seq n (zero V)) =' const_seq n (zero V) in seq _ _.
intros.
simpl in |- *.
red in |- *.
intro x.
simpl in |- *.
apply a_scalar_times_zero_gives_zero; auto with algebra.
Qed.
End mult_facts.

Hint Resolve mult_const_Zero mult_const_Zero: algebra.

Section proj_via_mult_by_scalars.

Let basisvec0prop :
  forall (F : field) (n : Nat) (H : 0 < S n),
  Seqtl (Basisvec_Fn F H) =' const_seq n (zero F) in _.
intros.
simpl in |- *.
red in |- *.
simpl in |- *.
intro.
case x.
auto with algebra.
Qed.

Let basisvecprop2 :
  forall (F : field) (n i : Nat) (H : i < n) (HS : S i < S n),
  Seqtl (Basisvec_Fn F HS) =' Basisvec_Fn F H in _.
intros.
simpl in |- *.
red in |- *.
intro x; case x.
intros.
apply Ap_comp; auto with algebra.
Qed.

(** - $v_i = \vec e_i\cdot \vec v$ *)

Lemma projection_via_mult_by_scalars :
 forall (F : field) (M : module F) (n i : Nat) (Hi Hi' : i < n) (v : seq n M),
 v (Build_finiteT Hi) =' sum (mult_by_scalars (Basisvec_Fn F Hi') v) in _.
intros F M n. 
induction  n as [| n Hrecn].
intros.
inversion Hi.
intros.
apply Trans with (sum (hdtl (mult_by_scalars (Basisvec_Fn F Hi) v)));
 auto with algebra.
unfold hdtl in |- *.
generalize Hi; clear Hi.
generalize Hi'; clear Hi'.
elim i.
intros Hi' Hi.
apply Trans with (head (mult_by_scalars (Basisvec_Fn F Hi) v) +' (zero M)).
apply Trans with (head (mult_by_scalars (Basisvec_Fn F Hi) v));
 auto with algebra.
simpl in |- *.
apply Trans with (head v); auto with algebra.
apply
 Trans
  with
    (head (mult_by_scalars (Basisvec_Fn F Hi) v) +'
     sum (Seqtl (mult_by_scalars (Basisvec_Fn F Hi) v))); 
 auto with algebra.
apply SGROUP_comp; auto with algebra.
apply Trans with (sum (const_seq n (zero M))).
apply Sym.
apply sum_of_zeros; auto with algebra.
apply sum_comp.
apply Trans with (mult_by_scalars (Seqtl (Basisvec_Fn F Hi)) (Seqtl v)).
apply
 Trans
  with
    (mult_by_scalars (R:=F) (V:=M) (N:=n) (const_seq n (zero F):Map _ _)
       (Seqtl v:Map _ _)); auto with algebra.
unfold mult_by_scalars in |- *.
apply pointwise_Seqtl; auto with algebra.
(**)
intros.
apply Trans with (hdtl v (Build_finiteT Hi)).
apply Ap_comp; auto with algebra.
apply
 Trans with (sum ((zero M);; Seqtl (mult_by_scalars (Basisvec_Fn F Hi) v))).
apply
 Trans with ((zero M) +' sum (Seqtl (mult_by_scalars (Basisvec_Fn F Hi) v)));
 auto with algebra.
apply Trans with (sum (Seqtl (mult_by_scalars (Basisvec_Fn F Hi) v)));
 auto with algebra.
unfold hdtl in |- *.
apply Trans with (Seqtl v (Build_finiteT (lt_S_n _ _ Hi))); auto with algebra.
apply Trans with (sum (mult_by_scalars (Seqtl (Basisvec_Fn F Hi)) (Seqtl v))).
apply
 Trans with (sum (mult_by_scalars (Basisvec_Fn F (lt_S_n _ _ Hi)) (Seqtl v)));
 auto with algebra.
2: apply sum_comp.
2: simpl in |- *.
2: red in |- *.
2: auto with algebra.
apply sum_comp.
simpl in |- *.
red in |- *.
simpl in |- *.
intro x; case x.
auto with algebra.
Qed.

End proj_via_mult_by_scalars.

(** - $\sum_i (v_i+v'_i) = \sum_i v_i + \sum_i v'_i$ *)

Lemma sum_of_sums :
 forall (n : Nat) (M : abelian_monoid) (v v' : seq n M),
 sum (pointwise (sgroup_law_map M) v v') =' sum v +' sum v' in _.
simple induction n.
intros.
simpl in |- *.
auto with algebra.
intros.
apply Trans with (sum (hdtl v) +' sum (hdtl v')); auto with algebra.
apply Trans with (sum (pointwise (sgroup_law_map M) (hdtl v) (hdtl v'))).
apply sum_comp.
apply toMap.
apply pointwise_comp; auto with algebra.
unfold hdtl in |- *.
apply Trans with (head v +' sum (Seqtl v) +' (head v' +' sum (Seqtl v')));
 auto with algebra.
apply
 Trans
  with
    (sum
       (sgroup_law_map (E:=M) M (couple (head v) (head v'));;
        pointwise (sgroup_law_map M) (Seqtl v) (Seqtl v')));
 auto with algebra.
apply
 Trans
  with
    (sgroup_law_map M (couple (head v) (head v')) +'
     sum (pointwise (sgroup_law_map M) (Seqtl v) (Seqtl v')));
 auto with algebra.
apply
 Trans
  with
    (sgroup_law_map M (couple (head v) (head v')) +'
     sgroup_law M (sum (Seqtl v)) (sum (Seqtl v'))); 
 auto with algebra.
apply Trans with (head v +' head v' +' (sum (Seqtl v) +' sum (Seqtl v')));
 auto with algebra.
Qed.

End MAIN.