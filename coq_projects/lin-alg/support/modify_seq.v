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


(** %\subsection*{ support :  modify\_seq.v }%*)
(** - if $v=\langle v_0...v_i...v_{n-1}\rangle$ then (modify v i a) =
 $\langle v_0...a...v_{n-1}\rangle$ *)
Set Implicit Arguments.
Unset Strict Implicit.
Require Export conshdtl.

(** %\label{modifyseq}% *)
Definition modify_seq :
  forall (A : Setoid) (n : Nat), seq n A -> fin n -> A -> seq n A.
induction n.
intros.
auto.
intros.
destruct X0.
destruct index as [| n0].
exact (X1;; Seqtl X).
exact (head X;; IHn (Seqtl X) (Build_finiteT (lt_S_n _ _ in_range_prf)) X1).
Defined.

Lemma modify_comp :
 forall (A : Setoid) (n : Nat) (a a' : A) (v v' : seq n A) (i i' : fin n),
 a =' a' in _ ->
 v =' v' in _ -> i =' i' in _ -> modify_seq v i a =' modify_seq v' i' a' in _.
induction n.
intros.
apply False_ind; auto with algebra.
intros.
destruct i.
destruct i'.
destruct index as [| n0].
destruct index0 as [| n0].
apply split_hd_tl_equality; auto with algebra.
intro.
destruct x.
simpl in |- *.
apply Ap_comp; auto with algebra.
inversion H1.
destruct index0 as [| n1].
inversion H1.
unfold modify_seq in |- *.
unfold nat_rect in |- *.
apply cons_comp; auto with algebra.
unfold modify_seq in IHn.
apply IHn; auto with algebra.
change (Seqtl v =' Seqtl v' in _) in |- *.
apply Seqtl_comp; auto with algebra.
Qed.

Hint Resolve modify_comp: algebra.

Lemma modify_hd_hd :
 forall (A : Setoid) (n : Nat) (v : seq (S n) A) (H : 0 < S n) (a : A),
 head (modify_seq v (Build_finiteT H) a) =' a in _.
intros.
simpl in |- *.
auto with algebra.
Qed.

Hint Resolve modify_hd_hd: algebra.

Lemma modify_hd_tl :
 forall (A : Setoid) (n : Nat) (v : seq (S n) A) (H : 0 < S n) (a : A),
 Seqtl (modify_seq v (Build_finiteT H) a) =' Seqtl v in _.
intros.
unfold modify_seq, nat_rect in |- *.
auto with algebra.
Qed.

Hint Resolve modify_hd_tl: algebra.

Lemma modify_tl_hd :
 forall (A : Setoid) (n : Nat) (v : seq (S n) A) (m : Nat) 
   (H : S m < S n) (a : A),
 head (modify_seq v (Build_finiteT H) a) =' head v in _.
intros.
simpl in |- *; auto with algebra.
Qed.

Hint Resolve modify_tl_hd: algebra.

Lemma modify_tl_tl :
 forall (A : Setoid) (n : Nat) (v : seq (S n) A) (m : Nat) 
   (HS : S m < S n) (H : m < n) (a : A),
 Seqtl (modify_seq v (Build_finiteT HS) a) ='
 modify_seq (Seqtl v) (Build_finiteT H) a in _.
intros; intro.
unfold Seqtl in |- *.
simpl in |- *.
case x.
intros.
apply Ap_comp; auto with algebra.
Qed.

Hint Resolve modify_tl_tl: algebra.

Lemma Seqtl_modify_seq :
 forall (A : Setoid) (n : Nat) (v : seq (S n) A) (a : A) (H : 0 < S n),
 modify_seq v (Build_finiteT H) a =' a;; Seqtl v in _.
intros; intro.
simpl in |- *.
auto with algebra.
Qed.

Hint Resolve Seqtl_modify_seq.

Lemma modify_seq_defprop :
 forall (A : Setoid) (n : Nat) (v : seq n A) (i : fin n) (a : A),
 modify_seq v i a i =' a in _.
induction n.
intros.
apply False_ind; auto with algebra.
intros.
case i.
destruct index as [| n0].
simpl in |- *.
auto with algebra.
intro.
apply
 Trans
  with
    (modify_seq (Seqtl v) (Build_finiteT (lt_S_n _ _ in_range_prf)) a
       (Build_finiteT (lt_S_n _ _ in_range_prf))); 
 auto with algebra.
Qed.

Hint Resolve modify_seq_defprop: algebra.

Lemma modify_seq_modifies_one_elt :
 forall (A : Setoid) (n : Nat) (v : seq n A) (i : fin n) (a : A) (j : fin n),
 ~ j =' i in _ -> modify_seq v i a j =' v j in _.
induction n.
intros v i.
apply False_ind; auto with algebra.
intros until j.
destruct i; destruct j.
destruct index as [| n0];
 [ destruct index0 as [| n0] | destruct index0 as [| n1] ]; 
 simpl in |- *.
intros; absurd (0 = 0); auto.
intros _.
apply Ap_comp; auto with algebra.
intros _.
auto with algebra.
intros.
rename in_range_prf0 into l.
apply Trans with ((head v;; Seqtl v) (Build_finiteT l)).
2: apply Trans with (hdtl v (Build_finiteT l)); auto with algebra.
apply Trans with (Seqtl v (Build_finiteT (lt_S_n _ _ l))); auto with algebra.
Qed.

Hint Resolve modify_seq_modifies_one_elt: algebra.