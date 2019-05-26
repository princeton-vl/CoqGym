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


(** %\subsection*{ support :  concat.v }%*)
(** - concatenation of sequences, denoted by "++" (Haskell notation) plus some
 preliminary lemmas *)
Set Implicit Arguments.
Unset Strict Implicit.
Require Export conshdtl.

Section MAIN.
Variable A : Setoid.

(** %\label{concat}% *)
Definition concat :
  forall (n m : Nat) (f : seq n A) (g : seq m A), seq (n + m) A.
simple induction n.
simpl in |- *.
intros.
exact g.
intros.
simpl in |- *.
exact (f (Build_finiteT (lt_O_Sn n0));; X _ (Seqtl f) g).
(* ie. (concat (f0 :: (Seqtl f) g)) = f0 :: (concat (Seqtl f) g) *)
Defined.

Infix "++" := concat (at level 60, right associativity).

Lemma concat_comp :
 forall (n m : Nat) (f f' : seq n A) (g g' : seq m A),
 f =' f' in _ -> g =' g' in _ -> f ++ g =' f' ++ g' in _.
simple induction n.
intros.
simpl in |- *.
assumption.
(* the induction step *)
intros.
set (fg := f ++ g) in |- *.
set (fg' := f' ++ g') in |- *.
simpl in |- *.
red in |- *.
destruct x.
destruct index as [| n1].
unfold fg in |- *.
unfold fg' in |- *.
simpl in |- *.
auto with algebra.
(**)
apply Trans with ((Seqtl f ++ g) (Build_finiteT (lt_S_n _ _ in_range_prf)));
 auto with algebra.
apply Trans with ((Seqtl f' ++ g') (Build_finiteT (lt_S_n _ _ in_range_prf)));
 auto with algebra.
apply Ap_comp; auto with algebra.
apply (H _ (Seqtl f) (Seqtl f') g g'); auto with algebra.
change (Seqtl f =' Seqtl f' in _) in |- *.
apply Seqtl_comp; auto with algebra.
Qed.

Hint Resolve concat_comp: algebra.

Variable n m : Nat.

Lemma cons_concat :
 forall (a a' : A) (v v' : seq n A) (w w' : seq m A),
 a =' a' in _ ->
 v =' v' in _ -> w =' w' in _ -> a;; v ++ w =' (a';; v') ++ w' in _.
intros.
apply Trans with ((a;; v) ++ w).
intro i.
destruct i.
destruct index as [| n0].
simpl in |- *.
auto with algebra.
rename in_range_prf into p.
apply Trans with ((v ++ w) (Build_finiteT (lt_S_n _ _ p))); auto with algebra.
apply Trans with ((Seqtl (a;; v) ++ w) (Build_finiteT (lt_S_n _ _ p)));
 auto with algebra.
change ((a;; v) ++ w =' (a';; v') ++ w' in seq (S n + m) A) in |- *.
apply concat_comp; auto with algebra.
Qed.

Hint Resolve cons_concat: algebra.

Lemma concat_cons :
 forall (a a' : A) (v v' : seq n A) (w w' : seq m A),
 a =' a' in _ ->
 v =' v' in _ -> w =' w' in _ -> (a';; v') ++ w' =' a;; v ++ w in _.
intros; apply Sym; apply cons_concat; auto with algebra.
Qed.

Hint Resolve concat_cons: algebra.

Lemma cons_concat_special :
 forall (a : A) (v : seq n A) (v' : seq m A),
 a;; v ++ v' =' (a;; v) ++ v' in _. 
intros.
intro i.
destruct i.
destruct index as [| n0].
simpl in |- *.
auto with algebra.
rename in_range_prf into p.
apply Trans with ((v ++ v') (Build_finiteT (lt_S_n _ _ p)));
 auto with algebra.
apply Trans with ((Seqtl (a;; v) ++ v') (Build_finiteT (lt_S_n _ _ p)));
 auto with algebra.
Qed.


Lemma concat_first_element :
 forall (v : seq (S n) A) (w : seq m A) (Hnm : 0 < S (n + m)) (Hn : 0 < S n),
 (v ++ w) (Build_finiteT Hnm) =' v (Build_finiteT Hn) in _.
intros.
apply Trans with (head v); auto with algebra.
Qed.

Lemma head_eats_concat :
 forall (v : seq (S n) A) (w : seq m A), head (v ++ w) =' head v in _.
intros.
unfold head in |- *; auto with algebra.
Qed.

Lemma Seqtl_concat :
 forall (v : seq (S n) A) (w : seq m A), Seqtl (v ++ w) =' Seqtl v ++ w in _.
intros.
apply Trans with (Seqtl (hdtl v ++ w)); auto with algebra.
apply Trans with (Seqtl (head v;; Seqtl v ++ w)); auto with algebra.
unfold hdtl in |- *.
apply Seqtl_comp; auto with algebra.
change (Seqtl (head v;; Seqtl v ++ w) =' Seqtl v ++ w in seq (n + m) A)
 in |- *.
generalize dependent (Seqtl_cons_inv (head v) (Seqtl v ++ w)).
auto.
Qed.

Lemma concat_Seqtl :
 forall (v : seq (S n) A) (w : seq m A), Seqtl v ++ w =' Seqtl (v ++ w) in _.
intros.
apply Sym.
apply Seqtl_concat.
Qed.

End MAIN.

Infix "++" := concat (at level 60, right associativity).
Hint Resolve concat_comp: algebra.
Hint Resolve cons_concat concat_cons: algebra.
Hint Resolve concat_first_element head_eats_concat: algebra.
Hint Resolve Seqtl_concat concat_Seqtl: algebra.
Hint Resolve cons_concat_special: algebra.