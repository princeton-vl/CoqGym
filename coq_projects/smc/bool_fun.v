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


Require Import Bool.
Require Import Sumbool.
Require Import Arith.
Require Import ZArith NArith Nnat Ndec Ndigits.
From IntMap Require Import Allmaps.

Require Import misc.

Section Bool_fun.

Definition var_env := BDDvar -> bool.

Definition bool_fun := var_env -> bool.

Definition bool_fun_eq (bf1 bf2 : bool_fun) :=
  forall vb : var_env, bf1 vb = bf2 vb.

Definition bool_fun_zero (vb : var_env) := false.

Definition bool_fun_one (vb : var_env) := true.

Definition bool_fun_neg (bf : bool_fun) : bool_fun :=
  fun vb : var_env => negb (bf vb).

Definition bool_fun_or (bf1 bf2 : bool_fun) : bool_fun :=
  fun vb : var_env => bf1 vb || bf2 vb.

Definition bool_fun_and (bf1 bf2 : bool_fun) : bool_fun :=
  fun vb : var_env => bf1 vb && bf2 vb.

Definition bool_fun_impl (bf1 bf2 : bool_fun) : bool_fun :=
  fun vb : var_env => implb (bf1 vb) (bf2 vb).

Definition bool_fun_iff (bf1 bf2 : bool_fun) : bool_fun :=
  fun vb : var_env => eqb (bf1 vb) (bf2 vb).

Definition bool_fun_if (x : BDDvar) (bf1 bf2 : bool_fun) : bool_fun :=
  fun vb : var_env => ifb (vb x) (bf1 vb) (bf2 vb). 

Definition bool_fun_var (x : BDDvar) : bool_fun := fun vb : var_env => vb x.

Definition augment (vb : var_env) (x : BDDvar) (b : bool) : var_env :=
  fun y : BDDvar => if Neqb x y then b else vb y.

Definition bool_fun_restrict (bf : bool_fun) (x : BDDvar) 
  (b : bool) : bool_fun := fun vb : var_env => bf (augment vb x b).

Definition bool_fun_independent (bf : bool_fun) (x : BDDvar) :=
  forall b : bool, bool_fun_eq (bool_fun_restrict bf x b) bf.

Definition bool_fun_forall (x : BDDvar) (bf : bool_fun) :=
  bool_fun_and (bool_fun_restrict bf x true) (bool_fun_restrict bf x false).

Definition bool_fun_ex (x : BDDvar) (bf : bool_fun) :=
  bool_fun_or (bool_fun_restrict bf x true) (bool_fun_restrict bf x false).

Definition bool_fun_ext (bf : bool_fun) :=
  forall vb vb' : var_env,
  (forall x : BDDvar, vb x = vb' x) -> bf vb = bf vb'.

Inductive bool_expr : Set :=
  | Zero : bool_expr
  | One : bool_expr
  | Var : BDDvar -> bool_expr
  | Neg : bool_expr -> bool_expr
  | Or : bool_expr -> bool_expr -> bool_expr
  | ANd : bool_expr -> bool_expr -> bool_expr
  | Impl : bool_expr -> bool_expr -> bool_expr
  | Iff : bool_expr -> bool_expr -> bool_expr.

Fixpoint bool_fun_of_bool_expr (be : bool_expr) : bool_fun :=
  match be with
  | Zero => bool_fun_zero
  | One => bool_fun_one
  | Var x => bool_fun_var x
  | Neg be' => bool_fun_neg (bool_fun_of_bool_expr be')
  | Or be1 be2 =>
      bool_fun_or (bool_fun_of_bool_expr be1) (bool_fun_of_bool_expr be2)
  | ANd be1 be2 =>
      bool_fun_and (bool_fun_of_bool_expr be1) (bool_fun_of_bool_expr be2)
  | Impl be1 be2 =>
      bool_fun_impl (bool_fun_of_bool_expr be1) (bool_fun_of_bool_expr be2)
  | Iff be1 be2 =>
      bool_fun_iff (bool_fun_of_bool_expr be1) (bool_fun_of_bool_expr be2)
  end.

Lemma bool_fun_eq_refl : forall bf : bool_fun, bool_fun_eq bf bf.
Proof.
  unfold bool_fun_eq in |- *.  intros.  reflexivity.
Qed.

Lemma bool_fun_eq_sym :
 forall bf1 bf2 : bool_fun, bool_fun_eq bf1 bf2 -> bool_fun_eq bf2 bf1.
Proof.
  unfold bool_fun_eq in |- *.  intros.  rewrite (H vb).  reflexivity.
Qed.

Lemma bool_fun_eq_trans :
 forall bf1 bf2 bf3 : bool_fun,
 bool_fun_eq bf1 bf2 -> bool_fun_eq bf2 bf3 -> bool_fun_eq bf1 bf3.
Proof.
  unfold bool_fun_eq in |- *.  intros.  rewrite (H vb).  rewrite <- (H0 vb).  reflexivity.
Qed.

Lemma bool_fun_neg_preserves_eq :
 forall bf1 bf2 : bool_fun,
 bool_fun_eq bf1 bf2 -> bool_fun_eq (bool_fun_neg bf1) (bool_fun_neg bf2).
Proof.
  intros.  unfold bool_fun_eq, bool_fun_neg in |- *.  intros.  rewrite (H vb).  reflexivity.
Qed.

Lemma bool_fun_or_preserves_eq :
 forall bf1 bf1' bf2 bf2' : bool_fun,
 bool_fun_eq bf1 bf1' ->
 bool_fun_eq bf2 bf2' ->
 bool_fun_eq (bool_fun_or bf1 bf2) (bool_fun_or bf1' bf2').
Proof.
  intros.  unfold bool_fun_eq, bool_fun_or in |- *.  intros.  rewrite (H vb).  rewrite (H0 vb).  reflexivity.
Qed.

Lemma bool_fun_if_preserves_eq :
 forall (x : BDDvar) (bf1 bf2 bf1' bf2' : bool_fun),
 bool_fun_eq bf1 bf1' ->
 bool_fun_eq bf2 bf2' ->
 bool_fun_eq (bool_fun_if x bf1 bf2) (bool_fun_if x bf1' bf2').
Proof.
  unfold bool_fun_eq, bool_fun_if in |- *.  intros.  rewrite (H vb).  rewrite (H0 vb).
  reflexivity.
Qed.

Lemma bool_fun_and_preserves_eq :
 forall bf1 bf1' bf2 bf2' : bool_fun,
 bool_fun_eq bf1 bf1' ->
 bool_fun_eq bf2 bf2' ->
 bool_fun_eq (bool_fun_and bf1 bf2) (bool_fun_and bf1' bf2').
Proof.
  unfold bool_fun_eq, bool_fun_and in |- *.  intros.  rewrite (H vb).  rewrite (H0 vb).
  reflexivity.
Qed.

Lemma bool_fun_impl_preserves_eq :
 forall bf1 bf1' bf2 bf2' : bool_fun,
 bool_fun_eq bf1 bf1' ->
 bool_fun_eq bf2 bf2' ->
 bool_fun_eq (bool_fun_impl bf1 bf2) (bool_fun_impl bf1' bf2').
Proof.
  unfold bool_fun_eq, bool_fun_impl in |- *.  intros.  rewrite (H vb).  rewrite (H0 vb).
  reflexivity.
Qed.

Lemma bool_fun_iff_preserves_eq :
 forall bf1 bf1' bf2 bf2' : bool_fun,
 bool_fun_eq bf1 bf1' ->
 bool_fun_eq bf2 bf2' ->
 bool_fun_eq (bool_fun_iff bf1 bf2) (bool_fun_iff bf1' bf2').
Proof.
  unfold bool_fun_eq, bool_fun_iff in |- *.  intros.  rewrite (H vb).  rewrite (H0 vb).
  reflexivity.
Qed.

Lemma bool_fun_forall_preserves_eq :
 forall (bf1 bf2 : bool_fun) (x : BDDvar),
 bool_fun_eq bf1 bf2 ->
 bool_fun_eq (bool_fun_forall x bf1) (bool_fun_forall x bf2).
Proof.
  unfold bool_fun_eq, bool_fun_forall, bool_fun_and in |- *.  intros.
  unfold bool_fun_restrict in |- *.  rewrite (H (augment vb x true)).
  rewrite (H (augment vb x false)).  reflexivity.
Qed.

Lemma bool_fun_ex_preserves_eq :
 forall (bf1 bf2 : bool_fun) (x : BDDvar),
 bool_fun_eq bf1 bf2 -> bool_fun_eq (bool_fun_ex x bf1) (bool_fun_ex x bf2).
Proof.
  unfold bool_fun_eq, bool_fun_ex, bool_fun_or in |- *.  intros.
  unfold bool_fun_restrict in |- *.  rewrite (H (augment vb x true)).
  rewrite (H (augment vb x false)).  reflexivity.
Qed.

Lemma bool_fun_neg_zero :
 bool_fun_eq (bool_fun_neg bool_fun_zero) bool_fun_one.
Proof.
  unfold bool_fun_eq in |- *.  reflexivity.
Qed.

Lemma bool_fun_neg_one :
 bool_fun_eq (bool_fun_neg bool_fun_one) bool_fun_zero.
Proof.
  unfold bool_fun_eq in |- *.  reflexivity.
Qed.

Lemma bool_fun_and_lemma :
 forall bf1 bf2 : bool_fun,
 bool_fun_eq (bool_fun_and bf1 bf2)
   (bool_fun_neg (bool_fun_or (bool_fun_neg bf1) (bool_fun_neg bf2))).
Proof.
  unfold bool_fun_eq, bool_fun_neg, bool_fun_or, bool_fun_and in |- *.  intros.
  elim (bf1 vb); elim (bf2 vb); reflexivity.
Qed.

Lemma bool_fun_impl_lemma :
 forall bf1 bf2 : bool_fun,
 bool_fun_eq (bool_fun_impl bf1 bf2) (bool_fun_or (bool_fun_neg bf1) bf2).
Proof.
  unfold bool_fun_eq, bool_fun_impl, bool_fun_or, bool_fun_neg in |- *.  intros.
  elim (bf1 vb); elim (bf2 vb); reflexivity.
Qed.

Lemma bool_fun_iff_lemma :
 forall bf1 bf2 : bool_fun,
 bool_fun_eq (bool_fun_iff bf1 bf2)
   (bool_fun_impl (bool_fun_or bf1 bf2) (bool_fun_and bf1 bf2)).
Proof.
  unfold bool_fun_eq, bool_fun_iff, bool_fun_impl, bool_fun_or, bool_fun_and
   in |- *.
  intros.  elim (bf1 vb); elim (bf2 vb); reflexivity.
Qed.

Lemma bool_fun_ex_lemma :
 forall (bf : bool_fun) (x : BDDvar),
 bool_fun_eq (bool_fun_ex x bf)
   (bool_fun_neg (bool_fun_forall x (bool_fun_neg bf))).
Proof.
  unfold bool_fun_ex in |- *.  intros.  unfold bool_fun_forall in |- *.
  unfold bool_fun_or, bool_fun_and, bool_fun_neg, bool_fun_restrict in |- *.
  unfold bool_fun_eq in |- *.  intro.
  elim (bf (augment vb x true)); elim (bf (augment vb x false)); reflexivity.
Qed.

Lemma bool_fun_var_lemma :
 forall x : BDDvar,
 bool_fun_eq (bool_fun_var x) (bool_fun_if x bool_fun_one bool_fun_zero).
Proof.
  unfold bool_fun_var, bool_fun_one, bool_fun_zero, bool_fun_if, bool_fun_eq
   in |- *.
  intros.  elim (vb x); reflexivity.
Qed.

Lemma bool_fun_eq_neg_eq :
 forall bf1 bf2 : bool_fun,
 bool_fun_eq (bool_fun_neg bf1) (bool_fun_neg bf2) -> bool_fun_eq bf1 bf2.
Proof.
  unfold bool_fun_eq, bool_fun_neg in |- *.  intros.  cut (negb (bf1 vb) = negb (bf2 vb)).
  elim (bf1 vb).  elim (bf2 vb).  reflexivity.  simpl in |- *.  intro; discriminate.
  elim (bf2 vb).  intro; discriminate.  reflexivity.  apply H.
Qed.

Lemma bool_fun_neg_orthogonal :
 forall (x : BDDvar) (bf1 bf2 : bool_fun),
 bool_fun_eq (bool_fun_neg (bool_fun_if x bf1 bf2))
   (bool_fun_if x (bool_fun_neg bf1) (bool_fun_neg bf2)).
Proof.
  unfold bool_fun_eq, bool_fun_if, bool_fun_neg in |- *.  intros.  elim (vb x).
  reflexivity.  reflexivity.
Qed.

Lemma bool_fun_or_zero :
 forall bf : bool_fun, bool_fun_eq (bool_fun_or bf bool_fun_zero) bf.
Proof.
  unfold bool_fun_eq, bool_fun_or, bool_fun_zero in |- *.  intros.
  elim (bf vb); reflexivity.
Qed.

Lemma bool_fun_or_one :
 forall bf : bool_fun, bool_fun_eq (bool_fun_or bf bool_fun_one) bool_fun_one.
Proof.
  unfold bool_fun_eq, bool_fun_or, bool_fun_one in |- *.  intros.
  elim (bf vb); reflexivity.
Qed.

Lemma bool_fun_or_comm :
 forall bf1 bf2 : bool_fun,
 bool_fun_eq (bool_fun_or bf1 bf2) (bool_fun_or bf2 bf1).
Proof.
  unfold bool_fun_eq, bool_fun_or in |- *.  intros.
  elim (bf1 vb); elim (bf2 vb); reflexivity.
Qed.

Lemma bool_fun_and_comm :
 forall bf1 bf2 : bool_fun,
 bool_fun_eq (bool_fun_and bf1 bf2) (bool_fun_and bf2 bf1).
Proof.
  unfold bool_fun_eq, bool_fun_and in |- *.  intros.
  elim (bf1 vb); elim (bf2 vb); reflexivity.
Qed.

Lemma bool_fun_and_idempotent :
 forall bf : bool_fun, bool_fun_eq (bool_fun_and bf bf) bf.
Proof.
  unfold bool_fun_eq, bool_fun_and in |- *.  intros.  elim (bf vb); reflexivity.
Qed.

Lemma bool_fun_or_orthogonal :
 forall (x : BDDvar) (bf1 bf2 bf1' bf2' : bool_fun),
 bool_fun_eq (bool_fun_or (bool_fun_if x bf1 bf2) (bool_fun_if x bf1' bf2'))
   (bool_fun_if x (bool_fun_or bf1 bf1') (bool_fun_or bf2 bf2')).
Proof.
  unfold bool_fun_eq, bool_fun_or, bool_fun_if in |- *.  intros.  elim (vb x).
  reflexivity.  reflexivity.
Qed.

Lemma bool_fun_or_orthogonal_right :
 forall (x : BDDvar) (bf bf1' bf2' : bool_fun),
 bool_fun_eq (bool_fun_or bf (bool_fun_if x bf1' bf2'))
   (bool_fun_if x (bool_fun_or bf bf1') (bool_fun_or bf bf2')).
Proof.
  unfold bool_fun_eq, bool_fun_or, bool_fun_if in |- *.  intros.  elim (vb x).
  reflexivity.  reflexivity.
Qed.

Lemma bool_fun_or_orthogonal_left :
 forall (x : BDDvar) (bf1 bf2 bf' : bool_fun),
 bool_fun_eq (bool_fun_or (bool_fun_if x bf1 bf2) bf')
   (bool_fun_if x (bool_fun_or bf1 bf') (bool_fun_or bf2 bf')).
Proof.
  unfold bool_fun_eq, bool_fun_or, bool_fun_if in |- *.  intros.  elim (vb x).
  reflexivity.  reflexivity.
Qed.

Lemma bool_fun_and_orthogonal :
 forall (x : BDDvar) (bf1 bf2 bf1' bf2' : bool_fun),
 bool_fun_eq (bool_fun_and (bool_fun_if x bf1 bf2) (bool_fun_if x bf1' bf2'))
   (bool_fun_if x (bool_fun_and bf1 bf1') (bool_fun_and bf2 bf2')).
Proof.
  unfold bool_fun_eq, bool_fun_and, bool_fun_if in |- *.  intros.  elim (vb x).
  reflexivity.  reflexivity.
Qed.

Lemma bool_fun_forall_independent :
 forall (x : BDDvar) (bf : bool_fun),
 bool_fun_independent bf x -> bool_fun_eq (bool_fun_forall x bf) bf.
Proof.
  unfold bool_fun_forall in |- *.  unfold bool_fun_independent in |- *.  intros.
  apply bool_fun_eq_trans with (bf2 := bool_fun_and bf bf).
  apply bool_fun_and_preserves_eq.  apply H.  apply H.
  apply bool_fun_and_idempotent.
Qed.

Lemma bool_fun_forall_zero :
 forall x : BDDvar,
 bool_fun_eq (bool_fun_forall x bool_fun_zero) bool_fun_zero.
Proof.
  intro.  unfold bool_fun_eq, bool_fun_forall, bool_fun_zero, bool_fun_restrict
   in |- *.
  intro.  reflexivity.
Qed.

Lemma bool_fun_forall_one :
 forall x : BDDvar, bool_fun_eq (bool_fun_forall x bool_fun_one) bool_fun_one.
Proof.
  intro.  unfold bool_fun_eq, bool_fun_forall, bool_fun_one, bool_fun_restrict
   in |- *.
  intro.  reflexivity.
Qed.

Lemma bool_fun_restrict_zero :
 forall (x : BDDvar) (b : bool),
 bool_fun_eq (bool_fun_restrict bool_fun_zero x b) bool_fun_zero.
Proof.
  intros.  unfold bool_fun_eq, bool_fun_restrict, bool_fun_zero, bool_fun_one in |- *.
  intros.  unfold augment in |- *.  reflexivity.
Qed.

Lemma bool_fun_restrict_one :
 forall (x : BDDvar) (b : bool),
 bool_fun_eq (bool_fun_restrict bool_fun_one x b) bool_fun_one.
Proof.
  intros.  unfold bool_fun_eq, bool_fun_restrict, bool_fun_zero, bool_fun_one in |- *.
  intros.  unfold augment in |- *.  reflexivity.
Qed.

Lemma bool_fun_restrict_preserves_eq :
 forall (bf1 bf2 : bool_fun) (x : BDDvar) (b : bool),
 bool_fun_eq bf1 bf2 ->
 bool_fun_eq (bool_fun_restrict bf1 x b) (bool_fun_restrict bf2 x b).
Proof.
  unfold bool_fun_eq, bool_fun_restrict in |- *.  intros.  rewrite (H (augment vb x b)).
  reflexivity.
Qed.

Lemma bool_fun_independent_zero :
 forall x : BDDvar, bool_fun_independent bool_fun_zero x.
Proof.
  unfold bool_fun_independent, bool_fun_zero in |- *.  unfold bool_fun_restrict, bool_fun_eq in |- *.
  reflexivity.
Qed.

Lemma bool_fun_independent_one :
 forall x : BDDvar, bool_fun_independent bool_fun_one x.
Proof.
  unfold bool_fun_independent, bool_fun_one in |- *.  unfold bool_fun_restrict, bool_fun_eq in |- *.
  reflexivity.
Qed.

Lemma bool_fun_eq_independent :
 forall (bf1 bf2 : bool_fun) (x : BDDvar),
 bool_fun_eq bf1 bf2 ->
 bool_fun_independent bf1 x -> bool_fun_independent bf2 x.
Proof.
  unfold bool_fun_independent in |- *.  intros.
  apply bool_fun_eq_trans with (bf2 := bool_fun_restrict bf1 x b).
  apply bool_fun_restrict_preserves_eq.  apply bool_fun_eq_sym.  assumption.
  apply bool_fun_eq_trans with (bf2 := bf1).  apply H0.  assumption.
Qed.

Lemma bool_fun_if_restrict_true :
 forall (bf1 bf2 : bool_fun) (x : BDDvar),
 bool_fun_eq (bool_fun_restrict (bool_fun_if x bf1 bf2) x true)
   (bool_fun_restrict bf1 x true).
Proof.
  intros.  unfold bool_fun_eq, bool_fun_if in |- *.  unfold bool_fun_restrict in |- *.
  unfold augment at 1 in |- *.  rewrite (Neqb_correct x).  simpl in |- *.  reflexivity.
Qed.

Lemma bool_fun_if_restrict_false :
 forall (bf1 bf2 : bool_fun) (x : BDDvar),
 bool_fun_eq (bool_fun_restrict (bool_fun_if x bf1 bf2) x false)
   (bool_fun_restrict bf2 x false).
Proof.
  intros.  unfold bool_fun_eq, bool_fun_if in |- *.  unfold bool_fun_restrict in |- *.
  unfold augment at 1 in |- *.  rewrite (Neqb_correct x).  simpl in |- *.  reflexivity.
Qed.

Lemma bool_fun_if_restrict :
 forall (bf1 bf2 : bool_fun) (x y : BDDvar) (b : bool),
 Neqb x y = false ->
 bool_fun_eq (bool_fun_restrict (bool_fun_if x bf1 bf2) y b)
   (bool_fun_if x (bool_fun_restrict bf1 y b) (bool_fun_restrict bf2 y b)).
Proof.
  intros.  unfold bool_fun_restrict in |- *.  unfold bool_fun_eq in |- *.  intros.
  unfold augment in |- *.  unfold bool_fun_if in |- *.  rewrite (Neqb_comm x y) in H.
  rewrite H.  reflexivity.  
Qed.

Lemma bool_fun_if_restrict_true_independent :
 forall (bf1 bf2 : bool_fun) (x : BDDvar),
 bool_fun_independent bf1 x ->
 bool_fun_eq (bool_fun_restrict (bool_fun_if x bf1 bf2) x true) bf1.
Proof.
  unfold bool_fun_independent in |- *.  intros.
  apply bool_fun_eq_trans with (bf2 := bool_fun_restrict bf1 x true).
  apply bool_fun_if_restrict_true.  apply H.
Qed.

Lemma bool_fun_if_restrict_false_independent :
 forall (bf1 bf2 : bool_fun) (x : BDDvar),
 bool_fun_independent bf2 x ->
 bool_fun_eq (bool_fun_restrict (bool_fun_if x bf1 bf2) x false) bf2.
Proof.
  unfold bool_fun_independent in |- *.  intros.
  apply bool_fun_eq_trans with (bf2 := bool_fun_restrict bf2 x false).
  apply bool_fun_if_restrict_false.  apply H.
Qed.

Lemma bool_fun_forall_orthogonal :
 forall (x u : BDDvar) (bf1 bf2 : bool_fun),
 Neqb x u = false ->
 bool_fun_eq (bool_fun_forall u (bool_fun_if x bf1 bf2))
   (bool_fun_if x (bool_fun_forall u bf1) (bool_fun_forall u bf2)).
Proof.
  intros.  unfold bool_fun_forall at 1 in |- *.
  apply
   bool_fun_eq_trans
    with
      (bf2 := bool_fun_and
                (bool_fun_if x (bool_fun_restrict bf1 u true)
                   (bool_fun_restrict bf2 u true))
                (bool_fun_if x (bool_fun_restrict bf1 u false)
                   (bool_fun_restrict bf2 u false))).
  apply bool_fun_and_preserves_eq.  apply bool_fun_if_restrict.  assumption.
  apply bool_fun_if_restrict.  assumption.  unfold bool_fun_forall in |- *.
  apply bool_fun_and_orthogonal.
Qed.

Lemma bool_fun_independent_if :
 forall (x y : BDDvar) (bf1 bf2 : bool_fun),
 bool_fun_independent bf1 x ->
 bool_fun_independent bf2 x ->
 Neqb x y = false -> bool_fun_independent (bool_fun_if y bf1 bf2) x.
Proof.
  intros.  unfold bool_fun_independent in |- *.  intro.
  apply
   bool_fun_eq_trans
    with
      (bf2 := bool_fun_if y (bool_fun_restrict bf1 x b)
                (bool_fun_restrict bf2 x b)).
  apply bool_fun_if_restrict.  rewrite (Neqb_comm x y) in H1; assumption.
  apply bool_fun_if_preserves_eq.  apply H.  apply H0.
Qed.

Lemma bool_fun_forall_if_egal :
 forall (x : BDDvar) (bf1 bf2 : bool_fun),
 bool_fun_independent bf1 x ->
 bool_fun_independent bf2 x ->
 bool_fun_eq (bool_fun_forall x (bool_fun_if x bf1 bf2))
   (bool_fun_and bf1 bf2).
Proof.
  intros.  unfold bool_fun_forall in |- *.  apply bool_fun_and_preserves_eq.
  apply bool_fun_if_restrict_true_independent.  assumption.
  apply bool_fun_if_restrict_false_independent.  assumption.
Qed.

Lemma bool_fun_if_eq_1 :
 forall (bf1 bf2 : bool_fun) (x : BDDvar),
 bool_fun_eq bf1 bf2 -> bool_fun_eq (bool_fun_if x bf1 bf2) bf1.
Proof.
  unfold bool_fun_eq, bool_fun_if in |- *.  intros.  rewrite (H vb).  elim (vb x).
  reflexivity.  reflexivity.
Qed.

Lemma bool_fun_if_eq_2 :
 forall (bf1 bf2 : bool_fun) (x : BDDvar),
 bool_fun_eq bf1 bf2 -> bool_fun_eq (bool_fun_if x bf1 bf2) bf2.
Proof.
  unfold bool_fun_eq, bool_fun_if in |- *.  intros.  rewrite (H vb).  elim (vb x).
  reflexivity.  reflexivity.
Qed.

Lemma bool_fun_ext_zero : bool_fun_ext bool_fun_zero.
Proof.
  unfold bool_fun_ext, bool_fun_zero in |- *.  reflexivity.
Qed.

Lemma bool_fun_ext_one : bool_fun_ext bool_fun_one.
Proof.
  unfold bool_fun_ext, bool_fun_one in |- *.  reflexivity.
Qed.

Lemma bool_fun_ext_if :
 forall (bf1 bf2 : bool_fun) (x : BDDvar),
 bool_fun_ext bf1 -> bool_fun_ext bf2 -> bool_fun_ext (bool_fun_if x bf1 bf2).
Proof.
  unfold bool_fun_ext, bool_fun_if in |- *.  intros.  rewrite (H vb vb' H1).
  rewrite (H0 vb vb' H1).  rewrite (H1 x).  reflexivity.
Qed.

End Bool_fun.