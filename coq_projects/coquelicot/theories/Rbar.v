(**
This file is part of the Coquelicot formalization of real
analysis in Coq: http://coquelicot.saclay.inria.fr/

Copyright (C) 2011-2015 Sylvie Boldo
#<br />#
Copyright (C) 2011-2015 Catherine Lelay
#<br />#
Copyright (C) 2011-2015 Guillaume Melquiond

This library is free software; you can redistribute it and/or
modify it under the terms of the GNU Lesser General Public
License as published by the Free Software Foundation; either
version 3 of the License, or (at your option) any later version.

This library is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
COPYING file for more details.
*)

Require Import Reals.
Require Import mathcomp.ssreflect.ssreflect.
Require Import Rcomplements.

(** This file contains the definition and properties of the set
 [R] # &#8746; {+ &infin;} &#8746; {- &infin;} # denoted by [Rbar]. We have defined:
  - coercions from [R] to [Rbar] and vice versa ([Finite] gives [R0] at infinity points)
  - an order [Rbar_lt] and [Rbar_le]
  - total operations: [Rbar_opp], [Rbar_plus], [Rbar_minus], [Rbar_inv], [Rbar_min] and [Rbar_abs]
  - lemmas about the decidability of the order and properties of the operations (such as [Rbar_plus_comm] or [Rbar_plus_lt_compat])
 *)


Open Scope R_scope.

(** * Definitions *)

Inductive Rbar :=
  | Finite : R -> Rbar
  | p_infty : Rbar
  | m_infty : Rbar.
Definition real (x : Rbar) :=
  match x with
    | Finite x => x
    | _ => 0
  end.
Coercion Finite : R >-> Rbar.
Coercion real : Rbar >-> R.

Definition is_finite (x : Rbar) := Finite (real x) = x.
Lemma is_finite_correct (x : Rbar) :
  is_finite x <-> exists y : R, x = Finite y.
Proof.
  rewrite /is_finite ;
  case: x => /= ; split => // H.
  by exists r.
  by case: H.
  by case: H.
Qed.

(** ** Order *)

Definition Rbar_lt (x y : Rbar) : Prop :=
  match x,y with
    | p_infty, _ | _, m_infty => False
    | m_infty, _ | _, p_infty => True
    | Finite x, Finite y => Rlt x y
  end.

Definition Rbar_le (x y : Rbar) : Prop :=
  match x,y with
    | m_infty, _ | _, p_infty => True
    | p_infty, _ | _, m_infty => False
    | Finite x, Finite y => Rle x y
  end.

(** ** Operations *)
(** *** Additive operators *)

Definition Rbar_opp (x : Rbar) :=
  match x with
    | Finite x => Finite (-x)
    | p_infty => m_infty
    | m_infty => p_infty
  end.

Definition Rbar_plus' (x y : Rbar) :=
  match x,y with
    | p_infty, m_infty | m_infty, p_infty => None
    | p_infty, _ | _, p_infty => Some p_infty
    | m_infty, _ | _, m_infty => Some m_infty
    | Finite x', Finite y' => Some (Finite (x' + y'))
  end.
Definition Rbar_plus (x y : Rbar) :=
  match Rbar_plus' x y with Some z => z | None => Finite 0 end.
Arguments Rbar_plus !x !y /.
Definition is_Rbar_plus (x y z : Rbar) : Prop :=
  Rbar_plus' x y = Some z.
Definition ex_Rbar_plus (x y : Rbar) : Prop :=
  match Rbar_plus' x y with Some _ => True | None => False end.
Arguments ex_Rbar_plus !x !y /.

Lemma is_Rbar_plus_unique (x y z : Rbar) :
  is_Rbar_plus x y z -> Rbar_plus x y = z.
Proof.
  unfold is_Rbar_plus, ex_Rbar_plus, Rbar_plus.
  case: Rbar_plus' => // a Ha.
  by inversion Ha.
Qed.
Lemma Rbar_plus_correct (x y : Rbar) :
  ex_Rbar_plus x y -> is_Rbar_plus x y (Rbar_plus x y).
Proof.
  unfold is_Rbar_plus, ex_Rbar_plus, Rbar_plus.
  by case: Rbar_plus'.
Qed.

Definition Rbar_minus (x y : Rbar) := Rbar_plus x (Rbar_opp y).
Arguments Rbar_minus !x !y /.
Definition is_Rbar_minus (x y z : Rbar) : Prop :=
  is_Rbar_plus x (Rbar_opp y) z.
Definition ex_Rbar_minus (x y : Rbar) : Prop :=
  ex_Rbar_plus x (Rbar_opp y).
Arguments ex_Rbar_minus !x !y /.

(** *** Multiplicative operators *)

Definition Rbar_inv (x : Rbar) : Rbar :=
  match x with
    | Finite x => Finite (/x)
    | _ => Finite 0
  end.

Definition Rbar_mult' (x y : Rbar) :=
  match x with
    | Finite x => match y with
      | Finite y => Some (Finite (x * y))
      | p_infty => match (Rle_dec 0 x) with
        | left H => match Rle_lt_or_eq_dec _ _ H with left _ => Some p_infty | right _ => None end
        | right _ => Some m_infty
      end
      | m_infty => match (Rle_dec 0 x) with
        | left H => match Rle_lt_or_eq_dec _ _ H with left _ => Some m_infty | right _ => None end
        | right _ => Some p_infty
      end
    end
    | p_infty => match y with
      | Finite y => match (Rle_dec 0 y) with
        | left H => match Rle_lt_or_eq_dec _ _ H with left _ => Some p_infty | right _ => None end
        | right _ => Some m_infty
      end
      | p_infty => Some p_infty
      | m_infty => Some m_infty
    end
    | m_infty => match y with
      | Finite y => match (Rle_dec 0 y) with
        | left H => match Rle_lt_or_eq_dec _ _ H with left _ => Some m_infty | right _ => None end
        | right _ => Some p_infty
      end
      | p_infty => Some m_infty
      | m_infty => Some p_infty
    end
  end.
Definition Rbar_mult (x y : Rbar) :=
  match Rbar_mult' x y with Some z => z | None => Finite 0 end.
Arguments Rbar_mult !x !y /.

Definition is_Rbar_mult (x y z : Rbar) : Prop :=
  Rbar_mult' x y = Some z.
Definition ex_Rbar_mult (x y : Rbar) : Prop :=
  match x with
    | Finite x => match y with
      | Finite y => True
      | p_infty => x <> 0
      | m_infty => x <> 0
    end
    | p_infty => match y with
      | Finite y => y <> 0
      | p_infty => True
      | m_infty => True
    end
    | m_infty => match y with
      | Finite y => y <> 0
      | p_infty => True
      | m_infty => True
    end
  end.
Arguments ex_Rbar_mult !x !y /.

Definition Rbar_mult_pos (x : Rbar) (y : posreal) :=
  match x with
    | Finite x => Finite (x*y)
    | _ => x
  end.

Lemma is_Rbar_mult_unique (x y z : Rbar) :
  is_Rbar_mult x y z -> Rbar_mult x y = z.
Proof.
  unfold is_Rbar_mult ;
  case: x => [x | | ] ;
  case: y => [y | | ] ;
  case: z => [z | | ] //= H ;
  inversion H => // ;
  case: Rle_dec H => // H0 ;
  case: Rle_lt_or_eq_dec => //.
Qed.
Lemma Rbar_mult_correct (x y : Rbar) :
  ex_Rbar_mult x y -> is_Rbar_mult x y (Rbar_mult x y).
Proof.
  case: x => [x | | ] ;
  case: y => [y | | ] //= H ;
  apply sym_not_eq in H ;
  unfold is_Rbar_mult ; simpl ;
  case: Rle_dec => // H0 ;
  case: Rle_lt_or_eq_dec => //.
Qed.
Lemma Rbar_mult_correct' (x y z : Rbar) :
  is_Rbar_mult x y z -> ex_Rbar_mult x y.
Proof.
  unfold is_Rbar_mult ;
  case: x => [x | | ] ;
  case: y => [y | | ] //= ;
  case: Rle_dec => //= H ; try (case: Rle_lt_or_eq_dec => //=) ; intros.
  by apply Rgt_not_eq.
  by apply Rlt_not_eq, Rnot_le_lt.
  by apply Rgt_not_eq.
  by apply Rlt_not_eq, Rnot_le_lt.
  by apply Rgt_not_eq.
  by apply Rlt_not_eq, Rnot_le_lt.
  by apply Rgt_not_eq.
  by apply Rlt_not_eq, Rnot_le_lt.
Qed.


Definition Rbar_div (x y : Rbar) : Rbar :=
  Rbar_mult x (Rbar_inv y).
Arguments Rbar_div !x !y /.
Definition is_Rbar_div (x y z : Rbar) : Prop :=
  is_Rbar_mult x (Rbar_inv y) z.
Definition ex_Rbar_div (x y : Rbar) : Prop :=
  ex_Rbar_mult x (Rbar_inv y).
Arguments ex_Rbar_div !x !y /.
Definition Rbar_div_pos (x : Rbar) (y : posreal) :=
  match x with
    | Finite x => Finite (x/y)
    | _ => x
  end.

(** * Compatibility with real numbers *)
(** For equality and order.
The compatibility of addition and multiplication is proved in Rbar_seq *)

Lemma Rbar_finite_eq (x y : R) :
  Finite x = Finite y <-> x = y.
Proof.
  split ; intros.
  apply Rle_antisym ; apply Rnot_lt_le ; intro.
  assert (Rbar_lt (Finite y) (Finite x)).
  simpl ; apply H0.
  rewrite H in H1 ; simpl in H1 ; by apply Rlt_irrefl in H1.
  assert (Rbar_lt (Finite x) (Finite y)).
  simpl ; apply H0.
  rewrite H in H1 ; simpl in H1 ; by apply Rlt_irrefl in H1.
  rewrite H ; reflexivity.
Qed.
Lemma Rbar_finite_neq (x y : R) :
  Finite x <> Finite y <-> x <> y.
Proof.
  split => H ; contradict H ; by apply Rbar_finite_eq.
Qed.

(** * Properties of order *)

(** ** Relations between inequalities *)

Lemma Rbar_lt_not_eq (x y : Rbar) :
  Rbar_lt x y -> x<>y.
Proof.
  destruct x ; destruct y ; simpl ; try easy.
  intros H H0.
  apply Rbar_finite_eq in H0 ; revert H0 ; apply Rlt_not_eq, H.
Qed.

Lemma Rbar_not_le_lt (x y : Rbar) :
  ~ Rbar_le x y -> Rbar_lt y x.
Proof.
  destruct x ; destruct y ; simpl ; intuition.
Qed.

Lemma Rbar_lt_not_le (x y : Rbar) :
  Rbar_lt y x -> ~ Rbar_le x y.
Proof.
  destruct x ; destruct y ; simpl ; intuition.
  apply (Rlt_irrefl r0).
  now apply Rlt_le_trans with (1 := H).
Qed.

Lemma Rbar_not_lt_le (x y : Rbar) :
  ~ Rbar_lt x y -> Rbar_le y x.
Proof.
  destruct x ; destruct y ; simpl ; intuition.
  now apply Rnot_lt_le.
Qed.

Lemma Rbar_le_not_lt (x y : Rbar) :
  Rbar_le y x -> ~ Rbar_lt x y.
Proof.
  destruct x ; destruct y ; simpl ; intuition ; contradict H0.
  now apply Rle_not_lt.
Qed.

Lemma Rbar_le_refl :
  forall x : Rbar, Rbar_le x x.
Proof.
intros [x| |] ; try easy.
apply Rle_refl.
Qed.

Lemma Rbar_lt_le :
  forall x y : Rbar,
  Rbar_lt x y -> Rbar_le x y.
Proof.
  intros [x| |] [y| |] ; try easy.
  apply Rlt_le.
Qed.

(** ** Decidability *)

Lemma Rbar_total_order (x y : Rbar) :
  {Rbar_lt x y} + {x = y} + {Rbar_lt y x}.
Proof.
  destruct x ; destruct y ; simpl ; intuition.
  destruct (total_order_T r r0) ; intuition.
Qed.

Lemma Rbar_eq_dec (x y : Rbar) :
  {x = y} + {x <> y}.
Proof.
  intros ; destruct (Rbar_total_order x y) as [[H|H]|H].
  right ; revert H ; destruct x as [x| |] ; destruct y as [y| |] ; simpl ; intros H ;
  try easy.
  contradict H.
  apply Rbar_finite_eq in H ; try apply Rle_not_lt, Req_le ; auto.
  left ; apply H.
  right ; revert H ; destruct x as [x| |] ; destruct y as [y| |] ; simpl ; intros H ;
  try easy.
  contradict H.
  apply Rbar_finite_eq in H ; apply Rle_not_lt, Req_le ; auto.
Qed.

Lemma Rbar_lt_dec (x y : Rbar) :
  {Rbar_lt x y} + {~Rbar_lt x y}.
Proof.
  destruct (Rbar_total_order x y) as [H|H] ; [ destruct H as [H|H]|].
  now left.
  right ; rewrite H ; clear H ; destruct y ; auto ; apply Rlt_irrefl ; auto.
  right ; revert H ; destruct x as [x | | ] ; destruct y as [y | | ] ; intros H ; auto ;
  apply Rle_not_lt, Rlt_le ; auto.
Qed.

Lemma Rbar_lt_le_dec (x y : Rbar) :
  {Rbar_lt x y} + {Rbar_le y x}.
Proof.
  destruct (Rbar_total_order x y) as [[H|H]|H].
  now left.
  right.
  rewrite H.
  apply Rbar_le_refl.
  right.
  now apply Rbar_lt_le.
Qed.

Lemma Rbar_le_dec (x y : Rbar) :
  {Rbar_le x y} + {~Rbar_le x y}.
Proof.
  destruct (Rbar_total_order x y) as [[H|H]|H].
  left.
  now apply Rbar_lt_le.
  left.
  rewrite H.
  apply Rbar_le_refl.
  right.
  now apply Rbar_lt_not_le.
Qed.

Lemma Rbar_le_lt_dec (x y : Rbar) :
  {Rbar_le x y} + {Rbar_lt y x}.
Proof.
  destruct (Rbar_total_order x y) as [[H|H]|H].
  left.
  now apply Rbar_lt_le.
  left.
  rewrite H.
  apply Rbar_le_refl.
  now right.
Qed.

Lemma Rbar_le_lt_or_eq_dec (x y : Rbar) :
  Rbar_le x y -> { Rbar_lt x y } + { x = y }.
Proof.
  destruct (Rbar_total_order x y) as [[H|H]|H].
  now left.
  now right.
  intros K.
  now elim (Rbar_le_not_lt _ _ K).
Qed.

(** ** Transitivity *)

Lemma Rbar_lt_trans (x y z : Rbar) :
  Rbar_lt x y -> Rbar_lt y z -> Rbar_lt x z.
Proof.
  destruct x ; destruct y ; destruct z ; simpl ; intuition.
  now apply Rlt_trans with r0.
Qed.

Lemma Rbar_lt_le_trans (x y z : Rbar) :
  Rbar_lt x y -> Rbar_le y z -> Rbar_lt x z.
Proof.
  destruct x ; destruct y ; destruct z ; simpl ; intuition.
  now apply Rlt_le_trans with r0.
Qed.

Lemma Rbar_le_lt_trans (x y z : Rbar) :
  Rbar_le x y -> Rbar_lt y z -> Rbar_lt x z.
Proof.
  destruct x ; destruct y ; destruct z ; simpl ; intuition.
  now apply Rle_lt_trans with r0.
Qed.

Lemma Rbar_le_trans (x y z : Rbar) :
  Rbar_le x y -> Rbar_le y z -> Rbar_le x z.
Proof.
  destruct x ; destruct y ; destruct z ; simpl ; intuition.
  now apply Rle_trans with r0.
Qed.

Lemma Rbar_le_antisym (x y : Rbar) :
  Rbar_le x y -> Rbar_le y x -> x = y.
Proof.
  destruct x ; destruct y ; simpl ; intuition.
Qed.

(** * Properties of operations *)
(** ** Additive operators *)
(** *** Rbar_opp *)

Lemma Rbar_opp_involutive (x : Rbar) : (Rbar_opp (Rbar_opp x)) = x.
Proof.
  destruct x as [x| | ] ; auto ; simpl ; rewrite Ropp_involutive ; auto.
Qed.

Lemma Rbar_opp_lt (x y : Rbar) : Rbar_lt (Rbar_opp x) (Rbar_opp y) <-> Rbar_lt y x.
Proof.
  destruct x as [x | | ] ; destruct y as [y | | ] ;
  split ; auto ; intro H ; simpl ; try left.
  apply Ropp_lt_cancel ; auto.
  apply Ropp_lt_contravar ; auto.
Qed.

Lemma Rbar_opp_le (x y : Rbar) : Rbar_le (Rbar_opp x) (Rbar_opp y) <-> Rbar_le y x.
Proof.
  destruct x as [x| |] ; destruct y as [y| |] ; simpl ; intuition.
Qed.

Lemma Rbar_opp_eq (x y : Rbar) : (Rbar_opp x) = (Rbar_opp y) <-> x = y.
Proof.
  split ; intros H.
  rewrite <- (Rbar_opp_involutive x), H, Rbar_opp_involutive ; reflexivity.
  rewrite H ; reflexivity.
Qed.

Lemma Rbar_opp_real (x : Rbar) : real (Rbar_opp x) = - real x.
Proof.
  destruct x as [x | | ] ; simpl ; intuition.
Qed.

(** *** Rbar_plus *)

Lemma Rbar_plus'_comm :
  forall x y, Rbar_plus' x y = Rbar_plus' y x.
Proof.
intros [x| |] [y| |] ; try reflexivity.
apply (f_equal (fun x => Some (Finite x))), Rplus_comm.
Qed.

Lemma ex_Rbar_plus_comm :
  forall x y,
  ex_Rbar_plus x y -> ex_Rbar_plus y x.
Proof.
now intros [x| |] [y| |].
Qed.

Lemma ex_Rbar_plus_opp (x y : Rbar) :
  ex_Rbar_plus x y -> ex_Rbar_plus (Rbar_opp x) (Rbar_opp y).
Proof.
  case: x => [x | | ] ;
  case: y => [y | | ] => //.
Qed.

Lemma Rbar_plus_0_r (x : Rbar) : Rbar_plus x (Finite 0) = x.
Proof.
  case: x => //= ; intuition.
Qed.
Lemma Rbar_plus_0_l (x : Rbar) : Rbar_plus (Finite 0) x = x.
Proof.
  case: x => //= ; intuition.
Qed.

Lemma Rbar_plus_comm (x y : Rbar) : Rbar_plus x y = Rbar_plus y x.
Proof.
  case x ; case y ; intuition.
  simpl.
  apply f_equal, Rplus_comm.
Qed.

Lemma Rbar_plus_lt_compat (a b c d : Rbar) :
  Rbar_lt a b -> Rbar_lt c d -> Rbar_lt (Rbar_plus a c) (Rbar_plus b d).
Proof.
  case: a => [a | | ] // ; case: b => [b | | ] // ;
  case: c => [c | | ] // ; case: d => [d | | ] // ;
  apply Rplus_lt_compat.
Qed.

Lemma Rbar_plus_le_compat (a b c d : Rbar) :
  Rbar_le a b -> Rbar_le c d -> Rbar_le (Rbar_plus a c) (Rbar_plus b d).
Proof.
  case: a => [a | | ] // ; case: b => [b | | ] // ;
  case: c => [c | | ] // ; case: d => [d | | ] //.
  apply Rplus_le_compat.
  intros _ _.
  apply Rle_refl.
  intros _ _.
  apply Rle_refl.
Qed.

Lemma Rbar_plus_opp (x y : Rbar) :
  Rbar_plus (Rbar_opp x) (Rbar_opp y) = Rbar_opp (Rbar_plus x y).
Proof.
  case: x => [x | | ] ;
  case: y => [y | | ] //= ; apply f_equal ; ring.
Qed.

(** *** Rbar_minus *)

Lemma Rbar_minus_eq_0 (x : Rbar) : Rbar_minus x x = 0.
Proof.
  case: x => //= x ; by apply f_equal, Rcomplements.Rminus_eq_0.
Qed.
Lemma Rbar_opp_minus (x y : Rbar) :
  Rbar_opp (Rbar_minus x y) = Rbar_minus y x.
Proof.
  case: x => [x | | ] ;
  case: y => [y | | ] //=.
  by rewrite Ropp_minus_distr'.
  by rewrite Ropp_0.
  by rewrite Ropp_0.
Qed.

(** ** Multiplicative *)

(** *** Rbar_inv *)

Lemma Rbar_inv_opp (x : Rbar) :
  x <> 0 -> Rbar_inv (Rbar_opp x) = Rbar_opp (Rbar_inv x).
Proof.
  case: x => [x | | ] /= Hx.
  rewrite Ropp_inv_permute => //.
  contradict Hx.
  by rewrite Hx.
  by rewrite Ropp_0.
  by rewrite Ropp_0.
Qed.

(** *** Rbar_mult *)

Lemma Rbar_mult'_comm (x y : Rbar) :
  Rbar_mult' x y = Rbar_mult' y x.
Proof.
  case: x => [x | | ] ;
  case: y => [y | | ] //=.
  by rewrite Rmult_comm.
Qed.

Lemma Rbar_mult'_opp_r (x y : Rbar) :
  Rbar_mult' x (Rbar_opp y) = match Rbar_mult' x y with Some z => Some (Rbar_opp z) | None => None end.
Proof.
  case: x => [x | | ] ;
  case: y => [y | | ] //= ;
  (try case: Rle_dec => Hx //=) ;
  (try case: Rle_lt_or_eq_dec => //= Hx0).
  by rewrite Ropp_mult_distr_r_reverse.
  rewrite -Ropp_0 in Hx0.
  apply Ropp_lt_cancel in Hx0.
  case Rle_dec => Hy //=.
  now elim Rle_not_lt with (1 := Hy).
  case Rle_dec => Hy //=.
  case Rle_lt_or_eq_dec => Hy0 //=.
  elim Rlt_not_le with (1 := Hy0).
  apply Ropp_le_cancel.
  by rewrite Ropp_0.
  elim Hy.
  apply Ropp_le_cancel.
  rewrite -Hx0 Ropp_0.
  apply Rle_refl.
  case Rle_dec => Hy //=.
  case Rle_lt_or_eq_dec => Hy0 //=.
  elim Hx.
  rewrite -Hy0 Ropp_0.
  apply Rle_refl.
  elim Hx.
  rewrite -Ropp_0.
  apply Ropp_le_contravar.
  apply Rlt_le.
  now apply Rnot_le_lt.
  case Rle_dec => Hy //=.
  elim Rlt_not_le with (1 := Hx0).
  rewrite -Ropp_0.
  now apply Ropp_le_contravar.
  case Rle_dec => Hy //=.
  case Rle_lt_or_eq_dec => Hy0 //=.
  elim Rlt_not_le with (1 := Hy0).
  apply Ropp_le_cancel.
  rewrite -Hx0 Ropp_0.
  apply Rle_refl.
  elim Hy.
  apply Ropp_le_cancel.
  rewrite -Hx0 Ropp_0.
  apply Rle_refl.
  case Rle_dec => Hy //=.
  case Rle_lt_or_eq_dec => Hy0 //=.
  elim Hx.
  rewrite -Hy0 Ropp_0.
  apply Rle_refl.
  elim Hx.
  rewrite -Ropp_0.
  apply Ropp_le_contravar.
  apply Rlt_le.
  now apply Rnot_le_lt.
Qed.

Lemma Rbar_mult_comm (x y : Rbar) :
  Rbar_mult x y = Rbar_mult y x.
Proof.
  unfold Rbar_mult.
  by rewrite Rbar_mult'_comm.
Qed.
Lemma Rbar_mult_opp_r (x y : Rbar) :
  Rbar_mult x (Rbar_opp y) = (Rbar_opp (Rbar_mult x y)).
Proof.
  unfold Rbar_mult.
  rewrite Rbar_mult'_opp_r.
  case Rbar_mult' => //=.
  apply f_equal, eq_sym, Ropp_0.
Qed.
Lemma Rbar_mult_opp_l (x y : Rbar) :
  Rbar_mult (Rbar_opp x) y = Rbar_opp (Rbar_mult x y).
Proof.
  rewrite ?(Rbar_mult_comm _ y).
  by apply Rbar_mult_opp_r.
Qed.
Lemma Rbar_mult_opp (x y : Rbar) :
  Rbar_mult (Rbar_opp x) (Rbar_opp y) = Rbar_mult x y.
Proof.
  by rewrite Rbar_mult_opp_l -Rbar_mult_opp_r Rbar_opp_involutive.
Qed.
Lemma Rbar_mult_0_l (x : Rbar) : Rbar_mult 0 x = 0.
Proof.
  case: x => [x | | ] //=.
  by rewrite Rmult_0_l.
  case: Rle_dec (Rle_refl 0) => // H _.
  case: Rle_lt_or_eq_dec (Rlt_irrefl 0) => // _ _.
  case: Rle_dec (Rle_refl 0) => // H _.
  case: Rle_lt_or_eq_dec (Rlt_irrefl 0) => // _ _.
Qed.
Lemma Rbar_mult_0_r (x : Rbar) : Rbar_mult x 0 = 0.
Proof.
  rewrite Rbar_mult_comm ; by apply Rbar_mult_0_l.
Qed.

Lemma Rbar_mult_eq_0 (y x : Rbar) :
  Rbar_mult x y = 0 -> x = 0 \/ y = 0.
Proof.
  case: x => [x | | ] //= ;
  case: y => [y | | ] //= ;
  (try case: Rle_dec => //= H) ;
  (try case: Rle_lt_or_eq_dec => //=) ;
  (try (left ; by apply f_equal)) ;
  (try (right ; by apply f_equal)).
  intros H.
  apply (f_equal real) in H.
  simpl in H.
  apply Rmult_integral in H ; case: H => ->.
  by left.
  by right.
Qed.

Lemma ex_Rbar_mult_sym (x y : Rbar) :
  ex_Rbar_mult x y -> ex_Rbar_mult y x.
Proof.
  case: x => [x | | ] ;
  case: y => [y | | ] //.
Qed.
Lemma ex_Rbar_mult_opp_l (x y : Rbar) :
  ex_Rbar_mult x y -> ex_Rbar_mult (Rbar_opp x) y.
Proof.
  case: x => [x | | ] ;
  case: y => [y | | ] //= Hx ;
  by apply Ropp_neq_0_compat.
Qed.
Lemma ex_Rbar_mult_opp_r (x y : Rbar) :
  ex_Rbar_mult x y -> ex_Rbar_mult x (Rbar_opp y).
Proof.
  case: x => [x | | ] ;
  case: y => [y | | ] //= Hx ;
  by apply Ropp_neq_0_compat.
Qed.

Lemma is_Rbar_mult_sym (x y z : Rbar) :
  is_Rbar_mult x y z -> is_Rbar_mult y x z.
Proof.
  case: x => [x | | ] ;
  case: y => [y | | ] ;
  case: z => [z | | ] //= ;
  unfold is_Rbar_mult, Rbar_mult' ;
  try (case: Rle_dec => // H) ;
  try (case: Rle_lt_or_eq_dec => // H0) ;
  try (case => <-) ; try (move => _).
  by rewrite Rmult_comm.
Qed.
Lemma is_Rbar_mult_opp_l (x y z : Rbar) :
  is_Rbar_mult x y z -> is_Rbar_mult (Rbar_opp x) y (Rbar_opp z).
Proof.
  case: x => [x | | ] ;
  case: y => [y | | ] ;
  case: z => [z | | ] //= ;
  unfold is_Rbar_mult, Rbar_mult' ;
  try (case: Rle_dec => // H) ;
  try (case: Rle_lt_or_eq_dec => // H0) ;
  try (case => <-) ; try (move => _).
  apply (f_equal (@Some _)), f_equal ; ring.
  apply Ropp_lt_contravar in H0 ; rewrite Ropp_0 in H0 ;
  now move/Rlt_not_le: H0 ; case: Rle_dec.
  apply Rnot_le_lt, Ropp_lt_contravar in H ; rewrite Ropp_0 in H ;
  move/Rlt_le: (H) ; case: Rle_dec => // H0 _ ;
  now move/Rlt_not_eq: H ; case: Rle_lt_or_eq_dec.
  apply Rnot_le_lt, Ropp_lt_contravar in H ; rewrite Ropp_0 in H ;
  move/Rlt_le: (H) ; case: Rle_dec => // H0 _ ;
  now move/Rlt_not_eq: H ; case: Rle_lt_or_eq_dec.
  apply Ropp_lt_contravar in H0 ; rewrite Ropp_0 in H0 ;
  now move/Rlt_not_le: H0 ; case: Rle_dec.
Qed.
Lemma is_Rbar_mult_opp_r (x y z : Rbar) :
  is_Rbar_mult x y z -> is_Rbar_mult x (Rbar_opp y) (Rbar_opp z).
Proof.
  move/is_Rbar_mult_sym => H.
  now apply is_Rbar_mult_sym, is_Rbar_mult_opp_l.
Qed.

Lemma is_Rbar_mult_p_infty_pos (x : Rbar) :
  Rbar_lt 0 x -> is_Rbar_mult p_infty x p_infty.
Proof.
  case: x => [x | | ] // Hx.
  unfold is_Rbar_mult, Rbar_mult'.
  case: Rle_dec (Rlt_le _ _ Hx) => // Hx' _.
  now case: Rle_lt_or_eq_dec (Rlt_not_eq _ _ Hx).
Qed.
Lemma is_Rbar_mult_p_infty_neg (x : Rbar) :
  Rbar_lt x 0 -> is_Rbar_mult p_infty x m_infty.
Proof.
  case: x => [x | | ] // Hx.
  unfold is_Rbar_mult, Rbar_mult'.
  case: Rle_dec (Rlt_not_le _ _ Hx) => // Hx' _.
Qed.
Lemma is_Rbar_mult_m_infty_pos (x : Rbar) :
  Rbar_lt 0 x -> is_Rbar_mult m_infty x m_infty.
Proof.
  case: x => [x | | ] // Hx.
  unfold is_Rbar_mult, Rbar_mult'.
  case: Rle_dec (Rlt_le _ _ Hx) => // Hx' _.
  now case: Rle_lt_or_eq_dec (Rlt_not_eq _ _ Hx).
Qed.
Lemma is_Rbar_mult_m_infty_neg (x : Rbar) :
  Rbar_lt x 0 -> is_Rbar_mult m_infty x p_infty.
Proof.
  case: x => [x | | ] // Hx.
  unfold is_Rbar_mult, Rbar_mult'.
  case: Rle_dec (Rlt_not_le _ _ Hx) => // Hx' _.
Qed.

(** Rbar_div *)

Lemma is_Rbar_div_p_infty (x : R) :
  is_Rbar_div x p_infty 0.
Proof.
  apply (f_equal (@Some _)).
  by rewrite Rmult_0_r.
Qed.
Lemma is_Rbar_div_m_infty (x : R) :
  is_Rbar_div x m_infty 0.
Proof.
  apply (f_equal (@Some _)).
  by rewrite Rmult_0_r.
Qed.

(** Rbar_mult_pos *)

Lemma Rbar_mult_pos_eq (x y : Rbar) (z : posreal) :
  x = y <-> (Rbar_mult_pos x z) = (Rbar_mult_pos y z).
Proof.
  case: z => z Hz ; case: x => [x | | ] ; case: y => [y | | ] ;
  split => //= H ; apply Rbar_finite_eq in H.
  by rewrite H.
  apply Rbar_finite_eq, (Rmult_eq_reg_r (z)) => // ;
  by apply Rgt_not_eq.
Qed.

Lemma Rbar_mult_pos_lt (x y : Rbar) (z : posreal) :
  Rbar_lt x y <-> Rbar_lt (Rbar_mult_pos x z) (Rbar_mult_pos y z).
Proof.
  case: z => z Hz ; case: x => [x | | ] ; case: y => [y | | ] ;
  split => //= H.
  apply (Rmult_lt_compat_r (z)) => //.
  apply (Rmult_lt_reg_r (z)) => //.
Qed.

Lemma Rbar_mult_pos_le (x y : Rbar) (z : posreal) :
  Rbar_le x y <-> Rbar_le (Rbar_mult_pos x z) (Rbar_mult_pos y z).
Proof.
  case: z => z Hz ; case: x => [x | | ] ; case: y => [y | | ] ;
  split => //= H.
  apply Rmult_le_compat_r with (2 := H).
  now apply Rlt_le.
  now apply Rmult_le_reg_r with (2 := H).
Qed.

(** Rbar_div_pos *)

Lemma Rbar_div_pos_eq (x y : Rbar) (z : posreal) :
  x = y <-> (Rbar_div_pos x z) = (Rbar_div_pos y z).
Proof.
  case: z => z Hz ; case: x => [x | | ] ; case: y => [y | | ] ;
  split => //= H ; apply Rbar_finite_eq in H.
  by rewrite H.
  apply Rbar_finite_eq, (Rmult_eq_reg_r (/z)) => // ;
  by apply Rgt_not_eq, Rinv_0_lt_compat.
Qed.

Lemma Rbar_div_pos_lt (x y : Rbar) (z : posreal) :
  Rbar_lt x y <-> Rbar_lt (Rbar_div_pos x z) (Rbar_div_pos y z).
Proof.
  case: z => z Hz ; case: x => [x | | ] ; case: y => [y | | ] ;
  split => //= H.
  apply (Rmult_lt_compat_r (/z)) => // ; by apply Rinv_0_lt_compat.
  apply (Rmult_lt_reg_r (/z)) => // ; by apply Rinv_0_lt_compat.
Qed.

Lemma Rbar_div_pos_le (x y : Rbar) (z : posreal) :
  Rbar_le x y <-> Rbar_le (Rbar_div_pos x z) (Rbar_div_pos y z).
Proof.
  case: z => z Hz ; case: x => [x | | ] ; case: y => [y | | ] ;
  split => //= H.
  apply Rmult_le_compat_r with (2 := H).
  now apply Rlt_le, Rinv_0_lt_compat.
  apply Rmult_le_reg_r with (2 := H).
  now apply Rinv_0_lt_compat.
Qed.

(** * Rbar_min *)

Definition Rbar_min (x y : Rbar) : Rbar :=
  match x, y with
  | z, p_infty | p_infty, z => z
  | _ , m_infty | m_infty, _ => m_infty
  | Finite x, Finite y => Rmin x y
  end.

Lemma Rbar_lt_locally (a b : Rbar) (x : R) :
  Rbar_lt a x -> Rbar_lt x b ->
  exists delta : posreal,
    forall y, Rabs (y - x) < delta -> Rbar_lt a y /\ Rbar_lt y b.
Proof.
  case: a => [ a /= Ha | | _ ] //= ; (try apply Rminus_lt_0 in Ha) ;
  case: b => [ b Hb | _ | ] //= ; (try apply Rminus_lt_0 in Hb).
  assert (0 < Rmin (x - a) (b - x)).
    by apply Rmin_case.
  exists (mkposreal _ H) => y /= Hy ; split.
  apply Rplus_lt_reg_r with (-x).
  replace (a+-x) with (-(x-a)) by ring.
  apply (Rabs_lt_between (y - x)).
  apply Rlt_le_trans with (1 := Hy).
  by apply Rmin_l.
  apply Rplus_lt_reg_r with (-x).
  apply (Rabs_lt_between (y - x)).
  apply Rlt_le_trans with (1 := Hy).
  by apply Rmin_r.
  exists (mkposreal _ Ha) => y /= Hy ; split => //.
  apply Rplus_lt_reg_r with (-x).
  replace (a+-x) with (-(x-a)) by ring.
  by apply (Rabs_lt_between (y - x)).
  exists (mkposreal _ Hb) => y /= Hy ; split => //.
  apply Rplus_lt_reg_r with (-x).
  by apply (Rabs_lt_between (y - x)).
  exists (mkposreal _ Rlt_0_1) ; by split.
Qed.

Lemma Rbar_min_comm (x y : Rbar) : Rbar_min x y = Rbar_min y x.
Proof.
  case: x => [x | | ] //= ;
  case: y => [y | | ] //=.
  by rewrite Rmin_comm.
Qed.

Lemma Rbar_min_r (x y : Rbar) : Rbar_le (Rbar_min x y) y.
Proof.
  case: x => [x | | ] //= ;
  case: y => [y | | ] //=.
  by apply Rmin_r.
  by apply Rle_refl.
Qed.

Lemma Rbar_min_l (x y : Rbar) : Rbar_le (Rbar_min x y) x.
Proof.
  rewrite Rbar_min_comm.
  by apply Rbar_min_r.
Qed.

Lemma Rbar_min_case (x y : Rbar) (P : Rbar -> Type) :
  P x -> P y -> P (Rbar_min x y).
Proof.
  case: x => [x | | ] //= ;
  case: y => [y | | ] //=.
  by apply Rmin_case.
Qed.
Lemma Rbar_min_case_strong (r1 r2 : Rbar) (P : Rbar -> Type) :
  (Rbar_le r1 r2 -> P r1) -> (Rbar_le r2 r1 -> P r2)
    -> P (Rbar_min r1 r2).
Proof.
  case: r1 => [x | | ] //= ;
  case: r2 => [y | | ] //= Hx Hy ;
  (try by apply Hx) ; (try by apply Hy).
  by apply Rmin_case_strong.
Qed.

(** * Rbar_abs *)

Definition Rbar_abs (x : Rbar) :=
  match x with
    | Finite x => Finite (Rabs x)
    | _ => p_infty
  end.

Lemma Rbar_abs_lt_between (x y : Rbar) :
  Rbar_lt (Rbar_abs x) y <-> (Rbar_lt (Rbar_opp y) x /\ Rbar_lt x y).
Proof.
  case: x => [x | | ] ; case: y => [y | | ] /= ; try by intuition.
  by apply Rabs_lt_between.
Qed.

Lemma Rbar_abs_opp (x : Rbar) :
  Rbar_abs (Rbar_opp x) = Rbar_abs x.
Proof.
  case: x => [x | | ] //=.
  by rewrite Rabs_Ropp.
Qed.

Lemma Rbar_abs_pos (x : Rbar) :
  Rbar_le 0 x -> Rbar_abs x = x.
Proof.
  case: x => [x | | ] //= Hx.
  by apply f_equal, Rabs_pos_eq.
Qed.
Lemma Rbar_abs_neg (x : Rbar) :
  Rbar_le x 0 -> Rbar_abs x = Rbar_opp x.
Proof.
  case: x => [x | | ] //= Hx.
  rewrite -Rabs_Ropp.
  apply f_equal, Rabs_pos_eq.
  now rewrite -Ropp_0 ; apply Ropp_le_contravar.
Qed.
