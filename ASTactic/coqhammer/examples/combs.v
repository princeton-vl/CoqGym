(*

This file showcases some tactics available in Hammer.Reconstr.

Author: Lukasz Czajka

*)

From Hammer Require Import Hammer Reconstr.

Require Import PeanoNat.
Require Import Omega.

Inductive Term : Set :=
| LS : Term
| LK : Term
| LI : Term
| LVar : nat -> Term
| LApp : Term -> Term -> Term
| LLam : nat -> Term -> Term.

Fixpoint size (t : Term) : nat :=
  match t with
    | LS | LK | LVar _ => 1
    | LI => 2
    | LApp x y => size x + size y + 1
    | LLam _ x => size x + 1
  end.

Fixpoint abstr (v : nat) (t : Term) : Term :=
  match t with
    | LS | LK | LI => LApp LK t
    | LVar n => if n =? v then LI else LApp LK t
    | LApp x y => LApp (LApp LS (abstr v x)) (abstr v y)
    | LLam _ _ => t
  end.

Fixpoint transl (t : Term) : Term :=
  match t with
    | LS | LK | LI | LVar _ => t
    | LApp x y => LApp (transl x) (transl y)
    | LLam v x => abstr v (transl x)
  end.

(* variable-capturing substitution *)
Fixpoint csubst (t : Term) (v : nat) (s : Term) : Term :=
  match t with
    | LS | LK | LI => t
    | LVar n => if n =? v then s else t
    | LApp x y => LApp (csubst x v s) (csubst y v s)
    | LLam u x => LLam u (csubst x v s)
  end.

Inductive NoLambdas : Term -> Prop :=
| nl_s : NoLambdas LS
| nl_k : NoLambdas LK
| nl_i : NoLambdas LI
| nl_var : forall n : nat, NoLambdas (LVar n)
| nl_app : forall x y : Term, NoLambdas x -> NoLambdas y -> NoLambdas (LApp x y).

Ltac pose_nolams := generalize nl_s nl_k nl_i nl_var nl_app; intros.

Lemma no_lams_abstr : forall (v : nat) (t : Term), NoLambdas t -> NoLambdas (abstr v t).
Proof.
  pose_nolams.
  induction t; yelles 2.
Qed.

Lemma no_lams_transl : forall t : Term, NoLambdas (transl t).
Proof.
  pose proof no_lams_abstr.
  pose_nolams.
  induction t; yelles 2.
Qed.

Inductive HasVar : nat -> Term -> Prop :=
| hs_var : forall n : nat, HasVar n (LVar n)
| hs_app : forall (n : nat) (x y : Term), HasVar n x \/ HasVar n y -> HasVar n (LApp x y)
| hs_lem : forall (n v : nat) (x : Term), n <> v -> HasVar n x -> HasVar n (LLam v x).

Ltac pose_hasvar := generalize hs_var hs_app hs_lem; intros.

Lemma vars_abstr :
  forall (t : Term) (n v : nat), n <> v -> (HasVar n t <-> HasVar n (abstr v t)).
Proof.
  pose_hasvar.
  induction t; sauto.
  Reconstr.reasy (@Coq.Arith.EqNat.beq_nat_true) Reconstr.Empty.
Qed.

Lemma novar_abstr : forall (v : nat) (t : Term), NoLambdas t -> ~(HasVar v (abstr v t)).
Proof.
  pose_hasvar.
  induction t; sauto.
  Reconstr.reasy (@Coq.Arith.PeanoNat.Nat.eqb_refl, @Coq.Bool.Bool.not_true_iff_false) Reconstr.Empty.
Qed.

Lemma vars_transl : forall (t : Term) (n : nat), HasVar n t <-> HasVar n (transl t).
Proof.
  pose_hasvar.
  induction t; sauto.
  - Reconstr.reasy (@vars_abstr) Reconstr.Empty.
  - Reconstr.rsimple (@hs_lem, @vars_abstr, @novar_abstr, @no_lams_transl) Reconstr.Empty.
Qed.

Notation "X @ Y" := (LApp X Y) (at level 11, left associativity).

Inductive WeakEqual : Term -> Term -> Prop :=
| we_refl : forall (t : Term), WeakEqual t t
| we_sym : forall (t u : Term), WeakEqual t u -> WeakEqual u t
| we_trans : forall (t u w : Term), WeakEqual t u -> WeakEqual u w -> WeakEqual t w
| we_cong : forall (t1 t2 s1 s2 : Term), 
              WeakEqual t1 t2 -> WeakEqual s1 s2 -> WeakEqual (t1 @ s1) (t2 @ s2)
| we_s : forall (x y z : Term), WeakEqual (LS @ x @ y @ z) ((x @ z) @ (y @ z))
| we_k : forall (x y : Term), WeakEqual (LK @ x @ y) x
| we_i : forall (x y : Term), WeakEqual (LI @ x) x.

Ltac pose_we := generalize we_refl we_sym we_trans we_cong we_s we_k we_i; intros.

Notation "X =w Y" := (WeakEqual X Y) (at level 80).

Lemma abstr_correct :
  forall (t s : Term) (v : nat), NoLambdas t -> abstr v t @ s =w csubst t v s.
Proof.
  pose_we.
  induction t; sauto.
  ycrush.
Qed.

Lemma abstr_size :
  forall (t : Term) (v : nat), size (abstr v t) <= 3 * size t.
Proof.
  intros; induction t; sauto; omega.
Qed.

Lemma lem_pow_3 : (forall x y : nat, 3 ^ x + 3 ^ y + 1 <= 3 ^ (x + y + 1)).
Proof.
  intros.
  induction x; simpl in *.
  induction y; simpl in *; omega.
  omega.
Qed.

Lemma transl_size :
  forall (t : Term), size (transl t) <= 3 ^ (size t).
Proof.
  induction t; sauto; try omega.
  assert (size (transl t1) + size (transl t2) <= 3 ^ size t1 + 3 ^ size t2).
  Reconstr.reasy (@Coq.Arith.PeanoNat.Nat.add_le_mono) Reconstr.Empty.
  assert (size (transl t1) + size (transl t2) + 1 <= 3 ^ size t1 + 3 ^ size t2 + 1).
  auto with zarith.
  Reconstr.reasy (@Coq.Arith.PeanoNat.Nat.le_lt_trans, @lem_pow_3, @Coq.Arith.PeanoNat.Nat.lt_succ_r)  Reconstr.Empty.
  assert (size (abstr n (transl t)) <= 3 * size (transl t)).
  pose proof abstr_size; eauto with zarith.
  assert (size (abstr n (transl t)) <= 3 * 3 ^ size t).
  pose proof le_trans; eauto with zarith.
  assert (forall x : nat, 3 * 3 ^ x = 3 ^ (x + 1)).
  Reconstr.reasy (@Coq.Arith.PeanoNat.Nat.add_0_r, @Coq.Arith.PeanoNat.Nat.pow_succ_r', @Coq.Arith.PeanoNat.Nat.shiftl_1_l, @Coq.Arith.PeanoNat.Nat.pow_1_r, @Coq.Arith.PeanoNat.Nat.pow_0_r, @Coq.Arith.PeanoNat.Nat.add_succ_r) Reconstr.Empty.
  ycrush.
Qed.

Lemma abstr_size_lb : forall (t : Term) (v : nat), NoLambdas t -> size (abstr v t) >= 2 * size t.
Proof.
  intros; induction t; sauto; omega.
Qed.

Fixpoint long_app (n : nat) : Term :=
  match n with
    | 0 => LVar 0
    | S k => LApp (long_app k) (LVar n)
  end.

Fixpoint long_term (n m : nat) : Term :=
  match n with
    | 0 => LLam m (long_app m)
    | S k => LLam (m - n) (long_term k m)
  end.

Definition cex_term (n : nat) := long_term n n.

Lemma size_nonneg : forall (t : Term), size t > 0.
Proof.
  induction t; simpl; omega.
Qed.

Lemma transl_size_lb : forall (n : nat), size (transl (cex_term n)) >= 2^n.
Proof.
  assert (forall (n m : nat), size (transl (long_term n m)) >= 2^n).
  induction n; sauto.
  Reconstr.reasy (@Coq.Arith.PeanoNat.Nat.nlt_ge, @Coq.Arith.Gt.gt_le_S, @Coq.Arith.Compare_dec.not_ge, @size_nonneg) Reconstr.Empty.
  assert (size (abstr (m - S n) (transl (long_term n m))) >= 2 * size (transl (long_term n m))).
  Reconstr.reasy (@abstr_size_lb, @no_lams_transl) Reconstr.Empty.
  assert (size (abstr (m - S n) (transl (long_term n m))) >= 2 * 2 ^ n).
  pose proof (IHn m); eauto with zarith.
  scrush.
  now unfold cex_term.
Qed.

Fixpoint occurs (v : nat) (t : Term) : bool :=
  match t with
    | LS | LK | LI => false
    | LVar n => if n =? v then true else false
    | LApp x y => orb (occurs v x) (occurs v y)
    | LLam n b => if n =? v then false else occurs v b
  end.

Lemma occurs_spec : forall (v : nat) (t : Term), occurs v t = true <-> HasVar v t.
Proof.
  pose_hasvar.
  pose proof Coq.Arith.EqNat.beq_nat_true.
  pose proof Coq.Arith.EqNat.beq_nat_false.
  induction t; sauto; unfold orb; try yelles 2.
  assert (occurs v t1 = true \/ occurs v t2 = true).
  Reconstr.reasy (@Coq.Bool.Bool.orb_prop) Reconstr.Empty.
  yelles 1.
Qed.

Fixpoint abstr2 (v : nat) (t : Term) : Term :=
  if occurs v t then
    match t with
      | LS | LK | LI => LApp LK t
      | LVar n => if n =? v then LI else LApp LK t
      | LApp x y => LApp (LApp LS (abstr2 v x)) (abstr2 v y)
      | LLam _ _ => t
    end
  else
    LApp LK t.

Fixpoint transl2 (t : Term) : Term :=
  match t with
    | LS | LK | LI | LVar _ => t
    | LApp x y => LApp (transl2 x) (transl2 y)
    | LLam v x => abstr2 v (transl2 x)
  end.

Lemma no_lams_abstr2 : forall (v : nat) (t : Term), NoLambdas t -> NoLambdas (abstr2 v t).
Proof.
  pose_nolams.
  induction t; yelles 2.
Qed.

Lemma no_lams_transl2 : forall t : Term, NoLambdas (transl2 t).
Proof.
  pose proof no_lams_abstr2.
  pose_nolams.
  induction t; yelles 2.
Qed.

Lemma vars_abstr2 :
  forall (t : Term) (n v : nat), n <> v -> (HasVar n t <-> HasVar n (abstr2 v t)).
Proof.
  pose_hasvar.
  induction t; sauto.
  Reconstr.reasy (@Coq.Arith.EqNat.beq_nat_true) Reconstr.Empty.
Qed.

Lemma novar_abstr2 : forall (v : nat) (t : Term), NoLambdas t -> ~(HasVar v (abstr2 v t)).
Proof.
  pose_hasvar.
  pose (u := t).
  induction t; destruct (occurs v u) eqn:?; sauto.
  - Reconstr.reasy (@Coq.Arith.PeanoNat.Nat.eqb_refl, @Coq.Bool.Bool.not_true_iff_false) Reconstr.Empty.
  - Reconstr.rsimple (@occurs_spec, @Coq.Bool.Bool.not_true_iff_false) (@Coq.Init.Datatypes.orb).
  - Reconstr.rscrush (@occurs_spec, @Coq.Bool.Bool.not_true_iff_false) (@Coq.Init.Datatypes.orb).
Qed.

Lemma vars_transl2 : forall (t : Term) (n : nat), HasVar n t <-> HasVar n (transl2 t).
Proof.
  pose_hasvar.
  induction t; sauto.
  - Reconstr.reasy (@vars_abstr2) Reconstr.Empty.
  - Reconstr.rsimple (@no_lams_transl2, @vars_abstr2, @novar_abstr2, @hs_lem) Reconstr.Empty.
Qed.

Lemma hasvar_inv :
  forall (t1 t2 : Term) (v : nat), ~(HasVar v (t1 @ t2)) -> ~(HasVar v t1) /\ ~(HasVar v t2).
Proof.
  scrush.
Qed.

Lemma csubst_novar :
  forall (t s : Term) (v : nat), NoLambdas t -> ~(HasVar v t) -> csubst t v s = t.
Proof.
  pose_hasvar.
  induction t; sauto.
  Reconstr.rsimple (@Coq.Arith.EqNat.beq_nat_true) Reconstr.Empty.
Qed.

Lemma abstr2_correct :
  forall (t s : Term) (v : nat), NoLambdas t -> abstr2 v t @ s =w csubst t v s.
Proof.
  pose_we.
  induction t; sauto.
  ycrush.
  assert (HH: forall b1 b2, (b1 || b2)%bool = false -> b1 = false /\ b2 = false).
  unfold orb; ycrush.
  pose proof occurs_spec.
  rewrite csubst_novar by ycrush.
  rewrite csubst_novar by ycrush.
  ycrush.
Qed.

Lemma abstr2_size_ub :
  forall (t : Term) (v : nat), size (abstr2 v t) <= 3 * size t.
Proof.
  intros; induction t; sauto; omega.
Qed.
