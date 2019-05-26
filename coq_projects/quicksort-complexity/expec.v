Set Implicit Arguments.

Require Import util.
Require Import List.
Require Import monads.
Require Import sums_and_averages.
Require Import Setoid.
Require ne_tree.
Require arith_lems.
Require Import Rbase.
Require ne_tree_monad.

Open Scope R_scope.

Definition expec (T: Set) (f: T -> nat): ne_tree.T T -> R :=
  TRavg ∘ ne_tree.map (INR ∘ f).
    (* note: currently specialized for discrete measures (hence the nat and INR) *)

Definition expec_sum (T U: Set) (f: U -> nat) (g: T -> ne_tree_monad.M U): list T -> R :=
  Rsum ∘ map (expec f ∘ g).

Section expec_ctors.

  Variables (T: Set) (f: T -> nat).

  Lemma expec_Leaf t: expec f (ne_tree.Leaf t) = INR (f t).
  Proof. auto. Qed.

  Lemma expec_Node l: expec f (ne_tree.Node l) = Ravg (ne_list.map (@expec _ f) l).
  Proof. unfold expec, compose. intros. simpl. rewrite ne_list.map_map. reflexivity. Qed.

  Lemma expec_Node_one x:
    expec f (ne_tree.Node (ne_list.one x)) = expec f x.
  Proof. unfold expec, compose. simpl. intros. rewrite Ravg_one. reflexivity. Qed.

  Lemma expec_Node_cons x t:
    expec f (ne_tree.Node (ne_list.cons x t)) =
    (expec f x + expec f (ne_tree.Node t) * INR (length t)) * / INR (S (length t)).
  Proof.
    intros.
    rewrite expec_Node.
    simpl ne_list.map.
    simpl Ravg.
    rewrite Ravg_cons.
    rewrite expec_Node.
    rewrite ne_list.map_length.
    field.
    auto with real.
  Qed.

End expec_ctors.

(* misc expec *)

Add Parametric Morphism (A: Set): (@expec A)
  with signature (@ext_eq A nat) ==> (@ext_eq (ne_tree.T A) R)
  as expec_ext_morph.
Proof. intros. unfold expec. rewrite H. reflexivity. Qed.

Lemma expec_ext (T: Set) (f g: T -> nat) (e: ext_eq f g): forall x, expec f x = expec g x.
Proof. fold (ext_eq (expec f) (expec g)). apply expec_ext_morph. assumption. Qed.

Lemma lin_nat c d: ext_eq
  (TRavg ∘ ne_tree.map (INR ∘ plus d ∘ mult c))
  (Rplus (INR d) ∘ Rmult (INR c) ∘ TRavg ∘ ne_tree.map INR).
Proof.
  intro.
  induction x.
      repeat rewrite comp_apply.
      simpl.
      repeat rewrite comp_apply.
      rewrite plus_INR.
      rewrite mult_INR.
      reflexivity.
    repeat rewrite comp_apply in *.
    simpl.
    rewrite IHx.
    repeat rewrite Ravg_one.
    reflexivity.
  repeat rewrite comp_apply in *.
  simpl.
  rewrite IHx.
  inversion IHx0.
  repeat rewrite ne_list.map_map in *.
  repeat rewrite Ravg_cons.
  rewrite ne_list.map_length.
  rewrite H0.
  rewrite ne_list.map_length.
  rewrite S_INR.
  field.
  auto with real.
Qed.

Lemma Rmult_INR1_id: ext_eq (Rmult (INR 1)) (@id R).
Proof. intro. apply Rmult_1_l. Qed.

Lemma mult_1_id: ext_eq (mult 1) (@id nat).
Proof. intro. apply mult_1_l. Qed.

Lemma expec_plus_c (T: Set) (g: T -> nat) (c: nat):
  ext_eq (expec (plus c ∘ g)) (Rplus (INR c) ∘ expec g).
Proof.
  intros.
  unfold expec.
  rewrite comp_ass.
  rewrite <- ne_tree.map_map_ext.
  rewrite <- (compose_runit (INR ∘ plus c)).
  rewrite <- mult_1_id.
  rewrite comp_ass.
  rewrite lin_nat.
  rewrite <- comp_ass.
  rewrite ne_tree.map_map_ext.
  rewrite Rmult_INR1_id.
  rewrite compose_runit.
  reflexivity.
Qed.

Lemma expec_plus (T: Set) (f g: T -> nat) (t: ne_tree.T T):
  expec (fun x => plus (f x) (g x)) t = expec f t + expec g t.
Proof with auto.
  induction t.
      repeat rewrite expec_Leaf.
      apply plus_INR.
    repeat rewrite expec_Node_one...
  repeat rewrite expec_Node_cons.
  rewrite IHt.
  rewrite IHt0.
  field...
Qed.

Lemma expec_map (T U: Set) (g: T -> U) (f: U -> nat) (t: ne_tree.T T):
  expec f (ne_tree.map g t) = expec (f ∘ g) t.
Proof. intros. unfold expec. repeat rewrite comp_apply. rewrite ne_tree.map_map. reflexivity. Qed.

Lemma expec_nonneg (T: Set) (m: ne_tree_monad.M T) (f: T -> nat): 0 <= expec f m.
Proof with auto with real.
  induction m; intros.
      rewrite expec_Leaf...
    rewrite expec_Node_one...
  rewrite expec_Node_cons.
  apply Rmult_le_pos...
  apply Rplus_le_le_0_compat...
  apply Rmult_le_pos...
Qed.

Hint Resolve expec_nonneg.

Lemma expec_le (X: Set) (f g: X -> nat) (t: ne_tree.T X):
  (forall x, ne_tree.In x t -> (f x <= g x)%nat) -> expec f t <= expec g t.
Proof with auto with real.
  induction t; intros.
      simpl.
      repeat rewrite expec_Leaf...
    repeat rewrite expec_Node_one...
  repeat rewrite expec_Node_cons.
  apply Rmult_le_compat_r...
  apply Rplus_le_compat...
  apply Rmult_le_compat_r...
  apply IHt0.
  intros.
  apply H.
  right.
  inversion_clear H0...
Qed.

Lemma expec_0_inv (T: Set) (f: T -> nat) (t: ne_tree.T T):
  expec f t = 0 -> forall x, ne_tree.In x t -> f x = 0%nat.
Proof with auto with real.
  induction t.
      simpl.
      intros.
      inversion_clear H0.
      apply arith_lems.INR_0_inv...
    simpl.
    rewrite expec_Node_one.
    intros.
    inversion_clear H0.
    inversion_clear H1...
  rewrite expec_Node_cons.
  intros.
  inversion_clear H0.
  destruct (arith_lems.Rmult_0_inv H).
    assert (expec f t = 0).
      apply Rplus_eq_0_l with (expec f (ne_tree.Node l) * INR (length l))...
      apply Rmult_le_pos...
    assert (expec f (ne_tree.Node l) = 0).
      rewrite Rplus_comm in H0.
      cut (expec f (ne_tree.Node l) * INR (length l) = 0).
        intro.
        destruct (arith_lems.Rmult_0_inv H3)...
        cset (arith_lems.INR_0_inv _ H4).
        destruct l; discriminate.
      apply Rplus_eq_0_l with (expec f t)...
      apply Rmult_le_pos...
    inversion_clear H1...
  elimtype False.
  apply (Rinv_neq_0_compat (INR (S (length l))))...
Qed.

Lemma expec_constant (T: Set) (f: T -> nat) (c: nat) (t: ne_tree_monad.M T):
   (forall x, ne_tree.In x t -> f x = c) -> expec f t = INR c.
Proof with auto with real.
  induction t.
      intros.
      rewrite expec_Leaf...
    simpl.
    rewrite expec_Node_one...
  rewrite expec_Node_cons.
  intros.
  rewrite IHt...
  rewrite IHt0.
    rewrite S_INR.
    field...
  intros.
  apply H.
  inversion_clear H0...
Qed.

Section bind_expecs.

  Variables (T U: Set) (f: T -> nat).

  Lemma expec_bind_leaf (g: U -> T) (m: ne_tree_monad.M U):
    expec f (m >>= (ne_tree_monad.ret ∘ g)) = expec (f ∘ g) m.
  Proof with auto.
    induction m...
      simpl in *.
      repeat rewrite expec_Node_one...
    simpl in *.
    repeat rewrite expec_Node_cons.
    rewrite IHm.
    rewrite IHm0.
    repeat rewrite ne_list.map_length...
  Qed.

  Lemma expec_bind_cons (x: ne_tree_monad.M U) t (g: U -> ne_tree_monad.M T):
    expec f (@bind ne_tree_monad.M _ _  (ne_tree.Node (ne_list.cons x t)) g) =
    (expec f (x >>= g) + expec f (@bind ne_tree_monad.M _ _ (ne_tree.Node t) g) * INR (length t)) * / INR (S (length t)).
  Proof.
    intros.
    simpl expec.
    rewrite expec_Node_cons.
    repeat rewrite ne_list.map_length.
    reflexivity.
  Qed.

End bind_expecs.
