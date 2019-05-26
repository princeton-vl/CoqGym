Require Import Arith List.
Require Import BellantoniCook.Lib BellantoniCook.Cobham.

Definition Zero_e (n:nat) : Cobham :=
  Comp n Zero nil.

Lemma arity_Zero n : arity (Zero_e n) = ok_arity n.
Proof.
  trivial.
Qed.

Lemma rec_bounded_Zero n : 
  rec_bounded (Zero_e n).
Proof.
simpl; tauto.
Qed.

Definition One_e (n:nat) : Cobham :=
  Comp n (Comp 0 (Succ true) [Zero]) nil.

Lemma arity_One n : arity (One_e n) = ok_arity n.
Proof.
  trivial.
Qed.

Lemma rec_bounded_One n :
  rec_bounded (One_e n).
Proof.
simpl; tauto.
Qed.

(** Def 12 of (Rose) *)

Definition App_e : Cobham :=
  Rec (Proj 1 0)
  (Comp 3 (Succ false) [Proj 3 1])
  (Comp 3 (Succ true) [Proj 3 1])
  (Comp 2 Smash [Comp 2 (Succ true) [Proj 2 0]; Comp 2 (Succ true) [Proj 2 1] ]).

Lemma arity_App : arity App_e = ok_arity 2.
Proof.
  trivial.
Qed.

Lemma rec_bounded_App : rec_bounded App_e.
Proof.
simpl.
intuition.
destruct l as [ | u [ | v l] ]; simpl.
omega.
rewrite length_smash, mult_1_r; simpl.
induction u as [ | [ | ] u IH]; simpl; omega.
rewrite length_smash', length_smash; simpl.
induction u as [ | [ | ] u IH]; simpl; omega.
Qed.

Lemma App_correct : forall l,
  Sem App_e l = hd nil l ++ hd nil (tl l).
Proof.
  intros; simpl.
  destruct l; simpl; trivial.
  induction l; simpl.
  destruct l0; simpl; trivial.
  rewrite IHl; case a; trivial.
Qed.

Opaque App_e.

Definition Rev_e : Cobham :=
  Rec
    Zero
    (Comp 2 App_e [Proj 2 1; Comp 2 (Succ false) [Zero_e 2]])
    (Comp 2 App_e [Proj 2 1; Comp 2 (Succ true) [Zero_e 2]])
    (Proj 1 0).

Lemma arity_Rev : 
  arity Rev_e = ok_arity 1.
Proof.
trivial.
Qed.

Lemma rec_bounded_Rev :
  rec_bounded Rev_e.
Proof.
simpl.
intuition.
apply rec_bounded_App.
apply rec_bounded_App.
destruct l as [ | v l].
trivial.
simpl.
induction v as [ | [ | ] v IH].
trivial.
simpl.
rewrite App_correct.
simpl.
rewrite app_length.
simpl; omega.
simpl.
rewrite App_correct.
simpl.
rewrite app_length.
simpl; omega.
Qed. 

Lemma Rev_correct l :
  Sem Rev_e l = List.rev (hd nil l).
Proof.
destruct l as [ | v l].
trivial.
simpl.
induction v as [ | [ | ] v IH].
trivial.
simpl.
rewrite App_correct.
simpl; congruence.
simpl.
rewrite App_correct.
simpl; congruence.
Qed.

Definition RemoveLSZ_e : Cobham :=
  Rec
    Zero
    (Proj 2 1)
    (Comp 2 (Succ true) [Proj 2 0])
    (Proj 1 0).

Lemma arity_RemoveLSZ : 
  arity RemoveLSZ_e = ok_arity 1.
Proof.
trivial.
Qed.

Lemma rec_bounded_RemoveLSZ :
  rec_bounded RemoveLSZ_e.
Proof.
simpl.
intuition.
destruct l as [ | v l].
trivial.
simpl.
induction v as [ | [ | ] v IH].
trivial.
trivial.
simpl; omega.
Qed.

Lemma RemoveLSZ_app u v l :
  Sem RemoveLSZ_e ((u++v)::l) =
  match Sem RemoveLSZ_e (u::l) with
  | nil => Sem RemoveLSZ_e (v::l)
  | u' => u'++v
  end.
Proof.
simpl.
induction u as [ | [ | ] u IH]; trivial.
Qed.

Definition Cond : Cobham :=
  Rec (Proj 3 0) (Proj 5 4) (Proj 5 3) (
    Comp 4 Smash [
      Comp 4 (Succ true) [Proj 4 1];
      Comp 4 Smash [
        Comp 4 (Succ true) [Proj 4 2];
        Comp 4 (Succ true) [Proj 4 3]
      ]
    ]
  ).

Lemma arity_Cond : arity Cond = ok_arity 4.
Proof.
trivial.
Qed.

Lemma rec_bounded_Cond : rec_bounded' Cond.
Proof.
  simpl; repeat (split; auto);  intros.
  repeat (rewrite length_smash'; simpl).
  repeat (rewrite length_smash; simpl).
  repeat (rewrite length_smash'; simpl).
  repeat (rewrite length_smash; simpl).
  
  destruct (hd nil l); simpl; repeat rewrite nth_S_tl.

  rewrite plus_n_Sm.
  rewrite plus_comm.
  apply le_plus_trans.
  apply le_trans with ( S (S (length (nth 1 l nil)) * 1)).
  omega.
  apply le_n_S.
  apply le_n_S.
  apply mult_le_compat.
  trivial.
  apply le_n_S.
  auto with arith.

  apply le_trans with ( S (length (if b then nth 2 l nil else nth 3 l nil)) * 1).
  rewrite mult_1_r; auto with arith.

  apply le_trans with (S (S (length (nth 2 l nil)) * S (length (nth 3 l nil)))).
  case b.
  rewrite mult_1_r.
  apply le_n_S.
  rewrite <- mult_1_r at 1.
  apply mult_le_compat; auto with arith.
  rewrite mult_1_r.
  apply le_n_S.
  rewrite <- mult_1_l at 1.
  apply mult_le_compat; auto with arith.
  set (R1 := length (nth 1 l nil)).
  set (R2 := length (nth 2 l nil)).
  set (R3 := length (nth 3 l nil)).
  set (R4 := length (nth 4 l nil)).
  ring_simplify.
  cutrewrite (R2 * R3 * R1 + R2 * R3 + R2 * R1 + R2 + R3 * R1 + R3 + 2 * R1 + 3 =
    (R2 * R3 + R2 + R3 + 2) + (R2 * R3 * R1 + R2 * R1 + R3 * R1 + 2 * R1 + 1)).
  auto with arith.
  ring.
Qed.

Lemma Cond_correct : forall l,
  Sem Cond l =
  match hd nil l with
  | nil => hd nil (tl l)
  | true::_ => hd nil (tl (tl l))
  | false::_ => hd nil (tl (tl (tl l)))
  end.
Proof.
destruct l as [ | [ | [ | ] v1] [ | v2 [ | v3 [ | v4 l] ] ] ]; trivial.
Qed.
