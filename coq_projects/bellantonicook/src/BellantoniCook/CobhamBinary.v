Require Import Arith Div2 List.
Require Import BellantoniCook.Lib BellantoniCook.Bitstring BellantoniCook.Cobham BellantoniCook.CobhamLib.

Opaque bs2nat.
Opaque Cond.

Lemma bs2nat_smash' : forall u v n,
  bs2nat v = power 2 n ->
  bs2nat (smash' u v) = power 2 (length u + n).
Proof.
  induction u; simpl; intros; auto.
  rewrite bs2nat_false, (IHu v n); trivial.
Qed.

Lemma bs2nat_smash_bs : forall u v,
  bs2nat (smash_bs u v) = power 2 (length u * length v).
Proof.
  induction u; simpl; intros; auto.
  rewrite bs2nat_smash' with (n := length u * length v); trivial.
Qed.

Lemma Smash_correct : forall l,
  bs2nat (Sem Smash l) = power 2 (length (hd nil l) * length (hd nil (tl l))).
Proof.
  intros [ | u [ | v l] ]; trivial; simpl.
  rewrite mult_0_r; simpl.
  induction u as [ | [ | ] u IH]; trivial.
  apply bs2nat_smash_bs.
Qed.

Lemma Zero_correct_bs n l: 
  Sem (Zero_e n) l = nil.
Proof.
  trivial.
Qed.

Lemma Zero_correct n l: 
  bs2nat (Sem (Zero_e n) l) = 0.
Proof.
  trivial.
Qed.

Definition False_e n :=
  Comp n (Succ false) [Zero_e n].

Lemma arity_False: forall n : nat, arity (False_e n) = ok_arity n.
Proof.
  simpl; simpl.
  intros.
  rewrite <- beq_nat_refl.
  simpl.
  trivial.
Qed.

Lemma rec_bounded_False: forall n : nat, rec_bounded (False_e n).
Proof.
 intros; simpl; intuition.
Qed.

Lemma False_correct: forall (n : nat) (l : list bs), bs2nat (Sem (False_e n) l) = 0.
Proof.
 intros; simpl; auto.
Qed.

Lemma False_correct_bs: forall (n : nat) (l : list bs), Sem (False_e n) l = [false].
Proof.
 intros; simpl; auto.
Qed.

Lemma One_correct n l: 
  bs2nat (Sem (One_e n) l) = 1.
Proof.
  trivial.
Qed.

Lemma One_correct_bs n l:
  Sem (One_e n) l = [true].
Proof.
  trivial.
Qed.

Opaque Zero_e One_e False_e Rev_e RemoveLSZ_e.

Definition Normalize_e : Cobham :=
  Comp 1 Rev_e [Comp 1 RemoveLSZ_e [Rev_e]].

Lemma arity_Normalize :
  arity Normalize_e = ok_arity 1.
Proof.
  trivial.
Qed.

Lemma rec_bounded_Normalize :
  rec_bounded Normalize_e.
Proof.
  simpl; intuition.
  apply rec_bounded_Rev.
  apply rec_bounded_RemoveLSZ.
  apply rec_bounded_Rev.
Qed.

Lemma Normalize_correct : forall l,
  bs2nat (Sem Normalize_e l) = bs2nat (Sem (Proj 1 0) l).
Proof.
  destruct l as [ | v l]; trivial;simpl.
  induction v as [ | [ | ] v IH]; trivial.
  
  rewrite bs2nat_true.
  do 2 rewrite Rev_correct in *; simpl in *.
  rewrite RemoveLSZ_app, <- IH.
  destruct (Sem RemoveLSZ_e [rev v]); trivial; simpl.
  rewrite rev_unit; trivial.

  rewrite bs2nat_false.
  do 2 rewrite Rev_correct in *; simpl in *.
  rewrite RemoveLSZ_app, <- IH.
  destruct (Sem RemoveLSZ_e [rev v]); trivial; simpl.
  rewrite rev_unit; trivial.
Qed.

Lemma Normalize_normal : forall l,
  Sem Normalize_e l = nil \/ bs2nat (Sem Normalize_e l) <> 0.
Proof.
  destruct l as [ | v l].
  tauto.
  simpl.
  induction v as [ | [ | ] v IH].
  
  tauto.

  do 2 rewrite Rev_correct in *.
  simpl in *.
  rewrite RemoveLSZ_app.
  destruct (Sem RemoveLSZ_e [rev v]).
  right.
  discriminate.
  right.
  simpl.
  rewrite rev_unit.
  discriminate.

  do 2 rewrite Rev_correct in *.
  simpl in *.
  rewrite RemoveLSZ_app.
  destruct (Sem RemoveLSZ_e [rev v]).
  trivial.
  simpl in *.
  rewrite rev_unit.
  simpl.
  right.
  rewrite bs2nat_false.
  destruct IH as [IH | IH].
  apply app_eq_nil in IH.
  destruct IH as [_ IH].
  congruence.
  omega.
Qed.

Opaque Normalize_e.

(** Def 1 of (Rose) *)

Definition Succ_e : Cobham :=
  Rec
    (Comp 0 (Succ true) [Zero])
    (Comp 2 (Succ true) [Proj 2 0])
    (Comp 2 (Succ false) [Proj 2 1])
    (Comp 1 (Succ true) [Proj 1 0]).

Lemma arity_Succ : arity Succ_e = ok_arity 1.
Proof.
  trivial.
Qed.

Lemma length_Succ : forall l,
  length (Sem Succ_e l) <= length (Sem (Comp 1 (Succ true) [Proj 1 0]) l).
Proof.
  destruct l as [ | v l]; trivial; simpl.
  induction v as [ | [ | ] v IH]; trivial; simpl; omega.
Qed.

Lemma le_1_length_Succ v : 
  1 <= length (Sem Succ_e [v]).
Proof.
  destruct v as [ | [ | ] v]; trivial; simpl; omega.
Qed.

Lemma le_length_Succ v :
  length v <= length (Sem Succ_e [v]).
Proof.
induction v as [ | [ | ] v IH].
simpl; omega.
simpl in *.
omega.
trivial.
Qed.

Lemma Succ_length v :
  length (Sem Succ_e v) <= S (length (hd nil v)).
Proof.
 intros; simpl.
 induction (hd nil v); simpl; auto.
 case a; simpl; omega.
Qed.  

Lemma rec_bounded_Succ :
  rec_bounded Succ_e.
Proof.
 simpl; intuition.
 eapply le_trans.
 eapply le_trans.
 2:apply length_Succ.
 simpl; trivial.
 trivial.
Qed.

Lemma Succ_correct : forall l,
  bs2nat (Sem Succ_e l) = 1 + bs2nat (hd nil l).
Proof.
  destruct l as [ | v l]; trivial; simpl hd.
  induction v as [ | [ | ] v IH]; trivial.
  simpl Sem in *.
  rewrite bs2nat_false, bs2nat_true, IH; ring.
Qed.

Opaque Succ_e.

(** Def 2 of (Rose) *)

Definition Pred'_e : Cobham :=
  Rec
    Zero
    (Comp 2 (Succ true) [Proj 2 1])
    (Comp 2 (Succ false) [Proj 2 0])
    (Proj 1 0).

Lemma arity_Pred' : arity Pred'_e = ok_arity 1.
Proof.
  trivial.
Qed.

Lemma rec_bounded_Pred' :
  rec_bounded Pred'_e.
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

Lemma Pred'_correct : forall l,
  hd nil l = nil \/ bs2nat (hd nil l) <> 0 ->
  bs2nat (Sem Pred'_e l) =  bs2nat (hd nil l) - 1.
Proof.
intros l H.
destruct l as [ | v l].
simpl.
trivial.
simpl hd.
induction v as [ | [ | ] v IH].

trivial.

simpl Sem in *.
rewrite bs2nat_false, bs2nat_true.
omega.

simpl Sem in *.
rewrite bs2nat_false, bs2nat_true, IH.
simpl in H.
destruct H as [H | H].
congruence.
rewrite bs2nat_false in H.
omega.
simpl in *.
destruct H as [H | H].
congruence.
rewrite bs2nat_false in H.

simpl in H.
right.
omega.
Qed.

Opaque Pred'_e.

Definition Pred_e : Cobham :=
  Comp 1 Pred'_e [Normalize_e].

Lemma arity_Pred : arity Pred_e = ok_arity 1.
Proof.
trivial.
Qed.

Lemma rec_bounded_Pred :
  rec_bounded Pred_e.
Proof.
simpl.
intuition.
apply rec_bounded_Pred'.
apply rec_bounded_Normalize.
Qed.

Lemma Pred_correct : forall l,
  bs2nat (Sem Pred_e l) =  bs2nat (hd nil l) - 1.
Proof.
intro l.
simpl.
rewrite Pred'_correct.
simpl.
rewrite Normalize_correct.
simpl.
rewrite hd_nth_0.
trivial.
apply Normalize_normal.
Qed.

Opaque Pred_e.

(** Def 3 of (Rose) *)

Definition OneMinus'_e : Cobham :=
  Rec2
    (One_e 0)
    (Zero_e 2)
    (One_e 1).

Lemma arity_OneMinus' : arity OneMinus'_e = ok_arity 1.
Proof.
trivial.
Qed.

Lemma rec_bounded_OneMinus' :
  rec_bounded OneMinus'_e.
Proof.
simpl.
intuition.
apply rec_bounded_One.
apply rec_bounded_One.
apply rec_bounded_Zero.
apply rec_bounded_Zero.
destruct l as [ | v l].
trivial.
simpl.
induction v as [ | [ | ] v IH].
trivial.
auto with arith.
auto with arith.
Qed.

Lemma OneMinus'_correct : forall l,
  hd nil l = nil \/ bs2nat (hd nil l) <> 0 ->
  bs2nat (Sem OneMinus'_e l) = 1 - bs2nat (hd nil l).
Proof.
intros [ | v l] H.
trivial.
simpl hd.
destruct v as [ | [ | ] v].
trivial.
trivial.
simpl Sem in *.
simpl in *.
rewrite Zero_correct.
rewrite bs2nat_false in *.
destruct H as [H | H].
congruence.
destruct (2 * bs2nat v).
tauto.
trivial.
Qed.

Opaque OneMinus'_e.

Definition OneMinus_e : Cobham :=
  Comp 1 OneMinus'_e [Normalize_e].

Lemma arity_OneMinus : arity OneMinus_e = ok_arity 1.
Proof.
trivial.
Qed.

Lemma rec_bounded_OneMinus :
  rec_bounded OneMinus_e.
Proof.
simpl.
intuition.
apply rec_bounded_OneMinus'.
apply rec_bounded_Normalize.
Qed.

Lemma OneMinus_correct : forall l,
  bs2nat (Sem OneMinus_e l) = 1 - bs2nat (hd nil l).
Proof.
intro l.
simpl.
rewrite OneMinus'_correct.
simpl.
rewrite Normalize_correct.
simpl.
rewrite hd_nth_0.
trivial.
apply Normalize_normal.
Qed.

Opaque OneMinus_e.

(** Def 4 of (Rose) *)

Definition Div2_e : Cobham :=
  Rec2
    Zero
    (Proj 2 0)
    (Proj 1 0).

Lemma arity_Div2 : arity Div2_e = ok_arity 1.
Proof.
trivial.
Qed.

Lemma length_Div2 : forall l,
  length (Sem Div2_e l) = length (hd nil l) - 1.
Proof.
destruct l as [ | v l].
trivial.
simpl.
induction v as [ | [ | ] v IH].
trivial.
simpl; omega.
simpl; omega.
Qed.

Lemma rec_bounded_Div2 :
  rec_bounded Div2_e.
Proof.
simpl.
intuition.
destruct l as [ | v l].
trivial.
simpl.
destruct v as [ | [ | ] v].
trivial.
simpl; omega.
simpl; omega.
Qed.

Lemma Div2_correct_bs : forall l,
  Sem Div2_e l =
  tl (hd nil l).
Proof.
destruct l as [ | v l].
trivial.
simpl.
destruct v as [ | [ | ] v]; trivial.
Qed.

Lemma Div2_correct : forall l,
  bs2nat (Sem Div2_e l) = div2 (bs2nat (hd nil l)).
Proof.
intros [ | v l].
trivial.
rewrite Div2_correct_bs.
simpl.
apply bs2nat_tl.
Qed.

Opaque Div2_e.

(** Def 5 of (Rose) *)

Definition Mod2_e : Cobham :=
  Rec
    Zero
    (False_e 2)
    (One_e 2)
    (One_e 1).

Lemma arity_Mod2 : arity Mod2_e = ok_arity 1.
Proof.
simpl.
trivial.
Qed.

Lemma rec_bounded_Mod2 :
  rec_bounded Mod2_e.
Proof.
simpl.
intuition.
apply rec_bounded_One.
apply rec_bounded_False.
apply rec_bounded_One.
destruct l as [ | v l].
simpl; omega.
simpl.
induction v as [ | [ | ] v IH].
simpl; omega.
auto with arith.
auto with arith.
Qed.

Lemma Mod2_correct_bs : forall l, 
  (hd nil l) <> nil ->
  Sem Mod2_e l = [hd true (hd nil l)].
Proof.
  intros.
  simpl.
  destruct (hd nil l); simpl; trivial.
  elim H; trivial.
  case b.
  rewrite One_correct_bs.
  trivial.
  rewrite False_correct_bs.
  trivial.
Qed.

Lemma Mod2_correct : forall l,
  bs2nat (Sem Mod2_e l) = mod2 (bs2nat (hd nil l)).
Proof.
unfold mod2.
destruct l as [ | v l].
trivial.
simpl hd.
destruct v as [ | [ | ] v].
trivial.
simpl Sem in *.
rewrite One_correct, bs2nat_true.
change (1 + 2 * bs2nat v) with (S (2 * bs2nat v)).
rewrite div2_double_plus_one.
omega.
simpl Sem in *.
rewrite bs2nat_false.
rewrite div2_double.
auto with arith.
Qed.

Opaque Mod2_e.

(** Def 6 of (Rose) *)

Definition Length_e : Cobham :=
  Rec2
    Zero
    (Comp 2 Succ_e [Proj 2 1])
    (Proj 1 0).

Lemma arity_Length : arity Length_e = ok_arity 1.
Proof.
  trivial.
Qed.

Lemma rec_bounded_Length :
  rec_bounded Length_e.
Proof.
simpl.
intuition.
apply rec_bounded_Succ.
apply rec_bounded_Succ.
destruct l as [ | v l].
trivial.
simpl.
induction v as [ | [ | ] v IH].
trivial.
simpl.
eapply le_trans.
apply length_Succ.
simpl; omega.
simpl.
eapply le_trans.
apply length_Succ.
simpl; omega.
Qed.

Lemma Length_correct : forall l,
  bs2nat (Sem Length_e l) = length (hd nil l).
Proof.
destruct l as [ | v l].
trivial.
simpl hd.
induction v as [ | [ | ] v IH].
trivial.
simpl.
rewrite Succ_correct.
simpl.
f_equal.
trivial.
simpl.
rewrite Succ_correct.
simpl.
f_equal.
trivial.
Qed.

Opaque Length_e.

(** Def 7 of (Rose) *)

Definition MultOneMinus'_e : Cobham :=
  Comp 2 Cond [
    Proj 2 1;
    Proj 2 0;
    Zero_e 2;
    Zero_e 2
  ].

Lemma arity_MultOneMinus' : arity MultOneMinus'_e = ok_arity 2.
Proof.
trivial.
Qed.

Lemma rec_bounded_MultOneMinus' :
  rec_bounded MultOneMinus'_e.
Proof.
simpl.
intuition.
apply rec_bounded'_spec with 4.
apply arity_Cond.
apply rec_bounded_Cond.
apply rec_bounded_Zero.
apply rec_bounded_Zero.
Qed.

Lemma MultOneMinus'_correct : forall l,
  hd nil (tl l) = nil \/ bs2nat (hd nil (tl l)) <> 0 ->
  bs2nat (Sem MultOneMinus'_e l) = bs2nat (hd nil l) * (1 - bs2nat (hd nil (tl l))).
Proof.
intros [ | u [ | v l] ] H.
trivial.
auto with arith.
simpl.
rewrite Cond_correct.
simpl in *.
destruct v as [ | [ | ] v].
auto with arith.
trivial.
rewrite Zero_correct.
rewrite bs2nat_false in *.
destruct (2 * bs2nat v).
destruct H.
congruence.
tauto.
trivial.
Qed. 

Opaque MultOneMinus'_e.

Definition MultOneMinus_e : Cobham :=
  Comp 2 MultOneMinus'_e [Proj 2 0; Comp 2 Normalize_e [Proj 2 1]].

Lemma arity_MultOneMinus : arity MultOneMinus_e = ok_arity 2.
Proof.
trivial.
Qed.

Lemma rec_bounded_MultOneMinus :
  rec_bounded MultOneMinus_e.
Proof.
simpl.
intuition.
apply rec_bounded_MultOneMinus'.
apply rec_bounded_Normalize.
Qed.

Lemma MultOneMinus_correct : forall l,
  bs2nat (Sem MultOneMinus_e l) = bs2nat (hd nil l) * (1 - bs2nat (hd nil (tl l))).
Proof.
intro l.
simpl.
rewrite MultOneMinus'_correct.
simpl.
rewrite Normalize_correct.
simpl.
rewrite hd_nth_1, hd_nth_0.
trivial.
simpl.
apply Normalize_normal.
Qed.

Opaque MultOneMinus_e.

(** Def 8 of (Rose) *)

Definition PlusOneMinus'_e : Cobham :=
  Comp 2 Cond [
    Proj 2 1;
    Comp 2 Succ_e [Proj 2 0];
    Proj 2 0;
    Proj 2 0
  ].

Lemma arity_PlusOneMinus' : arity PlusOneMinus'_e = ok_arity 2.
Proof.
trivial.
Qed.

Lemma rec_bounded_PlusOneMinus' :
  rec_bounded PlusOneMinus'_e.
Proof.
simpl.
intuition.
apply rec_bounded'_spec with 4.
apply arity_Cond.
apply rec_bounded_Cond.
apply rec_bounded_Succ.
Qed.

Lemma PlusOneMinus'_correct : forall l,
  hd nil (tl l) = nil \/ bs2nat (hd nil (tl l)) <> 0 ->
  bs2nat (Sem PlusOneMinus'_e l) = bs2nat (hd nil l) + (1 - bs2nat (hd nil (tl l))).
Proof.
intros [ | u [ | v l] ] H.
trivial.
simpl.
rewrite Cond_correct.
simpl.
rewrite Succ_correct, bs2nat_nil.
simpl; ring.
simpl.
rewrite Cond_correct.
simpl.
destruct v as [ | [ | ] v].
rewrite Succ_correct, bs2nat_nil.
simpl; ring.
trivial.
simpl in H.
rewrite bs2nat_false in *.
destruct (2 * bs2nat v).
destruct H.
congruence.
tauto.
trivial.
Qed.

Lemma PlusOneMinus'_length : forall l,
  length (Sem PlusOneMinus'_e [nth 0 l nil; Sem Normalize_e [nth 1 l nil]])
  <= S (length (hd nil l)).
Proof.
 intros; simpl.
 rewrite Cond_correct; simpl.
 rewrite hd_nth_0.
 destruct (Sem Normalize_e [nth 1 l nil]); auto.
 apply Succ_length.
 case b; auto.
Qed.

Opaque PlusOneMinus'_e.

Definition PlusOneMinus_e : Cobham :=
  Comp 2 PlusOneMinus'_e [Proj 2 0; Comp 2 Normalize_e [Proj 2 1] ].

Lemma arity_PlusOneMinus : arity PlusOneMinus_e = ok_arity 2.
Proof.
trivial.
Qed.

Lemma rec_bounded_PlusOneMinus :
  rec_bounded PlusOneMinus_e.
Proof.
simpl.
intuition.
apply rec_bounded_PlusOneMinus'.
apply rec_bounded_Normalize.
Qed.

Lemma PlusOneMinus_correct : forall l,
  bs2nat (Sem PlusOneMinus_e l) = bs2nat (hd nil l) + (1 - bs2nat (hd nil (tl l))).
Proof.
intro l.
simpl.
rewrite PlusOneMinus'_correct.
simpl.
rewrite Normalize_correct.
simpl.
rewrite hd_nth_1, hd_nth_0.
trivial.
simpl.
apply Normalize_normal.
Qed.

Lemma PlusOneMinus_length : forall l,
  length (Sem PlusOneMinus_e [nth 0 l nil; nth 1 l nil]) <= S (length (nth 0 l nil)).
Proof.
 intros; simpl.
 rewrite <- hd_nth_0 at 2.
 apply PlusOneMinus'_length.
Qed.

Opaque PlusOneMinus_e.

(** Def 9 of (Rose) *)

Definition OneMinusMultPlus'_e : Cobham :=
  Rec
    (Proj 1 0)
    (Comp 3 (Succ false) [Proj 3 0])
    (Comp 3 (Succ true) [Proj 3 0])
    (Comp 2 Smash [Comp 2 Succ_e [Proj 2 1]; Comp 2 (Succ true) [Proj 2 0]]).

Lemma arity_OneMinusMultPlus' : arity OneMinusMultPlus'_e = ok_arity 2.
Proof.
trivial.
Qed.

Lemma rec_bounded_OneMinusMultPlus' :
  rec_bounded OneMinusMultPlus'_e.
Proof.
simpl.
intuition.
apply rec_bounded_Succ.
destruct l as [ | v l].
simpl; omega.
simpl.
induction v as [ | [ | ] v IH]; simpl.
rewrite length_smash.
simpl.
rewrite mult_1_r.
eapply le_trans; [idtac | apply le_n_S; apply le_length_Succ].
omega.
rewrite length_smash.
simpl.
apply le_n_S.
rewrite <- (mult_1_l (length v)).
apply mult_le_compat.
apply le_1_length_Succ.
omega.
rewrite length_smash.
simpl.
apply le_n_S.
rewrite <- (mult_1_l (length v)).
apply mult_le_compat.
apply le_1_length_Succ.
omega.
Qed.

Lemma OneMinusMultPlus'_correct : forall l,
  hd nil l = nil \/ bs2nat (hd nil l) <> 0 ->
  bs2nat (Sem OneMinusMultPlus'_e l) =
  (1 - bs2nat (hd nil l)) * bs2nat (hd nil (tl l)) +
  bs2nat (hd nil l) * (1 - (1 - bs2nat (hd nil l))).
Proof.
intros [ | v l] H.
trivial.
simpl.
destruct v as [ | [ | ] v]; simpl.
rewrite bs2nat_nil, hd_nth_0.
ring.
rewrite bs2nat_true.
simpl; ring.
simpl in *.
rewrite bs2nat_false in *.
destruct (2 * bs2nat v).
destruct H.
congruence.
tauto.
ring.
Qed.

Opaque OneMinusMultPlus'_e.

Definition OneMinusMultPlus_e : Cobham :=
  Comp 2 OneMinusMultPlus'_e [Comp 2 Normalize_e [Proj 2 0]; Proj 2 1].

Lemma arity_OneMinusMultPlus : arity OneMinusMultPlus_e = ok_arity 2.
Proof.
trivial.
Qed.

Lemma rec_bounded_OneMinusMultPlus :
  rec_bounded OneMinusMultPlus_e.
Proof.
simpl.
intuition.
apply rec_bounded_OneMinusMultPlus'.
apply rec_bounded_Normalize.
Qed.

Lemma OneMinusMultPlus_correct : forall l,
  bs2nat (Sem OneMinusMultPlus_e l) =
  (1 - bs2nat (hd nil l)) * bs2nat (hd nil (tl l)) +
  bs2nat (hd nil l) * (1 - (1 - bs2nat (hd nil l))).
Proof.
intro l.
simpl.
rewrite OneMinusMultPlus'_correct.
simpl.
rewrite Normalize_correct.
simpl.
rewrite hd_nth_1, hd_nth_0.
trivial.
apply Normalize_normal.
Qed.

Opaque OneMinusMultPlus_e.

(** Def 10 of (Rose) *)

Definition PlusMod2_e : Cobham :=
  Comp 2 Cond [
     Proj 2 1;
     Proj 2 0;
     Comp 2 Succ_e [Proj 2 0];
     Proj 2 0
  ].

Lemma arity_PlusMod2 :
  arity PlusMod2_e = ok_arity 2.
Proof.
trivial.
Qed.

Lemma rec_bounded_PlusMod2 :
  rec_bounded PlusMod2_e.
Proof.
simpl.
intuition.
apply rec_bounded'_spec with 4.
apply arity_Cond.
apply rec_bounded_Cond.
apply rec_bounded_Succ.
Qed.

Lemma PlusMod2_correct : forall l,
  bs2nat (Sem PlusMod2_e l) =
  bs2nat (hd nil l) + mod2 (bs2nat (hd nil (tl l))).
Proof.
unfold mod2.
intros [ | u [ | v l] ]; simpl.
trivial.
rewrite Cond_correct, bs2nat_nil; simpl.
omega.
rewrite Cond_correct; simpl.
destruct v as [ | [ | ] v].
rewrite bs2nat_nil.
simpl; omega.
rewrite bs2nat_true, Succ_correct.
change (1 + 2 * bs2nat v) with (S (2 * bs2nat v)).
rewrite div2_double_plus_one.
simpl hd; omega.
rewrite bs2nat_false, div2_double.
omega.
Qed.

Opaque PlusMod2_e.

(** Def 11 of (Rose) *)

Definition PlusOneMinusMod2_e : Cobham :=
  Comp 3 Cond [
    Proj 3 2;
    Proj 3 0;
    Comp 3 PlusOneMinus_e [Proj 3 0; Proj 3 1];
    Proj 3 0
  ].

Lemma arity_PlusOneMinusMod2 :
  arity PlusOneMinusMod2_e = ok_arity 3.
Proof.
trivial.
Qed.

Lemma rec_bounded_PlusOneMinusMod2 :
  rec_bounded PlusOneMinusMod2_e.
Proof.
simpl.
intuition.
apply rec_bounded'_spec with 4.
apply arity_Cond.
apply rec_bounded_Cond.
apply rec_bounded_PlusOneMinus.
Qed.

Lemma PlusOneMinusMod2_correct : forall l,
  bs2nat (Sem PlusOneMinusMod2_e l) =
  bs2nat (hd nil l) +
  (1 - bs2nat (hd nil (tl l))) *
  mod2 (bs2nat (hd nil (tl (tl l)))).
Proof.
unfold mod2.
intros [ | u [ | v [ | w l] ] ]; simpl.
trivial.
trivial.
rewrite Cond_correct.
simpl.
rewrite bs2nat_nil.
simpl; ring.
rewrite Cond_correct.
simpl.
destruct w as [ | [ | ] w].
rewrite bs2nat_nil.
simpl; ring.
rewrite PlusOneMinus_correct.
simpl.
rewrite bs2nat_true.
change (1 + 2 * bs2nat w) with (S (2 * bs2nat w)).
rewrite div2_double_plus_one.
case (bs2nat v).
omega.
trivial.
rewrite bs2nat_false.
rewrite div2_double.
case (bs2nat v).
omega.
trivial.
Qed.

Lemma PlusOneMinusMod2_length : forall l,
  length (Sem PlusOneMinusMod2_e l) <= S (length (hd nil l)).
Proof.
 intros; simpl.
 rewrite Cond_correct; simpl.
 rewrite hd_nth_0.
 destruct (nth 2 l nil); auto.
 case b; auto.
 apply PlusOneMinus_length.
Qed.

Opaque PlusOneMinusMod2_e.

(** Def 13 of (Rose) *)

Definition MultTwoPowerLength'_e : Cobham :=
  Rec2
    (Proj 1 0)
    (Comp 3 (Succ false) [Proj 3 1])
    (Comp 2 Smash [Comp 2 (Succ true) [Proj 2 0]; Comp 2 (Succ true) [Proj 2 1] ] ).

(* FIXME: According to Rose (Def 13), 'plus 1' in arguments of Smash are not necessary
 *)

Lemma arity_MultTwoPowerLength' :
  arity MultTwoPowerLength'_e = ok_arity 2.
Proof.
trivial.
Qed.

Lemma rec_bounded_MultTwoPowerLength' :
  rec_bounded MultTwoPowerLength'_e.
Proof.
simpl.
intuition.
destruct l as [ | u [ | v l] ]; simpl.
omega.
rewrite length_smash; simpl.
rewrite mult_1_r.
induction u as [ | [ | ] u IH]; simpl; omega.
rewrite length_smash', length_smash; simpl.
induction u as [ | [ | ] u IH]; simpl; omega.
Qed.

Lemma MultTwoPowerLength'_correct : forall l,
  bs2nat (Sem MultTwoPowerLength'_e l) =
  power 2 (length (hd nil l)) * bs2nat (hd nil (tl l)).
Proof.
destruct l as [ | u [ | v l] ].
trivial.
simpl.
rewrite bs2nat_nil, mult_0_r.
induction u as [ | [ | ] u IH].
trivial.
simpl.
rewrite bs2nat_false.
omega.
simpl.
rewrite bs2nat_false.
omega.
induction u as [ | [ | ] u IH]; simpl in *.
trivial.
rewrite bs2nat_false, plus_0_r, IH.
ring.
rewrite bs2nat_false, plus_0_r, IH.
ring.
Qed.

Opaque MultTwoPowerLength'_e.

Definition MultTwoPowerLength_e : Cobham :=
  Comp 2 MultTwoPowerLength'_e [Proj 2 1; Proj 2 0].

Lemma arity_MultTwoPowerLength :
  arity MultTwoPowerLength_e = ok_arity 2.
Proof.
trivial.
Qed.

Lemma rec_bounded_MultTwoPowerLength :
  rec_bounded MultTwoPowerLength_e.
Proof.
simpl.
intuition.
apply rec_bounded_MultTwoPowerLength'.
Qed.

Lemma MultTwoPowerLength_correct : forall l,
  bs2nat (Sem MultTwoPowerLength_e l) =
  bs2nat (hd nil l) * power 2 (length (hd nil (tl l))).
Proof.
intro l.
simpl.
rewrite MultTwoPowerLength'_correct; simpl.
rewrite hd_nth_0, hd_nth_1.
ring.
Qed.

Opaque MultTwoPowerLength_e.

(** Def 14 of (Rose) *)

Definition DivTwoPower'_e : Cobham :=
  Rec2
    (Proj 1 0)
    (Comp 3 Div2_e [Proj 3 1])
    (Proj 2 1).

Lemma arity_DivTwoPower' :
  arity DivTwoPower'_e = ok_arity 2.
Proof.
trivial.
Qed.

Lemma length_DivTwoPower' : forall l,
  length (Sem DivTwoPower'_e l) = length (hd nil (tl l)) - length (hd nil l).
Proof.
intros [ | u [ | v l] ].
trivial.
simpl.
induction u as [ | [ | ] u IH].
trivial.
simpl.
rewrite length_Div2.
simpl; omega.
simpl.
rewrite length_Div2.
simpl; omega.
induction u as [ | [ | ] u IH].
simpl; omega.
simpl in *.
rewrite length_Div2.
simpl; omega.
simpl in *.
rewrite length_Div2.
simpl; omega.
Qed.

Lemma rec_bounded_DivTwoPower' :
  rec_bounded DivTwoPower'_e.
Proof.
simpl.
intuition.
apply rec_bounded_Div2.
apply rec_bounded_Div2.
destruct l as [ | u [ | v l] ].
trivial.
simpl.
induction u as [ | [ | ] u IH].
trivial.
simpl.
rewrite length_Div2.
simpl; omega.
simpl.
rewrite length_Div2.
simpl; omega.
induction u as [ | [ | ] u IH].
trivial.
simpl in *.
rewrite length_Div2.
simpl; omega.
simpl in *.
rewrite length_Div2.
simpl; omega.
Qed.

Lemma DivTwoPower'_correct_bs : forall l,
  Sem DivTwoPower'_e l =
  fun_power (length (hd nil l)) (@tl _) (hd nil (tl l)).
Proof.
intros [ | u [ | v l] ].
trivial.
simpl.
induction u as [ | [ | ] u IH].
trivial.
simpl.
rewrite Div2_correct_bs.
simpl; congruence.
simpl.
rewrite Div2_correct_bs.
simpl; congruence.
simpl.
induction u as [ | [ | ] u IH].
trivial.
simpl.
rewrite Div2_correct_bs.
simpl; congruence.
simpl.
rewrite Div2_correct_bs.
simpl; congruence.
Qed.

Lemma DivTwoPower'_correct : forall l,
  bs2nat (Sem DivTwoPower'_e l) =
  fun_power (length (hd nil l)) div2 (bs2nat (hd nil (tl l))).
Proof.
intro l.
rewrite DivTwoPower'_correct_bs.
induction (length (hd nil l)).
trivial.
simpl.
rewrite bs2nat_tl.
congruence.
Qed.

Opaque DivTwoPower'_e.

Definition DivTwoPower_e : Cobham :=
  Comp 2 DivTwoPower'_e [Proj 2 1; Proj 2 0].

Lemma arity_DivTwoPower :
  arity DivTwoPower_e = ok_arity 2.
Proof.
trivial.
Qed.

Lemma rec_bounded_DivTwoPower :
  rec_bounded DivTwoPower_e.
Proof.
simpl.
intuition.
apply rec_bounded_DivTwoPower'.
Qed.

Lemma DivTwoPower_correct_bs : forall l,
  Sem DivTwoPower_e l =
  fun_power (length (hd nil (tl l))) (@tl _) (hd nil l).
Proof.
intro l.
simpl.
rewrite DivTwoPower'_correct_bs.
simpl.
rewrite <- hd_nth_0, <- hd_nth_1.
trivial.
Qed.

Lemma length_DivTwoPower : forall l,
  length (Sem DivTwoPower_e l) = length (hd nil l) - length (hd nil (tl l)).
Proof.
intro l.
simpl.
rewrite length_DivTwoPower'.
simpl.
rewrite <- hd_nth_0, <- hd_nth_1.
trivial.
Qed.

Lemma skipn_tl : forall n (l : bs),
  skipn (S n) l = tl (skipn n l).
Proof.
  intros.
  destruct (le_lt_dec (length l) n).
  rewrite skipn_nil; simpl.
  rewrite skipn_nil; simpl; auto.
  omega.
  rewrite (skipn_hd n l true).
  reflexivity.
  trivial.
Qed.   
  
Lemma DivTwoPower_correct : forall l,
  Sem DivTwoPower_e l =
  skipn (length (nth 1 l nil)) (nth 0 l nil).
Proof.
  intros l.
  simpl.
  rewrite DivTwoPower'_correct_bs; simpl.
  induction (nth 1 l nil); simpl; auto.
  rewrite IHl0.
  destruct (nth 0 l nil); simpl.
  rewrite skipn_nil; simpl; auto.
  omega.
  rewrite <- skipn_tl.
  simpl.
  trivial.
Qed.

Opaque DivTwoPower_e.

(** Def 15 of (Rose) *)

Definition DivDivTwoPower_e : Cobham :=
  Comp 3 DivTwoPower_e [Proj 3 0; Comp 3 DivTwoPower_e [Proj 3 1; Proj 3 2] ].

Lemma arity_DivDivTwoPower :
  arity DivDivTwoPower_e = ok_arity 3.
Proof.
trivial.
Qed.

Lemma rec_bounded_DivDivTwoPower :
  rec_bounded DivDivTwoPower_e.
Proof.
simpl.
intuition.
apply rec_bounded_DivTwoPower.
apply rec_bounded_DivTwoPower.
Qed.

Lemma DivDivTwoPower_correct : forall l,
  Sem DivDivTwoPower_e l =
  skipn (length (nth 1 l nil) - length (nth 2 l nil)) (nth 0 l nil).
Proof.
  intros l.
  simpl.
  rewrite DivTwoPower_correct; simpl.
  rewrite DivTwoPower_correct; simpl.
  f_equal.
  rewrite length_skipn; trivial.
Qed.

Opaque DivDivTwoPower_e.

(** Def 16 of (Rose) *)

Fixpoint Repeat_e (n l : nat) (b : bool) : Cobham :=
  match l with
    | 0 => Zero_e n
    | S l' => Comp n (Succ b) [Repeat_e n l' b]
  end.

Lemma arity_Repeat : forall n len b,
  arity (Repeat_e n len b) = ok_arity n.
Proof.
induction len as [ | len' IH]; simpl; trivial; intros [ | ];
  rewrite IH; simpl; rewrite <- beq_nat_refl; trivial.
Qed.

Lemma rec_bounded_Repeat : forall n len b,
  rec_bounded (Repeat_e n len b).
Proof.
intros n len b.
induction len as [ | len' IH]; simpl.
apply rec_bounded_Zero.
intuition.
Qed.

Lemma length_Repeat : forall n l b l',
  length (Sem (Repeat_e n l b) l') = l.
Proof.
  induction l; simpl; auto.
Qed.

Opaque Repeat_e.

Definition RoseS'_e : Cobham :=
  Rec2
    (Zero_e 2)
    (Comp 4 PlusOneMinusMod2_e [
      Comp 4 (Succ false) [Proj 4 1];
      Comp 4 DivTwoPower_e [Comp 4 DivTwoPower_e [Proj 4 2; Proj 4 0]; Proj 4 3];
      Comp 4 DivDivTwoPower_e [Proj 4 2; Proj 4 2; Comp 4 (Succ false) [Proj 4 0]]
    ])
    (Comp 3 Smash [Proj 3 0; Repeat_e 3 2 true]).

Definition arity_RoseS' :
  arity RoseS'_e = ok_arity 3.
Proof.
trivial.
Qed.

Lemma rec_bounded_RoseS' :
  rec_bounded RoseS'_e.
Proof.
simpl.
intuition.
apply rec_bounded_Repeat.
apply rec_bounded_Zero.
apply rec_bounded_PlusOneMinusMod2.
apply rec_bounded_DivTwoPower.
apply rec_bounded_DivTwoPower.
apply rec_bounded_DivDivTwoPower.
apply rec_bounded_PlusOneMinusMod2.
apply rec_bounded_DivTwoPower.
apply rec_bounded_DivTwoPower.
apply rec_bounded_DivDivTwoPower.
rewrite <- hd_nth_0.
induction (hd nil l); simpl.
rewrite Zero_correct_bs; simpl; auto with arith.
case a.
eapply le_trans.
apply PlusOneMinusMod2_length.
simpl.
rewrite length_smash'.
rewrite length_Repeat.
omega.
eapply le_trans.
apply PlusOneMinusMod2_length.
simpl.
rewrite length_smash'.
rewrite length_Repeat.
omega.
Qed.

Definition RoseS_e : Cobham :=
  Comp 3 RoseS'_e [Proj 3 2; Proj 3 0; Proj 3 1].

Lemma arity_RoseS :
  arity RoseS_e = ok_arity 3.
Proof.
trivial.
Qed.

Opaque RoseS'_e.

Lemma rec_bounded_RoseS :
  rec_bounded RoseS_e.
Proof.
simpl.
intuition.
apply rec_bounded_RoseS'.
Qed.

Transparent RoseS'_e.

Lemma bs2nat_firstn_false : forall n l,
  bs2nat (firstn n (false :: l)) = 2 * bs2nat (firstn (n-1) l).
Proof.
  intros.
  destruct n.
  simpl.
  rewrite bs2nat_nil; ring.
  simpl firstn.
  rewrite bs2nat_false.
  f_equal.
  f_equal.
  f_equal.
  omega.
Qed.


Lemma bs2nat_app : forall l1 l2,
  bs2nat (l1 ++ l2) = bs2nat l1 + bs2nat (repeat (length l1) false ++ l2).
Proof.
 intros.
 induction l1; simpl.
 rewrite bs2nat_nil; auto.
 rewrite bs2nat_false; simpl.
 destruct a; simpl.
 repeat rewrite bs2nat_true.
 rewrite IHl1; simpl.
 simpl; ring.
 repeat rewrite bs2nat_false.
 rewrite IHl1; simpl.
 simpl; ring.
Qed.

Lemma bs2nat_power : forall l n,
  bs2nat (repeat n false ++ l) = (power 2 n) * (bs2nat l).
Proof.
 induction n; simpl; auto.
 rewrite bs2nat_false; simpl.
 rewrite IHn; ring.
Qed.

Fixpoint RoseS_spec (x y z : bs) :=
  match z with
    | nil => nil
    | _ :: z' =>
      if leb (length z) (length x - length y)
        then false :: RoseS_spec x y z'
        else hd false (skipn (length x - length z) x) :: RoseS_spec x y z'
  end.

Lemma RoseS_spec2_false : forall x y z,
  length z <= length x - length y ->
  bs2nat (RoseS_spec x y z) = 0.
Proof.
 induction z; simpl; intros.
 rewrite bs2nat_nil; trivial.
 case_eq (length x - length y); intros.
 rewrite H0 in H.
 elimtype False; omega.
 case_eq (leb (length z) n); intros.
 apply leb_complete in H1.
 rewrite bs2nat_false, IHz; auto.
 omega.
 apply leb_complete_conv in H1.
 elimtype False; omega.
Qed.

Lemma skipn_roseS : forall x y z,
  bs2nat (skipn (length z) (RoseS_spec x y z)) = 0.
Proof.
  induction z; simpl.
  rewrite bs2nat_nil; auto.
  case_eq (length x - length y); intros; auto.
  case_eq (leb (length z) n); intros; auto.
Qed.

Lemma RoseS_cons : forall x y z b1 b2,
  length z <= length x ->
  RoseS_spec (b1 :: x) (b2 :: y) z = RoseS_spec x y z.
Proof.
  induction z; simpl; trivial; intros.
  case_eq (length x - length y); intros.
  rewrite IHz;[ | omega ]; clear IHz.
  f_equal.
  destruct x; simpl in *.
  elimtype False; omega.
  destruct y; simpl in *.
  discriminate.
  destruct z; simpl.
  rewrite <- minus_n_O; trivial.
  simpl in *.
  cutrewrite (length x - length z = S (length x - S (length z))).
  simpl; trivial.
  omega.
  case_eq (leb (length z) n); intros.
  rewrite IHz; auto.
  omega.
  rewrite IHz.
  f_equal.  
  apply leb_complete_conv in H1.
  destruct x; simpl in *.
  discriminate.
  destruct y; simpl in *.
  elimtype False; omega.
  destruct z; simpl.
  rewrite <- minus_n_O; trivial.
  cutrewrite (length x - length z = S (length x - S (length z))).
  simpl; trivial.
  simpl in *; omega.
  omega.
Qed.

Lemma bs2nat_cons_eq : forall b l1 l2,
  bs2nat l1 = bs2nat l2 ->
  bs2nat (b :: l1) = bs2nat (b :: l2).
Proof.
  intros.
  case b.
  repeat rewrite bs2nat_true; ring [H].
  repeat rewrite bs2nat_false; ring [H].
Qed.

Fixpoint RoseS_spec' (x : bs) (y z : nat) :=
  match z with
    | 0 => nil
    | S z' =>
      if leb z (length x - y)
        then false :: RoseS_spec' x y z'
        else hd false (skipn (length x - z) x) :: RoseS_spec' x y z'
  end.
