Require Import Bool Arith Div2.
Require Import BellantoniCook.Lib BellantoniCook.Bitstring BellantoniCook.BC.

(** * Zero

  - with any arities (n, s)
*)

Definition zero_e (n s:nat) : BC :=
  comp n s zero nil nil.

Lemma zero_correct n s l1 l2: 
 bs2nat (sem (zero_e n s) l1 l2) = 0.
Proof. intros; simpl; trivial. Qed.

(** * One

  - with any arities (n, s)
*)

Definition one_e n s :=
  comp n s (comp 0 0 (succ true) nil [zero]) nil nil.

(** * Successor

  - arities: (1, 0)
*)

Definition succ_e : BC :=
  rec (one_e 0 0)
      (comp 1 1 (succ true) nil [proj 1 1 0])
      (comp 1 1 (succ false) nil [proj 1 1 1]).

Lemma succ_correct :
  forall n, bs2nat (sem succ_e [n] nil) = S (bs2nat n).
Proof.
 induction n; simpl in *; trivial.
 case a; simpl; [rewrite IHn | ]; ring.
Qed.

Global Opaque succ_e.

(** * Zero predicate

  - arities: (1,0)
*)

Definition is_zero_e : BC :=
  rec (one_e 0 0) (proj 1 1 1) (zero_e 1 1).

Lemma is_zero_correct v :
  bs2bool (sem is_zero_e [v] nil) = true <->
  bs2nat v = 0.
Proof.
 intros; split; induction v; simpl; trivial.
 case a; intros; simpl in *.
 discriminate.
 rewrite IHv; trivial.
 case a; intros; simpl in *.
 contradict H; omega.
 apply IHv; omega.
Qed.

Lemma is_zero_correct_conv v :
  bs2bool (sem is_zero_e [v] nil) = false <->
  bs2nat v <> 0.
Proof.
 intros; split; intros. intro.
 apply is_zero_correct in H0.
 rewrite H in H0; discriminate.
 apply not_true_is_false.
 intro; apply is_zero_correct in H0.
 rewrite H0 in H; auto.
Qed.

Global Opaque is_zero_e.

(** * Predecessor

  - arities: (1,0)
*)

Definition pred_pos_e : BC :=
  rec (zero_e 0 0)
      (comp 1 1 (succ true) nil [proj 1 1 1])
      (comp 1 1 (succ false) nil [proj 1 1 0]).

Lemma pred_pos_correct n :
  bs2nat n <> 0 ->  
  bs2nat (sem pred_pos_e [n] nil) = Peano.pred (bs2nat n).
Proof.
 intros; induction n; simpl in *; trivial.
 destruct a; simpl.
 trivial.
 rewrite IHn.
 destruct (bs2nat n).
 elim H; trivial.
 simpl.
 ring.
 omega.
Qed.

Global Opaque pred_pos_e.

Definition pred_e : BC :=
  comp 1 0 cond 
       nil [is_zero_e; pred_pos_e; zero_e 1 0; pred_pos_e].

Lemma pred_correct n :
  bs2nat (sem pred_e [n] nil) = Peano.pred (bs2nat n).
Proof.
 simpl; intros.
 case_eq (sem is_zero_e [n] nil); intros.
 assert (bs2bool (sem is_zero_e [n] nil) = false).
 rewrite H; simpl; trivial.
 apply is_zero_correct_conv  in H0.
 apply pred_pos_correct; trivial.
 destruct b.
 assert (bs2bool (sem is_zero_e [n] nil) = true).
 rewrite H; simpl; trivial.
 apply is_zero_correct  in H0.
 rewrite H0; simpl; trivial.
 assert (bs2bool (sem is_zero_e [n] nil) = false).
 rewrite H; simpl; trivial.
 apply is_zero_correct_conv  in H0.
 apply pred_pos_correct; trivial.
Qed.

Global Opaque pred_e.

(** * Division by 2

  - arities: (1,0)
*)

Notation div2_e := pred.

Lemma div2_correct : forall v,
  bs2nat (sem pred nil [v]) = div2 (bs2nat v).
Proof.
 intros v; case v; simpl; trivial; intros.
 case b.
 replace (bs2nat l + (bs2nat l + 0)) with (2 * (bs2nat l)).
 rewrite div2_double_plus_one; trivial.
 ring.
 replace (bs2nat l + (bs2nat l + 0)) with (2 * (bs2nat l)).
 rewrite div2_double; trivial.
 omega.
Qed.
