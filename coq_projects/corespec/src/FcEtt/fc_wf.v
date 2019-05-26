Require Import FcEtt.sigs.

Require Export FcEtt.imports.
Require Export FcEtt.ett_inf.
Require Export FcEtt.ett_ind.


Require Import FcEtt.tactics.

Require Import FcEtt.toplevel.


Set Bullet Behavior "Strict Subproofs".
Set Implicit Arguments.


(* ---------------------------------------------------- *)

Lemma ann_ctx_wff_mutual :
  (forall G0 a A, AnnTyping G0 a A -> AnnCtx G0) /\
  (forall G0 phi,   AnnPropWff G0 phi -> AnnCtx G0) /\
  (forall G0 D g p1 p2, AnnIso G0 D g p1 p2 -> AnnCtx G0) /\
  (forall G0 D g A B,   AnnDefEq G0 D g A B -> AnnCtx G0) /\
  (forall G0, AnnCtx G0 -> True).
Proof.
  eapply ann_typing_wff_iso_defeq_mutual; eauto.
Qed.


Definition AnnTyping_AnnCtx  := first  ann_ctx_wff_mutual.
Definition AnnPropWff_AnnCtx := second ann_ctx_wff_mutual.
Definition AnnIso_AnnCtx     := third  ann_ctx_wff_mutual.
Definition AnnDefEq_AnnCtx   := fourth ann_ctx_wff_mutual.

Hint Resolve AnnTyping_AnnCtx AnnPropWff_AnnCtx AnnIso_AnnCtx
     AnnDefEq_AnnCtx : ctx_wff.

(* Look for an extended context that we can derive information from *)
Ltac sort_inversion :=
  let h0 := fresh in
  match goal with
  | [ H : AnnTyping ([(?x,?s)] ++ ?G) _ _ |- _ ] =>
    have h0: AnnCtx (x ~ s ++ G); eauto with ctx_wff;
    inversion h0; subst; auto
  | [ H : AnnDefEq ([(?x,?s)] ++ ?G) _ _ _ |- _ ] =>
    have h0: AnnCtx (x ~ s ++ G); eauto with ctx_wff;
    inversion h0; subst; auto
  | [ H : AnnIso ([(?x,?s)] ++ ?G) _ _ _ |- _ ] =>
    have h0: AnnCtx (x ~ s ++ G); eauto with ctx_wff;
    inversion h0; subst; auto
  end.


(* ---------------------------------------------------- *)

Lemma AnnCtx_uniq G : AnnCtx G -> uniq G.
Proof. by elim=> * //=; apply uniq_cons. Qed.

Hint Resolve AnnCtx_uniq.

(* ---------------------------------------------------- *)

Hint Resolve lc_open_switch_co : lc.

Lemma lc_mutual :
  (forall G0 a A, AnnTyping G0 a A -> lc_tm a /\ lc_tm A) /\
  (forall G0 phi, AnnPropWff G0 phi -> lc_constraint phi) /\
  (forall G0 D g p1 p2, AnnIso G0 D g p1 p2 -> lc_constraint p1 /\ lc_constraint p2 /\ lc_co g) /\
  (forall G0 D g A B,  AnnDefEq G0 D g A B -> lc_tm A /\ lc_tm B /\ lc_co g) /\
  (forall G0, AnnCtx G0 -> forall x s , binds x s G0 -> lc_sort s).
Proof.
  apply ann_typing_wff_iso_defeq_mutual.
  all: pre; basic_solve_n 2; split_hyp.
  all: lc_solve.
Qed.

Definition AnnTyping_lc  := first lc_mutual.
Definition AnnPropWff_lc := second lc_mutual.
Definition AnnIso_lc     := third lc_mutual.
Definition AnnDefEq_lc   := fourth lc_mutual.
Definition AnnCtx_lc     := fifth lc_mutual.

Lemma AnnTyping_lc1 : forall G a A, AnnTyping G a A -> lc_tm a.
Proof.
  intros G a A H. destruct (AnnTyping_lc H); auto.
Qed.
Lemma AnnTyping_lc2 : forall G a A, AnnTyping G a A -> lc_tm A.
  intros G a A H. destruct (AnnTyping_lc H); auto.
Qed.

Lemma AnnIso_lc1 : forall G D g p1 p2, AnnIso G D g p1 p2 -> lc_constraint p1.
Proof. intros. destruct (AnnIso_lc H); auto. Qed.
Lemma AnnIso_lc2 : forall G D g p1 p2, AnnIso G D g p1 p2 -> lc_constraint p2.
Proof. intros. destruct (AnnIso_lc H); split_hyp; auto. Qed.
Lemma AnnIso_lc3 : forall G D g p1 p2, AnnIso G D g p1 p2 -> lc_co g.
Proof. intros. destruct (AnnIso_lc H); split_hyp; auto. Qed.
Lemma AnnDefEq_lc1 : forall G D g A B,  AnnDefEq G D g A B -> lc_tm A.
Proof. intros. destruct (AnnDefEq_lc H); auto. Qed.
Lemma AnnDefEq_lc2 : forall G D g A B,  AnnDefEq G D g A B -> lc_tm B.
Proof. intros. destruct (AnnDefEq_lc H); split_hyp; auto. Qed.
Lemma AnnDefEq_lc3 : forall G D g A B,  AnnDefEq G D g A B -> lc_co g.
Proof. intros. destruct (AnnDefEq_lc H); split_hyp; auto. Qed.

Hint Resolve AnnTyping_lc1 AnnTyping_lc2 AnnIso_lc1 AnnIso_lc2 AnnIso_lc3 AnnDefEq_lc1 AnnDefEq_lc2 AnnDefEq_lc3 AnnCtx_lc : lc.


Lemma AnnToplevel_lc : forall c s, binds c s an_toplevel -> lc_sig_sort s.
Proof. induction AnnSig_an_toplevel.
       intros; lc_solve.
       all: intros; lc_solve_binds; split_hyp; subst; eauto with lc.
Qed.
