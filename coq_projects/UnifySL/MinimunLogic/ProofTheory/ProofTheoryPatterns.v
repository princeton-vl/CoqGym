Require Import Logic.GeneralLogic.Base.
Require Import Logic.GeneralLogic.ProofTheory.BasicSequentCalculus.
Require Import Logic.MinimunLogic.Syntax.
Require Import Logic.MinimunLogic.ProofTheory.Minimun.
Require Import Logic.MinimunLogic.ProofTheory.RewriteClass.

Local Open Scope logic_base.
Local Open Scope syntax.

Class Adjointness (L: Language) {minL: MinimunLanguage L} (Gamma: ProofTheory L) (prodp funcp: expr -> expr -> expr): Prop := {
  adjoint: forall x y z, |-- prodp x y --> z <-> |-- x --> (funcp y z)
}.

Class Commutativity (L: Language) {minL: MinimunLanguage L} (Gamma: ProofTheory L) (prodp: expr -> expr -> expr): Prop := {
  prodp_comm_impp: forall x y, |-- prodp x y --> prodp y x
}.

Class Monotonicity (L: Language) {minL: MinimunLanguage L} (Gamma: ProofTheory L) (prodp: expr -> expr -> expr): Prop := {
  prodp_mono: forall x1 y1 x2 y2, |-- x1 --> x2 -> |-- y1 --> y2 -> |-- prodp x1 y1 --> prodp x2 y2
}.

Class Associativity (L: Language) {minL: MinimunLanguage L} (Gamma: ProofTheory L) (prodp: expr -> expr -> expr): Prop := {
  prodp_assoc1: forall x y z, |-- prodp x (prodp y z) --> prodp (prodp x y) z;
  prodp_assoc2: forall x y z, |-- prodp (prodp x y) z --> prodp x (prodp y z)
}.

Class LeftUnit (L: Language) {minL: MinimunLanguage L} (Gamma: ProofTheory L) (e: expr) (prodp: expr -> expr -> expr): Prop := {
  left_unit1: forall x, |-- prodp e x --> x;
  left_unit2: forall x, |-- x --> prodp e x
}.

Class RightUnit (L: Language) {minL: MinimunLanguage L} (Gamma: ProofTheory L) (e: expr) (prodp: expr -> expr -> expr): Prop := {
  right_unit1: forall x, |-- prodp x e --> x;
  right_unit2: forall x, |-- x --> prodp x e
}.

Section AdjointTheorems.

Context {L: Language}
        {minL: MinimunLanguage L}
        {Gamma: ProofTheory L}
        {minAX: MinimunAxiomatization L Gamma}
        {prodp funcp: expr -> expr -> expr}
        {Adj: Adjointness L Gamma prodp funcp}.

Lemma prodp_mono1: forall x1 x2 y, |-- x1 --> x2 -> |-- prodp x1 y --> prodp x2 y.
Proof.
  intros.
  apply adjoint.
  rewrite H.
  apply adjoint.
  apply provable_impp_refl.
Qed.

Lemma funcp_mono2: forall x y1 y2, |-- y1 --> y2 -> |-- funcp x y1 --> funcp x y2.
Proof.
  intros.
  apply adjoint.
  rewrite <- H.
  apply adjoint.
  apply provable_impp_refl.
Qed.

Lemma adjoint_modus_ponens:
  forall x y, |-- prodp (funcp x y) x --> y.
Proof.
  intros.
  apply adjoint.
  apply provable_impp_refl.
Qed.

Lemma adjoint_iter:
  forall x xs y,
    |-- fold_left prodp xs x --> y <-> |-- x --> (fold_right funcp y xs).
Proof.
  intros.
  revert x; induction xs; intros; simpl in *.
  + reflexivity.
  + rewrite <- adjoint.
    auto.
Qed.

Section AdjointCommutativeTheorems.

Context {Comm: Commutativity L Gamma prodp}.

Lemma Adjoint2Mono: Monotonicity L Gamma prodp.
Proof.
  constructor.
  intros.
  apply aux_minimun_rule02 with (prodp x2 y1).
  + apply prodp_mono1; auto.
  + rewrite (prodp_comm_impp x2 y1).
    rewrite <- (prodp_comm_impp y2 x2).
    apply prodp_mono1; auto.
Qed.

Lemma funcp_mono: forall x1 y1 x2 y2, |-- x2 --> x1 -> |-- y1 --> y2 -> |-- funcp x1 y1 --> funcp x2 y2.
Proof.
  intros.
  apply adjoint.
  rewrite <- H0.
  rewrite <- (adjoint_modus_ponens x1 y1) at 2.
  apply @prodp_mono.
  + apply Adjoint2Mono.
  + apply provable_impp_refl.
  + auto.
Qed.

End AdjointCommutativeTheorems.

End AdjointTheorems.

Section MonoTheorems.

Context {L: Language}
        {minL: MinimunLanguage L}
        {Gamma: ProofTheory L}
        {minAX: MinimunAxiomatization L Gamma}
        {prodp: expr -> expr -> expr}
        {Mono: Monotonicity L Gamma prodp}.

(* TODO: Maybe this should be abstracted to non-logic level about generic "Proper" vs. fold_left? *)
Lemma fold_left_mono: forall x1 x2 xs1 xs2,
  (Forall2 (fun x1 x2 => |-- x1 --> x2) xs1 xs2) ->
  |-- x1 --> x2 ->
  |-- fold_left prodp xs1 x1 --> fold_left prodp xs2 x2.
Proof.
  intros.
  revert x1 x2 H0.
  induction H; intros.
  + simpl; auto.
  + simpl.
    apply IHForall2.
    apply prodp_mono; auto.
Qed.

Lemma fold_right_mono: forall x1 x2 xs1 xs2,
  (Forall2 (fun x1 x2 => |-- x1 --> x2) xs1 xs2) ->
  |-- x1 --> x2 ->
  |-- fold_right prodp x1 xs1 --> fold_right prodp x2 xs2.
Proof.
  intros.
  induction H; intros.
  + simpl; auto.
  + simpl.
    apply prodp_mono; auto.
Qed.

Lemma fold_left_mono2: forall x1 x2 xs,
  |-- x1 --> x2 ->
  |-- fold_left prodp xs x1 --> fold_left prodp xs x2.
Proof.
  intros.
  apply fold_left_mono; auto.
  induction xs.
  + constructor.
  + constructor; auto.
    apply provable_impp_refl.
Qed.

Lemma fold_right_mono2: forall x1 x2 xs,
  |-- x1 --> x2 ->
  |-- fold_right prodp x1 xs --> fold_right prodp x2 xs.
Proof.
  intros.
  apply fold_right_mono; auto.
  induction xs.
  + constructor.
  + constructor; auto.
    apply provable_impp_refl.
Qed.

End MonoTheorems.

Section AssocTheorems.

Context {L: Language}
        {minL: MinimunLanguage L}
        {Gamma: ProofTheory L}
        {minAX: MinimunAxiomatization L Gamma}
        {prodp: expr -> expr -> expr}
        {e: expr}
        {Mono: Monotonicity L Gamma prodp}
        {Assoc: Associativity L Gamma prodp}
        {LU: LeftUnit L Gamma e prodp}
        {RU: RightUnit L Gamma e prodp}.

(* Since the left unit and right unit can only be identical, we can just assume that directly. *)

Lemma assoc_fold_left_cons: forall x xs,
  |-- fold_left prodp xs (prodp e x) --> prodp x (fold_right prodp e xs).
Proof.
  intros.
  revert x; induction xs; intros.
  + simpl.
    rewrite left_unit1.
    rewrite <- right_unit2.
    apply provable_impp_refl.
  + simpl.
    rewrite <- prodp_assoc2.
    eapply aux_minimun_rule02; [| apply IHxs].
    apply fold_left_mono2.
    apply prodp_assoc2.
Qed.

Lemma assoc_fold_right_cons: forall x xs,
  |-- prodp x (fold_right prodp e xs) --> fold_left prodp xs (prodp e x).
Proof.
  intros.
  revert x; induction xs; intros.
  + simpl.
    rewrite <- left_unit2.
    rewrite right_unit1.
    apply provable_impp_refl.
  + simpl.
    rewrite prodp_assoc1.
    eapply aux_minimun_rule02; [apply IHxs |].
    apply fold_left_mono2.
    apply prodp_assoc1.
Qed.

Lemma assoc_fold_left_fold_right: forall xs,
  |-- fold_left prodp xs e --> fold_right prodp e xs.
Proof.
  intros.
  induction xs.
  + simpl.
    apply provable_impp_refl.
  + simpl.
    apply assoc_fold_left_cons.
Qed.

Lemma assoc_fold_right_fold_left: forall xs,
  |-- fold_right prodp e xs --> fold_left prodp xs e.
Proof.
  intros.
  induction xs.
  + simpl.
    apply provable_impp_refl.
  + simpl.
    apply assoc_fold_right_cons.
Qed.

Lemma assoc_prodp_fold_left: forall xs1 xs2,
  |-- prodp (fold_left prodp xs1 e) (fold_left prodp xs2 e) --> fold_left prodp (xs1 ++ xs2) e.
Proof.
  intros.
  eapply aux_minimun_rule02; [apply prodp_mono; apply assoc_fold_left_fold_right |].
  rewrite <- assoc_fold_right_fold_left.
  induction xs1.
  + simpl.
    rewrite left_unit1.
    apply provable_impp_refl.
  + simpl.
    rewrite prodp_assoc2.
    apply prodp_mono; [apply provable_impp_refl |].
    auto.
Qed.

Lemma assoc_fold_left_app: forall xs1 xs2,
  |-- fold_left prodp (xs1 ++ xs2) e --> prodp (fold_left prodp xs1 e) (fold_left prodp xs2 e).
Proof.
  intros.
  eapply aux_minimun_rule02; [| apply prodp_mono; apply assoc_fold_right_fold_left].
  rewrite assoc_fold_left_fold_right.
  induction xs1.
  + simpl.
    rewrite <- left_unit2.
    apply provable_impp_refl.
  + simpl.
    rewrite <- prodp_assoc1.
    apply prodp_mono; [apply provable_impp_refl |].
    auto.
Qed.

End AssocTheorems.

