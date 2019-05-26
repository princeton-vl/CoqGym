Require Import Logic.GeneralLogic.KripkeModel.
Require Import Logic.ModalLogic.Model.KripkeModel.

Local Open Scope kripke_model.
Import KripkeModelNotation_Intuitionistic.

Class UpwardsClosedOrderedKripkeModel (worlds: Type) {R1: KI.Relation worlds} {R2: KM.Relation worlds} := {
  KM_relation_up: forall m m' n', m <= m' -> KM.Krelation m' n' -> exists n, n <= n' /\ KM.Krelation m n
}.

(* Generator *)

Instance prod_ukmM {A B: Type} (RA1: KI.Relation A) (RB1: KI.Relation B) (RA2: KM.Relation A) (RB2: KM.Relation B) {ukmM_A: UpwardsClosedOrderedKripkeModel A} {ukmM_B: UpwardsClosedOrderedKripkeModel B}: @UpwardsClosedOrderedKripkeModel (A * B) (RelProd RA1 RB1) (RelProd RA2 RB2).
Proof.
  constructor.
  intros [m1 m2] [m1' m2'] [n1 n2] [? ?] [? ?].
  hnf in H, H0, H1, H2; simpl in *.
  destruct (KM_relation_up _ _ _ H H1) as [n1' [? ?]].
  destruct (KM_relation_up _ _ _ H0 H2) as [n2' [? ?]].
  exists (n1', n2').
  split; split; auto.
Qed.

Instance eq1_ukmM (worlds: Type) {R: KM.Relation worlds}: @UpwardsClosedOrderedKripkeModel worlds eq R.
Proof.
  constructor; intros.
  exists n'; simpl in *.
  split.
  + reflexivity.
  + hnf in H; subst; auto.
Qed.

Instance eq2_ukmM (worlds: Type) {R: KI.Relation worlds}: @UpwardsClosedOrderedKripkeModel worlds R eq.
Proof.
  constructor; intros.
  exists m; simpl in *.
  split.
  + hnf in H0; subst; auto.
  + reflexivity.
Qed.
