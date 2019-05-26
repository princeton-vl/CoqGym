(* Descent.v *)

Require Export Wf_nat.
Require Export ZArith.
Open Scope Z_scope.

Definition R_noet (x y : nat * nat) : Prop :=
  ((fst x) + (snd x) < (fst y) + (snd y))%nat.

Definition f (x : nat * nat) := ((fst x) + (snd x))%nat.

Lemma R_noet_wf : well_founded R_noet.
Proof.
  apply (well_founded_lt_compat _ f R_noet); auto.
Qed.

Lemma noetherian : forall P : nat * nat -> Prop,
  (forall z : nat * nat, (forall y : nat * nat,
    (fst(y) + snd(y) < fst(z) + snd(z))%nat -> P y) -> P z) ->
  forall x : nat * nat, P x.
Proof.
  intros; generalize (well_founded_ind R_noet_wf P); auto.
Qed.

Lemma infinite_descent_nat : forall P : nat * nat -> Prop,
  (forall x : nat * nat, (P x -> exists y : nat * nat,
    (fst(y) + snd(y) < fst(x) + snd(x))%nat /\ P y)) ->
  forall x : nat * nat, ~(P x).
Proof.
  intros; apply (noetherian (fun x => ~(P x))); red; intros; elim (H z H1);
    intros; apply (H0 x0); tauto.
Qed.

Lemma infinite_descent : forall P : Z -> Z -> Prop,
  (forall x1 x2 : Z, 0 <= x1 -> 0 <= x2 ->
    (P x1 x2 -> exists y1 : Z, exists y2 : Z, 0 <= y1 /\ 0 <= y2 /\
    y1 + y2 < x1 + x2 /\ P y1 y2)) ->
  forall x y: Z, 0 <= x -> 0 <= y -> ~(P x y).
Proof.
  intros; elim (Z_of_nat_complete _ H0); clear H0; intros;
    elim (Z_of_nat_complete _ H1); clear H1; intros; rewrite H0; rewrite H1;
    clear H0 H1;
    generalize (infinite_descent_nat
                 (fun c => P (Z_of_nat (fst c)) (Z_of_nat (snd c)))); intro;
    cut (~( P (Z_of_nat (fst (x0, x1))) (Z_of_nat (snd (x0, x1))))); auto.
  apply H0; clear H0; intros;
    elim (H (Z_of_nat (fst x2)) (Z_of_nat (snd x2)) (Zle_0_nat (fst x2))
           (Zle_0_nat (snd x2)) H0); clear H; intros; elim H; clear H; intros;
    intuition; elim (Z_of_nat_complete x3 H1); intros;
    elim (Z_of_nat_complete x4 H); intros; exists (x5, x6); simpl;
    rewrite H3 in H4; rewrite H5 in H4; intuition.
Qed.
