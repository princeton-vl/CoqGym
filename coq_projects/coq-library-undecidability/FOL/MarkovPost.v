(** * Post's Theorem and Markov's Principle *)

Require Export DecidableEnumerable.
Require Import ConstructiveEpsilon.

Definition stable P := ~~ P -> P.

Definition MP := forall f : nat -> bool, stable (exists n, f n = true).

Definition mu (p : nat -> Prop) :
  (forall x, dec (p x)) -> ex p -> sig p.
Proof.
  apply constructive_indefinite_ground_description_nat_Acc.
Defined.

Local Notation R p :=
  (fun x y : nat => x = S y /\ ~ p y).

Lemma Acc_ind_dep (A : Type) (R : A -> A -> Prop) (P : forall a, Acc R a -> Prop) :
  (forall x (F : (forall y, R y x -> Acc R y)), (forall y (Hy : R y x), P y (F y Hy)) -> P x (Acc_intro x F))
  -> forall x (h : Acc R x), P x h.
Proof.
  refine (fix f H x h := match h with Acc_intro _ F => _ end).
  apply H. intros y Hy. apply f, H.
Qed.

Notation mu' d H := (proj1_sig (mu d H)).

Lemma mu_least (p : nat -> Prop) (d : forall x, dec (p x)) (H : ex p) :
  forall n, p n -> mu' d H <= n.
Proof.
  intros n H'. unfold mu, constructive_indefinite_ground_description_nat_Acc.
  unfold acc_implies_P_eventually. assert (Hn : 0 <= n) by omega. revert n H' Hn.
  generalize 0, (P_eventually_implies_acc_ex p H). clear H.
  intros k H. pattern k, H. apply (@Acc_ind_dep nat (R p)). clear k H.
  intros k F IH n H1 H2. cbn. destruct (d k) as [H|H]; trivial.
  destruct Fix_F eqn : E. rewrite <- E. apply IH; trivial. clear E.
  apply le_lt_eq_dec in H2 as [H2|H2]; subst; tauto.
Qed.

Definition ldecidable X (p : X -> Prop) :=
  forall x, p x \/ ~ p x.

Lemma weakPost X (p : X -> Prop) : discrete X ->
  ldecidable p -> enumerable p -> enumerable (compl p) -> decidable p.
Proof.
  intros [E] % discrete_iff Hl [f Hf] [g Hg].
  eapply decidable_iff. econstructor. intros x.
  assert (exists n, f n = Some x \/ g n = Some x) by (destruct (Hl x); firstorder).
  destruct (mu (p := fun n => f n = Some x \/ g n = Some x)) as [n HN]; trivial.
  - intros n. exact _.
  - decide (f n = Some x); decide (g n = Some x); firstorder.
Qed.

Lemma MP_to_decMP :
  MP -> (forall p : nat -> Prop, decidable p -> stable (exists n, p n)).
Proof.
  intros H p [d Hd] ?.
  specialize (H (fun x => if d x then true else false)).
  destruct H.
  - intros ?. eapply H0. intros [n]. eapply H. exists n. now eapply Hd in H1 as ->.
  - specialize (Hd x). destruct (d x); try congruence. exists x. now eapply Hd.
Qed.

Lemma decMP_to_eMP :
  (forall p : nat -> Prop, decidable p -> stable (exists n, p n)) -> (forall X (p : X -> Prop), enumerable p -> stable (exists n, p n)).
Proof.
  intros dMP X p [e He] ?. destruct (dMP (fun n => e n <> None)).
  - exists (fun n => match e n with Some _ => true | _ => false end). intros; destruct (e x); firstorder congruence.
  - intros ?. eapply H. intros [x]. eapply H0. eapply He in H1 as [n].
    exists n. congruence.
  - destruct (e x) eqn:E; try congruence. exists x0. eapply He. now exists x. 
Qed.

Lemma eMP_to_MP :
  (forall X (p : X -> Prop), enumerable p -> stable (exists n, p n)) -> MP.
Proof.
  intros eMP f ?. destruct (eMP nat (fun n => f n = true)).
  - eapply dec_count_enum. now exists f. exists Some. eauto.
  - firstorder. 
  - eauto.
Qed.

Lemma MP_enum_stable X (p : X -> Prop) :
  MP -> enumerable p -> discrete X -> forall x, stable (p x).
Proof.
  intros MP [f Hf] [d Hd] x. eapply MP_to_decMP with (p := fun n => f n = Some x) in MP.
  - intros H. rewrite Hf in *. now eapply MP.
  - exists (fun n => match f n with Some x' => d (x, x') | _ => false end).
    intros x0. destruct (f x0). rewrite <- (Hd (x,x1)). split. inversion 1. eauto. intros ->. eauto.
    split; inversion 1.
Qed.

Definition POST' :=
  forall X (p : X -> Prop), discrete X -> enumerable p -> enumerable (fun x => ~ p x) -> ldecidable p.

Theorem MP_Post :
  MP -> POST'.
Proof.
  intros mp X p HX [f Hf] [g Hg].
  cut (forall x, exists n, f n = Some x \/ g n = Some x).
  - intros H x. destruct (H x); firstorder.
  - intros x. apply (MP_to_decMP mp).
    + apply discrete_iff in HX as [H]. apply decidable_iff.
      constructor. intros n. exact _.
    + intros H. assert (H1 : ~ ~ (p x \/ ~ p x)) by tauto. firstorder.
Qed.

Lemma Post_to' :
   POST' -> MP.
Proof.
  intros HP. apply eMP_to_MP. apply decMP_to_eMP.
  intros p [Hp] % decidable_iff H. destruct (HP nat (fun _ => exists n, p n)) with (x:=0); trivial.
  - eapply discrete_iff. econstructor. exact _.
  - change (enumerable (fun m => exists n, (fun (x : nat * nat) => p (snd x)) (m,n))).
    apply projection. eapply dec_count_enum; try apply enumerable_nat_nat.
    apply decidable_iff. constructor. intros [n m]. exact _.
  - exists (fun _ => None). intros x. firstorder congruence.
  - contradiction.
Qed.

Definition POST :=
  forall X (p : X -> Prop), discrete X -> enumerable p -> enumerable (fun x => ~ p x) -> decidable p.

Lemma Post_MP :
  POST <-> MP.
Proof.
  split; intros.
  - intros ?. eapply Post_to'.
    intros ? ? ? ? ? ?. destruct (H X p H0 H1 H2) as [g].
    specialize (H3 x). destruct (g x); firstorder congruence.
  - intros ? ? ? ? ?. eapply weakPost; eauto.
    eapply MP_Post; eauto.
Qed.

  
