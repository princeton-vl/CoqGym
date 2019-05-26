Require Import Coq.Sets.Ensembles.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Logic.ChoiceFacts.
Require Import Coq.Logic.ClassicalChoice.
Require Import Logic.lib.RelationPairs_ext.
Require Import Logic.GeneralLogic.KripkeModel.
Require Import Logic.SeparationLogic.Model.SeparationAlgebra.
Require Import Logic.SeparationLogic.Model.OrderedSA.

(***********************************)
(* Separation Algebra Generators   *)
(***********************************)

Section trivialSA.
  Context {worlds: Type}.
  
  Definition trivial_Join: Join worlds:=  (fun a b c => False).

  Definition trivial_SA: @SeparationAlgebra worlds trivial_Join.
  Proof.
    constructor; intuition.
    inversion H.
  Qed.

  (* Trivial algebra is upwards closed *)
  (* Trivial is NOT downwards closed *)
  Definition trivial_uSA {R: Relation worlds}:
    @UpwardsClosedSeparationAlgebra worlds R (trivial_Join).
  Proof.
    intros until m2; intros.
    inversion H.
  Qed.

  (*Increasing*)
  Definition trivial_incrSA: @IncreasingSeparationAlgebra
                           worlds eq trivial_Join.
  Proof.
    constructor; intros.
    hnf; intros.
    inversion H.
  Qed.

  (*Trivial is NOT necessarily unital*)

  (*Trivial is NOT necessarily residual*)
  
End trivialSA.

Section unitSA.
  Definition unit_Join: Join unit:=  (fun _ _ _ => True).

  Definition unit_SA: @SeparationAlgebra unit unit_Join.
  Proof.
    constructor.
    + intros. constructor.
    + intros; exists tt; split; constructor.
  Qed.

  (* Unit algebra is upwards closed *)
  Definition unit_uSA:
    @UpwardsClosedSeparationAlgebra unit eq unit_Join.
  Proof.
    intros; exists tt, tt; intuition.
    + destruct m1; reflexivity.
    + destruct m2; reflexivity.
  Qed.

  (* Unit algebra is downwards closed *)
  Definition unit_dSA:
    @DownwardsClosedSeparationAlgebra unit eq unit_Join.
  Proof.
    intros; exists tt; intuition.
    destruct m; reflexivity.
  Qed.

  (*Increasing*)
  Instance unit_incrSA:
    @IncreasingSeparationAlgebra unit eq unit_Join.
  Proof.
    constructor; intros; hnf; intros.
    destruct n, n'; reflexivity.
  Qed.

  Instance unit_residual:
    @ResidualSeparationAlgebra unit eq unit_Join.
  Proof.
    constructor; intros.
    exists tt; exists tt; split.
    + constructor.
    + destruct n; reflexivity.
  Qed.

  Definition unit_unital:
    @UnitalSeparationAlgebra unit eq unit_Join.
  Proof.
    apply <- (@incr_unital_iff_residual unit eq (eq_preorder unit) unit_Join); auto.
    + apply unit_residual.
    + apply unit_incrSA.
  Qed.

End unitSA.


Section equivSA.
  Context {worlds: Type}.
  
  Definition equiv_Join: Join worlds:=  (fun a b c => a = c /\ b = c).

  Definition equiv_SA: @SeparationAlgebra worlds equiv_Join.
  Proof.
    constructor.
    + intros.
      inversion H.
      split; tauto.
    + intros.
      simpl in *.
      destruct H, H0.
      subst mx my mxy mz.
      exists mxyz; do 2 split; auto.
  Qed.

  (* Identity algebra is upwards closed *)
  (* Identity is NOT downwards closed *)
  Definition identity_uSA {R: Relation worlds}:
    @UpwardsClosedSeparationAlgebra worlds R equiv_Join.
  Proof.
    intros until m2; intros.
    destruct H; subst m1 m2.
    exists n, n; do 2 split; auto.
  Qed.

  Definition equiv_incrSA: @IncreasingSeparationAlgebra
                           worlds eq equiv_Join.
  Proof.
    constructor; intros.
    hnf; intros.
    inversion H; subst.
    constructor.
  Qed.

  Definition ikiM_uSA {R: Relation worlds} {po_R: PreOrder Krelation} {ikiM: IdentityKripkeIntuitionisticModel worlds} {J: Join worlds}: UpwardsClosedSeparationAlgebra worlds.
  Proof.
    intros until m2; intros.
    apply Korder_identity in H0.
    subst n.
    exists m1, m2.
    split; [| split]; auto; reflexivity.
  Qed.

  Definition ikiM_dSA {R: Relation worlds} {po_R: PreOrder Krelation} {ikiM: IdentityKripkeIntuitionisticModel worlds} {J: Join worlds}: DownwardsClosedSeparationAlgebra worlds.
  Proof.
    intros until n2; intros.
    apply Korder_identity in H0.
    apply Korder_identity in H1.
    subst n1 n2.
    exists m.
    split; auto; reflexivity.
  Qed.

  (*Identity is NOT necessarily increasing*)

  (*Identity is NOT necessarily unital*)

  (*Identity is NOT necessarily residual*)
  
End equivSA.

Section optionSA.
  Context (worlds: Type).
  
  Inductive option_join {J: Join worlds}: option worlds -> option worlds -> option worlds -> Prop :=
  | None_None_join: option_join None None None
  | None_Some_join: forall a, option_join None (Some a) (Some a)
  | Some_None_join: forall a, option_join (Some a) None (Some a)
  | Some_Some_join: forall a b c, join a b c -> option_join (Some a) (Some b) (Some c).

  Definition option_Join {SA: Join worlds}: Join (option worlds):=
    (@option_join SA).
  
  Definition option_SA
             {J: Join worlds}
             {SA: SeparationAlgebra worlds}:
    @SeparationAlgebra (option worlds) (option_Join).
  Proof.
    constructor.
    + intros.
      simpl in *.
      destruct H.
    - apply None_None_join.
    - apply Some_None_join.
    - apply None_Some_join.
    - apply Some_Some_join.
      apply join_comm; auto.
      + intros.
        simpl in *.
        inversion H; inversion H0; clear H H0; subst;
        try inversion H4; try inversion H5; try inversion H6; subst;
        try congruence;
        [.. | destruct (join_assoc _ _ _ _ _ H1 H5) as [? [? ?]];
           eexists; split; apply Some_Some_join; eassumption];
        eexists; split;
        try solve [ apply None_None_join | apply Some_None_join
                    | apply None_Some_join | apply Some_Some_join; eauto].
  Qed.

  (* Ordered option Upwards closed *)
  Lemma option_ord_uSA
        {R: Relation worlds}
        {J: Join worlds}
        (uSA: UpwardsClosedSeparationAlgebra worlds):
    @UpwardsClosedSeparationAlgebra (option worlds) (option01_relation Krelation) option_Join.
  Proof.
    hnf; intros.
    inversion H; subst.
    - inversion H0; subst.
      + exists None, None; repeat split; try constructor.
      + exists (Some a), None; repeat split; try constructor.
    - inversion H0; subst.
      exists None, (Some b); repeat split; try constructor; auto.
    - inversion H0; subst.
      exists (Some b), None; repeat split; try constructor; auto.
    - inversion H0; subst.
      destruct
        (uSA  _ _ _ _ H1 H3) as [n1 [n2 [HH1 [HH2 HH3]]]].
      exists (Some n1), (Some n2); repeat split; try constructor; auto.
  Qed.

  (* Downwards closed IF the algebra is increasing*)
  Lemma option_ord_dSA
        {R: Relation worlds}
        {po_R: PreOrder Krelation}
        {J: Join worlds}
        {SA: SeparationAlgebra worlds}
        (dSA: DownwardsClosedSeparationAlgebra worlds)
        {incrSA: IncreasingSeparationAlgebra worlds}:
    @DownwardsClosedSeparationAlgebra (option worlds) (option01_relation Krelation) option_Join.
  Proof.
    hnf; intros.
    inversion H0; [ | | inversion H1]; subst.
    - exists n2; inversion H; subst; split; auto;
      destruct n2; constructor.
    - exists n2; inversion H; subst; split; auto;
      destruct n2; constructor.
      + inversion H1.
      + inversion H; subst.
        apply all_increasing in H6.
        inversion H1; subst.
        transitivity b; auto.
    - exists (Some a); split; try constructor.
      inversion H; subst; auto.
    - exists (Some a); split; try constructor.
      transitivity (Some b); auto.
      inversion H; subst.
      constructor. eapply all_increasing. apply join_comm; eassumption.
    - inversion H; subst.
      destruct (dSA _ _ _ _ _ H6 H2 H5) as [n [HH1 HH2]].
      exists (Some n); split; constructor; auto.
  Qed.

  Lemma option_ord_incr_None
        {R: Relation worlds}
        {po_R: PreOrder Krelation}
        {J: Join worlds}
        {SA: SeparationAlgebra worlds}:
    @increasing (option worlds) (option01_relation Krelation) option_Join None.
  Proof.
    hnf; intros.
    inversion H; subst.
    + constructor.
    + constructor.
      reflexivity.
  Qed.

  Lemma option_ord_res_None
        {R: Relation worlds}
        {po_R: PreOrder Krelation}
        {J: Join worlds}
        {SA: SeparationAlgebra worlds}:
    forall n, @residue (option worlds) (option01_relation Krelation) option_Join n None.
  Proof.
    hnf; intros.
    exists n.
    split.
    + destruct n; constructor.
    + destruct n; constructor.
      reflexivity.
  Qed.

  Lemma option_ord_USA
        {R: Relation worlds}
        {po_R: PreOrder Krelation}
        {J: Join worlds}
        {SA: SeparationAlgebra worlds}:
    @UnitalSeparationAlgebra (option worlds) (option01_relation Krelation) option_Join.
  Proof.
    constructor.
    intros.
    exists None.
    split.
    + apply option_ord_res_None.
    + apply option_ord_incr_None.
  Qed.

  (* Disjoint option Upwards closed*)
  Lemma option_disj_uSA
        {R: Relation worlds}
        {J: Join worlds}
        (uSA: UpwardsClosedSeparationAlgebra worlds):
    @UpwardsClosedSeparationAlgebra (option worlds) (option00_relation Krelation) option_Join.
  Proof.
    hnf; intros.
    inversion H; subst.
    - inversion H0; subst.
      exists None, None; repeat split; try constructor.
    - inversion H0; subst.
      exists None, (Some b); repeat split; try constructor; auto.
    - inversion H0; subst.
      exists (Some b), None; repeat split; try constructor; auto.
    - inversion H0; subst.
      destruct
        (uSA  _ _ _ _ H1 H3) as [n1 [n2 [HH1 [HH2 HH3]]]].
      exists (Some n1), (Some n2); repeat split; try constructor; auto.
  Qed.

  (* Disjointed option Downwards *)
  Lemma option_disj_dSA
        {R: Relation worlds}
        {J: Join worlds}
        {SA: SeparationAlgebra worlds}
        (dSA: DownwardsClosedSeparationAlgebra worlds):
    @DownwardsClosedSeparationAlgebra (option worlds) (option00_relation Krelation) option_Join.
  Proof.
    hnf; intros.
    inversion H0; [ | inversion H1]; subst.
    - exists n2; inversion H; subst; split; auto;
      destruct n2; constructor.
    - exists (Some a); split; try constructor.
      inversion H; subst; auto.
    - inversion H; subst.
      destruct (dSA _ _ _ _ _ H6 H2 H5) as [n [HH1 HH2]].
      exists (Some n); split; constructor; auto.
  Qed.

  Lemma option_disj_incr_None
        {R: Relation worlds}
        {po_R: PreOrder Krelation}
        {J: Join worlds}
        {SA: SeparationAlgebra worlds}:
    @increasing (option worlds) (option00_relation Krelation) option_Join None.
  Proof.
    hnf; intros.
    inversion H; subst.
    + constructor.
    + constructor.
      reflexivity.
  Qed.

  Lemma option_disj_res_None
        {R: Relation worlds}
        {po_R: PreOrder Krelation}
        {J: Join worlds}
        {SA: SeparationAlgebra worlds}:
    forall n, @residue (option worlds) (option00_relation Krelation) option_Join n None.
  Proof.
    hnf; intros.
    exists n.
    split.
    + destruct n; constructor.
    + destruct n; constructor.
      reflexivity.
  Qed.

  Lemma option_disj_USA
        {R: Relation worlds}
        {po_R: PreOrder Krelation}
        {J: Join worlds}
        {SA: SeparationAlgebra worlds}:
    @UnitalSeparationAlgebra (option worlds) (option00_relation Krelation) option_Join.
  Proof.
    constructor.
    intros.
    exists None.
    split.
    + apply option_disj_res_None.
    + apply option_disj_incr_None.
  Qed.

  Lemma option_disj_USA'
        {R: Relation worlds}
        {po_R: PreOrder Krelation}
        {J: Join worlds}
        {SA: SeparationAlgebra worlds}:
    @UnitalSeparationAlgebra' (option worlds) (option00_relation Krelation) option_Join.
  Proof.
    constructor.
    intros.
    exists None.
    split.
    + apply option_disj_res_None.
    + hnf; intros.
      inversion H; subst.
      apply option_disj_incr_None.
  Qed.

End optionSA.

Section exponentialSA.
  Definition fun_Join (A B: Type) {J_B: Join B}: Join (A -> B) :=
    (fun a b c => forall x, join (a x) (b x) (c x)).

  Definition fun_SA
             (A B: Type)
             {Join_B: Join B}
             {SA_B: SeparationAlgebra B}: @SeparationAlgebra (A -> B) (fun_Join A B).
  Proof.
    constructor.
    + intros.
      simpl in *.
      intros x; specialize (H x).
      apply join_comm; auto.
    + intros.
      simpl in *.
      destruct (choice (fun x fx => join (my x) (mz x) fx /\ join (mx x) fx (mxyz x) )) as [myz ?].
    - intros x; specialize (H x); specialize (H0 x).
      apply (join_assoc _ _ _ _ _ H H0); auto.
    - exists myz; firstorder.
  Qed.

  (* Exponential is upwards closed *)
  Lemma fun_uSA 
        (A B: Type)
        {R_B: Relation B}
        {J_B: Join B}
        (uSA_B: UpwardsClosedSeparationAlgebra B):
    @UpwardsClosedSeparationAlgebra (A -> B) (pointwise_relation A R_B) (fun_Join A B).
  Proof.
    hnf; intros.
    unfold join, fun_Join in H.
    unfold Krelation, pointwise_relation in H0.
    destruct (choice (fun x nn => join (fst nn) (snd nn) (n x) /\
                               Krelation (m1 x) (fst nn) /\
                               Krelation (m2 x) (snd nn)))
      as [nn H1].
    intros x.
    destruct (uSA_B (m x) (n x) (m1 x) (m2 x) (H x) (H0 x)) as [x1 [x2 ?]];
      exists (x1, x2); auto.
    exists (fun x => fst (nn x)), (fun x => snd (nn x)).
    simpl; repeat split; intros x; specialize (H1 x); destruct H1 as [H1 [H2 H3]];
    assumption.
  Qed.

  
  (* Exponential is downwards closed *)
  Lemma fun_dSA 
        (A B: Type)
        {R_B: Relation B}
        {J_B: Join B}
        (dSA_B: DownwardsClosedSeparationAlgebra B):
    @DownwardsClosedSeparationAlgebra (A -> B) (pointwise_relation A R_B) (fun_Join A B).
  Proof.
    hnf; intros.
    unfold join, fun_Join in H.
    unfold Krelation, pointwise_relation in H0.
    destruct (choice (fun x n => join (n1 x) (n2 x) (n) /\
                               Krelation (n) (m x)))
      as [n H2].
    intros x.
    destruct (dSA_B (m1 x) (m2 x) (m x) (n1 x) (n2 x) (H x) (H0 x)) as [x1 [x2 ?]]; auto.
    + apply H1.
    + exists x1; auto.
    + exists n; split; hnf; intros x; specialize (H2 x); destruct H2; auto.
  Qed.

  (* Exponential is increasing *)
  Lemma fun_incrSA 
        (A B: Type)
        {R_B: Relation B}
        {J_B: Join B}
        (incr_B: IncreasingSeparationAlgebra B):
    @IncreasingSeparationAlgebra (A -> B) (pointwise_relation A R_B) (fun_Join A B).
  Proof.
    constructor; intros.
    hnf; intros.
    hnf; intros.
    specialize (H a).
    eapply all_increasing; eauto.
  Qed.

  (* Exponential is Unital*)
  Lemma fun_unitSA 
        (A B: Type)
        {R_B: Relation B}
        {J_B: Join B}
        (USA_B: UnitalSeparationAlgebra B):
    @UnitalSeparationAlgebra (A -> B) (pointwise_relation A R_B) (fun_Join A B).
  Proof.
    constructor; intros.
    destruct (choice (fun x mx => residue (n x) mx /\ increasing mx)) as [M HH].
    { intros;
      specialize (incr_exists (n x)); intros [y HH];
      exists y; auto. }
    exists M; split.
    + cut (forall x, residue (n x) (M x)).
      - clear; unfold residue; intros.
        apply choice in H; destruct H as [n' H].
        exists n'; split; hnf; intros x;
        specialize (H x); destruct H; auto.
      - intros x; specialize (HH x); destruct HH; auto.
    + unfold increasing; intros.
      unfold join, fun_Join in H.
      hnf; intros x.
      specialize (HH x); destruct HH as [ _ HH].
      apply HH.
      auto.
  Qed.

  (* Exponential is Unital' *)
  Lemma fun_unitSA' 
        (A B: Type)
        {R_B: Relation B}
        {J_B: Join B}
        (USA'_B: UnitalSeparationAlgebra' B):
    @UnitalSeparationAlgebra' (A -> B) (pointwise_relation A R_B) (fun_Join A B).
  Proof.
    constructor; intros.
    destruct (choice (fun x mx => residue (n x) mx /\ increasing' mx)) as [M HH].
    { intros;
      specialize (incr'_exists (n x)); intros [y HH];
      exists y; auto. }
    exists M; split.
    + cut (forall x, residue (n x) (M x)).
      - clear; unfold residue; intros.
        apply choice in H; destruct H as [n' H].
        exists n'; split; hnf; intros x;
        specialize (H x); destruct H; auto.
      - intros x; specialize (HH x); destruct HH; auto.
    + unfold increasing', increasing; intros.
      unfold join, fun_Join in H.
      hnf; intros x.
      specialize (HH x); destruct HH as [ _ HH].
      eapply (HH _); eauto.
      apply H.
  Qed.

End exponentialSA.

Section sumSA.

  Inductive sum_worlds {worlds1 worlds2}: Type:
    Type:=
  | lw (w:worlds1): sum_worlds
  | rw (w:worlds2): sum_worlds.

  Inductive sum_join {A B: Type} {J1: Join A} {J2: Join B}:
    @sum_worlds A B ->
    @sum_worlds A B ->
    @sum_worlds A B-> Prop :=
  | left_join a b c:
      join a b c ->
      sum_join (lw a) (lw b) (lw c)
  | right_join a b c:
      join a b c ->
      sum_join (rw a) (rw b) (rw c).

  Definition sum_Join (A B: Type) {Join_A: Join A} {Join_B: Join B}: Join (@sum_worlds A B) :=
    (@sum_join A B Join_A Join_B).

  Definition sum_SA (A B: Type) {Join_A: Join A} {Join_B: Join B} {SA_A: SeparationAlgebra A} {SA_B: SeparationAlgebra B}: @SeparationAlgebra (@sum_worlds A B) (sum_Join A B).
  Proof.
    constructor.
    - intros; inversion H;
      constructor; apply join_comm; auto.
    - intros.
      inversion H; subst;
      inversion H0;
      destruct (join_assoc _ _ _ _ _ H1 H3) as [myz [HH1 HH2]].
      + exists (lw myz); split; constructor; auto.
      + exists (rw myz); split; constructor; auto.
  Qed.

End sumSA.

Section productSA.

  Definition prod_Join (A B: Type) {Join_A: Join A} {Join_B: Join B}: Join (A * B) :=
    (fun a b c => join (fst a) (fst b) (fst c) /\ join (snd a) (snd b) (snd c)).

  Definition prod_SA (A B: Type) {Join_A: Join A} {Join_B: Join B} {SA_A: SeparationAlgebra A} {SA_B: SeparationAlgebra B}: @SeparationAlgebra (A * B) (prod_Join A B).
  Proof.
    constructor.
    + intros.
      simpl in *.
      destruct H; split;
      apply join_comm; auto.
    + intros.
      simpl in *.
      destruct H, H0.
      destruct (join_assoc _ _ _ _ _ H H0) as [myz1 [? ?]].
      destruct (join_assoc _ _ _ _ _ H1 H2) as [myz2 [? ?]].
      exists (myz1, myz2).
      do 2 split; auto.
  Qed.

  Lemma prod_uSA
        (A B: Type)
        {R_A: Relation A}
        {R_B: Relation B}
        {Join_A: Join A}
        {Join_B: Join B}
        {dSA_A: UpwardsClosedSeparationAlgebra A}
        {dSA_B: UpwardsClosedSeparationAlgebra B}:
    @UpwardsClosedSeparationAlgebra (A * B) (RelProd R_A R_B) (@prod_Join _ _ Join_A Join_B).
  Proof.
    intros until m2; intros.
    destruct H, H0.
    destruct (join_Korder_up _ _ _ _ H H0) as [fst_n1 [fst_n2 [? [? ?]]]].
    destruct (join_Korder_up _ _ _ _ H1 H2) as [snd_n1 [snd_n2 [? [? ?]]]].
    exists (fst_n1, snd_n1), (fst_n2, snd_n2).
    do 2 split; simpl; auto;
    constructor; auto.
  Qed.

  Lemma prod_dSA
        (A B: Type)
        {R_A: Relation A}
        {R_B: Relation B}
        {Join_A: Join A}
        {Join_B: Join B}
        {uSA_A: DownwardsClosedSeparationAlgebra A}
        {uSA_B: DownwardsClosedSeparationAlgebra B}:
    @DownwardsClosedSeparationAlgebra (A * B) (RelProd R_A R_B) (@prod_Join _ _ Join_A Join_B).
  Proof.
    intros until n2; intros.
    destruct H, H0, H1.
    destruct (join_Korder_down _ _ _ _ _ H H0 H1) as [fst_n [? ?]].
    destruct (join_Korder_down _ _ _ _ _ H2 H3 H4) as [snd_n [? ?]].
    exists (fst_n, snd_n).
    do 2 split; simpl; auto.
  Qed.

  Lemma prod_incr
        (A B: Type)
        {R_A: Relation A}
        {R_B: Relation B}
        {Join_A: Join A}
        {Join_B: Join B}:
    forall (a: A) (b: B),
      increasing a -> increasing b ->
      @increasing _
                   (RelProd R_A R_B)
                   (@prod_Join _ _ Join_A Join_B) (a,b).
  Proof.
    intros. hnf; intros.
    destruct n, n'.
    inversion H1; simpl in *.
    hnf; intros; split.
    apply H; auto.
    apply H0; auto.
  Qed.

  Lemma prod_incrSA
        (A B: Type)
        {R_A: Relation A}
        {R_B: Relation B}
        {Join_A: Join A}
        {Join_B: Join B}
        {incrSA_A: IncreasingSeparationAlgebra A}
        {incrSA_B: IncreasingSeparationAlgebra B}:
    @IncreasingSeparationAlgebra (A * B) (RelProd R_A R_B) (@prod_Join _ _ Join_A Join_B).
  Proof.
    constructor; intros.
    destruct x; apply prod_incr; auto.
    + apply incrSA_A.
    + apply incrSA_B.
  Qed.

  Lemma prod_residualSA
        (A B: Type)
        {R_A: Relation A}
        {R_B: Relation B}
        {Join_A: Join A}
        {Join_B: Join B}
        {residualSA_A: ResidualSeparationAlgebra A}
        {residualSA_B: ResidualSeparationAlgebra B}:
    @ResidualSeparationAlgebra (A * B) (RelProd R_A R_B) (@prod_Join _ _ Join_A Join_B).
  Proof.
    constructor; intros.
    destruct n as [a b].
    inversion residualSA_A;
      inversion residualSA_B.
    destruct (residue_exists a) as [a' [a'' [Ha1 Ha2]]].
    destruct (residue_exists0 b) as [b' [b'' [Hb1 Hb2]]].
    exists (a', b'); hnf; intros.
    exists (a'', b''); hnf; intros;
    split; hnf; intros;
    split; simpl; auto.
  Qed.

  Lemma prod_unitalSA
        (A B: Type)
        {R_A: Relation A}
        {R_B: Relation B}
        {Join_A: Join A}
        {Join_B: Join B}
        {unitalSA_A: UnitalSeparationAlgebra A}
        {unitalSA_B: UnitalSeparationAlgebra B}:
    @UnitalSeparationAlgebra (A * B) (RelProd R_A R_B) (@prod_Join _ _ Join_A Join_B).
  Proof.
    inversion unitalSA_A.
    inversion unitalSA_B.
    constructor; intros.
    - destruct n as [a b].
      destruct (incr_exists a) as [a' [Ha1 Ha2]].
      destruct (incr_exists0 b) as [b' [Hb1 Hb2]].
      exists (a', b'); split; hnf; intros.
      + destruct Ha1 as [a'' [Ha1 Ha3]].
        destruct Hb1 as [b'' [Hb1 Hb3]].
        exists (a'',b''); split; hnf; hnf; intros; try constructor; simpl; auto.
      + destruct n, n'.
        inversion H; simpl in *.
        apply Ha2 in H0.
        apply Hb2 in H1.
        split; auto.
  Qed.

End productSA.

Class SeparationAlgebra_unit (worlds: Type) {J: Join worlds} := {
                                                                 unit: worlds;
                                                                 unit_join: forall n, join n unit n;
                                                                 unit_spec: forall n m, join n unit m -> n = m
                                                               }.

(***********************************)
(* Preorder examples               *)
(***********************************)


(***********************************)
(* dSA uSA examples                *)
(***********************************)


(***********************************)
(* More examples                   *)
(***********************************)

(*
Program Definition nat_le_kiM: KripkeIntuitionisticModel nat := 
  Build_KripkeIntuitionisticModel nat (fun a b => a <= b) _.
Next Obligation.
  constructor; hnf; intros.
  + apply le_n.
  + eapply NPeano.Nat.le_trans; eauto.
Qed.

(* TODO: Probably don't need this one. *)
Program Definition SAu_kiM (worlds: Type) {J: Join worlds} {SA: SeparationAlgebra worlds} {SAu: SeparationAlgebra_unit worlds} : KripkeIntuitionisticModel worlds :=
  Build_KripkeIntuitionisticModel worlds (fun a b => exists b', join b b' a) _.
Next Obligation.
  constructor; hnf; intros.
  + exists unit; apply unit_join.
  + destruct H as [? ?], H0 as [? ?].
    destruct (join_assoc _ _ _ _ _ H0 H) as [? [? ?]].
    exists x2; auto.
Qed.

Definition Heap (addr val: Type): Type := addr -> option val.

Instance Heap_Join (addr val: Type): Join (Heap addr val) :=
  @fun_Join _ _ (@option_Join _ (equiv_Join _)).

Instance Heap_SA (addr val: Type): SeparationAlgebra (Heap addr val) :=
  @fun_SA _ _ _ (@option_SA _ _ (equiv_SA _)).

Instance mfHeap_kiM (addr val: Type): KripkeIntuitionisticModel (Heap addr val) :=
  identity_kiM _.

Instance gcHeap_kiM (addr val: Type): KripkeIntuitionisticModel (Heap addr val) :=
  @fun_kiM _ _ (@option_ord_kiM _ (identity_kiM _)).

Definition Stack (LV val: Type): Type := LV -> val.

Definition StepIndex_kiM (worlds: Type) {po_R: PreOrder Krelation}: KripkeIntuitionisticModel (nat * worlds) := @prod_kiM _ _ nat_le_kiM kiM.

Definition StepIndex_Join (worlds: Type) {J: Join worlds}: Join (nat * worlds) :=
  @prod_Join _ _ (equiv_Join _) J.

Definition StepIndex_SA (worlds: Type) {J: Join worlds} {SA: SeparationAlgebra worlds}:
  @SeparationAlgebra (nat * worlds) (StepIndex_Join worlds) := @prod_SA _ _ _ _ (equiv_SA _) SA.

Definition StepIndex_dSA (worlds: Type) {po_R: PreOrder Krelation}
           {J: Join worlds} {dSA: UpwardsClosedSeparationAlgebra worlds}:
  @UpwardsClosedSeparationAlgebra (nat * worlds) (StepIndex_Join worlds) (StepIndex_kiM worlds):= @prod_dSA _ _ _ _ _ _ (@identity_dSA _ nat_le_kiM) dSA.

 *)