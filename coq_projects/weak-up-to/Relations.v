(** * Definition of binary relations, auxiliary results *)
Set Implicit Arguments.

Ltac cgen  H := generalize H; clear H.
Ltac celim H := elim H; clear H.

(** A binary relation is a predicate over pairs of processes *)
Definition relation2(X Y: Type) := X -> Y -> Prop.
Definition relation (X: Type) := relation2 X X.
Definition set(X: Type) := X -> Prop.

Section Definitions.

  Variables X Y Z: Type.
  (** Inclusion *)
  Definition incl: relation (relation2 X Y) := fun R1 R2 => forall x y, R1 x y -> R2 x y.
  (** Extensional equality *)
  Definition eeq: relation (relation2 X Y) := fun R1 R2 => incl R1 R2 /\ incl R2 R1.

  Variable R: relation X.
  Definition reflexive     := forall x, R x x.
  Definition transitive    := forall y x z, R x y -> R y z -> R x z.
  Definition symmetric     := forall x y, R x y -> R y x.
  Definition antisymmetric := forall x y, R x y -> R y x -> x=y.

End Definitions.
Hint Unfold incl.


Section Operators.

  Section O.
    Variables X Y Z: Type.
    Variable Rxy:  relation2 X Y.
    Variable Rxy': relation2 X Y.
    Variable Ryz:  relation2 Y Z.

    (* begin hide *)
    Definition eta2: relation2 X Y := fun x y => Rxy x y.
    (* end hide *)

    (** Transposition, composition, union, union `such that' *)
    Definition trans:  relation2 Y X := fun y x => Rxy x y.
    Definition comp:   relation2 X Z := fun x z => exists2 y, Rxy x y & Ryz y z.
    Definition union2: relation2 X Y := fun x y => Rxy x y \/ Rxy' x y.
    Definition union (I: Type) R: relation2 X Y := fun x y => exists i: I, R i x y.
    Definition union_st (P: set (relation2 X Y)) := fun x y => exists2 R, P R & R x y.

  End O.

  Variable X: Type.
  Variable R: relation X.

  (** Reflexive, transitive closure *) 
  Inductive star: relation X := 
    | star_refl: forall x, star x x
    | S_star: forall y x z, R x y -> star y z -> star x z.

  (** Transitive closure *) 
  Definition plus: relation X := comp R star.

End Operators.
Hint Unfold trans.
Hint Immediate star_refl.


Section Eeq1.

  Variables I X Y Z: Type.
  Variable R' R1': relation2 X Y.
  Variable S': relation2 Y Z.
  Variable R  R1: relation2 X Y.
  Variable S : relation2 Y Z.
  Variables T' T: relation X.
  Variables F' F: I -> relation2 X Y.

  Lemma trans_incl: incl R R' -> incl (trans R) (trans R').
  Proof. auto. Qed.

  Lemma trans_eeq: eeq R R' -> eeq (trans R) (trans R').
  Proof. unfold eeq; intuition. Qed.

  Lemma comp_incl: incl R R' -> incl S S' -> incl (comp R S) (comp R' S').
  Proof. 
    unfold eeq, comp, incl; intuition.
    destruct H1 as [ t ]; exists t; auto.
  Qed.

  Lemma comp_eeq: eeq R R' -> eeq S S' -> eeq (comp R S) (comp R' S').
  Proof. 
    unfold eeq, comp, incl; intuition;
    destruct H0 as [ t ]; exists t; auto.
  Qed.

  Lemma union_incl: (forall i, incl (F i) (F' i)) -> incl (union F) (union F').
  Proof. 
    unfold eeq, union, incl; intuition.
    destruct H0 as [ i ]; exists i; auto. 
  Qed.

  Lemma union_eeq: (forall i, eeq (F i) (F' i)) -> eeq (union F) (union F').
  Proof. 
    unfold eeq, union, incl; intuition;
    destruct H0 as [ i ]; destruct (H i); exists i; auto.
  Qed.

  Lemma union2_incl: incl R R' -> incl R1 R1' -> incl (union2 R R1) (union2 R' R1').
  Proof. 
    unfold incl, union2; intuition.
  Qed.

  Lemma union2_eeq: eeq R R' -> eeq R1 R1' -> eeq (union2 R R1) (union2 R' R1').
  Proof. 
    unfold eeq, union2, incl; intuition.
  Qed.

  Lemma star_incl: incl T T' -> incl (star T) (star T').
  Proof. 
    intros H x y XY; induction XY as [ x | w x y XW WY IH ]; auto;
      apply S_star with w; auto.
  Qed.

  Lemma star_eeq: eeq T T' -> eeq (star T) (star T').
  Proof. 
    intro H; destruct H as [ H1 H2 ]; split; 
      intros x y XY; induction XY as [ x | w x y XW WY IH ]; auto;
	apply S_star with w; auto.
  Qed.

  Lemma plus_incl: incl T T' -> incl (plus T) (plus T').
  Proof. 
    intros H x y XY; destruct XY as [ w XW WY ]; exists w; auto.
    apply (star_incl H); assumption.
  Qed.
  
  Lemma plus_eeq: eeq T T' -> eeq (plus T) (plus T').
  Proof. 
    intro H; elim H; intros H1 H2; split; 
      intros x y XY; destruct XY as [ w XW WY ]; exists w; auto.
    apply (proj1 (star_eeq H)); assumption.
    apply (proj2 (star_eeq H)); assumption.
  Qed.
  
End Eeq1.
Hint Resolve trans_incl.
Hint Resolve comp_incl.
Hint Resolve union_incl.
Hint Resolve star_incl.
Hint Resolve plus_incl.
Hint Resolve trans_eeq.
Hint Resolve comp_eeq.
Hint Resolve union_eeq.
Hint Resolve star_eeq.
Hint Resolve plus_eeq.


Section InclEeq.

  Variables X Y: Type.
  Variables S R T: relation2 X Y.
  
  Lemma incl_refl: incl R R.
  Proof fun x y H => H.
  
  Lemma incl_trans: incl R S -> incl S T -> incl R T.
  Proof. unfold incl; auto. Qed.
  
  Lemma eeq_refl: eeq R R.
  Proof. intros; split; apply incl_refl. Qed.
  
  Lemma eeq_trans: eeq R S -> eeq S T -> eeq R T.
  Proof. unfold eeq, incl; split; intuition. Qed.
  
  Lemma eeq_sym: eeq R S -> eeq S R.
  Proof. unfold eeq, incl; split; intuition. Qed.

End InclEeq.
Hint Immediate incl_refl.
Hint Immediate eeq_refl.
Hint Resolve eeq_sym.


Section star.

  Variable X: Type.
  Variable R: relation X.

  Lemma star1: forall x y, R x y -> star R x y.
  Proof.
    intros x y xRy; eapply S_star; [ apply xRy | apply star_refl ].
  Qed.

  Lemma star_S: forall x y z, star R x y -> R y z -> star R x z.
  Proof.
    intros x y z XY YZ; induction XY.
    apply star1; assumption.
    apply S_star with y; intuition.
  Qed.

  Lemma star_trans: forall x y z, star R x y -> star R y z -> star R x z.
  Proof.
    intros x y z xy; induction xy; intuition.
    apply S_star with y; assumption.
  Qed.

  Lemma plus_star: forall x y, plus R x y -> star R x y.
  Proof.
    intros x y XY; elim XY; intros w XW WY.
    apply S_star with w; intuition.
  Qed.

  Lemma plus_star_plus: forall y x z, plus R x y -> star R y z -> plus R x z.
  Proof.
    intros y x z XY YZ; elim XY; intros w XW WY.
    exists w; intuition.
    apply star_trans with y; assumption.
  Qed.

  Lemma star_plus_plus: forall y x z, star R x y -> plus R y z -> plus R x z.
  Proof.
    induction 1 as [ x | w x y XW WY IH ]; intros YZ.
    assumption.
    exists w; intuition.
    apply plus_star; assumption.
  Qed.

  Lemma plus_trans: forall y x z, plus R x y -> plus R y z -> plus R x z.
  Proof.
    intros y x z XY YZ; apply plus_star_plus with y; try apply plus_star; assumption.
  Qed.

  Lemma plus1: forall x y, R x y -> plus R x y.
  Proof.
    intros x y XY; exists y; intuition.
  Qed.

  Lemma plus_S: forall y x z, star R x y -> R y z -> plus R x z.
  Proof.
    intros y x z XY YZ; apply star_plus_plus with y; try apply plus1; assumption.
  Qed.

  Lemma S_plus: forall y x z, R x y -> star R y z -> plus R x z.
  Proof.
    intros y x z XY YZ; exists y; assumption.
  Qed.

End star.
Hint Resolve star1.
Hint Resolve plus1.
Hint Resolve plus_star.

Ltac destar H w := 
  match type of H with 
    star _ ?x ?y => destruct H as [ x | w x y _H1 _H2 ];
      [ idtac | generalize (S_plus _ _H1 _H2); clear _H1 _H2; intro H ]
    | _ => fail "not a star hypothesis"
  end.

Section Plus_WF.
  Variable X: Set.
  Variable R: relation X.
  Hypothesis Rwf: well_founded (trans R).
  
  Lemma Acc_clos_trans : forall x, Acc (trans R) x -> Acc (trans (plus R)) x.
  Proof.
    induction 1 as [z _ Hz].
    apply Acc_intro.
    intros y Hy.
    elim Hy; intros w Hzw Hwy; clear Hy.
    generalize (Hz _ Hzw); clear Hz Hzw; intro Hw.
    destruct Hwy; intuition.
    apply Acc_inv with x; auto.
    exists y; intuition.
  Qed.
  Hint Resolve Acc_clos_trans.
  
  Theorem plus_wf: well_founded (trans (plus R)).
  Proof.
    intro; auto.
  Qed.
End Plus_WF.


Section Eeq2.

  Variables I X Y Z: Type.
  Variables R R': relation2 X Y.
  Variable  S: relation2 Y Z.
  Variable  T: relation X.
  Variable  F: I -> relation2 X Y.

  Lemma inv_inv: eeq (trans (trans T)) T.
  Proof. 
    intros; unfold trans, eeq, incl; intuition. 
  Qed.
  
  Lemma inv_comp: eeq (trans (comp R S)) (comp (trans S) (trans R)).
  Proof.
    intros; unfold comp, trans, eeq, incl; intuition;
    destruct H as [ t ]; exists t; auto.
  Qed.
  
  Lemma inv_union: eeq (trans (union F)) (union (fun i => trans (F i))).
  Proof.
    intros; unfold union, trans, eeq, incl; intuition.
  Qed.
  
  Lemma inv_star: eeq (trans (star T)) (star (trans T)).
  Proof.
    split.
    unfold incl; induction 1; auto; apply star_S with y; auto.
    unfold incl, trans; induction 1; auto; apply star_S with y; auto.
  Qed.
  
  Lemma inv_plus: eeq (trans (plus T)) (plus (trans T)).
  Proof.
    split.

    unfold trans; intros x y YX; destruct YX as [ w YW WX ].
    cgen YW; cgen y.
    induction WX as [ w | t w x WT TX IH ]; intros y YW.
    apply plus1; apply YW.
    elim IH with w; auto.
    intros t' T'Y WT'.
    exists t'; intuition.
    apply star_S with w; auto. 

    unfold trans; intros x y XY; destruct XY as [ w XW WY ].
    cgen XW; cgen x.
    induction WY as [ w | t w y WT TY IH ]; intros x XW.
    apply plus1; apply XW.
    elim IH with w; auto.
    intros t' T'Y WT'.
    exists t'; intuition.
    apply star_S with w; auto. 
  Qed.

  Lemma inv_union2: eeq (trans (union2 R R')) (union2 (trans R) (trans R')).
  Proof.
    split; (intros x y H; celim H; intro H; [ left | right ]; auto).
  Qed. 

  Lemma comp_assoc: forall W: Type, forall U: relation2 Z W,
    eeq (comp (comp R S) U) (comp R (comp S U)).
  Proof.
    intros W U; split; intros x y H; destruct H as [ w H1 H2 ];
    [ destruct H1 as [ t ] | destruct H2 as [ t ] ]; 
    exists t; auto; exists w; auto.
  Qed.

  Lemma comp_star_star: eeq (comp (star T) (star T)) (star T).
  Proof.
    split; intros x y H.
    destruct H as [ w ]; apply star_trans with w; assumption.
    exists x; auto.
  Qed.

  Lemma comp_plus_star: eeq (comp (plus T) (star T)) (plus T).
  Proof.
    split; intros x y H; destruct H as [ w ].
    apply plus_star_plus with w; assumption.
    exists w; auto.
  Qed.

  Lemma comp_star_plus: eeq (comp (star T) (plus T)) (plus T).
  Proof.
    split; intros x y H; destruct H as [ w ].
    apply star_plus_plus with w; assumption.
    exists x; auto; apply S_plus with w; assumption.
  Qed.

End Eeq2.
Hint Immediate inv_inv.
Hint Immediate inv_comp.
Hint Immediate inv_union.
Hint Immediate inv_star.
Hint Immediate inv_plus.
Hint Immediate comp_assoc.
Hint Immediate comp_star_star.
Hint Immediate comp_plus_star.
Hint Immediate comp_star_plus.
