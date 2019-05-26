(** * Results about commutation diagrams *)

Require Export Relations.
Set Implicit Arguments.

(** Definitions *)
Section Def1.
  Variables X X' Y Y': Type.
  Variable RX: relation2 X X'.
  Variable R:  relation2 X Y.
  Variable RY: relation2 Y Y'.
  Variable R': relation2 X' Y'.
  Definition diagram := forall x x' y, RX x x' -> R x y -> exists2 y', RY y y' & R' x' y'.
End Def1.
Section Def2.
  Variable X: Type.
  Variables R S: relation X.
  Definition strong_commute := diagram R S R S.
  Definition local_commute  := diagram R S (star R) (star S).
  Definition semi_commute   := diagram R S (star R) S.
  Definition commute        := diagram (star R) (star S) (star R) (star S).
  Definition confluent      := diagram (star R) (star R) (star R) (star R).
End Def2.

(** Variance w.r.t inclusion *)
Section Incl.
  Variables X X' Y Y': Type.
  Variable RX: relation2 X X'.
  Variable R R':  relation2 X Y.
  Variable RY: relation2 Y Y'.
  Variables S S': relation2 X' Y'.
  Hypothesis H: diagram RX R RY S.
  Hypothesis HR: forall x y, R' x y -> R x y.
  Hypothesis HS: forall x y, S x y -> S' x y.
  Theorem diagram_incl: diagram RX R' RY S'.
  Proof.
    intros x x' y Hxx' xRy.
    elim (H Hxx' (y:=y)); auto.
    intros y' Hyy' x'Ry'.
    exists y'; auto.
  Qed.
End Incl.

(** Reversing diagrams *)
Section Reverse.
  Variables X X' Y Y': Type.
  Variable RX: relation2 X X'.
  Variable R:  relation2 X Y.
  Variable RY: relation2 Y Y'.
  Variable R': relation2 X' Y'.
  Hypothesis H: diagram RX R RY R'.
  Theorem diagram_reverse: diagram R RX R' RY.
  Proof.
    intros x x' y Hxx' xRy.
    elim (H xRy Hxx'); intros y' A B.
    exists y'; assumption.
  Qed.
End Reverse.

(** Composing diagrams *)
Section Compose.
  Variables X Y Z X' Y' Z': Type.
  Variable RY: relation2 Y Y'.
  Variable RX: relation2 X X'.
  Variable R1: relation2 X Y.
  Variable R2: relation2 Y Z.
  Variable RZ: relation2 Z Z'.
  Variable S1: relation2 X' Y'.
  Variable S2: relation2 Y' Z'.
  Hypothesis H1: diagram RX R1 RY S1.
  Hypothesis H2: diagram RY R2 RZ S2.
  Theorem diagram_comp: diagram RX (comp R1 R2) RZ (comp S1 S2).
  Proof.
    intros x x' z Hxx' xRz; destruct xRz as [ y xRy yRz ].
    elim (H1 Hxx' xRy); intros y' Hyy' x'Sy'.
    elim (H2 Hyy' yRz); intros z' Hzz' y'Sz'.
    exists z'; auto.
    exists y'; assumption.
  Qed.
End Compose.

(** Merging diagrams *)
Section Union.
  Variables X Y X' Y' I: Type.
  Variable  RX: relation2 X X'.
  Variables R: I -> relation2 X Y.
  Variable  RY: relation2 Y Y'.
  Variable  S: relation2 X' Y'.
  Hypothesis H: forall i, diagram RX (R i) RY S.
  Theorem diagram_union: diagram RX (union R) RY S.
  Proof.
    intros x x' z Hxx' xRy; destruct xRy as [ i xRy ].
    elim (H Hxx' xRy); intros y' Hyy' x'Sy'.
    exists y'; assumption.
  Qed.
End Union.

(** Iterating one side of a diagram *)
Section Star.
  Variables X X': Type.
  Variable RX: relation2 X X'.
  Variable R: relation X.
  Variable S: relation X'.
  Hypothesis H: diagram RX R RX (star S).
  Theorem diagram_star: diagram RX (star R) RX (star S).
  Proof.
    intros x x' y Hxx' xRy; cgen Hxx'; cgen x'.
    induction xRy as [ x | y x z xRy yRz IH ]; intros x' Hxx'.
    exists x'; auto.
    elim (H Hxx' xRy); intros y' Hyy' x'Sy'.
    elim (IH _ Hyy'); intros z' Hzz' y'Sz'.
    exists z'; auto.
    apply star_trans with y'; assumption.
  Qed.
End Star.

(** Iterating strictly one side of a diagram *)
Section Plus.
  Variables X X': Type.
  Variable RX: relation2 X X'.
  Variable R: relation X.
  Variable S: relation X'.
  Hypothesis HR: diagram RX R RX (plus S).
  Theorem diagram_plus: diagram RX (plus R) RX (plus S).
  Proof.
    intros x x' z Hxx' xRz; destruct xRz as [ y xRy yRz ].
    elim (HR Hxx' xRy); intros y' Hyy' x'Sy'.
    elim diagram_star with X X' RX R S y y' z; auto.
    intros z' Hzz' y'Sz'.
    exists z'; auto; apply plus_star_plus with y'; assumption.
    apply diagram_incl with R (plus S); auto.
  Qed.
End Plus.



(** A First Termination Argument : Subsection 4.1 *)
Section PlusWf.

  Variable X: Set.
  Variable S: relation X.
  Variable TX: relation X.

  Hypothesis HS: diagram TX S (star TX) (plus S).
  Hypothesis Hwf: well_founded (trans S).
  Let Hpwf: well_founded (trans (plus S)) := plus_wf Hwf.

  (** Lemma 4.1 *)
  Lemma diagram_plus_wf: diagram (star TX) (plus S) (star TX) (plus S).
  Proof.
    (* induction horizontale sur la terminaison de S+ *)
    intros x x'; cgen x.
    induction x' as [x' IH ] using (well_founded_ind Hpwf).
    intros x y xTx'; cgen y.
    (* induction verticale sur la dérivation de xT*x' *)
    induction xTx' as [ x | x1 x x' xTx1 x1Ts' IHv ]; intros y xSy.
    exists y; auto.
    destruct xSy as [ w xSw wSy ].
    destruct (HS xTx1 xSw) as [ w1 wTw1 x1Sw1 ].
    elim IHv with w1; auto; intros w' w1Tw' x'Sw'.
    destar wSy z.
    exists w'; auto; apply star_trans with w1; assumption.
    elim IH with w' w y; auto.
    intros y' yTy' w'Ty'.
    exists y'; auto; apply plus_trans with w'; assumption.
    apply star_trans with w1; assumption.
  Qed.

  Variable TX': relation X.
  
  Hypothesis HS': diagram TX' S (comp (star TX) TX') (plus S).

  (** Lemma 4.3 *)
  Lemma diagram_plus_wf_1: strong_commute (comp (star TX) TX') (plus S).
  Proof.
    (* induction horizontale sur la terminaison de S+ *)
    intros x x'; cgen x.
    induction x' as [x' IH ] using (well_founded_ind Hpwf).
    intros x y xTx' xSy; destruct xTx' as [ x1 xTx1 x1Tx' ].
    destruct (diagram_plus_wf xTx1 xSy) as [ y1 yTy1 x1Sy1 ].
    destruct x1Sy1 as [ w1 x1Sw1 w1Sy1 ].
    destruct (HS' x1Tx' x1Sw1) as [ w' w1Tw' x'Sw' ].
    destar w1Sy1 z1.
    destruct w1Tw' as [ w2 w1Tw2 w2Tw' ]; 
      exists w'; auto; exists w2; auto; apply star_trans with w1; auto.
    elim IH with w' w1 y1; auto.
    intros y' y1Ty' w'Sy'; exists y'.
    destruct y1Ty' as [ y2 y1Ty2 y2Ty' ]; 
      exists y2; auto; apply star_trans with y1; auto.
    apply plus_trans with w'; auto.
  Qed.

  Variable Y: Type.
  Variables R R': relation2 X Y.
  Variable TY TY': relation Y.

  Hypothesis HR: diagram TX R (star TY) (comp (star S) R).
  Hypothesis HR': diagram TX' R (comp (star TY) TY') (comp (star S) R').

  (** Proposition 4.4 *)
  Theorem diagram_plus_wf_2: diagram (comp (star TX) TX') (comp (star S) R) (comp (star TY) TY') (comp (star S) R').
  Proof.
    (* induction horizontale sur la terminaison de S+ *)
    intros x x'; cgen x.
    induction x' as [x' IH ] using (well_founded_ind Hpwf).
    intros x y xTx' xSRy; destruct xSRy as [ w xSw wRy ].
    destar xSw z.
     destruct xTx' as [ x1 xTx2 x2Tx' ].
     (* induction horizontale sur la terminaison de S+ *)
     cgen wRy; cgen y; induction xTx2 as [ x | x1 x x2 xTx1 x1Tx2 IHv ]; intros y xRy.
     exact (HR' x2Tx' xRy).
     destruct (HR xTx1 xRy) as [ y1 yTy1 x1SRy1 ].
     destruct x1SRy1 as [ w1 x1Sw1 w1Ry1 ]; destar x1Sw1 z1.
     elim IHv with y1; auto; intros y' y1Ty' x'SRy'.
     destruct y1Ty' as [ y2 ].
     exists y'; auto; exists y2; auto; apply star_trans with y1; auto.
    
     elim diagram_plus_wf_1 with x1 x' w1; auto.
     intros w' w1Tw' x'Sw'.
     elim IH with w' w1 y1; auto.
     intros y' y1Ty' w'SRy'; exists y'; auto.
     destruct y1Ty' as [ y2 ]; exists y2; auto; apply star_trans with y1; auto.
     destruct w'SRy' as [ z' ]; exists z'; auto; apply star_trans with w'; auto.
     exists w1; auto.
     exists x2; auto.
     
    destruct (diagram_plus_wf_1 xTx' xSw) as [ w' wTw' x'Sw' ].
     elim IH with w' w y; auto.
     intros y' yTy' w'SRy'; exists y'; auto.
     destruct w'SRy' as [ z' ]; exists z'; auto; apply star_trans with w'; auto.
     exists w; auto.
  Qed.

End PlusWf.



(** A Generalisation of Newmann's Lemma : Subsection 4.2 *)
Section StarWf.

  Variable X: Set.
  Variable S: relation X.
  Variable TX: relation X.
 
  Hypothesis HS: local_commute TX S.
  Hypothesis Hwf: well_founded (trans (comp (plus S) (plus TX))). 

  Section Gen.
    Variable Y: Type.
    Variable R: relation2 X Y.
    Variable TY: relation Y.
  
    Let SR := comp (star S) R.
    Hypothesis HR: diagram TX R (star TY) SR.
  
    (** Lemma 4.5 *)
    Lemma diagram_star_wf_1: diagram (star TX) SR (star TY) SR.
    Proof.
      apply diagram_reverse.
      apply diagram_star.
      apply diagram_reverse.
      (* induction sur la terminaison de S+TX+ *)
      intro x; induction x as [ x IH ] using (well_founded_ind Hwf).
      intros x' y xTx' xSRy; cgen xTx'; cgen x'.
      destruct xSRy as [ z xSz zRy ].
      (* induction sur la dérivation xS*z *)
      induction xSz as [ x | w x z xSw wSz IHh ]; intros x' xTx'.
      destruct (HR xTx' zRy) as [ y' yTy' x'SRy' ]; exists y'; auto. 
      destruct (HS xTx' xSw) as [ w' wTw' x'Sw' ].
      destruct wTw' as [ w | w1 w w' wTw1 w1Tw' ].
      exists y; auto; exists z; auto; apply star_trans with w; assumption.
      elim IHh with w1; auto. (* 1 *)
      intros z1 zTz1 w1Sz1.
      cut (forall w2, (* 2 *)
        star TX w1 w2 ->
        forall w3 y2,
  	TX w2 w3 -> SR w2 y2 -> exists2 y3, star TY y2 y3 & SR w3 y3).
      clear IH IHh xTx' xSw x wSz wTw1 w; intro IH; cgen w1Sz1; cgen zTz1; cgen z1.
      (* induction sur la dérivation w1T*w' *)
      induction w1Tw' as [ w1 | w2 w1 w' w1Tw2 w2Tw' IHv ]; intros y1 yTy1 w1SRy1.
      destruct w1SRy1 as [ z1 w1Sz1 z1Ry1 ].
      exists y1; auto; exists z1; auto; apply star_trans with w1; auto.
      elim IH with w1 w2 y1; auto; intros y2 y1Ty2 w2Sy2.
      elim IHv with y2; auto.
      intros y' y2Ty' w'SRy'.
      destruct w'SRy' as [ z' w'Sz' z'Ry' ].
      exists y'; auto; exists z'; auto; apply star_trans with z1; assumption.
      intros w3 w2Tw3 w4 y3 w3Tw4 w3SRy3.
      elim IH with w3 w4 y3; auto.
      intros y4 y3Ty4 w4SRy4.
      destruct w4SRy4 as [ z4 w4Sz4 s4Ry4 ].
      exists y4; auto; exists z4; auto; apply star_trans with w3; assumption.
      apply S_star with w2; assumption.
      apply star_trans with y1; assumption.
  
      (* factoriser ces deux petits bouts ??? *)
      
      intros w2 w1Tw2 w3 y2 w2Tw3 w2SRy2; destruct w2SRy2 as [ z2 w2Sz2 z2Ry2 ].
      elim IH with w2 w3 y2; auto.
      intros y3 y2Ty3 w3SRy3.
      exists y3; auto.
      exists w; auto.
      exists w1; assumption.
      exists z2; assumption.
  
      intros w2 wSTw2 w3 y2 w2Tw3 w2SRy2; destruct w2SRy2 as [ z2 w2Sz2 z2Ry2 ].
      destruct wSTw2 as [ u wSu uTw2 ].
      elim IH with w2 w3 y2; auto.
      intros y3 y2Ty3 w3SRy3; destruct w3SRy3 as [ z3 w3Sz3 z3Ry3 ].
      exists y3; auto.
      exists z3; auto.
      exists u; auto; exists w; auto.
      exists z2; assumption.
    Qed.

    Variables X' Y': Type.
    Variable TaX: relation2 X X'.
    Variable TaY: relation2 Y Y'.
    Variable S' : relation2 X' X'.
    Variable R' : relation2 X' Y'.
  
    Let SR' := comp (star S') R'.
    Let TAX := comp (star TX) TaX.
    Let TAY := comp (star TY) TaY.

    Hypothesis HT:  diagram TaX S TAX (star S').
    Hypothesis HRT: diagram TaX R TAY SR'.

    (** Proposition 4.8 *)
    Theorem diagram_star_wf_2: diagram TAX SR TAY SR'.
    Proof.
      apply diagram_reverse.
      apply diagram_incl with TAX (comp (star TY) TAY); auto.
      unfold TAX; eapply diagram_comp;
      apply diagram_reverse.
      apply diagram_star_wf_1.
      (* induction sur la terminaison de S+TX+ *)
      intro x; induction x as [ x IH ] using (well_founded_ind Hwf).
      intros x' y xTx' xSRy; cgen xTx'; cgen x'.
      destruct xSRy as [ z xSz zRy ].
      (* induction sur la dérivation xS*z *)
      induction xSz as [ x | w x z xSw wSz IHh ]; intros x' xTx'.
      destruct (HRT xTx' zRy) as [ y' yTy' x'SRy' ]; exists y'; auto. 
      destruct (HT xTx' xSw) as [ w' wTw' x'Sw' ].
      destruct wTw' as [ wa wTwa waTw' ].
      destruct wTwa as [ w | w1 w wa wTw1 w1Twa ].
       elim IHh with w'; auto.
       intros y' yTy' w'SRy'; exists y'; auto.
       destruct w'SRy' as [ z' ]; exists z'; auto; apply star_trans with w'; assumption.
       intros u Hu; apply IH; auto; destruct Hu as [ t ]; exists t; auto; apply S_plus with w; auto.
    
       elim diagram_star_wf_1 with w wa y.
       intros ya yTya waSRya.
       elim IH with wa w' ya; auto.
       intros y' yaTy' w'SRy'; exists y'.
       destruct yaTy' as [ yb yaTyb ybTy' ]; exists yb; auto; apply star_trans with ya; assumption.
       destruct w'SRy' as [ z' w'Tz' z'Ty' ]; exists z'; auto; apply star_trans with w'; assumption.
       exists w; auto; exists w1; assumption.
       apply S_star with w1; assumption.
       exists z; auto.

      intros x y H; destruct H as [ z H H']; destruct H' as [ t ]; 
	exists t; auto; apply star_trans with z; assumption.
    Qed.
 
  End Gen.

  (** Corollary 4.6 *)
  Lemma diagram_star_wf: commute TX S.
  Proof.
    unfold commute.
    generalize (diagram_star_wf_1 (Y:=X) (R := eq (A:=X)) (TY:=TX)); intro H.
    intros x x' y xTx' xSy.
    elim H with x x' y; auto.
    intros y' yTy' x'Sy'; exists y'; auto.
    destruct x'Sy' as [ t' XT TY ]. 
    destruct TY; assumption.
    intros u u' v UU' UV; destruct UV; exists u'; auto; exists u'; auto.
    exists y; auto.
  Qed.
  
End StarWf.
