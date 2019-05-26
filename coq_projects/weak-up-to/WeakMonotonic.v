(** * Study of the class of weakly monotonic functions (Lemma 2.3) *)

Require Export Monotonic.
Set Implicit Arguments.

Section Global.

  Variable A: Type.

  Section A.

    Variables X Y: Type.
    Variable TX: reduction_t A X.
    Variable TY: reduction_t A Y.

    (** weak monotonicity entails monotonicity *)
    Lemma monotonic_wmonotonic: forall F, monotonic TX TY F -> wmonotonic TX TY F.
    Proof.
      intros F HF; split; auto.
      apply (mon_m HF).
      intros R HR; apply (mon_t HF HR); auto.
      intros R S HR HS HRS HRS'; apply (mon_a HF); auto.
      intro l; destruct l; auto.
      apply evolve_incl with R; auto.
    Qed.

    (** transitive, reflexive closure respects weak monotonicity *)
    Lemma star_wmon: wmonotonic TX TX (star (X:=X)).
    Proof.
      split.
      intros R S H x y XY; induction XY as [ x | w x y XW WY IH ]; auto; apply S_star with w; auto.
      intros R HR; unfold simulation_t, evolve_t, evolve_1. 
      apply diagram_reverse; apply diagram_incl with (Weak TX (T _)) (Weak TX (T _)); auto; apply diagram_reverse.
      apply diagram_star; apply diagram_incl with R R; auto; apply weak_strong_t; exact HR.
      intros R S HR HS HRS HRS' a; unfold evolve_1. 
      apply diagram_reverse; apply diagram_incl with (Weak TX (L a)) (Weak TX (L a)); auto; apply diagram_reverse.
      intros x x' y Hxx' xRy; cgen Hxx'; cgen x'; induction xRy as [ x | w x y xRw wRy IH ]; intros x' Hxx'.
      exists x'; auto.
      destruct Hxx' as [ x1 Hxx1 Hx1x' ]; destruct Hx1x' as [ x2 Hx1x2 Hx2x' ].
      destruct (weak_strong_t HR _ Hxx1 xRw) as [ w1 Hww1 x1Rw1 ].
      destruct (HRS _ _ _ _ Hx1x2 x1Rw1) as [ w2 Hw1w2 x2Rw2 ].
      destruct (weak_strong_t HS _ Hx2x' x2Rw2) as [ w' Hw2w' x'Rw' ].
      elim IH with w'.
      intros y' Hyy' w'Ry'; exists y'; auto; apply S_star with w'; auto.
      apply taus_weak with w1; auto; apply weak_taus with w2; auto.
    Qed.

    Variables F G: function X Y.
    Hypothesis HF: wmonotonic TX TY F.
    Hypothesis HG: wmonotonic TX TY G.

    (** Composition respects weak monotonicity *)
    Lemma Comp_wmon: wmonotonic TX TY (Comp G F).
    Proof.
      unfold Comp; split.
      intros R S HRS; apply (wmon_m HG); apply (wmon_m HF); exact HRS.
      intros R HR; exact (wmon_t HG (wmon_t HF HR)).
      intros R S HR HS HRS HRS'; apply (wmon_a HG).
      apply (wmon_t HF HR).
      apply (wmon_t HF HS).
      exact (wmon_a HF HR HS HRS HRS').
      apply (wmon_m HF HRS').      
    Qed.

    (** Binary union respects weak monotonicity *)
    Lemma Union2_wmon: wmonotonic TX TY (Union2 F G).
    Proof.
      unfold Union2; split.
      intros R S HRS x y H; destruct H; [ left; apply (wmon_m HF HRS) | right; apply (wmon_m HG HRS) ]; auto.
      intros R HR x x' y Hxx' xRy; celim xRy; intro xRy;
	[ destruct (wmon_t HF HR _ _ _ Hxx' xRy) as [ y' ] 
        | destruct (wmon_t HG HR _ _ _ Hxx' xRy) as [ y' ] ]; 
	exists y'; auto; [ left | right ]; auto.
      intros R S HR HS HRS HRS' a x x' y Hxx' xRy; celim xRy; intro xRy;
	[ destruct (wmon_a HF HR HS HRS HRS' _ _ _ _ Hxx' xRy) as [ y' ] 
        | destruct (wmon_a HG HR HS HRS HRS' _ _ _ _ Hxx' xRy) as [ y' ] ]; 
	exists y'; auto; [ left | right ]; auto.
    Qed.
    
    Section Union.

      Variable I: Type.
      Variable H: I -> function X Y.
      Hypothesis HH: forall i, wmonotonic TX TY (H i).

      (** Union respects weak monotonicity *)
      Lemma Union_wmon: wmonotonic TX TY (Union H).
      Proof.
	unfold Union; split.
	intros R S HRS x y K; destruct K as [ i ]; exists i; apply (wmon_m (HH i) HRS); auto.
	intros R HR x x' y Hxx' xRy; destruct xRy as [ i xRy ];
	  destruct (wmon_t (HH i) HR _ _ _ Hxx' xRy) as [ y' ]; 
	    exists y'; auto; exists i; auto.
	intros R S HR HS HRS HRS' a x x' y Hxx' xRy; destruct xRy as [ i xRy ];
	  destruct (wmon_a (HH i) HR HS HRS HRS' _ _ _ _ Hxx' xRy) as [ y' ];
	    exists y'; auto; exists i; auto.
      Qed.

    End Union.

  End A.

  Section B.

    Variables X Y: Type.
    Variable TX: reduction_t A X.
    Variable TY: reduction_t A Y.

    Variables F G: function X Y.
    Hypothesis HF: wmonotonic TX TY F.
    Hypothesis HG: wmonotonic TX TY G.

    (** Iteration respects weak monotonicity *)
    Lemma UExp_wmon: forall n, wmonotonic TX TY (fun R => UExp F R n).
    Proof.
      intro n; induction n as [ | n IH ].
      apply (monotonic_wmonotonic (identity_mon TX TY)).
      simpl; fold (Union2 (fun R => UExp F R n) (fun R => F (UExp F R n))).
      apply Union2_wmon; auto.
      fold (Comp F (fun R => UExp F R n)).
      apply Comp_wmon; auto.
    Qed.
    Lemma UIter_wmon: wmonotonic TX TY (UIter F).
    Proof.
      unfold UIter.
      change (fun R => union (UExp F R)) with (Union (fun n => (fun R => UExp F R n))).
      apply Union_wmon; intro i; apply UExp_wmon.
    Qed.

  End B.

  Section C.
  
    Variables X Y: Type.
    Variable TX: reduction_t A X.
    Variable TY: reduction_t A Y.

    Variables F G: function X X.
    Hypothesis HF: wmonotonic TX TX F.
    Hypothesis HG: wmonotonic TX TX G.

    (** Chaining respects weak monotonicity *)
    Lemma Chaining_wmon: wmonotonic TX TX (Chain F G).
    Proof.
      unfold Chain; split.
      intros R S HRS x y H; destruct H as [ w H1 H2 ]; exists w; 
	[ apply (wmon_m HF HRS) | apply (wmon_m HG HRS) ]; auto.
      intros R HR x x' y Hxx' xRy; destruct xRy as [ w xRw wRy ].
      destruct (wmon_t HF HR _ _ _ Hxx' xRw) as [ w' Hww' x'Rw' ].
      destruct (weak_strong_t (wmon_t HG HR) _ Hww' wRy) as [ y' Hyy' x'Ry' ].
      exists y'; auto; exists w'; auto.
      intros R S HR HS HRS HRS' a x x' y Hxx' xRy; destruct xRy as [ w xRw wRy ].
      destruct (wmon_a HF HR HS HRS HRS' _ _ _ _ Hxx' xRw) as [ w' Hww' x'Rw' ].
      destruct Hww' as [ w1 Hww1 Hw1w' ]; destruct Hw1w' as [ w2 Hw1w2 Hw2w' ].
      destruct (weak_strong_t (wmon_t HG HR) _ Hww1 wRy) as [ y1 Hyy1 w1Ry1 ].
      destruct (wmon_a HG HR HS HRS HRS' _ _ _ _ Hw1w2 w1Ry1) as [ y2 Hy1y2 w2Ry2 ].
      destruct (weak_strong_t (wmon_t HG HS) _ Hw2w' w2Ry2) as [ y' Hy2y' w'Ry' ].
      exists y'.
      apply taus_weak with y1; auto; apply weak_taus with y2; auto.
      exists w'; auto.
    Qed.

    (* on doit faire le lemme suivant directement, pour pouvoir utiliser des transitions différentes *)
    Variable L: relation Y.
    Hypothesis HL: simulation TY TY L.
    
    (** The following lemma is not a consequence of the previous one, for typing reasons *)
    Lemma chaing_l_wmon: wmonotonic TY TX (chaining_l L).
    Proof.
      split.
      intros R S HRS x y H; destruct H as [ w ]; exists w; auto.
      intros R HR x x' y Hxx' xRy; destruct xRy as [ w xRw wRy ].
      destruct (HL Hxx' xRw) as [ w' Hww' x'Rw' ].
      destruct (weak_strong_t HR _ Hww' wRy) as [ y' Hyy' x'Ry' ].
      exists y'; auto; exists w'; auto.
      intros R S HR HS HRS HRS' a x x' y Hxx' xRy; destruct xRy as [ w xRw wRy ].
      destruct (HL Hxx' xRw) as [ w' Hww' x'Rw' ].
      destruct Hww' as [ w1 Hww1 Hw1w' ]; destruct Hw1w' as [ w2 Hw1w2 Hw2w' ].
      destruct (weak_strong_t HR _ Hww1 wRy) as [ y1 Hyy1 w1Ry1 ].
      destruct (HRS _ _ _ _ Hw1w2 w1Ry1) as [ y2 Hy1y2 w2Ry2 ].
      destruct (weak_strong_t HS _ Hw2w' w2Ry2) as [ y' Hy2y' w'Ry' ].
      exists y'.
      apply taus_weak with y1; auto; apply weak_taus with y2; auto.
      exists w'; auto.
    Qed.
  
  End C.

End Global.

