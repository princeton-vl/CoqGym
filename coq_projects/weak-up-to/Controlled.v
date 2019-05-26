(** * Study of controlled simulations *)

Require Export Theory.
Set Implicit Arguments.

(** ** Relaxed expansion: Subsection 3.2 *)
Section RelaxedExpansion.
  
  Variables A X Y: Type.
  Variable TX: reduction_t A X.
  Variable TY: reduction_t A Y.
  
  Variable B: relation X.
  Hypothesis HB: wexpansion1 TX TX B.

  (** Silent case *)
  Let wexpansion1_ctrl_t: 
  forall R, evolve_t TX TY R (comp (star B) R) -> simulation_t TX TY (comp (star B) R).
  Proof.
    intros R HR x x' y Hxx' xRy; destruct xRy as [ w xRw wRy ].
    cgen Hxx'; cgen x'; induction xRw as [ x | z x w xRz zRw IH ]; intros x' Hxx'.
    apply (HR _ _ _ Hxx' wRy).
    destruct (HB Hxx' xRz) as [ z' Hzz' x'Rz' ].
    celim Hzz'; intro Hzz'.
    destruct Hzz'; exists y; auto; exists w; auto; apply star_trans with z; auto.
    destruct (IH wRy _ Hzz') as [ y' Hyy' z'Ry' ] ; destruct z'Ry' as [ w' ].
    exists y'; auto; exists w'; auto; apply S_star with z'; auto.
  Qed.
  
  (** Lemma 3.10 *)
  Theorem wexpansion1_ctrl: wexpansion1 TX TX B -> controlled TX TY B.
  Proof.
    split; auto.
    intros R S HR HS HRS HRS' a x x' y Hxx' xRy; destruct xRy as [ w xRw wRy ].
    cgen Hxx'; cgen x'; induction xRw as [ x | z x w xRz zRw IH ]; intros x' Hxx'.
    destruct (HRS _ _ _ _ Hxx' wRy) as [ y' Hyy' w'Ry' ]; exists y'; auto; exists x'; auto.
    destruct (HB Hxx' xRz) as [ z' Hzz' x'Rz' ].
    destruct Hzz' as [ z1 Hzz1 Hz1z' ].
    destruct (IH wRy _ Hzz1) as [ y1 Hyy1 z1Ry1 ].
    cut (simulation_t TX TY (comp (star B) S)).
    intro HS'; destruct (weak_strong_t HS' _ Hz1z' z1Ry1) as [ y' Hy1y' z'Ry' ]; exists y'.
    apply weak_taus with y1; auto.
    destruct z'Ry' as [ w' ]; exists w'; auto; apply S_star with z'; auto.
    apply wexpansion1_ctrl_t; auto.
    unfold evolve_t; eapply evolve_incl; try apply HS; intros u v K; exists u; auto.
  Qed.

End RelaxedExpansion.


(** ** Termination Guarantees: Subsection 3.3 *)
Section PlusWf.
  
  Variable A: Type.
  Variable X: Set.
  Variable Y: Type.
  Variable TX: reduction_t A X.
  Variable TY: reduction_t A Y.
  
  Variable B: relation X.
  Hypothesis HB: evolve TX TX B (plus B).
  Hypothesis HB': well_founded (trans B).

  (** Theorem 3.11 *)
  Theorem plus_wf_controlled: controlled TX TY B.
  Proof.
    split.
    intros R HR x x' y Hxx' xRy; destruct xRy as [ w xRw wRy ]; destar xRw z.
    apply (HR _ _ _ Hxx' wRy).
    elim (diagram_plus_wf_2 (HB (l:=T _)) HB') with (eq (A:=X)) Y R R (TY (T A)) (eq (A:=Y)) x x' y; auto.
    intros y' Hyy' x'Ry'; exists y'; auto; destruct Hyy' as [ y1 Hyy1 Hy1y' ]; destruct Hy1y'; auto.
    intros u u' v Huu' uRv; destruct Huu'; exists v; auto; exists v; auto.
    intros u u' v Huu' uRv; destruct Huu'; exists v; auto; (exists v || exists u); auto.
    exists x'; auto.
    exists w; auto.

    intros R S HR HS HRS HRS' a x x' y Hxx' xRy. 
    elim (diagram_plus_wf_2 (HB (l:=T _)) HB') with 
      (comp (TX (L a)) (star (TX (T _)))) Y R S (TY (T _))
      (comp (TY (L a)) (star (TY (T _)))) x x' y; auto.
    intros y' Hyy' x'Ry'; exists y'; auto.
    clear Hxx' xRy x x' y; intros x x' y Hxx' xRy; destruct Hxx' as [ x1 Hxx1 Hx1x' ].
    destruct (HB Hxx1 xRy) as [ y1 Hyy1 x1Ry1 ].
    destruct (diagram_plus_wf (HB (l:=T _)) HB' Hx1x' x1Ry1) as [ y' Hy1y' x'Ry' ].
    exists y'; auto; fold (Weak TX (L a)); apply weak_taus with y1; auto.  
    clear Hxx' xRy x x' y; intros x x' y Hxx' xRy; destruct Hxx' as [ x1 Hxx1 Hx1x' ].
    destruct (HRS _ _ _ _ Hxx1 xRy) as [ y1 Hyy1 x1Ry1 ].
    destruct (weak_strong_t HS _ Hx1x' x1Ry1) as [ y' Hy1y' x'Ry' ]; exists y'.
    fold (Weak TY (L a)); apply weak_taus with y1; auto.  
    exists x'; auto.
    exists x; auto; exists x'; auto.
  Qed.

End PlusWf.


Section StarWf.
  
  Variable A: Type.
  Variable X: Set.
  Variable Y: Type.
  Variable TX: reduction_t A X.
  Variable TY: reduction_t A Y.
  
  Variable B: relation X.
  Hypothesis HB: evolve TX TX B (star B).
  Hypothesis HB': well_founded (trans (comp (plus B) (plus (TX (T _))))).

  (** Theorem 3.12 *)
  Theorem star_wf_controlled: controlled TX TY B.
  Proof.
    split.
    intros R HR; unfold simulation_t, evolve_t, evolve_1, Weak.
    apply diagram_reverse; apply diagram_incl with (star (TX (T _))) (star (TY (T _))); auto; apply diagram_reverse.
    apply diagram_star_wf_1; auto; exact (HB (l:=T _)).

    intros R S HR HS HRS HRS' a; unfold evolve_1.
    apply diagram_reverse; apply diagram_incl with (Weak TX (L a)) (Weak TY (L a)); auto; apply diagram_reverse.
    unfold Weak; apply diagram_star_wf_2; auto; try exact (HB (l:=T _)); 
      intros x x' y Hxx' xRy; destruct Hxx' as [ x1 Hxx1 Hx1x' ]. 
    destruct (HB Hxx1 xRy) as [ y1 Hyy1 x1Ry1 ].
    destruct (diagram_star_wf (HB (l:=T _)) HB' Hx1x' x1Ry1) as [ y' Hy1y' x'Ry' ].
    exists y'; auto; fold (Weak TX (L a)); apply weak_taus with y1; auto.  
    destruct (HRS _ _ _ _ Hxx1 xRy) as [ y1 Hyy1 x1Ry1 ].
    destruct (weak_strong_t HS _ Hx1x' x1Ry1) as [ y' Hy1y' x'Ry' ]; exists y'.
    fold (Weak TY (L a)); apply weak_taus with y1; auto.  
    exists x'; auto.
  Qed.

End StarWf.

