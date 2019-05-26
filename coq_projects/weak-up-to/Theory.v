(** * Correctness of the up-to techniques corresponding to the notions of (weak) monotonic functions, or controlled simulations *)

Require Export WeakMonotonic.
Set Implicit Arguments.

Section Global.

  Variables A X Y: Type.
  Variable TX: reduction_t A X.
  Variable TY: reduction_t A Y.
  
  (** ** Correctness with a monotonic function *)
  Section MonotonicCorrect.

    Variable F: function X Y.
    Hypothesis HF: monotonic TX TY F.

    Variable R: relation2 X Y.
    Hypothesis HR: evolve TX TY R (F R).

    (** predicate for the induction *)
    Let phi: forall n, evolve TX TY (UExp F R n) (UExp F R (S n)).
    Proof.
      intro n; induction n as [ | n IH ].
      intros l x x' y Hxx' xRy.
      destruct (HR Hxx' xRy) as [ y']; exists y'; auto; right; assumption.
      simpl; intro l; apply union2_evolve.
      apply union2_evolve_left; auto.
      apply union2_evolve_right.
      destruct l as [ | a ].
      apply (mon_t HF); [ unfold evolve_t; apply IH | left; auto ].
      apply (mon_a HF); auto; left; auto.
    Qed.

    (** Proposition 1.6 *)
    Theorem monotonic_correct: simulation TX TY (UIter F R).
    Proof. 
      intro l; unfold UIter; union_evolve n; exists (S n); apply phi.
    Qed.

  End MonotonicCorrect.


  (** ** Correctness with a weakly monotonic function *)
  Section WeakMonotonicCorrect.

    Variable F: function X Y.
    Hypothesis HF: wmonotonic TX TY F.

    Variable R: relation2 X Y.
    Hypothesis HRt: simulation_t TX TY R.
    Hypothesis HRa: evolve_a TX TY R (F R).
    
    (** first induction predicate *)
    Let silent: forall n, simulation_t TX TY (UExp F R n).
    Proof.
      intro n; induction n as [ | n IH ]; auto.
      simpl; unfold simulation_t, evolve_t.
      apply union2_evolve.
      apply union2_evolve_left; auto.
      apply union2_evolve_right; apply (wmon_t HF IH). 
    Qed.

    (** correction w.r.t. silent steps *)
    Lemma wmonotonic_correct_t: simulation_t TX TY (UIter F R).
    Proof.
	unfold UIter, simulation_t, evolve_t; union_evolve n; exists n; apply silent.        
    Qed.

   (** second induction predicate *)
    Let visible: forall n, evolve_a TX TY (UExp F R n) (UExp F R (S n)).
    Proof.
      intro n; induction n as [ | n IH ]; intro a; simpl.
      apply union2_evolve_right; apply HRa.
      apply union2_evolve.
      apply union2_evolve_left; auto.
      apply union2_evolve_right. 
      apply (wmon_a HF); auto.
      apply (silent (S n)).
      left; auto.
    Qed.

    (** Proposition 2.2 *)
    Theorem wmonotonic_correct: simulation TX TY (UIter F R).
    Proof.
      intro l; destruct l.
      apply wmonotonic_correct_t.
      unfold UIter; union_evolve n; exists (S n); apply visible.
    Qed.

  End WeakMonotonicCorrect.


  (** ** Correctness with a monotonic function, and a weakly monotonic function *)
  Section UnifiedCorrect.

    Variables F G: function X Y.
    Hypothesis HF : monotonic TX TY F.
    Hypothesis HG : wmonotonic TX TY G.

    Variable R: relation2 X Y.

    Hypothesis HFG: contains F G.  

    Hypothesis HRt: evolve_t TX TY R (F R).
    Hypothesis HRa: evolve_a TX TY R (G R).

    (** first induction predicate *)
    Let pre_silent: forall n, evolve_t TX TY (UExp F R n) (UExp F R (S n)).
    Proof.
      intro n; induction n as [ | n IH ]; simpl; unfold evolve_t.
      apply union2_evolve_right; apply HRt.
      apply union2_evolve.
      apply union2_evolve_left; auto.
      apply union2_evolve_right.  
      apply (mon_t HF); auto; left; auto.
    Qed.
    Let silent: simulation_t TX TY (UIter F R).
    Proof.
	unfold UIter, simulation_t, evolve_t; union_evolve n; exists (S n); apply pre_silent.
    Qed.

    Let HFGn: forall n, incl (UExp F R n) (UExp G R n).
    Proof.
      intro n; induction n as [ | n IH ]; simpl; auto.
      intros x y H; destruct H.
      left; auto.
      right; apply (HFG (mon_m HF IH _ _ H)).
    Qed.

    (** second induction predicate *)
    Let pre_visible: forall n, evolve TX TY (UExp F R n) (UExp G R (S n)).
    Proof.
      intros n; induction n as [ | n IH ]; simpl; intro l.
      destruct l; auto.
      apply evolve_incl with (F R); unfold evolve_1; auto; right; apply HFG; auto.
      apply union2_evolve_right; auto.
      apply union2_evolve; [ apply union2_evolve_left | apply union2_evolve_right ]; auto.
      apply evolve_incl with (F (UExp G R (S n))); auto.
      destruct l.
      apply (mon_t HF (IH _)); left; apply HFGn; auto.
      apply (mon_a HF IH); left; apply HFGn; auto.
    Qed.	
    Let visible: evolve_a TX TY (UIter F R) (UIter G R).
    Proof.
      intro a; unfold UIter; union_evolve n; exists (S n); apply pre_visible.
    Qed.
   
    Let HGFGn: forall n, incl (UExp (UIter G) (UIter G R) n) (UExp (UIter G) R (S n)).
    Proof.
      intro n; induction n as [ | n IH ].
      right; auto.
      intros x y H; celim H; intro H; auto.
      left; auto.
      right; exact (UIter_inc (wmon_m HG) IH H).
    Qed.
    Let HGFG: eeq (UIter (UIter G) (UIter F R)) (UIter (UIter G) R).
    Proof.
      split.
      apply incl_trans with (UIter (UIter G) (UIter G R)).
      repeat apply UIter_inc.
      apply (wmon_m HG).
      intros x y H; destruct H as [ n H ]; exists n; apply HFGn; assumption.
      intros x y H; destruct H as [ n H ]; exists (S n); apply HGFGn; exact H.
      repeat apply UIter_inc; auto; apply (wmon_m HG).
    Qed.

    (** Proposition 2.4 *)
    Theorem unified_correct: simulation TX TY (UIter (UIter G) R).
    Proof.
      eapply simulation_eeq; try apply HGFG. 
      apply wmonotonic_correct.
      apply UIter_wmon; exact HG.
      exact silent.
      intro a; apply evolve_incl with (UIter G R); auto.
      apply UIter_inc; auto; apply (wmon_m HG).
    Qed.

  End UnifiedCorrect.

  (** ** Correctness with a monotonic function, a weakly monotonic function, and a controlled simulation *)
  Section ControlledCorrect.

    Variable B: relation X.
    Hypothesis HB: controlled TX TY B.

    Variables F G: function X Y.
    Hypothesis HF : monotonic TX TY F.
    Hypothesis HG : wmonotonic TX TY G.

    Hypothesis HBF: transparent B F.
    Hypothesis HFG: contains F G. 
    Hypothesis HBG: contains (chaining_l (star B)) G.
(*     Hypothesis HBG: forall R, incl (comp (star B) (G R)) (G R).  *)

    Variable R: relation2 X Y.
    Hypothesis HRt: evolve_t TX TY R (comp (star B) (F R)).
    Hypothesis HRa: evolve_a TX TY R (G R).

    (** first induction predicate *)
    Let pre_silent: forall n, evolve_t TX TY (UExp F R n) (comp (star B) (UExp F R (S n))).
    Proof.
      intro n; induction n as [ | n IH ]; simpl; unfold evolve_t.
      apply evolve_incl with (comp (star B) (F R)); auto;
	intros x y H; destruct H as [ w ]; exists w; auto; right; auto.
      apply union2_evolve.
      eapply evolve_incl; [ apply comp_incl | apply IH ]; auto; left; exact H.
      eapply evolve_incl; try apply (mon_t HF IH).
      eapply incl_trans; try apply HBF; apply comp_incl; auto; right; auto.
      intros x y H; exists x; auto; left; auto.
    Qed.
    Let silent: simulation_t TX TY (comp (star B) (UIter F R)).
    Proof.
      apply (ctrl_t HB).
      unfold UIter, evolve_t; apply union_evolve; intro n.
      apply evolve_incl with (union (fun n: nat => comp (star B) (UExp F R n))). 
      intros x y H; destruct H as [ j H ]; destruct H as [ w ]; exists w; auto; exists j; auto.
      apply evolve_union; exists (S n); apply pre_silent.
    Qed.
    
    Let HFGn: forall n, incl (UExp F R n) (UExp G R n).
    Proof.
      intro n; induction n as [ | n IH ]; simpl; auto.
      intros x y H; destruct H.
      left; auto.
      right; apply (HFG (mon_m HF IH _ _ H)).
    Qed.
    Let HBGGn: forall R n, incl (comp (star B) (UExp G R n)) (UExp G R (S n)).
    Proof. intros RR n x y H; right; apply (HBG H). Qed.

    (** second induction predicate *)
    Let pre_visible: forall n, evolve TX TY (UExp F R n) (UExp G R (2+n)).
    Proof.
      intros n; induction n as [ | n IH ]; intro l.
      destruct l.
      apply evolve_incl with (comp (star B) (F R)); auto.
      intros x y H; destruct H as [ w H H' ]; right; apply HBG; exists w; auto; right; apply (HFG H').
      simpl; apply union2_evolve_left; auto; apply union2_evolve_right; auto.
      simpl; apply union2_evolve.
      apply union2_evolve_left; auto.
      apply union2_evolve_right; auto.
      destruct l; eapply evolve_incl; 
	try (apply (mon_t HF (IH _)) || apply (mon_a HF IH)); auto;
	  apply incl_trans with (UExp G R n); auto; intros x y H; left; left; exact H.
    Qed.	
    Let visible: evolve_a TX TY (comp (star B) (UIter F R)) (UIter G (comp (star B) (UIter F R))).
    Proof.
      intro a; apply evolve_incl with (comp (star B) (UIter G (comp (star B) (UIter F R)))).
      intros x y H; destruct H as [ w XW WY ]; destruct WY as [ n WY ]; exists (S n); apply HBGGn; exists w; auto.
      apply (ctrl_a HB); auto.
      intros x x' y Hxx' xRy; elim (silent (y:=y) Hxx'); [ intros y'; exists y' | exists x ]; auto.
      union_evolve n; exists n; induction n as [ | n IH ]; auto; simpl; apply union2_evolve; 
	[ apply union2_evolve_left; apply IH | apply union2_evolve_right; apply (wmon_t HG IH) ].
      clear a; intro a; union_evolve n; exists (2+n);
	eapply evolve_incl; try apply pre_visible;
	  apply (UExp_inc (wmon_m HG)); intros x; exists x; auto; exists 0; auto.
      intros x; exists 0; exists x; auto.
    Qed.
    
    Let HGGBF: eeq (UIter (UIter G) (comp (star B) (UIter F R))) (UIter (UIter G) R).
    Proof.
      split.
      intros x y H; destruct H as [ n H ]; exists (S n).
      cgen H; cgen y; cgen x; induction n as [ | n IH ]; intros x y H.
      destruct H as [ w XW WY ]; destruct WY as [ n ].
      right; exists (S n); apply HBGGn; exists w; auto; apply HFGn; auto.
      celim H; intro H.
      left; apply IH; auto.
      right; exact (UIter_inc (wmon_m HG) IH H).
      intros x y H; apply (UIter_inc (UIter_inc (wmon_m HG)) (R:=R)); auto.
      intros u v K; exists u; auto; exists 0; auto.
    Qed.

    (** Proposition 3.4 *)
    Theorem controlled_correct: simulation TX TY (UIter (UIter G) R).
    Proof.
      eapply simulation_eeq; try apply HGGBF.
      exact (wmonotonic_correct (UIter_wmon HG) silent visible).
    Qed.

  End ControlledCorrect.

End Global.
