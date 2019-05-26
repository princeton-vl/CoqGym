(** * General setting for behavioural equivalences *)

Require Export Functions.
Require Export Reductions.
Set Implicit Arguments.

Section Global.

  Variable A: Type.

  Section Sim.

    Variables X Y: Type.
    Variable TX: reduction_t A X.
    Variable TY: reduction_t A Y.
    
    (** More or less generic evolution predicates (Definitions 1.2)  *)
    Definition evolve_1 l R S := diagram (TX l) R (Weak TY l) S.
    Definition evolve_t   R S := evolve_1 (T A) R S.
    Definition evolve_a   R S := forall a, evolve_1 (L a) R S .
    Definition evolve     R S := forall l, evolve_1 l R S.

    (** (Silent) simulation, expansion (Definitions 1.3) *)
    Definition simulation_t R := evolve_t R R.
    Definition simulation   R := evolve   R R.

    (** (Relaxed) expansion  (on one side only) *)
    Definition expansion1   R := diagram_r TX R (EWeak TY) R.
    Definition wexpansion1  R := diagram_r TX R (REWeak TY) R.
    
    Variable F: function X Y.

    (** Monotonicity: Definition 1.5 *)
    Record monotonic: Prop := mkmon {
      mon_m:> increasing F;
      mon_t:  forall R S, evolve_t R S -> incl R S -> evolve_t (F R) (F S);
      mon_a:  forall R S, evolve   R S -> incl R S -> evolve_a (F R) (F S)
    }.
    (** Weak monotonicity: Definition 2.1 *)
    Record wmonotonic: Prop := mkwmon {
      wmon_m:> increasing F;
      wmon_t:  forall R, simulation_t R -> simulation_t (F R);
      wmon_a:  forall R S, simulation_t R -> simulation_t S -> evolve_a R S -> incl R S -> evolve_a (F R) (F S)
    }.

    (** Controlled relations: Definition 3.1 *)
    Variable B: relation X.
    Record controlled: Prop := mkctrl {
      ctrl_t:  forall R, evolve_t R (comp (star B) R) -> simulation_t (comp (star B) R);
      ctrl_a:  forall R S, evolve_t R (comp (star B) R) -> simulation_t S -> 
	                  evolve_a R S -> incl R S -> evolve_a (comp (star B) R) (comp (star B) S)
    }.
    (** Lemma 1.4 (1) *)
    Lemma weak_strong_t: forall R, simulation_t R -> diagram (Weak TX (T A)) R (Weak TY (T A)) R.
    Proof.
      intros R HR; simpl; apply diagram_reverse; apply diagram_star; apply diagram_reverse; exact HR.
    Qed.
    Lemma weak_strong: forall R, simulation R -> diagram_r (Weak TX) R (Weak TY) R.
    Proof.
      intros R HR; generalize (weak_strong_t (HR (T A)));
	intros Ht l; destruct l as [ | a ]; auto.
      intros x x' y Hxx' xRy; destruct Hxx' as [ x1 Hxx1 Hx1x' ]; destruct Hx1x' as [ x2 Hx1x2 Hx2x' ].
      destruct (Ht _ _ _ Hxx1 xRy) as [ y1 Hyy1 x1Ry1 ].
      destruct (HR _ _ _ _ Hx1x2 x1Ry1) as [ y2 Hy1y2 x2Ry2 ].
      destruct (Ht _ _ _ Hx2x' x2Ry2) as [ y' Hy2y' x'Ry' ].
      exists y'; auto.
      apply taus_weak with y1; auto.
      apply weak_taus with y2; auto.
    Qed.

    (** Lemma 1.4 (2) (splitted into several practical results) *)
    Lemma union2_evolve: forall l R R' S, evolve_1 l R S -> evolve_1 l R' S -> evolve_1 l (union2 R R') S.
    Proof.
      intros l R R' S HR HR' x x' y Hxx' xRy; destruct xRy as [ xRy | xRy ].
      destruct (HR _ _ _ Hxx' xRy) as [ y' ]; exists y'; auto.
      destruct (HR' _ _ _ Hxx' xRy) as [ y' ]; exists y'; auto.
    Qed.
    Lemma union2_evolve_left: forall l R S S', evolve_1 l R S -> evolve_1 l R (union2 S S').
    Proof.
      intros l R S S' H x x' y Hxx' xRy; destruct (H _ _ _ Hxx' xRy) as [ y' ]; 
	exists y'; auto; left; auto.
    Qed.
    Lemma union2_evolve_right: forall l R S S', evolve_1 l R S' -> evolve_1 l R (union2 S S').
    Proof.
      intros l R S S' H x x' y Hxx' xRy; destruct (H _ _ _ Hxx' xRy) as [ y' ]; 
	exists y'; auto; right; auto.
    Qed.
    Lemma union_evolve: forall l I R S, 
      (forall i:I, evolve_1 l (R i) S) -> evolve_1 l (union R) S.
    Proof.
      intros l I R S H x x' y Hxx' xRy; destruct xRy as [ i xRy ].
      destruct (H i _ _ _ Hxx' xRy) as [ y' ]; exists y'; auto.     
    Qed.
    Lemma evolve_union: forall l J R S, 
      (exists j:J, evolve_1 l R (S j)) -> evolve_1 l R (union S).
    Proof.
      intros l J R S H x x' y Hxx' xRy.
      destruct H as [ j Hj ]; destruct (Hj _ _ _ Hxx' xRy) as [ y' ].
      exists y'; auto; exists j; auto.     
    Qed.

    (** Evolutions behave like functional arrows (contra/co-variance) *)
    Lemma incl_evolve: forall l R R' S, incl R R' -> evolve_1 l R' S -> evolve_1 l R S.
    Proof.
      intros l R R' S HRR' HR'S x x' y Hxx' xRy.
      destruct (HR'S _ _ _ Hxx' (HRR' _ _ xRy)) as [ y' ]; exists y'; auto.
    Qed.
    Lemma evolve_incl: forall l S R S', incl S S' -> evolve_1 l R S -> evolve_1 l R S'.
    Proof.
      intros l S R S' HSS' HRS x x' y Hxx' xRy.
      destruct (HRS _ _ _ Hxx' xRy) as [ y' ]; exists y'; auto.
    Qed.
      
    (** (Silent) simulations are insensitive to extensional equality *)
    Lemma simulation_eeq: forall R S, eeq R S -> simulation R -> simulation S.
    Proof.
      intros R S HRS H l.
      apply evolve_incl with R.
      apply (proj1 HRS).
      apply incl_evolve with R.
      apply (proj2 HRS).
      apply H.
    Qed.
    Lemma simulation_t_eeq: forall R S, eeq R S -> simulation_t R -> simulation_t S.
    Proof.
      intros R S HRS H; unfold simulation_t, evolve_t.
      apply evolve_incl with R.
      apply (proj1 HRS).
      apply incl_evolve with R.
      apply (proj2 HRS).
      apply H.
    Qed.

  End Sim.

  Section Bi.

    Variables X Y: Type.
    Variable TX: reduction_t A X.
    Variable TY: reduction_t A Y.

    (** Quantifications on both sides of a relation *)
    Definition bisimulation R := simulation  TX TY R /\ simulation TY TX (trans R).
    Definition expansion    R := expansion1  TX TY R /\ simulation TY TX (trans R).
    Definition wexpansion   R := wexpansion1 TX TY R /\ simulation TY TX (trans R).

    (** Definition of the co-inductive relations as `greatest relations such that' *)
    Definition bisim   := union_st bisimulation.
    Definition expand  := union_st expansion.
    Definition wexpand := union_st wexpansion.

    (** Validity of previous definitions *)
    Lemma bisimulation_bisim: bisimulation bisim.
    Proof.
      split; intros l x x' y Hxx' xRy; destruct xRy as [ R HR xRy ];
      [ destruct (proj1 HR _ _ _ _ Hxx' xRy) as [ y' ]
      | destruct (proj2 HR _ _ _ _ Hxx' xRy) as [ y' ] ];
      exists y'; auto; exists R; auto.      
    Qed.
    Lemma expansion_expand: expansion expand.
    Proof.
      split; intros l x x' y Hxx' xRy; destruct xRy as [ R HR xRy ];
      [ destruct (proj1 HR _ _ _ _ Hxx' xRy) as [ y' ]
      | destruct (proj2 HR _ _ _ _ Hxx' xRy) as [ y' ] ];
      exists y'; auto; exists R; auto.      
    Qed.
    Lemma wexpansion_wexpand: wexpansion wexpand.
    Proof.
      split; intros l x x' y Hxx' xRy; destruct xRy as [ R HR xRy ];
      [ destruct (proj1 HR _ _ _ _ Hxx' xRy) as [ y' ]
      | destruct (proj2 HR _ _ _ _ Hxx' xRy) as [ y' ] ];
      exists y'; auto; exists R; auto.      
    Qed.

    (** Inclusions *)
    Lemma expand_wexpand: incl expand wexpand.
    Proof.
      intros P Q H; destruct H as [ R H H' ]; exists R; auto; split.
      intros l x x' y Hxx' xRy; destruct (proj1 H _ _ _ _ Hxx' xRy) as [ y' Hyy' x'Ry' ]; exists y'; auto.
      destruct l; simpl in Hyy'; intuition; exists y'; auto.
      exact (proj2 H).
    Qed.
    Lemma wexpand_bisim: incl wexpand bisim.
    Proof.
      intros P Q H; destruct H as [ R H H' ]; exists R; auto; split.
      intros l x x' y Hxx' xRy; destruct (proj1 H _ _ _ _ Hxx' xRy) as [ y' Hyy' x'Ry' ]; exists y'; auto.
      destruct l; simpl in Hyy'.
      celim Hyy'; intro Hyy'; try destruct Hyy'; auto.
      exists y; auto.
      exact (proj2 H).
    Qed.

  End Bi.


  (** * Composition of simulation, expansion1, wexpansion1 relations *)
  Section Composition.
   
    Variables X Y Z: Type.
    Variable TX: reduction_t A X.
    Variable TY: reduction_t A Y.
    Variable TZ: reduction_t A Z.
    
    Variable R: relation2 X Y.
    Variable S: relation2 Y Z.
    
    Lemma simulation_comp: simulation TX TY R -> simulation TY TZ S -> simulation TX TZ (comp R S).
    Proof.
      intros HR HS l x x' y Hxx' xRy; destruct xRy as [ t xRt tRy ].
      destruct (HR _ _ _ _ Hxx' xRt) as [ t' Htt' x'Rt' ].
      destruct (weak_strong HS _ _ _ _ Htt' tRy) as [ y' Hyy' t'Ry' ].
      exists y'; auto; exists t'; auto.
    Qed.

    Lemma expansion1_comp: expansion1 TX TY R -> expansion1 TY TZ S -> expansion1 TX TZ (comp R S).
    Proof.
      intros HR HS l x x' y Hxx' xRy; destruct xRy as [ t xRt tRy ].
      destruct (HR _ _ _ _ Hxx' xRt) as [ t' Htt' x'Rt' ]; destruct l. 
      celim Htt'; intro Htt'.
      destruct Htt'; exists y; [ left | exists t ]; auto.
      destruct (HS _ _ _ _ Htt' tRy) as [ y' Hyy' t'Ry' ];
	exists y'; auto; exists t'; auto.
      destruct (HS _ _ _ _ Htt' tRy) as [ y' Hyy' t'Ry' ];
	exists y'; auto; exists t'; auto.      
    Qed.

    Let wexpansion1_t: wexpansion1 TY TZ S -> 
      forall x x' y, star (TY (T _)) x x' -> S x y -> exists2 y', star (TZ (T _)) y y' & S x' y'.
    Proof.
      intros H x x' y Hxx'; cgen y; induction Hxx' as [ x | x1 x x' Hxx1 Hx1x' IH ]; intros y xRy.
      exists y; auto.
      destruct (H _ _ _ _ Hxx1 xRy) as [ y1 Hyy1 x1Ry1 ].
      destruct (IH _ x1Ry1) as [ y' Hy1y' x'Ry' ].
      exists y'; auto.
      celim Hyy1; intro Hyy1.
      destruct Hyy1; auto.
      apply S_star with y1; auto.
    Qed.

    Lemma wexpansion1_comp: wexpansion1 TX TY R -> wexpansion1 TY TZ S -> wexpansion1 TX TZ (comp R S).
    Proof.
      intros HR HS l x x' y Hxx' xRy; destruct xRy as [ t xRt tRy ].
      destruct (HR _ _ _ _ Hxx' xRt) as [ t' Htt' x'Rt' ]; destruct l. 
      celim Htt'; intro Htt'.
      destruct Htt'; exists y; [ left | exists t ]; auto.
      destruct (HS _ _ _ _ Htt' tRy) as [ y' Hyy' t'Ry' ];
	exists y'; auto; exists t'; auto.
      destruct Htt' as [ t1 Htt1 Ht1t' ].
      destruct (HS _ _ _ _ Htt1 tRy) as [ y1 Hyy1 t1Ry1 ].
      destruct (wexpansion1_t HS Ht1t' t1Ry1) as [ y' Hy1y' t'Ry' ].
      exists y'.
      destruct Hyy1 as [ y2 ]; exists y2; auto; apply star_trans with y1; auto.
      exists t'; auto.
    Qed.

  End Composition.

  
  (** * Composition of bisimulation, expansion, wexpansion relations *)
  Section BiComposition.
   
    Variables X Y Z: Type.
    Variable TX: reduction_t A X.
    Variable TY: reduction_t A Y.
    Variable TZ: reduction_t A Z.
    
    Variable R: relation2 X Y.
    Variable S: relation2 Y Z.
    
    Lemma bisimulation_comp: bisimulation TX TY R -> bisimulation TY TZ S -> bisimulation TX TZ (comp R S).
    Proof.
      unfold bisimulation; intros HR HS; split.
      apply simulation_comp with TY; intuition.
      eapply simulation_eeq; try (apply eeq_sym; apply inv_comp).
      apply simulation_comp with TY; intuition.
    Qed.

    Lemma expansion_comp: expansion TX TY R -> expansion TY TZ S -> expansion TX TZ (comp R S).
    Proof.
      unfold expansion; intros HR HS; split.
      apply expansion1_comp with TY; intuition.
      eapply simulation_eeq; try (apply eeq_sym; apply inv_comp).
      apply simulation_comp with TY; intuition.
    Qed.

    Lemma wexpansion_comp: wexpansion TX TY R -> wexpansion TY TZ S -> wexpansion TX TZ (comp R S).
    Proof.
      unfold wexpansion; intros HR HS; split.
      apply wexpansion1_comp with TY; intuition.
      eapply simulation_eeq; try (apply eeq_sym; apply inv_comp).
      apply simulation_comp with TY; intuition.
    Qed.

  End BiComposition.

  
  (** * Bisimilarity is an equivalence relation, Expansion and Weak expansion are preorders *)   
  Section Properties.

    Variable X: Type.
    Variable TX: reduction_t A X.

    (** Symmetry of Bisimilarity *)
    Lemma bisim_sym: symmetric (bisim TX TX).
    Proof.
      intros x y H; destruct H as [ R HR H ].
      exists (trans R); auto.
      celim HR; intro HR; split; auto.
    Qed.

    (** Reflexivity of Bisimilarity *)
    Lemma bisim_refl: reflexive (bisim TX TX).
    Proof.
      intro u; exists (eq (A:=X)); auto.
      split; intros l x x' y Hxx' xRy; exists x'; destruct xRy; auto.
    Qed.

    (** Transitivity of Bisimilarity *) 
    Lemma bisim_trans: transitive (bisim TX TX).
    Proof.
      intros y x z XY YZ.
      destruct XY as [ R HR XY ].
      destruct YZ as [ S HS YZ ].
      exists (comp R S).
      apply bisimulation_comp with TX; auto.
      exists y; auto.
    Qed.

    (** Definition of Controlled Bisimulations *)
    Definition bicontrolled R := controlled TX TX R /\ incl R (bisim TX TX).


    (** Reflexivity of Expansion *)
    Lemma expand_refl: reflexive (expand TX TX).
    Proof.
      intro u; exists (eq (A:=X)); auto.
      split; intros l x x' y Hxx' xRy; exists x'; destruct xRy; auto.
      destruct l; auto; right; auto.
    Qed.

    (** Transitivity of Expansion *) 
    Lemma expand_trans: transitive (expand TX TX).
    Proof.
      intros y x z XY YZ.
      destruct XY as [ R HR XY ].
      destruct YZ as [ S HS YZ ].
      exists (comp R S).
      apply expansion_comp with TX; auto.
      exists y; auto.
    Qed.


    (** Reflexivity of Weak Expansion *)
    Lemma wexpand_refl: reflexive (wexpand TX TX).
    Proof.
      intro u; exists (eq (A:=X)); auto.
      split; intros l x x' y Hxx' xRy; exists x'; destruct xRy; auto.
      destruct l; [ right | exists x' ]; auto.
    Qed.

    (** Transitivity of Weak Expansion *) 
    Lemma wexpand_trans: transitive (wexpand TX TX).
    Proof.
      intros y x z XY YZ.
      destruct XY as [ R HR XY ].
      destruct YZ as [ S HS YZ ].
      exists (comp R S).
      apply wexpansion_comp with TX; auto.
      exists y; auto.
    Qed.

  End Properties.

End Global.

Ltac union_evolve n := unfold UIter, simulation_t, evolve_t; apply union_evolve; intro n; apply evolve_union.

