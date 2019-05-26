From Categories Require Import Essentials.Notations.
From Categories Require Import Essentials.Types.
From Categories Require Import Essentials.Facts_Tactics.
From Categories Require Import Category.Main.
From Categories Require Import Basic_Cons.Equalizer.
From Categories Require Import Coq_Cats.Type_Cat.Type_Cat.

Local Obligation Tactic := idtac.

(** Just like in category of sets, in category of types, the equalizer is the type
that reperesents the subset of the cartesian profuct of the domain of the two functions
that is mapped to equal values by both functions. *)
Section Equalizer.
  Context {A B : Type} (f g : A → B).

  Program Definition Type_Cat_Eq : Equalizer Type_Cat f g :=
    {|
      equalizer := {x : A | f x = g x};
      equalizer_morph := @proj1_sig _ _;
      equalizer_morph_ex :=
        fun T eqm H x =>
          exist _ (eqm x) _
    |}.

  Next Obligation.
  Proof.
    extensionality x; destruct x as [x Px]; trivial.
  Qed.  

  Next Obligation.
  Proof.  
    intros T eqm H x.
    apply (fun w => equal_f w x) in H; trivial.
  Qed.

  Next Obligation.
  Proof.
    trivial.
  Qed.

  Next Obligation.
  Proof.
    intros T eqm H1 u u' H2 H3.
    extensionality x.
    apply (fun w => equal_f w x) in H2; cbn in H2.
    apply (fun w => equal_f w x) in H3; cbn in H3.
    destruct (u x) as [ux e]; destruct (u' x) as [ux' e']; cbn in *.
    destruct H2; destruct H3.
    PIR.
    trivial.
  Qed.

End Equalizer.

(** Similar to the category set, in category of types, the coequalizer of two
    functions f,g : A -> B is quotient of B with respect to the equivalence
relation ~. Here, ~ is the equivalence closure of the relation for which we have

x ~ y if and only if ∃z. (f(z) = x) ∧ (g(z) = y)

*)


Program Instance Type_Cat_Has_Equalizers : Has_Equalizers Type_Cat :=
  fun _ _ => Type_Cat_Eq.

Require Import Coq.Relations.Relations Coq.Relations.Relation_Definitions.
Require Import Coq.Logic.ClassicalChoice Coq.Logic.ChoiceFacts.
Require Coq.Logic.ClassicalFacts.

Section CoEqualizer.
  Context {A B : Type} (f g : A → B).

  Local Obligation Tactic := idtac.

  Definition CoEq_rel_base : relation B := fun x y => exists z, f z = x ∧ g z = y.

  Definition CoEq_rel : relation B := clos_refl_sym_trans _ CoEq_rel_base.

  Definition CoEq_rel_refl :=
    equiv_refl _ _ (clos_rst_is_equiv _ CoEq_rel_base).
  Definition CoEq_rel_sym :=
    equiv_sym _ _ (clos_rst_is_equiv _ CoEq_rel_base).
  Definition CoEq_rel_trans :=
    equiv_trans _ _ (clos_rst_is_equiv _ CoEq_rel_base).

  Definition CoEq_Type :=
    {P : B → Prop | exists z : B, P z ∧ (∀ (y : B), (P y ↔ CoEq_rel z y))}.

  Local Axiom ConstructiveIndefiniteDescription_B :
    ConstructiveIndefiniteDescription_on B.

  Definition CoEq_Choice (ct : CoEq_Type) : {x : B | (proj1_sig ct) x}.
  Proof.
    apply ConstructiveIndefiniteDescription_B.
    destruct ct as [P [z [H1 H2]]].
    exists z; trivial.
  Defined.

  Local Axiom PropExt : ClassicalFacts.prop_extensionality.

  Theorem CoEq_rel_Ext : ∀ (x : A) (y : B), CoEq_rel (f x) y = CoEq_rel (g x) y.
  Proof.
    intros x y.
    assert (Hx : CoEq_rel (f x) (g x)).
    {
      constructor 1.
      exists x; split; trivial.
    }
    apply PropExt; split; intros H.
    {
      apply CoEq_rel_sym in Hx.
      apply (CoEq_rel_trans _ _ _ Hx H).
    }
    {
      apply (CoEq_rel_trans _ _ _ Hx H).
    }
  Qed.

  Program Definition Type_Cat_CoEq  : CoEqualizer Type_Cat f g :=
    {|
      equalizer := CoEq_Type
    |}.

  Next Obligation.
  Proof.  
    cbn in *.
    intros x.
    exists (fun y => CoEq_rel x y).
    exists x; split.
    apply CoEq_rel_refl.
    intros z; split; intros; trivial.
  Defined.

  Next Obligation.
  Proof.
    extensionality x.
    apply sig_proof_irrelevance.
    extensionality y.
    apply CoEq_rel_Ext.
  Qed.

  Next Obligation.
  Proof.
    intros T F H x.
    exact (F (proj1_sig (CoEq_Choice x))).
  Defined.

  Next Obligation.
  Proof.
    intros T eqm H.
    unfold Type_Cat_CoEq_obligation_1, Type_Cat_CoEq_obligation_3.
    extensionality x.
    cbn in *.
    match goal with
      [|- eqm (proj1_sig ?A) = _] =>
      destruct A as [z Hz]
    end.
    cbn in *.
    induction Hz as [? ? [w [[] []]]| | |]; auto.
    {
      eapply equal_f in H; eauto.
    }
  Qed.

  Next Obligation.
  Proof.
    intros T eqm H1 u u' H2 H3.
    destruct H3.
    extensionality x.
    destruct x as [P [z [Hz1 Hz2]]].
    unfold Type_Cat_CoEq_obligation_1 in H2; cbn in *.
    apply equal_f with (x := z) in H2.
    match goal with
      [|- ?A = ?B] =>
      match type of H2 with
        ?C = ?D => cutrewrite (A = C); [cutrewrite (B = D)|]; trivial
      end
    end.
    {
      apply f_equal.
      apply sig_proof_irrelevance; cbn.
      extensionality y; apply PropExt; trivial.
    }
    {
      apply f_equal.
      apply sig_proof_irrelevance; cbn.
      extensionality y; apply PropExt; trivial.
    }
  Qed.

End CoEqualizer.

Program Instance Type_Cat_Has_CoEqualizers : Has_CoEqualizers Type_Cat :=
  fun _ _ => Type_Cat_CoEq.
