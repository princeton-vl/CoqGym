(** * Labelled Transition Systems (LTS) *)

Require Export Diagrams.
Set Implicit Arguments.

Ltac cgen H := generalize H; clear H.

Section Reductions.

  Section R.
    Variables A X: Type.
    Definition reduction := A -> relation X.
    Definition incl_r: relation reduction := fun R1 R2 => forall a, incl (R1 a) (R2 a).
    Definition eeq_r: relation reduction := fun R1 R2 => forall a, eeq (R1 a) (R2 a).
  End R.

  Variable A: Type.

  Section Diagram.
    Variables X Y: Type.
    Definition diagram_r(RX: reduction A X) R (RY: reduction A Y) S := forall a, diagram (RX a) R (RY a) S.
  End Diagram. 

  Section Weak.
  
    (** A `label' is either the silent action, or a visible one *)  
    Inductive Lbl: Type := T | L(a: A).
    Definition reduction_t := reduction Lbl.
  
    Variable X: Type.
    Variable Red: reduction_t X.

    (** Weak transition relation *)  
    Definition Weak: reduction_t X := fun l => 
      match l with 
	| T => star (Red T)
	| L a => comp (star (Red T)) (comp (Red (L a)) (star (Red T)))
      end.

    (** Transition relation for expansion *)
    Definition EWeak: reduction_t X := fun l => 
      match l with 
	| T => union2 (eq (A:=X)) (Red T)
	| L a => Red (L a)
      end.

    (** Transition relation for relaxed expansion *)
    Definition REWeak: reduction_t X := fun l => 
      match l with 
	| T => union2 (eq (A:=X)) (Red T)
	| L a => comp (Red (L a)) (star (Red T))
      end.

    Lemma weak_refl: forall x, Weak T x x.
    Proof. intro x; simpl; auto. Qed.
    Hint Immediate weak_refl.

    Lemma tau_weak: forall y l x z, Red T x y -> Weak l y z -> Weak l x z.
    Proof. 
      intros y l; destruct l; simpl; intros x z XY YZ.
      apply S_star with y; assumption.
      destruct YZ as [ w YW WZ ].
      exists w; auto.
      apply S_star with y; assumption.
    Qed.

    Lemma weak_tau: forall y l x z, Red l x y -> Weak T y z -> Weak l x z.
    Proof.
      intros y l; destruct l; simpl; intros x z XY YZ.
      apply S_star with y; assumption.
      exists x; auto.
      exists y; auto.
    Qed.

    Lemma red_weak: forall l x y, Red l x y -> Weak l x y.
    Proof.
      intros l x y H.
      apply weak_tau with y; auto.
    Qed.

    Lemma taus_weak: forall y l x z, Weak T x y -> Weak l y z -> Weak l x z.
    Proof. 
      intros y l; destruct l; simpl; intros x z XY YZ.
      apply star_trans with y; assumption.
      destruct YZ as [ w YW WZ ].
      exists w; auto.
      apply star_trans with y; assumption.
    Qed.

    Lemma weak_taus: forall y l x z, Weak l x y -> Weak T y z -> Weak l x z.
    Proof.
      intros y l; destruct l; simpl; intros x z XY YZ.
      apply star_trans with y; assumption.
      destruct XY as [ w XW WY ].
      destruct WY as [ t WT TY ].
      exists w; auto.
      exists t; auto.
      apply star_trans with y; assumption.
    Qed.

    (** A useful induction principle: just look at the first action *)
    Theorem Weak_ind:
       forall P: Lbl -> X -> X -> Prop,
       (forall x, P T x x) ->
       (forall y l x z ,
        Red T x y -> Weak l y z -> P l y z -> P l x z) ->
       (forall y a x z,
        Red (L a) x y -> Weak T y z -> P T y z -> P (L a) x z) ->
       forall l x x', Weak l x x' -> P l x x'.
    Proof.
      intros P Hrefl Htau Ha l x x' Hxx'.
      destruct l.
      induction Hxx' as [ x | x1 x x' Hxx1 Hx1x' IH ]; [ apply Hrefl | apply Htau with x1; assumption ].
      destruct Hxx' as [ x1 Hxx1 Hx1x' ].
      destruct Hx1x' as [ x2 Hx1x2 Hx2x' ].
      induction Hxx1 as [ x | w x x1 Hxw Hwx1 IH ].
      apply Ha with x2; simpl; auto.
      clear Hx1x2.
      induction Hx2x' as [ x2 | u x2 x' Hux1 Hx1x' IH ]; [ apply Hrefl | apply Htau with u; assumption ].
      apply Htau with w; auto.
      exists x1; auto; exists x2; assumption.
    Qed.

  End Weak.

End Reductions.


Hint Immediate weak_refl.
Hint Resolve red_weak.

