Require Import Coq.Bool.Bool.
Require Import Coq.Classes.RelationClasses.
Require Coq.Setoids.Setoid.

Set Implicit Arguments.
Set Strict Implicit.

Class RelDec (T : Type) (equ : T -> T -> Prop) : Type :=
{ rel_dec : T -> T -> bool }.

Arguments rel_dec {_} {equ} {_} _ _.
Arguments rel_dec _ _ _ !x !y.

Class RelDec_Correct T (equ : T -> T -> Prop) (ED : RelDec equ) : Prop :=
{ rel_dec_correct : forall x y : T, rel_dec x y = true <-> equ x y }.

Notation "a ?[ r  ]  b" := (@rel_dec _ r _ a b) (at level 30, b at next level).

Definition eq_dec {T : Type} {ED : RelDec (@eq T)} := rel_dec.

Section neg_rel_dec_correct.
  Context {T} {R:T -> T -> Prop} {RD:RelDec R} {RDC:RelDec_Correct RD}.

  Definition neg_rel_dec_correct : forall {x y}, ~R x y <-> rel_dec x y = false.
  Proof. intros x y. destruct (bool_dec (rel_dec x y) true) ; constructor ; intros ;
    repeat
      match goal with
      | [ |- ~ _ ] => unfold not ; intros
      | [ H1 : ?P, H2 : ~?P |- _ ] => specialize (H2 H1) ; contradiction
      | [ H1 : ?P = true, H2 : ?P = false |- _ ] => rewrite H1 in H2 ; discriminate
      | [ H1 : ?P <> true |- ?P = false ] => apply not_true_is_false ; exact H1
      | [ H1 : ?rel_dec ?a ?b = true, H2 : ~?R ?a ?b |- _ ] =>
          apply rel_dec_correct in H1
      | [ H1 : ?rel_dec ?a ?b = false, H2 : ?R ?a ?b |- _ ] =>
          apply rel_dec_correct in H2
      end.
  Qed.
End neg_rel_dec_correct.

Section rel_dec_p.
  Context {T} {R:T -> T -> Prop} {RD:RelDec R} {RDC:RelDec_Correct RD}.

  Definition rel_dec_p (x:T) (y:T) : {R x y} + {~R x y}.
  Proof. destruct (bool_dec (rel_dec x y) true) as [H | H].
    apply rel_dec_correct in H ; eauto.
    apply not_true_is_false in H ; apply neg_rel_dec_correct in H ; eauto.
  Qed.

  Definition neg_rel_dec_p (x:T) (y:T) : {~R x y} + {R x y}.
  Proof. destruct (rel_dec_p x y) ; [ right | left ] ; auto. Qed.
End rel_dec_p.

Section lemmas.
  Variable T : Type.
  Variable eqt : T -> T -> Prop.
  Variable r : RelDec eqt.
  Variable rc : RelDec_Correct r.

  Theorem rel_dec_eq_true : forall x y,
    eqt x y -> rel_dec x y = true.
  Proof.
    intros. eapply rel_dec_correct in H. assumption.
  Qed.

  Theorem rel_dec_neq_false : forall x y,
    ~eqt x y -> rel_dec x y = false.
  Proof.
    intros. remember (x ?[ eqt ] y).
    symmetry in Heqb.
    destruct b; try reflexivity.
    exfalso. eapply (@rel_dec_correct _ _ _ rc) in Heqb. auto.
  Qed.

  Theorem rel_dec_sym : Symmetric eqt -> forall x y,
    x ?[ eqt ] y = y ?[ eqt ] x.
  Proof.
    intros.
    remember (x ?[ eqt ] y); remember (y ?[ eqt ] x); intuition.
    destruct b; destruct b0; auto.
    { symmetry in Heqb; symmetry in Heqb0.
      eapply (@rel_dec_correct _ _ _ rc) in Heqb.
      symmetry in Heqb.
      eapply (@rel_dec_correct _ _ _ rc) in Heqb.
      congruence. }
    { symmetry in Heqb; symmetry in Heqb0.
      eapply (@rel_dec_correct _ _ _ rc) in Heqb0.
      symmetry in Heqb0.
      eapply (@rel_dec_correct _ _ _ rc) in Heqb0.
      congruence. }
  Qed.
End lemmas.

Section RelDec_from_dec.
  Context {T} (R : T -> T -> Prop).
  Variable (f : forall a b : T, {R a b} + {~R a b}).
  Definition RelDec_from_dec
  : RelDec R :=
  {| rel_dec := fun a b =>
                  match f a b with
                  | left _ => true
                  | right _ => false
                  end |}.

  Global Instance RelDec_Correct_eq_typ : RelDec_Correct RelDec_from_dec.
  Proof.
    constructor.
    intros.
    unfold rel_dec; simpl.
    destruct (f x y).
    - tauto.
    - split.
      + inversion 1.
      + intro. apply n in H. tauto.
  Qed.
End RelDec_from_dec.


(*
Section SumEq.
  Variable T : Type.
  Variable U : Type.

  Variable EDT : RelDec (@eq T).
  Variable EDU : RelDec (@eq U).

  (** Specialization for equality **)
  Global Instance RelDec_eq_sum : RelDec (@eq (T + U)) :=
  { rel_dec := fun x y =>
    match x , y with
      | inl x , inl y => eq_dec x y
      | inr x , inr y => eq_dec x y
      | _ , _ => false
    end }.

  Variable EDCT : RelDec_Correct EDT.
  Variable EDCU : RelDec_Correct EDU.

  Global Instance RelDec_Correct_eq_sum : RelDec_Correct RelDec_eq_sum.
  Proof.
    constructor; destruct x; destruct y; split; simpl in *; intros; try congruence;
      f_equal; try match goal with
                     | [ H : context [ eq_dec ?X ?Y ] |- _ ] =>
                       consider (eq_dec X Y)
                     | [ |- context [ eq_dec ?X ?Y ] ] =>
                       consider (eq_dec X Y)
                   end; auto; congruence.
  Qed.

End SumEq.
*)
