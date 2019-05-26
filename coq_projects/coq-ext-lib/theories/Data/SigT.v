Require Coq.Classes.EquivDec.
Require Import ExtLib.Core.Type.
Require Import ExtLib.Structures.EqDep.
Require Import ExtLib.Tactics.Injection.
Require Import ExtLib.Tactics.EqDep.
Require Import ExtLib.Tactics.TypeTac.

Set Implicit Arguments.
Set Strict Implicit.
Set Printing Universes.

Section type.
  Variable T : Type.
  Variable F : T -> Type.
  Variable ED : EquivDec.EqDec _ (@eq T).
  Variable tT : type T.
  Variable typF : forall x, type (F x).

  Global Instance type_sigT : type (sigT F) :=
  { equal := fun x y =>
    equal (projT1 x) (projT1 y) /\
    exists pf : projT1 y = projT1 x,
      equal (projT2 x) (match pf in _ = t return F t with
                          | eq_refl => projT2 y
                        end)
  ; proper := fun x => proper (projT1 x) /\ proper (projT2 x)
  }.

  Variable typeOkT : typeOk tT.
  Variable typOkF : forall x, typeOk (typF x).

  Global Instance typeOk_sigT : typeOk type_sigT.
  Proof.
    constructor.
    { destruct x; destruct y; intros. simpl in *. destruct H. destruct H0. subst.
      apply only_proper in H; [ | eauto with typeclass_instances ].
      apply only_proper in H0; [ | eauto with typeclass_instances ]. intuition. }
    { red. destruct x; intros. do 2 red in H.
      do 2 red; simpl in *. intuition.
      try solve [ apply equiv_prefl; eauto ].
      exists eq_refl.
      eapply Proper.preflexive; [ | eapply H1 ].
      eauto with typeclass_instances. }
    { red; destruct x; destruct y; intros; simpl in *.
      intuition. destruct H1; subst. exists eq_refl. symmetry; assumption. }
    { red; destruct x; destruct y; destruct z; intros; simpl in *; intuition.
      etransitivity; eauto.
      destruct H2; destruct H3; subst. exists eq_refl. etransitivity; eauto. }
  Qed.

  Global Instance proper_existT a b : proper a -> proper b -> proper (existT F a b).
  Proof.
    red; simpl. intuition.
  Qed.

  Global Instance proper_projT1 a : proper a -> proper (projT1 a).
  Proof.
    red; simpl. intuition.
  Qed.

  Global Instance proper_projT2 a : proper a -> proper (projT2 a).
  Proof.
    red; simpl. intuition.
  Qed.

End type.

Section injective.
  Variable T : Type.
  Variable F : T -> Type.
  Variable ED : EquivDec.EqDec _ (@eq T).

  Global Instance Injective_existT a b d
    : Injective (existT F a b = existT F a d) | 1.
  refine {| result := b = d |}.
  abstract (eauto using inj_pair2).
  Defined.

  Global Instance Injective_existT_dif a b c d
  : Injective (existT F a b = existT F c d) | 2.
  refine {| result := exists pf : c = a,
            b = match pf in _ = t return F t with
                  | eq_refl => d
                end |}.
  abstract (inversion 1; subst; exists eq_refl; auto).
  Defined.
End injective.

Lemma eq_sigT_rw
: forall T U F (a b : T) (pf : a = b) s,
    match pf in _ = x return @sigT U (F x) with
    | eq_refl => s
    end =
    @existT U (F b) (projT1 s)
            match pf in _ = x return F x (projT1 s) with
            | eq_refl => (projT2 s)
            end.
Proof. destruct pf. destruct s; reflexivity. Qed.

Hint Rewrite eq_sigT_rw : eq_rw.
