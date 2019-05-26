Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import ExtLib.Core.Type.
Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Structures.Reducible.
Require Import ExtLib.Structures.Traversable.
Require Import ExtLib.Structures.Applicative.
Require Import ExtLib.Structures.Functor.
Require Import ExtLib.Structures.FunctorLaws.
Require Import ExtLib.Structures.Proper.
Require Import ExtLib.Data.Fun.
Require Import ExtLib.Tactics.Injection.
Require Import ExtLib.Tactics.Consider.

Set Implicit Arguments.
Set Strict Implicit.

Global Instance Foldable_option {T} : Foldable (option T) T :=
  fun _ f d v =>
    match v with
      | None => d
      | Some x => f x d
    end.

Global Instance Traversable_option : Traversable option :=
{| mapT := fun F _ _ _ f o =>
  match o with
    | None => pure None
    | Some o => ap (pure (@Some _)) (f o)
  end
|}.

Global Instance Applicative_option : Applicative option :=
{| pure := @Some
 ; ap := fun _ _ f x =>
           match f , x with
             | Some f , Some x => Some (f x)
             | _ , _ => None
           end
|}.

Global Instance Functor_option : Functor option :=
{| fmap := fun _ _ f x => match x with
                            | None => None
                            | Some x => Some (f x)
                          end |}.

Section relation.
  Context {T : Type}.
  Variable (R : relation T).

  Inductive Roption : Relation_Definitions.relation (option T) :=
  | Roption_None : Roption None None
  | Roption_Some : forall x y, R x y -> Roption (Some x) (Some y).

  Lemma Reflexive_Roption : Reflexive R -> Reflexive Roption.
  Proof. clear. compute. destruct x; try constructor; auto. Qed.

  Lemma Symmetric_Roption : Symmetric R -> Symmetric Roption.
  Proof. clear. compute. intros.
         destruct H0; constructor. auto.
  Qed.

  Lemma Transitive_Roption : Transitive R -> Transitive Roption.
  Proof.
    clear. compute. intros.
    destruct H0; auto.
    inversion H1. constructor; auto. subst. eapply H; eassumption.
  Qed.

  Global Instance Injective_Roption_None
  : Injective (Roption None None).
  refine {| result := True |}.
  auto.
  Defined.

  Global Instance Injective_Roption_None_Some a
  : Injective (Roption None (Some a)).
  refine {| result := False |}.
  inversion 1.
  Defined.

  Global Instance Injective_Roption_Some_None a
  : Injective (Roption (Some a) None).
  refine {| result := False |}.
  inversion 1.
  Defined.

  Global Instance Injective_Roption_Some_Some a b
  : Injective (Roption (Some a) (Some b)).
  refine {| result := R a b |}.
  inversion 1. auto.
  Defined.

  Global Instance Injective_Proper_Roption_Some x
  : Injective (Proper Roption (Some x)).
  refine {| result := R x x |}.
  abstract (inversion 1; assumption).
  Defined.

End relation.

Section type.
  Variable T : Type.
  Variable tT : type T.

  Global Instance type_option : type (option T) :=
  { equal := Roption equal
  ; proper := fun x => match x with
                         | None => True
                         | Some y => proper y
                       end }.

  Variable tTOk : typeOk tT.

  Global Instance typeOk_option : typeOk type_option.
  Proof.
    constructor.
    { inversion 1.
      split; constructor.
      split; simpl; eapply only_proper; eauto. symmetry; eauto. }
    { red. destruct x; simpl. constructor.
      eapply preflexive; [ | eapply H ].
      eapply equiv_prefl; auto. constructor. }
    { red. destruct 1. constructor. constructor. symmetry. assumption. }
    { red. destruct 1; inversion 1; subst. assumption.
      constructor. etransitivity; eauto. }
  Qed.

  Global Instance proper_Some : proper (@Some T).
  Proof. constructor; assumption. Qed.

  Global Instance proper_None : proper (@None T).
  Proof. constructor. Qed.

End type.

(*
Global Instance FunctorLaws_option : FunctorLaws Functor_option type_option.
Proof.
  constructor.
  { simpl. red. destruct x; destruct y; simpl; auto.
    inversion 1; simpl. red in H0.
    unfold id. constructor. etransitivity. eapply H0. 2: eauto.
    eapply proper_left; eauto.
    inversion 1. }
  { intros. simpl in *.
    red. intros.
    destruct H4; simpl.
    - unfold compose. constructor.
    - unfold compose. constructor.
      eapply H3. eapply H2. assumption. }
  { intros; simpl in *.
    red. red. inversion 2. constructor.
    constructor. apply H1. assumption. }
Qed.
*)

Global Instance Injective_Some (T : Type) (a b : T) : Injective (Some a = Some b) :=
{ result := a = b
; injection := 
    fun P : Some a = Some b =>
      match P with 
      | eq_refl => eq_refl
      end
}.

Require ExtLib.Core.EquivDec.

Global Instance EqDec_option (T : Type) (EDT : EquivDec.EqDec T (@eq T)) : EquivDec.EqDec (option T) (@eq _).
Proof.
  red. unfold Equivalence.equiv, RelationClasses.complement. intros.
  change (x = y -> False) with (x <> y).
  decide equality. apply EDT.
Qed.

Section OptionEq.
  Variable T : Type.
  Variable EDT : RelDec (@eq T).

  (** Specialization for equality **)
  Global Instance RelDec_eq_option : RelDec (@eq (option T)) :=
  { rel_dec := fun x y =>
    match x , y with
      | None , None => true
      | Some x , Some y => eq_dec x y
      | _ , _ => false
    end }.

  Variable EDCT : RelDec_Correct EDT.

  Global Instance RelDec_Correct_eq_option : RelDec_Correct RelDec_eq_option.
  Proof.
    constructor; destruct x; destruct y; split; simpl in *; intros; try congruence;
      f_equal; try match goal with
                     | [ H : context [ eq_dec ?X ?Y ] |- _ ] =>
                       consider (eq_dec X Y)
                     | [ |- context [ eq_dec ?X ?Y ] ] =>
                       consider (eq_dec X Y)
                   end; auto; congruence.
  Qed.

End OptionEq.

Lemma eq_option_eq
: forall T (a b : T) (pf : a = b) (F : _ -> Type) val,
    match pf in _ = x return option (F x) with
      | eq_refl => val
    end = match val with
            | None => None
            | Some val => Some match pf in _ = x return F x with
                                 | eq_refl => val
                               end
          end.
Proof.
  destruct pf. destruct val; reflexivity.
Defined.

Hint Rewrite eq_option_eq : eq_rw.
