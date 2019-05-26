Require Import Coq.Bool.Bool.
Require Import Coq.Classes.RelationClasses.
Require Import ExtLib.Tactics.Consider.

Set Implicit Arguments.
Set Strict Implicit.

Class CmpDec (T : Type) (equ : T -> T -> Prop) (ltu : T -> T -> Prop) : Type :=
{ cmp_dec : T -> T -> comparison }.

Class CmpDec_Correct T (equ ltu : T -> T -> Prop) (ED : CmpDec equ ltu) : Prop :=
{ cmp_dec_correct : forall x y : T, 
  match cmp_dec x y with
    | Eq => equ x y
    | Lt => ltu x y
    | Gt => ltu y x
  end }.

Inductive cmp_case (P Q R : Prop) : comparison -> Prop :=
| CaseEq : P -> cmp_case P Q R Eq
| CaseLt : Q -> cmp_case P Q R Lt
| CaseGt : R -> cmp_case P Q R Gt.

Section pair.
  Variable T U : Type.
  Variables eqt ltt : T -> T -> Prop.
  Variables equ ltu : U -> U -> Prop.

  Definition eq_pair (a b : T * U) : Prop :=
    eqt (fst a) (fst b) /\ equ (snd a) (snd b).

  Definition lt_pair (a b : T * U) : Prop :=
    ltt (fst a) (fst b) \/ (eqt (fst a) (fst b) /\ ltu (snd a) (snd b)).

  Variable cdt : CmpDec eqt ltt.
  Variable cdu : CmpDec equ ltu.

  Instance CmpDec_pair : CmpDec eq_pair lt_pair :=
  { cmp_dec := fun a b =>
    let '(al,ar) := a in
    let '(bl,br) := b in
    match cmp_dec al bl with
      | Eq => cmp_dec ar br 
      | x => x 
    end }.

  Variable cdtC : CmpDec_Correct cdt.
  Variable cduC : CmpDec_Correct cdu.
  Variable Symmetric_eqt : Symmetric eqt.

  Instance CmpDec_Correct_pair : CmpDec_Correct CmpDec_pair.
  Proof.
    constructor. destruct x; destruct y; unfold eq_pair, lt_pair; simpl in *.
    generalize (cmp_dec_correct t t0); destruct (cmp_dec t t0); simpl; intros; auto.
    generalize (cmp_dec_correct u u0); destruct (cmp_dec u u0); simpl; intros; auto.
  Qed.
End pair.

