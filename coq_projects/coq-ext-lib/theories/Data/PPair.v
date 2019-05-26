Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Tactics.Injection.

Set Printing Universes.
Set Primitive Projections.
Set Universe Polymorphism.

Section pair.
  Polymorphic Universes i j.
  Variable (T : Type@{i}) (U : Type@{j}).

  Polymorphic Record pprod : Type@{max (i, j)} := ppair
  { pfst : T
  ; psnd : U }.

End pair.

Arguments pprod _ _ : assert.
Arguments ppair {_ _} _ _.
Arguments pfst {_ _} _.
Arguments psnd {_ _} _.

Section equality.
  Polymorphic Lemma eq_pair_rw
  : forall T U (a b : T) (c d : U) (pf : (ppair a c) = (ppair b d)),
    exists (pf' : a = b) (pf'' : c = d),
      pf = match pf' , pf'' with
           | eq_refl , eq_refl => eq_refl
           end.
  Proof.
    clear.
    intros.
    exists (f_equal pfst pf).
    exists (f_equal psnd pf).
    change (pf =
            match
              @f_equal (pprod T U) T (@pfst T U) (ppair a c) (ppair b d) pf in (_ = t)
              return ((ppair a c) = (ppair t d))
            with
            | eq_refl =>
              match
                @f_equal (pprod T U) U (@psnd T U) (ppair a c) (ppair b d) pf in (_ = u)
                return ((ppair a c) = (ppair (pfst (ppair a c)) u))
              with
              | eq_refl => @eq_refl (pprod T U) (ppair a c)
              end
            end).
    generalize dependent (ppair a c).
    intros; subst. reflexivity.
  Defined.
End equality.

Section Injective.
  Polymorphic Universes i j.
  Context {T : Type@{i}} {U : Type@{j}}.

  Global Instance Injective_pprod (a : T) (b : U) c d
  : Injective (ppair a b = ppair c d).
  Proof.
  refine {| result := a = c /\ b = d |}.
    intros.
    change a with (pfst@{i j} {| pfst := a ; psnd := b |}).
    change b with (psnd@{i j} {| pfst := a ; psnd := b |}) at 2.
    rewrite H. split; reflexivity.
  Defined.
End Injective.

Section PProdEq.
  Polymorphic Universes i j.
  Context {T : Type@{i}} {U : Type@{j}}.
  Context {EDT : RelDec (@eq T)}.
  Context {EDU : RelDec (@eq U)}.
  Context {EDCT : RelDec_Correct EDT}.
  Context {EDCU : RelDec_Correct EDU}.

  Polymorphic Definition ppair_eqb (p1 p2 : pprod T U) : bool :=
    pfst p1 ?[ eq ] pfst p2 && psnd p1 ?[ eq ] psnd p2.

  (** Specialization for equality **)
  Global Polymorphic Instance RelDec_eq_ppair : RelDec (@eq (@pprod T U)) :=
  { rel_dec := ppair_eqb }.

  Global Polymorphic Instance RelDec_Correct_eq_ppair
  : RelDec_Correct RelDec_eq_ppair.
  Proof.
    constructor. intros p1 p2. destruct p1, p2. simpl.
    unfold ppair_eqb. simpl.
    rewrite Bool.andb_true_iff.
    repeat rewrite rel_dec_correct.
    split.
    { destruct 1. f_equal; assumption. }
    { intros. inv_all. tauto. }
  Qed.

End PProdEq.
