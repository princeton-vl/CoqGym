From Categories Require Import Essentials.Notations.
From Categories Require Import Essentials.Types.
From Categories Require Import Essentials.Facts_Tactics.
From Categories Require Import Category.Main.
From Categories Require Import Basic_Cons.CCC.
From Categories Require Import Coq_Cats.Coq_Cat.

(*
**********************************************************
***************                          *****************
***************     Prop Category        *****************
***************                          *****************
**********************************************************
*)


(* The category of Types in Coq's "Prop" universe (Coq's Proposits) *)

Program Definition Prop_Cat : Category := Coq_Cat Prop.

Local Hint Extern 1 => contradiction.

Program Instance False_init : (𝟘_ Prop_Cat)%object := {|terminal := False|}.

Local Hint Extern 1 => match goal with
                        |- ?A = ?B :> True => destruct A; destruct B
                      end.

Program Instance True_term : (𝟙_ Prop_Cat)%object := {terminal := True}.

Local Hint Extern 1 => match goal with
                        |- ?A = ?B :> _ ∧ _ => destruct A; destruct B
                      end.

Local Hint Extern 1 => tauto.

Section Prod.
  Context (P Q : Prop).

  Local Notation "P × Q" := (Product Prop_Cat P Q) : object_scope.
  
  Program Definition Conj_Product : (P × Q)%object := {|product := (P ∧ Q)|}.
  
  Local Obligation Tactic := idtac.
  
  Next Obligation. (* Prod_morph_unique *)
  Proof.
    intros p' r1 r2 f g H1 H2 H3 H4.
    rewrite <- H3 in H1.
    rewrite <- H4 in H2.
    clear H3 H4.
    extensionality x.
    apply (fun p => equal_f p x) in H1; apply (fun p => equal_f p x) in H2.
    cbn in H1, H2.
  destruct (f x); destruct (g x); cbn in *; subst; trivial.
  Qed.

End Prod.
  
Program Instance Prop_Cat_Has_Products : Has_Products Prop_Cat := Conj_Product.

Local Hint Extern 1 => match goal with H : _ ∧ _ |- _ => destruct H end.

Section Exp.
  Context (P Q : Prop_Cat).
  
  Program Definition implication_exp : (P ⇑ Q)%object
    :=
      {|
        exponential := (P -> Q)
      |}.

  Local Obligation Tactic := idtac.
  
  Next Obligation. (* Exp_morph_unique *)
  Proof.
    intros z f u u' H1 H2.
    rewrite H1 in H2; clear H1.
    extensionality a; extensionality x.
    apply (fun p => equal_f p (conj a x)) in H2.
    assumption.
  Qed.

End Exp.

Program Instance Prop_Cat_Has_Exponentials : Has_Exponentials Prop_Cat :=
  implication_exp.

Program Instance Prop_Cat_CCC : CCC Prop_Cat.

Local Hint Extern 1 => match goal with H : _ ∨ _ |- _ => destruct H end.

Section Sum.
  Context (P Q : Prop).

  Local Notation "P + Q" := (Sum Prop_Cat P Q) : object_scope.
  
  Program Definition Disj_Sum  : (P + Q)%object := {|product := (P ∨ Q)|}.

  Local Obligation Tactic := idtac.

  Next Obligation. (* Sum_morph_unique *)
  Proof.
    intros p' r1 r2 f g H1 H2 H3 H4.
    rewrite <- H3 in H1.
    rewrite <- H4 in H2.
    clear H3 H4.
    extensionality x.
    destruct x as [x1|x2].
    + apply (fun p => equal_f p x1) in H1; auto.
    + apply (fun p => equal_f p x2) in H2; auto.
  Qed.
  
End Sum.

Program Instance Prop_Cat_Has_Sums : Has_Sums Prop_Cat := Disj_Sum.
