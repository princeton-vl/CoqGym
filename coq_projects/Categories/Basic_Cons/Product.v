From Categories Require Import Essentials.Notations.
From Categories Require Import Essentials.Types.
From Categories Require Import Essentials.Facts_Tactics.
From Categories Require Import Category.Main.
From Categories Require Import Ext_Cons.Prod_Cat.Prod_Cat Ext_Cons.Prod_Cat.Operations.
From Categories Require Import Functor.Main.

Local Open Scope morphism_scope.

(**
Given two objects a and b, their product a×b is an object such that there are
two projections from it to a and b:

#
<pre>

                    π₁        π₂
                a <—–——– a×b ———–—> b
</pre>
#
such that for any object z with two projections to a and b, there is a unique
arrow h that makes the following diagram commute:

#
<pre>
                    π₁        π₂
                a <—–——–– a×b –———–—> b
                 ↖         ↑        ↗
                  \        |       /
                   \       |      /
                    \      |∃!h  /
                     \     |    /
                      \    |   /
                       \   |  /
                           z
</pre>
#
*)
Record Product {C : Category} (c d : C) : Type :=
{
  product : C;

  Pi_1 : product –≻ c;

  Pi_2 : product –≻ d;

  Prod_morph_ex : ∀ (p' : Obj) (r1 : p' –≻ c) (r2 : p' –≻ d), p' –≻ product;

  Prod_morph_com_1 : ∀ (p' : Obj) (r1 : p' –≻ c) (r2 : p' –≻ d),
      (Pi_1 ∘ (Prod_morph_ex p' r1 r2))%morphism = r1;
  
  Prod_morph_com_2 : ∀ (p' : Obj) (r1 : p' –≻ c) (r2 : p' –≻ d),
      (Pi_2 ∘ (Prod_morph_ex p' r1 r2))%morphism = r2;
  
  Prod_morph_unique :
    ∀ (p' : Obj) (r1 : p' –≻ c) (r2 : p' –≻ d) (f g : p' –≻ product),
      Pi_1 ∘ f = r1
      → Pi_2 ∘ f = r2
      → Pi_1 ∘ g = r1
      → Pi_2 ∘ g = r2
      → f = g
}.

Arguments Product _ _ _, {_} _ _.

Arguments Pi_1 {_ _ _ _}, {_ _ _} _.
Arguments Pi_2 {_ _ _ _}, {_ _ _} _.
Arguments Prod_morph_ex {_ _ _} _ _ _ _.
Arguments Prod_morph_com_1 {_ _ _} _ _ _ _.
Arguments Prod_morph_com_2 {_ _ _} _ _ _ _.
Arguments Prod_morph_unique {_ _ _} _ _ _ _ _ _ _ _ _ _.

Coercion product : Product >-> Obj.

Notation "a × b" := (Product a b) : object_scope.

Local Open Scope object_scope.

(** for any pair of objects, their product is unique up to isomorphism. *)
Theorem Product_iso {C : Category} (c d : Obj) (P : c × d) (P' : c × d)
  : (P ≃ P')%isomorphism.
Proof.
  eapply (Build_Isomorphism _ _ _
                            (Prod_morph_ex P' P Pi_1 Pi_2)
                            (Prod_morph_ex P P' Pi_1 Pi_2));
  eapply Prod_morph_unique; eauto;
  rewrite <- assoc;
  repeat (rewrite Prod_morph_com_1 || rewrite Prod_morph_com_2); auto.
Qed.

Definition Has_Products (C : Category) : Type := ∀ a b, a × b.

Existing Class Has_Products.

(**
The product functor maps each pair of objects (an object of the product
category C×C) to their product in C.
*)
Program Definition Prod_Func (C : Category) {HP : Has_Products C}
  : ((C × C) –≻ C)%functor :=
{|
  FO := fun x => HP (fst x) (snd x); 
  FA := fun a b f => Prod_morph_ex _ _ ((fst f) ∘ Pi_1) ((snd f) ∘ Pi_2)
|}.

Next Obligation. (* F_id *)  
Proof.
  eapply Prod_morph_unique;
  try reflexivity; [rewrite Prod_morph_com_1|rewrite Prod_morph_com_2]; auto.
Qed.  

Next Obligation. (* F_compose *)  
Proof.
  eapply Prod_morph_unique;
  try ((rewrite Prod_morph_com_1 || rewrite Prod_morph_com_2); reflexivity);
  repeat rewrite <- assoc; (rewrite Prod_morph_com_1 || rewrite Prod_morph_com_2);
  rewrite assoc; (rewrite Prod_morph_com_1 || rewrite Prod_morph_com_2); auto.
Qed.

Arguments Prod_Func _ _, _ {_}.

Notation "×ᶠⁿᶜ" := Prod_Func : functor_scope.

(** Sum is the dual of product *)
Definition Sum (C : Category) := @Product (C^op).

Arguments Sum _ _ _, {_} _ _.

Notation "a + b" := (Sum a b) : object_scope.

Definition Has_Sums (C : Category) : Type :=  ∀ (a b : C), (a + b)%object.

Existing Class Has_Sums.

(**
The sum functor maps each pair of objects (an object of the product category
C×C) to their sum in C.
*)
Definition Sum_Func {C : Category} {HS : Has_Sums C} : ((C × C) –≻ C)%functor :=
  (×ᶠⁿᶜ (C^op) HS)^op.

Arguments Sum_Func _ _, _ {_}.

Notation "+ᶠⁿᶜ" := Sum_Func : functor_scope.
