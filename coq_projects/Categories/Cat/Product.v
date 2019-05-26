From Categories Require Import Essentials.Notations.
From Categories Require Import Essentials.Types.
From Categories Require Import Essentials.Facts_Tactics.
From Categories Require Import Category.Main.
From Categories Require Import Functor.Main.
From Categories Require Import Cat.Cat.
From Categories Require Import Ext_Cons.Prod_Cat.Prod_Cat Ext_Cons.Prod_Cat.Operations.
From Categories Require Import Basic_Cons.Product.

Local Notation "A × B" := (@Product Cat A B) : object_scope.

(** Product in category of categories is imply the product of actegories *)
Program Definition Cat_Products (C C' : Category) : (C × C')%object :=
{|
  product := (C × C')%category;

  Pi_1 := Cat_Proj1 C C';

  Pi_2 := Cat_Proj2 C C';

  Prod_morph_ex := fun P => fun F G =>  Functor_compose (Diag_Func P) (Prod_Functor F G)
|}.

Local Obligation Tactic := idtac.

Next Obligation. (* Prod_morph_unique *)
Proof.
  intros C C' p' r1 r2 f g H1 H2 H3 H4.
  cbn in *.
  transitivity (Functor_compose (Diag_Func p') (Prod_Functor r1 r2)).
  + symmetry.
    rewrite <- H1, <- H2.
    apply Prod_Functor_Cat_Proj.
  + rewrite <- H3, <- H4.
    apply Prod_Functor_Cat_Proj.
Qed.

(* Cat_Products defined *)

Program Instance Cat_Has_Products : Has_Products Cat := Cat_Products.




