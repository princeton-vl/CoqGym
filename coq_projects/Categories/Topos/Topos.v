From Categories Require Import Category.Main.
From Categories Require Import Limits.Limit.
From Categories Require Import Coq_Cats.Type_Cat.Card_Restriction.
From Categories Require Import Basic_Cons.CCC.
From Categories Require Import Topos.SubObject_Classifier.

Class Topos : Type :=
  {
    Topos_Cat : Category;
    Topos_Cat_CCC : CCC Topos_Cat;
    Topos_Cat_Fin_Limit : Has_Restr_Limits Topos_Cat Finite;
    Topos_Cat_SOC : SubObject_Classifier Topos_Cat
  }.

Coercion Topos_Cat : Topos >-> Category.
