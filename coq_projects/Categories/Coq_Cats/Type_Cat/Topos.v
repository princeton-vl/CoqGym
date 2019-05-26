From Categories Require Import Category.Main.
From Categories Require Import Topos.Topos.
From Categories Require Import Limits.Limit.
From Categories Require Import Coq_Cats.Type_Cat.Card_Restriction.
From Categories Require Import Coq_Cats.Type_Cat.Type_Cat.
From Categories Require Import Coq_Cats.Type_Cat.CCC.
From Categories Require Import Coq_Cats.Type_Cat.Complete.
From Categories Require Import Coq_Cats.Type_Cat.SubObject_Classifier. 

Instance Type_Cat_Topos : Topos :=
  {
    Topos_Cat := Type_Cat;
    Topos_Cat_CCC := Type_Cat_CCC;
    Topos_Cat_SOC := Type_Cat_SubObject_Classifier;
    Topos_Cat_Fin_Limit := Complete_Has_Restricted_Limits Type_Cat Finite
  }.
