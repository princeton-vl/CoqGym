From Categories Require Import Category.Main.
From Categories Require Import Topos.Topos.
From Categories Require Import Limits.Limit.
From Categories Require Import Coq_Cats.Type_Cat.Card_Restriction.
From Categories Require Import PreSheaf.PreSheaf.
From Categories Require Import PreSheaf.CCC.
From Categories Require Import PreSheaf.Complete.
From Categories Require Import PreSheaf.SubObject_Classifier. 

Instance Type_Cat_Topos (C : Category) : Topos :=
  {
    Topos_Cat := PShCat C;
    Topos_Cat_CCC := PShCat_CCC C;
    Topos_Cat_SOC := PSh_SubObject_Classifier C;
    Topos_Cat_Fin_Limit := Complete_Has_Restricted_Limits (PShCat C) Finite
  }.
