From Categories Require Import Category.Main.
From Categories Require Import Coq_Cats.Type_Cat.Type_Cat.
From Categories Require Import Type_Cat.GenProd Type_Cat.GenSum Type_Cat.Equalizer.
From Categories Require Import Limits.Limit Limits.GenProd_Eq_Limits.
From Categories Require Import PreSheaf.PreSheaf.
From Categories Require Import
        PreSheaf.Equalizer
        PreSheaf.GenProd
        PreSheaf.GenSum
.

Instance PShCat_Complete (C: Category) : Complete (PShCat C) :=
  @GenProd_Eq_Complete (PShCat C) (PSh_GenProd C) (@PSh_Has_Equalizers C).

Instance PShCat_CoComplete (C: Category) : CoComplete (PShCat C) :=
  @GenSum_CoEq_CoComplete (PShCat C) (PSh_GenSum C) (@PSh_Has_CoEqualizers C).
