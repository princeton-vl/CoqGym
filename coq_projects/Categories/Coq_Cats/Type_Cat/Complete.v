From Categories Require Import Category.Main.
From Categories Require Import Coq_Cats.Type_Cat.Type_Cat.
From Categories Require Import Type_Cat.GenProd Type_Cat.GenSum Type_Cat.Equalizer.
From Categories Require Import Limits.Limit Limits.GenProd_Eq_Limits.

Instance Type_Cat_Complete : Complete Type_Cat :=
  @GenProd_Eq_Complete Type_Cat Type_Cat_GenProd Type_Cat_Has_Equalizers.

Instance Type_Cat_CoComplete : CoComplete Type_Cat :=
  @GenSum_CoEq_CoComplete Type_Cat Type_Cat_GenSum Type_Cat_Has_CoEqualizers.
