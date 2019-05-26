From Categories Require Import Essentials.Notations.
From Categories Require Import Essentials.Types.
From Categories Require Import Essentials.Facts_Tactics.
From Categories Require Import Category.Main.
From Categories Require Import Basic_Cons.CCC.
From Categories Require Import PreSheaf.PreSheaf.
From Categories Require Export PreSheaf.Terminal.
From Categories Require Export PreSheaf.Product.
From Categories Require Export PreSheaf.Exponential.

(** Category of presheaves over C is cartesian closed. *)
Program Instance PShCat_CCC (C : Category) : CCC (PShCat C)
  :=
    {|
      CCC_term := PSh_Terminal C;
      CCC_HP := PSh_Has_Products C;
      CCC_HEXP := PSh_Has_Exponentials C
    |}.


