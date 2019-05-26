From Categories Require Import Essentials.Notations.
From Categories Require Import Essentials.Types.
From Categories Require Import Essentials.Facts_Tactics.
From Categories Require Import Category.Main.
From Categories Require Import
        Limits.Limit
        Limits.GenProd_GenSum
        Limits.GenProd_Eq_Limits
.
From Categories Require Import Functor.Functor Functor.Functor_Ops.
From Categories Require Import NatTrans.Main.
From Categories Require Import Ext_Cons.Comma.

From Categories Require Import Archetypal.Discr.Discr.

From Categories Require Import
        Adjunction.AFT.Commas_Complete.Commas_GenProd
        Adjunction.AFT.Commas_Complete.Commas_Equalizer
.

(** We show that if C is a complete category and G : C –≻ D preserves limits,
then every comma category (Comma (Func_From_SingletonCat x) G) for (x : D) is
complete. *)
Section Commas_Complete.
  Context
    {C D : Category}
    {CC : Complete C}
    {G : (C –≻ D)%functor}
    (GCont : Continuous CC G)
    (x : D)
  .

  Definition Commas_Complete : Complete (Comma (Func_From_SingletonCat x) G)
    :=
      @GenProd_Eq_Complete
        (Comma (Func_From_SingletonCat x) G)
        (@Comma_GenProd _ _ _ _ GCont x)
        (@Comma_Equalizer _ _ _ _ GCont x)
  .

End Commas_Complete.
