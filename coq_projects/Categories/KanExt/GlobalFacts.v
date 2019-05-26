From Categories Require Import Essentials.Notations.
From Categories Require Import Essentials.Types.
From Categories Require Import Essentials.Facts_Tactics.
From Categories Require Import Category.Main.
From Categories Require Import Functor.Functor Functor.Functor_Ops Functor.Functor_Properties.
From Categories Require Import NatTrans.NatTrans NatTrans.Func_Cat NatTrans.NatIso.
From Categories Require Import Adjunction.Adjunction Adjunction.Adj_Facts.
From Categories Require Import KanExt.Global KanExt.LocalFacts.NatIso
        KanExt.LocaltoGlobal KanExt.GlobaltoLocal
.

Section Facts.
  Context {C C' : Category} (p : (C –≻ C')%functor)
          {D : Category}.

  (** Right kan extensions are unique up to natural isomorphisms. *)
  Section Right_KanExt_Unique.
    Context (rke rke' : Right_KanExt p D).

    Definition Right_KanExt_Unique : (rke ≃ rke')%natiso :=
      Adjunct_right_unique (right_kan_ext_adj rke) (right_kan_ext_adj rke').
    
    Definition Right_KanExt_Unique_points (F : (C –≻ D)%functor) :
      (rke _o F ≃ rke' _o F)%isomorphism := NatIso_Image Right_KanExt_Unique F.

  End Right_KanExt_Unique.

  (** Left kan extensions are unique up to natural isomorphisms. *)
  Section Left_KanExt_Unique.
    Context (lke lke' : Left_KanExt p D).

    Definition Left_KanExt_Unique : (lke ≃ lke')%natiso :=
      Adjunct_left_unique (left_kan_ext_adj lke) (left_kan_ext_adj lke').

    Definition Left_KanExt_Unique_points (F : (C –≻ D)%functor) :
      (lke _o F ≃ lke' _o F)%isomorphism := NatIso_Image Left_KanExt_Unique F.

  End Left_KanExt_Unique.

  Section Right_KanExt_Iso.
    Context (rke : Right_KanExt p D)
            {F F' : (C –≻ D)%functor}
            (I : (F ≃ F')%natiso).

    Definition Right_KanExt_Iso : (rke _o F ≃ rke _o F')%isomorphism :=
      Functors_Preserve_Isos rke I.

  End Right_KanExt_Iso.

  Section Left_KanExt_Iso.
    Context (lke : Left_KanExt p D)
            {F F' : (C –≻ D)%functor}
            (I : (F ≃ F')%natiso).

    Definition Left_KanExt_Iso : (lke _o F ≃ lke _o F')%isomorphism :=
      Functors_Preserve_Isos lke I.

  End Left_KanExt_Iso.

  Section Right_KanExt_Iso_along.
    Context {p' : (C –≻ C')%functor}
            (N : (p' ≃ p)%natiso)
            (rke : Right_KanExt p D)
    .
    
    Definition Right_KanExt_Iso_along : Right_KanExt p' D :=
      Local_to_Global_Right
        p'
        D
        (
          fun F =>
            Local_Right_KanExt_Iso_along
              N
              (Global_to_Local_Right p D rke F)
        ).

  End Right_KanExt_Iso_along.

  Section Left_KanExt_Iso_along.
    Context {p' : (C –≻ C')%functor}
            (N : (p' ≃ p)%natiso)
            (lke : Left_KanExt p D)
    .
    
    Definition Left_KanExt_Iso_along : Left_KanExt p' D :=
      Local_to_Global_Left
        p'
        D
        (
          fun F =>
            Local_Right_KanExt_Iso_along
              (N^op)%natiso
              (Global_to_Local_Left p D lke F)
        ).

  End Left_KanExt_Iso_along.  

End Facts.
