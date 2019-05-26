From Categories Require Import Essentials.Notations.
From Categories Require Import Essentials.Types.
From Categories Require Import Essentials.Facts_Tactics.
From Categories Require Import Category.Main.
From Categories Require Import Functor.Functor Functor.Functor_Ops
        Functor.Representable.Hom_Func.
From Categories Require Import Functor.Functor_Extender.
From Categories Require Import NatTrans.NatTrans NatTrans.Operations
        NatTrans.Func_Cat NatTrans.NatIso.
From Categories Require Import Ext_Cons.Prod_Cat.Prod_Cat Ext_Cons.Prod_Cat.Operations
        Ext_Cons.Prod_Cat.Nat_Facts.
From Categories Require Import KanExt.Local
        KanExt.LocalFacts.HomToCones
        KanExt.LocalFacts.ConesToHom.

Local Open Scope functor_scope.

(** This module contains facts about local kan extensions involving natural
    isomorphism. *)

(** Any two naturally isomorphic functors have the same kan extensions –
stated with hom functor definition of local kan extensions. *)
Section Hom_Local_Right_KanExt_Iso.
  Context {C C' : Category} {p : C –≻ C'}
          {D : Category} {F F' : C –≻ D}
          (N : (F' ≃ F)%natiso)
          (hlrke : Hom_Local_Right_KanExt p F).

  Definition Hom_Local_Right_KanExt_Iso : Hom_Local_Right_KanExt p F' :=
    {|
      HLRKE := hlrke;
      HLRKE_Iso :=
        (
          (HLRKE_Iso hlrke)
            ∘ (
              (Fix_Bi_Func_2_object_NatIso (Hom_Func (Func_Cat C D)) N)
               ∘_h (NatTrans_id_Iso (Left_Functor_Extender p D)^op)
            )
        )%isomorphism%natiso
          
    |}.

End Hom_Local_Right_KanExt_Iso.

(** Any two naturally isomorphic functors have the same kan extensions –
stated with cones definition of local kan extensions. *)
Section Local_Right_KanExt_Iso.
  Context {C C' : Category}
          {p : C –≻ C'}
          {D : Category}
          {F F' : C –≻ D}
          (N : (F' ≃ F)%natiso)
          (hlrke : Local_Right_KanExt p F).

  Definition Local_Right_KanExt_Iso : Local_Right_KanExt p F' :=
    Hom_Local_Right_KanExt_to_Local_Right_KanExt
      (Hom_Local_Right_KanExt_Iso
         N
         (Local_Right_KanExt_to_Hom_Local_Right_KanExt hlrke)
      ).

End Local_Right_KanExt_Iso.

(** If a functor is naturally isomorphic to the local right kan extension then
it also is local right kan extensions *)
Section Iso_Hom_Local_Right_KanExt.
  Context {C C' : Category}
          {p : C –≻ C'}
          {D : Category}
          {F : C –≻ D}
          {hlrke hlrke' : C' –≻ D}
          (N : (hlrke ≃ hlrke')%natiso)
          (ihlrke : Hom_Local_Right_KanExt_Isomorphism p F hlrke).
  
  Definition Iso_Hom_Local_Right_KanExt : Hom_Local_Right_KanExt p F :=
    {|
      HLRKE := hlrke';
      HLRKE_Iso :=
        ((Fix_Bi_Func_2_object_NatIso (Hom_Func (Func_Cat C' D)) N)
           ∘ ihlrke)%isomorphism
    |}.

End Iso_Hom_Local_Right_KanExt.

(** If a functor is naturally isomorphic to the local left kan extension then
it also is local left kan extensions – proven using duality. *)
Section Iso_Local_Right_KanExt.
  Context {C C' : Category}
          {p : C –≻ C'}
          {D : Category}
          {F : C –≻ D}
          {hlrke hlrke' : C' –≻ D}
          (N : (hlrke ≃ hlrke')%natiso)
          (ihlrke : is_Local_Right_KanExt p F hlrke).

  Definition  Iso_Local_Right_KanExt : is_Local_Right_KanExt p F hlrke' :=
    Local_Right_KanExt_is_Local_Right_KanExt
      _
      _
      (
        Hom_Local_Right_KanExt_to_Local_Right_KanExt
          (Iso_Hom_Local_Right_KanExt
             N
             (HLRKE_Iso
                (Local_Right_KanExt_to_Hom_Local_Right_KanExt
                   (is_Local_Right_KanExt_Local_Right_KanExt _ _ ihlrke)
                )
             )
          )
      ).

End Iso_Local_Right_KanExt.


(** Kan extension along any two naturally isomorphic functors is the same –
stated with hom functor definition of local kan extensions. *)
Section Hom_Local_Right_KanExt_Iso_along.
  Context {C C' : Category} {p p' : C –≻ C'}
          (N : (p' ≃ p )%natiso)
          {D : Category} {F : C –≻ D}
          (hlrke : Hom_Local_Right_KanExt p F).

  Program Definition Hom_Local_Right_KanExt_Iso_along
    : Hom_Local_Right_KanExt p' F :=
    {|
      HLRKE := hlrke;
      HLRKE_Iso :=
        (
          (HLRKE_Iso hlrke)
            ∘ (
              (NatTrans_id_Iso
                 (@Fix_Bi_Func_2
                    _ (Func_Cat C D) _ F (Hom_Func (Func_Cat C D))))
                ∘_h ((Left_Functor_Extender_Iso N D)^op)
            )
        )%isomorphism%natiso
    |}.

End Hom_Local_Right_KanExt_Iso_along.

(** Any two naturally isomorphic functors have the same kan extensions –
stated with cones definition of local kan extensions. *)
Section Local_Right_KanExt_Iso_along.
  Context {C C' : Category} {p p' : C –≻ C'}
          (N : (p' ≃ p)%natiso)
          {D : Category} {F : C –≻ D}
          (hlrke : Local_Right_KanExt p F).

  Definition Local_Right_KanExt_Iso_along : Local_Right_KanExt p' F :=
    Hom_Local_Right_KanExt_to_Local_Right_KanExt
      (Hom_Local_Right_KanExt_Iso_along
         N
         (Local_Right_KanExt_to_Hom_Local_Right_KanExt hlrke)
      ).

End Local_Right_KanExt_Iso_along.
