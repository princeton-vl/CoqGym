From Categories Require Import Essentials.Notations.
From Categories Require Import Essentials.Types.
From Categories Require Import Essentials.Facts_Tactics.
From Categories Require Import Category.Main.
From Categories Require Import Functor.Functor Functor.Functor_Ops
        Functor.Representable.Hom_Func_Prop.
From Categories Require Import Ext_Cons.Prod_Cat.Prod_Cat.
From Categories Require Import NatTrans.NatTrans NatTrans.Operations.
From Categories Require Import Adjunction.Adjunction Adjunction.Duality
        Adjunction.Adj_Facts.
From Categories Require Import KanExt.Global KanExt.Local KanExt.LocalFacts.ConesToHom
        KanExt.LocalFacts.HomToCones KanExt.GlobalDuality.

Local Open Scope functor_scope.

(** This module contains conversion from global to local kan extensions. *)
Section Global_to_Local_Right.
  Context {C C' : Category}
          (p : C –≻ C')
          (D : Category)
          (rke : Right_KanExt p D)
          (F : C –≻ D).

  (** The cone which (we will prove) is the local kan extension. *)
  Definition Cone_for_LoKan : LoKan_Cone p F :=
    {|
      cone_apex := (rke _o F)%object;
      cone_edge :=
        @adj_morph_ex _ _ _ _
                      (right_kan_ext_adj rke) (rke _o F) F (NatTrans_id _)
    |}.

  Section Cone_Morph_to_Cone_for_LoKan.
    Context (Cn : LoKan_Cone p F).

    (** We show that any natural transformation from any cone (the apex functor
        of a cone) to (apex functor of) the cone we constructed above remains
        the same under the following transformation:

        morph : Cn ——––>  (rke _o F)

        morph ∘_h (NatTrans_id p) : (Cn ∘ p) ————> ((rke _o F) ∘ p)

        η_{NatTrans_id (rke _o F)} ∘ (morph ∘_h (NatTrans_id p)) 
           : (Cn ∘ p) ————> F

        rke @_a (Cn ∘ p) F (η_{NatTrans_id (rke _o F)} 
                             ∘ (morph ∘_h (NatTrans_id p))) : 
          (rke _o (Cn ∘ p)) ————> (rke _o F)

        (rke @_a (Cn ∘ p) F (η_{NatTrans_id (rke _o F)}
                               ∘ (morph ∘_h (NatTrans_id p))))
          ∘ (Trans (adj_unit (right_kan_ext_adj rke)) Cn) : 
          Cn ————> (rke _o F)


        This result is used to show existence and unique ness of cones from Cn
        to the cone constructed above.
     *)
    
    Lemma Cone_Morph_to_Cone_for_LoKan_adj_unit_rke_id
          (morph : (Cn –≻ ((rke _o)%object F))%nattrans) :
      morph =
      (
        (
          (rke @_a)%morphism (Cn ∘ p)%functor F
                 (
                   (adj_morph_ex
                      (right_kan_ext_adj rke) (NatTrans_id ((rke _o) F)%object))
                     ∘ (morph ∘_h (NatTrans_id p))
                 )
        ) ∘ (Trans (adj_unit (right_kan_ext_adj rke)) Cn)
      )%nattrans.
    Proof.
      rewrite (@F_compose); cbn.
      rewrite NatTrans_compose_assoc.
      cbn_rewrite <- (@Trans_com
                       _ _ _ _
                       (@adj_unit _ _ _ _ (right_kan_ext_adj rke)) _ _ morph).
      rewrite <- NatTrans_compose_assoc.
      cbn_rewrite <- (
                    @adj_morph_com _ _ _ _
                                   (right_kan_ext_adj rke)
                                   _
                                   _
                                   (NatTrans_id ((rke _o)%object F))
                  ).
      rewrite NatTrans_id_unit_left.
      trivial.
    Qed.

    (** Given a cone, we construct a cone morph to the cone morph that we
        constructed above. *)
    Program Definition Cone_Morph_to_Cone_for_LoKan :
      LoKan_Cone_Morph Cn Cone_for_LoKan :=
      {|
        cone_morph :=
          (((rke _a (cone_edge Cn))%morphism)
             ∘ (Trans (adj_unit (right_kan_ext_adj rke)) Cn))%nattrans
      |}.

    Next Obligation.
    Proof.
      match goal with
        [|- _ = NatTrans_compose (NatTrans_hor_comp _ ?X) _] =>
        apply (@adj_morph_unique _ _ _ _ (right_kan_ext_adj rke) _ _ X); trivial
      end.
      apply Cone_Morph_to_Cone_for_LoKan_adj_unit_rke_id.
    Qed.

  End Cone_Morph_to_Cone_for_LoKan.

  Section Cone_Morph_to_Cone_for_LoKan_Unique.
    Context {Cn : LoKan_Cone p F} (M M' : LoKan_Cone_Morph Cn Cone_for_LoKan).

    (** Cone morph to the cone constructed is unique. *)
    Theorem Cone_Morph_to_Cone_for_LoKan_Unique : (M = M' :> (_ –≻ _)%nattrans).
    Proof.
      rewrite (Cone_Morph_to_Cone_for_LoKan_adj_unit_rke_id Cn M).
      rewrite (Cone_Morph_to_Cone_for_LoKan_adj_unit_rke_id Cn M').
      do 2 apply f_equal.
      set (H := cone_morph_com M'); rewrite (cone_morph_com M) in H; exact H.
    Qed.
      
  End Cone_Morph_to_Cone_for_LoKan_Unique.

  (** The conversion from global kan extensions to local kan extensions *)
  Definition Global_to_Local_Right : Local_Right_KanExt p F :=
    {|
      LRKE := Cone_for_LoKan;
      LRKE_morph_ex := Cone_Morph_to_Cone_for_LoKan;
      LRKE_morph_unique := @Cone_Morph_to_Cone_for_LoKan_Unique
    |}.

End Global_to_Local_Right.

(** Teh conversion from global left kan extensions to local left kan extensions
    is jsut the dual what we just proved. *)
Section Global_to_Local_Left.
  Context {C C' : Category}
          (p : C –≻ C')
          (D : Category)
          (lke : Left_KanExt p D)
          (F : C –≻ D).

  Definition Global_to_Local_Left : Local_Left_KanExt p F :=
    Global_to_Local_Right _ _ (KanExt_Left_to_Right _ _ lke) (F^op).

End Global_to_Local_Left.
