From Categories Require Import Essentials.Notations.
From Categories Require Import Essentials.Types.
From Categories Require Import Essentials.Facts_Tactics.
From Categories Require Import Category.Main.
From Categories Require Import Functor.Functor Functor.Functor_Ops
        Functor.Representable.Hom_Func.
From Categories Require Import NatTrans.NatTrans NatTrans.Operations
        NatTrans.Func_Cat NatTrans.NatIso.
From Categories Require Import Ext_Cons.Prod_Cat.Prod_Cat Ext_Cons.Prod_Cat.Operations
        Ext_Cons.Prod_Cat.Nat_Facts.
From Categories Require Import Adjunction.Adjunction.
From Categories Require Import KanExt.Local.
From Categories Require Import Basic_Cons.Terminal.

Local Open Scope functor_scope.

(** In this module we show uniqueness of local kan extensions by
forming category of cones and showing that the local right kan
extensions are terminal objects of those categories.
 *)
Section Facts.
  Context {C C' : Category} (p : C –≻ C')
          {D : Category} (F : C –≻ D).

  Section LoKan_Cone_Morph_eq_simplify.
    Context {Cn Cn' : LoKan_Cone p F} (M M' : LoKan_Cone_Morph Cn Cn').

    (** Two local kan extension cone morphisms are equal if their underlying
natural transformations are. *)
    Theorem LoKan_Cone_Morph_eq_simplify : M = M' :> (_ –≻ _)%nattrans → M = M'.
    Proof.
      intros H.
      destruct M; destruct M'; cbn in *.
      ElimEq.
      PIR.
      trivial.
    Qed.      

  End LoKan_Cone_Morph_eq_simplify.

  Section LoKan_id_Cone_Morph.
    Context (Cn : LoKan_Cone p F).

    Local Hint Extern 1 => apply NatTrans_eq_simplify; cbn.

    (** The identity cone morph. *)
    Program Definition LoKan_id_Cone_Morph : LoKan_Cone_Morph Cn Cn :=
      {|
        cone_morph := NatTrans_id _
      |}.

  End LoKan_id_Cone_Morph.

  Section LoKan_Cone_Morph_compose.
    Context {Cn Cn' Cn'' : LoKan_Cone p F}
            (h : LoKan_Cone_Morph Cn Cn')
            (h' : LoKan_Cone_Morph Cn' Cn'').

    (** Composition of cone morphs. *)
    Program Definition LoKan_Cone_Morph_compose : LoKan_Cone_Morph Cn Cn'' :=
      {|
        cone_morph := NatTrans_compose h h'
      |}.

    Next Obligation.
    Proof.
      rewrite (cone_morph_com h).
      rewrite (cone_morph_com h').
      rewrite NatTrans_compose_assoc.
      rewrite NatTrans_comp_hor_comp.
      rewrite NatTrans_id_unit_right.
      trivial.
    Qed.

  End LoKan_Cone_Morph_compose.

  Section LoKan_Cone_Morph_compose_assoc.
    Context {Cn Cn' Cn'' Cn''' : LoKan_Cone p F}
            (h : LoKan_Cone_Morph Cn Cn')
            (h' : LoKan_Cone_Morph Cn' Cn'')
            (h'' : LoKan_Cone_Morph Cn'' Cn''').

    (** Composition of cone morphs is associative. *)
    Theorem LoKan_Cone_Morph_compose_assoc :
      LoKan_Cone_Morph_compose h (LoKan_Cone_Morph_compose h' h'') =
      LoKan_Cone_Morph_compose (LoKan_Cone_Morph_compose h h') h''.
    Proof.
      apply LoKan_Cone_Morph_eq_simplify.
      apply NatTrans_compose_assoc.
    Qed.      

  End LoKan_Cone_Morph_compose_assoc.

  (** id_unit_left and id_unit_right for cone morphs *)
  Section LoKan_id_Cone_Morph_unit.
    Context {Cn Cn' : LoKan_Cone p F} (h : LoKan_Cone_Morph Cn Cn').

    Theorem LoKan_id_Cone_Morph_unit_right :
      LoKan_Cone_Morph_compose (LoKan_id_Cone_Morph _) h = h.
    Proof.    
      apply LoKan_Cone_Morph_eq_simplify.
      apply NatTrans_id_unit_right.
    Qed.

    Theorem LoKan_id_Cone_Morph_unit_left :
      LoKan_Cone_Morph_compose h (LoKan_id_Cone_Morph _) = h.
    Proof.    
      apply LoKan_Cone_Morph_eq_simplify.
      apply NatTrans_id_unit_left.
    Qed.

  End LoKan_id_Cone_Morph_unit.

  (** Local kan extension cones form a category. *)
  Definition LoKan_Cone_Cat : Category :=
    {|
      Obj := LoKan_Cone p F;
      Hom := LoKan_Cone_Morph;
      compose :=
        fun _ _ _ h h' =>
          LoKan_Cone_Morph_compose h h';
      assoc :=
        fun _ _ _ _ =>
          LoKan_Cone_Morph_compose_assoc;
      assoc_sym :=
        fun _ _ _ _ f g h =>
          eq_sym (LoKan_Cone_Morph_compose_assoc f g h);
      id := LoKan_id_Cone_Morph;
      id_unit_left := @LoKan_id_Cone_Morph_unit_left;
      id_unit_right := @LoKan_id_Cone_Morph_unit_right
    |}.

  (** Local right kan extensions are terminal objects of
the category of cones. *)
  Section Local_Right_KanExt_terminal.
    Context (rke : Local_Right_KanExt p F).

    Program Definition Local_Right_KanExt_terminal
      : (𝟙_ LoKan_Cone_Cat)%object :=
      {|
        terminal := LRKE rke;
        t_morph := LRKE_morph_ex rke
      |}.

    Next Obligation.
    Proof.    
      apply LoKan_Cone_Morph_eq_simplify.
      apply (LRKE_morph_unique rke).
    Qed.

  End Local_Right_KanExt_terminal.

  (** Local right kan extensions are unique – because they are
terminal objects in the category of cones. *)
  Section Local_Right_KanExt_unique.
    Context (rke rke' : Local_Right_KanExt p F).

    Theorem Local_Right_KanExt_unique :
      ((LRKE rke) ≃≃ (LRKE rke') ::> LoKan_Cone_Cat)%isomorphism.
    Proof (
        Terminal_iso
          (Local_Right_KanExt_terminal rke)
          (Local_Right_KanExt_terminal rke')
      ).
      
  End Local_Right_KanExt_unique.

  (** If cones are isomorphic, then also are objects of their their images. *)
  Section LoKan_Cone_Iso_object_Iso.
    Context {Cn Cn' : LoKan_Cone p F}
            (N : (Cn ≃≃ Cn' ::> LoKan_Cone_Cat)%isomorphism).

    Program Definition LoKan_Cone_Iso_object_Iso (c : C') :
      (Cn _o c ≃ Cn' _o c)%isomorphism :=
      {|
        iso_morphism := Trans (iso_morphism N) c;
        inverse_morphism := Trans (inverse_morphism N) c
      |}.

    Next Obligation.
    Proof.
      change (Trans (inverse_morphism N) c ∘ Trans (iso_morphism N) c)%morphism
      with (Trans ((inverse_morphism N) ∘ (iso_morphism N))%nattrans c).
      cbn_rewrite (f_equal (cone_morph) (left_inverse N)); trivial.
    Qed.

    Next Obligation.
    Proof.
      change (Trans (iso_morphism N) c ∘ Trans (inverse_morphism N) c)%morphism
      with (Trans ((iso_morphism N) ∘ (inverse_morphism N))%nattrans c).
      cbn_rewrite (f_equal (cone_morph) (right_inverse N)); trivial.
    Qed.

  End LoKan_Cone_Iso_object_Iso.

End Facts.
