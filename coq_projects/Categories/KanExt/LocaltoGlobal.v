From Categories Require Import Essentials.Notations.
From Categories Require Import Essentials.Types.
From Categories Require Import Essentials.Facts_Tactics.
From Categories Require Import Category.Main.
From Categories Require Import Functor.Functor Functor.Functor_Ops
        Functor.Representable.Hom_Func_Prop.
From Categories Require Import Functor.Functor_Extender.
From Categories Require Import Ext_Cons.Prod_Cat.Prod_Cat.
From Categories Require Import NatTrans.NatTrans NatTrans.Operations NatTrans.Func_Cat.
From Categories Require Import Adjunction.Adjunction Adjunction.Duality Adjunction.Adj_Facts.
From Categories Require Import KanExt.Global KanExt.Local KanExt.LocalFacts.Uniqueness
        KanExt.GlobalDuality.

Local Open Scope functor_scope.

(** This module contains conversion from local to global kan extensions. 
That is, we show that if we have all local kan extensions, we also have
the global kan extension.
 *)

(** To do this, we need to build a functor from (Func_Cat C D) to 
(Func_Cat C' D). That means we have to provide a natural transformation
(a cone morph) from the local kan extension of one functor to the local
kan extension of another functor. Of course, this is easy as each local
right kan extension is the terminal object of the category of cones there
always is a cone morph to it. The only practical difficulty is converting
the local kan extension of a functor (which is a cone for that functor) to
the cone of another functor – and provide necessary tools for conversion.
This is waht we do below.
*)
Section Local_to_Global_Right.
  Context {C C' : Category}
          (p : C –≻ C')
          (D : Category)
          (rke : ∀ F : C –≻ D,  Local_Right_KanExt p F)
  .

  (** Conversion from a cone of a functor to the cone of another functor.
The appex remains the same (the objects in D are not changed) but the
cone_edge does – see below. *)
  Section Cone_conv.
    Context {F G : C –≻ D} (N : (F –≻ G)%nattrans) (Cn : LoKan_Cone p F).

    Definition Cone_conv : LoKan_Cone p G :=
      {|
        cone_apex := Cn;
        cone_edge := NatTrans_compose Cn N
      |}.

  End Cone_conv.

  Section Cone_conv_Morph_for_compose.
    Context {F G H : C –≻ D}
            (N : (F –≻ G)%nattrans)
            (N' : (G –≻ H)%nattrans)
            (Cn : LoKan_Cone p F)
    .

    (** If we convert using the composition of two natural transformations it is
        the same as converting twice. We show this by building a cone morph from
        the former to the latter which is simply an identity natural
        transformation. In cases such as this, proving equality requires
        destruction of equality proofs in terms whereas composing with the
        identity natural transformation gives a composition with identity
        morphism at the level of the terms produced. *)
    Program Definition Cone_conv_Morph_for_compose :
      LoKan_Cone_Morph (Cone_conv (N' ∘ N) Cn) (Cone_conv N' (Cone_conv N Cn))
      :=
      {|
        cone_morph := NatTrans_id Cn
      |}.
    
    Next Obligation.
    Proof.
      rewrite NatTrans_hor_comp_ids.
      rewrite NatTrans_id_unit_right.
      rewrite NatTrans_compose_assoc; trivial.
    Qed.      

  End Cone_conv_Morph_for_compose.

  Section Cone_Morph_conv.
    Context {F G : C –≻ D}
            (N : (F –≻ G)%nattrans)
            {Cn Cn' : LoKan_Cone p F}
            (h : LoKan_Cone_Morph Cn Cn')
    .

    (** Conversion of cone morphs. *)
    Program Definition Cone_Morph_conv :
      LoKan_Cone_Morph (Cone_conv N Cn) (Cone_conv N Cn') :=
      {|
        cone_morph := h
      |}.

    Next Obligation.
    Proof.
      unfold Cone_conv; cbn.
      rewrite NatTrans_compose_assoc.
      rewrite (cone_morph_com h).
      trivial.
    Qed.
    
  End Cone_Morph_conv.

  (** For any functor (that can be the functor of a cone), there is a functor
for which it is cone trivially. *)
  Section Trivial_Cone.
    Context (F : C' –≻ D).

    Definition Trivial_Cone : LoKan_Cone p (Functor_compose p F) :=
      {|
        cone_apex := F;
        cone_edge := ((NatTrans_id F) ∘_h (NatTrans_id p))%nattrans
      |}.

  End Trivial_Cone.

  Section Trivial_Cone_Morph.
    Context {F G : C' –≻ D} (N : (F –≻ G)%nattrans).

    (** If N : F -> G is a natural transformation, then there is a trivial cone
        morphism from trivial cone of F to trivial cone of G – after
        conversion. *)
    Program Definition Trivial_Cone_Morph :
      LoKan_Cone_Morph
        (Cone_conv (N ∘_h (NatTrans_id p)) (Trivial_Cone F))
        (Trivial_Cone G) :=
      {|
        cone_morph := N
      |}.

    Next Obligation.
    Proof.
      repeat rewrite NatTrans_hor_comp_ids.
      rewrite NatTrans_id_unit_left.
      rewrite NatTrans_id_unit_right.
      trivial.
    Qed.
      
  End Trivial_Cone_Morph.

  Section Cone_Morph_to_other_Cone.
    Context {L : C' –≻ D}
            {F : C –≻ D}
            (Cn : LoKan_Cone p F)
            (N : (L –≻ Cn)%nattrans)
    .

    (** Given a natural transformation from some functor L : C' -> D to a cone 
        (the underlying functor) we construct a cone morphism from trivial cone
        of L (after conversion) to the given cone. *)
    Program Definition Cone_Morph_to_other_Cone :
      LoKan_Cone_Morph
        (Cone_conv (Cn ∘ (N ∘_h (NatTrans_id p))) (Trivial_Cone L))
        Cn :=
      {|
        cone_morph := N
      |}.

    Next Obligation.
      rewrite NatTrans_hor_comp_ids.
      rewrite NatTrans_id_unit_right.
      trivial.
    Qed.
    
  End Cone_Morph_to_other_Cone.

  Local Obligation Tactic := idtac.

  (** The functor (mapping functors to their kan extensions) for global
      kan extension. *)
  Program Definition Local_to_Global_Right_Functor :
    (Func_Cat C D) –≻ (Func_Cat C' D) :=
    {|
      FO := fun F => LRKE (rke F);
      FA := fun F G N => LRKE_morph_ex (rke G) (Cone_conv N (LRKE (rke F)))
    |}.
  
  Next Obligation.
  Proof.
    intros F; cbn.
    unfold Cone_conv.
    rewrite NatTrans_id_unit_left.
    change (NatTrans_id (LRKE (rke F)))
    with (cone_morph (LoKan_id_Cone_Morph _ _ (LRKE (rke F)))).
    apply LRKE_morph_unique.
  Qed.

  Next Obligation.
  Proof.
    intros F G H N N'; cbn.
    match goal with
      [|- _ = ?A] =>
      match A with
      | ((cone_morph ?Y) ∘ (cone_morph ?X))%nattrans =>
        replace A with (A ∘(NatTrans_id _))%nattrans;
          [|apply NatTrans_id_unit_right];
        set (V := (LoKan_Cone_Morph_compose _ _ (Cone_Morph_conv N' X) Y));
        set (Z := Cone_conv_Morph_for_compose N N' (LRKE (rke F)));
        set (U := cone_morph (LoKan_Cone_Morph_compose _ _ Z V));
        unfold V, Z in U; clear V Z
      end
    end.
    match goal with
      [|- _ = ?A] =>
      change A with U
    end.
    apply (LRKE_morph_unique (rke H) (Cone_conv (N' ∘ N) (LRKE (rke F)))).
  Qed.

  (** The unit of adjunction for global kan extension. *)
  Program Definition Local_to_Global_Right_adj_unit :
      ((Functor_id (Func_Cat C' D))
         –≻ (Functor_compose
               (Left_Functor_Extender p D)
               Local_to_Global_Right_Functor))%nattrans
    :=
    {|
      Trans := fun F => LRKE_morph_ex (rke (F ∘ p)) (Trivial_Cone F)
    |}.

  Next Obligation.
  Proof.
    intros F G N.
    cbn.
    change N with (cone_morph (Trivial_Cone_Morph N)).
    match goal with
      [|- ?X = ?Y] =>
      match X with
        ((cone_morph ?B) ∘ (cone_morph ?A))%nattrans =>
        change X with (cone_morph (LoKan_Cone_Morph_compose _ _ A B))
      end;
        match Y with
          ((cone_morph ?B) ∘ (cone_morph ?A))%nattrans =>
          change Y
          with (cone_morph
                  (LoKan_Cone_Morph_compose
                     _ _ (Cone_Morph_conv (N ∘_h (NatTrans_id p)) A) B
                  )
               )
        end
    end.
    apply (LRKE_morph_unique
             (rke (Functor_compose p G))
             (Cone_conv (N ∘_h (NatTrans_id p)) (Trivial_Cone F))
          ).
  Qed.    

  Next Obligation.
  Proof.
    symmetry.
    apply Local_to_Global_Right_adj_unit_obligation_1.
  Qed.

  (** Existence of conversion for adjunction – see definition of Adjunct. *)
  Definition Local_to_Global_Right_adj_morph_ex
             (L : C' –≻ D)
             (F : C –≻ D)
             (N : (L –≻ (LRKE (rke F)))%nattrans)
    : ((L ∘ p) –≻ F)%nattrans :=
    ((cone_edge (LRKE (rke F))) ∘ (N ∘_h (NatTrans_id p)))%nattrans.

  (** Conversion from local kan extensions (if we have all of them) to the 
      global kan extension. *)
  Program Definition Local_to_Global_Right : Right_KanExt p D :=
    {|
      right_kan_ext := Local_to_Global_Right_Functor;
      right_kan_ext_adj := {|
                            adj_unit := Local_to_Global_Right_adj_unit;
                            adj_morph_ex := Local_to_Global_Right_adj_morph_ex|}
    |}.

  Next Obligation.
  Proof.
    intros L F h.
    unfold Local_to_Global_Right_adj_morph_ex.
    cbn in *.
    match goal with
      [|- ?X = ?Y] =>
        match Y with
          ((cone_morph ?B) ∘ (cone_morph ?A))%nattrans =>
          change Y
          with (cone_morph
                  (LoKan_Cone_Morph_compose
                     _ _
                     (Cone_Morph_conv
                        ((LRKE (rke F) ∘ (h ∘_h (NatTrans_id p)))) A) B
                  )
               )
        end
    end.
    change h with (cone_morph (Cone_Morph_to_other_Cone (LRKE (rke F)) h)).
    apply (LRKE_morph_unique
             (rke F)
             (Cone_conv ((LRKE (rke F))
                           ∘ (h ∘_h (NatTrans_id p))) (Trivial_Cone L))
          ).
  Qed.

  Next Obligation.
  Proof.
    intros L F h g g' H1 H2.
    cbn in *.
    match type of H1 with
      _ = ?X =>
      match X with
          NatTrans_compose (cone_morph ?A) (cone_morph ?B) =>
          change X with
          (cone_morph(LoKan_Cone_Morph_compose _ _ (Cone_Morph_conv g A) B))
            in H1
      end
    end.
    match type of H2 with
      _ = ?X =>
      match X with
          NatTrans_compose (cone_morph ?A) (cone_morph ?B) =>
          change X with
          (cone_morph (LoKan_Cone_Morph_compose _ _ (Cone_Morph_conv g' A) B))
            in H2
      end
    end.
    match type of H1 with
      _ = cone_morph ?X =>
      set (H4 := cone_morph_com X); rewrite <- H1 in H4; cbn in H4;
      match type of H2 with
        _ = cone_morph ?Y =>
        set (H3 := cone_morph_com Y); rewrite <- H2 in H3; cbn in H3
      end;
      rewrite <- H4 in H3; clear H4
    end.
    rewrite NatTrans_hor_comp_ids in H3.
    repeat rewrite NatTrans_id_unit_right in H3.
    symmetry; trivial.
  Qed.

End Local_to_Global_Right.

(** The conversion from local left kan extensions to global left kan extensions 
    is just the daul of that for right. *)
Section Local_to_Global_Left.
  Context {C C' : Category} (p : C –≻ C') (D : Category).

  Context (lke : ∀ F : C –≻ D,  Local_Left_KanExt p F).

  Definition Local_to_Global_Left : Left_KanExt p D :=
    KanExt_Right_to_Left
      _ _ (Local_to_Global_Right _ _ (fun (F : C^op –≻ D^op) => (lke (F^op)))).

End Local_to_Global_Left.

