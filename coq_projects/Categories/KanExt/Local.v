From Categories Require Import Essentials.Notations.
From Categories Require Import Essentials.Types.
From Categories Require Import Essentials.Facts_Tactics.
From Categories Require Import Category.Main.
From Categories Require Import Functor.Functor Functor.Functor_Ops Functor.Representable.Hom_Func.
From Categories Require Import Ext_Cons.Prod_Cat.Prod_Cat Ext_Cons.Prod_Cat.Operations.
From Categories Require Import NatTrans.NatTrans NatTrans.Operations NatTrans.Func_Cat NatTrans.NatIso.
From Categories Require Import Functor.Functor_Extender.

(**
Given a functor p : C -> C' and a functor F : C -> D, the local right
kan extension of F along p is functor G : C' -> D together with natural
transformation η : G ∘ p -> F:
#
<pre>
          F
      C ——————–————> D
      | \          ↗
    p |  \ η     /
      |    ↘   / G
      |      / 
      |    /
      ↓  / 
      C'
</pre>
#

such that for any G' : C' -> D and η' : G' ∘ p -> F we have a unique natrual
transformation ε : G' → G such that the following diagram
(natural transformations η, η' and ε) commute:
 #
<pre>
          F
      C —————–——————–——–——————————–> D
      | \ \       _______________↗  ↗
    p |  \  \η' /      G'         /
      | η \   ↘/               / 
      |    \  /   ε          / 
      |     \/ —————–—>  / G
      |     /\        /
      |    /  ↘    /
      |   /     /
      |  /   /
      ↓ / / 
      C'
</pre>
#

In the follwing, we separate this notion into three parts:
  1. Local Kan extension Cones (LoKan_Cone)
      is a functor G together with a natural transformation η : G ∘ p -> F

  2. Local Kan extesion Cone Morphisms (Lokan_Cone_Morph)
      is a natrual transformation from underlying functor of the domain cone to
      the underlying functor of the co-domain cone such that makes it makes the
      natural transformations commute (see defintion above).

  3. Lokan Right Kan Extensions (Local_Right_KanExt)
     is in principle the terminal cone in the category† defined above (objects
     are cones and arrows are cone morphisms).

______________________
# <br> <br/> #
†) We separately show that these cones and cone morphisms create a category. We
   will use this to show that local kan extensions (as terminal objects of this
   category) are unique.

*)
Section KanExtension.
  Context {C C' : Category} (p : (C –≻ C')%functor).

  Section Right.
    Context {D : Category} (F : (C –≻ D)%functor).

    Record LoKan_Cone : Type :=
      {
        cone_apex : (C' –≻ D)%functor;
        cone_edge : ((cone_apex ∘ p) –≻ F)%nattrans
      }.

    Coercion cone_apex : LoKan_Cone >-> Functor.
    Coercion cone_edge : LoKan_Cone >-> NatTrans.

    Section LoKan_Cone_Morph.
      Context (Cn Cn' : LoKan_Cone).

      Record LoKan_Cone_Morph : Type :=
        {
          cone_morph : (Cn –≻ Cn')%nattrans;
          cone_morph_com :
            Cn = (Cn' ∘ (cone_morph
                           ∘_h (NatTrans_id p)))%nattrans :> (_ –≻ _)%nattrans
        }.

      Coercion cone_morph : LoKan_Cone_Morph >-> NatTrans.

    End LoKan_Cone_Morph.

    Record Local_Right_KanExt :=
      {
        LRKE : LoKan_Cone;
        LRKE_morph_ex : ∀ (Cn : LoKan_Cone), LoKan_Cone_Morph Cn LRKE;
        LRKE_morph_unique :
          ∀ (Cn : LoKan_Cone)
            (h h' : LoKan_Cone_Morph Cn LRKE), h = h' :> (_ –≻ _)%nattrans
      }.

    Coercion LRKE : Local_Right_KanExt >-> LoKan_Cone.

    (** The predicate form of local right kan extensions. *)
    Record is_Local_Right_KanExt (Cn_apex : (C' –≻ D)%functor) :=
      {
        isLRKE_Cn_edge : ((Cn_apex ∘ p) –≻ F)%nattrans;
        isLRKE_morph_ex : ∀ (Cn : LoKan_Cone), LoKan_Cone_Morph
                                                 Cn
                                                 {|cone_apex :=
                                                     Cn_apex;
                                                   cone_edge := isLRKE_Cn_edge
                                                 |};
        isLRKE_morph_unique : ∀ (Cn : LoKan_Cone)
                                (h h' : LoKan_Cone_Morph
                                          Cn
                                          {|cone_apex := Cn_apex;
                                            cone_edge := isLRKE_Cn_edge
                                          |}),
            h = h' :> (_ –≻ _)%nattrans
      }.

    (** The predicate from implies the compact form. *)
    Definition is_Local_Right_KanExt_Local_Right_KanExt
               {Cn_apex : (C' –≻ D)%functor}
               (ilrke : is_Local_Right_KanExt Cn_apex) : Local_Right_KanExt :=
      {|
        LRKE := {|cone_apex := Cn_apex; cone_edge := @isLRKE_Cn_edge _ ilrke|};
        LRKE_morph_ex := @isLRKE_morph_ex _ ilrke;
        LRKE_morph_unique := @isLRKE_morph_unique _ ilrke
      |}.

    (** The compact form implies the preicate form. *)
    Definition Local_Right_KanExt_is_Local_Right_KanExt
               (lrke : Local_Right_KanExt)
      : is_Local_Right_KanExt lrke :=
      {|
        isLRKE_Cn_edge := lrke;
        isLRKE_morph_ex := @LRKE_morph_ex lrke;
        isLRKE_morph_unique := @LRKE_morph_unique lrke
      |}.

    (** The predicate form of local right kan extensions for cones. *)
    Record is_Cone_Local_Right_KanExt (Cn : LoKan_Cone) :=
      {
        isCLRKE_morph_ex : ∀ (Cn' : LoKan_Cone), LoKan_Cone_Morph Cn' Cn;
        isCLRKE_morph_unique :
          ∀ (Cn' : LoKan_Cone) (h h' : LoKan_Cone_Morph Cn' Cn),
            h = h' :> (_ –≻ _)%nattrans
      }.

    (** The predicate from implies the compact form. *)
    Definition is_Cone_Local_Right_KanExt_Local_Right_KanExt {Cn : LoKan_Cone}
               (ilrke : is_Cone_Local_Right_KanExt Cn) : Local_Right_KanExt :=
      {|
        LRKE := Cn;
        LRKE_morph_ex := @isCLRKE_morph_ex _ ilrke;
        LRKE_morph_unique := @isCLRKE_morph_unique _ ilrke
      |}.

    (** The compact form implies the preicate form. *)
    Definition Local_Right_KanExt_is_Cone_Local_Right_KanExt
               (lrke : Local_Right_KanExt)
      : is_Cone_Local_Right_KanExt lrke :=
      {|
        isCLRKE_morph_ex := @LRKE_morph_ex lrke;
        isCLRKE_morph_unique := @LRKE_morph_unique lrke
      |}.
    
  End Right.
  
End KanExtension.

(** The local left kan extension is simply defined as the dual of local
    right kan extension. *)
Section Left.
  Context {C C' : Category} (p : (C –≻ C')%functor)
          {D : Category} (F : (C –≻ D)%functor).

  Definition Local_Left_KanExt := Local_Right_KanExt (p^op) (F^op).

  Definition is_Local_Left_KanExt (Cn_apex : (C' –≻ D)%functor) :=
    is_Local_Right_KanExt (p^op) (F^op) (Cn_apex^op)
  .
  
End Left.
  
Arguments cone_apex {_ _ _ _ _} _.
Arguments cone_edge {_ _ _ _ _} _.
Arguments LoKan_Cone_Morph {_ _ _ _ _} _ _.
Arguments cone_morph {_ _ _ _ _ _ _} _.
Arguments cone_morph_com {_ _ _ _ _ _ _} _.
Arguments LRKE {_ _ _ _ _} _.
Arguments LRKE_morph_ex {_ _ _ _ _} _ _.
Arguments LRKE_morph_unique {_ _ _ _ _} _ _ _ _.


(** The local kan extension defined using hom-functors. In short:
    HLRKE : C' -> D is the local right kan extension of F : C -> D
    along p : C -> C' if the following isomorphism holds:

    Hom_{D^C}(–, F) ∘ (Left_Functor_Extender p D)ᵒᵖ ≃ Hom_{D^C'}(–, HLRKE)

    Note that: (Left_Functor_Extender p D) : (D^C') -> (D^C).
 *)
Section Hom_Local_Right_KanExt.
  Context {C C' : Category} (p : (C –≻ C')%functor)
          {D : Category} (F : (C –≻ D)%functor).

  Definition Hom_Local_Right_KanExt_Isomorphism (HLRKE : (C' –≻ D)%functor) :=
    (
      (
        (@Fix_Bi_Func_2 _ (Func_Cat _ _) _ F (Hom_Func (Func_Cat C D)))
          ∘ (Left_Functor_Extender p D)^op
      )%functor
       ≃
       (
         @Fix_Bi_Func_2 _ (Func_Cat _ _) _ HLRKE (Hom_Func (Func_Cat C' D))
       )
    )%natiso
  .
  
  Record Hom_Local_Right_KanExt := 
    {
      HLRKE : (C' –≻ D)%functor;
      HLRKE_Iso : Hom_Local_Right_KanExt_Isomorphism HLRKE
    }.
  
  Coercion HLRKE : Hom_Local_Right_KanExt >-> Functor.
  
End Hom_Local_Right_KanExt.

Section Hom_Local_Left_KanExt.
  Context {C C' : Category} (p : (C –≻ C')%functor)
          {D : Category} (F : (C –≻ D)%functor).

  Definition Hom_Local_Left_KanExt :=
    Hom_Local_Right_KanExt (p^op) (F^op).
  
End Hom_Local_Left_KanExt.

Arguments HLRKE {_ _ _ _ _} _.
Arguments HLRKE_Iso {_ _ _ _ _} _.
