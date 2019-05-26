From Categories Require Import Essentials.Notations.
From Categories Require Import Essentials.Types.
From Categories Require Import Essentials.Facts_Tactics.
From Categories Require Import Category.Main.
From Categories Require Import Functor.Main.
From Categories Require Import Basic_Cons.Terminal.
From Categories Require Import Ext_Cons.Arrow.
From Categories Require Import Coq_Cats.Type_Cat.Card_Restriction.
From Categories Require Export NatTrans.NatTrans NatTrans.Operations.
From Categories Require Export KanExt.Local KanExt.Global KanExt.GlobalDuality
        KanExt.GlobaltoLocal KanExt.LocaltoGlobal KanExt.LocalFacts.Main.
From Categories Require Export Cat.Terminal.

Local Open Scope functor_scope.

(** Definition of limits and colimits using right and left kan extensions
    along the functor to the terminal category. *)
Section Limit.
  Context {J C : Category} (D : J –≻ C).

  Definition Cone := LoKan_Cone (Functor_To_1_Cat J) D.

  Definition Cone_Morph Cn Cn' :=
    @LoKan_Cone_Morph _ _ (Functor_To_1_Cat J) _ D Cn Cn'.
  
  Definition Limit : Type := Local_Right_KanExt (Functor_To_1_Cat J) D.

  Definition limit_to_cone (l : Limit) : Cone := (LRKE l).

  Coercion limit_to_cone : Limit >-> Cone.
  
  Definition cone_to_obj (cn : Cone) : C := (cone_apex cn) _o tt.

  Coercion cone_to_obj : Cone >-> Obj.

  Definition is_Limit (Cn : Cone) :=
    is_Cone_Local_Right_KanExt (Functor_To_1_Cat J) D Cn.

  Definition is_Limit_Limit {Cn : Cone} (il : is_Limit Cn) : Limit :=
    is_Cone_Local_Right_KanExt_Local_Right_KanExt (Functor_To_1_Cat J) D il.

  Definition Limit_is_Limit {L : Limit} : is_Limit L :=
    Local_Right_KanExt_is_Cone_Local_Right_KanExt (Functor_To_1_Cat J) D L.
  
End Limit.

(** Limits are unique up to isomorphism. *)
Program Definition Limit_Iso {J C : Category} {D : J –≻ C} (l l' : Limit D) :
  (l ≃≃ l' ::> C)%isomorphism :=
  {|
    iso_morphism :=
      Trans
        (cone_morph (iso_morphism (Local_Right_KanExt_unique _ _ l l')))
        tt;
    inverse_morphism :=
      Trans
        (cone_morph (inverse_morphism (Local_Right_KanExt_unique _ _ l l')))
        tt
  |}.

Next Obligation.
Proof (
    f_equal
      (fun x : LoKan_Cone_Morph l l => Trans (cone_morph x) tt)
      (left_inverse (Local_Right_KanExt_unique _ _ l l'))
  ).

Next Obligation.
Proof (
    f_equal
      (fun x : LoKan_Cone_Morph l' l' => Trans (cone_morph x) tt)
      (right_inverse (Local_Right_KanExt_unique _ _ l l'))
  ).

(** Proposition stating that category C has all limits of cardinality
    specified by P *)
Definition Has_Restr_Limits (C : Category) (P : Card_Restriction) :=
  ∀ {J : Category} (D : J –≻ C), P J → P (Arrow J) → Limit D.

(** A complete category has all limits – here it has global
    right kan extension *)
Definition Complete (C : Category) :=
  ∀ J : Category, Right_KanExt (Functor_To_1_Cat J) C.

Existing Class Complete.

(** If a category is complete, we can produce all limits. *)
Definition LimitOf {C D : Category} {H : Complete D} (F : C –≻ D) : Limit F :=
  Global_to_Local_Right _ _ (H _) F.

(** A category having restricted limitis where the restriction always holds 
is just complete. *)
Section Restricted_Limits_to_Complete.
  Context {C : Category} {P : Card_Restriction} (HRL : Has_Restr_Limits C P).

  Definition No_Restriction_Complete : (∀ t, P t) → Complete C :=
    fun All_Ps J => Local_to_Global_Right
                   _ _ (fun D => HRL _ D (All_Ps J) (All_Ps (Arrow J))).

End Restricted_Limits_to_Complete.

(** A complete category has restricted limits for any restriction. *)
Section Complete_to_Restricted_Limits.
  Context (C : Category) {CC : Complete C} (P : Card_Restriction).
  
  Definition Complete_Has_Restricted_Limits : Has_Restr_Limits C P :=
    fun J D _ _ => Global_to_Local_Right _ _ (CC _) D.

End Complete_to_Restricted_Limits.

(** A functor is continuous if it preserces all limits. *)
Section Continuous.
  Context
    {C D : Category}
    (CC : Complete C)
    (G : (C –≻ D)%functor)
  .

  Section Cone_Conv.
    Context
      {J : Category}
      {F : (J –≻ C)%functor}
      (Cn : Cone F)
    .
    
    Program Definition Cone_Conv : Cone (G ∘ F)%functor
      :=
        {|
          cone_apex :=
            (G ∘ (cone_apex Cn))%functor;
          cone_edge :=
            (((NatTrans_id G)
                ∘_h (cone_edge Cn)) ∘ (NatTrans_Functor_assoc _ _ _))%nattrans
        |}
    .

  End Cone_Conv.

  Definition Continuous :=
    ∀ (J : Category) (F : (J –≻ C)%functor),
      is_Cone_Local_Right_KanExt _ _ (Cone_Conv (LRKE (LimitOf F)))
  .

End Continuous.

(** CoLimits *)

Section CoLimit.
  Context {J C : Category} (D : J –≻ C).

  Definition CoCone :=
    LoKan_Cone (Functor_To_1_Cat J^op) (D^op).

  Definition CoCone_Morph Cn Cn' :=
    @LoKan_Cone_Morph _ _ (Functor_To_1_Cat J^op) _ (D^op) Cn Cn'.

  Definition CoLimit := Local_Left_KanExt (Functor_To_1_Cat J) D.

  Definition is_CoLimit (Cn : CoCone) :=
    is_Cone_Local_Right_KanExt (Functor_To_1_Cat (J^op)) (D^op) Cn.

  Definition is_CoLimit_CoLimit {Cn : CoCone} (il : is_CoLimit Cn) : CoLimit :=
    is_Cone_Local_Right_KanExt_Local_Right_KanExt
      (Functor_To_1_Cat (J^op)) (D^op) il.

  Definition CoLimit_is_CoLimit {L : CoLimit} : is_CoLimit L :=
    Local_Right_KanExt_is_Cone_Local_Right_KanExt
      (Functor_To_1_Cat (J^op)) (D^op) L.

End CoLimit.

(** Proposition stating that category C has all colimits of
    cardinality specified by P *)
Definition Has_Restr_CoLimits (C : Category) (P : Card_Restriction) :=
  ∀ {J : Category} (D : J –≻ C), P J → P (Arrow J) → CoLimit D.

(** A cocomplete category has all colimits – here it has global
    left kan extension *)
Definition CoComplete (C : Category) :=
  ∀ J : Category, Left_KanExt (Functor_To_1_Cat J) C.

Existing Class CoComplete.

(** If a category is cocomplete, we can produce all colimits. *)
Definition CoLimitOf {C D : Category} {H : CoComplete D} (F : C –≻ D) :
  CoLimit F := Global_to_Local_Left _ _ (H _) F.

(** If a category is complete, its dual is cocomplete *)
Definition Complete_to_CoComplete_Op {C : Category} {CC : Complete C}
  : CoComplete (C ^op) :=
fun D => KanExt_Right_to_Left (Functor_To_1_Cat D ^op) C (CC (D ^op)%category).

(** If a category is cocomplete, its dual is complete *)
Definition CoComplete_to_Complete_Op {C : Category} {CC : CoComplete C}
  : Complete (C ^op) :=
    fun D => KanExt_Left_to_Right (Functor_To_1_Cat D ^op) C (CC (D ^op)%category).

(** A category having restricted colimitis where the restriction always holds 
is just cocomplete. *)
Section Restricted_CoLimits_to_CoComplete.
  Context {C : Category} {P : Card_Restriction} (HRL : Has_Restr_CoLimits C P).

  Definition No_Restriction_CoComplete : (∀ t, P t) → CoComplete C :=
    fun All_Ps J =>
      Local_to_Global_Left _ _ (fun D => HRL _ D (All_Ps J) (All_Ps (Arrow J))).

End Restricted_CoLimits_to_CoComplete.

(** A cocomplete category has restricted colimits for any restriction. *)
Section CoComplete_to_Restricted_CoLimits.
  Context (C : Category) {CC : CoComplete C} (P : Card_Restriction).
  
  Definition CoComplete_Has_Restricted_CoLimits : Has_Restr_CoLimits C P :=
    fun J D _ _ => Global_to_Local_Left _ _ (CC _) D.

End CoComplete_to_Restricted_CoLimits.

(** If a category has restricted limits, its dual has restricted colomits *)
Definition Has_Restr_Limits_to_Has_Restr_CoLimits_Op
        {C : Category} {P : Card_Restriction}
        (HRL : Has_Restr_Limits C P) :
  Has_Restr_CoLimits (C ^op) P :=
  (fun (D : Category)
       (F : D –≻ C ^op)
       (H1 : P D)
       (H2 : P (Arrow D)) =>
     HRL
       (D ^op)%category
       (F ^op)%functor H1
       (Card_Rest_Respect P (Arrow D) (Arrow (D^op)) (Arrow_OP_Iso D) H2)
  ).

(** If a category has restricted colimits, its dual has restricted lomits *)
Definition Has_Restr_CoLimits_to_Has_Restr_Limits_Op
        {C : Category}
        {P : Card_Restriction}
        (HRL : Has_Restr_CoLimits C P) :
  Has_Restr_Limits (C ^op) P :=
  (fun (D : Category)
       (F : D –≻ C ^op)
       (H1 : P D)
       (H2 : P (Arrow D)) =>
     HRL
       (D ^op)%category
       (F ^op)%functor
       H1
       (Card_Rest_Respect P (Arrow D) (Arrow (D^op)) (Arrow_OP_Iso D) H2)
  ).

(** A functor is co-continuous if it preserces all co-limits. *)
Section CoContinuous.
  Context
    {C D : Category}
    (CC : CoComplete C)
    (G : (C –≻ D)%functor)
  .

  Section CoCone_Conv.
    Context
      {J : Category}
      {F : (J –≻ C)%functor}
      (Cn : CoCone F)
    .
    
    Program Definition CoCone_Conv : CoCone (G ∘ F)%functor
      :=
        {|
          cone_apex :=
            ((G ^op) ∘ (cone_apex Cn))%functor;
          cone_edge := _
                         (((NatTrans_id (G ^op)) ∘_h (cone_edge Cn))
                            ∘ (NatTrans_Functor_assoc _ _ _))%nattrans
        |}
    .

  End CoCone_Conv.

  Definition CoContinuous :=
    ∀ (J : Category) (F : (J –≻ C)%functor),
      is_Cone_Local_Right_KanExt _ _ (CoCone_Conv (LRKE (CoLimitOf F)))
  .

End CoContinuous.
