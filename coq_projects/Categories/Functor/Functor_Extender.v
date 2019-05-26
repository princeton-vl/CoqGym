From Categories Require Import Essentials.Notations.
From Categories Require Import Essentials.Types.
From Categories Require Import Essentials.Facts_Tactics.
From Categories Require Import Category.Main.
From Categories Require Import Functor.Functor Functor.Functor_Ops.
From Categories Require Import NatTrans.Main.

(** Local notations for readability *)
Local Notation NID := NatTrans_id (only parsing).

Local Hint Extern 1 => progress
                        (repeat (apply NatTrans_eq_simplify; FunExt); cbn in *).

(** for a functor p : C -> C' and a category D, the left functor extender is a
     functor that maps (as an object) functor F : C' -> D to F ∘ p : C -> D.  *)
Section Left_Functor_Extender.
  Context {C C' : Category} (p : (C –≻ C')%functor) (D : Category).

    Program Definition Left_Functor_Extender :
      ((Func_Cat C' D) –≻ (Func_Cat C D))%functor :=
      {|
        FO := fun F => (F ∘ p)%functor;
        FA := fun F F' N => (N ∘_h (NID p))%nattrans
      |}.

End Left_Functor_Extender.

(** for a functor p : C -> C' and a category D, the left functor extender is a
    functor that maps (as an object) functor F : D -> C to p ∘ F : D -> C'.  *)
Section Right_Functor_Extender.
  Context {C C' : Category} (p : (C –≻ C')%functor) (D : Category).

    Program Definition Right_Functor_Extender :
      ((Func_Cat D C) –≻ (Func_Cat D C'))%functor :=
      {|
        FO := fun F => (p ∘ F)%functor;
        FA := fun F F' N => ((NID p) ∘_h N)%nattrans
      |}.

End Right_Functor_Extender.

(** if two functors are naturally isomorphic then so are left exending with them. *)
Section Left_Functor_Extender_Iso.
  Context {C C' : Category} {p p' : (C –≻ C')%functor}
          (N : (p ≃ p')%natiso) (D : Category).

  Local Hint Extern 1 => (rewrite Trans_com); trivial; fail.
  Local Hint Extern 1 => rewrite <- F_compose.
  Local Hint Extern 1 =>
  match goal with
    [w : @Obj C |- _] =>
    cbn_rewrite (f_equal (fun u => Trans u w) (left_inverse N))
  end.
  Local Hint Extern 1 =>
  match goal with
    [w : @Obj C |- _] =>
    cbn_rewrite (f_equal (fun u => Trans u w) (right_inverse N))
  end.

  
  Program Definition Left_Functor_Extender_Iso :
    ((Left_Functor_Extender p D) ≃ (Left_Functor_Extender p' D))%natiso
    :=
      {|
        iso_morphism :=
          {|
            Trans :=
              fun e =>
                ((NatTrans_id_Iso e) ∘_h N)%natiso
          |};
        inverse_morphism :=
          {|
            Trans :=
              fun e =>
                ((NatTrans_id_Iso e) ∘_h (N⁻¹))%natiso
          |}
      |}
  .
      
End Left_Functor_Extender_Iso.

(** if two functors are naturally isomorphic then so are right exending with them. *)
Section Right_Functor_Extender_Iso.
  Context {C C' : Category} {p p' : (C –≻ C')%functor}
          (N : (p ≃ p')%natiso) (D : Category).
  
  Local Hint Extern 1 => (rewrite Trans_com); trivial; fail.
  Local Hint Extern 1 => rewrite <- F_compose.
  Local Hint Extern 1 =>
  match goal with
    [w : @Obj D, F : (D –≻ C)%functor |- _] =>
    cbn_rewrite (f_equal (fun u => Trans u (F _o w)%object) (left_inverse N))
    end.
  Local Hint Extern 1 =>
  match goal with
    [w : @Obj D, F : (D –≻ C)%functor |- _] =>
    cbn_rewrite (f_equal (fun u => Trans u (F _o w)%object) (right_inverse N))
    end.

  
  Program Definition Right_Functor_Extender_Iso :
    ((Right_Functor_Extender p D) ≃ (Right_Functor_Extender p' D))%natiso
    :=
      {|
        iso_morphism :=
          {|
            Trans :=
              fun e =>
                (N ∘_h (NatTrans_id_Iso e))%natiso
          |};
        inverse_morphism :=
          {|
            Trans :=
              fun e =>
                ((N⁻¹) ∘_h (NatTrans_id_Iso e))%natiso
          |}
      |}
  .
 
End Right_Functor_Extender_Iso.

Section Right_Left_Functor_Extension_Iso.
  Context {B C D E : Category} (F : (B –≻ C)%functor) (G : (D –≻ E)%functor).
  
  (** It doesn't matter if we first extend from left or right.
      The resulting functors are isomorphic. *)
  Program Definition Right_Left_Functor_Extension_Iso :
    (
      (((Right_Functor_Extender G B) ∘ (Left_Functor_Extender F D))%functor)
        ≃ ((Left_Functor_Extender F E) ∘ (Right_Functor_Extender G C))%functor
    )%natiso :=
    {|
      iso_morphism := {|Trans := fun h => NatTrans_Functor_assoc_sym F h G |};
      inverse_morphism := {|Trans := fun h => NatTrans_Functor_assoc F h G |}
    |}.

End Right_Left_Functor_Extension_Iso.
