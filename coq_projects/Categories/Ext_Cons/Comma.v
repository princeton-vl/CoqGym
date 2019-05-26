From Categories Require Import Essentials.Notations.
From Categories Require Import Essentials.Types.
From Categories Require Import Essentials.Facts_Tactics.
From Categories Require Import Category.Category Category.Morph Category.Opposite.
From Categories Require Import Ext_Cons.Arrow.
From Categories Require Import Functor.Functor Functor.Functor_Ops Const_Func.
From Categories Require Import Archetypal.Discr.Discr.
From Categories Require Import Cat.Cat Cat.Cat_Iso.
From Categories Require Import NatTrans.NatTrans NatTrans.NatIso.

Local Open Scope morphism_scope.

(**
A comma category for Functors F : B → C and G : D → C is a category whose
objects are arrows in C

#
<pre>   
   F _o x ———————–> G _o y
</pre>
#

for x an object of B and y an object of D. Arrows of comma are commutative
diagrams in C:

#
<pre>
         F _o x ———————–> G _o y
           |                |
           |                |
   F _a h  |                |  F _a h'
           |                |
           |                |
           ↓                ↓
         F _o x' ———————–> G _o y'
</pre>
#

for h : x → x' an arrow in B and h' : y → y' an arrow in G.
 
*)
Section Comma.
  Context {B C D : Category} (F : (B –≻ C)%functor) (G : (D –≻ C)%functor).

  Record Comma_Obj : Type :=
    {
      CMO_src : B;
      CMO_trg : D;
      CMO_hom : ((F _o CMO_src) –≻ (G _o CMO_trg))%object
    }.

  Record Comma_Hom (a b : Comma_Obj) : Type :=
    {
      CMH_left : (CMO_src a) –≻ (CMO_src b);
      CMH_right : (CMO_trg a) –≻ (CMO_trg b);
      CMH_com :  ((G _a CMH_right) ∘ (@CMO_hom a) =
                  (@CMO_hom b) ∘ (F _a CMH_left))%morphism
    }.

  Arguments CMH_left {_ _} _.
  Arguments CMH_right {_ _} _.
  Arguments CMH_com {_ _} _.

  Theorem Comma_Hom_eq_simplify {a b : Comma_Obj} (h h' : Comma_Hom a b) :
    (@CMH_left _ _ h) = (@CMH_left _ _ h') →
    (@CMH_right _ _ h) = (@CMH_right _ _ h') → h = h'.
  Proof.
    intros H1 H2.
    destruct h; destruct h'.
    cbn in *.
    ElimEq.
    PIR.
    trivial.
  Qed.

  Program Definition Comma_Hom_compose
          {a b c : Comma_Obj} (h : Comma_Hom a b) (h' : Comma_Hom b c) :
    Comma_Hom a c :=
    {|
      CMH_left := (CMH_left h') ∘ (CMH_left h);
      CMH_right := (CMH_right h') ∘ (CMH_right h)
    |}.

  Next Obligation.
  Proof.
    repeat rewrite F_compose.
    rewrite assoc.
    rewrite CMH_com.
    rewrite assoc_sym.
    rewrite CMH_com.
    auto.
  Qed.

  Theorem Comma_Hom_compose_assoc {a b c d : Comma_Obj} (h : Comma_Hom a b)
          (h' : Comma_Hom b c) (h'' : Comma_Hom c d) :
    Comma_Hom_compose h (Comma_Hom_compose h' h'') =
    Comma_Hom_compose (Comma_Hom_compose h h') h''.
  Proof.                    
    apply Comma_Hom_eq_simplify; cbn; auto.
  Qed.    

  Program Definition Comma_Hom_id (a : Comma_Obj) : Comma_Hom a a :=
    {|
      CMH_left := id;
      CMH_right := id
    |}.

  Theorem Comma_Hom_id_unit_left {a b : Comma_Obj} (h : Comma_Hom a b) :
    Comma_Hom_compose h (Comma_Hom_id b) = h.
  Proof.
    apply Comma_Hom_eq_simplify; cbn; auto.
  Qed.

  Theorem Comma_Hom_id_unit_right {a b : Comma_Obj} (h : Comma_Hom a b) :
    Comma_Hom_compose (Comma_Hom_id a) h = h.
  Proof.
    apply Comma_Hom_eq_simplify; cbn; auto.
  Qed.

  
  Definition Comma : Category :=
    {|
      Obj := Comma_Obj;

      Hom := Comma_Hom;

      compose := @Comma_Hom_compose;

      assoc := @Comma_Hom_compose_assoc;

      assoc_sym := fun _ _ _ _ f g h => eq_sym (Comma_Hom_compose_assoc f g h);
      
      id := Comma_Hom_id;

      id_unit_right := @Comma_Hom_id_unit_right;

      id_unit_left := @Comma_Hom_id_unit_left
    |}.

End Comma.

Arguments CMO_src {_ _ _ _ _} _.
Arguments CMO_trg {_ _ _ _ _} _.
Arguments CMO_hom {_ _ _ _ _} _.
Arguments CMH_left {_ _ _ _ _ _ _} _.
Arguments CMH_right {_ _ _ _ _ _ _} _.
Arguments CMH_com {_ _ _ _ _ _ _} _.

(** In this section we show that the opposite the comma category of (Comma F G)
is isomorphic to the comma category (Comma Gᵒᵖ Fᵒᵖ).
 *)
Section Comma_Opposite_Iso.
  Context {B C D : Category} (F : (B –≻ C)%functor) (G : (D –≻ C)%functor).

  Local Hint Extern 1 => progress cbn.

  Local Hint Extern 1 => apply Comma_Hom_eq_simplify.
  
  Program Definition Comma_Opposite_Iso_LR :
    Functor ((Comma F G)^op) (Comma (G ^op) (F ^op))
    :=
      {|
        FO :=
          fun x =>
            {|
              CMO_src := CMO_trg x;
              CMO_trg := CMO_src x;
              CMO_hom := CMO_hom x
            |};
        FA :=
          fun c c' h =>
            {|
              CMH_left := CMH_right h;
              CMH_right := CMH_left h;
              CMH_com := eq_sym (CMH_com h)
            |}
      |}.

  Program Definition Comma_Opposite_Iso_RL :
    Functor (Comma (G ^op) (F ^op)) ((Comma F G)^op)
    :=
      {|
        FO :=
          fun x =>
            {|
              CMO_src := CMO_trg x;
              CMO_trg := CMO_src x;
              CMO_hom := CMO_hom x
            |};
        FA :=
          fun c c' h =>
            {|
              CMH_left := CMH_right h;
              CMH_right := CMH_left h;
              CMH_com := eq_sym (CMH_com h)
            |}
      |}.
    
    
  Program Definition Comma_Opposite_Iso :
    (((Comma F G)^op)%category ≃≃ Comma (G ^op) (F ^op) ::> Cat)%isomorphism
    :=
      {|
        iso_morphism := Comma_Opposite_Iso_LR;
        inverse_morphism := Comma_Opposite_Iso_RL
      |}
  .

End Comma_Opposite_Iso.

(** In this section we show that whenever F and F' are two naturally
isomorphic functors, then (Comma F G) is isomorphic to (Comma F' G).
 *)
Section Comma_Left_Func_Iso.
  Context {B C D : Category}.

  Local Hint Extern 1 => progress cbn.

  Local Hint Extern 1 => apply Comma_Hom_eq_simplify.

  Section Comma_Left_Func_Iso_FC.
    Context
      {F F' : (B –≻ C)%functor}
      (I : (F ≃ F')%natiso)
      (G : (D –≻ C)%functor)
    .

    (** Given a natural isomorphism we build a functor. *)
    Program Definition Comma_Left_Func_Iso_FC :
      Functor (Comma F G) (Comma F' G)
      :=
        {|
          FO :=
            fun x =>
              {|
                CMO_src := CMO_src x;
                CMO_trg := CMO_trg x;
                CMO_hom := (CMO_hom x) ∘ (Trans (inverse_morphism I) (CMO_src x))
              |};
          FA :=
            fun c c' h =>
              {|
                CMH_left := CMH_left h;
                CMH_right := CMH_right h;
              CMH_com := _
              |}
        |}.
    
    Next Obligation.
    Proof.
      rewrite assoc_sym.
      rewrite (CMH_com h).
      rewrite assoc.
      rewrite <- (Trans_com (inverse_morphism I) (CMH_left h)).
      auto.    
    Qed.
    
  End Comma_Left_Func_Iso_FC.

  Section Comma_Left_Func_Iso_FC_Iso.
    Context
      {F F' : (B –≻ C)%functor}
      (I : (F ≃ F')%natiso)
      (G : (D –≻ C)%functor)
    .

    (** Functors produced from a natural isomorphism and its inverse
are inverses.
*)
    Lemma Comma_Left_Func_Iso_FC_Iso :
      ((Comma_Left_Func_Iso_FC I G)
         ∘
         (Comma_Left_Func_Iso_FC (Inverse_Isomorphism I) G))%functor
      =
      Functor_id _
    .
    Proof.
      Func_eq_simpl.
      {
        extensionality x.
        extensionality y.
        extensionality f.
        match type of H with
          ?A = ?B =>
          set (H' :=
                 fun x =>
                   match H in _ = y return
                         A x = y x
                   with
                     eq_refl => eq_refl
                   end
              )
        end.
        transitivity (
            match H' x in _ = u return
                  u –≻ _
            with
              eq_refl =>
              match H' y in _ = v return
                    _ –≻ v
              with
                eq_refl =>
                ((Comma_Left_Func_Iso_FC I G ∘ Comma_Left_Func_Iso_FC (I ⁻¹) G) _a f)
              end
            end
          ).
        {
          destruct H; trivial.
        }
        {
          apply Comma_Hom_eq_simplify.
          {
            apply JMeq_eq.
            destruct H; trivial.
          }
          {
            apply JMeq_eq.
            destruct H; trivial.
          }
        }
      }
      {
        extensionality x.
        destruct x as [s t h]; cbn.
        rewrite assoc.
        change ((Trans (iso_morphism I) s) ∘ Trans (I ⁻¹)%morphism s) with
        (Trans ((iso_morphism I) ∘ (I ⁻¹)%morphism) s).
        cbn_rewrite (right_inverse I).
        cbn; auto.
      }
    Qed.
    
  End Comma_Left_Func_Iso_FC_Iso.

  
  Context
    {F F' : (B –≻ C)%functor}
    (I : (F ≃ F')%natiso)
    (G : (D –≻ C)%functor)
  .

  Local Hint Extern 1 => apply Comma_Left_Func_Iso_FC_Iso.
  
  Program Definition Comma_Left_Func_Iso :
    ((Comma F G) ≃≃ (Comma F' G) ::> Cat)%isomorphism
    :=
      {|
        iso_morphism := Comma_Left_Func_Iso_FC I G;
        inverse_morphism := Comma_Left_Func_Iso_FC (Inverse_Isomorphism I) G
      |}
  . 
    
End Comma_Left_Func_Iso.

(** In this section we show that whenever G and G' are two naturally
isomorphic functors, then (Comma F G) is isomorphic to (Comma F G').
This follows from Comma_Left_Func_Iso and Comma_Opposite_Iso proven
above.
 *)
Section Comma_Right_Func_Iso.
  Context
    {B C D : Category}
    (F : (B –≻ C)%functor)
    {G G' : (D –≻ C)%functor}
    (I : (G ≃ G')%natiso)
  .

  Definition Comma_Right_Func_Iso :
    ((Comma F G) ≃≃ (Comma F G') ::> Cat)%isomorphism :=
    Isomorphism_Compose
      (
        Isomorphism_Compose
          (Inverse_Isomorphism (Comma_Opposite_Iso (G ^op) (F ^op)))
          (Opposite_Cat_Iso (Comma_Left_Func_Iso (Opposite_NatIso I) (F^op)))
      )
      (Comma_Opposite_Iso (G' ^op) (F ^op))
  .
    
End Comma_Right_Func_Iso.

(**
Slice, coslice and arrow categories are special cases of comma categories
defined below:
*)

Section Slice_CoSlice.
  Context (C : Category) (c : Obj).
  
  (**
   The Slice of Category C with respect to c:
     Objects : Arrows of C ending in c
     Arrows: for g : a → c and h : b → c, an arrow from g to h is a pair of
       arrows f : a → b s.t. the ollowing commutes:

#
<pre>

           g
         a –––→ c
         |     ↗
         ∣    /    
        f∣   / h
         |  /
         ↓ /
         b 
</pre>
#
   *)

  Definition Slice : Category := Comma (Functor_id _) (Const_Func 1 c).

  (**
   The Slice of Category C with respect to c:
     Objects : Arrows of C ending in c
     Arrows: for g : a → c and h : b → c, 
       an arrow from g to h is a pair of arrows f : a → b s.t. the ollowing commutes:

#
<pre>
            g
         c ←––– a
         ↑     /
         ∣    /
        h∣   / f
         |  /
         | ↙
         b 
</pre>
#
   *)

  Definition CoSlice : Category := Comma (Const_Func 1 c) (Functor_id _).

End Slice_CoSlice.

Section Arrow_Cat.
  Context (C : Category).

  (**
   The Arrow Category of C:
     Objects : Arrows of C
     Arrows: for g : a → b and h : c → d,
       an arrow from g to h is a pair of arrows (f,f') s.t. the ollowing commutes:

#
<pre>

             g
         a ––––→ b
         ∣       ∣
        f∣       ∣f'
         ↓       ↓
         c –——–→ d
             h
</pre>
#
   *)

  Definition Arrow_Cat : Category := Comma (Functor_id C) (Functor_id C).

End Arrow_Cat.
