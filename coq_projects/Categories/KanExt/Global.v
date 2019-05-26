From Categories Require Import Essentials.Notations.
From Categories Require Import Essentials.Types.
From Categories Require Import Essentials.Facts_Tactics.
From Categories Require Import Category.Main.
From Categories Require Import Functor.Functor Functor.Functor_Ops.
From Categories Require Import NatTrans.NatTrans NatTrans.Operations NatTrans.Func_Cat.
From Categories Require Import Adjunction.Adjunction.
From Categories Require Import Functor.Functor_Extender.

Local Open Scope functor_scope.

(**
Given functor p : C -> C', we define the global kan extension along p operation.

To define it, notice Left_Functor_Extender p D. It functor which maps
(as objects) a functor F : C' -> D to F ∘ p : C -> D. The global
left/right kan extension operation along p is simply the left/right
adjoint to this functor. 

*)
Section KanExtension.
  Context {C C' : Category} (p : (C –≻ C')%functor).

  Section Global.
    Context (D : Category).

    Record Left_KanExt : Type :=
      {
        left_kan_ext : (Func_Cat C D) –≻ (Func_Cat C' D);
        left_kan_ext_adj : left_kan_ext ⊣ (Left_Functor_Extender p D)
      }.

    Coercion left_kan_ext : Left_KanExt >-> Functor.

    Record Right_KanExt : Type :=
      {
        right_kan_ext : (Func_Cat C D) –≻ (Func_Cat C' D);
        right_kan_ext_adj : (Left_Functor_Extender p D) ⊣ right_kan_ext
      }.

    Coercion right_kan_ext : Right_KanExt >-> Functor.

  End Global.

End KanExtension.

Arguments left_kan_ext {_ _ _ _} _.
Arguments left_kan_ext_adj {_ _ _ _} _.

Arguments right_kan_ext {_ _ _ _} _.
Arguments right_kan_ext_adj {_ _ _ _} _.
