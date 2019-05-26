From Categories Require Import Essentials.Notations.
From Categories Require Import Essentials.Types.
From Categories Require Import Essentials.Facts_Tactics.
From Categories Require Import Category.Main.
From Categories Require Import Functor.Functor Functor.Representable.Hom_Func.
From Categories Require Import Coq_Cats.Type_Cat.Type_Cat.
From Categories Require Import Ext_Cons.Prod_Cat.Prod_Cat Ext_Cons.Prod_Cat.Operations.
From Categories Require Import NatTrans.NatIso.

(** A functor F : C → Type_Cat is representable if F is naturaly isomorphic to
Hom_C(x, -) for some x : C. In this case, we say F is represented by x. *)
Section Representable.
  Context {C : Category} (F : (C –≻ Type_Cat)%functor).

  Record Representable : Type :=
    {
      representer : C;
      representation_Iso :
        (F ≃ @Fix_Bi_Func_1 (C^op) _ _ representer (Hom_Func C))%natiso
    }.

End Representable.

Arguments representer {_ _} _.
Arguments representation_Iso {_ _} _.

Definition CoRepresentable {C : Category} (F : (C^op –≻ Type_Cat)%functor) :=
  @Representable (C^op) F.
