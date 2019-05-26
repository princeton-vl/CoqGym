From Categories Require Import Essentials.Notations.
From Categories Require Import Essentials.Types.
From Categories Require Import Essentials.Facts_Tactics.
From Categories Require Import Category.Main.
From Categories Require Import Functor.Functor Functor.Functor_Ops
        Functor.Representable.Hom_Func
        Functor.Representable.Representable.
From Categories Require Import Ext_Cons.Prod_Cat.Prod_Cat Ext_Cons.Prod_Cat.Operations.
From Categories Require Import Coq_Cats.Type_Cat.Type_Cat.
From Categories Require Import NatTrans.NatTrans NatTrans.Operations NatTrans.Func_Cat.
From Categories Require Import KanExt.Local.

Local Open Scope functor_scope.

(** A local kan extension is pointwise if it is preserved by representable
    functors. In other words, in the following diagram,

#
<pre>
           F            G
     C ———————–> D ——————–> Set
     |          ↗          ↗
     |        /          /
   p |      / R       /
     |    /        /   G ∘ R
     ↓  /       /
     C' ———–———
</pre>
#
where R is the left/right local kan extension of F along p, and G is a
representable functor and we have (G ∘ R) is the left/right kan extension
of (G ∘ F) along p.
*)

(** Pointwise-ness for local left kan extensions. *)
Section Pointwise_LRKE.
  Context {C C' : Category}
          {p : C –≻ C'}
          {D: Category}
          {F : C –≻ D}
          (lrke : Local_Right_KanExt p F)
  .

  Definition Pointwise_LRKE :=
    ∀ (G : D –≻ Type_Cat) (GR : Representable G),
    is_Local_Right_KanExt p (G ∘ F) (G ∘ lrke)
  .
  
End Pointwise_LRKE.

(** Pointwiseness for local right kan extensions. *)
Section Pointwise_LLKE.
  Context {C C' : Category}
          {p : C –≻ C'}
          {D: Category}
          {F : C –≻ D}
          (llke : Local_Left_KanExt p F)
  .
  
  Definition Pointwise_LLKE :=
    ∀ (G : D^op –≻ Type_Cat) (GR : CoRepresentable G),
    is_Local_Right_KanExt p (G^op ∘ F) ((G ∘ llke)^op)
  .
  
End Pointwise_LLKE.
