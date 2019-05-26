From Categories Require Import Category.Main.
From Categories Require Import Ext_Cons.Prod_Cat.Prod_Cat Ext_Cons.Prod_Cat.Operations.
From Categories Require Import Functor.Main.
From Categories Require Import Functor.Representable.Hom_Func Functor.Representable.Hom_Func_Prop.
From Categories Require Import NatTrans.NatTrans NatTrans.NatIso.
From Categories Require Import Adjunction.Adjunction.

Local Open Scope functor_scope.

Section Hom_Adj_Duality.
  Context {C D : Category} {F : C –≻ D} {G : D –≻ C} (adj : F ⊣_hom G).

  (** Duality for hom adjunctions. *)
  Definition Hom_Adjunct_Duality : G^op ⊣_hom F^op :=
    (Prod_Func_Hom_Func (adj⁻¹))
  .

End Hom_Adj_Duality.

Section Adj_Duality.
  Context {C D : Category} {F : C –≻ D} {G : D –≻ C} (adj : F ⊣ G).

  (** Duality for adjunctions. It follows from Hom_Adjunct_Duality. *)
  Definition Adjunct_Duality : G^op ⊣ F^op :=
    (Hom_Adj_to_Adj (Hom_Adjunct_Duality (Adj_to_Hom_Adj adj)))
  .

End Adj_Duality.
