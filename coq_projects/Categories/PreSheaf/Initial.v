From Categories Require Import Essentials.Notations.
From Categories Require Import Essentials.Types.
From Categories Require Import Essentials.Facts_Tactics.
From Categories Require Import Category.Main.
From Categories Require Import Functor.Main.
From Categories Require Import Basic_Cons.Terminal.
From Categories Require Import Coq_Cats.Type_Cat.Type_Cat.
From Categories Require Import NatTrans.NatTrans NatTrans.Func_Cat.
From Categories Require Import Basic_Cons.Terminal.
From Categories Require Import PreSheaf.PreSheaf.

Section Initial.
  Context (C : Category).
  
  (** The initial element of the category of presheaves. *)
  Program Definition PSh_Init_Func : Functor (C^op) Type_Cat :=
    {|
      FO := fun _ => (Empty : Type)
    |}.

  Local Hint Resolve NatTrans_eq_simplify.
  Local Hint Extern 1 => progress cbn in *.

  (** The functor that maps to the empty type in coq is the terminal object of
      presheaves. *)
  Program Instance PSh_Initial : (𝟘_ (PShCat C))%object :=
    {|
      terminal := PSh_Init_Func;
      t_morph := fun u => {|Trans := fun x y => _ |}
    |}.
    
End Initial.
