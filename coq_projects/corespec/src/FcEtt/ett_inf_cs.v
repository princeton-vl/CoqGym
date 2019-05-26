(* Completing the infrastructure of ett

   Current additions:
   - polymorphic functions (via canonical structures)
*)

Require Import FcEtt.ett_inf.
Require Import FcEtt.imports.

(**** Operators on syntactic sorts ****)
(* TODO: better name? *)
Module Operators.

  Module Close.

    Record class1 (ssort : Type) (vartype : Type) :=  Class1 {close_ : vartype -> ssort -> ssort; close_rec_ : nat -> vartype -> ssort -> ssort}.

    Record class (ssort : Type) := Class {class_tm : class1 ssort tmvar; class_co : class1 ssort covar}.

    Arguments Class {ssort} class_tm class_co.
    Arguments Class1 {ssort vartype} close_ close_rec_.

  End Close.


  Module Open.

    (* TODO *)

  End Open.


  Module Erase.

    Record class (ssort : Type) := Class {erase_ssort : ssort -> ssort}.

    Arguments Class {ssort} erase_ssort.

  End Erase.


  Module FV.

    Record class (ssort : Type) := Class {fv_tm : ssort -> atoms; fv_co : ssort -> atoms}.

    Arguments Class {ssort} fv_tm fv_co.

  End FV.

  (* TODO; open, fv *)
  Structure type := Pack {stxsort : Type; class_close : Close.class stxsort; class_Erase : Erase.class stxsort; class_Fv : FV.class stxsort}.

  Definition close_tm' (e : type) : tmvar -> stxsort e -> stxsort e :=
    let 'Pack _ (Close.Class (Close.Class1 c _) _) _ _ := e return tmvar -> stxsort e -> stxsort e in c.

  Definition close_tm_rec' (e : type) : nat -> tmvar -> stxsort e -> stxsort e :=
    let 'Pack _ (Close.Class (Close.Class1 _ c) _) _ _ := e return nat -> tmvar -> stxsort e -> stxsort e in c.

  Definition close_co' (e : type) : covar -> stxsort e -> stxsort e :=
    let 'Pack _ (Close.Class _ (Close.Class1 c _)) _ _ := e return covar -> stxsort e -> stxsort e in c.

  Definition close_co_rec' (e : type) : nat -> covar -> stxsort e -> stxsort e :=
    let 'Pack _ (Close.Class _ (Close.Class1 _ c)) _ _ := e return nat -> covar -> stxsort e -> stxsort e in c.

  Definition erase' (e : type) : stxsort e -> stxsort e :=
    let 'Pack _ _ (Erase.Class c) _ := e in c.

  Definition fv_tm' (e : type) : stxsort e -> atoms :=
    let 'Pack _ _ _ (FV.Class c _) := e in c.

  Definition fv_co' (e : type) : stxsort e -> atoms :=
    let 'Pack _ _ _ (FV.Class _ c) := e in c.

  Arguments close_tm' {e} s v : simpl nomatch.
  Arguments close_tm_rec' {e} k s v : simpl nomatch.
  Arguments close_co' {e} s v : simpl nomatch.
  Arguments close_co_rec' {e} k s v : simpl nomatch.
  Arguments erase' {e} s : simpl nomatch.
  Arguments fv_tm' {e} s : simpl nomatch.
  Arguments fv_co' {e} s : simpl nomatch.


  Module Theory.

    Notation close_tm := close_tm'.
    Notation close_tm_rec := close_tm_rec'.
    Notation close_co := close_co'.
    Notation close_co_rec := close_co_rec'.

    Notation erase := erase'.

    Notation fv_tm := fv_tm'.
    Notation fv_co := fv_co'.

  End Theory.

End Operators.

Export Operators.Theory.


Definition tm_Closecl         : Operators.Close.class tm         := Operators.Close.Class (Operators.Close.Class1 close_tm_wrt_tm close_tm_wrt_tm_rec)                 (Operators.Close.Class1 close_tm_wrt_co close_tm_wrt_co_rec).
Definition co_Closecl         : Operators.Close.class co         := Operators.Close.Class (Operators.Close.Class1 close_co_wrt_tm close_co_wrt_tm_rec)                 (Operators.Close.Class1 close_co_wrt_co close_co_wrt_co_rec).
Definition brs_Closecl        : Operators.Close.class brs        := Operators.Close.Class (Operators.Close.Class1 close_brs_wrt_tm close_brs_wrt_tm_rec)               (Operators.Close.Class1 close_brs_wrt_co close_brs_wrt_co_rec).
Definition constraint_Closecl : Operators.Close.class constraint := Operators.Close.Class (Operators.Close.Class1 close_constraint_wrt_tm close_constraint_wrt_tm_rec) (Operators.Close.Class1 close_constraint_wrt_co close_constraint_wrt_co_rec).


(* TODO: this function is not yet defined with the other erase_*, as it's pretty much useless, but do we want to define it in the ott file? *)
Definition erase_co (_ : co) := g_Triv.

Definition tm_Erasecl         : Operators.Erase.class tm         := Operators.Erase.Class erase_tm.
Definition co_Erasecl         : Operators.Erase.class co         := Operators.Erase.Class erase_co.
Definition brs_Erasecl        : Operators.Erase.class brs        := Operators.Erase.Class erase_brs.
Definition constraint_Erasecl : Operators.Erase.class constraint := Operators.Erase.Class erase_constraint.

Definition tm_FVcl         : Operators.FV.class tm         := Operators.FV.Class fv_tm_tm_tm         fv_co_co_tm.
Definition co_FVcl         : Operators.FV.class co         := Operators.FV.Class fv_tm_tm_co         fv_co_co_co.
Definition brs_FVcl        : Operators.FV.class brs        := Operators.FV.Class fv_tm_tm_brs        fv_co_co_brs.
Definition constraint_FVcl : Operators.FV.class constraint := Operators.FV.Class fv_tm_tm_constraint fv_co_co_constraint.

Canonical Structure tm_OpsTy         : Operators.type := Operators.Pack tm_Closecl         tm_Erasecl         tm_FVcl.
Canonical Structure co_OpsTy         : Operators.type := Operators.Pack co_Closecl         co_Erasecl         co_FVcl.
Canonical Structure brs_OpsTy        : Operators.type := Operators.Pack brs_Closecl        brs_Erasecl        brs_FVcl.
Canonical Structure constraint_OpsTy : Operators.type := Operators.Pack constraint_Closecl constraint_Erasecl constraint_FVcl.


Module Test.


  (*
  Check close_tm x a_Star.
  Check close_tm x (g_Refl a_Star).
  Check close_tm x (Eq a_Star a_Star).
  Check close_tm x br_None.

  Check erase a_Star.
  Check erase (g_Refl a_Star).
  Check erase (Eq a_Star a_Star).
  Check erase br_None.
   *)

End Test.


(* TODO: could be nicer with some more canonical structures *)
Module Rew.
  Definition r_erase_tm         : forall x, erase_tm x = erase x         := fun _ => eq_refl.
  Definition r_erase_co         : forall x, erase_co x = erase x         := fun _ => eq_refl.
  Definition r_erase_brs        : forall x, erase_brs x = erase x        := fun _ => eq_refl.
  Definition r_erase_constraint : forall x, erase_constraint x = erase x := fun _ => eq_refl.

  Definition r_close_tm_tm         : forall x t, close_tm_wrt_tm x t = close_tm x t         := fun _ _ => eq_refl.
  Definition r_close_tm_co         : forall x t, close_co_wrt_tm x t = close_tm x t         := fun _ _ => eq_refl.
  Definition r_close_tm_brs        : forall x t, close_brs_wrt_tm x t = close_tm x t        := fun _ _ => eq_refl.
  Definition r_close_tm_constraint : forall x t, close_constraint_wrt_tm x t = close_tm x t := fun _ _ => eq_refl.

  Definition r_close_co_tm         : forall x t, close_tm_wrt_co x t = close_co x t         := fun _ _ => eq_refl.
  Definition r_close_co_co         : forall x t, close_co_wrt_co x t = close_co x t         := fun _ _ => eq_refl.
  Definition r_close_co_brs        : forall x t, close_brs_wrt_co x t = close_co x t        := fun _ _ => eq_refl.
  Definition r_close_co_constraint : forall x t, close_constraint_wrt_co x t = close_co x t := fun _ _ => eq_refl.


  (* Proper/canonical name for this module? *)
  Module Exprt.
    Hint Rewrite -> r_erase_tm r_erase_co r_erase_brs r_erase_constraint : rewdb_cs.

    (* Ugly but autorewrite fails weirdly with the facts above *)
    Ltac autorewcs :=
      rewrite ? r_erase_tm;
      rewrite ? r_erase_co;
      rewrite ? r_erase_brs;
      rewrite ? r_erase_constraint;

      rewrite ? r_close_tm_tm;
      rewrite ? r_close_tm_co;
      rewrite ? r_close_tm_brs;
      rewrite ? r_close_tm_constraint;

      rewrite ? r_close_co_tm;
      rewrite ? r_close_co_co;
      rewrite ? r_close_co_brs;
      rewrite ? r_close_co_constraint.

    (* Ugly but autorewrite fails weirdly with the facts above *)
    Ltac autorewcshyp H :=
      rewrite ? r_erase_tm in H;
      rewrite ? r_erase_co in H;
      rewrite ? r_erase_brs in H;
      rewrite ? r_erase_constraint in H;

      rewrite ? r_close_tm_tm in H;
      rewrite ? r_close_tm_co in H;
      rewrite ? r_close_tm_brs in H;
      rewrite ? r_close_tm_constraint in H;

      rewrite ? r_close_co_tm in H;
      rewrite ? r_close_co_co in H;
      rewrite ? r_close_co_brs in H;
      rewrite ? r_close_co_constraint in H.
  End Exprt.
End Rew.

Export Rew.Exprt.
