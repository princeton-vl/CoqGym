From Categories Require Import Category.Main.
From Categories Require Import Coq_Cats.Coq_Cat.
  
(*
**********************************************************
***************                          *****************
***************      Set Category        *****************
***************                          *****************
**********************************************************
*)


(** The category of types in Set universe (Coq's "Set")*)

Program Definition Set_Cat : Category := Coq_Cat Set.

