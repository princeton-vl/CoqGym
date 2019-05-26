From Categories Require Import Category.Main.
From Categories Require Import Coq_Cats.Coq_Cat.

(** The category of Types (Coq's "Type")*)

Program Definition Type_Cat : Category := Coq_Cat Type.
