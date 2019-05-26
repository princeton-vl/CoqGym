(** The Cont Monad Class
 **)
Require Import ExtLib.Structures.Monad.

Class Cont (m : Type -> Type) : Type :=
{ callCC : forall a b, ((a -> m b) -> m a) -> m a }.

Arguments callCC {m Cm} {_ _} _ : rename.