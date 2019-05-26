Require Import ExtLib.Structures.Monad.

Set Implicit Arguments.
Set Maximal Implicit Insertion.

Section Ident.
  Inductive ident A := mkIdent { unIdent : A }.

  Global Instance Monad_ident : Monad ident :=
  { ret  := fun _ v => mkIdent v
  ; bind := fun _ _ c f => f (unIdent c)
  }.

End Ident.