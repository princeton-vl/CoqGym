Require Export List.
Set Implicit Arguments.

Module Type base_mod.

Delimit Scope My_scope with M. 
Open Scope My_scope. 

Parameter PropVars : Set.
Axiom Varseq_dec : forall x y:PropVars, {x = y} + {x <> y}.

(** We define a construction on lists which we'll use often later.

[map_fold_right f g a l] equals fold_right [g a (map f l)], i.e.

[map_fold_right f g a [x0; ... ; xn]] equals [g (f x0) (g (f x1) (... g (f(xn) a)...)] 
*)
Fixpoint map_fold_right (A B:Type) (f : B -> A) (g : A -> A -> A) a l := match l with
 | nil => a
 | b::l2 => g (f b) (map_fold_right f g a l2)
end.

End base_mod.
