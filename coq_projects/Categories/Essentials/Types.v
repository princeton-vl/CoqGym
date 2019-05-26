Global Set Primitive Projections.

Global Set Universe Polymorphism.

Global Unset Universe Minimization ToSet.

(** The Empty Type. *)
Inductive Empty : Type :=.

Hint Extern 1 =>
let tac := (repeat intros ?); match goal with [H : Empty |- _] => contradict H end in
match goal with
  | [|- context[Empty]] => tac
  | [H : context[Empty] |- _] => tac
end
.

(** The product type, defined as a record to enjoy eta rule for records. *)
Record prod (A B : Type) := {fst : A; snd : B}.

Arguments fst {_ _ } _.
Arguments snd {_ _ } _.
Arguments Build_prod {_ _ } _ _.

Notation "( X , Y )" := (Build_prod X Y).
Notation "X * Y" := (prod X Y) : type_scope.
