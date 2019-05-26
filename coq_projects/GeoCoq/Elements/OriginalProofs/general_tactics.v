(** Some useful tactics *)



Ltac hyp_of_type t :=
 match goal with
| H1:t |- _ => H1
  end.


Ltac mysubst :=
 repeat
( match goal with
 | H1:?a=?b |- _ => (subst a;try revert H1)
 end);intros.
   
Ltac spliter := repeat
match goal with
   | H:(?X1 /\ ?X2) |- _ => induction H
end.

Ltac splits :=
 repeat
 match goal with
  | |- ?x /\ ?y => split
end.

Ltac remove_exists :=
repeat
 match goal with
  | |- exists x, _ => eexists
 end.

Ltac destruct_all := 
repeat
match goal with
   | H:_ |- _ => progress (decompose [ex and] H);clear H
end.

Ltac one_of_disjunct :=
 solve [repeat (assumption || (left;assumption) || right)].


Ltac rename_H H := let T := fresh in try rename H into T.
