(* Julien Narboux *)
(* Formalization of *)
(* Tarski's axiomatic *)

(* Some general tactics *)

Ltac DecompEx H P := elim H;intro P;intro;clear H.

Ltac DecompExAnd H P :=
  elim H;intro P;let id:=fresh in
(intro id;decompose [and] id;clear id;clear H).

Ltac exist_hyp t := match goal with
  | H1:t |- _ => idtac
 end.

Ltac hyp_of_type t := match goal with
  | H1:t |- _ => H1
end.

Ltac clean_duplicated_hyps :=
  repeat match goal with
      | H:?X1 |- _ => clear H; exist_hyp X1
end.

Ltac suppose H := cut H;[intro|idtac].

Ltac not_exist_hyp t := match goal with
  | H1:t |- _ => fail 2
 end || idtac.

Ltac DecompAndAll := 
 repeat  
 match goal with
   | H:(?X1 /\ ?X2) |- _ => decompose [and] H;clear H
end.

Ltac assert_if_not_exist H :=
  not_exist_hyp H;assert H.

(* classical_left  transforms |- A \/ B into ~B |- A *)
(* classical_right transforms |- A \/ B into ~A |- B *)
(*
Ltac classical_right :=  match goal with
 | _:_ |-?X1 \/ _ => (elim (classic X1);intro;[left;trivial|right])
end.

Ltac classical_left := match goal with
| _:_ |- _ \/?X1 => (elim (classic X1);intro;[right;trivial|left])
end.
*)