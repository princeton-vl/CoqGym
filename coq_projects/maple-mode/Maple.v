(* Maple.v *)

Require Import Field_tac.

Declare ML Module "maple".
(* Defines tactics: tac_iter and reductions raw_simplify, raw_factor,
   raw_expand and raw_normal (transformations operating on syntactic
   field expressions). *)

Ltac prove_rw ope x :=
  prove_with_field ope x;
  [ let H := fresh "Heq_maple" in
    intro H; simpl in H;
    (** Small hack: rewrite sometimes does not find the term after simpl *)
    match type of H with ?P ?a ?b => change (P x b) in H end;
    rewrite H; clear H
  |..].

Ltac maple_simplify x := (eval raw_simplify in x).
Tactic Notation "simplify" ne_constr_list(l) :=
  tac_iter (prove_rw maple_simplify) l.

Ltac maple_factor x := (eval raw_factor in x).
Tactic Notation "factor" ne_constr_list(l) :=
  tac_iter (prove_rw maple_factor) l.

Ltac maple_expand x := (eval raw_expand in x).
Tactic Notation "expand" ne_constr_list(l) :=
  tac_iter (prove_rw maple_expand) l.

Ltac maple_normal x := (eval raw_normal in x).
Tactic Notation "normal" ne_constr_list(l) :=
  tac_iter (prove_rw maple_normal) l.

(* maple.ml uses these 4 tactics to build the reduction functions *)
Ltac red_simplify := reduce_field_ope maple_simplify.
Ltac red_factor   := reduce_field_ope maple_factor.
Ltac red_expand   := reduce_field_ope maple_expand.
Ltac red_normal   := reduce_field_ope maple_normal.

(*
Add Reduction simplify := reduce_ope maple_simplify.
Add Reduction factor   := reduce_ope maple_factor.
Add Reduction expand   := reduce_ope maple_expand.
Add Reduction normal   := reduce_ope maple_normal.
*)
