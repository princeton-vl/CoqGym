Require Import Coq.Bool.Bool.

Set Implicit Arguments.
Set Strict Implicit.

Hint Rewrite negb_orb negb_andb negb_involutive if_negb : bool_rw.

Lemma negb_true : forall a, negb a = true -> a = false.
Proof.
  destruct a; auto.
Qed.

Lemma negb_false : forall a, negb a = false -> a = true.
Proof.
  destruct a; auto.
Qed.

Ltac do_bool' runner :=
  ( autorewrite with bool_rw in * );
  repeat match goal with
           | [ H : negb _ = true |- _ ] => apply negb_true in H
           | [ H : negb _ = false |- _ ] => apply negb_false in H
           | [ H : andb _ _ = true |- _ ] =>
             apply andb_true_iff in H; destruct H
           | [ H : orb _ _ = false |- _ ] =>
             apply orb_false_iff in H; destruct H
           | [ H : true = andb _ _ |- _ ] =>
             symmetry in H; apply andb_true_iff in H; destruct H
           | [ H : false = orb _ _ |- _ ] =>
             symmetry in H; apply orb_false_iff in H; destruct H
           | [ H : andb _ _ = false |- _ ] =>
             apply andb_false_iff in H; runner H
           | [ H : orb _ _ = true |- _ ] =>
             apply orb_true_iff in H; runner H
           | [ H : false = andb _ _ |- _ ] =>
             symmetry in H; apply andb_false_iff in H; runner H
           | [ H : true = orb _ _ |- _ ] =>
             symmetry in H; apply orb_true_iff in H; runner H
         end.

Ltac do_bool_case :=
  let t H := (destruct H) in do_bool' t.

Ltac do_bool :=
  let t _ := idtac in do_bool' t.

(** Test **)
(*
Goal forall a b c d e f : bool,
  negb (a || b) = true ->
  negb (a && b) = false ->
  a && b && c = true -> b && c && d = false -> d || e || f = true -> b || c || d = false ->
  true = a && b && c -> false = b && c && d -> true = d || e || f -> false = b || c || d ->
  if a && b then True else False.
Proof.
  intros.
  do_bool.
Abort.
*)