Require Import ExtLib.Tactics.Consider.

Set Implicit Arguments.
Set Strict Implicit.

(** This tactic will perform case splits on terms that
 ** are matched on. It only does this on terms where only
 ** one of the cases is non-trivial (i.e. by [intuition congruence]).
 **
 **)
Ltac forward' dst sol :=
  let check X :=
    match X with
      | match _ with _ => _ end => fail 1
      | if _ then _ else _ => fail 1
      | _ => idtac
    end
  in
  let go X :=
    first [ (dst X; try solve [ sol ]); [ intros ]
          | dst X; solve [ sol ] ]
  in
  repeat match goal with
           | [ H : context [ match ?X with _ => _ end ] |- _ ] =>
             go X
           | [ H : context [ if ?X then _ else _ ] |- _ ] =>
             go X
           | [ |- context [ match ?X with _ => _ end ] ] =>
             go X
           | [ |- context [ if ?X then _ else _ ] ] =>
             go X
         end.

Ltac forward :=
  forward'
    ltac:(fun x => consider x; intros)
    ltac:(intuition congruence).

Ltac forward_unsafe' dst sol :=
  let check X :=
    match X with
      | match _ with _ => _ end => fail 1
      | if _ then _ else _ => fail 1
      | _ => idtac
    end
  in
  let go X :=
      dst X; try solve [ sol ]
  in
  repeat match goal with
           | [ H : context [ match ?X with _ => _ end ] |- _ ] =>
             go X
           | [ H : context [ if ?X then _ else _ ] |- _ ] =>
             go X
           | [ |- context [ match ?X with _ => _ end ] ] =>
             go X
           | [ |- context [ if ?X then _ else _ ] ] =>
             go X
         end.

Ltac forward_unsafe :=
  forward_unsafe'
    ltac:(fun x => consider x; intros)
    ltac:(intuition congruence).

Ltac change_rewrite H :=
  match type of H with
    | ?X = _ =>
      match goal with
        | |- context [ ?Y ] =>
          change Y with X ; rewrite H
      end
  end.

Ltac change_rewrite_in H H' :=
  match type of H with
    | ?X = _ =>
      match type of H' with
        | context [ ?Y ] =>
          change Y with X in H' ; rewrite H in H'
      end
  end.

Tactic Notation "change_rewrite" hyp(H) := (change_rewrite H).
Tactic Notation "change_rewrite" hyp(H) "in" hyp(H') := (change_rewrite_in H H').

Ltac rewrite_all_goal :=
  repeat match goal with
           | [ H : _ |- _ ] =>
             progress (erewrite H by eauto with typeclass_instances)
         end.

Ltac rewrite_all_in H' :=
  repeat match goal with
           | [ H : _ |- _ ] =>
             progress (erewrite H in H' by eauto with typeclass_instances)
         end.

Ltac rewrite_all_star :=
  repeat match goal with
           | [ H : _ |- _ ] =>
             progress (erewrite H in * by eauto with typeclass_instances)
         end.

(*
Ltac rewrite_all := rewrite_all_goal.
*)