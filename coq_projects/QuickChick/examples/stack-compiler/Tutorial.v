(** * Tutorial for QuickChick at POPL Tutorial Fest 2019 *)

(** QuickChick is a clone of Haskell's QuickCheck, on steroids.  *) 

From QuickChick Require Import QuickChick.
Open Scope qc_scope.
Set Warnings "-extraction-opaque-accessed,-extraction".
Set Warnings "-notation-overridden,-parsing".

Require Import List ZArith. Import ListNotations.

From mathcomp Require Import seq ssreflect ssrbool ssrnat eqtype.

(** ** Introduction *)
     
(** It is not uncommon during a verification effort to spend many
    hours attempting to prove a slightly false theorem, only to result
    in frustration when the mistake is realized and one needs to start
    over. Other theorem provers have testing tools to quickly raise
    one's confidence before embarking on the body of the proof;
    Isabelle has its own QuickCheck clone, as well as Nitpick,
    Sledgehammer and a variety of other tools; ACL2 has gone a step
    further using random testing to facilitate its
    automation. QuickChick is meant to fill this void for Coq.

    Consider the following short function [remove] that takes a
    natural number [x] and a list of nats [l] and proceeds to remove
    [x] from the list. While one might be tempted to pose the question
    "Is there a bug in this definition?", such a question has little
    meaning without an explicit specification. Here, [removeP]
    requires that after removing [x] from [l], the resulting list does
    not contain any occurences of [x]. *)

Fixpoint remove (x : nat) (l : list nat) : list nat :=
  match l with
    | []   => []
    | h::t => if beq_nat h x then t else h :: remove x t
  end.

Definition removeP (x : nat) (l : list nat) := 
  (~~ (existsb (fun y => beq_nat y x) (remove x l))).

(** For this simple example, it is not hard to "spot" the bug by
    inspection. We will use QuickChick to find out what is wrong.

    QuickChick provides a toplevel command [QuickChick] that receives
    as input an executable property and attempts to falsify it. *)

(* QuickChick removeP. *)

(** Internally, the code is extracted to OCaml, compiled and ran to
obtain the output:
<<
    0

    [ 0, 0 ]

    Failed! After 17 tests and 12 shrinks
>>
    The output signifies that if we use an input where [x] is [0] and
    [l] is the two element list containing two zeros, then our
    property fails. Indeed, we can now identify that the [then] branch
    of [remove] fails to make a recursive call, which means that only
    one occurence of each element will be deleted. The last line of
    the output states that it took 17 tests to identify some fault
    inducing input and 12 shrinks to reduce it to a minimal
    counterexample.

    Before we begin to explain exactly how QuickChick magically comes
    up with this result, it is important to point out the first (and
    arguably most important) limitation of this tool: it requires an
    *executable* specification. QuickChick needs to be able to "run" a
    property and decide whether it is true or not; a definition like
    [remove_spec] can't be QuickChecked! *)
