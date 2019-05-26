Set Warnings "-extraction-opaque-accessed,-extraction".
Set Warnings "-notation-overridden,-parsing".

From Coq Require Import
     Ascii
     List
     NArith
     String
     ZArith.
From mathcomp Require Import
     ssrbool
     ssreflect
     ssrnat.
From QuickChick Require Import Checker.

Set Bullet Behavior "Strict Subproofs".

(* Class wrapper around "decidable" *)
(* begin decidable_class *)
    Class Dec (P : Prop) : Type := { dec : decidable P }.
(* end decidable_class *)

Class DecOpt (P : Prop) := { decOpt : nat -> option bool }.

Axiom checkable_size_limit : nat.
Extract Constant checkable_size_limit => "10000".

Import GenLow.GenLow.
(* Discard tests that run further than the limit *)
(* For proofs, the size parameter will need to be taken into account
   to prove limit results. We just add it to the large, practical constant.
 *)
Global Instance decOpt__checkable {P} `{DecOpt P} : Checkable P :=
  {| checker _ :=
       sized (fun s =>
                match decOpt (checkable_size_limit + s) with
                | Some b => checker b
                | None => checker tt
                end
             )
  |}.

Global Instance dec_decOpt {P} `{Dec P} : DecOpt P :=
  {| decOpt := fun _ => match @dec P _ with
                        | left  _ => Some true
                        | right _ => Some false
                        end |}.

(* Note: maybe this should become thunked? *)
Definition checker_backtrack (l : list (unit -> option bool)) : option bool :=
  let fix aux l b :=
      match l with
      | t :: ts =>
        match t tt with
        | Some true  => Some true
        | Some false => aux ts b
        | None => aux ts true
        end
      | nil => if b then None else Some false
      end
  in aux l false.

(* BCP: If I understand correctly, removing "Global" everywhere would
   change nothing... Or? *)

(* Additional Checkable instance *)
Global Instance testDec {P} `{H : Dec P} : Checkable P.
Proof.
  constructor.
  destruct H.
  destruct dec0.
  - intros; exact (checker true).
  - intros; exact (checker false).
Defined.

Global Instance Dec_neg {P} {H : Dec P} : Dec (~ P).
Proof.
  constructor. unfold decidable.
  destruct H as [D]; destruct D; auto.
Defined.

Global Instance Dec_conj {P Q} {H : Dec P} {I : Dec Q} : Dec (P /\ Q).
Proof.
  constructor. unfold decidable.
  destruct H as [D]; destruct D;
    destruct I as [D]; destruct D; auto;
      right; intro; destruct H; contradiction.
Defined.

Global Instance Dec_disj {P Q} {H : Dec P} {I : Dec Q} : Dec (P \/ Q).
Proof.
  constructor. unfold decidable.
  destruct H as [D]; destruct D;
    destruct I as [D]; destruct D; auto;
      right; intro; destruct H; contradiction.
Defined.

(* BCP: Not clear this is a good idea, but... *)
(* Leo: Should be ok with really low priority *)
Global Instance Dec_impl {P Q} {H : Dec P} {I : Dec Q} : Dec (P -> Q) | 100.
Proof.
  constructor. unfold decidable.
  destruct H as [D]. destruct D; destruct I as [D]; destruct D; auto.
  left. intros. contradiction.
Defined.

Global Instance Dec_In {A} (Eq: forall (x y : A), Dec (x = y))
         (x : A) (l : list A) : Dec (In x l) :=
  {| dec := in_dec (fun x' y' => @dec _ (Eq x' y')) x l |}.

Class Dec_Eq (A : Type) :=
  {
    dec_eq : forall (x y : A), decidable (x = y)
  }.

Theorem dec_if_dec_eq {A} (x y: A): Dec (x = y) -> {x = y} + {x <> y}.
Proof.
  intros. inversion H as [D].
  unfold decidable in D. assumption.
Defined.

Hint Resolve dec_if_dec_eq: eq_dec.

Ltac dec_eq :=
  repeat match goal with
         | [ |- _ ] => solve [auto with eq_dec]
         | [ |- Dec _ ] => constructor
         | [ |- context[decidable _] ] => unfold decidable

         | [ H: context[decidable _] |- _ ] => unfold decidable in H

         | [ |- {?x = ?y} + {?x <> ?y} ] =>
           multimatch goal with
             | [ H: forall x y, Dec _ |- _ ] => apply H
             | [ H: Dec_Eq _ |- _ ] => apply H
             | [ |- _ ] => decide equality
           end
         end.

Global Instance Eq__Dec {A} `{H : Dec_Eq A} (x y : A) : Dec (x = y).
Proof.
constructor.
dec_eq.
Defined.

(* Lifting common decidable instances *)
Global Instance Dec_eq_unit (x y : unit) : Dec (x = y).
Proof. dec_eq. Defined.

Global Instance Dec_eq_bool (x y : bool) : Dec (x = y).
Proof. dec_eq. Defined.

Global Instance Dec_eq_nat (m n : nat) : Dec (m = n).
Proof. dec_eq. Defined.

Global Instance Dec_eq_Z (m n : Z) : Dec (m = n).
Proof. dec_eq. Defined.

Global Instance Dec_eq_N (m n : N) : Dec (m = n).
Proof. dec_eq. Defined.

Global Instance Dec_eq_opt (A : Type) (m n : option A)
  `{_ : forall (x y : A), Dec (x = y)} : Dec (m = n).
Proof. dec_eq. Defined.

Global Instance Dec_eq_prod (A B : Type) (m n : A * B)
  `{_ : forall (x y : A), Dec (x = y)}
  `{_ : forall (x y : B), Dec (x = y)}
  : Dec (m = n).
Proof. dec_eq. Defined.

Global Instance Dec_eq_list (A : Type) (m n : list A)
  `{_ : forall (x y : A), Dec (x = y)} : Dec (m = n).
Proof. dec_eq. Defined.

Hint Resolve ascii_dec: eq_dec.
Hint Resolve string_dec: eq_dec.

Global Instance Dec_ascii (m n : Ascii.ascii) : Dec (m = n).
Proof. dec_eq. Defined.

Global Instance Dec_string (m n : string) : Dec (m = n).
Proof. dec_eq. Defined.

(* Everything that uses the Decidable Class *)
Require Import DecidableClass.

Global Instance dec_class_dec P (H : Decidable P): Dec P.
Proof.
  constructor; destruct H; destruct Decidable_witness.
  - left; auto.
    apply Decidable_spec; auto.
  - right => H; eauto.
    apply Decidable_spec in H.
    inversion H.
Defined.

(*
Example foo (m n : nat) :=
  match @dec (m = n) _ with
    | left  _ => 0
    | right _ => 1
  end.

(* Eval compute in foo 0 1. *)
Example bar (m n : nat) :=
  if (m=n)? then 0 else 1.

(* Eval compute in bar 0 1. *)
*)


(* Not sure about the level or binding, but good idea *)
Notation "P '?'" := (match (@dec P _) with
                       | left _ => true
                       | right _ => false
                     end) (at level 100).

Hint Resolve Dec_eq_bool : eq_dec.
Hint Resolve Dec_eq_nat : eq_dec.
Hint Resolve Dec_eq_Z : eq_dec.
Hint Resolve Dec_eq_N : eq_dec.
Hint Resolve Dec_eq_opt : eq_dec.
Hint Resolve Dec_eq_prod : eq_dec.
Hint Resolve Dec_eq_list : eq_dec.
Hint Resolve Dec_string : eq_dec.
