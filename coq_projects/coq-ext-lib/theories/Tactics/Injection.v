Set Implicit Arguments.
Set Strict Implicit.

Class Injective (P : Prop) : Type :=
{ result : Prop
; injection : P -> result
}.

Ltac destruct_ands H :=
  match type of H with
    | _ /\ _ =>
      let H1 := fresh in
      let H2 := fresh in
      destruct H as [ H1 H2 ] ;
        destruct_ands H1 ; destruct_ands H2
    | exists x , _ =>
      let H1 := fresh in
      destruct H as [ ? H1 ] ;
        destruct_ands H1
    | _ => idtac
  end.

Ltac inv_all :=
  repeat match goal with
           | [ H : ?X |- _ ] =>
             let z := constr:(_ : Injective X) in
             eapply (@injection X z) in H; do 2 red in H ; destruct_ands H
         end.

(* Example
Global Instance Injective_Some (T : Type) (a b : T) : Injective (Some a = Some b) :=
{ result := a = b }.
abstract (inversion 1; auto).
Defined.


Goal forall x y : nat, Some x = Some y -> x = y.
Proof.
  intros; inv_all; assumption.
Qed.
*)