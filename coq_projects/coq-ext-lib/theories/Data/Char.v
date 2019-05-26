Require Import Coq.Strings.Ascii.
Require Import ExtLib.Data.Bool.
Require Import ExtLib.Tactics.Consider.
Require Import ExtLib.Core.RelDec.

Set Implicit Arguments.
Set Strict Implicit.

Definition ascii_dec (l r : Ascii.ascii) : bool :=
  match l , r with
    | Ascii.Ascii l1 l2 l3 l4 l5 l6 l7 l8 ,
      Ascii.Ascii r1 r2 r3 r4 r5 r6 r7 r8 =>
      if Bool.eqb l1 r1 then
      if Bool.eqb l2 r2 then
      if Bool.eqb l3 r3 then
      if Bool.eqb l4 r4 then
      if Bool.eqb l5 r5 then
      if Bool.eqb l6 r6 then
      if Bool.eqb l7 r7 then
      if Bool.eqb l8 r8 then true
        else false
        else false
        else false
        else false
        else false
        else false
        else false
        else false
  end.

Theorem ascii_dec_sound : forall l r,
  ascii_dec l r = true <-> l = r.
Proof.
  unfold ascii_dec. intros.
  destruct l; destruct r.
  repeat match goal with
           | [ |- (if ?X then _ else _) = true <-> _ ] =>
             consider X; intros; subst
         end; split; congruence.
Qed.

Global Instance RelDec_ascii : RelDec (@eq Ascii.ascii) :=
{ rel_dec := ascii_dec }.

Global Instance RelDec_Correct_ascii : RelDec_Correct RelDec_ascii.
Proof.
  constructor; auto using ascii_dec_sound.
Qed.

Global Instance Reflect_ascii_dec a b : Reflect (ascii_dec a b) (a = b) (a <> b).
Proof.
  apply iff_to_reflect; auto using ascii_dec_sound.
Qed.

Definition digit2ascii (n:nat) : Ascii.ascii :=
  match n with
    | 0 => "0"
    | 1 => "1"
    | 2 => "2"
    | 3 => "3"
    | 4 => "4"
    | 5 => "5"
    | 6 => "6"
    | 7 => "7"
    | 8 => "8"
    | 9 => "9"
    | n => ascii_of_nat (n - 10 + nat_of_ascii "A")
  end%char.

Definition chr_newline : ascii :=
  Eval compute in ascii_of_nat 10.

Export Ascii.
