(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import List Arith NArith NPeano Ascii String Omega.

Set Implicit Arguments.

Local Open Scope string_scope.

Local Definition natToDigit (n : nat) : string :=
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
    | _ => "9"
  end.

Local Definition NToDigit (n : N) := natToDigit (N.to_nat n).

Local Fixpoint writeNatAux (time n : nat) (acc : string) : string :=
  let acc' := natToDigit (n mod 10) ++ acc in
  match time with
    | 0 => acc'
    | S time' =>
      match n / 10 with
        | 0 => acc'
        | n' => writeNatAux time' n' acc'
      end
  end.

Local Fixpoint writeNAux (time : nat) (n : N) (acc : string) : string :=
  let acc' := NToDigit (n mod 10)%N ++ acc in
  match time with
    | 0 => acc'
    | S time' =>
      match (n / 10)%N with
        | N0 => acc'
        | n' => writeNAux time' n' acc'
      end
  end.

Section N_to_string.
  
  Let loop := fix loop l n s :=
    let (d,r) := N.div_eucl n 10 in
    let s'    := String (ascii_of_N (48+r)) s
    in match d, l with
         | N0, _   => s'
         | _ , 0   => s'
         | _ , S l => loop l d s'
    end.
  
  (* We limit the display of N to 10^12 *)
 
  Definition string_of_N n := 
    match n with 
      | N0 => "0"
      | _  => loop 12 n EmptyString
    end.
  
End N_to_string.

Definition string_of_nat n := writeNatAux n n "".

Eval compute in string_of_N 123456789012309271072.
