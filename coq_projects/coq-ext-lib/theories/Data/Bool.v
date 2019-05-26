Require Import ExtLib.Core.RelDec.

Set Implicit Arguments.
Set Strict Implicit.

Global Instance RelDec_eq : RelDec (@eq bool) :=
{ rel_dec := fun x y => match x , y with
                          | true , true
                          | false , false => true
                          | _ , _=> false
                        end }.

Global Instance RelDec_Correct_eq_bool : RelDec_Correct RelDec_eq.
  constructor. destruct x; destruct y; auto; simpl; intuition.
Qed.