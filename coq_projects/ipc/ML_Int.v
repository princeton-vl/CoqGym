(* File: ML_int.v    (last edited on 25/10/2000  (c) Klaus Weich  *)

(* Axiomisation of the ML type "int" *)

Axiom Int : Set.
Axiom Less : Int -> Int -> Prop.
Axiom Equal : Int -> Int -> Prop.
Axiom int_succ : forall x : Int, {y : Int | Less x y}.
Axiom int_null : Int.

Axiom equal_dec : forall x y : Int, {Equal x y} + {~ Equal x y}.
Axiom less_dec : forall x y : Int, {Less x y} + {~ Less x y}.


Axiom
  notequal_notless_greater :
    forall x y : Int, ~ Equal x y -> ~ Less x y -> Less y x.

Axiom less_trans : forall x y z : Int, Less x y -> Less y z -> Less x z.
Axiom equal_less_less : forall x y z : Int, Equal x y -> Less y z -> Less x z.
Axiom less_equal_less : forall x y z : Int, Less x y -> Equal y z -> Less x z.
Axiom equal_sym : forall x y : Int, Equal x y -> Equal y x.
Axiom equal_trans : forall x y z : Int, Equal x y -> Equal y z -> Equal x z.
Axiom equal_refl : forall x : Int, Equal x x.
Axiom equal_eq : forall x y : Int, Equal x y -> x = y.

Axiom less_irrefl : forall x : Int, Less x x -> False.


Lemma equal_dec_refl :
 forall (i : Int) (A : Set) (a b : A),
 match equal_dec i i with
 | left _ => a
 | right _ => b
 end = a.
intros i A a b.
elim (equal_dec i i).
intros; trivial.
intros notequal; elimtype False; apply notequal.
apply equal_refl.
Qed.


Inductive max_int_spec (i0 i1 : Int) : Set :=
    Max_Int_Intro :
      forall j : Int,
      Less i0 j \/ Equal i0 j ->
      Less i1 j \/ Equal i1 j -> max_int_spec i0 i1.

Lemma max_int : forall i0 i1 : Int, max_int_spec i0 i1.
intros i0 i1.
elim (equal_dec i0 i1).
intros eq_i0_i1.
exists i0.
right.
apply equal_refl.
right.
apply equal_sym; assumption.

intros not_eq_i0_i1.
elim (less_dec i0 i1).
intros less_i0_i1.
exists i1.
left; assumption.
right.
apply equal_refl.

intros ge_i0_i1.
exists i0.
right.
apply equal_refl.
left.
apply notequal_notless_greater; assumption.
Qed.




