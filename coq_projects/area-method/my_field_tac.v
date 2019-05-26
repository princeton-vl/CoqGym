(***************************************************************************)
(* Formalization of the Chou, Gao and Zhang's decision procedure.          *)
(* Julien Narboux (Julien@narboux.fr)                                      *)
(* LIX/INRIA FUTURS 2004-2006                                              *)
(* University of Strasbourg 2008                                           *)
(***************************************************************************)

Require Export field_general_properties.
Require Import field.
Require Import chou_gao_zhang_axioms.

(** We define our own field tactic based on the new ring *)
(** This tactic is geared toward automation because it does not generate non nullity conditions 
but it assumes that we know that the denominators of the input are not zero (syntactically !) *)
(** This tactic is also used to reduce a term to a unique fraction *)
(** This tactic is not reflexive, it is basically a reduction to the same denominators
but even using the legacy ring it is quicker than the legacy field tactic 
on our examples *)

Ltac assumption_or_ax := assumption || apply chara_not_2.

Ltac solve_conds :=  
repeat split;
repeat (assumption_or_ax || 
           apply nonzeromult || 
           apply nonzerodiv ||
           apply nonzeroinv).


Ltac smart_field := field; solve_conds.

Ltac smart_field_simplify_eq := field_simplify_eq;solve_conds.

Lemma same_denom_add_1 : forall a b c d : F, 
  b<>0 ->
  d<>0 -> 
 a/b + c/d = (a*d+c*b) / (b*d).
Proof.
intros.
smart_field.
Qed.

Lemma same_denom_add_2 : forall a b c : F, 
  b<>0 ->
  a/b + c = (a+c*b) / b.
Proof.
intros.
smart_field.
Qed.

Lemma same_denom_add_3 : forall a c d : F, 
  d<>0 -> 
  a + c/d = (a*d+c) / d.
Proof.
intros.
smart_field.
Qed.

Lemma same_denom_min_1 : forall a b c d : F, 
  b<>0 ->
  d<>0 -> 
 a/b - c/d = (a*d-c*b) / (b*d).
Proof.
intros.
smart_field.
Qed.

Lemma same_denom_min_2 : forall a b c : F, 
  b<>0 ->
 a/b - c = (a-c*b) / b.
Proof.
intros.
smart_field.
Qed.

Lemma same_denom_min_3 : forall a  c d : F, 
  d<>0 ->
 a - (c/d) = (a*d-c) / d.
Proof.
intros.
smart_field.
Qed.

Lemma same_denom_mul_1 : forall a b c d : F, 
  b<>0 ->
  d<>0 -> 
 a/b * c/d = (a*c) / (b*d).
Proof.
intros.
smart_field.
Qed.

Lemma same_denom_mul_2 : forall a b c : F, 
  b<>0 -> 
 a/b * c = (a*c) / b.
Proof.
intros.
smart_field.
Qed.

Lemma same_denom_mul_3 : forall a c d : F, 
  d<>0 -> 
 a * (c/d) = (a*c) / d.
Proof.
intros.
smart_field.
Qed.

Lemma same_denom_div_1 : forall a b c d : F, 
  b<>0 ->
  c/d<>0 ->
  d<>0 -> 
 (a/b) / (c/d) = (a*d) / (b*c).
Proof.
intros.
smart_field.
unfold not;intro.
rewrite H2 in H0.
replace (0/d) with 0 in H0.
intuition.
smart_field.
Qed.

Lemma invariant_div_1 : forall b c d,
  b<>0 ->
  c/d<>0 ->
  d<>0 ->
  b*c <> 0.
Proof.
intros.
apply nonzeromult;auto.
unfold not;intro.
subst c.
replace (0/d) with 0 in H0.
intuition.
smart_field.
Qed.

Lemma same_denom_div_3 : forall a c d : F, 
  c/d<>0 ->
  d<>0 -> 
 a / (c/d) = (a*d) / c.
Proof.
intros.
smart_field.
unfold not;intro.
rewrite H1 in H.
replace (0/d) with 0 in H.
intuition.
smart_field.
Qed.

Lemma invariant_div_3 : forall c d,
  c/d<>0 ->
  d<>0 ->
  c <> 0.
Proof.
intros.
unfold not;intro.
subst c.
replace (0/d) with 0 in H.
intuition.
smart_field.
Qed.

Lemma same_denom_div_2 : forall a b c : F, 
  b<>0 ->
  c<>0 -> 
 (a/b) / c = a / (b*c).
Proof.
intros.
smart_field.
Qed.

Lemma remove_inv : forall a : F, 
 Finv a = 1/a.
Proof.
intros.
unfold Fdiv; ring.
Qed.

Lemma remove_opp : forall a : F,
 -a = 0-a.
Proof.
intro.
ring.
Qed.

Lemma simp_1 : forall a : F,
a*0 = 0.
Proof.
intro.
ring.
Qed.

Lemma simp_2 : forall a : F,
0*a = 0.
Proof.
intro.
ring.
Qed.

Lemma simp_3 : forall a : F,
1*a = a.
Proof.
intro.
ring.
Qed.

Lemma simp_4 : forall a : F,
a*1 = a.
Proof.
intro.
ring.
Qed.

Lemma simp_5 : forall a : F,
0+a = a.
Proof.
intro.
ring.
Qed.

Lemma simp_6: forall a : F,
a+0 = a.
Proof.
intro.
ring.
Qed.

Lemma simp_7: forall a : F,
a-0 = a.
Proof.
intro.
ring.
Qed.

Lemma simp_8: forall a : F,
a-a = 0.
Proof.
intro.
ring.
Qed.

Lemma simp_9: forall a : F,
-a+a = 0.
Proof.
intro.
ring.
Qed.

Lemma simp_10: forall a b : F,
a+ -(b)= a-b.
Proof.
intros.
ring.
Qed.

Lemma simp_11 : -0=0.
Proof.
ring.
Qed.

Lemma simp_12 : forall a, - - a=a.
Proof.
intro.
ring.
Qed.

Lemma simp_13 : forall a b, - a * -b=a*b.
Proof.
intros.
ring.
Qed.

Lemma simp_14 : forall a b, (- a) * b=-(a*b).
Proof.
intros.
ring.
Qed.

Lemma simp_15 : forall a b, a * (- b)=-(a*b).
Proof.
intros.
ring.
Qed.


Hint Rewrite 
simp_1 simp_2 simp_3 simp_4 simp_5 
simp_6 simp_7 simp_8 simp_9 simp_10 
simp_11 simp_12 simp_13 simp_14 simp_15 
: ring_simplification.

Hint Rewrite 
same_denom_add_1
same_denom_add_2
same_denom_add_3
same_denom_min_1
same_denom_min_2
same_denom_min_3
same_denom_mul_1
same_denom_mul_2
same_denom_mul_3
same_denom_div_1
same_denom_div_2 
same_denom_div_3 
: same_denom.

Lemma simp_frac_1: forall a : F,
a<>0 ->
a/a = 1.
Proof.
intros.
smart_field.
Qed.

Lemma simp_frac_2: forall a : F,
a<>0 ->
a * Finv a = 1.
Proof.
intros.
smart_field.
Qed.

Lemma simp_frac_3: forall a : F,
a<>0 ->
a * - Finv a = - (1).
Proof.
intros.
smart_field.
Qed.

Lemma simp_frac_4: forall a : F,
a<>0 ->
(-a) * - Finv a = 1.
Proof.
intros.
smart_field.
Qed.

Lemma simp_frac_5: forall a : F,
a<>0 ->
(-a) / a = - (1).
Proof.
intros.
smart_field.
Qed.

Lemma simp_frac_6: forall a : F,
-a<>0 ->
a / -a = - (1).
Proof.
intros.
smart_field.
Qed.

Lemma simp_frac_7: forall a : F,
-a<>0 ->
(-a) / -a = 1.
Proof.
intros.
smart_field.
Qed.


Lemma simp_frac_8: forall a b c : F,
a*c<>0 ->
(a*b) / (a*c) = b/c.
Proof.
intros.
smart_field.
eapply multnonzero_r;eauto.
eapply multnonzero_l;eauto.
Qed.

Lemma simp_frac_9: forall a b c : F,
c*a<>0 ->
(b*a) / (c*a) = b/c.
Proof.
intros.
smart_field.
eapply multnonzero_l;eauto.
eapply multnonzero_r;eauto.
Qed.

Lemma simp_frac_10 : forall a, a<>0 ->
0/a=0. 
Proof.
intros.
smart_field.
Qed.

Lemma simp_frac_11 : forall a, a<>0 ->
a*(1/a)=1. 
Proof.
intros.
smart_field.
Qed.

Lemma simp_frac_12: forall a b : F,
b<>0 ->
(a*b) / b = a.
Proof.
intros.
smart_field.
Qed.

Lemma simp_frac_13: forall a b : F,
a<>0 ->
(a*b) / a = b.
Proof.
intros.
smart_field.
Qed.

Lemma simp_frac_14: forall a b : F,
b<>0 ->
(-a) / b = -(a/b).
Proof.
intros.
smart_field.
Qed.

Lemma simp_frac_15: forall a : F,
a / 1 = a.
Proof.
intros.
smart_field.
Geometry.
Qed.

Lemma simp_frac_16: forall a b : F,
-b<>0 -> a/(-b) = - (a/b).
Proof.
intros.
smart_field.
Geometry.
Qed.

Lemma simp_frac_16_inv : forall a, -a<>0 -> a<>0.
Proof.
intros.
unfold not;intro.
subst a.
intuition.
Qed.

Hint Rewrite 
simp_frac_1
simp_frac_2
simp_frac_3
simp_frac_4
simp_frac_5
simp_frac_6
simp_frac_7
simp_frac_8 
simp_frac_9 
simp_frac_10
simp_frac_11
simp_frac_12
simp_frac_13
simp_frac_14
simp_frac_15
simp_frac_16
: field_simplification.

Ltac basic_field_simpl_goal :=
  repeat
   match goal with
  | H:?X1<>0 |- context [?X1 / ?X1] =>
           rewrite (simp_frac_1 X1 H) in * 
  | H:?X1<>0 |- context [(- ?X1) / ?X1] =>
           rewrite (simp_frac_5 X1 H) in *
  | H:- ?X1<>0 |- context [?X1 / - ?X1] =>
           rewrite (simp_frac_6 X1 H) in *
  | H:- ?X1<>0 |- context [(-?X1) / - ?X1] =>
           rewrite (simp_frac_7 X1 H) in *
  | H: ?X1<>0 |- context [0 / ?X1] =>
           rewrite (simp_frac_10 X1 H) in *
  | H: ?X1<>0 |- context [?X1 * (1 / ?X1)] =>
           rewrite (simp_frac_11 X1 H) in *
  | H: ?X2<>0 |- context [(?X1 * ?X2) / ?X2] =>
           rewrite (simp_frac_12 X1 X2 H) in *
  | H: ?X1<>0 |- context [(?X1 * ?X2) / ?X1] =>
           rewrite (simp_frac_13 X1 X2 H) in *
  | H: ?X2<>0 |- context [(- ?X1) / ?X2] =>
           rewrite (simp_frac_14 X1 X2 H) in *
 | H: - ?X2<>0 |- context [ ?X1 / (- ?X2)] =>
           rewrite (simp_frac_16 X1 X2 H) in *;
           let T:=fresh in 
           assert (T:= simp_frac_16_inv X2 H)
  | H:_ |- context [?X1 / 1] =>
           rewrite (simp_frac_15 X1) in *
end.

Ltac basic_field_simpl_hyps :=
  repeat
   match goal with
  | H:?X1<>0, Hc: context [?X1 / ?X1] |- _ =>
           rewrite (simp_frac_1 X1 H) in *|-
  | H:?X1<>0, Hc: context [(- ?X1) / ?X1] |- _ =>
           rewrite (simp_frac_5 X1 H) in *|-
  | H:- ?X1<>0, Hc: context [?X1 / - ?X1] |- _ =>
           rewrite (simp_frac_6 X1 H) in *|-
  | H:- ?X1<>0, Hc: context [(- ?X1) / - ?X1] |- _ =>
           rewrite (simp_frac_7 X1 H) in *|-
  | H: ?X1<>0, Hc: context [0 / ?X1] |- _ =>
           rewrite (simp_frac_10 X1 H) in *|-
  | H: ?X1<>0, Hc: context [?X1 * (1 / ?X1)] |- _ =>
           rewrite (simp_frac_11 X1 H) in *|-
  | H: ?X2<>0, Hc: context [(?X1 * ?X2) / ?X2] |- _ =>
           rewrite (simp_frac_12 X1 X2 H) in *|-
  | H: ?X1<>0, Hc: context [(?X1 * ?X2) / ?X1] |- _ =>
           rewrite (simp_frac_13 X1 X2 H) in *|-
 | H: ?X2<>0, Hc: context [(-?X1) / ?X2] |- _ =>
           rewrite (simp_frac_14 X1 X2 H) in *|-
 | H: - ?X2<>0, Hc: context [ ?X1 / (- ?X2)] |- _ =>
           rewrite (simp_frac_16 X1 X2 H) in *|-;
           let T:=fresh in 
           assert (T:= simp_frac_16_inv X2 H)
 | Hc: context [?X1 / 1] |- _ =>
           rewrite (simp_frac_15 X1) in *|-
end.

Ltac basic_field_simpl := basic_field_simpl_goal;basic_field_simpl_hyps.

Goal forall a b , a<>0 -> b<>0 -> -a<>0 -> -b<>0 ->
 a/a + (-a)/a + a/(-a) + (-a)/(-a) + 0/a + a*(1/a) + (a*b)/a +(a*b)/b -a/1 +a/(-b)= 1  -> 
 b/b + (-b)/b + b/(-b) + (-b)/(-b) +0/b + b*(1/b) +(b*a)/b + (b*a)/a -b/1 + (-a)/1 = 1.
Proof.
intros.
basic_field_simpl.
ring.
Qed.

Lemma same_denom_conclude_1 : forall a b c d :F,
 a*d = c*b ->
 b<>0 ->
 d<>0 ->
 a/b = c/d. 
Proof. 
intros.
RewriteVar a H.
smart_field.
Qed.

Lemma same_denom_conclude_2 : forall a b c :F,
 a = c*b ->
 b<>0 ->
 a/b = c. 
Proof. 
intros.
rewrite H.
smart_field.
Qed.

Lemma same_denom_conclude_3 : forall a c d :F,
 a*d = c ->
 d<>0 ->
 a = c/d. 
Proof. 
intros.
rewrite <- H.
smart_field.
Qed.


Lemma same_denom_conclude_4 : forall a b : F,
 a=0 -> 
 b<>0 ->
 a/b = 0.
Proof.
intros.
field_simplify_eq; trivial.
Qed.

Lemma same_denom_conclude_5 : forall a b : F,
 0=a -> 
 b<>0 ->
 0 = a/b.
Proof.
intros.
field_simplify_eq; trivial.
Qed.

Ltac split_hyp_not_eq_zero  :=
   repeat 
   match goal with
         |  H: (Fmult _ _) <> F0 |- _ =>
                   case (multnonzero  _ _ H); clear H; intros
         | H: (Fdiv ?X ?Y) <> F0 |- _ =>
                 let T:=fresh in 
               assert (T:= (divnonzero X Y H));clear H
   end.

Goal forall x y : F,
 x*y<>0 -> x/y <> 0 -> True.
intros.
split_hyp_not_eq_zero.
auto.
Qed.

Ltac removes_inv_opp :=
 repeat rewrite remove_opp in *;
 repeat rewrite remove_inv in *.

Ltac rewrite_for_same_denom :=
match goal with 
 | H:_ |- context[?X*0] => rewrite simp_1 in *
 | H:_ |- context[0*?X] => rewrite simp_2 in *
 | H:_ |- context[1*?X] => rewrite simp_3 in *
 | H:_ |- context[?X*1] => rewrite simp_4 in *
 | H:_ |- context[0+?X] => rewrite simp_5 in *
 | H:_ |- context[?X+0] => rewrite simp_6 in * 
 | H:_ |- context[?X-0] => rewrite simp_7 in *

 | H1:?B<>0, H2: ?C/?D<>0, H3:?D<>0 |- context[?A/?B / ?C/?D ] =>
     rewrite (same_denom_div_1 A B C D H1 H2 H3) in *;
        let T:=fresh in assert (T:=(invariant_div_1 B C D H1 H2 H3))
 | H1:?B<>0, H2:?C<>0 |- context[(?A/?B) / ?C ] =>
     rewrite (same_denom_div_2 A B C H1 H2) in *;
    let T:=fresh in assert (T:=(nonzeromult B C H1 H2))
 | H1: ?C/?D<>0, H2: ?D<>0 |- context[?A / (?C/?D) ] =>
     rewrite (same_denom_div_3 A C D H1 H2) in *;
      let T:=fresh in assert (T:=(invariant_div_3 C D H1 H2))

 | H1:?B<>0, H2: ?D<>0 |- context[?A/?B + ?C/?D ] =>
     rewrite (same_denom_add_1 A B C D H1 H2) in *;
     let T:=fresh in assert (T:=(nonzeromult B D H1 H2))
 | H1:?B<>0 |- context[?A/?B + ?C ] =>
     rewrite (same_denom_add_2 A B C H1) in *
 | H2: ?D<>0 |- context[?A + ?C/?D ] =>
     rewrite (same_denom_add_3 A C D H2) in *

 | H1:?B<>0, H2: ?D<>0 |- context[?A/?B - ?C/?D ] =>
     rewrite (same_denom_min_1 A B C D H1 H2) in *;
     let T:=fresh in assert (T:=(nonzeromult B D H1 H2))
 | H1:?B<>0 |- context[?A/?B - ?C ] =>
     rewrite (same_denom_min_2 A B C H1) in *
 | H2: ?D<>0 |- context[?A - ?C/?D ] =>
     rewrite (same_denom_min_3 A C D H2) in *


 | H1:?B<>0, H2: ?D<>0 |- context[(?A/?B) * (?C/?D) ] =>
     rewrite (same_denom_mul_1 A B C D H1 H2) in *;
     let T:=fresh in assert (T:=(nonzeromult B D H1 H2))
 | H1:?B<>0 |- context[(?A/?B) * ?C ] =>
     rewrite (same_denom_mul_2 A B C H1) in *
 | H2: ?D<>0 |- context[?A * (?C/?D) ] =>
     rewrite (same_denom_mul_3 A C D H2) in *
end.

Goal forall a b c d, 
b<>0 -> d<>0 -> (a/b) + (c/d) <> 0 ->
(a/b) + (c/d) = (a * d + c * b) / (b * d) .
Proof.
intros.
rewrite_for_same_denom.
auto.
Qed.


Goal forall a b c d, 
d<>0 -> (a/b) + (c/d) <> 0 ->
a + (c/d) = (a * d + c) / d.
Proof.
intros.
rewrite_for_same_denom.
auto.
Qed.



Ltac same_denom := 
 let H:=fresh in assert (H:=chara_not_2);
 removes_inv_opp;try assumption_or_ax;
 repeat rewrite_for_same_denom.

Ltac same_denom_prepare_for_ring:=  repeat (
  (** First we try the case 0 *)
             apply same_denom_conclude_4 || 
             apply same_denom_conclude_5 || 
 (** Then the other cases *)

             apply same_denom_conclude_1 || 
             apply same_denom_conclude_2 || 
             apply same_denom_conclude_3);
  try assumption;same_denom.

Ltac Ffield_before_ring := 
 let H:=fresh in assert (H:=chara_not_2);
  same_denom;
  same_denom_prepare_for_ring.

Ltac Ffield := Ffield_before_ring;Fring.

Goal  forall f f0, 
 f0 <> 0 ->
 f * f0 - (- f0 + f * f0) * (f * f0) * / f0 <> 0 ->
 / (f * f0 - (- f0 + f * f0) * (f * f0) * / f0) * 
     (f * f0 * ((1 - f) * f0) * / f0 * f0) <> 0 ->

/ (f * f0 - (- f0 + f * f0) * (f * f0) * / f0) *
(f * f0 * ((- f0 + f * f0) * f0 * / f0)) *
/
(/ (f * f0 - (- f0 + f * f0) * (f * f0) * / f0) *
 (f * f0 * ((1 - f) * f0) * / f0 * f0)) = - (1).
Proof.
intros.
Ffield.
Qed.


Goal forall x y z t,  x<>0 -> -x <> 0 -> False ->
- (y * / x) - z * / - x + t * / x = 1.
Proof.
intros.
Ffield.
intuition.
Qed.

Goal forall f,  / 2 * f + / 2 * (/ 2 * f) <> 0 ->
- (/ 2 * (/ (/ 2 * f + / 2 * (/ 2 * f)) * (/ 2 * (/ 2 * f) * f))) +
/ 2 * (/ (/ 2 * f + / 2 * (/ 2 * f)) * (/ 2 * f * (/ 2 * f))) = 0.
Proof.
intros.
Ffield.
Qed.

Goal forall x,  / 2 * x + / 2 * (/ 2 * x) <> 0 -> / 2 * x + / 2 * (/ 2 * x) <> 0 ->
-
(/ 2 *
 (/ (/ 2 * x + / 2 * (/ 2 * x)) *
  (/ 2 * (/ 2 * x) * x))) +
/ 2 *
(/ (/ 2 * x + / 2 * (/ 2 * x)) *
 (/ 2 * x * (/ 2 * x))) = 0.
Proof.
intros.
Ffield.
Qed.

(* field; trivial works... *)
Goal forall f f1 f0, 
- (f * f1 + (1 - f) * (f0 * f1)) <> 0 ->
-
((f * f1 + (1 - f) * (f0 * f1) - f * f1) * f1 *
 / - (f * f1 + (1 - f) * (f0 * f1))) +
(f * f1 * ((1 - f) * (f0 * f1)) -
 - ((f * f1 + (1 - f) * (f0 * f1) - f * f1) * ((1 - f) * f1))) *
/ - (f * f1 + (1 - f) * (f0 * f1)) = 0.
Proof.
intros.
Ffield.
Qed.

(*...*)
Goal forall x,  / 2 * (/ 2 * x) <> 0 ->
/ 2 * x * / (/ 2 * (/ 2 * x)) = 2.
Proof.
intros.
Ffield.
Qed.

Goal forall x y z, z<>0 -> x * (y/z) = (x*y)/z.
intros.
Ffield.
Qed.

Goal forall a b c d : F,
b <> 0 ->
d <> 0 ->
a/b+c/d+a/b = a/b+c/d+a/b.
Proof.
intros.
Ffield.
Qed.

Goal forall x, -x<>0 -> -x + x = 0.
Proof.
intros.
Ffield.
Qed.

Goal forall x,  x - x = 0.
Proof.
intros.
Ffield.
Qed.

Goal forall x, x*x <> 0 -> 1<>0 ->  1/(x*x)<> 0 -> 1 / (1 / (x * x)) = x * x.
Proof.
intros.
Ffield.
Qed.

Goal forall x, 1/x<>0 -> x <> 0 -> 1 <> 0 ->  1 / (1 / x) = x.
Proof.
intros.
Ffield.
Qed.

Goal forall x, x <> 0 -> x <> 0 -> x <> 0 ->  1 / x  + 1 /x  = 2/x.
Proof.
intros.
Ffield.
Qed.

Goal forall x, 2*x <> 0 -> 2*x <> 0 -> x<>0 ->  1 / (2*x)  + 1 /(2*x)  = 1/x.
Proof.
intros.
Ffield.
Qed.

Goal forall x, 1*x <> 0 -> 1*x <> 0 -> 1/2*x<>0 -> 1 / (1*x)  + 1 /(1*x)  = 1/(1/2*x).
intros.
Ffield.
Qed.

Goal forall x,  x - (1 - - (1)) * (/ 2 * x) = 0.
intros.
Ffield.
Qed.

(** This example needs an efficient ring tactic *)

Goal forall x, x <> 0 -> 
2*2*2*2*2*2*2*2*x<>0 ->
2*2*2*2*2*2*2*2*x<>0 -> 
2*2*2*2*2*2*2*x<>0 ->
 1 / (2*2*2*2*2*2*2*2*x)  + 1 /(2*2*2*2*2*2*2*2*x)  = 1/(2*2*2*2*2*2*2*x).
Proof.
intros.
Ffield.
Qed.

Lemma eq_simpl: forall a b : F,
a-b = 0 -> a =b .
Proof.
intros.
IsoleVar a H.
rewrite H. 
ring.
Qed.

Ltac ring_simplify_eq := apply eq_simpl;ring_simplify.