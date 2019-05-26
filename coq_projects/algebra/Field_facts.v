(* This program is free software; you can redistribute it and/or      *)
(* modify it under the terms of the GNU Lesser General Public License *)
(* as published by the Free Software Foundation; either version 2.1   *)
(* of the License, or (at your option) any later version.             *)
(*                                                                    *)
(* This program is distributed in the hope that it will be useful,    *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of     *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the      *)
(* GNU General Public License for more details.                       *)
(*                                                                    *)
(* You should have received a copy of the GNU Lesser General Public   *)
(* License along with this program; if not, write to the Free         *)
(* Software Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA *)
(* 02110-1301 USA                                                     *)


Set Implicit Arguments.
Unset Strict Implicit.
Require Export Field_cat.
Require Export Ring_facts.
(** Title "Basic properties of fields." *)
Section Lemmas1.
Variable K : FIELD.

Definition field_inverse (x : K) : K := Ap (field_inverse_map K) x.

Definition field_div (x y : K) : K := ring_mult x (field_inverse y).

Lemma FIELD_inverse_r :
 forall x : K,
 ~ Equal x (monoid_unit K) ->
 Equal (ring_mult x (field_inverse x)) (ring_unit K).
exact (field_inverse_r_prf K).
Qed.

Lemma FIELD_inverse_l :
 forall x : K,
 ~ Equal x (monoid_unit K) ->
 Equal (ring_mult (field_inverse x) x) (ring_unit K).
exact (field_inverse_l_prf K).
Qed.

Lemma FIELD_unit_non_zero : ~ Equal (ring_unit K) (monoid_unit K).
exact (field_unit_non_zero K).
Qed.

Lemma FIELD_comp :
 forall x x' : K, Equal x x' -> Equal (field_inverse x) (field_inverse x').
unfold field_inverse in |- *.
auto with algebra.
Qed.
Hint Resolve FIELD_comp FIELD_inverse_r FIELD_inverse_l FIELD_unit_non_zero:
  algebra.

Lemma FIELD_unit_inverse : Equal (field_inverse (ring_unit K)) (ring_unit K).
apply Trans with (ring_mult (field_inverse (ring_unit K)) (ring_unit K));
 auto with algebra.
Qed.
Hint Resolve FIELD_unit_inverse: algebra.

Lemma FIELD_reg_left :
 forall x y z : K,
 ~ Equal x (monoid_unit K) ->
 Equal (ring_mult x y) (ring_mult x z) -> Equal y z.
intros x y z H' H'0; try assumption.
apply Trans with (ring_mult (ring_unit K) y).
auto with algebra.
apply Trans with (ring_mult (ring_mult (field_inverse x) x) y).
apply Sym; auto with algebra.
apply Trans with (ring_mult (field_inverse x) (ring_mult x y)).
auto with algebra.
apply Trans with (ring_mult (field_inverse x) (ring_mult x z)).
auto with algebra.
apply Trans with (ring_mult (ring_mult (field_inverse x) x) z).
auto with algebra.
apply Trans with (ring_mult (ring_unit K) z); auto with algebra.
Qed.

Lemma FIELD_reg_right :
 forall x y z : K,
 ~ Equal x (monoid_unit K) ->
 Equal (ring_mult y x) (ring_mult z x) -> Equal y z.
intros x y z H' H'0; try assumption.
apply Trans with (ring_mult y (ring_unit K)).
auto with algebra.
apply Trans with (ring_mult y (ring_mult x (field_inverse x))).
apply Sym; auto with algebra.
apply Trans with (ring_mult (ring_mult y x) (field_inverse x)).
auto with algebra.
apply Trans with (ring_mult (ring_mult z x) (field_inverse x)).
auto with algebra.
apply Trans with (ring_mult z (ring_mult x (field_inverse x))).
auto with algebra.
apply Trans with (ring_mult z (ring_unit K)).
auto with algebra.
auto with algebra.
Qed.

Lemma FIELD_inverse_non_zero :
 forall x : K,
 ~ Equal x (monoid_unit K) -> ~ Equal (field_inverse x) (monoid_unit K).
intuition.
apply FIELD_unit_non_zero.
apply Trans with (ring_mult (field_inverse x) x:K); auto with algebra.
apply Sym; auto with algebra.
apply Trans with (ring_mult (monoid_unit K) x:K); auto with algebra.
Qed.
Hint Resolve FIELD_inverse_non_zero: algebra.

Lemma FIELD_inverse_inverse :
 forall x : K,
 ~ Equal x (monoid_unit K) -> Equal (field_inverse (field_inverse x)) x.
intros x H'; try assumption.
apply FIELD_reg_right with (field_inverse x); auto with algebra.
apply Trans with (ring_unit K:K); auto with algebra.
apply Sym; auto with algebra.
Qed.
Hint Resolve FIELD_inverse_inverse: algebra.

Lemma FIELD_integral_domain_l :
 forall x y : K,
 ~ Equal (ring_mult x y) (monoid_unit K) -> ~ Equal x (monoid_unit K).
unfold not in |- *.
intros x y H' H'0; try assumption.
absurd (Equal (ring_mult x y) (monoid_unit K)); auto with algebra.
apply Trans with (ring_mult (monoid_unit K) y:K); auto with algebra.
Qed.

Lemma FIELD_integral_domain_r :
 forall x y : K,
 ~ Equal (ring_mult x y) (monoid_unit K) -> ~ Equal y (monoid_unit K).
unfold not in |- *.
intros x y H' H'0; try assumption.
absurd (Equal (ring_mult x y) (monoid_unit K)); auto with algebra.
apply Trans with (ring_mult x (monoid_unit K):K); auto with algebra.
Qed.

Lemma FIELD_law_inverse :
 forall x y : K,
 Equal (ring_mult x y) (ring_unit K) -> Equal (field_inverse x) y.
intros x y H'; try assumption.
apply FIELD_reg_left with x.
apply FIELD_integral_domain_l with y; auto with algebra.
intuition.
absurd (Equal (ring_unit K) (monoid_unit K)); auto with algebra.
apply Trans with (ring_mult x y:K); auto with algebra.
apply Trans with (ring_unit K:K); auto with algebra.
apply FIELD_inverse_r.
intuition.
absurd (Equal (ring_unit K) (monoid_unit K)); auto with algebra.
apply Trans with (ring_mult x y:K); auto with algebra.
apply Trans with (ring_mult (monoid_unit K) y:K); auto with algebra.
Qed.

Lemma FIELD_inverse_law :
 forall x y : K,
 ~ Equal x (monoid_unit K) ->
 ~ Equal y (monoid_unit K) ->
 Equal (field_inverse (ring_mult x y))
   (ring_mult (field_inverse y) (field_inverse x)).
intros x y H' H'0; try assumption.
apply FIELD_law_inverse.
apply
 Trans
  with
    (ring_mult x
       (ring_mult y (ring_mult (field_inverse y) (field_inverse x)))
     :K); auto with algebra.
apply
 Trans
  with
    (ring_mult x
       (ring_mult (ring_mult y (field_inverse y)) (field_inverse x))
     :K); auto with algebra.
apply Trans with (ring_mult x (ring_mult (ring_unit K) (field_inverse x)):K);
 auto with algebra.
apply Trans with (ring_mult x (field_inverse x):K); auto with algebra.
Qed.
Hint Resolve FIELD_inverse_law: algebra.

Lemma FIELD_x_div_x :
 forall x : K,
 ~ Equal x (monoid_unit K) -> Equal (field_div x x) (ring_unit K).
unfold field_div in |- *; auto with algebra.
Qed.
Hint Resolve FIELD_x_div_x: algebra.

Lemma FIELD_simpl_r :
 forall x y : K,
 ~ Equal y (monoid_unit K) -> Equal (ring_mult (field_div x y) y) x.
unfold field_div in |- *.
intros x y H'; try assumption.
apply Trans with (ring_mult x (ring_mult (field_inverse y) y):K);
 auto with algebra.
apply Trans with (ring_mult x (ring_unit K):K); auto with algebra.
Qed.
Hint Resolve FIELD_simpl_r: algebra.

Lemma FIELD_one_div_x :
 forall x : K,
 ~ Equal x (monoid_unit K) ->
 Equal (field_div (ring_unit K) x) (field_inverse x).
unfold field_div in |- *; auto with algebra.
Qed.
Hint Resolve FIELD_one_div_x: algebra.

Lemma FIELD_one_div_xy :
 forall x y : K,
 ~ Equal x (monoid_unit K) ->
 ~ Equal y (monoid_unit K) ->
 Equal (field_div (ring_unit K) (ring_mult x y))
   (ring_mult (field_div (ring_unit K) y) (field_div (ring_unit K) x)).
unfold field_div in |- *.
intros x y H' H'0; try assumption.
apply Trans with (field_inverse (ring_mult x y):K); auto with algebra.
apply Trans with (ring_mult (field_inverse y) (field_inverse x):K);
 auto with algebra.
Qed.
Hint Resolve FIELD_one_div_xy: algebra.

Lemma FIELD_one_div_div :
 forall x y : K,
 ~ Equal x (monoid_unit K) ->
 ~ Equal y (monoid_unit K) ->
 Equal (field_div (ring_unit K) (field_div x y)) (field_div y x).
unfold field_div in |- *.
intros x y H' H'0; try assumption.
apply Trans with (field_inverse (ring_mult x (field_inverse y)):K);
 auto with algebra.
apply
 Trans with (ring_mult (field_inverse (field_inverse y)) (field_inverse x):K);
 auto with algebra.
Qed.
Hint Resolve FIELD_one_div_div: algebra.

Lemma FIELD_div_div :
 forall x y z : K,
 ~ Equal y (monoid_unit K) ->
 ~ Equal z (monoid_unit K) ->
 Equal (field_div x (field_div y z)) (field_div (ring_mult x z) y).
unfold field_div in |- *.
intros x y z H' H'0; try assumption.
apply
 Trans
  with
    (ring_mult x
       (ring_mult (field_inverse (field_inverse z)) (field_inverse y))
     :K); auto with algebra.
apply Trans with (ring_mult x (ring_mult z (field_inverse y)):K);
 auto with algebra.
Qed.
Hint Resolve FIELD_div_div: algebra.
Comments "Normalisation.".

Lemma FIELD_mult_div_l :
 forall x y z : K,
 Equal (ring_mult x (field_div y z)) (field_div (ring_mult x y) z).
intros x y z; try assumption.
unfold field_div in |- *.
auto with algebra.
Qed.
Hint Resolve FIELD_mult_div_l: algebra.

Lemma FIELD_div_div2 :
 forall x y z : K,
 ~ Equal y (monoid_unit K) ->
 ~ Equal z (monoid_unit K) ->
 Equal (field_div (field_div x y) z) (field_div x (ring_mult z y)).
unfold field_div in |- *.
intros x y z H' H'0; try assumption.
apply
 Trans with (ring_mult x (ring_mult (field_inverse y) (field_inverse z)):K);
 auto with algebra.
apply Sym; auto with algebra.
Qed.

Lemma FIELD_inv_div :
 forall x y : K,
 ~ Equal x (monoid_unit K) ->
 ~ Equal y (monoid_unit K) ->
 Equal (field_inverse (field_div x y)) (field_div y x).
unfold field_div in |- *.
intros x y H' H'0; try assumption.
apply
 Trans with (ring_mult (field_inverse (field_inverse y)) (field_inverse x):K);
 auto with algebra.
Qed.
End Lemmas1.
Hint Resolve FIELD_inverse_r FIELD_inverse_l FIELD_unit_non_zero FIELD_comp
  FIELD_unit_inverse FIELD_reg_left FIELD_reg_right FIELD_inverse_non_zero
  FIELD_inverse_inverse FIELD_integral_domain_l FIELD_integral_domain_r
  FIELD_law_inverse FIELD_inverse_law FIELD_x_div_x FIELD_simpl_r
  FIELD_one_div_x FIELD_one_div_xy FIELD_one_div_div FIELD_div_div
  FIELD_mult_div_l FIELD_div_div2 FIELD_inv_div: algebra.