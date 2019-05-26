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


Set Automatic Coercions Import.
Set Implicit Arguments.
Unset Strict Implicit.
Require Export Integral_domain_facts.
Require Export Cfield_cat.
Require Export Abelian_group_facts.
Require Export Ring_util.
(** Title "The field of fractions of an integral domain" "with decidable equality." *)
Section Def.
Variable R : INTEGRAL_DOMAIN.
Variable diff10 : ~ Equal (ring_unit R) (monoid_unit R).
Set Strict Implicit.
Unset Implicit Arguments.

Record fraction : Type := 
  {num : R; den : R; den_prf : ~ Equal den (monoid_unit R)}.
Set Implicit Arguments.
Unset Strict Implicit.
Hint Resolve den_prf: algebra.

Definition eqfraction (x y : fraction) :=
  Equal (ring_mult (num x) (den y)) (ring_mult (num y) (den x)).

Lemma eqfraction_refl : reflexive eqfraction.
red in |- *.
intros x; red in |- *.
red in |- *.
auto with algebra.
Qed.

Definition fraction0 := Build_fraction (monoid_unit R) (ring_unit R) diff10.

Lemma eqfraction0 :
 forall x : fraction, eqfraction x fraction0 -> Equal (num x) (monoid_unit R).
intros x; try assumption.
case x; unfold eqfraction, fraction0 in |- *; simpl in |- *.
intros numer denom H' H'0; try assumption.
apply Trans with (ring_mult numer (ring_unit R)); auto with algebra.
apply Trans with (ring_mult (monoid_unit R) denom); auto with algebra.
Qed.

Lemma eqfraction_num0 :
 forall x : fraction, Equal (num x) (monoid_unit R) -> eqfraction x fraction0.
intros x; try assumption.
case x; unfold eqfraction, fraction0 in |- *; simpl in |- *.
intros numer denom H' H'0; try assumption.
apply Trans with numer; auto with algebra.
apply Trans with (monoid_unit R); auto with algebra.
Qed.

Lemma eqfraction_sym : symmetric eqfraction.
red in |- *.
unfold app_rel, eqfraction in |- *; auto with algebra.
Qed.

Lemma eqfraction_trans : transitive eqfraction.
red in |- *.
unfold app_rel, eqfraction in |- *.
intros x y z H' H'0; try assumption.
apply INTEGRAL_DOMAIN_simpl_l with (den y).
auto with algebra.
apply Trans with (ring_mult (ring_mult (den y) (num x)) (den z)).
auto with algebra.
apply Trans with (ring_mult (ring_mult (num x) (den y)) (den z)).
auto with algebra.
apply Trans with (ring_mult (ring_mult (num y) (den x)) (den z)).
auto with algebra.
apply Trans with (ring_mult (ring_mult (den x) (num y)) (den z)).
auto with algebra.
apply Trans with (ring_mult (den x) (ring_mult (num y) (den z))).
auto with algebra.
apply Trans with (ring_mult (den x) (ring_mult (num z) (den y))).
auto with algebra.
apply Trans with (ring_mult (ring_mult (den x) (num z)) (den y)).
auto with algebra.
apply Trans with (ring_mult (ring_mult (num z) (den x)) (den y));
 auto with algebra.
Qed.

Definition fraction_set : SET.
apply (Build_Setoid (Carrier:=fraction) (Equal:=eqfraction)).
red in |- *.
split; [ try assumption | idtac ].
exact eqfraction_refl.
red in |- *.
split; [ try assumption | idtac ].
exact eqfraction_trans.
exact eqfraction_sym.
Defined.

Definition addfraction_fun (x y : fraction_set) : fraction_set :=
  Build_fraction
    (sgroup_law R (ring_mult (num x) (den y)) (ring_mult (num y) (den x)))
    (ring_mult (den x) (den y))
    (INTEGRAL_DOMAIN_prop_rev (den_prf x) (den_prf y)).

Definition opfraction_fun (x : fraction_set) : fraction_set :=
  Build_fraction (group_inverse R (num x)) (den x) (den_prf x).

Definition multfraction_fun (x y : fraction_set) : fraction_set :=
  Build_fraction (ring_mult (num x) (num y)) (ring_mult (den x) (den y))
    (INTEGRAL_DOMAIN_prop_rev (den_prf x) (den_prf y)).

Definition fraction1 : fraction_set :=
  Build_fraction (ring_unit R) (ring_unit R) diff10.

Lemma addfraction_law_l :
 forall x x' y : fraction_set,
 Equal x x' -> Equal (addfraction_fun x y) (addfraction_fun x' y).
unfold addfraction_fun in |- *; simpl in |- *.
unfold eqfraction in |- *; simpl in |- *.
intros x x' y H'; try assumption.
apply
 Trans
  with
    (ring_mult
       (ring_mult
          (sgroup_law R (ring_mult (num x) (den y))
             (ring_mult (num y) (den x))) (den x')) 
       (den y)).
auto with algebra.
apply
 Trans
  with
    (ring_mult
       (ring_mult
          (sgroup_law R (ring_mult (num x') (den y))
             (ring_mult (num y) (den x'))) (den x)) 
       (den y)).
apply RING_comp.
apply
 Trans
  with
    (sgroup_law R (ring_mult (ring_mult (num x) (den y)) (den x'))
       (ring_mult (ring_mult (num y) (den x)) (den x'))).
auto with algebra.
apply
 Trans
  with
    (sgroup_law R (ring_mult (ring_mult (num x') (den y)) (den x))
       (ring_mult (ring_mult (num y) (den x')) (den x))).
apply SGROUP_comp.
apply Trans with (ring_mult (ring_mult (den y) (num x)) (den x')).
auto with algebra.
apply Trans with (ring_mult (ring_mult (den y) (num x')) (den x)).
apply Trans with (ring_mult (den y) (ring_mult (num x) (den x'))).
auto with algebra.
apply Trans with (ring_mult (den y) (ring_mult (num x') (den x))).
auto with algebra.
auto with algebra.
auto with algebra.
apply Trans with (ring_mult (num y) (ring_mult (den x) (den x'))).
auto with algebra.
apply Trans with (ring_mult (num y) (ring_mult (den x') (den x))).
auto with algebra.
auto with algebra.
auto with algebra.
auto with algebra.
auto with algebra.
Qed.

Lemma addfraction_fun_com :
 forall x y : fraction_set, Equal (addfraction_fun x y) (addfraction_fun y x).
unfold addfraction_fun in |- *; simpl in |- *.
unfold eqfraction in |- *; simpl in |- *.
intros x y; try assumption.
apply RING_comp; auto with algebra.
Qed.

Lemma addfraction_law_r :
 forall x y y' : fraction_set,
 Equal y y' -> Equal (addfraction_fun x y) (addfraction_fun x y').
intros x y y' H'; try assumption.
apply Trans with (addfraction_fun y x).
apply addfraction_fun_com.
apply Trans with (addfraction_fun y' x).
apply addfraction_law_l; auto with algebra.
apply addfraction_fun_com.
Qed.

Lemma addfraction_law : fun2_compatible addfraction_fun.
red in |- *.
intros x x' y y' H' H'0; try assumption.
apply Trans with (addfraction_fun x' y).
apply addfraction_law_l; auto with algebra.
apply addfraction_law_r; auto with algebra.
Qed.

Lemma multfraction_dist_l :
 forall x y z : fraction_set,
 Equal (multfraction_fun x (addfraction_fun y z))
   (addfraction_fun (multfraction_fun x y) (multfraction_fun x z)).
simpl in |- *.
unfold multfraction_fun, eqfraction in |- *; simpl in |- *.
intros x y z; try assumption.
apply
 Trans
  with
    (ring_mult
       (ring_mult (num x)
          (sgroup_law R (ring_mult (num y) (den z))
             (ring_mult (num z) (den y))))
       (ring_mult (den x) (ring_mult (den y) (ring_mult (den x) (den z))))).
auto with algebra.
apply
 Trans
  with
    (ring_mult
       (ring_mult
          (ring_mult (num x)
             (sgroup_law R (ring_mult (num y) (den z))
                (ring_mult (num z) (den y)))) (den x))
       (ring_mult (den y) (ring_mult (den x) (den z)))).
auto with algebra.
apply RING_comp.
apply
 Trans
  with
    (ring_mult
       (sgroup_law R (ring_mult (num x) (ring_mult (num y) (den z)))
          (ring_mult (num x) (ring_mult (num z) (den y)))) 
       (den x)).
auto with algebra.
apply
 Trans
  with
    (sgroup_law R
       (ring_mult (ring_mult (num x) (ring_mult (num y) (den z))) (den x))
       (ring_mult (ring_mult (num x) (ring_mult (num z) (den y))) (den x))).
auto with algebra.
apply SGROUP_comp.
apply
 Trans
  with (ring_mult (ring_mult (ring_mult (num x) (num y)) (den z)) (den x)).
auto with algebra.
apply
 Trans
  with (ring_mult (ring_mult (num x) (num y)) (ring_mult (den z) (den x)));
 auto with algebra.
apply
 Trans
  with (ring_mult (ring_mult (ring_mult (num x) (num z)) (den y)) (den x)).
auto with algebra.
apply
 Trans
  with (ring_mult (ring_mult (num x) (num z)) (ring_mult (den y) (den x)));
 auto with algebra.
auto with algebra.
Qed.

Lemma multfraction_com :
 forall x y : fraction_set,
 Equal (multfraction_fun x y) (multfraction_fun y x).
simpl in |- *.
unfold multfraction_fun, eqfraction in |- *; simpl in |- *; auto with algebra.
Qed.

Definition fract_field_ring_aux : RING.
apply
 (BUILD_RING (E:=fraction_set) (ringplus:=addfraction_fun)
    (ringmult:=multfraction_fun) (zero:=fraction0) (un:=fraction1)
    (ringopp:=opfraction_fun)).
exact addfraction_law.
simpl in |- *.
unfold addfraction_fun, eqfraction in |- *; simpl in |- *.
intros x y z; try assumption.
apply
 Trans
  with
    (ring_mult
       (sgroup_law R
          (ring_mult
             (sgroup_law R (ring_mult (num x) (den y))
                (ring_mult (num y) (den x))) (den z))
          (ring_mult (num z) (ring_mult (den x) (den y))))
       (ring_mult (ring_mult (den x) (den y)) (den z))).
auto with algebra.
apply RING_comp.
apply
 Trans
  with
    (sgroup_law R
       (sgroup_law R (ring_mult (ring_mult (num x) (den y)) (den z))
          (ring_mult (ring_mult (num y) (den x)) (den z)))
       (ring_mult (num z) (ring_mult (den x) (den y)))).
auto with algebra.
apply
 Trans
  with
    (sgroup_law R (ring_mult (ring_mult (num x) (den y)) (den z))
       (sgroup_law R (ring_mult (ring_mult (num y) (den x)) (den z))
          (ring_mult (num z) (ring_mult (den x) (den y))))).
auto with algebra.
apply SGROUP_comp.
auto with algebra.
apply
 Trans
  with
    (sgroup_law R (ring_mult (ring_mult (num y) (den z)) (den x))
       (ring_mult (ring_mult (num z) (den y)) (den x))).
apply SGROUP_comp.
auto with algebra.
apply Trans with (ring_mult (num z) (ring_mult (den y) (den x)));
 auto with algebra.
auto with algebra.
auto with algebra.
simpl in |- *.
unfold addfraction_fun, eqfraction in |- *; simpl in |- *.
intros x; try assumption.
apply Trans with (ring_mult (sgroup_law R (num x) (monoid_unit R)) (den x));
 auto with algebra.
simpl in |- *.
unfold opfraction_fun, eqfraction in |- *; simpl in |- *.
intros x y H'; try assumption.
apply Trans with (group_inverse R (ring_mult (num x) (den y)));
 auto with algebra.
apply Trans with (group_inverse R (ring_mult (num y) (den x)));
 auto with algebra.
simpl in |- *.
unfold addfraction_fun, opfraction_fun, eqfraction in |- *; simpl in |- *.
intros x; try assumption.
apply
 Trans
  with
    (sgroup_law R (ring_mult (num x) (den x))
       (ring_mult (group_inverse R (num x)) (den x))); 
 auto with algebra.
apply
 Trans
  with (ring_mult (sgroup_law R (num x) (group_inverse R (num x))) (den x));
 auto with algebra.
apply Trans with (ring_mult (monoid_unit R) (den x)); auto with algebra.
apply Trans with (monoid_unit R); auto with algebra.
exact addfraction_fun_com.
simpl in |- *.
unfold multfraction_fun, eqfraction in |- *; simpl in |- *.
intros x x' y y' H' H'0; try assumption.
apply
 Trans
  with (ring_mult (ring_mult (num x) (den x')) (ring_mult (num y) (den y')));
 auto with algebra.
apply
 Trans
  with (ring_mult (ring_mult (num x') (den x)) (ring_mult (num y') (den y)));
 auto with algebra.
simpl in |- *.
unfold multfraction_fun, eqfraction in |- *; simpl in |- *.
auto with algebra.
simpl in |- *.
unfold multfraction_fun, eqfraction in |- *; simpl in |- *.
auto with algebra.
intros x; try assumption.
apply Trans with (multfraction_fun x fraction1); auto with algebra.
apply multfraction_com.
unfold multfraction_fun, eqfraction in |- *; simpl in |- *.
unfold multfraction_fun, eqfraction in |- *; simpl in |- *.
auto with algebra.
exact multfraction_dist_l.
intros x y z; try assumption.
apply Trans with (multfraction_fun z (addfraction_fun x y));
 auto with algebra.
apply multfraction_com.
apply
 Trans with (addfraction_fun (multfraction_fun z x) (multfraction_fun z y));
 auto with algebra.
apply multfraction_dist_l.
apply addfraction_law.
apply multfraction_com.
apply multfraction_com.
Defined.

Definition fract_field_ring : CRING.
apply (Build_cring (cring_ring:=fract_field_ring_aux)).
apply (Build_cring_on (R:=fract_field_ring_aux)).
exact multfraction_com.
Defined.
Variable
  zero_dec :
    forall x : R, {Equal x (monoid_unit R)} + {~ Equal x (monoid_unit R)}.

Definition invfraction_fun : fract_field_ring -> fract_field_ring :=
  fun x : fraction_set =>
  match zero_dec (num x) with
  | left _ => x
  | right n => Build_fraction (den x) (num x) n
  end.

Definition invfraction : MAP fract_field_ring fract_field_ring.
apply
 (Build_Map (A:=fract_field_ring) (B:=fract_field_ring) (Ap:=invfraction_fun)).
red in |- *.
simpl in |- *.
unfold invfraction_fun, eqfraction in |- *; simpl in |- *.
intros x y; try assumption.
case (zero_dec (num x)); intros.
case (zero_dec (num y)); intros.
auto with algebra.
simpl in |- *.
cut (Equal (den x) (monoid_unit R)).
intros H'; try assumption.
apply Trans with (ring_mult (monoid_unit R) (num y)).
auto with algebra.
apply Trans with (monoid_unit R); auto with algebra.
apply Trans with (ring_mult (den y) (monoid_unit R)); auto with algebra.
apply INTEGRAL_DOMAIN_mult_n0_l with (num y); auto with algebra.
apply Trans with (ring_mult (num x) (den y)); auto with algebra.
apply Trans with (ring_mult (monoid_unit R) (den y)); auto with algebra.
case (zero_dec (num y)); intros.
simpl in |- *.
cut (Equal (den y) (monoid_unit R)).
intros H'; try assumption.
apply Trans with (ring_mult (monoid_unit R) (num x)).
auto with algebra.
apply Trans with (monoid_unit R); auto with algebra.
apply Trans with (ring_mult (den x) (monoid_unit R)); auto with algebra.
auto with algebra.
apply INTEGRAL_DOMAIN_mult_n0_l with (num x); auto with algebra.
apply Trans with (ring_mult (num y) (den x)); auto with algebra.
apply Trans with (ring_mult (monoid_unit R) (den x)); auto with algebra.
simpl in |- *.
apply Trans with (ring_mult (num y) (den x)); auto with algebra.
apply Trans with (ring_mult (num x) (den y)); auto with algebra.
Defined.

Let ff_inr_r :
  forall x : fract_field_ring,
  ~ Equal x (monoid_unit fract_field_ring) ->
  Equal (ring_mult x (Ap invfraction x)) (ring_unit fract_field_ring).
simpl in |- *.
unfold invfraction_fun, eqfraction in |- *; simpl in |- *.
intros x; try assumption.
case (zero_dec (num x)); simpl in |- *; intros.
absurd (Equal (num x) (monoid_unit R)); auto with algebra.
intuition.
apply H.
apply Trans with (num x); auto with algebra.
apply Trans with (monoid_unit R); auto with algebra.
apply Trans with (ring_mult (num x) (den x)); auto with algebra.
apply Trans with (ring_mult (den x) (num x)); auto with algebra.
Qed.

Hint Resolve ff_inr_r: algebra.

Let ff_field_on : field_on fract_field_ring.
apply (Build_field_on (R:=fract_field_ring) (field_inverse_map:=invfraction)).
exact ff_inr_r.
intros x H'; try assumption.
apply Trans with (ring_mult x (Ap invfraction x)); auto with algebra.
simpl in |- *.
unfold eqfraction in |- *; simpl in |- *.
unfold not in |- *.
intros H'; try assumption.
absurd (Equal (ring_unit R:R) (monoid_unit R)); auto with algebra.
apply Trans with (ring_mult (ring_unit R) (ring_unit R)); auto with algebra.
apply Trans with (ring_mult (monoid_unit R) (ring_unit R)); auto with algebra.
Defined.

Definition fraction_cfield := Build_cfield ff_field_on.
End Def.
