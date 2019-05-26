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
Require Export Field_facts.
Require Export Cfield_cat.
(** Title "Basic properties of  commutative fields." *)
Section Lemmas1.
Variable K : CFIELD.

Lemma CFIELD_com : forall x y : K, Equal (ring_mult x y) (ring_mult y x).
exact (cring_com_prf K).
Qed.
Hint Immediate CFIELD_com: algebra.

Lemma CFIELD_inverse_law2 :
 forall x y : K,
 ~ Equal x (monoid_unit K) ->
 ~ Equal y (monoid_unit K) ->
 Equal (field_inverse (ring_mult x y))
   (ring_mult (field_inverse x) (field_inverse y)).
intros x y H' H'0; try assumption.
apply Trans with (ring_mult (field_inverse y) (field_inverse x):K);
 auto with algebra.
Qed.
Hint Resolve CFIELD_inverse_law2: algebra.

Lemma CFIELD_simpl_l :
 forall x y : K,
 ~ Equal y (monoid_unit K) -> Equal (ring_mult y (field_div x y)) x.
intros x y H'; try assumption.
apply Trans with (ring_mult (field_div x y) y:K); auto with algebra.
Qed.
Hint Resolve CFIELD_simpl_l: algebra.
Comments "Normalisation.".

Lemma CFIELD_mult4 :
 forall a b c d : K,
 Equal (ring_mult (ring_mult a b) (ring_mult c d))
   (ring_mult (ring_mult a c) (ring_mult b d)).
exact (CRING_mult4 (R1:=K)).
Qed.
Hint Resolve CRING_mult4: algebra.

Lemma CFIELD_mult3 :
 forall x y z : K,
 Equal (ring_mult x (ring_mult y z)) (ring_mult y (ring_mult x z)).
exact (CRING_mult3 (R1:=K)).
Qed.
Hint Resolve CFIELD_mult3: algebra.

Lemma CFIELD_mult3bis :
 forall x y z : K,
 Equal (ring_mult (ring_mult x y) z) (ring_mult (ring_mult x z) y).
exact (CRING_mult3bis (R1:=K)).
Qed.
Hint Resolve CFIELD_mult3bis: algebra.

Lemma CFIELD_mult_div_r :
 forall x y z : K,
 Equal (ring_mult (field_div y z) x) (field_div (ring_mult y x) z).
unfold field_div in |- *.
auto with algebra.
Qed.
End Lemmas1.
Hint Resolve CFIELD_inverse_law2 CFIELD_simpl_l CFIELD_mult4 CFIELD_mult3
  CFIELD_mult3bis CFIELD_mult_div_r: algebra.
Hint Immediate CFIELD_com: algebra.
