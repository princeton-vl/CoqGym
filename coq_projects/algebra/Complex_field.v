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
Require Export Cfield_facts.
Section Def.
Variable R : CFIELD.

Record Ctype : Type :=  {real :> R; imag : R}.

Definition Cadd (z z' : Ctype) : Ctype :=
  Build_Ctype (sgroup_law R (real z) (real z'))
    (sgroup_law R (imag z) (imag z')).

Definition Cmult (z z' : Ctype) : Ctype :=
  Build_Ctype
    (sgroup_law R (ring_mult (real z) (real z'))
       (group_inverse R (ring_mult (imag z) (imag z'))))
    (sgroup_law R (ring_mult (real z) (imag z'))
       (ring_mult (imag z) (real z'))).

Definition Copp (z : Ctype) : Ctype :=
  Build_Ctype (group_inverse R (real z)) (group_inverse R (imag z)).

Definition Cone : Ctype := Build_Ctype (ring_unit R) (monoid_unit R).

Definition Czero : Ctype := Build_Ctype (monoid_unit R) (monoid_unit R).

Definition Ceq (z z' : Ctype) :=
  Equal (real z) (real z') /\ Equal (imag z) (imag z').

Definition Cset : Setoid.
apply (Build_Setoid (Carrier:=Ctype) (Equal:=Ceq)).
red in |- *.
split; [ red in |- * | red in |- * ].
intros x; red in |- *; red in |- *; auto with algebra.
split; [ red in |- * | red in |- * ].
unfold app_rel, Ceq in |- *.
intros x y z H' H'0; split; [ try assumption | idtac ].
apply Trans with (real y); intuition.
apply Trans with (imag y); intuition.
unfold app_rel, Ceq in |- *.
intuition.
Defined.
Require Export Ring_util.

Lemma Build_Ctype_comp :
 forall x x' y y' : R,
 Equal x x' ->
 Equal y y' -> Equal (s:=Cset) (Build_Ctype x y) (Build_Ctype x' y').
intros x x' y y' H' H'0; try assumption.
simpl in |- *.
red in |- *; auto with algebra.
Qed.
Hint Resolve Build_Ctype_comp: algebra.

Lemma real_comp : forall x x' : Cset, Equal x x' -> Equal (real x) (real x').
simpl in |- *.
unfold Ceq in |- *.
intros x x' H'; elim H'; intros H'0 H'1; try exact H'0; clear H'.
Qed.
Hint Resolve real_comp: algebra.

Lemma imag_comp : forall x x' : Cset, Equal x x' -> Equal (imag x) (imag x').
simpl in |- *.
unfold Ceq in |- *.
intros x x' H'; elim H'; intros H'0 H'1; try exact H'1; clear H'.
Qed.
Hint Resolve imag_comp: algebra.

Lemma Build_Ctype_comp2 :
 forall x x' y y' : R,
 Equal x x' -> Equal y y' -> Ceq (Build_Ctype x y) (Build_Ctype x' y').
intros x x' y y' H' H'0; try assumption.
simpl in |- *.
red in |- *; auto with algebra.
Qed.
Hint Resolve Build_Ctype_comp2: algebra.

Definition Cring : RING.
apply
 (BUILD_RING (E:=Cset) (ringplus:=Cadd) (ringmult:=Cmult) (zero:=Czero)
    (un:=Cone) (ringopp:=Copp)).
unfold Cadd in |- *.
auto with algebra.
unfold Cadd in |- *.
simpl in |- *.
auto with algebra.
unfold Cadd, Czero in |- *.
simpl in |- *.
intros x; red in |- *.
simpl in |- *.
auto with algebra.
unfold Copp in |- *.
auto with algebra.
unfold Cadd, Czero, Copp in |- *.
simpl in |- *.
auto with algebra.
unfold Cadd in |- *.
auto with algebra.
unfold Cmult in |- *.
intros x x' y y' H' H'0; try assumption.
apply Build_Ctype_comp.
auto with algebra.
auto with algebra.
unfold Cmult in |- *.
simpl in |- *.
intros x y z; try assumption.
apply Build_Ctype_comp2.
apply
 Trans
  with
    (sgroup_law R
       (sgroup_law R (ring_mult (ring_mult x y) z)
          (ring_mult (group_inverse R (ring_mult (imag x) (imag y))) z))
       (group_inverse R
          (sgroup_law R (ring_mult (ring_mult x (imag y)) (imag z))
             (ring_mult (ring_mult (imag x) y) (imag z))))).
auto with algebra.
apply
 Trans
  with
    (sgroup_law R
       (sgroup_law R (ring_mult x (ring_mult y z))
          (ring_mult x (group_inverse R (ring_mult (imag y) (imag z)))))
       (group_inverse R
          (sgroup_law R (ring_mult (imag x) (ring_mult y (imag z)))
             (ring_mult (imag x) (ring_mult (imag y) z))))).
apply
 Trans
  with
    (sgroup_law R (ring_mult (ring_mult x y) z)
       (sgroup_law R
          (ring_mult (group_inverse R (ring_mult (imag x) (imag y))) z)
          (group_inverse R
             (sgroup_law R (ring_mult (ring_mult x (imag y)) (imag z))
                (ring_mult (ring_mult (imag x) y) (imag z)))))).
auto with algebra.
apply
 Trans
  with
    (sgroup_law R (ring_mult x (ring_mult y z))
       (sgroup_law R
          (ring_mult x (group_inverse R (ring_mult (imag y) (imag z))))
          (group_inverse R
             (sgroup_law R (ring_mult (imag x) (ring_mult y (imag z)))
                (ring_mult (imag x) (ring_mult (imag y) z)))))).
apply SGROUP_comp.
auto with algebra.
apply
 Trans
  with
    (sgroup_law R
       (ring_mult (group_inverse R (ring_mult (imag x) (imag y))) z)
       (sgroup_law R
          (group_inverse R (ring_mult (ring_mult (imag x) y) (imag z)))
          (group_inverse R (ring_mult (ring_mult x (imag y)) (imag z))))).
auto with algebra.
apply
 Trans
  with
    (sgroup_law R
       (ring_mult x (group_inverse R (ring_mult (imag y) (imag z))))
       (sgroup_law R
          (group_inverse R (ring_mult (imag x) (ring_mult (imag y) z)))
          (group_inverse R (ring_mult (imag x) (ring_mult y (imag z)))))).
apply
 Trans
  with
    (sgroup_law R
       (group_inverse R (ring_mult (ring_mult x (imag y)) (imag z)))
       (sgroup_law R
          (ring_mult (group_inverse R (ring_mult (imag x) (imag y))) z)
          (group_inverse R (ring_mult (ring_mult (imag x) y) (imag z))))).
apply
 Trans
  with
    (sgroup_law R
       (ring_mult (group_inverse R (ring_mult (imag x) (imag y))) z)
       (sgroup_law R
          (group_inverse R (ring_mult (ring_mult x (imag y)) (imag z)))
          (group_inverse R (ring_mult (ring_mult (imag x) y) (imag z))))).
auto with algebra.
apply
 Trans
  with
    (sgroup_law R
       (group_inverse R (ring_mult (ring_mult x (imag y)) (imag z)))
       (sgroup_law R
          (ring_mult (group_inverse R (ring_mult (imag x) (imag y))) z)
          (group_inverse R (ring_mult (ring_mult (imag x) y) (imag z))))).
auto with algebra.
auto with algebra.
apply SGROUP_comp.
apply
 Trans with (ring_mult (group_inverse R (ring_mult x (imag y))) (imag z)).
auto with algebra.
apply
 Trans with (ring_mult (ring_mult x (group_inverse R (imag y))) (imag z)).
auto with algebra.
apply
 Trans with (ring_mult x (ring_mult (group_inverse R (imag y)) (imag z))).
auto with algebra.
auto with algebra.
apply SGROUP_comp.
apply
 Trans with (group_inverse R (ring_mult (ring_mult (imag x) (imag y)) z)).
auto with algebra.
auto with algebra.
auto with algebra.
auto with algebra.
auto with algebra.
auto with algebra.
apply
 Trans
  with
    (sgroup_law R
       (sgroup_law R (ring_mult (ring_mult x y) (imag z))
          (ring_mult (group_inverse R (ring_mult (imag x) (imag y))) (imag z)))
       (sgroup_law R (ring_mult (ring_mult x (imag y)) z)
          (ring_mult (ring_mult (imag x) y) z))).
auto with algebra.
apply
 Trans
  with
    (sgroup_law R
       (sgroup_law R (ring_mult x (ring_mult y (imag z)))
          (ring_mult x (ring_mult (imag y) z)))
       (sgroup_law R (ring_mult (imag x) (ring_mult y z))
          (ring_mult (imag x) (group_inverse R (ring_mult (imag y) (imag z)))))).
apply
 Trans
  with
    (sgroup_law R (ring_mult (ring_mult x y) (imag z))
       (sgroup_law R
          (ring_mult (group_inverse R (ring_mult (imag x) (imag y))) (imag z))
          (sgroup_law R (ring_mult (ring_mult x (imag y)) z)
             (ring_mult (ring_mult (imag x) y) z)))).
auto with algebra.
apply
 Trans
  with
    (sgroup_law R (ring_mult x (ring_mult y (imag z)))
       (sgroup_law R (ring_mult x (ring_mult (imag y) z))
          (sgroup_law R (ring_mult (imag x) (ring_mult y z))
             (ring_mult (imag x)
                (group_inverse R (ring_mult (imag y) (imag z))))))).
apply SGROUP_comp.
auto with algebra.
apply
 Trans
  with
    (sgroup_law R (ring_mult (ring_mult x (imag y)) z)
       (sgroup_law R
          (ring_mult (group_inverse R (ring_mult (imag x) (imag y))) (imag z))
          (ring_mult (ring_mult (imag x) y) z))).
auto with algebra.
apply SGROUP_comp.
auto with algebra.
apply
 Trans
  with
    (sgroup_law R (ring_mult (ring_mult (imag x) y) z)
       (ring_mult (group_inverse R (ring_mult (imag x) (imag y))) (imag z))).
auto with algebra.
apply SGROUP_comp.
auto with algebra.
apply
 Trans
  with (group_inverse R (ring_mult (ring_mult (imag x) (imag y)) (imag z))).
auto with algebra.
apply
 Trans
  with (group_inverse R (ring_mult (imag x) (ring_mult (imag y) (imag z)))).
auto with algebra.
auto with algebra.
auto with algebra.
auto with algebra.
unfold Cmult, Cone in |- *.
simpl in |- *.
intros x; try assumption.
elim x.
simpl in |- *.
unfold Ceq in |- *.
simpl in |- *.
intros real0 imag0; split; [ try assumption | idtac ].
apply Trans with (sgroup_law R real0 (group_inverse R (monoid_unit R)));
 auto with algebra.
apply Trans with (sgroup_law R real0 (monoid_unit R)); auto with algebra.
apply Trans with (sgroup_law R (monoid_unit R) imag0); auto with algebra.
unfold Cmult, Cone in |- *.
simpl in |- *.
intros x; try assumption.
elim x.
simpl in |- *.
unfold Ceq in |- *.
simpl in |- *.
intros real0 imag0; split; [ try assumption | idtac ].
apply Trans with (sgroup_law R real0 (group_inverse R (monoid_unit R)));
 auto with algebra.
apply Trans with (sgroup_law R real0 (monoid_unit R)); auto with algebra.
apply Trans with (sgroup_law R imag0 (monoid_unit R)); auto with algebra.
unfold Cmult, Cadd in |- *.
simpl in |- *.
unfold Ceq in |- *.
simpl in |- *.
intros x y z; split; [ try assumption | idtac ].
apply
 Trans
  with
    (sgroup_law R (sgroup_law R (ring_mult x y) (ring_mult x z))
       (group_inverse R (ring_mult (imag x) (sgroup_law R (imag y) (imag z))))).
auto with algebra.
apply
 Trans
  with
    (sgroup_law R (ring_mult x y)
       (sgroup_law R (ring_mult x z)
          (group_inverse R
             (ring_mult (imag x) (sgroup_law R (imag y) (imag z)))))).
auto with algebra.
apply
 Trans
  with
    (sgroup_law R (ring_mult x y)
       (sgroup_law R (group_inverse R (ring_mult (imag x) (imag y)))
          (sgroup_law R (ring_mult x z)
             (group_inverse R (ring_mult (imag x) (imag z)))))).
apply SGROUP_comp.
auto with algebra.
apply
 Trans
  with
    (sgroup_law R (ring_mult x z)
       (ring_mult (group_inverse R (imag x)) (sgroup_law R (imag y) (imag z)))).
auto with algebra.
apply
 Trans
  with
    (sgroup_law R (ring_mult x z)
       (sgroup_law R (ring_mult (group_inverse R (imag x)) (imag y))
          (ring_mult (group_inverse R (imag x)) (imag z)))).
auto with algebra.
apply
 Trans
  with
    (sgroup_law R (ring_mult (group_inverse R (imag x)) (imag y))
       (sgroup_law R (ring_mult x z)
          (ring_mult (group_inverse R (imag x)) (imag z)))).
auto with algebra.
auto with algebra.
auto with algebra.
apply
 Trans
  with
    (sgroup_law R
       (sgroup_law R (ring_mult x (imag y)) (ring_mult x (imag z)))
       (sgroup_law R (ring_mult (imag x) y) (ring_mult (imag x) z))).
auto with algebra.
apply
 Trans
  with
    (sgroup_law R (ring_mult x (imag y))
       (sgroup_law R (ring_mult x (imag z))
          (sgroup_law R (ring_mult (imag x) y) (ring_mult (imag x) z)))).
auto with algebra.
apply
 Trans
  with
    (sgroup_law R (ring_mult x (imag y))
       (sgroup_law R (ring_mult (imag x) y)
          (sgroup_law R (ring_mult x (imag z)) (ring_mult (imag x) z)))).
apply SGROUP_comp.
auto with algebra.
auto with algebra.
auto with algebra.
unfold Cmult, Cadd in |- *.
simpl in |- *.
unfold Ceq in |- *.
simpl in |- *.
intros x y z; split; [ try assumption | idtac ].
apply
 Trans
  with
    (sgroup_law R (sgroup_law R (ring_mult x z) (ring_mult y z))
       (group_inverse R
          (sgroup_law R (ring_mult (imag x) (imag z))
             (ring_mult (imag y) (imag z))))).
auto with algebra.
apply
 Trans
  with
    (sgroup_law R (ring_mult x z)
       (sgroup_law R (ring_mult y z)
          (group_inverse R
             (sgroup_law R (ring_mult (imag x) (imag z))
                (ring_mult (imag y) (imag z)))))).
auto with algebra.
apply
 Trans
  with
    (sgroup_law R (ring_mult x z)
       (sgroup_law R (group_inverse R (ring_mult (imag x) (imag z)))
          (sgroup_law R (ring_mult y z)
             (group_inverse R (ring_mult (imag y) (imag z)))))).
apply SGROUP_comp.
auto with algebra.
apply
 Trans
  with
    (sgroup_law R (ring_mult y z)
       (sgroup_law R (group_inverse R (ring_mult (imag y) (imag z)))
          (group_inverse R (ring_mult (imag x) (imag z))))).
auto with algebra.
apply
 Trans
  with
    (sgroup_law R (ring_mult y z)
       (sgroup_law R (group_inverse R (ring_mult (imag x) (imag z)))
          (group_inverse R (ring_mult (imag y) (imag z))))).
auto with algebra.
auto with algebra.
auto with algebra.
apply
 Trans
  with
    (sgroup_law R
       (sgroup_law R (ring_mult x (imag z)) (ring_mult y (imag z)))
       (sgroup_law R (ring_mult (imag x) z) (ring_mult (imag y) z))).
auto with algebra.
apply
 Trans
  with
    (sgroup_law R (ring_mult x (imag z))
       (sgroup_law R (ring_mult y (imag z))
          (sgroup_law R (ring_mult (imag x) z) (ring_mult (imag y) z)))).
auto with algebra.
apply
 Trans
  with
    (sgroup_law R (ring_mult x (imag z))
       (sgroup_law R (ring_mult (imag x) z)
          (sgroup_law R (ring_mult y (imag z)) (ring_mult (imag y) z)))).
apply SGROUP_comp.
auto with algebra.
auto with algebra.
auto with algebra.
Defined.

Definition Ccring : CRING.
apply (Build_cring (cring_ring:=Cring)).
apply (Build_cring_on (R:=Cring)).
red in |- *.
simpl in |- *.
unfold Cmult, Ceq in |- *; simpl in |- *.
intros x y; split; [ try assumption | idtac ].
auto with algebra.
apply Trans with (sgroup_law R (ring_mult (imag y) x) (ring_mult y (imag x)));
 auto with algebra.
apply SGROUP_comp; auto with algebra.
exact (CRING_com (R1:=R) x (imag y)).
exact (CRING_com (R1:=R) (imag x) y).
Defined.

Definition conjugate (z : Ctype) : Ctype :=
  Build_Ctype (real z) (group_inverse R (imag z)).

Definition CdivR (z : Ctype) (r : R) : Ctype :=
  Build_Ctype (field_div (real z) r) (field_div (imag z) r).

Definition Cinv (z : Ctype) : Ctype :=
  CdivR (conjugate z) (Cmult z (conjugate z)).

Definition Cinv_map : MAP Ccring Ccring.
apply (Build_Map (A:=Ccring) (B:=Ccring) (Ap:=Cinv)).
red in |- *.
unfold Cinv in |- *.
unfold CdivR in |- *.
unfold conjugate in |- *.
intros x y H'; try assumption.
simpl in |- *.
unfold Ceq in |- *; simpl in |- *.
simpl in H'.
red in H'.
elim H'; intros H'0 H'1; try exact H'0; clear H'.
split; [ try assumption | idtac ].
unfold field_div in |- *.
apply RING_comp.
auto with algebra.
apply FIELD_comp.
apply SGROUP_comp.
auto with algebra.
auto with algebra.
unfold field_div in |- *.
apply RING_comp.
auto with algebra.
apply FIELD_comp.
apply SGROUP_comp.
auto with algebra.
auto with algebra.
Defined.
Hypothesis
  sum_of_square :
    forall x y : R,
    Equal (sgroup_law R (ring_mult x x) (ring_mult y y)) (monoid_unit R) ->
    Equal x (monoid_unit R) /\ Equal y (monoid_unit R).

Lemma C_inv_r :
 forall x : Ccring,
 ~ Equal x (monoid_unit Ccring) ->
 Equal (ring_mult x (Ap Cinv_map x)) (ring_unit Ccring).
intros x; try assumption.
simpl in |- *.
unfold Ceq in |- *; simpl in |- *.
unfold field_div in |- *.
elim x.
intros r i; try assumption.
simpl in |- *.
intros H'; split; [ try assumption | idtac ].
apply
 Trans
  with
    (sgroup_law R
       (ring_mult (ring_mult r r)
          (field_inverse
             (sgroup_law R (ring_mult r r)
                (group_inverse R (ring_mult i (group_inverse R i))))))
       (group_inverse R
          (ring_mult (ring_mult i (group_inverse R i))
             (field_inverse
                (sgroup_law R (ring_mult r r)
                   (group_inverse R (ring_mult i (group_inverse R i)))))))).
auto with algebra.
apply
 Trans
  with
    (sgroup_law (Build_field R)
       (ring_mult (ring_mult r r)
          (field_inverse
             (sgroup_law (Build_field R) (ring_mult r r)
                (group_inverse (Build_field R)
                   (ring_mult i (group_inverse (Build_field R) i))))))
       (ring_mult
          (group_inverse (Build_field R)
             (ring_mult i (group_inverse (Build_field R) i)))
          (field_inverse
             (sgroup_law (Build_field R) (ring_mult r r)
                (group_inverse (Build_field R)
                   (ring_mult i (group_inverse (Build_field R) i))))))).
auto with algebra.
apply
 Trans
  with
    (ring_mult
       (sgroup_law (Build_field R) (ring_mult r r)
          (group_inverse (Build_field R)
             (ring_mult i (group_inverse (Build_field R) i))))
       (field_inverse
          (sgroup_law (Build_field R) (ring_mult r r)
             (group_inverse (Build_field R)
                (ring_mult i (group_inverse (Build_field R) i)))))).
auto with algebra.
apply (FIELD_inverse_r (K:=R)).
red in |- *.
intros H'0; try assumption.
cut
 (Equal (sgroup_law (Build_field R) (ring_mult r r) (ring_mult i i))
    (monoid_unit (Build_field R))).
intros H'1; try assumption.
absurd (Equal r (monoid_unit R) /\ Equal i (monoid_unit R));
 auto with algebra.
apply
 Trans
  with
    (sgroup_law (Build_field R) (ring_mult r r)
       (group_inverse (Build_field R)
          (ring_mult i (group_inverse (Build_field R) i)))).
apply SGROUP_comp.
auto with algebra.
apply
 Trans
  with
    (group_inverse (Build_field R)
       (group_inverse (Build_field R) (ring_mult i i))).
auto with algebra.
auto with algebra.
auto with algebra.
apply
 Trans
  with
    (sgroup_law R
       (ring_mult (ring_mult r (group_inverse R i))
          (field_inverse
             (sgroup_law R (ring_mult r r)
                (group_inverse R (ring_mult i (group_inverse R i))))))
       (ring_mult (ring_mult i r)
          (field_inverse
             (sgroup_law R (ring_mult r r)
                (group_inverse R (ring_mult i (group_inverse R i))))))).
auto with algebra.
apply
 Trans
  with
    (ring_mult
       (sgroup_law (Build_field R)
          (ring_mult r (group_inverse (Build_field R) i)) 
          (ring_mult i r))
       (field_inverse
          (sgroup_law R (ring_mult r r)
             (group_inverse R (ring_mult i (group_inverse R i)))))).
auto with algebra.
apply
 Trans
  with
    (ring_mult (monoid_unit R)
       (field_inverse
          (sgroup_law R (ring_mult r r)
             (group_inverse R (ring_mult i (group_inverse R i)))))).
apply RING_comp.
apply
 Trans
  with
    (sgroup_law (Build_field R)
       (group_inverse (Build_field R) (ring_mult r i)) 
       (ring_mult i r)).
auto with algebra.
apply
 Trans
  with
    (sgroup_law (Build_field R)
       (group_inverse (Build_field R) (ring_mult i r)) 
       (ring_mult i r)).
auto with algebra.
auto with algebra.
auto with algebra.
auto with algebra.
Qed.

Definition C_field_on : field_on Ccring.
apply (Build_field_on (R:=Ccring) (field_inverse_map:=Cinv_map)).
exact C_inv_r.
intros x H'; try assumption.
apply Trans with (ring_mult x (Ap Cinv_map x)).
auto with algebra.
apply C_inv_r; auto with algebra.
simpl in |- *.
unfold Ceq in |- *.
simpl in |- *.
red in |- *.
intros H'; try assumption.
elim H'; intros H'0 H'1; try exact H'0; clear H'.
absurd (Equal (ring_unit R) (monoid_unit R)); auto with algebra.
Defined.

Definition CC : CFIELD := Build_cfield C_field_on.
End Def.