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
Require Export Z_group_facts.
(** Title "Universal property of integers." *)
Section Zup1.
Variable R : RING.
Hint Resolve Z_to_group_nat_eq_pos: algebra.
Hint Resolve Z_to_group_nat_unit: algebra.
Hint Resolve Zl1: algebra.
Hint Resolve Zl2: algebra.

Lemma nat_to_group_mult :
 forall n m : nat,
 Equal (nat_to_group (ring_unit R) (n * m))
   (ring_mult (nat_to_group (ring_unit R) n) (nat_to_group (ring_unit R) m)).
simple induction n; simpl in |- *.
auto with algebra.
intros n0 H' m; try assumption.
apply
 Trans
  with
    (sgroup_law R (nat_to_group (ring_unit R) m)
       (nat_to_group (ring_unit R) (n0 * m))); auto with algebra.
apply
 Trans
  with
    (sgroup_law R
       (ring_mult (nat_to_group (ring_unit R) n0)
          (nat_to_group (ring_unit R) m))
       (ring_mult (ring_unit R) (nat_to_group (ring_unit R) m)));
 auto with algebra.
apply
 Trans
  with
    (sgroup_law R
       (ring_mult (nat_to_group (ring_unit R) n0)
          (nat_to_group (ring_unit R) m)) (nat_to_group (ring_unit R) m));
 auto with algebra.
apply
 Trans
  with
    (sgroup_law R (nat_to_group (ring_unit R) m)
       (ring_mult (nat_to_group (ring_unit R) n0)
          (nat_to_group (ring_unit R) m))); auto with algebra.
Qed.
Hint Resolve nat_to_group_mult: algebra.
Hint Resolve Zl3: algebra.

Definition Z_to_ring : Hom (ZZ:RING) R.
apply
 (BUILD_HOM_RING (Ring1:=ZZ:RING) (Ring2:=R) (ff:=Z_to_group (ring_unit R))).
auto with algebra.
auto with algebra.
auto with algebra.
simpl in |- *.
intros x y; try assumption.
apply Trans with (Z_to_group_nat_fun (ring_unit R) (ring_mult (x:ZZ) y));
 auto with algebra.
apply
 Trans
  with
    (ring_mult (Z_to_group_nat_fun (ring_unit R) x)
       (Z_to_group_nat_fun (ring_unit R) y)); auto with algebra.
elim x; simpl in |- *; unfold ring_mult at 1 in |- *; simpl in |- *; intros.
apply
 Trans with (ring_mult (monoid_unit R) (Z_to_group_nat_fun (ring_unit R) y));
 auto with algebra.
apply Trans with (monoid_unit R); auto with algebra.
elim y; simpl in |- *; intros.
apply Trans with (monoid_unit R); auto with algebra.
apply
 Trans
  with
    (ring_mult (Z_to_group_nat_fun (ring_unit R) (Zpos p)) (monoid_unit R));
 auto with algebra.
apply
 Trans
  with
    (nat_to_group (ring_unit R)
       (nat_of_P
          (pos_abs
             (ax3
                ((fun (x : positive) (_ : positive -> positive)
                    (y : positive) => (x * y)%positive) p
                   (fun y : positive => y) p0))))); 
 auto with algebra.
simpl in |- *.
rewrite
 (fun (x y : positive) (_ : positive -> positive) =>
  nat_of_P_mult_morphism x y).
apply
 Trans
  with
    (ring_mult (nat_to_group (ring_unit R) (nat_of_P (pos_abs (ax3 p))))
       (nat_to_group (ring_unit R) (nat_of_P (pos_abs (ax3 p0)))));
 auto with algebra.
apply
 Trans
  with
    (group_inverse R
       (nat_to_group (ring_unit R)
          (nat_of_P
             (pos_abs
                (ax3
                   ((fun (x : positive) (_ : positive -> positive)
                       (y : positive) => (x * y)%positive) p
                      (fun y : positive => y) p0)))))); 
 auto with algebra.
simpl in |- *.
rewrite
 (fun (x y : positive) (_ : positive -> positive) =>
  nat_of_P_mult_morphism x y).
apply
 Trans
  with
    (ring_mult (nat_to_group (ring_unit R) (nat_of_P (pos_abs (ax3 p))))
       (group_inverse R
          (nat_to_group (ring_unit R) (nat_of_P (pos_abs (ax3 p0))))));
 auto with algebra.
simpl in |- *.
apply
 Trans
  with
    (group_inverse R
       (ring_mult (nat_to_group (ring_unit R) (nat_of_P p))
          (nat_to_group (ring_unit R) (nat_of_P p0)))); 
 auto with algebra.
elim y; simpl in |- *; intros.
apply Trans with (monoid_unit R); auto with algebra.
apply
 Trans
  with
    (ring_mult (Z_to_group_nat_fun (ring_unit R) (Zneg p)) (monoid_unit R));
 auto with algebra.
apply
 Trans
  with
    (group_inverse R
       (nat_to_group (ring_unit R)
          (nat_of_P
             (pos_abs
                (ax3
                   ((fun (x : positive) (_ : positive -> positive)
                       (y : positive) => (x * y)%positive) p
                      (fun y : positive => y) p0)))))); 
 auto with algebra.
simpl in |- *.
rewrite
 (fun (x y : positive) (_ : positive -> positive) =>
  nat_of_P_mult_morphism x y).
apply
 Trans
  with
    (ring_mult
       (group_inverse R
          (nat_to_group (ring_unit R) (nat_of_P (pos_abs (ax3 p)))))
       (nat_to_group (ring_unit R) (nat_of_P (pos_abs (ax3 p0)))));
 auto with algebra.
simpl in |- *.
apply
 Trans
  with
    (group_inverse R
       (ring_mult (nat_to_group (ring_unit R) (nat_of_P p))
          (nat_to_group (ring_unit R) (nat_of_P p0)))); 
 auto with algebra.
apply
 Trans
  with
    (nat_to_group (ring_unit R)
       (nat_of_P
          (pos_abs
             (ax3
                ((fun (x : positive) (_ : positive -> positive)
                    (y : positive) => (x * y)%positive) p
                   (fun y : positive => y) p0))))); 
 auto with algebra.
simpl in |- *.
rewrite
 (fun (x y : positive) (_ : positive -> positive) =>
  nat_of_P_mult_morphism x y).
apply
 Trans
  with
    (ring_mult
       (group_inverse R
          (nat_to_group (ring_unit R) (nat_of_P (pos_abs (ax3 p)))))
       (group_inverse R
          (nat_to_group (ring_unit R) (nat_of_P (pos_abs (ax3 p0))))));
 auto with algebra.
apply
 Trans
  with
    (ring_mult (nat_to_group (ring_unit R) (nat_of_P p))
       (nat_to_group (ring_unit R) (nat_of_P p0))); 
 auto with algebra.
simpl in |- *.
apply
 Trans
  with
    (group_inverse R
       (ring_mult (nat_to_group (ring_unit R) (nat_of_P p))
          (group_inverse R (nat_to_group (ring_unit R) (nat_of_P p0)))));
 auto with algebra.
apply
 Trans
  with
    (group_inverse R
       (group_inverse R
          (ring_mult (nat_to_group (ring_unit R) (nat_of_P p))
             (nat_to_group (ring_unit R) (nat_of_P p0))))); 
 auto with algebra.
simpl in |- *; auto with algebra.
Defined.

End Zup1.