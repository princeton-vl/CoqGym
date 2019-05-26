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
Require Export ZArith.
Require Export ZArith.
Require Export auxiliary.
Require Export ZArith_dec.
Require Export Zmisc.
Hint Resolve Zle_refl: algebra.
Require Export Ring_util.
Require Export Integral_domain_facts.

Definition Zr_aux : RING.
apply
 (BUILD_RING (E:=Leibnitz_set BinInt.Z) (ringplus:=Zplus) (ringmult:=Zmult)
    (zero:=0%Z) (un:=1%Z) (ringopp:=Zopp)).
simpl in |- *.
intros x x' y y' H' H'0; try assumption.
rewrite H'0.
rewrite H'.
auto with algebra.
intros x y z; try assumption.
apply Sym.
simpl in |- *.
generalize BinInt.Zplus_assoc.
intros H'; try assumption.
rewrite (H' x y z).
auto with algebra.
simpl in |- *.
intros x; try assumption.
generalize BinInt.Zplus_0_r.
intros H'; try assumption.
rewrite (H' x); auto with algebra.
simpl in |- *.
intros x y H'; try assumption.
rewrite H'; auto with algebra.
simpl in |- *.
intros x; try assumption.
generalize BinInt.Zplus_opp_r.
intros H'; try assumption.
rewrite (H' x); auto with algebra.
simpl in |- *.
intros x y; try assumption.
generalize BinInt.Zplus_comm.
intros H'; try assumption.
rewrite (H' x y); auto with algebra.
simpl in |- *.
intros x x' y y' H' H'0; try assumption.
rewrite H'0.
rewrite H'.
auto with algebra.
simpl in |- *.
intros x y z; try assumption.
generalize BinInt.Zmult_assoc.
intros H'; try assumption.
rewrite (H' x y z); auto with algebra.
simpl in |- *.
intros x; try assumption.
generalize BinInt.Zmult_1_l.
intros H'; try assumption.
replace (x * 1)%Z with (1 * x)%Z.
rewrite (H' x); auto with algebra.
apply BinInt.Zmult_comm.
intros x; try assumption.
generalize BinInt.Zmult_1_l.
intros H'; try assumption.
rewrite (H' x); auto with algebra.
intros x y z; try assumption.
generalize BinInt.Zmult_plus_distr_r.
intros H'; try assumption.
rewrite (H' x y z); auto with algebra.
intros x y z; try assumption.
generalize BinInt.Zmult_plus_distr_l.
intros H'; try assumption.
rewrite (H' x y z); auto with algebra.
Defined.

Definition Zr : CRING.
apply (Build_cring (cring_ring:=Zr_aux)).
apply (Build_cring_on (R:=Zr_aux)).
red in |- *.
simpl in |- *.
intros x y; try assumption.
generalize BinInt.Zmult_comm.
intros H'; try assumption.
rewrite (H' x y); auto with algebra.
Defined.

Definition Zzero_dec :
  forall x : Zr, {Equal x (monoid_unit Zr)} + {~ Equal x (monoid_unit Zr)}.
simpl in |- *.
intros x; try assumption.
case (Z_eq_dec x 0).
intros H'; try assumption.
cut (x = 0%Z :>BinInt.Z).
auto with algebra.
rewrite H'.
auto with algebra.
intros H'; try assumption.
cut (x <> 0%Z :>BinInt.Z).
auto with algebra.
red in |- *.
intros H'0; try assumption.
apply H'.
rewrite H'0.
auto with algebra.
Defined.

Definition ZZ : INTEGRAL_DOMAIN.
apply (Build_idomain (idomain_ring:=Zr)).
apply Build_idomain_on.
red in |- *.
intros x y; try assumption.
simpl in |- *.
generalize (BinInt.Zmult_integral_l x y).
unfold not in |- *.
intros H' H'0 H'1 H'2; try assumption.
apply H'1.
rewrite H'.
auto with algebra.
intros H'3; try assumption.
apply H'0.
rewrite H'3.
auto with algebra.
rewrite <- H'2.
change (Equal (ring_mult y x) (ring_mult x y)) in |- *.
auto with algebra.
Defined.
