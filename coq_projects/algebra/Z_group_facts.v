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
Require Export Z_group.
(** Title "Facts about powers." *)
Section Lemmas.
Variable G : GROUP.

Lemma Z_to_group_nat_eq_pos :
 forall (n : Z) (g : G), Equal (Z_to_group_nat_fun g n) (Z_to_group_fun g n).
intros n g; try assumption.
apply Trans with (Ap (sgroup_map (monoid_sgroup_hom (Z_to_group_nat g))) n);
 auto with algebra.
apply Sym.
apply Z_to_group_fun_eq.
Qed.
Hint Resolve Z_to_group_nat_eq_pos: algebra.

Lemma Zopp1 : forall n : Z, (n < 0)%Z -> (- n > 0)%Z.
simple induction n.
intros H'; try assumption.
inversion H'.
intros p H'; try assumption.
replace 0%Z with (- (0))%Z.
apply Zlt_gt; auto with algebra.
auto with algebra.
intros p H'; try assumption.
replace 0%Z with (- (0))%Z.
apply Zlt_gt; auto with algebra.
auto with algebra.
Qed.
Hint Resolve Zopp1: algebra.

Lemma Zopp2 : forall n : Z, (n > 0)%Z -> (- n < 0)%Z.
simple induction n.
intros H'; try assumption.
inversion H'.
intros p H'; try assumption.
replace 0%Z with (- (0))%Z.
apply Zgt_lt; auto with algebra.
auto with algebra.
intros p H'; try assumption.
replace 0%Z with (- (0))%Z.
apply Zgt_lt; auto with algebra.
auto with algebra.
Qed.
Hint Resolve Zopp2: algebra.

Lemma pos_abs_comp :
 forall (x : Z) (p p' : (x > 0)%Z), pos_abs p = pos_abs p'.
intros x; try assumption.
elim x.
intros p p'; try assumption.
red in p'.
inversion p.
intros p p0 p'; simpl in |- *.
auto with algebra.
intros p p0 p'; try assumption.
red in p'.
simpl in p'.
inversion p'.
Qed.
Hint Resolve Zl2 Zl1 Zl3 nat_to_group_inverse: algebra.

Lemma nat_to_group_comp :
 forall (r r' : G) (n : nat),
 Equal r r' -> Equal (nat_to_group r n) (nat_to_group r' n).
simple induction n; simpl in |- *; auto with algebra.
Qed.
Hint Resolve nat_to_group_comp: algebra.

Lemma Z_to_group_nat_fun_comp :
 forall (r r' : G) (n : Z),
 Equal r r' -> Equal (Z_to_group_nat_fun r n) (Z_to_group_nat_fun r' n).
intros r r' n H'; try assumption.
elim n.
apply Trans with (monoid_unit G); auto with algebra.
intros p; try assumption.
apply Trans with (nat_to_group r (nat_of_P (pos_abs (ax3 p))));
 auto with algebra.
apply Trans with (nat_to_group r' (nat_of_P (pos_abs (ax3 p))));
 auto with algebra.
intros p; try assumption.
apply
 Trans with (group_inverse G (nat_to_group r (nat_of_P (pos_abs (ax3 p)))));
 auto with algebra.
apply
 Trans with (group_inverse G (nat_to_group r' (nat_of_P (pos_abs (ax3 p)))));
 auto with algebra.
Qed.
Hint Resolve Z_to_group_nat_fun_comp: algebra.

Lemma Z_to_group_nat_neg :
 forall (p : positive) (r : G),
 Equal (Z_to_group_nat_fun r (Zneg p))
   (Z_to_group_nat_fun (group_inverse G r) (Zpos p)).
intros p r; try assumption.
apply
 Trans with (group_inverse G (nat_to_group r (nat_of_P (pos_abs (ax3 p)))));
 auto with algebra.
apply
 Trans with (nat_to_group (group_inverse G r) (nat_of_P (pos_abs (ax3 p))));
 auto with algebra.
Qed.
Hint Resolve Z_to_group_nat_neg: algebra.

Lemma Z_to_group_nat_inv :
 forall (n : Z) (r : G),
 Equal (Z_to_group_nat_fun r (- n)%Z)
   (Z_to_group_nat_fun (group_inverse G r) n).
simple induction n; simpl in |- *.
intros r; try assumption.
apply Trans with (monoid_unit G); auto with algebra.
auto with algebra.
intros p r; try assumption.
apply
 Trans
  with (Z_to_group_nat_fun (group_inverse G (group_inverse G r)) (Zpos p));
 auto with algebra.
Qed.
Hint Resolve Z_to_group_nat_inv: algebra.

Lemma nat_to_group_mult :
 forall (r : G) (n m : nat),
 Equal (nat_to_group r (n * m)) (nat_to_group (nat_to_group r n) m).
simple induction m; simpl in |- *.
rewrite mult_comm; simpl in |- *; auto with algebra.
intros n0 H'; try assumption.
rewrite mult_comm; simpl in |- *; auto with algebra.
simpl in |- *.
apply Trans with (sgroup_law G (nat_to_group r n) (nat_to_group r (n0 * n)));
 auto with algebra.
apply Trans with (sgroup_law G (nat_to_group r (n0 * n)) (nat_to_group r n));
 auto with algebra.
apply SGROUP_comp; auto with algebra.
rewrite mult_comm; simpl in |- *; auto with algebra.
Qed.
Hint Resolve nat_to_group_mult: algebra.

Lemma nat_to_group_unit :
 forall n : nat, Equal (nat_to_group (monoid_unit G) n) (monoid_unit G).
simple induction n; simpl in |- *; auto with algebra.
intros n0 H'; try assumption.
apply Trans with (sgroup_law G (monoid_unit G) (monoid_unit G));
 auto with algebra.
Qed.
Hint Resolve nat_to_group_unit: algebra.

Lemma Z_to_group_nat_unit :
 forall n : Z, Equal (Z_to_group_nat_fun (monoid_unit G) n) (monoid_unit G).
simple induction n; simpl in |- *; auto with algebra.
intros p; try assumption.
apply Trans with (nat_to_group (monoid_unit G) (nat_of_P (pos_abs (ax3 p))));
 auto with algebra.
intros p; try assumption.
apply
 Trans
  with
    (group_inverse G
       (nat_to_group (monoid_unit G) (nat_of_P (pos_abs (ax3 p)))));
 auto with algebra.
apply Trans with (group_inverse G (monoid_unit G)); auto with algebra.
Qed.
Hint Resolve Z_to_group_nat_unit: algebra.

Lemma group_power_plus :
 forall (g : G) (n m : ZZ),
 Equal (group_power G g (sgroup_law ZZ n m))
   (sgroup_law G (group_power G g n) (group_power G g m)).
unfold group_power in |- *; auto with algebra.
Qed.
Hint Resolve group_power_plus: algebra.

Lemma group_power_S :
 forall (g : G) (n : ZZ),
 Equal (group_power G g (sgroup_law ZZ n (ring_unit ZZ)))
   (sgroup_law G (group_power G g n) g).
unfold group_power in |- *.
simpl in |- *.
intros g n; try assumption.
apply
 Trans
  with (sgroup_law G (Z_to_group_fun g n) (Z_to_group_fun g (ring_unit Zr)));
 auto with algebra.
Qed.
Hint Resolve group_power_S: algebra.

Lemma group_power_0 :
 forall g : G, Equal (group_power G g (monoid_unit ZZ)) (monoid_unit G).
unfold group_power in |- *.
simpl in |- *.
intros g; try assumption.
apply Trans with (Z_to_group_nat_fun g 0%Z); auto with algebra.
Qed.
Hint Resolve group_power_0: algebra.

Lemma group_power_1 : forall g : G, Equal (group_power G g (ring_unit ZZ)) g.
intros g; try assumption.
apply
 Trans with (group_power G g (sgroup_law ZZ (monoid_unit ZZ) (ring_unit ZZ)));
 auto with algebra.
Qed.
Hint Resolve group_power_1: algebra.

Lemma group_power_inv :
 forall (g : G) (n : ZZ),
 Equal (group_power G g (group_inverse ZZ n))
   (group_power G (group_inverse G g) n).
unfold group_power in |- *.
intros g n; try assumption.
simpl in |- *.
apply Trans with (Z_to_group_nat_fun g (group_inverse ZZ n));
 auto with algebra.
apply Trans with (Z_to_group_nat_fun (group_inverse G g) n);
 auto with algebra.
Qed.
Hint Resolve group_power_inv: algebra.

Lemma Z_group_nat_fun_mult_pos :
 forall (p q : positive) (g : G),
 Equal (Z_to_group_nat_fun g (Zpos p * Zpos q)%Z)
   (Z_to_group_nat_fun (Z_to_group_nat_fun g (Zpos p)) (Zpos q)).
simpl in |- *.
intros p q g; try assumption.
apply
 Trans
  with
    (nat_to_group g
       (nat_of_P
          (pos_abs
             (ax3
                ((fun (x : positive) (_ : positive -> positive)
                    (y : positive) => (x * y)%positive) p
                   (fun y : positive => y) q))))); 
 auto with algebra.
apply
 Trans
  with
    (nat_to_group (Z_to_group_nat_fun g (Zpos p))
       (nat_of_P (pos_abs (ax3 q)))); auto with algebra.
simpl in |- *.
rewrite
 (fun (x y : positive) (_ : positive -> positive) =>
  nat_of_P_mult_morphism x y).
apply Trans with (nat_to_group (nat_to_group g (nat_of_P p)) (nat_of_P q));
 auto with algebra.
Qed.
Hint Resolve Z_group_nat_fun_mult_pos: algebra.

Lemma group_power_mult :
 forall (g : G) (n m : ZZ),
 Equal (group_power G g (ring_mult n m))
   (group_power G (group_power G g n) m).
unfold group_power in |- *.
intros g n m; try assumption.
simpl in |- *.
apply Trans with (Z_to_group_nat_fun g (ring_mult n m)); auto with algebra.
apply Trans with (Z_to_group_nat_fun (Z_to_group_nat_fun g n) m);
 auto with algebra.
unfold ring_mult in |- *; simpl in |- *.
elim m.
rewrite Zmult_0_r.
apply Trans with (monoid_unit G); auto with algebra.
elim n.
intros p; try assumption.
rewrite Zmult_0_l.
apply Trans with (Z_to_group_nat_fun (monoid_unit G) (Zpos p));
 auto with algebra.
auto with algebra.
intros p p0; try assumption.
replace (Zneg p * Zpos p0)%Z with (- (Zpos p * Zpos p0))%Z.
apply
 Trans with (Z_to_group_nat_fun (group_inverse G g) (Zpos p * Zpos p0)%Z);
 auto with algebra.
apply
 Trans
  with
    (Z_to_group_nat_fun (Z_to_group_nat_fun (group_inverse G g) (Zpos p))
       (Zpos p0)); auto with algebra.
rewrite <- Zopp_mult_distr_l_reverse.
auto with algebra.
elim n.
intros p; try assumption.
rewrite Zmult_0_l.
apply Trans with (Z_to_group_nat_fun (monoid_unit G) (Zneg p));
 auto with algebra.
intros p p0; try assumption.
replace (Zpos p * Zneg p0)%Z with (- (Zpos p * Zpos p0))%Z.
apply
 Trans with (Z_to_group_nat_fun (group_inverse G g) (Zpos p * Zpos p0)%Z);
 auto with algebra.
apply
 Trans
  with
    (Z_to_group_nat_fun (group_inverse G (Z_to_group_nat_fun g (Zpos p)))
       (Zpos p0)); auto with algebra.
apply
 Trans
  with
    (Z_to_group_nat_fun (Z_to_group_nat_fun (group_inverse G g) (Zpos p))
       (Zpos p0)); auto with algebra.
apply Z_to_group_nat_fun_comp; auto with algebra.
apply Trans with (Z_to_group_nat_fun g (Zneg p)); auto with algebra.
replace (Zpos p) with (- Zneg p)%Z.
auto with algebra.
auto with algebra.
intros p p0; try assumption.
replace (Zneg p * Zneg p0)%Z with (- (Zpos p * Zneg p0))%Z.
replace (Zpos p * Zneg p0)%Z with (- (Zpos p * Zpos p0))%Z.
replace (- - (Zpos p * Zpos p0))%Z with (Zpos p * Zpos p0)%Z.
apply
 Trans with (Z_to_group_nat_fun (Z_to_group_nat_fun g (Zpos p)) (Zpos p0));
 auto with algebra.
apply
 Trans
  with
    (Z_to_group_nat_fun (group_inverse G (Z_to_group_nat_fun g (Zneg p)))
       (Zpos p0)); auto with algebra.
apply Z_to_group_nat_fun_comp; auto with algebra.
apply Trans with (group_power G g (Zpos p)); auto with algebra.
apply Trans with (group_inverse G (group_power G g (Zneg p)));
 auto with algebra.
apply Sym.
apply GROUP_law_inverse.
apply Trans with (group_power G g (Zneg p + Zpos p)%Z); auto with algebra.
replace (Zneg p) with (- Zpos p)%Z.
rewrite Zplus_opp_l.
auto with algebra.
auto with algebra.
rewrite Zopp_involutive; auto with algebra.
replace (Zneg p0) with (- Zpos p0)%Z.
replace (Zpos p * - Zpos p0)%Z with (- Zpos p0 * Zpos p)%Z.
rewrite Zopp_mult_distr_l_reverse.
rewrite Zmult_comm.
auto with algebra.
rewrite Zmult_comm.
auto with algebra.
auto with algebra.
replace (Zneg p) with (- Zpos p)%Z.
rewrite Zopp_mult_distr_l_reverse.
auto with algebra.
auto with algebra.
apply Trans with (Z_to_group_nat_fun (Z_to_group_fun g n) m);
 auto with algebra.
Qed.
Hint Resolve group_power_mult: algebra.
End Lemmas.
Hint Resolve group_power_plus group_power_S group_power_0 group_power_1
  group_power_inv group_power_mult: algebra.
