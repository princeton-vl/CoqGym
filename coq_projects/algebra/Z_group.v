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
Unset Standard Proposition Elimination Names.
Require Export Zring.
Require Export Group_kernel.
(** Title "Universal property of integers." *)
Section Int_power.
Variable G : GROUP.
Set Strict Implicit.
Unset Implicit Arguments.

Definition group_square (x : G) : G := sgroup_law G x x.
Set Implicit Arguments.
Unset Strict Implicit.
End Int_power.
Section Zup1.
Variable G : GROUP.
Variable r : G.

Fixpoint nat_to_group (n : nat) : G :=
  match n with
  | O => monoid_unit G
  | S n' => sgroup_law G (nat_to_group n') r
  end.

Definition pos_abs : forall x : Z, (x > 0)%Z -> positive.
intros x; try assumption.
case x.
intros H'; red in H'.
simpl in H'.
inversion H'.
intros p H'.
exact p.
intros p H'; red in H'.
simpl in H'.
inversion H'.
Defined.

Lemma pos_abs_ok : forall (x : Z) (px : (x > 0)%Z), x = Zpos (pos_abs px).
intros x; try assumption.
elim x.
intros px; red in px.
simpl in px.
inversion px.
simpl in |- *.
auto with *.
intros p px; red in px.
simpl in px.
inversion px.
Qed.

Lemma Zlt_reg_l : forall a b c : Z, (a < b)%Z -> (c + a < c + b)%Z.
intros a b c; try assumption.
unfold Zlt, not in |- *.
intros H'; try assumption.
rewrite <- H'.
apply Zcompare_plus_compat; assumption.
Qed.

Lemma Zlemma1 : forall x : Z, (x < 0)%Z -> (- x > 0)%Z.
intros x H'; try assumption.
apply Zlt_gt.
replace (- x)%Z with (- x + 0)%Z.
pattern 0%Z at 1 in |- *.
replace 0%Z with (- x + x)%Z.
apply Zlt_reg_l.
auto with *.
apply Zplus_opp_l.
apply Zplus_0_r.
Qed.
Comments "The powers of" r ".".

Definition Z_to_group_nat_fun : ZZ -> G.
intros x.
case (Z_gt_le_dec x 0); intros z.
exact (nat_to_group (nat_of_P (pos_abs z))).
case (Z_le_lt_eq_dec _ _ z); intros.
cut (- x > 0)%Z.
intros H'.
exact (group_inverse G (nat_to_group (nat_of_P (pos_abs H')))).
apply Zlemma1.
auto with *.
exact (monoid_unit G).
Defined.

Lemma nat_to_group_com :
 forall n : nat,
 Equal (sgroup_law G (nat_to_group n) r) (sgroup_law G r (nat_to_group n)).
simple induction n; simpl in |- *; auto with *.
apply Trans with r; auto with *.
intros n0 H'; try assumption.
apply Trans with (sgroup_law G (sgroup_law G r (nat_to_group n0)) r);
 auto with *.
Qed.
Hint Resolve nat_to_group_com: algebra.

Lemma nat_to_group_add :
 forall n m : nat,
 Equal (nat_to_group (n + m))
   (sgroup_law G (nat_to_group n) (nat_to_group m)).
simple induction n; simpl in |- *.
auto with *.
intros n0 H' m; try assumption.
apply
 Trans
  with (sgroup_law G (nat_to_group n0) (sgroup_law G r (nat_to_group m)));
 auto with *.
apply
 Trans
  with (sgroup_law G (nat_to_group n0) (sgroup_law G (nat_to_group m) r));
 auto with *.
apply
 Trans
  with (sgroup_law G (sgroup_law G (nat_to_group n0) (nat_to_group m)) r);
 auto with *.
Qed.
Hint Resolve nat_to_group_add: algebra.

Lemma ax1 : ~ (0 > 0)%Z.
red in |- *.
intros H'; try assumption.
red in H'.
simpl in H'.
inversion H'.
Qed.
Hint Resolve ax1: algebra.

Lemma ax2 : ~ (0 < 0)%Z.
red in |- *.
intros H'; try assumption.
red in H'.
simpl in H'.
inversion H'.
Qed.
Hint Resolve ax2: algebra.

Lemma Zl1 : Equal (Z_to_group_nat_fun 0%Z) (monoid_unit G).
unfold Z_to_group_nat_fun in |- *.
case (Z_gt_le_dec 0 0).
intros z; try assumption.
absurd (0 > 0)%Z; auto with *.
intros z; try assumption.
case (Z_le_lt_eq_dec 0 0 z).
intros z0; try assumption.
absurd (0 < 0)%Z; auto with *.
auto with *.
Qed.
Hint Resolve Zl1: algebra.

Lemma ax3 : forall p : positive, (Zpos p > 0)%Z.
intros p; try assumption.
red in |- *.
simpl in |- *.
auto with *.
Qed.
Hint Resolve ax3: algebra.

Lemma Zl2 :
 forall p : positive,
 Equal (Z_to_group_nat_fun (Zpos p))
   (nat_to_group (nat_of_P (pos_abs (ax3 p)))).
intros p; try assumption.
unfold Z_to_group_nat_fun in |- *.
case (Z_gt_le_dec (Zpos p) 0); intros z.
simpl in |- *; auto with *.
case (Z_le_lt_eq_dec (Zpos p) 0 z); intros.
absurd (Zpos p < 0)%Z; auto with *.
inversion e.
Qed.
Hint Resolve Zl2: algebra.

Lemma ax4 : forall p : positive, ~ (Zneg p > 0)%Z.
intros p; red in |- *.
intros H'; try assumption.
red in H'.
simpl in H'.
inversion H'.
Qed.
Hint Resolve ax4: algebra.

Lemma Zl3 :
 forall p : positive,
 Equal (Z_to_group_nat_fun (Zneg p))
   (group_inverse G (nat_to_group (nat_of_P (pos_abs (ax3 p))))).
intros p; try assumption.
unfold Z_to_group_nat_fun in |- *.
case (Z_gt_le_dec (Zneg p) 0); intros z.
absurd (Zneg p > 0)%Z; auto with *.
case (Z_le_lt_eq_dec (Zneg p) 0 z); intros.
simpl in |- *; auto with *.
inversion e.
Qed.
Hint Resolve Zl3: algebra.

Lemma ax5 :
 forall p q : positive,
 (Zpos p > Zpos q)%Z -> (Zpos p + Zneg q)%Z = Zpos (p - q).
intros p q H'; red in H'.
simpl in H'.
simpl in |- *.
rewrite Z.pos_sub_spec.
rewrite H'.
auto with *.
Qed.

Lemma ax6 :
 forall p q : positive,
 (Zpos p < Zpos q)%Z -> (Zpos p + Zneg q)%Z = Zneg (q - p).
intros p q H'; red in H'.
simpl in H'.
simpl in |- *.
rewrite Z.pos_sub_spec.
rewrite H'.
auto with *.
Qed.

Lemma ax7 : forall p : positive, (Zpos p + Zneg p)%Z = 0%Z.
intros p; try assumption.
simpl in |- *.
rewrite Z.pos_sub_spec; unfold Pos.compare.
replace (Pcompare p p Datatypes.Eq) with Datatypes.Eq.
auto with *.
elim p.
intros p0; simpl in |- *.
auto with *.
intros p0; simpl in |- *.
auto with *.
simpl in |- *.
auto with *.
Qed.
Hint Resolve ax7 ax6 ax5: algebra.

Lemma nat_to_group_com2 :
 forall n m : nat,
 Equal (sgroup_law G (nat_to_group n) (nat_to_group m))
   (sgroup_law G (nat_to_group m) (nat_to_group n)).
simple induction n; simpl in |- *; auto with *.
intros m; try assumption.
apply Trans with (nat_to_group m); auto with *.
intros n0 H' m; try assumption.
apply
 Trans
  with (sgroup_law G (nat_to_group n0) (sgroup_law G r (nat_to_group m)));
 auto with *.
apply
 Trans
  with (sgroup_law G (nat_to_group n0) (sgroup_law G (nat_to_group m) r));
 auto with *.
apply
 Trans
  with (sgroup_law G (sgroup_law G (nat_to_group n0) (nat_to_group m)) r);
 auto with *.
apply
 Trans
  with (sgroup_law G (sgroup_law G (nat_to_group m) (nat_to_group n0)) r);
 auto with *.
Qed.
Hint Resolve nat_to_group_com2: algebra.

Lemma nat_to_group_minus :
 forall n m : nat,
 n > m ->
 Equal (nat_to_group (n - m))
   (sgroup_law G (nat_to_group n) (group_inverse G (nat_to_group m))).
intros n m H'; try assumption.
replace n with (m + (n - m)).
rewrite minus_plus.
apply
 Trans
  with
    (sgroup_law G (sgroup_law G (nat_to_group m) (nat_to_group (n - m)))
       (group_inverse G (nat_to_group m))); auto with *.
apply GROUP_reg_right with (nat_to_group m); auto with *.
apply
 Trans
  with
    (sgroup_law G (sgroup_law G (nat_to_group m) (nat_to_group (n - m)))
       (sgroup_law G (group_inverse G (nat_to_group m)) (nat_to_group m)));
 auto with *.
apply
 Trans
  with
    (sgroup_law G (sgroup_law G (nat_to_group m) (nat_to_group (n - m)))
       (monoid_unit G)); auto with *.
apply Trans with (sgroup_law G (nat_to_group m) (nat_to_group (n - m)));
 auto with *.
auto with *.
Qed.
Hint Resolve nat_to_group_minus: algebra.

Lemma ax8 :
 forall p q : positive,
 Pcompare p q Datatypes.Eq = Datatypes.Lt ->
 Pcompare q p Datatypes.Eq = Datatypes.Gt.
intros p q H'; try assumption.
apply nat_of_P_gt_Gt_compare_complement_morphism.
red in |- *.
apply nat_of_P_lt_Lt_compare_morphism; auto with *.
Qed.
Hint Resolve ax8: algebra.

Lemma Zl4 :
 forall p p0 : positive,
 Equal (Z_to_group_nat_fun (Zpos p + Zneg p0)%Z)
   (sgroup_law G (nat_to_group (nat_of_P p))
      (group_inverse G (nat_to_group (nat_of_P p0)))).
intros p p0; try assumption.
case (Z_gt_le_dec (Zpos p) (Zpos p0)); intros z.
rewrite ax5; auto with *.
apply Trans with (nat_to_group (nat_of_P (pos_abs (ax3 (p - p0)))));
 auto with *.
simpl in |- *.
rewrite nat_of_P_minus_morphism; auto with *.
apply nat_to_group_minus.
apply nat_of_P_gt_Gt_compare_morphism.
auto with *.
case (Z_le_lt_eq_dec _ _ z); intros.
rewrite ax6; auto with *.
apply
 Trans
  with (group_inverse G (nat_to_group (nat_of_P (pos_abs (ax3 (p0 - p))))));
 auto with *.
simpl in |- *.
rewrite nat_of_P_minus_morphism; auto with *.
apply
 Trans
  with
    (group_inverse G
       (sgroup_law G (nat_to_group (nat_of_P p0))
          (group_inverse G (nat_to_group (nat_of_P p))))); 
 auto with *.
apply GROUP_comp.
apply nat_to_group_minus.
apply nat_of_P_gt_Gt_compare_morphism.
auto with *.
apply
 Trans
  with
    (sgroup_law G
       (group_inverse G (group_inverse G (nat_to_group (nat_of_P p))))
       (group_inverse G (nat_to_group (nat_of_P p0)))); 
 auto with *.
injection e.
intros H'; try assumption.
rewrite <- H'.
rewrite ax7.
apply Trans with (monoid_unit G); auto with *.
Qed.
Hint Resolve Zl4: algebra.

Lemma nat_to_group_com3 :
 forall n : nat,
 Equal (sgroup_law G (nat_to_group n) (group_inverse G r))
   (sgroup_law G (group_inverse G r) (nat_to_group n)).
simple induction n; simpl in |- *; auto with *.
apply Trans with (group_inverse G r); auto with *.
intros n0 H'; try assumption.
apply
 Trans
  with (sgroup_law G (nat_to_group n0) (sgroup_law G r (group_inverse G r)));
 auto with *.
apply Trans with (sgroup_law G (nat_to_group n0) (monoid_unit G));
 auto with *.
apply Trans with (nat_to_group n0); auto with *.
apply
 Trans
  with (sgroup_law G (group_inverse G r) (sgroup_law G r (nat_to_group n0)));
 auto with *.
apply
 Trans
  with (sgroup_law G (sgroup_law G (group_inverse G r) r) (nat_to_group n0));
 auto with *.
apply Trans with (sgroup_law G (monoid_unit G) (nat_to_group n0));
 auto with *.
Qed.
Hint Resolve nat_to_group_com3: algebra.

Lemma Zl5 : Equal (Z_to_group_nat_fun (ring_unit ZZ)) r.
unfold Z_to_group_nat_fun in |- *.
case (Z_gt_le_dec (ring_unit ZZ) 0).
intros z; try assumption.
simpl in |- *.
auto with *.
intros z; try assumption.
case (Z_le_lt_eq_dec (ring_unit ZZ) 0 z).
intros z0; try assumption.
absurd (ring_unit ZZ < 0)%Z; auto with *.
intros H'; try assumption.
inversion H'.
Qed.
Hint Resolve Zl5: algebra.

Lemma nat_to_group_com4 :
 forall n m : nat,
 Equal (sgroup_law G (nat_to_group m) (group_inverse G (nat_to_group n)))
   (sgroup_law G (group_inverse G (nat_to_group n)) (nat_to_group m)).
simple induction n; simpl in |- *; auto with *.
intros m; try assumption.
apply Trans with (sgroup_law G (nat_to_group m) (monoid_unit G)); auto with *.
apply Trans with (nat_to_group m); auto with *.
apply Trans with (sgroup_law G (monoid_unit G) (nat_to_group m)); auto with *.
intros n0 H' m; try assumption.
apply
 Trans
  with
    (sgroup_law G (nat_to_group m)
       (sgroup_law G (group_inverse G r) (group_inverse G (nat_to_group n0))));
 auto with *.
apply
 Trans
  with
    (sgroup_law G (sgroup_law G (nat_to_group m) (group_inverse G r))
       (group_inverse G (nat_to_group n0))); auto with *.
apply
 Trans
  with
    (sgroup_law G (sgroup_law G (group_inverse G r) (nat_to_group m))
       (group_inverse G (nat_to_group n0))); auto with *.
apply
 Trans
  with
    (sgroup_law G (group_inverse G r)
       (sgroup_law G (nat_to_group m) (group_inverse G (nat_to_group n0))));
 auto with *.
apply
 Trans
  with
    (sgroup_law G (group_inverse G r)
       (sgroup_law G (group_inverse G (nat_to_group n0)) (nat_to_group m)));
 auto with *.
apply
 Trans
  with
    (sgroup_law G
       (sgroup_law G (group_inverse G r) (group_inverse G (nat_to_group n0)))
       (nat_to_group m)); auto with *.
Qed.
Hint Resolve nat_to_group_com4: algebra.
Comments "The group  morphism from the integers to an arbitrary group.".

Definition Z_to_group_nat : Hom (ZZ:GROUP) G.
apply (BUILD_HOM_GROUP (G:=ZZ:GROUP) (G':=G) (ff:=Z_to_group_nat_fun)).
simpl in |- *.
intros x y H'; try assumption.
rewrite H'; auto with *.
simple induction x; simple induction y; simpl in |- *.
unfold sgroup_law at 1 in |- *; simpl in |- *.
apply Trans with (sgroup_law G (Z_to_group_nat_fun 0%Z) (monoid_unit G));
 auto with *.
intros p; try assumption.
rewrite Zplus_0_l.
apply Trans with (sgroup_law G (monoid_unit G) (Z_to_group_nat_fun (Zpos p)));
 auto with *.
intros p; try assumption.
rewrite Zplus_0_l.
apply Trans with (sgroup_law G (monoid_unit G) (Z_to_group_nat_fun (Zneg p)));
 auto with *.
rewrite Zplus_0_r.
apply Trans with (sgroup_law G (Z_to_group_nat_fun (Zpos p)) (monoid_unit G));
 auto with *.
unfold sgroup_law at 1 in |- *; simpl in |- *.
intros p0; try assumption.
apply Trans with (nat_to_group (nat_of_P (pos_abs (ax3 (p + p0)))));
 auto with *.
apply
 Trans
  with
    (sgroup_law G (nat_to_group (nat_of_P (pos_abs (ax3 p))))
       (nat_to_group (nat_of_P (pos_abs (ax3 p0))))); 
 auto with *.
simpl in |- *.
rewrite nat_of_P_plus_morphism.
auto with *.
intros p0; try assumption.
apply
 Trans
  with
    (sgroup_law G (nat_to_group (nat_of_P (pos_abs (ax3 p))))
       (group_inverse G (nat_to_group (nat_of_P (pos_abs (ax3 p0))))));
 auto with *.
apply Trans with (sgroup_law G (Z_to_group_nat_fun (Zneg p)) (monoid_unit G));
 auto with *.
intros p0; try assumption.
rewrite Zplus_comm.
apply
 Trans
  with
    (sgroup_law G
       (group_inverse G (nat_to_group (nat_of_P (pos_abs (ax3 p)))))
       (nat_to_group (nat_of_P (pos_abs (ax3 p0))))); 
 auto with *.
apply
 Trans
  with
    (sgroup_law G (nat_to_group (nat_of_P (pos_abs (ax3 p0))))
       (group_inverse G (nat_to_group (nat_of_P (pos_abs (ax3 p))))));
 auto with *.
unfold sgroup_law at 1 in |- *; simpl in |- *.
simpl in |- *; auto with *.
intros p0; try assumption.
apply
 Trans
  with (group_inverse G (nat_to_group (nat_of_P (pos_abs (ax3 (p + p0))))));
 auto with *.
apply
 Trans
  with
    (sgroup_law G
       (group_inverse G (nat_to_group (nat_of_P (pos_abs (ax3 p)))))
       (group_inverse G (nat_to_group (nat_of_P (pos_abs (ax3 p0))))));
 auto with *.
simpl in |- *.
rewrite nat_of_P_plus_morphism.
apply
 Trans
  with
    (group_inverse G
       (sgroup_law G (nat_to_group (nat_of_P p)) (nat_to_group (nat_of_P p0))));
 auto with *.
apply
 Trans
  with
    (group_inverse G
       (sgroup_law G (nat_to_group (nat_of_P p0)) (nat_to_group (nat_of_P p))));
 auto with *.
auto with *.
Defined.
End Zup1.
Hint Resolve nat_to_group_com nat_to_group_add nat_to_group_com2
  nat_to_group_minus nat_to_group_com3 nat_to_group_com4: algebra.
Section Zup2.
Variable G : GROUP.
Section pos_def.
Variable r : G.

Fixpoint pos_to_group (p : positive) : G :=
  match p with
  | xH => r
  | xO p' => group_square G (pos_to_group p')
  | xI p' => sgroup_law G (group_square G (pos_to_group p')) r
  end.

Lemma pos_nat_group :
 forall p : positive, Equal (pos_to_group p) (nat_to_group r (nat_of_P p)).
simple induction p; simpl in |- *.
intros p0 H'; try assumption.
rewrite ZL6.
unfold group_square in |- *.
apply
 Trans
  with
    (sgroup_law G
       (sgroup_law G (nat_to_group r (nat_of_P p0))
          (nat_to_group r (nat_of_P p0))) r); auto with *.
unfold group_square in |- *.
intros p0 H'; try assumption.
unfold nat_of_P in |- *.
simpl in |- *.
rewrite ZL6.
apply
 Trans
  with
    (sgroup_law G (nat_to_group r (nat_of_P p0))
       (nat_to_group r (nat_of_P p0))); auto with *.
auto with *.
Qed.
End pos_def.
Hint Resolve pos_nat_group: algebra.
Variable r : G.

Definition Z_to_group_fun : ZZ -> G.
intros x.
case (Z_gt_le_dec x 0); intros z.
exact (pos_to_group r (pos_abs z)).
case (Z_le_lt_eq_dec _ _ z); intros.
cut (- x > 0)%Z.
intros H'.
exact (pos_to_group (group_inverse G r) (pos_abs H')).
apply Zlemma1.
auto with *.
exact (monoid_unit G).
Defined.

Lemma nat_to_group_inverse :
 forall (n : nat) (r : G),
 Equal (group_inverse G (nat_to_group r n))
   (nat_to_group (group_inverse G r) n).
simple induction n; simpl in |- *; auto with *.
intros n0 H' r0; try assumption.
apply
 Trans
  with
    (sgroup_law G (group_inverse G r0) (group_inverse G (nat_to_group r0 n0)));
 auto with *.
apply
 Trans
  with
    (sgroup_law G (group_inverse G r0) (nat_to_group (group_inverse G r0) n0));
 auto with *.
Qed.
Hint Resolve nat_to_group_inverse: algebra.

Lemma Z_to_group_fun_eq :
 forall z : ZZ, Equal (Z_to_group_fun z) (Z_to_group_nat r z).
intros z; simpl in |- *.
unfold Z_to_group_fun in |- *.
unfold Z_to_group_nat_fun in |- *.
case (Z_gt_le_dec z 0); intros z0.
auto with *.
case (Z_le_lt_eq_dec z 0 z0); intros z1.
apply
 Trans
  with (nat_to_group (group_inverse G r) (nat_of_P (pos_abs (Zlemma1 z1))));
 auto with *.
auto with *.
Qed.
Hint Resolve Z_to_group_fun_eq: algebra.

Definition Z_to_group : Hom (ZZ:GROUP) G.
apply (BUILD_HOM_GROUP (G:=ZZ:GROUP) (G':=G) (ff:=Z_to_group_fun)).
intros x y H'; try assumption.
apply Trans with (Z_to_group_nat r x); auto with *.
apply Trans with (Z_to_group_nat r y); auto with *.
intros x y; try assumption.
apply Trans with (Z_to_group_nat r (sgroup_law ZZ x y)); auto with *.
apply Trans with (sgroup_law G (Z_to_group_nat r x) (Z_to_group_nat r y));
 auto with *.
apply Trans with (Z_to_group_nat r (monoid_unit ZZ)); auto with *.
Defined.
End Zup2.
Set Strict Implicit.
Unset Implicit Arguments.

Definition group_power (G : GROUP) (x : G) (n : ZZ) := Z_to_group x n.
Set Implicit Arguments.
Unset Strict Implicit.

Definition sgroup_powers (G : GROUP) (g : G) := coKer (Z_to_group g).

Lemma sgroup_powers_prop :
 forall (G : GROUP) (g x : G),
 in_part x (sgroup_powers g) -> exists n : ZZ, Equal x (group_power G g n).
intros G g x H'; try assumption.
elim H'.
intros x0 H'0; try assumption.
elim H'0; intros H'1 H'2; try exact H'2; clear H'0.
exists x0; try assumption.
Qed.

Lemma sgroup_powers_rev :
 forall (G : GROUP) (g : G) (n : ZZ),
 in_part (group_power G g n) (sgroup_powers g).
intros G g n; try assumption.
simpl in |- *.
exists n; split; [ idtac | try assumption ].
auto with *.
unfold group_power in |- *; auto with *.
Qed.
Hint Resolve sgroup_powers_prop sgroup_powers_rev: algebra.
