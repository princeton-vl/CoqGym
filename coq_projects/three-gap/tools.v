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


(****************************************************************************)
(*                                                                          *)
(*  Proof of the three gap theorem.                                         *)
(*                                                                          *)
(*  Micaela Mayero (INRIA-Rocquencourt)                                     *)
(*  September 1998                                                          *)
(*                                                                          *)
(****************************************************************************)
(****************************************************************************)
(*                               tools.v                                    *)
(****************************************************************************)

(*********************************************************)
(*            Tools for The three gap theorem            *)
(*                                                       *)
(*********************************************************)

Require Export Reals.
Require Export Nat_compl.

Unset Standard Proposition Elimination Names.

Parameter alpha : R.
(*********************************************************)

Axiom prop_alpha : (0 < alpha)%R /\ (alpha < 1)%R.

(*********************************************************)
(*           first and last                              *)
(*********************************************************)

(**********)
Definition frac_part_n_alpha (n : nat) : R := frac_part (INR n * alpha).

(**********)
Definition ordre_total (n m : nat) :=
  (0 < alpha)%R /\ (alpha < 1)%R ->
  (frac_part_n_alpha n <= frac_part_n_alpha m)%R.

(**********)
Lemma N_classic : forall N : nat, {N = 0} + {N = 1} + {N >= 2}.
simple induction N; auto with arith real.
intros; elim H; intro y.
elim y; intro y0.
left; right; auto with arith real.
right; rewrite <- y0; auto with arith real.
right; auto with arith real.
Qed.

(**********)
Lemma tech_total_order : forall n : nat, ordre_total n n.
intro; unfold ordre_total in |- *; intro; unfold Rle in |- *; right;
 auto with arith real.
Qed.

(**********)
Lemma exist_first :
 forall N : nat,
 N >= 2 ->
 sigT
   (fun n : nat =>
    0 < n /\ n < N /\ (forall m : nat, 0 < m /\ m < N -> ordre_total n m)).
simple induction N; intro.
absurd (0 >= 2).
inversion H.
auto with arith real.
intro X; case (N_classic n); intro.
elim s; intro y.
rewrite y; intro; absurd (1 >= 2); inversion H; inversion H1;
 auto with arith real.
rewrite y; intro; exists 1; split; auto with arith real.
split; auto with arith real.
intros; replace m with 1.
apply tech_total_order.
apply sym_equal; elim H0; intro.
inversion H1; auto with arith real.
intros.
elim (X g); intros.
cut
 ({(frac_part_n_alpha x <= frac_part_n_alpha n)%R} +
  {~ (frac_part_n_alpha x <= frac_part_n_alpha n)%R}).
intro X0; elim X0; intro.
exists x; split.
elim p; intros; auto with arith real.
split.
elim p; intros.
elim H1; intros; auto with arith real.
intros; elim p; intros; elim H2; intros; cut (0 < m /\ m < n \/ m = n).
intro; elim H5; intro.
elim (H4 m H6); auto with arith real.
apply prop_alpha.
rewrite H6; unfold ordre_total in |- *; intro; auto with arith real.
elim H0; intros; cut (0 < m /\ m < n \/ 0 < m /\ m = n).
intro; elim H7; intros.
left; auto with arith real.
elim H8; intros; right; auto with arith real.
cut (0 < m /\ (m < n \/ m = n)).
intro; elim H7; intros; elim H9; intro.
left; auto with arith real.
right; auto with arith real.
split; auto with arith real.
unfold lt in H6; inversion H6; auto with arith real.
exists n; split; auto with arith real.
split; auto with arith real.
intros; cut (0 < m /\ m < n \/ m = n).
intro; elim H1.
intro; elim p; intros; elim H4; intros; unfold ordre_total in |- *; intro.
cut (frac_part_n_alpha x <= frac_part_n_alpha m)%R.
cut (frac_part_n_alpha x > frac_part_n_alpha n)%R.
intros; unfold Rgt in H8; cut (frac_part_n_alpha n < frac_part_n_alpha m)%R.
intro; apply (Rlt_le (frac_part_n_alpha n) (frac_part_n_alpha m) H10).
apply
 (Rlt_le_trans (frac_part_n_alpha n) (frac_part_n_alpha x)
    (frac_part_n_alpha m) H8 H9).
apply (Rnot_le_lt (frac_part_n_alpha x) (frac_part_n_alpha n) b).
elim (H6 m H2).
intro; apply (Rlt_le (frac_part_n_alpha x) (frac_part_n_alpha m) H8).
intro; rewrite H8; unfold Rle in |- *; right; auto with arith real.
apply prop_alpha.
intro; rewrite H2; apply tech_total_order.
elim H0; intros.
cut (0 < m /\ m < n \/ 0 < m /\ m = n).
intro; elim H3; intro.
left; auto with arith real.
elim H4; intros.
right; auto with arith real.
cut (0 < m /\ (m < n \/ m = n)).
intro; elim H3; intros.
elim H5; intro.
left; auto with arith real.
right; auto with arith real.
split; auto with arith real.
unfold lt in H2; inversion H2; auto with arith real.
apply (Rle_dec (frac_part_n_alpha x) (frac_part_n_alpha n)).
Qed.

(**********)
Lemma exist_last :
 forall N : nat,
 N >= 2 ->
 sigT
   (fun n : nat =>
    0 < n /\ n < N /\ (forall m : nat, 0 < m /\ m < N -> ordre_total m n)).
simple induction N; intro.
absurd (0 >= 2).
inversion H.
auto with arith real.
intro X; case (N_classic n); intro.
elim s; intro y.
rewrite y; intro; absurd (1 >= 2); inversion H; inversion H1;
 auto with arith real.
rewrite y; intro; exists 1; split; auto with arith real.
split; auto with arith real.
intros; replace m with 1.
apply tech_total_order.
apply sym_equal; elim H0; intro.
inversion H1; auto with arith real.
intros.
elim (X g); intros.
cut
 ({(frac_part_n_alpha x <= frac_part_n_alpha n)%R} +
  {~ (frac_part_n_alpha x <= frac_part_n_alpha n)%R}).
intro X0; elim X0; intro.
exists n; split; auto with arith real.
split; auto with arith real.
intros; cut (0 < m /\ m < n \/ m = n).
intro; elim H1.
intro; elim p; intros; elim H4; intros; unfold ordre_total in |- *; intro.
cut (frac_part_n_alpha m <= frac_part_n_alpha x)%R.
intro;
 apply
  (Rle_trans (frac_part_n_alpha m) (frac_part_n_alpha x)
     (frac_part_n_alpha n) H8 a).
elim (H6 m H2).
intro; apply (Rlt_le (frac_part_n_alpha m) (frac_part_n_alpha x) H8).
intro; rewrite H8; unfold Rle in |- *; right; auto with arith real.
apply prop_alpha.
intro; rewrite H2; apply tech_total_order.
elim H0; intros.
cut (0 < m /\ m < n \/ 0 < m /\ m = n).
intro; elim H3; intro.
left; auto with arith real.
elim H4; intros.
right; auto with arith real.
cut (0 < m /\ (m < n \/ m = n)).
intro; elim H3; intros.
elim H5; intro.
left; auto with arith real.
right; auto with arith real.
split; auto with arith real.
unfold lt in H2; inversion H2; auto with arith real.
exists x; split.
elim p; intros; auto with arith real.
split.
elim p; intros.
elim H1; intros; auto with arith real.
intros; elim p; intros; elim H2; intros; cut (0 < m /\ m < n \/ m = n).
intro; elim H5; intro.
elim (H4 m H6); auto with arith real.
apply prop_alpha.
rewrite H6; unfold ordre_total in |- *; intro.
cut (frac_part_n_alpha n < frac_part_n_alpha x)%R.
intro; apply (Rlt_le (frac_part_n_alpha n) (frac_part_n_alpha x) H8).
apply (Rnot_le_lt (frac_part_n_alpha x) (frac_part_n_alpha n) b).
elim H0; intros; cut (0 < m /\ m < n \/ 0 < m /\ m = n).
intro; elim H7; intros.
left; auto with arith real.
elim H8; intros; right; auto with arith real.
cut (0 < m /\ (m < n \/ m = n)).
intro; elim H7; intros; elim H9; intro.
left; auto with arith real.
right; auto with arith real.
split; auto with arith real.
unfold lt in H6; inversion H6; auto with arith real.
apply (Rle_dec (frac_part_n_alpha x) (frac_part_n_alpha n)).
Qed.


(**********)
Definition first (N : nat) :=
  match N_classic N with
  | inright p => match exist_first N p return nat with
                 | existT a b => a
                 end
  | _ => 0
  end.

(**********)
Definition last (N : nat) :=
  match N_classic N with
  | inright p => match exist_last N p return nat with
                 | existT a b => a
                 end
  | _ => 0
  end.

(*********************************************************)
(*       Definition of the next point                    *)
(*********************************************************)


Lemma exist_after_M :
 forall M : R,
 (0 <= M)%R ->
 (M < 1)%R ->
 forall N : nat,
 sig
   (fun I : nat =>
    0 < I /\
    I < N /\
    (M < frac_part_n_alpha I)%R /\
    (forall m : nat,
     0 <= m ->
     m < N ->
     (frac_part_n_alpha m > M)%R ->
     (frac_part_n_alpha m >= frac_part_n_alpha I)%R)) +
 {(forall m : nat,
   0 <= m ->
   m < N -> (0 <= frac_part_n_alpha m)%R /\ (frac_part_n_alpha m <= M)%R)}.
simple induction N.
right; intros; absurd (m < 0); auto with arith real.
intros n X; elim X; intro y;
 cut
  ({(0 <= M)%R /\ (M < frac_part_n_alpha n)%R} +
   {(frac_part_n_alpha n <= M)%R /\ (M < 1)%R}).
intro X0; elim y; intros x y0.
left; elim X0; intro y1.
cut
 ({(frac_part_n_alpha n < frac_part_n_alpha x)%R} +
  {(frac_part_n_alpha x <= frac_part_n_alpha n)%R}).
intro X1; elim X1; intro y2.
split with n; split.
elim y1; intros.
generalize (Rle_lt_trans 0 M (frac_part_n_alpha n) H1 H2).
intro; apply neq_O_lt.
cut (0%R <> frac_part_n_alpha n).
intro; unfold frac_part_n_alpha in H4;
 generalize (R0_fp_O (INR n * alpha) H4); intro; generalize (sym_not_eq H5);
 clear H5; intro; generalize (Rmult_neq_0_reg (INR n) alpha H5); 
 intro; elim H6; intros.
apply sym_not_equal.
apply (not_INR_O n); auto with arith real.
apply (Rlt_dichotomy_converse 0 (frac_part_n_alpha n)).
left; assumption.
split; auto with arith real.
split; elim y1; auto with arith real.
intros; cut (0 <= m /\ m < n \/ m = n).
intro; elim H6; intro.
elim H7; intros.
elim y0; intros.
elim H11; intros.
elim H13; intros.
generalize (H15 m H8 H9 H5); intro;
 generalize (Rge_le (frac_part_n_alpha m) (frac_part_n_alpha x) H16); 
 intro;
 generalize
  (Rlt_le_trans (frac_part_n_alpha n) (frac_part_n_alpha x)
     (frac_part_n_alpha m) y2 H17); intro;
 generalize (Rlt_le (frac_part_n_alpha n) (frac_part_n_alpha m) H18); 
 intro; apply (Rle_ge (frac_part_n_alpha n) (frac_part_n_alpha m) H19).
rewrite H7; unfold Rge in |- *; right; auto with arith real.
cut (0 <= m /\ m < n \/ 0 <= m /\ m = n).
intro; elim H6; intros.
left; auto with arith real.
elim H7; intros; right; auto with arith real.
cut (0 <= m /\ (m < n \/ m = n)).
intro; elim H6; intros; elim H8; intro.
left; auto with arith real.
right; auto with arith real.
split; auto with arith real.
unfold lt in H4; inversion H4; auto with arith real.
exists x; elim y0; intros.
split; auto with arith real.
split; elim H2; intros; auto with arith real.
split; elim H4; intros; auto with arith real.
cut (0 <= m /\ m < n \/ m = n).
intro; elim H10; intro.
elim H11; auto with arith real.
rewrite H11; apply Rle_ge; auto with arith real.
cut (0 <= m /\ m < n \/ 0 <= m /\ m = n).
intro; elim H10; intros.
left; auto with arith real.
elim H11; intros; right; auto with arith real.
cut (0 <= m /\ (m < n \/ m = n)).
intro; elim H10; intros; elim H12; intro.
left; auto with arith real.
right; auto with arith real.
split; auto with arith real.
unfold lt in H8; inversion H8; auto with arith real.
generalize (Rle_dec (frac_part_n_alpha x) (frac_part_n_alpha n)); intro X1;
 elim X1; intro y2.
right; auto with arith real.
left; generalize (Rnot_le_lt (frac_part_n_alpha x) (frac_part_n_alpha n) y2);
 unfold Rgt in |- *; auto with arith real.
exists x; elim y0; intros.
split; auto with arith real.
split; elim H2; intros; auto with arith real.
split; elim H4; intros; auto with arith real.
cut (0 <= m /\ m < n \/ m = n).
intro; elim H10; intro.
elim H11; intros.
apply (H6 m H7 H13 H9).
elim y1; intros; rewrite H11 in H9; absurd (frac_part_n_alpha n > M)%R.
inversion H12.
unfold Rgt in |- *; apply (Rlt_asym (frac_part_n_alpha n) M);
 auto with arith real.
rewrite H14; unfold Rgt in |- *; apply Rlt_irrefl.
auto with arith real.
cut (0 <= m /\ m < n \/ 0 <= m /\ m = n).
intro; elim H10; intros.
left; auto with arith real.
elim H11; intros; right; auto with arith real.
cut (0 <= m /\ (m < n \/ m = n)).
intro; elim H10; intros; elim H12; intro.
left; auto with arith real.
right; auto with arith real.
split; auto with arith real.
unfold lt in H8; inversion H8; auto with arith real.
apply (inser_trans_R 0 M 1 (frac_part_n_alpha n)); auto with arith real.
intro X0; elim X0; intro y0.
left; exists n; split.
elim y0; intros.
generalize (Rle_lt_trans 0 M (frac_part_n_alpha n) H1 H2).
intro; apply neq_O_lt.
cut (0%R <> frac_part_n_alpha n).
intro; unfold frac_part_n_alpha in H4;
 generalize (R0_fp_O (INR n * alpha) H4); intro; generalize (sym_not_eq H5);
 clear H5; intro; generalize (Rmult_neq_0_reg (INR n) alpha H5); 
 intro; elim H6; intros.
apply sym_not_equal.
apply (not_INR_O n); auto with arith real.
apply (Rlt_dichotomy_converse 0 (frac_part_n_alpha n)).
left; assumption.
split; auto with arith real.
split; elim y0; auto with arith real.
intros; cut (0 <= m /\ m < n \/ m = n).
intro; elim H6; intro.
elim H7; intros.
absurd (frac_part_n_alpha m > M)%R.
generalize (y m H8 H9); intro; elim H10; intros.
inversion H12.
unfold Rgt in |- *; apply (Rlt_asym (frac_part_n_alpha m) M);
 auto with arith real.
rewrite H13; unfold Rgt in |- *; apply Rlt_irrefl.
auto with arith real.
rewrite H7; unfold Rge in |- *; right; auto with arith real.
cut (0 <= m /\ m < n \/ 0 <= m /\ m = n).
intro; elim H6; intros.
left; auto with arith real.
elim H7; intros; right; auto with arith real.
cut (0 <= m /\ (m < n \/ m = n)).
intro; elim H6; intros; elim H8; intro.
left; auto with arith real.
right; auto with arith real.
split; auto with arith real.
unfold lt in H4; inversion H4; auto with arith real.
right; intros; cut (0 <= m /\ m < n \/ m = n).
intro; elim H3; intro.
elim H4; intros.
apply (y m H5 H6).
split.
unfold frac_part_n_alpha in |- *; generalize (base_fp (INR m * alpha)); intro;
 elim H5; intros.
apply (Rge_le (frac_part (INR m * alpha)) 0 H6).
rewrite H4; elim y0; auto with arith real.
cut (0 <= m /\ m < n \/ 0 <= m /\ m = n).
intro; elim H3; intros.
left; auto with arith real.
elim H4; intros; right; auto with arith real.
cut (0 <= m /\ (m < n \/ m = n)).
intro; elim H3; intros; elim H5; intro.
left; auto with arith real.
right; auto with arith real.
split; auto with arith real.
unfold lt in H2; inversion H2; auto with arith real.
apply (inser_trans_R 0 M 1 (frac_part_n_alpha n)); auto with arith real.
Qed.

(**********)
Lemma P1 : forall n : nat, (0 <= frac_part_n_alpha n)%R.
intro; unfold frac_part_n_alpha in |- *; elim (base_fp (INR n * alpha));
 intros; apply (Rge_le (frac_part (INR n * alpha)) 0 H).
Qed.

(**********)
Lemma P2 : forall n : nat, (frac_part_n_alpha n < 1)%R.
intro; unfold frac_part_n_alpha in |- *; elim (base_fp (INR n * alpha));
 auto with arith real.
Qed.

(**********)
Definition after (N n : nat) :=
  match exist_after_M (frac_part_n_alpha n) (P1 n) (P2 n) N with
  | inleft p => match p return nat with
                | exist a b => a
                end
  | _ => 0
  end.










