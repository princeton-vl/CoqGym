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
(*                               prop_fl.v                                  *)
(****************************************************************************)

(*********************************************************)
(*              Properties first last after              *)
(*                                                       *)
(*********************************************************)

Require Export prop_elem.
Require Export Classical_Prop.

Unset Standard Proposition Elimination Names.

(*********************************************************)

Section theoreme.
Hypothesis alpha_irr : forall n p : Z, (alpha * IZR p)%R <> IZR n.
Hypothesis prop_alpha : (0 < alpha)%R /\ (alpha < 1)%R.
Hypothesis prop_N : forall N : nat, N >= 2.

(**********)
Lemma tech_fp_alp_irr :
 forall n m : nat, frac_part_n_alpha n = frac_part_n_alpha m -> n = m.
intros;
 generalize (Rminus_diag_eq (frac_part_n_alpha n) (frac_part_n_alpha m) H);
 unfold frac_part_n_alpha in |- *;
 elim (Rminus_fp1 (INR n * alpha) (INR m * alpha)).
unfold Rminus in |- *; rewrite <- Ropp_mult_distr_l_reverse;
 rewrite (Rmult_comm (INR n) alpha); rewrite (Rmult_comm (- INR m) alpha);
 rewrite <- Rmult_plus_distr_l; intro;
 elim (fp_nat (alpha * (INR n + - INR m)) H0); intros;
 fold (INR n - INR m)%R in H1; rewrite (INR_IZR_INZ n) in H1;
 rewrite (INR_IZR_INZ m) in H1;
 rewrite (Z_R_minus (Z_of_nat n) (Z_of_nat m)) in H1;
 generalize (alpha_irr x (Z_of_nat n - Z_of_nat m)); 
 intro; elimtype False; auto.
unfold Rge in |- *; auto.
Qed.

(**********)
Lemma fp_first_R0 : forall N : nat, (frac_part_n_alpha (first N) > 0)%R.
intro; generalize (P1 (first N)); intro; unfold Rle in H; unfold Rgt in |- *;
 elim H; intro; auto; clear H; rewrite <- fp_R0 in H0;
 rewrite <- (Rmult_0_l alpha) in H0; cut (INR 0 = 0%R).
intro; rewrite <- H in H0;
 cut (frac_part (INR 0 * alpha) = frac_part_n_alpha 0).
intro; rewrite H1 in H0; generalize (tech_fp_alp_irr 0 (first N) H0); intro;
 generalize (first_0 N (prop_N N)); intro;
 generalize (lt_not_eq 0 (first N) H3); intro; elimtype False; 
 auto.
unfold frac_part_n_alpha in |- *; auto.
auto.
Qed.

(**********)
Lemma contra_tech_fp_alp_irr :
 forall n m : nat, n <> m -> frac_part_n_alpha n <> frac_part_n_alpha m.
intros; generalize (tech_fp_alp_irr n m); tauto.
Qed.

(**********)
Lemma contradiction1 :
 forall N k : nat,
 N <= k ->
 k < first N + last N ->
 (frac_part_n_alpha k < frac_part_n_alpha (first N))%R \/
 (frac_part_n_alpha k > frac_part_n_alpha (last N))%R -> False.
intros; elim H1; intro; clear H1.
cut
 ((frac_part_n_alpha (last N) -
   (frac_part_n_alpha k - frac_part_n_alpha (first N) + 1))%R = 0%R).
unfold frac_part_n_alpha in |- *;
 rewrite <- (Rminus_fp2 (INR k * alpha) (INR (first N) * alpha) H2);
 generalize
  (Rminus_fp1 (INR (last N) * alpha) (INR k * alpha - INR (first N) * alpha));
 intros;
 cut
  (frac_part (INR (last N) * alpha) >=
   frac_part (INR k * alpha - INR (first N) * alpha))%R.
intro; rewrite <- (H1 H4) in H3; clear H1 H4;
 elim
  (fp_nat (INR (last N) * alpha - (INR k * alpha - INR (first N) * alpha)) H3).
unfold Rminus in |- *;
 rewrite <- (Ropp_mult_distr_l_reverse (INR (first N)) alpha);
 rewrite (Ropp_plus_distr (INR k * alpha) (- INR (first N) * alpha));
 rewrite <- (Ropp_mult_distr_l_reverse (INR k) alpha);
 rewrite <- (Ropp_mult_distr_l_reverse (- INR (first N)) alpha);
 rewrite (Ropp_involutive (INR (first N)));
 rewrite (Rmult_comm (- INR k) alpha);
 rewrite (Rmult_comm (INR (first N)) alpha);
 rewrite (Rmult_comm (INR (last N)) alpha);
 rewrite <- (Rmult_plus_distr_l alpha (- INR k) (INR (first N)));
 rewrite <-
  (Rmult_plus_distr_l alpha (INR (last N)) (- INR k + INR (first N)))
  ; rewrite (Rplus_comm (- INR k) (INR (first N)));
 rewrite <- (Rplus_assoc (INR (last N)) (INR (first N)) (- INR k));
 fold (INR (last N) + INR (first N) - INR k)%R in |- *;
 rewrite <- (plus_INR (last N) (first N));
 rewrite (INR_IZR_INZ (last N + first N)).
rewrite (INR_IZR_INZ k).
rewrite (Z_R_minus (Z_of_nat (last N + first N)) (Z_of_nat k)).
intros.
generalize (alpha_irr x (Z_of_nat (last N + first N) - Z_of_nat k)).
intro.
auto.
unfold Rge in |- *; right; apply Rminus_diag_uniq; auto.
cut
 ((frac_part_n_alpha k - frac_part_n_alpha (first N) + 1 <=
   frac_part_n_alpha (last N))%R /\
  (frac_part_n_alpha k - frac_part_n_alpha (last N) + 1 >=
   frac_part_n_alpha (first N))%R).
intro; elim H1; intros; clear H1.
generalize
 (Rle_minus (frac_part_n_alpha k - frac_part_n_alpha (first N) + 1)
    (frac_part_n_alpha (last N)) H3);
 generalize
  (Rge_minus (frac_part_n_alpha k - frac_part_n_alpha (last N) + 1)
     (frac_part_n_alpha (first N)) H4); intros; clear H3 H4;
 generalize
  (Rge_le
     (frac_part_n_alpha k - frac_part_n_alpha (last N) + 1 -
      frac_part_n_alpha (first N)) 0 H1); intro; clear H1;
 rewrite <- Ropp_minus_distr; rewrite <- Ropp_0; apply Ropp_eq_compat.
unfold Rminus in H3;
 rewrite (Rplus_comm (frac_part_n_alpha k) (- frac_part_n_alpha (last N)))
   in H3;
 rewrite (Rplus_assoc (- frac_part_n_alpha (last N)) (frac_part_n_alpha k) 1)
   in H3.
rewrite
 (Rplus_assoc (- frac_part_n_alpha (last N)) (frac_part_n_alpha k + 1)
    (- frac_part_n_alpha (first N))) in H3;
 rewrite
  (Rplus_comm (- frac_part_n_alpha (last N))
     (frac_part_n_alpha k + 1 + - frac_part_n_alpha (first N)))
   in H3;
 rewrite
  (Rplus_assoc (frac_part_n_alpha k) 1 (- frac_part_n_alpha (first N)))
   in H3; rewrite (Rplus_comm 1 (- frac_part_n_alpha (first N))) in H3;
 rewrite <-
  (Rplus_assoc (frac_part_n_alpha k) (- frac_part_n_alpha (first N)) 1)
   in H3; fold (frac_part_n_alpha k - frac_part_n_alpha (first N))%R in H3;
 fold
  (frac_part_n_alpha k - frac_part_n_alpha (first N) + 1 -
   frac_part_n_alpha (last N))%R in H3;
 elim
  (Rle_le_eq
     (frac_part_n_alpha k - frac_part_n_alpha (first N) + 1 -
      frac_part_n_alpha (last N)) 0); auto.
split; unfold frac_part_n_alpha in |- *.
unfold frac_part_n_alpha in H2;
 rewrite <- (Rminus_fp2 (INR k * alpha) (INR (first N) * alpha) H2);
 elim (tech_first_last N (k - first N) (prop_N N)).
intros; unfold ordre_total in H3; unfold frac_part_n_alpha in H3;
 cut (first N <= k).
intro; rewrite (minus_INR k (first N) H4) in H3; unfold Rminus in H3;
 rewrite (Rmult_comm (INR k + - INR (first N)) alpha) in H3;
 rewrite (Rmult_plus_distr_l alpha (INR k) (- INR (first N))) in H3;
 rewrite (Rmult_comm alpha (- INR (first N))) in H3;
 rewrite (Ropp_mult_distr_l_reverse (INR (first N)) alpha) in H3;
 fold (alpha * INR k - INR (first N) * alpha)%R in H3;
 rewrite (Rmult_comm alpha (INR k)) in H3; auto.
generalize (first_N01 N); intro; apply (le_trans (first N) N k H4 H).
elim (lt_minus2 (first N) k); auto.
generalize (first_N N (prop_N N)); intro. 
apply (lt_le_trans (first N) N k H1 H).
cut (k - first N < last N).
generalize (last_N01 N); intros;
 apply (lt_le_trans (k - first N) (last N) N H3 H1).
apply (lt_plus_minus k (first N) (last N)).
generalize (first_N N (prop_N N)); intro;
 apply (lt_le_trans (first N) N k H1 H).
assumption.
cut (frac_part_n_alpha k < frac_part_n_alpha (last N))%R.
intro; unfold frac_part_n_alpha in H1;
 rewrite <- (Rminus_fp2 (INR k * alpha) (INR (last N) * alpha) H1);
 elim (tech_first_last N (k - last N) (prop_N N)).
intros; unfold ordre_total in H3; unfold frac_part_n_alpha in H3;
 cut (last N <= k).
intro; rewrite (minus_INR k (last N) H5) in H3; unfold Rminus in H3;
 rewrite (Rmult_comm (INR k + - INR (last N)) alpha) in H3;
 rewrite (Rmult_plus_distr_l alpha (INR k) (- INR (last N))) in H3;
 rewrite (Rmult_comm alpha (- INR (last N))) in H3;
 rewrite (Ropp_mult_distr_l_reverse (INR (last N)) alpha) in H3;
 fold (alpha * INR k - INR (last N) * alpha)%R in H3;
 rewrite (Rmult_comm alpha (INR k)) in H3;
 apply
  (Rle_ge (frac_part (INR (first N) * alpha))
     (frac_part (INR k * alpha - INR (last N) * alpha)) 
     (H3 prop_alpha)).
generalize (last_N01 N); intro; apply (le_trans (last N) N k H5 H).
elim (lt_minus2 (last N) k); auto.
generalize (last_N N (prop_N N)); intro.
apply (lt_le_trans (last N) N k H3 H).
cut (k - last N < first N).
generalize (first_N01 N); intros;
 apply (lt_le_trans (k - last N) (first N) N H4 H3).
apply (lt_plus_minus k (last N) (first N)).
generalize (last_N N (prop_N N)); intro;
 apply (lt_le_trans (last N) N k H3 H).
rewrite plus_comm; assumption.
generalize (le_first_last N (prop_N N)); unfold ordre_total in |- *; intros;
 apply
  (Rlt_le_trans (frac_part_n_alpha k) (frac_part_n_alpha (first N))
     (frac_part_n_alpha (last N)) H2 (H1 prop_alpha)).
(***)
cut
 ((frac_part_n_alpha (last N) -
   (frac_part_n_alpha k - frac_part_n_alpha (first N)))%R = 0%R).
cut (frac_part_n_alpha k >= frac_part_n_alpha (first N))%R.
unfold frac_part_n_alpha in |- *; intro;
 rewrite <- (Rminus_fp1 (INR k * alpha) (INR (first N) * alpha) H1);
 generalize
  (Rminus_fp1 (INR (last N) * alpha) (INR k * alpha - INR (first N) * alpha));
 intros;
 cut
  (frac_part (INR (last N) * alpha) >=
   frac_part (INR k * alpha - INR (first N) * alpha))%R.
intro; rewrite <- (H3 H5) in H4; clear H3 H5;
 elim
  (fp_nat (INR (last N) * alpha - (INR k * alpha - INR (first N) * alpha)) H4).
unfold Rminus in |- *;
 rewrite <- (Ropp_mult_distr_l_reverse (INR (first N)) alpha);
 rewrite (Ropp_plus_distr (INR k * alpha) (- INR (first N) * alpha));
 rewrite <- (Ropp_mult_distr_l_reverse (INR k) alpha);
 rewrite <- (Ropp_mult_distr_l_reverse (- INR (first N)) alpha);
 rewrite (Ropp_involutive (INR (first N)));
 rewrite (Rmult_comm (- INR k) alpha);
 rewrite (Rmult_comm (INR (first N)) alpha);
 rewrite (Rmult_comm (INR (last N)) alpha);
 rewrite <- (Rmult_plus_distr_l alpha (- INR k) (INR (first N)));
 rewrite <-
  (Rmult_plus_distr_l alpha (INR (last N)) (- INR k + INR (first N)))
  ; rewrite (Rplus_comm (- INR k) (INR (first N)));
 rewrite <- (Rplus_assoc (INR (last N)) (INR (first N)) (- INR k));
 fold (INR (last N) + INR (first N) - INR k)%R in |- *;
 rewrite <- (plus_INR (last N) (first N)).
rewrite (INR_IZR_INZ (last N + first N)).
rewrite (INR_IZR_INZ k).
rewrite (Z_R_minus (Z_of_nat (last N + first N)) (Z_of_nat k)).
intros.
generalize (alpha_irr x (Z_of_nat (last N + first N) - Z_of_nat k)).
intro.
auto.
unfold Rge in |- *; right; apply Rminus_diag_uniq; auto.
generalize (le_first_last N (prop_N N)); unfold ordre_total in |- *; intros;
 unfold Rgt in H2; cut (frac_part_n_alpha (first N) <= frac_part_n_alpha k)%R.
intro; apply (Rle_ge (frac_part_n_alpha (first N)) (frac_part_n_alpha k) H3).
cut (frac_part_n_alpha (first N) < frac_part_n_alpha k)%R.
intro; apply (Rlt_le (frac_part_n_alpha (first N)) (frac_part_n_alpha k) H3).
apply
 (Rle_lt_trans (frac_part_n_alpha (first N)) (frac_part_n_alpha (last N))
    (frac_part_n_alpha k) (H1 prop_alpha) H2).
cut
 ((frac_part_n_alpha k - frac_part_n_alpha (first N) <=
   frac_part_n_alpha (last N))%R /\
  (frac_part_n_alpha k - frac_part_n_alpha (last N) >=
   frac_part_n_alpha (first N))%R).
intro; elim H1; intros; clear H1.
generalize
 (Rle_minus (frac_part_n_alpha k - frac_part_n_alpha (first N))
    (frac_part_n_alpha (last N)) H3);
 generalize
  (Rge_minus (frac_part_n_alpha k - frac_part_n_alpha (last N))
     (frac_part_n_alpha (first N)) H4); intros; clear H3 H4;
 generalize
  (Rge_le
     (frac_part_n_alpha k - frac_part_n_alpha (last N) -
      frac_part_n_alpha (first N)) 0 H1); intro; clear H1;
 rewrite <- Ropp_minus_distr; rewrite <- Ropp_0; apply Ropp_eq_compat.
unfold Rminus in H3;
 rewrite
  (Rplus_assoc (frac_part_n_alpha k) (- frac_part_n_alpha (last N))
     (- frac_part_n_alpha (first N))) in H3;
 rewrite
  (Rplus_comm (- frac_part_n_alpha (last N)) (- frac_part_n_alpha (first N)))
   in H3;
 rewrite <-
  (Rplus_assoc (frac_part_n_alpha k) (- frac_part_n_alpha (first N))
     (- frac_part_n_alpha (last N))) in H3;
 fold (frac_part_n_alpha k - frac_part_n_alpha (first N))%R in H3;
 fold
  (frac_part_n_alpha k - frac_part_n_alpha (first N) -
   frac_part_n_alpha (last N))%R in H3;
 elim
  (Rle_le_eq
     (frac_part_n_alpha k - frac_part_n_alpha (first N) -
      frac_part_n_alpha (last N)) 0); auto.
split.
cut (frac_part_n_alpha k >= frac_part_n_alpha (first N))%R.
unfold frac_part_n_alpha in |- *; intro;
 rewrite <- (Rminus_fp1 (INR k * alpha) (INR (first N) * alpha) H1);
 elim (tech_first_last N (k - first N) (prop_N N)).
intros; unfold ordre_total in H4; unfold frac_part_n_alpha in H4;
 cut (first N <= k).
intro; rewrite (minus_INR k (first N) H5) in H4; unfold Rminus in H4;
 rewrite (Rmult_comm (INR k + - INR (first N)) alpha) in H4;
 rewrite (Rmult_plus_distr_l alpha (INR k) (- INR (first N))) in H4;
 rewrite (Rmult_comm alpha (- INR (first N))) in H4;
 rewrite (Ropp_mult_distr_l_reverse (INR (first N)) alpha) in H4;
 fold (alpha * INR k - INR (first N) * alpha)%R in H4;
 rewrite (Rmult_comm alpha (INR k)) in H4; auto.
generalize (first_N01 N); intro; apply (le_trans (first N) N k H5 H).
elim (lt_minus2 (first N) k); auto.
generalize (first_N N (prop_N N)); intro.
apply (lt_le_trans (first N) N k H3 H).
cut (k - first N < last N).
generalize (last_N01 N); intros;
 apply (lt_le_trans (k - first N) (last N) N H4 H3).
apply (lt_plus_minus k (first N) (last N)).
generalize (first_N N (prop_N N)); intro;
 apply (lt_le_trans (first N) N k H3 H).
assumption.
unfold frac_part_n_alpha in |- *; generalize (le_first_last N (prop_N N));
 unfold ordre_total in |- *; intros; unfold Rgt in H2;
 cut (frac_part_n_alpha (first N) <= frac_part_n_alpha k)%R.
intro; apply (Rle_ge (frac_part_n_alpha (first N)) (frac_part_n_alpha k) H3).
cut (frac_part_n_alpha (first N) < frac_part_n_alpha k)%R.
intro; apply (Rlt_le (frac_part_n_alpha (first N)) (frac_part_n_alpha k) H3).
apply
 (Rle_lt_trans (frac_part_n_alpha (first N)) (frac_part_n_alpha (last N))
    (frac_part_n_alpha k) (H1 prop_alpha) H2).
cut (frac_part_n_alpha k >= frac_part_n_alpha (last N))%R.
unfold frac_part_n_alpha in |- *; intro;
 rewrite <- (Rminus_fp1 (INR k * alpha) (INR (last N) * alpha) H1);
 elim (tech_first_last N (k - last N) (prop_N N)).
intros; unfold ordre_total in H3; unfold frac_part_n_alpha in H3;
 cut (last N <= k).
intro; rewrite (minus_INR k (last N) H5) in H3; unfold Rminus in H3;
 rewrite (Rmult_comm (INR k + - INR (last N)) alpha) in H3;
 rewrite (Rmult_plus_distr_l alpha (INR k) (- INR (last N))) in H3;
 rewrite (Rmult_comm alpha (- INR (last N))) in H3;
 rewrite (Ropp_mult_distr_l_reverse (INR (last N)) alpha) in H3;
 fold (alpha * INR k - INR (last N) * alpha)%R in H3;
 rewrite (Rmult_comm alpha (INR k)) in H3;
 apply
  (Rle_ge (frac_part (INR (first N) * alpha))
     (frac_part (INR k * alpha - INR (last N) * alpha)) 
     (H3 prop_alpha)).
generalize (last_N01 N); intro; apply (le_trans (last N) N k H5 H).
elim (lt_minus2 (last N) k); auto.
generalize (last_N N (prop_N N)); intro.
apply (lt_le_trans (last N) N k H3 H).
cut (k - last N < first N).
generalize (first_N01 N); intros;
 apply (lt_le_trans (k - last N) (first N) N H4 H3).
apply (lt_plus_minus k (last N) (first N)).
generalize (last_N N (prop_N N)); intro;
 apply (lt_le_trans (last N) N k H3 H).
rewrite plus_comm; assumption.
apply Rgt_ge; auto.
Qed.

(**********)
Lemma absurd1 :
 forall N k : nat,
 N <= k ->
 k < first N + last N ->
 (frac_part_n_alpha k >= frac_part_n_alpha (first N))%R /\
 (frac_part_n_alpha k <= frac_part_n_alpha (last N))%R.
intros; generalize (contradiction1 N k H H0); intro;
 cut
  (~ (frac_part_n_alpha k < frac_part_n_alpha (first N))%R /\
   ~ (frac_part_n_alpha k > frac_part_n_alpha (last N))%R).
intro; elim H2; intros; split.
apply (Rnot_lt_ge (frac_part_n_alpha k) (frac_part_n_alpha (first N)) H3).
apply (Rnot_gt_le (frac_part_n_alpha k) (frac_part_n_alpha (last N)) H4).
apply
 (not_or_and (frac_part_n_alpha k < frac_part_n_alpha (first N))%R
    (frac_part_n_alpha k > frac_part_n_alpha (last N))%R H1).
Qed.

(**********)
Lemma absurd_first :
 forall N k : nat,
 0 < k ->
 k < first N + last N ->
 (frac_part_n_alpha (first N) <= frac_part_n_alpha k)%R.
intros; elim inser_trans_lt with 0 k (first N + last N) N.
intro y; elim y; intros; apply (first_n N k (prop_N N) H1 H2 prop_alpha).
intro y; elim y; intros.
elim (absurd1 N k H1 H2); intros.
unfold Rge in H3; unfold Rle in |- *; unfold Rgt in H3; elim H3; intro.
left; assumption.
right; auto.
auto.
Qed.

(**********)
Lemma absurd_last :
 forall N k : nat,
 0 < k ->
 k < first N + last N ->
 (frac_part_n_alpha k <= frac_part_n_alpha (last N))%R.
intros; elim inser_trans_lt with 0 k (first N + last N) N.
intro y; elim y; intros; apply (last_n N k (prop_N N) H1 H2 prop_alpha).
intro y; elim y; intros.
elim (absurd1 N k H1 H2); intros; auto.
auto.
Qed.

(**********)
Lemma tech_first_aux :
 forall N a : nat,
 0 < a ->
 a < N ->
 ((forall b : nat,
   0 < b -> b < N -> (frac_part_n_alpha a <= frac_part_n_alpha b)%R) <->
  a = first N).
intros; split; intro.
cut (frac_part_n_alpha a = frac_part_n_alpha (first N)).
intro; apply (tech_fp_alp_irr a (first N) H2).
elim (Rle_le_eq (frac_part_n_alpha a) (frac_part_n_alpha (first N))); intros;
 clear H3;
 generalize (H1 (first N) (first_0 N (prop_N N)) (first_N N (prop_N N)));
 generalize (first_n N a (prop_N N) H H0 prop_alpha); 
 intros; apply H2.
split; auto.
intros; rewrite H1; apply (first_n N b (prop_N N) H2 H3 prop_alpha).
Qed.

(**********)
Lemma eq_first_M_N :
 forall N M : nat,
 M = first N + last N ->
 ((forall b : nat,
   0 < b -> b < M -> (frac_part_n_alpha (first N) <= frac_part_n_alpha b)%R) <->
  first N = first M).
intros; split; intro.
elim (tech_first_aux M (first N) (first_0 N (prop_N N))).
intros; clear H2; auto.
rewrite H; apply (lt_plus (first N) (last N) (last_0 N (prop_N N))).
elim
 (tech_first_aux M (first M) (first_0 M (prop_N M)) (first_N M (prop_N M))).
intros; clear H1; rewrite H0; auto.
Qed.

(**********)
Lemma first_eq_M_N :
 forall N M : nat, M = first N + last N -> first N = first M. 
intros; elim (eq_first_M_N N M H); intros; clear H1; apply H0.
intros; rewrite H in H2; apply (absurd_first N b H1 H2).
Qed.

(**********)
Lemma tech_last_aux :
 forall N a : nat,
 0 < a ->
 a < N ->
 ((forall b : nat,
   0 < b -> b < N -> (frac_part_n_alpha b <= frac_part_n_alpha a)%R) <->
  a = last N).
intros; split; intro.
cut (frac_part_n_alpha a = frac_part_n_alpha (last N)).
intro; apply (tech_fp_alp_irr a (last N) H2).
elim (Rle_le_eq (frac_part_n_alpha a) (frac_part_n_alpha (last N))); intros;
 clear H3;
 generalize (H1 (last N) (last_0 N (prop_N N)) (last_N N (prop_N N)));
 generalize (last_n N a (prop_N N) H H0 prop_alpha); 
 intros; apply H2.
split; auto.
intros; rewrite H1; apply (last_n N b (prop_N N) H2 H3 prop_alpha).
Qed.

(**********)
Lemma eq_last_M_N :
 forall N M : nat,
 M = first N + last N ->
 ((forall b : nat,
   0 < b -> b < M -> (frac_part_n_alpha b <= frac_part_n_alpha (last N))%R) <->
  last N = last M).
intros; split; intro.
elim (tech_last_aux M (last N) (last_0 N (prop_N N))).
intros; clear H2; auto.
rewrite H; rewrite plus_comm;
 apply (lt_plus (last N) (first N) (first_0 N (prop_N N))).
elim (tech_last_aux M (last M) (last_0 M (prop_N M)) (last_N M (prop_N M))).
intros; clear H1; rewrite H0; auto.
Qed.

(**********)
Lemma last_eq_M_N : forall N M : nat, M = first N + last N -> last N = last M. 
intros; elim (eq_last_M_N N M H); intros; clear H1; apply H0.
intros; rewrite H in H2; apply (absurd_last N b H1 H2).
Qed.

(**********)
Lemma tech_after :
 forall N n m : nat,
 0 < n ->
 n < N ->
 0 <= m ->
 m < N ->
 (frac_part_n_alpha n < frac_part_n_alpha m)%R ->
 ((exists k : nat,
     0 < k /\
     k < N /\
     (frac_part_n_alpha n < frac_part_n_alpha k)%R /\
     (frac_part_n_alpha k < frac_part_n_alpha m)%R) -> False) ->
 m = after N n.
intros; unfold after in |- *.
case (exist_after_M (frac_part_n_alpha n) (P1 n) (P2 n) N); intro.
elim s; intros x y.
elim y; intros.
clear s y.
elim H6; intros; clear H6.
elim H8; intros; clear H8.
generalize
 (tech_not_exist_pt (fun k : nat => 0 < k) (fun k : nat => k < N)
    (fun k : nat => (frac_part_n_alpha n < frac_part_n_alpha k)%R)
    (fun k : nat => (frac_part_n_alpha k < frac_part_n_alpha m)%R) H4);
 clear H4; intro.
elim (H4 x H5 H7); intro.
absurd (frac_part_n_alpha n < frac_part_n_alpha x)%R; auto.
unfold Rgt in H9; generalize (H9 m H1 H2 H3); intro;
 generalize (Rnot_lt_ge (frac_part_n_alpha x) (frac_part_n_alpha m) H8);
 intro;
 generalize (Rge_antisym (frac_part_n_alpha m) (frac_part_n_alpha x) H10 H11);
 intro; apply (tech_fp_alp_irr m x H12).
elim (a m H1 H2); intros; unfold Rle in H6; elim H6; intro.
generalize (Rlt_asym (frac_part_n_alpha m) (frac_part_n_alpha n) H7); intro;
 elimtype False; auto.
cut
 ((frac_part_n_alpha n < frac_part_n_alpha m)%R \/
  (frac_part_n_alpha n > frac_part_n_alpha m)%R).
intro;
 generalize
  (Rlt_dichotomy_converse (frac_part_n_alpha n) (frac_part_n_alpha m) H8);
 intro; elimtype False; auto.
left; auto.
Qed.

(**********)
Lemma prop_after :
 forall N n m : nat,
 after N n = m ->
 (exists k : nat,
    0 < k /\
    k < N /\
    (frac_part_n_alpha n < frac_part_n_alpha k)%R /\
    (frac_part_n_alpha k < frac_part_n_alpha m)%R) -> False. 
intros; elim H0; intros; elim H1; intros; elim H3; intros; elim H5; intro;
 clear H0 H1 H3 H5; rewrite <- H; unfold after in |- *;
 case (exist_after_M (frac_part_n_alpha n) (P1 n) (P2 n) N); 
 intro.
elim s; intros x0 y H0; elim y; intros; elim H3; intros; elim H7; intros;
 clear s y H3 H7; fold (frac_part_n_alpha x > frac_part_n_alpha n)%R in H6;
 generalize (H9 x (lt_le_weak 0 x H2) H4 H6); intro;
 generalize (Rgt_not_le (frac_part_n_alpha x0) (frac_part_n_alpha x) H0);
 intro; cut (frac_part_n_alpha x0 <= frac_part_n_alpha x)%R.
intro; auto.
unfold Rge in H3; unfold Rle in |- *; elim H3; auto.
unfold frac_part_n_alpha in |- *; simpl in |- *; rewrite (Rmult_0_l alpha);
 rewrite fp_R0; elim (base_fp (INR x * alpha)); intros;
 generalize (Rgt_not_le 0 (frac_part (INR x * alpha)) H3); 
 intro; cut (0 <= frac_part (INR x * alpha))%R.
intro; auto.
unfold Rge in H0; unfold Rle in |- *; elim H0; auto.
Qed.

(**********)
Lemma tech_after_lt :
 forall N n m : nat,
 0 < n ->
 n < N ->
 m <> 0 -> after N n = m -> (frac_part_n_alpha n < frac_part_n_alpha m)%R.
intros; rewrite <- H2; unfold after in |- *;
 case (exist_after_M (frac_part_n_alpha n) (P1 n) (P2 n) N); 
 intros.
elim s; intros x y.
elim y; intros; clear y.
elim H4; intros; clear H4.
elim H6; intros; clear H6; auto.
cut (after N n = 0).
intro; rewrite H2 in H3; elimtype False; auto.
unfold after in |- *;
 case (exist_after_M (frac_part_n_alpha n) (P1 n) (P2 n) N); 
 intros; auto.
elim s; intros x y.
elim y; intros; clear y.
elim H4; intros; clear H4.
elim H6; intros; clear H6; clear s.
generalize (lt_le_weak 0 x H3); intro.
elim (a x H6 H5); intros.
unfold Rle in H9; elim H9; intro; clear H9.
generalize (Rlt_asym (frac_part_n_alpha n) (frac_part_n_alpha x) H4); intro;
 elimtype False; auto.
generalize (sym_eq H10); intro; clear H10.
cut
 ((frac_part_n_alpha n < frac_part_n_alpha x)%R \/
  (frac_part_n_alpha n > frac_part_n_alpha x)%R); auto.
intro;
 generalize
  (Rlt_dichotomy_converse (frac_part_n_alpha n) (frac_part_n_alpha x) H10);
 intro; elimtype False; auto.
Qed.

(**********)
Lemma after_last : forall N : nat, after N (last N) = 0.
unfold after in |- *; intro;
 case
  (exist_after_M (frac_part_n_alpha (last N)) (P1 (last N)) (P2 (last N)) N);
 auto.
intro; elim s; intros x y; elim y; intros; elim H0; intros; elim H2; intros;
 clear s y H0 H2 H4; generalize (last_n N x (prop_N N) H H1 prop_alpha);
 intro;
 generalize
  (Rgt_not_le (frac_part_n_alpha x) (frac_part_n_alpha (last N)) H3); 
 intro; elimtype False; auto.
Qed.

(**********)
Lemma prop_M :
 forall N M : nat,
 M = first N + last N ->
 (frac_part_n_alpha M < frac_part_n_alpha (first N))%R \/
 (frac_part_n_alpha M > frac_part_n_alpha (last N))%R.
intros; rewrite H;
 cut
  ((frac_part_n_alpha (first N) + frac_part_n_alpha (last N) < 1)%R \/
   (frac_part_n_alpha (first N) + frac_part_n_alpha (last N) >= 1)%R).
intros; elim H0; intro; clear H0.
right; unfold frac_part_n_alpha in H1; unfold frac_part_n_alpha in |- *;
 rewrite (plus_INR (first N) (last N));
 rewrite (Rmult_comm (INR (first N) + INR (last N)) alpha);
 rewrite (Rmult_plus_distr_l alpha (INR (first N)) (INR (last N)));
 rewrite (Rmult_comm (INR (first N)) alpha) in H1;
 rewrite (Rmult_comm (INR (last N)) alpha) in H1;
 rewrite (Rmult_comm (INR (last N)) alpha);
 rewrite (plus_frac_part2 (alpha * INR (first N)) (alpha * INR (last N)) H1);
 elim (Rplus_ne (alpha * INR (last N))); intros; clear H0;
 pattern (alpha * INR (last N))%R at 2 in |- *; rewrite <- H2;
 rewrite
  (Rplus_comm (frac_part (alpha * INR (first N)))
     (frac_part (alpha * INR (last N))));
 rewrite (Rplus_comm 0 (alpha * INR (last N)));
 cut (frac_part (alpha * INR (last N)) + frac_part 0 < 1)%R.
intro; rewrite (plus_frac_part2 (alpha * INR (last N)) 0 H0); rewrite fp_R0;
 apply
  (Rplus_gt_compat_l (frac_part (alpha * INR (last N)))
     (frac_part (alpha * INR (first N))) 0); generalize (fp_first_R0 N);
 unfold frac_part_n_alpha in |- *; rewrite (Rmult_comm alpha (INR (first N)));
 auto.
rewrite fp_R0; elim (Rplus_ne (frac_part (alpha * INR (last N)))); intros;
 clear H3; rewrite H0; rewrite (Rmult_comm alpha (INR (last N)));
 cut (frac_part (INR (last N) * alpha) = frac_part_n_alpha (last N)).
intro; rewrite H3; apply (P2 (last N)).
unfold frac_part_n_alpha in |- *; auto.
(**)
left; unfold frac_part_n_alpha in H1; unfold frac_part_n_alpha in |- *;
 unfold frac_part_n_alpha in |- *; rewrite (plus_INR (first N) (last N));
 rewrite (Rmult_comm (INR (first N) + INR (last N)) alpha);
 rewrite (Rmult_plus_distr_l alpha (INR (first N)) (INR (last N)));
 rewrite (Rmult_comm (INR (first N)) alpha) in H1;
 rewrite (Rmult_comm (INR (last N)) alpha) in H1;
 rewrite (Rmult_comm (INR (first N)) alpha);
 rewrite (plus_frac_part1 (alpha * INR (first N)) (alpha * INR (last N)) H1);
 unfold Rminus in |- *; rewrite Rplus_assoc;
 elim (Rplus_ne (alpha * INR (first N))); intros; clear H2;
 pattern (alpha * INR (first N))%R at 2 in |- *; rewrite <- H0;
 cut (frac_part (alpha * INR (first N)) + frac_part 0 < 1)%R.
intro; rewrite (plus_frac_part2 (alpha * INR (first N)) 0 H2); rewrite fp_R0;
 apply
  (Rplus_lt_compat_l (frac_part (alpha * INR (first N)))
     (frac_part (alpha * INR (last N)) + -1) 0);
 cut
  ((frac_part (alpha * INR (last N)) + -1)%R =
   (frac_part (alpha * INR (last N)) - 1)%R).
intro; rewrite H3; clear H3;
 apply (Rlt_minus (frac_part (alpha * INR (last N))) 1).
rewrite (Rmult_comm alpha (INR (last N)));
 cut (frac_part (INR (last N) * alpha) = frac_part_n_alpha (last N)).
intro; rewrite H3; apply (P2 (last N)).
unfold frac_part_n_alpha in |- *; auto.
unfold Rminus in |- *; auto.
rewrite fp_R0; elim (Rplus_ne (frac_part (alpha * INR (first N)))); intros;
 clear H3; rewrite H2; rewrite (Rmult_comm alpha (INR (first N)));
 cut (frac_part (INR (first N) * alpha) = frac_part_n_alpha (first N)).
intro; rewrite H3; apply (P2 (first N)).
unfold frac_part_n_alpha in |- *; auto.
(**)
unfold Rge in |- *;
 generalize
  (Rtotal_order (frac_part_n_alpha (first N) + frac_part_n_alpha (last N)) 1);
 intro; elim H0; intro.
left; auto.
right; elim H1; auto.
Qed.

(**********)
Lemma le_N_M : forall N M : nat, M = first N + last N -> N <= M.
intros; generalize (prop_M N M H); intro; cut (~ N > M).
intro; apply not_gt_le; auto.
unfold gt in |- *; red in |- *; intro; cut (0 < M).
intro; elim H0; intro; clear H0.
generalize (first_n N M (prop_N N) H2 H1 prop_alpha); intro.
generalize
 (Rgt_not_le (frac_part_n_alpha (first N)) (frac_part_n_alpha M) H3); 
 intro; clear H3; auto.
generalize (last_n N M (prop_N N) H2 H1 prop_alpha); intro.
unfold Rgt in H3;
 generalize
  (Rgt_not_le (frac_part_n_alpha M) (frac_part_n_alpha (last N)) H3); 
 intro; clear H3; auto.
rewrite H; generalize (first_0 N (prop_N N)); intro;
 apply (lt_O_plus (first N) (last N) H2).
Qed.

End theoreme.





