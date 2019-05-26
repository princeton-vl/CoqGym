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
(*                               preuve1.v                                  *)
(****************************************************************************)

(*********************************************************)
(*           Intermediate proof 1                        *)
(*                                                       *)
(*********************************************************)

Require Export prop_fl.

Unset Standard Proposition Elimination Names.

Section particular.
Hypothesis alpha_irr : forall n p : Z, (alpha * IZR p)%R <> IZR n.
Hypothesis prop_alpha : (0 < alpha)%R /\ (alpha < 1)%R.
Hypothesis prop_N : forall N : nat, N >= 2.

(**********)
Definition M (N : nat) := first N + last N.

(**********)
Lemma inter31a :
 forall N n : nat, 0 < n -> n < last (M N) -> after (M N) n = n + first (M N).
intros; apply (sym_equal (x:=n + first (M N)) (y:=after (M N) n));
 apply (tech_after alpha_irr (M N) n (n + first (M N)) H);
 auto with arith real.
apply (lt_le_trans n (last (M N)) (M N) H0 (last_N01 (M N))).
unfold M at 2 in |- *;
 rewrite (last_eq_M_N alpha_irr prop_alpha prop_N N (M N));
 auto with arith real;
 rewrite (first_eq_M_N alpha_irr prop_alpha prop_N N (M N));
 auto with arith real.
rewrite (plus_comm (first (M N)) (last (M N)));
 apply (plus_lt_compat_r n (last (M N)) (first (M N)) H0).
fold (frac_part_n_alpha (n + first (M N)) > frac_part_n_alpha n)%R in |- *;
 apply
  (Rnot_le_lt (frac_part_n_alpha (n + first (M N))) (frac_part_n_alpha n));
 red in |- *; intro;
 generalize
  (Rplus_le_compat_l (- frac_part_n_alpha (first (M N)))
     (frac_part_n_alpha (n + first (M N))) (frac_part_n_alpha n) H1);
 rewrite
  (Rplus_comm (- frac_part_n_alpha (first (M N)))
     (frac_part_n_alpha (n + first (M N))));
 rewrite
  (Rplus_comm (- frac_part_n_alpha (first (M N))) (frac_part_n_alpha n))
  ;
 fold
  (frac_part_n_alpha (n + first (M N)) - frac_part_n_alpha (first (M N)))%R
  in |- *;
 fold (frac_part_n_alpha n - frac_part_n_alpha (first (M N)))%R in |- *;
 cut
  (frac_part_n_alpha (n + first (M N)) >= frac_part_n_alpha (first (M N)))%R.
intro; unfold frac_part_n_alpha at 1 2 in |- *;
 unfold frac_part_n_alpha in H2;
 rewrite <-
  (Rminus_fp1 (INR (n + first (M N)) * alpha) (INR (first (M N)) * alpha) H2)
  ; rewrite (plus_INR n (first (M N)));
 rewrite (Rmult_comm (INR n + INR (first (M N))) alpha);
 rewrite (Rmult_plus_distr_l alpha (INR n) (INR (first (M N))));
 rewrite (Rmult_comm alpha (INR (first (M N)))); unfold Rminus at 1 in |- *;
 rewrite
  (Rplus_assoc (alpha * INR n) (INR (first (M N)) * alpha)
     (- (INR (first (M N)) * alpha)));
 rewrite (Rplus_opp_r (INR (first (M N)) * alpha)).
 elim (Rplus_ne (alpha * INR n)); intros a b; rewrite a; clear a b;
  rewrite (Rmult_comm alpha (INR n)); fold (frac_part_n_alpha n) in |- *;
  intro; cut (0 < frac_part_n_alpha (first (M N)))%R.
intro;
 generalize
  (tech_Rgt_minus (frac_part_n_alpha n) (frac_part_n_alpha (first (M N))) H4);
 clear H4 H1 H2; intro; unfold Rgt in H1;
 generalize
  (Rgt_not_le (frac_part_n_alpha n)
     (frac_part_n_alpha n - frac_part_n_alpha (first (M N))) H1);
 auto with arith real.
fold (frac_part_n_alpha (first (M N)) > 0)%R in |- *;
 apply (fp_first_R0 alpha_irr prop_N (M N)).
unfold Rge in |- *; unfold Rgt in |- *;
 cut
  ((frac_part_n_alpha (first (M N)) < frac_part_n_alpha (n + first (M N)))%R \/
   frac_part_n_alpha (first (M N)) = frac_part_n_alpha (n + first (M N))).
intro; elim H2; intro.
left; auto with arith real.
right; auto with arith real.
fold
 (frac_part_n_alpha (first (M N)) <= frac_part_n_alpha (n + first (M N)))%R
 in |- *; apply (first_n (M N) (n + first (M N))); 
 auto with arith real;
 generalize (plus_lt_compat_r n (last (M N)) (first (M N)) H0); 
 intro; unfold M at 2 in |- *;
 rewrite (first_eq_M_N alpha_irr prop_alpha prop_N N (M N));
 auto with arith real;
 rewrite (last_eq_M_N alpha_irr prop_alpha prop_N N (M N));
 auto with arith real; rewrite (plus_comm (first (M N)) (last (M N)));
 assumption.
(**)
intro; elim H1; intros; elim H2; intros; elim H4; intros; elim H6; intros;
 clear H6 H4 H2 H1.
elim (le_or_lt x n); intro.
generalize
 (Ropp_lt_gt_contravar (frac_part_n_alpha n) (frac_part_n_alpha x) H7); 
 intro;
 generalize
  (Rplus_gt_compat_l (frac_part_n_alpha (n + first (M N)))
     (- frac_part_n_alpha n) (- frac_part_n_alpha x) H2);
 fold (frac_part_n_alpha (n + first (M N)) - frac_part_n_alpha n)%R in |- *;
 fold (frac_part_n_alpha (n + first (M N)) - frac_part_n_alpha x)%R in |- *;
 fold (frac_part_n_alpha (n + first (M N)) > frac_part_n_alpha x)%R in H8;
 generalize
  (Rgt_ge (frac_part_n_alpha (n + first (M N))) (frac_part_n_alpha x) H8);
 intro; unfold frac_part_n_alpha in H4; unfold frac_part_n_alpha in |- *;
 rewrite <- (Rminus_fp1 (INR (n + first (M N)) * alpha) (INR x * alpha) H4);
 fold (frac_part_n_alpha x > frac_part_n_alpha n)%R in H7;
 generalize
  (Rgt_trans (frac_part_n_alpha (n + first (M N))) 
     (frac_part_n_alpha x) (frac_part_n_alpha n) H8 H7); 
 intro;
 generalize
  (Rgt_ge (frac_part_n_alpha (n + first (M N))) (frac_part_n_alpha n) H6);
 intro; unfold frac_part_n_alpha in H9;
 rewrite <- (Rminus_fp1 (INR (n + first (M N)) * alpha) (INR n * alpha) H9);
 rewrite (plus_INR n (first (M N)));
 rewrite (Rmult_comm (INR n + INR (first (M N))) alpha);
 rewrite (Rmult_plus_distr_l alpha (INR n) (INR (first (M N))));
 rewrite (Rmult_comm alpha (INR n)); unfold Rminus at 1 in |- *;
 rewrite (Rplus_comm (INR n * alpha) (alpha * INR (first (M N))));
 rewrite
  (Rplus_assoc (alpha * INR (first (M N))) (INR n * alpha)
     (- (INR n * alpha))); rewrite (Rplus_opp_r (INR n * alpha));
 elim (Rplus_ne (alpha * INR (first (M N)))); intros a b; 
 rewrite a; clear a b; rewrite (Rmult_comm alpha (INR (first (M N))));
 fold (frac_part_n_alpha (first (M N))) in |- *; unfold Rminus in |- *;
 rewrite
  (Rplus_assoc (INR (first (M N)) * alpha) (INR n * alpha)
     (- (INR x * alpha))); rewrite (Rmult_comm (INR (first (M N))) alpha);
 rewrite (Rmult_comm (INR n) alpha);
 rewrite <- (Ropp_mult_distr_l_reverse (INR x) alpha);
 rewrite (Rmult_comm (- INR x) alpha);
 rewrite <- (Rmult_plus_distr_l alpha (INR n) (- INR x));
 rewrite <- (Rmult_plus_distr_l alpha (INR (first (M N))) (INR n + - INR x));
 fold (INR n - INR x)%R in |- *; rewrite <- (minus_INR n x H1);
 rewrite <- (plus_INR (first (M N)) (n - x));
 rewrite (Rmult_comm alpha (INR (first (M N) + (n - x))));
 fold (frac_part_n_alpha (first (M N) + (n - x))) in |- *; 
 intro; clear H2 H4 H6 H9; cut (0 < first (M N) + (n - x)).
cut (first (M N) + (n - x) < M N).
intros;
 generalize
  (first_n (M N) (first (M N) + (n - x)) (prop_N (M N)) H4 H2 prop_alpha);
 intro; clear H2 H4; unfold Rgt in H10;
 generalize
  (Rgt_not_le (frac_part_n_alpha (first (M N)))
     (frac_part_n_alpha (first (M N) + (n - x))) H10); 
 auto with arith real.
unfold M at 2 in |- *;
 rewrite (first_eq_M_N alpha_irr prop_alpha prop_N N (M N));
 auto with arith real.
apply (plus_lt_compat_l (n - x) (last N) (first (M N)));
 rewrite (last_eq_M_N alpha_irr prop_alpha prop_N N (M N));
 auto with arith real.
apply (lt_minus_p n (last (M N)) x H0).
apply (lt_O_plus (first (M N)) (n - x) (first_0 (M N) (prop_N (M N)))). 
(**)
generalize
 (Rplus_lt_compat_l (- frac_part_n_alpha n) (frac_part_n_alpha x)
    (frac_part_n_alpha (n + first (M N))) H8);
 rewrite (Rplus_comm (- frac_part_n_alpha n) (frac_part_n_alpha x));
 rewrite
  (Rplus_comm (- frac_part_n_alpha n) (frac_part_n_alpha (n + first (M N))))
  ; fold (frac_part_n_alpha x - frac_part_n_alpha n)%R in |- *;
 fold (frac_part_n_alpha (n + first (M N)) - frac_part_n_alpha n)%R in |- *;
 fold (frac_part_n_alpha x > frac_part_n_alpha n)%R in H7;
 generalize (Rgt_ge (frac_part_n_alpha x) (frac_part_n_alpha n) H7); 
 intro;
 fold (frac_part_n_alpha (n + first (M N)) > frac_part_n_alpha x)%R in H8;
 generalize
  (Rgt_trans (frac_part_n_alpha (n + first (M N))) 
     (frac_part_n_alpha x) (frac_part_n_alpha n) H8 H7); 
 intro;
 generalize
  (Rgt_ge (frac_part_n_alpha (n + first (M N))) (frac_part_n_alpha n) H4);
 intro; unfold frac_part_n_alpha in H2, H6; unfold frac_part_n_alpha in |- *;
 rewrite <- (Rminus_fp1 (INR x * alpha) (INR n * alpha) H2);
 rewrite <- (Rminus_fp1 (INR (n + first (M N)) * alpha) (INR n * alpha) H6);
 rewrite (plus_INR n (first (M N)));
 rewrite (Rmult_comm (INR n + INR (first (M N))) alpha);
 rewrite (Rmult_plus_distr_l alpha (INR n) (INR (first (M N))));
 rewrite (Rmult_comm alpha (INR n));
 rewrite (Rmult_comm alpha (INR (first (M N)))); unfold Rminus at 2 in |- *;
 rewrite (Rplus_comm (INR n * alpha) (INR (first (M N)) * alpha));
 rewrite
  (Rplus_assoc (INR (first (M N)) * alpha) (INR n * alpha)
     (- (INR n * alpha))); rewrite (Rplus_opp_r (INR n * alpha));
 elim (Rplus_ne (INR (first (M N)) * alpha)); intros a b; 
 rewrite a; clear a b; fold (frac_part_n_alpha (first (M N))) in |- *;
 clear H2 H4 H6; unfold Rminus in |- *; rewrite (Rmult_comm (INR x) alpha);
 rewrite <- (Ropp_mult_distr_l_reverse (INR n) alpha);
 rewrite (Rmult_comm (- INR n) alpha);
 rewrite <- (Rmult_plus_distr_l alpha (INR x) (- INR n));
 fold (INR x - INR n)%R in |- *; rewrite (Rmult_comm alpha (INR x - INR n));
 generalize (lt_le_weak n x H1); intro; rewrite <- (minus_INR x n H2);
 fold (frac_part_n_alpha (x - n)) in |- *; intro; cut (0 < x - n).
intro; cut (x - n < M N).
intro; generalize (first_n (M N) (x - n) (prop_N (M N)) H6 H9 prop_alpha);
 intro; clear H9 H6;
 generalize
  (Rgt_not_le (frac_part_n_alpha (first (M N))) (frac_part_n_alpha (x - n))
     H4); auto with arith real.
apply (lt_minus_p x (M N) n H5).
apply (lt_minus2 n x H1).
Qed.

(**********)
Lemma inter31b :
 forall N n : nat,
 last (M N) <= n -> n < M N -> after (M N) n = n - last (M N).
intros; elim (le_lt_or_eq (last (M N)) n H); intro; clear H.
apply (sym_equal (x:=n - last (M N)) (y:=after (M N) n));
 apply (tech_after alpha_irr (M N) n (n - last (M N))); 
 auto with arith real.
apply (lt_trans 0 (last (M N)) n (last_0 (M N) (prop_N (M N))) H1).
apply (lt_minus_p n (M N) (last (M N)) H0).
cut
 (frac_part_n_alpha n <
  frac_part_n_alpha n - frac_part_n_alpha (last (M N)) + 1)%R. 
intro; unfold frac_part_n_alpha in H; generalize H; clear H;
 rewrite <- (Rminus_fp2 (INR n * alpha) (INR (last (M N)) * alpha)).
fold (frac_part_n_alpha n) in |- *; rewrite (Rmult_comm (INR n) alpha);
 unfold Rminus in |- *;
 rewrite <- (Ropp_mult_distr_l_reverse (INR (last (M N))) alpha);
 rewrite (Rmult_comm (- INR (last (M N))) alpha);
 rewrite <- (Rmult_plus_distr_l alpha (INR n) (- INR (last (M N))));
 fold (INR n - INR (last (M N)))%R in |- *;
 rewrite <- (minus_INR n (last (M N)) (lt_le_weak (last (M N)) n H1));
 rewrite (Rmult_comm alpha (INR (n - last (M N))));
 fold (frac_part_n_alpha (n - last (M N))) in |- *; 
 trivial.
fold (frac_part_n_alpha n) in |- *;
 fold (frac_part_n_alpha (last (M N))) in |- *;
 generalize
  (last_n (M N) n (prop_N (M N))
     (lt_trans 0 (last (M N)) n (last_0 (M N) (prop_N (M N))) H1) H0
     prop_alpha); intro; unfold Rle in H; elim H; intro; 
 auto with arith real.
generalize
 (contra_tech_fp_alp_irr alpha_irr prop_alpha (last (M N)) n
    (lt_not_eq (last (M N)) n H1)); intro; elimtype False;
 auto with arith real.
unfold Rminus in |- *;
 rewrite
  (Rplus_assoc (frac_part_n_alpha n) (- frac_part_n_alpha (last (M N))) 1)
  ; rewrite (Rplus_comm (- frac_part_n_alpha (last (M N))) 1);
 fold (1 - frac_part_n_alpha (last (M N)))%R in |- *;
 elim (Rplus_ne (frac_part_n_alpha n)); intros a b;
 pattern (frac_part_n_alpha n) at 1 in |- *; rewrite <- a; 
 clear a b;
 apply
  (Rplus_lt_compat_l (frac_part_n_alpha n) 0
     (1 - frac_part_n_alpha (last (M N))));
 fold (1 - frac_part_n_alpha (last (M N)) > 0)%R in |- *;
 apply (Rgt_minus 1 (frac_part_n_alpha (last (M N)))); 
 unfold Rgt in |- *; unfold frac_part_n_alpha in |- *;
 elim (base_fp (INR (last (M N)) * alpha)); intros; 
 assumption.
(**)
intro; elim H; intros; elim H2; intros; elim H4; intros; elim H6; intros;
 clear H H2 H4 H6.
elim (le_or_lt n x); intro.
generalize
 (Rplus_lt_compat_l (- frac_part_n_alpha (n - last (M N)))
    (frac_part_n_alpha n) (frac_part_n_alpha x) H7); 
 intro;
 generalize
  (Rplus_lt_compat_l 1
     (- frac_part_n_alpha (n - last (M N)) + frac_part_n_alpha n)
     (- frac_part_n_alpha (n - last (M N)) + frac_part_n_alpha x) H2);
 clear H2;
 rewrite
  (Rplus_comm 1 (- frac_part_n_alpha (n - last (M N)) + frac_part_n_alpha n))
  ;
 rewrite
  (Rplus_comm 1 (- frac_part_n_alpha (n - last (M N)) + frac_part_n_alpha x))
  ;
 rewrite
  (Rplus_comm (- frac_part_n_alpha (n - last (M N))) (frac_part_n_alpha n))
  ;
 rewrite
  (Rplus_comm (- frac_part_n_alpha (n - last (M N))) (frac_part_n_alpha x))
  ; fold (frac_part_n_alpha n - frac_part_n_alpha (n - last (M N)))%R in |- *;
 fold (frac_part_n_alpha x - frac_part_n_alpha (n - last (M N)))%R in |- *;
 unfold frac_part_n_alpha in |- *;
 rewrite <- (Rminus_fp2 (INR n * alpha) (INR (n - last (M N)) * alpha)). 
rewrite <- (Rminus_fp2 (INR x * alpha) (INR (n - last (M N)) * alpha)). 
rewrite (minus_INR n (last (M N)) (lt_le_weak (last (M N)) n H1));
 unfold Rminus in |- *;
 rewrite (Rmult_comm (INR n + - INR (last (M N))) alpha);
 rewrite (Rmult_plus_distr_l alpha (INR n) (- INR (last (M N))));
 rewrite (Ropp_plus_distr (alpha * INR n) (alpha * - INR (last (M N))));
 rewrite <-
  (Rplus_assoc (INR n * alpha) (- (alpha * INR n))
     (- (alpha * - INR (last (M N))))); rewrite (Rmult_comm (INR n) alpha);
 rewrite (Rplus_opp_r (alpha * INR n));
 elim (Rplus_ne (- (alpha * - INR (last (M N))))); 
 intros a b; rewrite b; clear a b;
 rewrite (Rmult_comm alpha (- INR (last (M N))));
 rewrite <- (Ropp_mult_distr_l_reverse (- INR (last (M N))) alpha);
 rewrite (Ropp_involutive (INR (last (M N))));
 fold (frac_part_n_alpha (last (M N))) in |- *;
 rewrite <-
  (Rplus_assoc (INR x * alpha) (- (alpha * INR n)) (INR (last (M N)) * alpha))
  ; rewrite (Rmult_comm alpha (INR n));
 rewrite <- (Ropp_mult_distr_l_reverse (INR n) alpha);
 rewrite (Rmult_comm (- INR n) alpha); rewrite (Rmult_comm (INR x) alpha);
 rewrite <- (Rmult_plus_distr_l alpha (INR x) (- INR n));
 fold (INR x - INR n)%R in |- *; rewrite <- (minus_INR x n H);
 rewrite (Rmult_comm (INR (last (M N))) alpha);
 rewrite <- (Rmult_plus_distr_l alpha (INR (x - n)) (INR (last (M N))));
 rewrite <- (plus_INR (x - n) (last (M N)));
 rewrite (Rmult_comm alpha (INR (x - n + last (M N))));
 fold (frac_part_n_alpha (x - n + last (M N))) in |- *; 
 intro; cut (0 < x - n + last (M N)). 
intro; cut (x - n + last (M N) < M N).
intro;
 generalize
  (last_n (M N) (x - n + last (M N)) (prop_N (M N)) H4 H6 prop_alpha); 
 intro; clear H4 H6;
 generalize
  (Rgt_not_le (frac_part_n_alpha (x - n + last (M N)))
     (frac_part_n_alpha (last (M N))) H2); intro; elimtype False;
 auto with arith real.
apply (tech_inter31b (last (M N)) n x (M N) H1 H H5).
rewrite plus_comm;
 apply (lt_O_plus (last (M N)) (x - n) (last_0 (M N) (prop_N (M N)))). 
fold (frac_part_n_alpha x) in |- *;
 fold (frac_part_n_alpha (n - last (M N))) in |- *; 
 assumption.
fold (frac_part_n_alpha n) in |- *;
 fold (frac_part_n_alpha (n - last (M N))) in |- *;
 apply
  (Rlt_trans (frac_part_n_alpha n) (frac_part_n_alpha x)
     (frac_part_n_alpha (n - last (M N))) H7 H8).
(**)
generalize
 (Ropp_lt_gt_contravar (frac_part_n_alpha x)
    (frac_part_n_alpha (n - last (M N))) H8); unfold Rgt in |- *; 
 intro;
 generalize
  (Rplus_lt_compat_l (frac_part_n_alpha n)
     (- frac_part_n_alpha (n - last (M N))) (- frac_part_n_alpha x) H2);
 clear H2;
 fold (frac_part_n_alpha n - frac_part_n_alpha (n - last (M N)))%R in |- *;
 fold (frac_part_n_alpha n - frac_part_n_alpha x)%R in |- *; 
 intro;
 generalize
  (Rplus_lt_compat_l 1
     (frac_part_n_alpha n - frac_part_n_alpha (n - last (M N)))
     (frac_part_n_alpha n - frac_part_n_alpha x) H2); 
 clear H2;
 rewrite
  (Rplus_comm 1 (frac_part_n_alpha n - frac_part_n_alpha (n - last (M N))))
  ; rewrite (Rplus_comm 1 (frac_part_n_alpha n - frac_part_n_alpha x));
 unfold frac_part_n_alpha in |- *;
 rewrite <- (Rminus_fp2 (INR n * alpha) (INR (n - last (M N)) * alpha)).
rewrite <- (Rminus_fp2 (INR n * alpha) (INR x * alpha)). 
rewrite (Rmult_comm (INR n) alpha); unfold Rminus at 2 in |- *;
 rewrite <- (Ropp_mult_distr_l_reverse (INR x) alpha);
 rewrite (Rmult_comm (- INR x) alpha);
 rewrite <- (Rmult_plus_distr_l alpha (INR n) (- INR x));
 fold (INR n - INR x)%R in |- *;
 rewrite <- (minus_INR n x (lt_le_weak x n H));
 rewrite (Rmult_comm alpha (INR (n - x)));
 fold (frac_part_n_alpha (n - x)) in |- *;
 rewrite (minus_INR n (last (M N)) (lt_le_weak (last (M N)) n H1));
 unfold Rminus in |- *;
 rewrite (Rmult_comm (INR n + - INR (last (M N))) alpha);
 rewrite (Rmult_plus_distr_l alpha (INR n) (- INR (last (M N))));
 rewrite (Ropp_plus_distr (alpha * INR n) (alpha * - INR (last (M N))));
 rewrite <-
  (Rplus_assoc (alpha * INR n) (- (alpha * INR n))
     (- (alpha * - INR (last (M N))))); rewrite (Rplus_opp_r (alpha * INR n));
 elim (Rplus_ne (- (alpha * - INR (last (M N))))); 
 intros a b; rewrite b; clear a b;
 rewrite (Rmult_comm alpha (- INR (last (M N))));
 rewrite <- (Ropp_mult_distr_l_reverse (- INR (last (M N))) alpha);
 rewrite (Ropp_involutive (INR (last (M N))));
 fold (frac_part_n_alpha (last (M N))) in |- *; intro; 
 cut (0 < n - x).
intro; cut (n - x < M N).
intro; generalize (last_n (M N) (n - x) (prop_N (M N)) H4 H6 prop_alpha);
 intro;
 generalize
  (Rgt_not_le (frac_part_n_alpha (n - x)) (frac_part_n_alpha (last (M N))) H2);
 intro; elimtype False; auto with arith real.
apply (lt_minus_p n (M N) x H0).
apply (lt_minus2 x n H).
fold (frac_part_n_alpha n) in |- *; fold (frac_part_n_alpha x) in |- *;
 assumption.
fold (frac_part_n_alpha n) in |- *;
 fold (frac_part_n_alpha (n - last (M N))) in |- *;
 apply
  (Rlt_trans (frac_part_n_alpha n) (frac_part_n_alpha x)
     (frac_part_n_alpha (n - last (M N))) H7 H8).
rewrite <- H1; rewrite <- (minus_n_n (last (M N)));
 apply (after_last prop_alpha prop_N (M N)).
Qed.

(**********)
Lemma tech1 :
 forall N n : nat,
 N - first N <= n ->
 n < last N ->
 (frac_part_n_alpha n < frac_part_n_alpha (n + first N - last N))%R.
intros; cut (frac_part_n_alpha n < frac_part_n_alpha (n + first N))%R.
intro;
 cut
  (frac_part_n_alpha (n + first N) < frac_part_n_alpha (n + first N - last N))%R.
intro;
 apply
  (Rlt_trans (frac_part_n_alpha n) (frac_part_n_alpha (n + first N))
     (frac_part_n_alpha (n + first N - last N)) H1 H2).
cut (0 < n + first N).
cut (n + first N < M N).
intros;
 apply (tech_after_lt (M N) (n + first N) (n + first N - last N) H3 H2).
apply (lt_minus_not (last N) (n + first N)).
generalize (le_minus_plus N (first N) n H); intro;
 apply (lt_le_trans (last N) N (n + first N) (last_N N (prop_N N)) H4).
rewrite (last_eq_M_N alpha_irr prop_alpha prop_N N (M N));
 auto with arith real.
generalize H2; clear H2;
 rewrite (first_eq_M_N alpha_irr prop_alpha prop_N N (M N));
 auto with arith real.
intro; cut (last (M N) <= n + first (M N)).
intro; apply (inter31b N (n + first (M N)) H4 H2).
rewrite <- (last_eq_M_N alpha_irr prop_alpha prop_N N (M N));
 auto with arith real.
rewrite <- (first_eq_M_N alpha_irr prop_alpha prop_N N (M N));
 auto with arith real.
generalize (le_minus_plus N (first N) n H); intro;
 apply (le_trans (last N) N (n + first N) (last_N01 N) H4).
unfold M in |- *; rewrite (plus_comm (first N) (last N));
 apply (plus_lt_compat_r n (last N) (first N) H0).
generalize (le_minus_plus N (first N) n H); intro; cut (0 < N).
intro; apply (lt_le_trans 0 N (n + first N) H3 H2).
apply (arith_2_0 N (prop_N N)).
(**)
cut (0 < n).
cut (n < M N).
intros; apply (tech_after_lt (M N) n (n + first N) H2 H1).
generalize (lt_O_plus n (first N) H2); intro; apply Compare.not_eq_sym;
 red in |- *; intro; apply (lt_not_eq 0 (n + first N) H3 H4).
rewrite (first_eq_M_N alpha_irr prop_alpha prop_N N (M N));
 auto with arith real.
generalize H0; rewrite (last_eq_M_N alpha_irr prop_alpha prop_N N (M N));
 auto with arith real; clear H0; intro; apply (inter31a N n H2 H0).
generalize (lt_trans n (last N) N H0 (last_N N (prop_N N))); intro;
 unfold M in |- *; cut (N <= first N + last N).
intro; apply (lt_le_trans n N (first N + last N) H1 H2).
apply (le_N_M alpha_irr prop_alpha prop_N N (M N)); auto with arith real.
apply
 (lt_le_trans 0 (N - first N) n
    (lt_minus2 (first N) N (first_N N (prop_N N))) H).
Qed.

(**********)
Lemma tech_suc_N :
 forall N n : nat,
 0 < n ->
 n < N ->
 forall k : nat,
 0 < k ->
 k < N ->
 (frac_part_n_alpha n < frac_part_n_alpha k)%R ->
 frac_part_n_alpha k <> frac_part_n_alpha (after N n) ->
 (frac_part_n_alpha (after N n) < frac_part_n_alpha k)%R.
unfold after in |- *; intros; generalize H4; clear H4;
 case (exist_after_M (frac_part_n_alpha n) (P1 n) (P2 n) N); 
 intro.
elim s; intros x y H4; clear s; elim y; intros; clear y; unfold Rgt in H6;
 cut (0 <= k).
elim H6; intros; elim H8; intros; generalize (H11 k H9 H2 H3);
 unfold Rge in |- *; unfold Rgt in |- *; intro; elim H12;
 auto with arith real.
intro; elimtype False; auto with arith real.
apply (lt_le_weak 0 k H1).
unfold frac_part_n_alpha in |- *; simpl in |- *; rewrite Rmult_0_l;
 rewrite fp_R0; elim (base_fp (INR k * alpha)); intros; 
 unfold Rge in H4; elim H4; auto with arith real.
intro; elimtype False; auto with arith real.
Qed.

(**********)
Lemma tech_suc_M :
 forall N n : nat,
 N - first N <= n ->
 n < last N ->
 (exists k : nat,
    0 < k /\
    k < N /\
    (frac_part_n_alpha n < frac_part_n_alpha k)%R /\
    (frac_part_n_alpha k < frac_part_n_alpha (n + first N - last N))%R) ->
 False.
intros; elim H1; intros; clear H1.
elim H2; intros; elim H3; intros; clear H3; clear H2; elim H5; intros;
 clear H5.
cut (0 < n).
intro; cut (n < M N).
intros; cut (x < M N).
intro;
 elim (Rtotal_order (frac_part_n_alpha x) (frac_part_n_alpha (n + first N)));
 intro.
cut (n + first N = after (M N) n).
intro; rewrite H9 in H8;
 cut (frac_part_n_alpha x <> frac_part_n_alpha (after (M N) n)).
intro; generalize (tech_suc_N (M N) n H5 H6 x H1 H7 H2 H10).
intro;
 generalize
  (Rlt_asym (frac_part_n_alpha x) (frac_part_n_alpha (after (M N) n)) H8).
intro; auto with arith real.
apply
 (Rlt_dichotomy_converse (frac_part_n_alpha x)
    (frac_part_n_alpha (after (M N) n))).
left; auto with arith real.
apply sym_equal.
rewrite (first_eq_M_N alpha_irr prop_alpha prop_N N (M N)).
apply (inter31a N n H5).
rewrite <- (last_eq_M_N alpha_irr prop_alpha prop_N N (M N)).
assumption.
auto with arith real.
auto with arith real.
(**)
elim H8; intro; clear H8.
cut (x <> n + first N).
intro;
 generalize (contra_tech_fp_alp_irr alpha_irr prop_alpha x (n + first N) H8);
 auto with arith real.
cut (x < n + first N).
intro; red in |- *; intro; apply (lt_not_eq x (n + first N) H8); assumption.
generalize (le_minus_plus N (first N) n H); intro;
 apply (lt_le_trans x N (n + first N) H4 H8).
(**)
cut (0 < n + first (M N)).
intro; cut (n + first (M N) < M N).
intro;
 cut
  (frac_part_n_alpha x <> frac_part_n_alpha (after (M N) (n + first (M N)))).
intro; unfold Rgt in H9;
 rewrite
  (first_eq_M_N alpha_irr prop_alpha prop_N N (M N)
     (refl_equal (first N + last N))) in H9;
 generalize (tech_suc_N (M N) (n + first (M N)) H8 H10 x H1 H7 H9 H11); 
 intro; cut (last (M N) <= n + first (M N)).
intro; rewrite (inter31b N (n + first (M N)) H13 H10) in H12.
rewrite
 (first_eq_M_N alpha_irr prop_alpha prop_N N (M N)
    (refl_equal (first N + last N))) in H3;
 rewrite
  (last_eq_M_N alpha_irr prop_alpha prop_N N (M N)
     (refl_equal (first N + last N))) in H3;
 generalize
  (Rlt_asym (frac_part_n_alpha (n + first (M N) - last (M N)))
     (frac_part_n_alpha x) H12); intro; auto with arith real.
generalize (le_minus_plus N (first N) n H); intro.
generalize (last_N01 N); intro.
rewrite <-
 (first_eq_M_N alpha_irr prop_alpha prop_N N (M N)
    (refl_equal (first N + last N)));
 rewrite <-
  (last_eq_M_N alpha_irr prop_alpha prop_N N (M N)
     (refl_equal (first N + last N)));
 apply (le_trans (last N) N (n + first N) H14 H13).
cut (last (M N) <= n + first (M N)).
intro; rewrite (inter31b N (n + first (M N)) H11 H10);
 rewrite <-
  (first_eq_M_N alpha_irr prop_alpha prop_N N (M N)
     (refl_equal (first N + last N)));
 rewrite <-
  (last_eq_M_N alpha_irr prop_alpha prop_N N (M N)
     (refl_equal (first N + last N)));
 apply
  (Rlt_dichotomy_converse (frac_part_n_alpha x)
     (frac_part_n_alpha (n + first N - last N))).
left; assumption.
generalize (le_minus_plus N (first N) n H); intro.
generalize (last_N01 N); intro;
 rewrite <-
  (first_eq_M_N alpha_irr prop_alpha prop_N N (M N)
     (refl_equal (first N + last N)));
 rewrite <-
  (last_eq_M_N alpha_irr prop_alpha prop_N N (M N)
     (refl_equal (first N + last N)));
 apply (le_trans (last N) N (n + first N) H12 H11).
rewrite <-
 (first_eq_M_N alpha_irr prop_alpha prop_N N (M N)
    (refl_equal (first N + last N))); unfold M in |- *;
 rewrite (plus_comm (first N) (last N));
 apply (plus_lt_compat_r n (last N) (first N) H0).
apply (lt_O_plus n (first (M N)) H5).
cut (N <= M N).
intro; apply (lt_le_trans x N (M N) H4 H7).
apply
 (le_N_M alpha_irr prop_alpha prop_N N (M N) (refl_equal (first N + last N))).
cut (last N < N).
intro; cut (N <= M N).
intro; generalize (lt_trans n (last N) N H0 H6).
intro; apply (lt_le_trans n N (M N) H8 H7).
apply
 (le_N_M alpha_irr prop_alpha prop_N N (M N) (refl_equal (first N + last N))).
apply (last_N N (prop_N N)).
cut (0 < N - first N).
intro; apply (lt_le_trans 0 (N - first N) n H5 H).
apply (lt_minus2 (first N) N (first_N N (prop_N N))).
Qed.

(**********)
Lemma tech_suc_M1 :
 forall N n : nat,
 N - first N <= n ->
 n < last N ->
 forall k : nat,
 ~
 (0 < k /\
  k < N /\
  (frac_part_n_alpha n < frac_part_n_alpha k)%R /\
  (frac_part_n_alpha k < frac_part_n_alpha (n + first N - last N))%R).
intros; generalize (tech_suc_M N n H H0); intro; red in |- *; intro; apply H1;
 split with k; auto with arith real.
Qed.

(**********)
Lemma eq_after_M_N1 :
 forall N n : nat, 0 < n -> n < N - first N -> after (M N) n = after N n.
intros; cut (n < last (M N)).
intro; generalize (inter31a N n H H1);
 rewrite <-
  (first_eq_M_N alpha_irr prop_alpha prop_N N (M N) (refl_equal (M N)))
  ; intro; apply (tech_fp_alp_irr alpha_irr (after (M N) n) (after N n));
 apply
  (Rge_antisym (frac_part_n_alpha (after (M N) n))
     (frac_part_n_alpha (after N n))).
apply
 (Rnot_lt_ge (frac_part_n_alpha (after (M N) n))
    (frac_part_n_alpha (after N n))); red in |- *; 
 intro; cut (0 < after (M N) n).
intro; cut (after (M N) n < N).
intro; cut (frac_part_n_alpha n < frac_part_n_alpha (after (M N) n))%R.
intro;
 generalize
  (tech_suc_N N n H (contra_lt_minus_p n N (first N) H0) 
     (after (M N) n) H4 H5 H6
     (Rlt_dichotomy_converse (frac_part_n_alpha (after (M N) n))
        (frac_part_n_alpha (after N n))
        (or_introl
           (frac_part_n_alpha (after (M N) n) > frac_part_n_alpha (after N n))%R
           H3))); intro;
 generalize
  (Rlt_asym (frac_part_n_alpha (after (M N) n))
     (frac_part_n_alpha (after N n)) H3); intro; elimtype False;
 auto with arith real.
apply
 (tech_after_lt (M N) n (after (M N) n) H
    (lt_le_trans n N (M N) (contra_lt_minus_p n N (first N) H0)
       (le_N_M alpha_irr prop_alpha prop_N N (M N) (refl_equal (M N)))));
 auto with arith real.
rewrite H2; red in |- *; intro; apply (lt_O_plus_eq n (first N) H);
 auto with arith real.
rewrite H2; apply (lt_n_minus_plus n N (first N) H0). 
rewrite H2; apply (lt_O_plus n (first N) H).
(**)
apply
 (Rnot_lt_ge (frac_part_n_alpha (after N n))
    (frac_part_n_alpha (after (M N) n))); red in |- *; 
 intro; apply (prop_after (M N) n (after (M N) n)); 
 auto with arith real.
split with (after N n); split.
unfold after in |- *;
 case (exist_after_M (frac_part_n_alpha n) (P1 n) (P2 n) N).
intro; elim s; intros x y; elim y; intros; assumption.
intro; generalize (a (last N) (le_O_n (last N)) (last_N N (prop_N N))); intro;
 elim H4; intros; clear a H4;
 generalize
  (last_n N n (prop_N N) H (contra_lt_minus_p n N (first N) H0) prop_alpha);
 intro; cut (frac_part_n_alpha n = frac_part_n_alpha (last N)).
intro; generalize (tech_fp_alp_irr alpha_irr n (last N) H7);
 rewrite (last_eq_M_N alpha_irr prop_alpha prop_N N (M N));
 auto with arith real.
intro; generalize (lt_not_eq n (last (M N)) H1); intro; elimtype False;
 auto with arith real.
elim (Rle_le_eq (frac_part_n_alpha n) (frac_part_n_alpha (last N))); intros;
 clear H8; apply H7; auto with arith real.
split.
cut (after N n < N).
intro;
 apply
  (lt_le_trans (after N n) N (M N) H4
     (le_N_M alpha_irr prop_alpha prop_N N (M N) (refl_equal (M N)))).
unfold after in |- *;
 case (exist_after_M (frac_part_n_alpha n) (P1 n) (P2 n) N).
intro; elim s; intros x y; elim y; intros; elim H5; intros; assumption.
intro; apply (arith_2_0 N (prop_N N)).
split; auto with arith real.
apply (tech_after_lt N n (after N n) H (contra_lt_minus_p n N (first N) H0));
 auto with arith real.
red in |- *; unfold after in |- *;
 case (exist_after_M (frac_part_n_alpha n) (P1 n) (P2 n) N).
intro; elim s; intros x y H4; elim y; intros; generalize (lt_not_eq 0 x H5);
 intro; auto with arith real.
intros; generalize (a (last N) (le_O_n (last N)) (last_N N (prop_N N)));
 intro; elim H5; intros; clear a H5;
 generalize
  (last_n N n (prop_N N) H (contra_lt_minus_p n N (first N) H0) prop_alpha);
 intro; cut (frac_part_n_alpha n = frac_part_n_alpha (last N)).
intro; generalize (tech_fp_alp_irr alpha_irr n (last N) H8);
 rewrite (last_eq_M_N alpha_irr prop_alpha prop_N N (M N));
 auto with arith real.
intro; generalize (lt_not_eq n (last (M N)) H1); intro; elimtype False;
 auto with arith real.
elim (Rle_le_eq (frac_part_n_alpha n) (frac_part_n_alpha (last N))); intros;
 clear H9; apply H8; auto with arith real.
cut (N - first N <= last (M N)).
intro; apply (lt_le_trans n (N - first N) (last (M N)) H0 H1).
generalize (le_N_M alpha_irr prop_alpha prop_N N (M N) (refl_equal (M N)));
 unfold M at 1 in |- *;
 rewrite <-
  (last_eq_M_N alpha_irr prop_alpha prop_N N (M N) (refl_equal (M N)))
  ; intro; apply (le_plus_min N (first N) (last N) H1).
Qed.

(**********)
Lemma eq_after_M_N2 :
 forall N n : nat, last N <= n -> n < N -> after (M N) n = after N n.
intros; generalize (le_lt_or_eq (last N) n H); intro; elim H1; intro;
 clear H1.
rewrite (last_eq_M_N alpha_irr prop_alpha prop_N N (M N) (refl_equal (M N)))
  in H;
 generalize
  (inter31b N n H
     (lt_le_trans n N (M N) H0
        (le_N_M alpha_irr prop_alpha prop_N N (M N) (refl_equal (M N)))));
 rewrite <-
  (last_eq_M_N alpha_irr prop_alpha prop_N N (M N) (refl_equal (M N)))
  ; intro; apply (tech_fp_alp_irr alpha_irr (after (M N) n) (after N n));
 apply
  (Rge_antisym (frac_part_n_alpha (after (M N) n))
     (frac_part_n_alpha (after N n))).
apply
 (Rnot_lt_ge (frac_part_n_alpha (after (M N) n))
    (frac_part_n_alpha (after N n))); red in |- *; 
 intro; cut (0 < after (M N) n).
intro; cut (after (M N) n < N).
intro; cut (frac_part_n_alpha n < frac_part_n_alpha (after (M N) n))%R.
intro;
 generalize
  (tech_suc_N N n (lt_trans 0 (last N) n (last_0 N (prop_N N)) H2) H0
     (after (M N) n) H4 H5 H6
     (Rlt_dichotomy_converse (frac_part_n_alpha (after (M N) n))
        (frac_part_n_alpha (after N n))
        (or_introl
           (frac_part_n_alpha (after (M N) n) > frac_part_n_alpha (after N n))%R
           H3))); intro;
 generalize
  (Rlt_asym (frac_part_n_alpha (after (M N) n))
     (frac_part_n_alpha (after N n)) H3); intro; elimtype False;
 auto with arith real.
apply
 (tech_after_lt (M N) n (after (M N) n)
    (lt_trans 0 (last N) n (last_0 N (prop_N N)) H2)
    (lt_le_trans n N (M N) H0
       (le_N_M alpha_irr prop_alpha prop_N N (M N) (refl_equal (M N)))));
 auto with arith real.
rewrite H1; red in |- *; intro; apply (lt_minus_not (last N) n H2);
 auto with arith real.
rewrite H1; apply (lt_minus_p n N (last N) H0). 
rewrite H1; apply (lt_minus2 (last N) n H2).
(**)
apply
 (Rnot_lt_ge (frac_part_n_alpha (after N n))
    (frac_part_n_alpha (after (M N) n))); red in |- *; 
 intro; apply (prop_after (M N) n (after (M N) n)); 
 auto with arith real.
split with (after N n); split.
unfold after in |- *;
 case (exist_after_M (frac_part_n_alpha n) (P1 n) (P2 n) N).
intro; elim s; intros x y; elim y; intros; assumption.
intro; generalize (a (last N) (le_O_n (last N)) (last_N N (prop_N N))); intro;
 elim H4; intros; clear a H4;
 generalize
  (last_n N n (prop_N N) (lt_trans 0 (last N) n (last_0 N (prop_N N)) H2) H0
     prop_alpha); intro;
 cut (frac_part_n_alpha n = frac_part_n_alpha (last N)).
intro; generalize (tech_fp_alp_irr alpha_irr n (last N) H7).
intro; generalize (lt_not_eq (last N) n H2); intro; elimtype False;
 auto with arith real.
elim (Rle_le_eq (frac_part_n_alpha n) (frac_part_n_alpha (last N))); intros;
 clear H8; apply H7; auto with arith real.
split.
cut (after N n < N).
intro;
 apply
  (lt_le_trans (after N n) N (M N) H4
     (le_N_M alpha_irr prop_alpha prop_N N (M N) (refl_equal (M N)))).
unfold after in |- *;
 case (exist_after_M (frac_part_n_alpha n) (P1 n) (P2 n) N).
intro; elim s; intros x y; elim y; intros; elim H5; intros; assumption.
intro; apply (arith_2_0 N (prop_N N)).
split; auto with arith real.
apply
 (tech_after_lt N n (after N n)
    (lt_trans 0 (last N) n (last_0 N (prop_N N)) H2) H0);
 auto with arith real.
red in |- *; unfold after in |- *;
 case (exist_after_M (frac_part_n_alpha n) (P1 n) (P2 n) N).
intro; elim s; intros x y H4; elim y; intros; generalize (lt_not_eq 0 x H5);
 intro; auto with arith real.
intros; generalize (a (last N) (le_O_n (last N)) (last_N N (prop_N N)));
 intro; elim H5; intros; clear a H5;
 generalize
  (last_n N n (prop_N N) (lt_trans 0 (last N) n (last_0 N (prop_N N)) H2) H0
     prop_alpha); intro;
 cut (frac_part_n_alpha n = frac_part_n_alpha (last N)).
intro; generalize (tech_fp_alp_irr alpha_irr n (last N) H8); intro;
 generalize (lt_not_eq (last N) n H2); intro; auto with arith real.
elim (Rle_le_eq (frac_part_n_alpha n) (frac_part_n_alpha (last N))); intros;
 clear H9; apply H8; auto with arith real.
rewrite <- H2; rewrite (after_last prop_alpha prop_N N);
 rewrite
  (last_eq_M_N alpha_irr prop_alpha prop_N N (M N)
     (refl_equal (first N + last N))); auto with arith real;
 rewrite (after_last prop_alpha prop_N (M N)); trivial.
Qed.

End particular.
