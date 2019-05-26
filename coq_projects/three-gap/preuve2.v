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
(*                               preuve2.v                                  *)
(****************************************************************************)

(*********************************************************)
(*                 Intermediate proof 2                  *)
(*                                                       *)
(*********************************************************)

Require Export preuve1.
(*********************************************************)

Section Three.
Hypothesis alpha_irr : forall n p : Z, (alpha * IZR p)%R <> IZR n.
Hypothesis prop_alpha : (0 < alpha)%R /\ (alpha < 1)%R.
Hypothesis prop_N : forall N : nat, N >= 2.

(**********)
Lemma three_gap1 :
 forall N n : nat, 0 < n -> n < N - first N -> after N n = n + first N.
intros; generalize (inter31a alpha_irr prop_alpha prop_N N n); intros;
 generalize (eq_after_M_N1 alpha_irr prop_alpha prop_N N n H H0); 
 intro; rewrite <- H2; cut (n < last (M N)).
intro;
 rewrite
  (first_eq_M_N alpha_irr prop_alpha prop_N N (M N)
     (refl_equal (first N + last N))); apply (H1 H H3).
generalize
 (le_N_M alpha_irr prop_alpha prop_N N (M N) (refl_equal (first N + last N)));
 intro; generalize (le_lt_or_eq N (first N + last N) H3); 
 intro; elim H4; intro.
cut (N - first N < last (M N)).
intro; apply (lt_trans n (N - first N) (last (M N)) H0 H6).
rewrite <-
 (last_eq_M_N alpha_irr prop_alpha prop_N N (M N)
    (refl_equal (first N + last N)));
 apply (lt_plus_minus N (first N) (last N) (first_N N (prop_N N)) H5).
rewrite <-
 (last_eq_M_N alpha_irr prop_alpha prop_N N (M N)
    (refl_equal (first N + last N))); cut (M N = first N + last N).
intro; rewrite <- H6 in H5; rewrite H5 in H0;
 rewrite <-
  (first_eq_M_N alpha_irr prop_alpha prop_N N (M N)
     (refl_equal (first N + last N))) in H0;
 rewrite (plus_minus (M N) (first N) (last N) H6); 
 auto with arith real.
auto with arith real.
Qed.

(**********)
Lemma three_gap2 :
 forall N n : nat,
 N - first N <= n -> n < last N -> after N n = n + first N - last N.
intros; apply sym_equal;
 apply (tech_after alpha_irr N n (n + first N - last N)).
generalize (first_N N (prop_N N)); intro;
 generalize (lt_minus2 (first N) N H1); intro;
 apply (lt_le_trans 0 (N - first N) n H2 H).
generalize (last_N N (prop_N N)); intro; apply (lt_trans n (last N) N H0 H1).
auto with arith real.
generalize (plus_lt_compat_r n (last N) (first N) H0); intro;
 generalize (lt_reg_minus (n + first N) (last N + first N) (last N) H1);
 intro; rewrite (minus_plus (last N) (first N)) in H2;
 cut (last N <= n + first N).
intro;
 apply
  (lt_trans (n + first N - last N) (first N) N (H2 H3) (first_N N (prop_N N))).
clear H1 H2; generalize (le_minus_plus N (first N) n H); intro;
 apply (le_trans (last N) N (n + first N) (last_N01 N) H1).
apply (tech1 alpha_irr prop_alpha prop_N N n H H0).
generalize (tech_suc_M alpha_irr prop_alpha prop_N N n H H0);
 auto with arith real.
Qed.

(**********)
Lemma three_gap3 :
 forall N n : nat, last N <= n -> n < N -> after N n = n - last N.
intros; generalize (inter31b alpha_irr prop_alpha prop_N N n); intros;
 generalize (eq_after_M_N2 alpha_irr prop_alpha prop_N N n H H0); 
 intro; rewrite <- H2; cut (n < M N).
intro;
 rewrite
  (last_eq_M_N alpha_irr prop_alpha prop_N N (M N)
     (refl_equal (first N + last N)));
 rewrite
  (last_eq_M_N alpha_irr prop_alpha prop_N N (M N)
     (refl_equal (first N + last N))) in H; apply (H1 H H3).
generalize
 (le_N_M alpha_irr prop_alpha prop_N N (M N) (refl_equal (first N + last N)));
 intro; unfold M in |- *; apply (lt_le_trans n N (first N + last N) H0 H3).
Qed.

End Three.