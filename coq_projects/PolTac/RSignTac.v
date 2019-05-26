(* Ugly tacty to resolve sign condition for R *)

Require Import Reals.
Require Import RPolS.
Require Import List.
Require Import Replace2.
Require Export RGroundTac.

(* Theorems to simplify the goal 0 ? x * y and x * y ? 0 where ? is < > <= >= *)

Theorem Rle_sign_pos_pos: forall x y, (0 <= x -> 0 <= y  -> 0 <= x * y)%R.
intros x y H; apply Rmult_le_pos; auto with real.
Qed.

Theorem Rle_sign_neg_neg: forall x y, (x <= 0 -> y <= 0  -> 0 <= x * y)%R.
intros x y H1 H2; replace (x * y)%R with (-x * -y)%R; auto with real; try ring.
apply Rmult_le_pos; auto with real.
Qed.

Theorem Rle_pos_neg: forall x, (0 <= -x -> x <= 0)%R.
intros x H; rewrite <- (Ropp_involutive 0);  rewrite <- (Ropp_involutive x); auto with real.
apply Ropp_le_contravar; auto with real.
rewrite Ropp_0; auto with real.
Qed.

Theorem Rle_sign_pos_neg: forall x y: R, (0 <= x -> y <= 0  -> x * y <= 0)%R.
intros x y H1 H2; apply Rle_pos_neg; replace (- (x * y))%R with (x * (- y))%R; auto with real; try ring.
apply Rmult_le_pos; auto with real.
Qed.

Theorem Rle_sign_neg_pos: forall x y, (x <= 0 -> 0 <= y  -> x * y <= 0)%R.
intros x y H1 H2; apply Rle_pos_neg; replace (- (x * y))%R with (-x * y)%R; auto with real; try ring.
apply Rmult_le_pos; auto with real.
Qed.

Theorem Rlt_sign_pos_pos: forall x y, (0 < x -> 0 < y  -> 0 < x * y)%R.
intros; apply Rmult_lt_0_compat; auto with real.
Qed.

Theorem Rlt_sign_neg_neg: forall x y, (x < 0 -> y < 0  -> 0 < x * y)%R.
intros x y H1 H2; replace (x * y)%R with (-x * -y)%R; auto with real; try ring.
apply Rmult_lt_0_compat; auto with real.
Qed.

Theorem Rlt_pos_neg: forall x, (0 < -x -> x < 0)%R.
intros x H; rewrite <- (Ropp_involutive 0);  rewrite <- (Ropp_involutive x); auto with real.
apply Ropp_lt_contravar; auto with real.
rewrite Ropp_0; auto with real.
Qed.

Theorem Rlt_sign_pos_neg: forall x y, (0 < x -> y < 0  -> x * y < 0)%R.
intros x y H1 H2; apply Rlt_pos_neg; replace (- (x * y))%R with (x * (- y))%R; auto with real; try ring.
apply Rmult_lt_0_compat; auto.
replace 0%R with (-0)%R; auto with real.
Qed.

Theorem Rlt_sign_neg_pos: forall x y, (x < 0 -> 0 < y  -> x * y < 0)%R.
intros x y H1 H2; apply Rlt_pos_neg; replace (- (x * y))%R with (-x * y)%R; auto with real; try ring.
apply Rmult_lt_0_compat; auto with real.
Qed.



Theorem Rge_sign_neg_neg: forall x y, (0 >= x -> 0 >= y  -> x * y >= 0)%R.
intros; apply Rle_ge; apply Rle_sign_neg_neg; auto with real.
Qed.

Theorem Rge_sign_pos_pos: forall x y, (x >= 0 -> y >= 0  -> x * y >= 0)%R.
intros; apply Rle_ge; apply Rle_sign_pos_pos; auto with real.
Qed.

Theorem Rge_neg_pos: forall x, (0 >= -x -> x >= 0)%R.
intros x H; rewrite <- (Ropp_involutive 0);  rewrite <- (Ropp_involutive x); auto with real.
apply Rle_ge;apply Ropp_le_contravar; auto with real.
rewrite Ropp_0; auto with real.
Qed.

Theorem Rge_sign_neg_pos: forall x y: R, (0 >= x -> y >= 0  -> 0>= x * y)%R.
intros; apply Rle_ge; apply Rle_sign_neg_pos; auto with real.
Qed.

Theorem Rge_sign_pos_neg: forall x y, (x >= 0 -> 0 >= y  -> 0 >= x * y)%R.
intros; apply Rle_ge; apply Rle_sign_pos_neg; auto with real.
Qed.


Theorem Rgt_sign_neg_neg: forall x y, (0 > x -> 0 > y  -> x * y > 0)%R.
intros; red;  apply Rlt_sign_neg_neg; auto with real.
Qed.

Theorem Rgt_sign_pos_pos: forall x y, (x > 0 -> y > 0  -> x * y > 0)%R.
intros; red; apply Rlt_sign_pos_pos; auto with real.
Qed.

Theorem Rgt_neg_pos: forall x, (0 > -x -> x > 0)%R.
intros x H; rewrite <- (Ropp_involutive 0);  rewrite <- (Ropp_involutive x); auto with real.
red;apply Ropp_lt_contravar; auto with real.
rewrite Ropp_0; auto with real.
Qed.

Theorem Rgt_sign_neg_pos: forall x y, (0 > x -> y > 0  -> 0> x * y)%R.
intros; red; apply Rlt_sign_neg_pos; auto with real.
Qed.

Theorem Rgt_sign_pos_neg: forall x y, (x > 0 -> 0 > y  -> 0 > x * y)%R.
intros; red; apply Rlt_sign_pos_neg; auto with real.
Qed.

(* Theorems to simplify the hyp 0 ? x * y and x * y ? 0 where ? is < > <= >= *)

Theorem Rle_sign_pos_pos_rev: forall x y: R, (0 < x -> 0 <= x * y -> 0 <= y)%R.
intros x y H1 H2; case (Rle_or_lt 0 y); auto with real.
intros H3; absurd (0 <= x * y)%R; auto with real.
apply Rlt_not_le;apply Rlt_sign_pos_neg; auto.
Qed.

Theorem Rle_sign_neg_neg_rev: forall x y: R, (x < 0 -> 0 <= x * y ->  y <= 0)%R.
intros x y H1 H2; case (Rle_or_lt y  0); auto with real.
intros H3; absurd (0 <= x * y)%R; auto with real.
apply Rlt_not_le;apply Rlt_sign_neg_pos; auto.
Qed.

Theorem Rle_sign_pos_neg_rev: forall x y: R, (0 < x -> x * y <= 0 -> y <= 0)%R.
intros x y H1 H2; case (Rle_or_lt y 0); auto with real.
intros H3; absurd (x * y <= 0)%R; auto with real.
apply Rlt_not_le;apply Rlt_sign_pos_pos; auto.
Qed.

Theorem Rle_sign_neg_pos_rev: forall x y: R, (x < 0 -> x * y <= 0 ->  0 <= y)%R.
intros x y H1 H2; case (Rle_or_lt 0 y); auto with real.
intros H3; absurd (x * y <= 0)%R; auto with real.
apply Rlt_not_le;apply Rlt_sign_neg_neg; auto.
Qed.

Theorem Rge_sign_pos_pos_rev: forall x y: R, (x > 0 -> x * y >= 0 -> y >= 0)%R.
intros x y H1 H2; apply Rle_ge; apply Rle_sign_pos_pos_rev with x; auto with real.
Qed.

Theorem Rge_sign_neg_neg_rev: forall x y: R, (0 > x -> x * y  >= 0->  0 >= y)%R.
intros x y H1 H2; apply Rle_ge; apply Rle_sign_neg_neg_rev with x; auto with real.
Qed.

Theorem Rge_sign_pos_neg_rev: forall x y: R, (x > 0 -> 0 >= x * y -> 0 >= y)%R.
intros x y H1 H2; apply Rle_ge; apply Rle_sign_pos_neg_rev with x; auto with real.
Qed.

Theorem Rge_sign_neg_pos_rev: forall x y: R, (0 > x -> 0 >= x * y ->  y >= 0)%R.
intros x y H1 H2; apply Rle_ge; apply Rle_sign_neg_pos_rev with x; auto with real.
Qed.

Theorem Rlt_sign_pos_pos_rev: forall x y: R, (0 < x -> 0 < x * y -> 0 < y)%R.
intros x y H1 H2; case (Rle_or_lt y 0); auto with real.
intros H3; absurd (0 < x * y)%R; auto with real.
apply Rle_not_lt;apply Rle_sign_pos_neg; auto with real.
Qed.

Theorem Rlt_sign_neg_neg_rev: forall x y: R, (x < 0 -> 0 < x * y ->  y < 0)%R.
intros x y H1 H2; case (Rle_or_lt 0 y); auto with real.
intros H3; absurd (0 < x * y)%R; auto with real.
apply Rle_not_lt;apply Rle_sign_neg_pos; auto with real.
Qed.

Theorem Rlt_sign_pos_neg_rev: forall x y: R, (0 < x -> x * y < 0 -> y < 0)%R.
intros x y H1 H2; case (Rle_or_lt 0 y); auto with real.
intros H3; absurd (x * y < 0)%R; auto with real.
apply Rle_not_lt;apply Rle_sign_pos_pos; auto with real.
Qed.

Theorem Rlt_sign_neg_pos_rev: forall x y: R, (x < 0 -> x * y < 0 ->  0 < y)%R.
intros x y H1 H2; case (Rle_or_lt y 0); auto with real.
intros H3; absurd (x * y < 0)%R; auto with real.
apply Rle_not_lt;apply Rle_sign_neg_neg; auto with real.
Qed.

Theorem Rgt_sign_pos_pos_rev: forall x y: R, (x > 0 -> x * y > 0 -> y > 0)%R.
intros x y H1 H2; red; apply Rlt_sign_pos_pos_rev with x; auto with real.
Qed.

Theorem Rgt_sign_neg_neg_rev: forall x y: R, (0 > x -> x * y  > 0->  0 > y)%R.
intros x y H1 H2; red; apply Rlt_sign_neg_neg_rev with x; auto with real.
Qed.

Theorem Rgt_sign_pos_neg_rev: forall x y: R, (x > 0 -> 0 > x * y -> 0 > y)%R.
intros x y H1 H2; red; apply Rlt_sign_pos_neg_rev with x; auto with real.
Qed.

Theorem Rgt_sign_neg_pos_rev: forall x y: R, (0 > x -> 0 > x * y ->  y > 0)%R.
intros x y H1 H2; red; apply Rlt_sign_neg_pos_rev with x; auto with real.
Qed.

(* Theorem to simplify x * y ? x * z where ? is < > <= >= *)

Theorem Rmult_le_compat_l:
  forall n m p : R, (m <= n)%R -> (0 <= p)%R -> (p * m <= p * n)%R.
auto with real.
Qed.

Theorem Rmult_le_neg_compat_l:
  forall n m p : R, (m <= n)%R -> (p <= 0)%R -> (p * n <= p * m)%R.
intros n m p H1 H2; replace (p * n)%R with (-(-p * n))%R; auto with real; try ring.
replace (p * m)%R with (-(-p * m))%R; auto with real; try ring.
Qed.

Theorem Ropp_lt: forall n m, (m < n -> -n < -m)%R.
auto with real.
Qed.

Theorem Rmult_lt_neg_compat_l:
  forall n m p : R, (m < n)%R -> (p < 0)%R -> (p * n < p * m)%R.
intros n m p H1 H2; replace (p * n)%R with (-(-p * n))%R; auto with real; try ring.
replace (p * m)%R with (-(-p * m))%R; auto with real; try ring.
Qed.

Theorem Ropp_ge: forall n m, (m >= n -> -n >= -m)%R.
auto with real.
Qed.

Theorem Rmult_ge_compat_l:
  forall n m p : R, (m >= n)%R -> (p >= 0)%R -> (p * m >= p * n)%R.
intros n m p H H1; apply Rle_ge; auto with real.
Qed.

Theorem Rmult_ge_neg_compat_l:
  forall n m p : R, (m >= n)%R -> (0 >= p)%R -> (p * n >= p * m)%R.
intros n m p H1 H2; replace (p * n)%R with (-(-p * n))%R; auto with real; try ring.
replace (p * m)%R with (-(-p * m))%R; auto with real;try ring.
Qed.

Theorem Ropp_gt: forall n m, (m > n -> -n > -m)%R.
auto with real.
Qed.

Theorem Rmult_gt_compat_l:
  forall n m p : R, (n > m)%R -> (p > 0)%R -> (p * n > p * m)%R.
unfold Rgt; auto with real.
Qed.


Theorem Rmult_gt_neg_compat_l:
  forall n m p : R, (m > n)%R -> (0 > p)%R -> (p * n > p * m)%R.
intros n m p H1 H2; replace (p * n)%R with (-(-p * n))%R; auto with real; try ring.
replace (p * m)%R with (-(-p * m))%R; auto with real; try ring.
Qed.

(* Theorem to simplify a hyp x * y ? x * z where ? is < > <= >= *)


Theorem Rmult_le_compat_l_rev:
  forall n m p : R, (0 < p)%R -> (p * n <= p * m)%R -> (n <= m)%R.
intros n m p H H1; case (Rle_or_lt n m); auto; intros H2.
absurd (p * n <= p * m)%R; auto with real.
apply Rlt_not_le; apply Rmult_lt_compat_l; auto.
Qed.

Theorem Rmult_le_neg_compat_l_rev:
  forall n m p : R, (p < 0)%R -> (p * n <= p * m)%R -> (m <= n)%R.
intros n m p H H1; case (Rle_or_lt m n); auto; intros H2.
absurd (p * n <= p * m)%R; auto with real.
apply Rlt_not_le; apply Rmult_lt_neg_compat_l; auto.
Qed.

Theorem Rmult_lt_compat_l_rev:
  forall n m p : R, (0 < p)%R -> (p * n < p * m)%R -> (n < m)%R.
intros n m p H H1; case (Rle_or_lt m n); auto; intros H2.
absurd (p * n < p * m)%R; auto with real.
apply Rle_not_lt; apply Rmult_le_compat_l; auto with real.
Qed.

Theorem Rmult_lt_neg_compat_l_rev:
  forall n m p : R, (p < 0)%R -> (p * n < p * m)%R -> (m < n)%R.
intros n m p H H1; case (Rle_or_lt n m); auto; intros H2.
absurd (p * n < p * m)%R; auto with real.
apply Rle_not_lt; apply Rmult_le_neg_compat_l; auto with real.
Qed.

Theorem Rmult_ge_compat_l_rev:
  forall n m p : R, (p > 0)%R -> (p * n >= p * m)%R -> (n >= m)%R.
intros n m p H H1; 
 apply Rle_ge; apply Rmult_le_compat_l_rev with p; auto with real.
Qed.

Theorem Rmult_ge_neg_compat_l_rev:
  forall n m p : R, (0 > p)%R -> (p * n >= p * m)%R -> (m >= n)%R.
intros n m p H H1; 
 apply Rle_ge; apply Rmult_le_neg_compat_l_rev with p; auto with real.
Qed.

Theorem Rmult_gt_compat_l_rev:
  forall n m p : R, (p > 0)%R -> (p * n > p * m)%R -> (n > m)%R.
intros n m p H H1; 
 red; apply Rmult_lt_compat_l_rev with p; auto with real.
Qed.

Theorem Rmult_gt_neg_compat_l_rev:
  forall n m p : R, (0 > p)%R -> (p * n > p * m)%R -> (m > n)%R.
intros n m p H H1; 
 red; apply Rmult_lt_neg_compat_l_rev with p; auto with real.
Qed.

Definition Rsign_type := fun (x y:list R) => Prop.

Definition Rsign_cons : forall x y, (Rsign_type  x y) := fun x y => True.

Ltac Rsign_push term1 term2 := generalize (Rsign_cons term1 term2); intro.

Ltac Rsign_le term :=
  match term with 
    (?X1 * ?X2)%R =>  Rsign_le X1;
                             match goal with 
                             H1: (Rsign_type ?s1 ?s2) |- _ =>
                                    Rsign_le X2;
                                   match goal with 
                                      H2: (Rsign_type ?s3 ?s4) |- _ => clear H1 H2;
                                              let s5 := eval unfold List.app in (s1++s3) in
                                              let s6 := eval unfold List.app in (s2++s4) in
                                               Rsign_push s5 s6
                                   end
                              end
| _ =>  let H1 := fresh "H" in
    (((assert (H1: (0 <= term)%R); [auto with real; fail | idtac])
      ||
     (assert (H1: (term <= 0)%R); [auto with real; fail | idtac])); clear H1;
         Rsign_push (term::nil) (@nil R)) || Rsign_push (@nil R) (term::nil)
end.

Ltac Rsign_lt term :=
  match term with 
    (?X1 * ?X2)%R =>  Rsign_lt X1;
                             match goal with 
                             H1: (Rsign_type ?s1 ?s2) |- _ =>
                                    Rsign_lt X2;
                                   match goal with 
                                      H2: (Rsign_type ?s3 ?s4) |- _ => clear H1 H2;
                                              let s5 := eval unfold List.app in (s1++s3) in
                                              let s6 := eval unfold List.app in (s2++s4) in
                                               Rsign_push s5 s6
                                   end
                              end
| _ =>  let H1 := fresh "H" in
    (((assert (H1: (0 < term)%R); [auto with real; fail | idtac])
      ||
     (assert (H1: (term < 0)%R); [auto with real; fail | idtac])); clear H1;
         Rsign_push (term::nil) (@nil R)) || Rsign_push (@nil R) (term::nil)
end.

Ltac Rsign_top0 :=
  match goal with
  |- (0 <= ?X1)%R => Rsign_le  X1
| |- (?X1 <= 0)%R => Rsign_le  X1
| |- (0 < ?X1)%R => Rsign_lt  X1
| |- (?X1 < 0)%R => Rsign_le  X1
| |- (0 >= ?X1)%R => Rsign_le  X1
| |- (?X1 >= 0)%R => Rsign_le  X1
| |- (0 > ?X1 )%R => Rsign_lt X1
| |- (?X1 > 0)%R => Rsign_le  X1
  end.


Ltac Rsign_top :=
  match goal with
| |- (?X1 * _ <= ?X1 * _)%R => Rsign_le  X1
| |- (?X1 * _ < ?X1 * _)%R => Rsign_le  X1
| |- (?X1 * _ >= ?X1 * _)%R => Rsign_le  X1
| |- (?X1 * _ > ?X1 * _)%R => Rsign_le  X1
  end.


Ltac Rhyp_sign_top0 H:=
  match type of H with
   (0 <= ?X1)%R => Rsign_lt  X1
|  (?X1 <= 0)%R => Rsign_lt  X1
|  (0 < ?X1)%R => Rsign_lt  X1
|  (?X1 < 0)%R => Rsign_lt X1
|  (0 >= ?X1)%R => Rsign_lt  X1
|  (?X1 >= 0)%R => Rsign_lt  X1
|  (0 > ?X1 )%R => Rsign_lt X1
|  (?X1 > 0)%R => Rsign_lt  X1
  end.


Ltac Rhyp_sign_top H :=
  match type of H with
|  (?X1 * _ <= ?X1 * _)%R => Rsign_lt  X1
|  (?X1 * _ < ?X1 * _)%R => Rsign_lt X1
|  (?X1 * _ >= ?X1 * _)%R => Rsign_lt  X1
|  (?X1 * _ > ?X1 * _)%R => Rsign_lt  X1
|  ?X1 => generalize H
  end.

Ltac Rsign_get_term g :=
  match g with
   (0 <= ?X1)%R =>  X1
|  (?X1 <= 0)%R => X1
|  (?X1 * _ <= ?X1 * _)%R =>  X1
|  (0 < ?X1)%R =>  X1
|  (?X1 < 0)%R => X1
|  (?X1 * _ < ?X1 * _)%R =>  X1
|  (0 >= ?X1)%R => X1
|  (?X1 >= 0)%R => X1
|  (?X1 * _ >= ?X1 * _)%R =>  X1
|  (?X1 * _  >= _)%R => X1
|  (0 > ?X1)%R => X1
|  (?X1 > 0)%R => X1
|  (?X1 * _ > ?X1 * _)%R =>  X1
  end.

Ltac Rsign_get_left g :=
  match g with
|  (_ * ?X1 <=  _)%R =>  X1
|  (_ * ?X1 <  _)%R =>  X1
|  (_ * ?X1 >=  _)%R =>  X1
|  (_ * ?X1 >  _)%R =>  X1
end.

Ltac Rsign_get_right g :=
  match g with
|  (_ <= _ * ?X1)%R =>  X1
|  (_ < _ * ?X1)%R =>  X1
|  (_ >= _ * ?X1)%R =>  X1
|  (_ > _ * ?X1)%R =>  X1
end.

Fixpoint mkRprodt (l: list R)(t:R) {struct l}: R :=
match l with nil => t | e::l1 => (e * mkRprodt l1 t)%R end.

Fixpoint mkRprod (l: list R) : R :=
match l with nil => 1%R  | e::nil => e | e::l1 => (e * mkRprod l1)%R end.


(* Tactic for 0 ? x * y where ? is < > <= >= *)

Ltac rsign_tac_aux0 := 
match goal with
  |- (0 <= ?X1 * ?X2)%R =>
  let H1 := fresh "H" in
    ((assert (H1: (0 <= X1)%R); auto with real; apply Rle_sign_pos_pos)
      ||
     (assert (H1: (X1 <= 0)%R); auto with real; apply Rle_sign_neg_neg); try rsign_tac_aux0; clear H1)
| |- (?X1 * ?X2 <= 0)%R =>
  let H1 := fresh "H" in
    ((assert (H1: (0 <= X1)%R); auto with real; apply Rle_sign_pos_neg)
      ||
     (assert (H1: (X1 <= 0)%R); auto with real; apply Rle_sign_neg_pos); try rsign_tac_aux0; clear H1)
| |- (0 < ?X1 * ?X2)%R =>
  let H1 := fresh "H" in
    ((assert (H1: (0 < X1)%R); auto with real; apply Rlt_sign_pos_pos)
      ||
     (assert (H1: (X1 < 0)%R); auto with real; apply Rlt_sign_neg_neg); try rsign_tac_aux0; clear H1)
| |- (?X1 * ?X2 < 0)%R =>
  let H1 := fresh "H" in
    ((assert (H1: (0 < X1)%R); auto with real; apply Rlt_sign_pos_neg)
      ||
     (assert (H1: (X1 < 0)%R); auto with real; apply Rlt_sign_neg_pos); try rsign_tac_aux0; clear H1)
 | |- (?X1 * ?X2 >= 0)%R =>
  let H1 := fresh "H" in
    ((assert (H1: (0 >= X1)%R); auto with real; apply Rge_sign_neg_neg)
      ||
     (assert (H1:  (X1 >= 0)%R); auto with real; apply Rge_sign_pos_pos); try rsign_tac_aux0; clear H1)
| |- (0 >= ?X1 * ?X2)%R =>
  let H1 := fresh "H" in
    ((assert (H1: (X1 >= 0)%R); auto with real; apply Rge_sign_pos_neg)
      ||
     (assert (H1: (0 >= X1)%R); auto with real; apply Rge_sign_neg_pos); try rsign_tac_aux0; clear H1)
| |- (0 > ?X1 * ?X2)%R =>
  let H1 := fresh "H" in
    ((assert (H1: (0 > X1)%R); auto with real; apply Rgt_sign_neg_pos)
      ||
     (assert (H1: (X1 > 0)%R); auto with real; apply Rgt_sign_pos_neg); try rsign_tac_aux0; clear H1)
| |- (?X1 * ?X2 > 0)%R =>
  let H1 := fresh "H" in
    ((assert (H1: (0 > X1)%R); auto with real; apply Rgt_sign_neg_neg)
      ||
     (assert (H1: (X1 > 0)%R); auto with real; apply Rgt_sign_pos_pos); try rsign_tac_aux0; clear H1)
|
 _ => auto with real; fail 1 "rsign_tac_aux"
end.

Ltac rsign_tac0 := Rsign_top0;
  match goal with
    H1: (Rsign_type ?s1 ?s2) |- ?g => clear H1;
    let s := eval unfold mkRprod, mkRprodt in 
                  (mkRprodt s1 (mkRprod s2)) in
    let t := Rsign_get_term g in
         replace t with s; [try rsign_tac_aux0 | try ring]; auto with real
  end.

(* tatic for hyp 0 ? x * y where ? is < > <= >= *)

Ltac hyp_rsign_tac_aux0 H := 
match  type of H  with
   (0 <= ?X1 * ?X2)%R =>
  let H1 := fresh "H" in
    ((assert (H1: (0 < X1)%R); auto with real; generalize (Rle_sign_pos_pos_rev  _ _ H1 H)
      ||
     (assert (H1: (X1 < 0)%R); auto with real; generalize (Rle_sign_neg_neg_rev  _ _ H1 H))); 
     clear H; intros H; try hyp_rsign_tac_aux0 H; clear H1)
|  (?X1 * ?X2 <= 0)%R =>
  let H1 := fresh "H" in
    ((assert (H1: (0 < X1)%R); auto with real; generalize (Rle_sign_pos_neg_rev  _ _ H1 H))
      ||
     (assert (H1: (X1 <= 0)%R); auto with real; generalize (Rle_sign_neg_pos_rev  _ _ H1 H)); 
      clear H; intros H; try hyp_rsign_tac_aux0 H; clear H1)
|  (0 < ?X1 * ?X2)%R =>
  let H1 := fresh "H" in
    ((assert (H1: (0 < X1)%R); auto with real; generalize (Rlt_sign_pos_pos_rev _  _ H1 H))
      ||
     (assert (H1: (X1 < 0)%R); auto with real; generalize (Rlt_sign_neg_neg_rev _ _ H1 H)); 
      clear H; intros H; try hyp_rsign_tac_aux0 H; clear H1)
|  (?X1 * ?X2 < 0)%R =>
  let H1 := fresh "H" in
    ((assert (H1: (0 < X1)%R); auto with real; generalize (Rlt_sign_pos_neg_rev _ _ H1 H))
      ||
     (assert (H1: (X1 < 0)%R); auto with real; generalize (Rlt_sign_neg_pos_rev _ _ H1 H)); 
     clear H; intros H; try hyp_rsign_tac_aux0 H; clear H1)
 |  (?X1 * ?X2 >= 0)%R =>
  let H1 := fresh "H" in
    ((assert (H1: (0 >X1)%R); auto with real; generalize (Rge_sign_neg_neg_rev _ _ H1 H))
      ||
     (assert (H1:  (X1 > 0)%R); auto with real; generalize (Rge_sign_pos_pos _ _ H1 H));
      clear H; intros H; try hyp_rsign_tac_aux0 H; clear H1)
|  (0 >= ?X1 * ?X2)%R =>
  let H1 := fresh "H" in
    ((assert (H1: (X1 > 0)%R); auto with real; generalize (Rge_sign_pos_neg _ _ H1 H))
      ||
     (assert (H1: (0 > X1)%R); auto with real; generalize (Rge_sign_neg_pos _ _ H1 H));
     clear H; intros H; try hyp_rsign_tac_aux0 H; clear H1)
|  (0 > ?X1 * ?X2)%R =>
  let H1 := fresh "H" in
    ((assert (H1: (0 > X1)%R); auto with real; generalize (Rgt_sign_neg_pos _ _ H1 H))
      ||
     (assert (H1: (X1 > 0)%R); auto with real; generalize (Rgt_sign_pos_neg _ _ H1 H));
     clear H; intros H; try hyp_rsign_tac_aux0 H; clear H1)
|  (?X1 * ?X2 > 0)%R =>
  let H1 := fresh "H" in
    ((assert (H1: (0 > X1)%R); auto with real; generalize (Rgt_sign_neg_neg _ _ H1 H))
      ||
     (assert (H1: (X1 > 0)%R); auto with real; generalize (Rgt_sign_pos_pos _ _ H1 H));
     clear H; intros H; try hyp_rsign_tac_aux0 H; clear H1)
|
 _ => auto with real; fail 1 "hyp_rsign_tac_aux0"
end.

Ltac hyp_rsign_tac0 H := Rhyp_sign_top0 H;
  match goal with
    H1: (Rsign_type ?s1 ?s2) |- ?g => clear H1;
    let s := eval unfold mkRprod, mkRprodt in 
                  (mkRprodt s1 (mkRprod s2)) in
    let t := Rsign_get_term g in
         replace t with s in H; [try hyp_rsign_tac_aux0 H | try ring]; auto with real
  end.

(* Tactic for goal x1 * x2 ? x1 * x3 where ? is < > <= >= *)

Ltac rsign_tac_aux := 
match goal with
 | |- (?X1 * ?X2 <= ?X1 * ?X3)%R =>
  let H1 := fresh "H" in
    ((assert (H1: (0 <= X1)%R); auto with real; apply Rmult_le_compat_l)
      ||
     (assert (H1: (X1 <= 0)%R); auto with real; apply Rmult_le_neg_compat_l); try rsign_tac_aux; clear H1)
| |- (?X1 * ?X2 < ?X1 * ?X3)%R =>
  let H1 := fresh "H" in
    ((assert (H1: (0 <= X1)%R); auto with real; apply Rmult_lt_compat_l)
      ||
     (assert (H1: (X1 <= 0)%R); auto with real; apply Rmult_lt_neg_compat_l); try rsign_tac_aux; clear H1) 
 | |- (?X1 * ?X2 >= ?X1 * ?X3)%R =>
  let H1 := fresh "H" in
    ((assert (H1: (X1 >= 0)%R); auto with real; apply Rmult_ge_compat_l)
      ||
     (assert (H1:  (0 >= X1)%R); auto with real; apply Rmult_ge_neg_compat_l); try rsign_tac_aux; clear H1)
| |- (?X1 * ?X2 > ?X1 * ?X3)%R =>
  let H1 := fresh "H" in
    ((assert (H1: (0 <= X1)%R); auto with real; apply Rmult_lt_compat_l)
      ||
     (assert (H1: (X1 <= 0)%R); auto with real; apply Rmult_lt_neg_compat_l); try rsign_tac_aux; clear H1)
|
 _ => auto with real; fail 1 "Rsign_tac_aux"
end.

Ltac rsign_tac := rsign_tac0 || (Rsign_top;
  match goal with
    H1: (Rsign_type ?s1 ?s2) |- ?g => clear H1;
    let s := eval unfold mkRprod, mkRprodt in 
                  (mkRprodt s1 (mkRprod s2)) in
    let t := Rsign_get_term g in
    let l := Rsign_get_left g in
    let r := Rsign_get_right g in
    let sl := eval unfold mkRprod, mkRprodt in 
                  (mkRprodt s1 (Rmult (mkRprod s2) l)) in
    let sr := eval unfold mkRprod, mkRprodt in 
                  (mkRprodt s1 (Rmult (mkRprod s2) r)) in
         replace2_tac (Rmult t l) (Rmult t r) sl sr; [rsign_tac_aux | ring | ring]
  end).

(* Tactic for hyp x1 * x2 ? x1 * x3 where ? is < > <= >= *)

Ltac hyp_rsign_tac_aux H := 
match type of H with
 | (?X1 * ?X2 <= ?X1 * ?X3)%R =>
  let H1 := fresh "H" in
    ((assert (H1: (0 < X1)%R); auto with real; generalize (Rmult_le_compat_l_rev _ _ _ H1 H))
      ||
     (assert (H1: (X1 < 0)%R); auto with real; generalize (Rmult_le_neg_compat_l_rev _ _ _ H1 H)); 
     clear H; intros H; try hyp_rsign_tac_aux H; clear H1)
|  (?X1 * ?X2 < ?X1 * ?X3)%R =>
  let H1 := fresh "H" in
    ((assert (H1: (0 < X1)%R); auto with real; generalize (Rmult_lt_compat_l_rev _ _ _ H1 H))
      ||
     (assert (H1: (X1 < 0)%R); auto with real; generalize (Rmult_lt_neg_compat_l_rev _ _ _ H1 H)); 
    clear H; intros H; try hyp_rsign_tac_aux H; clear H1) 
 |  (?X1 * ?X2 >= ?X1 * ?X3)%R =>
  let H1 := fresh "H" in
    ((assert (H1: (X1 > 0)%R); auto with real; generalize (Rmult_ge_compat_l_rev _ _ _ H1 H))
      ||
     (assert (H1:  (0 > X1)%R); auto with real; generalize (Rmult_ge_neg_compat_l_rev _ _ _ H1 H)); 
    clear H; intros H; try hyp_rsign_tac_aux H; clear H1)
| (?X1 * ?X2 > ?X1 * ?X3)%R =>
  let H1 := fresh "H" in
    ((assert (H1: (0 < X1)%R); auto with real; generalize (Rmult_gt_compat_l_rev _ _ _ H1 H))
      ||
     (assert (H1: (X1 < 0)%R); auto with real; generalize (Rmult_gt_neg_compat_l_rev _ _ _ H1 H)); 
     clear H; intros H; try hyp_rsign_tac_aux H; clear H1)
|
 _ => auto with real; fail 0 "Rhyp_sign_tac_aux"
end.

Ltac hyp_rsign_tac H := hyp_rsign_tac0  H|| (Rhyp_sign_top H;
  match goal with
    H1: (Rsign_type ?s1 ?s2) |- _ => clear H1;
    let s := eval unfold mkRprod, mkRprodt in 
                  (mkRprodt s1 (mkRprod s2)) in
    let g := type of H in
    let t := Rsign_get_term g in
    let l := Rsign_get_left g in
    let r := Rsign_get_right g in
    let sl := eval unfold mkRprod, mkRprodt in 
                  (mkRprodt s1 (Rmult (mkRprod s2) l)) in
    let sr := eval unfold mkRprod, mkRprodt in 
                  (mkRprodt s1 (Rmult (mkRprod s2) r)) in
         (generalize H; replace2_tac (Rmult t l) (Rmult t r) sl sr; [clear H; intros H; try hyp_rsign_tac_aux H| ring | ring])
  end).

Section Test.

Let test : forall a b c, (0 < a -> a * b < a * c -> b < c)%R.
intros a b c H1 H.
hyp_rsign_tac H.
Qed.


Let test1 : forall a b c, (a < 0 -> a * b < a * c -> c < b)%R.
intros a b c H H1.
hyp_rsign_tac H1.
Qed.

Let test2 : forall a b c, (0 < a -> a * b <= a * c -> b <= c)%R.
intros a b c H H1.
hyp_rsign_tac H1.
Qed.

Let test3 : forall a b c, (0 >  a ->  (a * b) >= (a * c) -> c >= b)%R.
intros a b c H H1.
hyp_rsign_tac H1.
Qed.

End Test.
