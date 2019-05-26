(************************************************************************)
(* Copyright 2006 Milad Niqui                                           *)
(* This file is distributed under the terms of the                      *)
(* GNU Lesser General Public License Version 2.1                        *)
(* A copy of the license can be found at                                *)
(*                  <http://www.gnu.org/licenses/lgpl-2.1.html>         *)
(************************************************************************)


Require Export Qsyntax.
Require Export Field_Theory_Q.

Lemma Qmult_absorb_nonzero_r: forall x y : Q, x * y <> Zero -> y <> Zero.
Proof.
 abstract (intros x y H1 H2; apply H1; subst; field; assumption).
Qed.

Lemma Qmult_absorb_nonzero_l: forall x y : Q, x * y <> Zero -> x <> Zero.
Proof.
 abstract (intros x y H1 H2; apply H1; subst; field; assumption).
Qed.

Lemma Qle_Qminus_Zero: forall x y: Q, x <= y -> Zero <= y-x.
Proof.
 intros x y H;
 stepl (-x+x); try ring;
 stepr (-x+y); try ring;
 apply (Qle_plus_plus (-x) (-x) x y (Qle_reflexive (-x)) H). 
Qed.

Lemma Qle_Qminus_Zero_neg: forall x y : Q, x <= y -> x-y <= Zero.
Proof.
 intros x y H;
 stepr (-y+y); try ring;
 stepl (-y+x); try ring;
 apply Qle_plus_plus; trivial. 
Qed. 

Lemma Qle_Zero_Qminus_neg: forall x y : Q, x-y <= Zero -> x <= y.
Proof.
 intros x y H;
 stepl (y+(x-y)); try ring;
 stepr (y+Zero); try ring;
 apply Qle_plus_plus; trivial. 
Qed.


Lemma Qle_Zero_Qminus: forall x y: Q,  Zero <= y-x -> x <= y.
Proof.
 intros x y H;
 stepl (x+Zero); try ring;
 stepr (x+(y-x)); try ring;
 apply (Qle_plus_plus x x Zero (y-x) (Qle_reflexive x) H).
Qed.


Lemma Qmult_mult_nonneg: forall x:Q, Zero <= x*x.
Proof.
 let T_local := apply Qlt_le_weak; apply Qsgn_9; rewrite Qsgn_15; reflexivity in
 (intros [|x|x];
 [ apply Qle_reflexive
 | T_local
 | T_local
 ]).
Qed.

Lemma Qmult_mult_pos: forall x:Q, x<> Zero -> Zero < x*x.
Proof.
 intros [|x|x] Hx;
 [ apply False_ind; apply Hx
 | apply Qsgn_9; rewrite Qsgn_15
 | apply Qsgn_9; rewrite Qsgn_15
 ]; reflexivity.
Qed.

Lemma Qlt_opp:forall x y, Qopp x < Qopp y -> y < x.
Proof.
 intros [|x|x] [|y|y]; simpl; intro Hxy; trivial;
 inversion_clear Hxy; constructor; trivial.
Qed.

Lemma Qlt_plus:forall x y z : Q, x < y -> z + x < z + y.
Proof.
 intros x y z; unfold Qlt; apply Qgt_plus.
Qed.

Lemma Qlt_Qminus_Zero: forall x y : Q, x < y -> Zero < y - x.
Proof.
 intros x y H;
 stepl (-x+x); try ring;
 stepr (-x+y); try ring;
 apply Qlt_plus; assumption.
Qed. 

Lemma Qlt_Qminus_Zero_neg: forall x y : Q, x < y -> x-y < Zero.
Proof.
 intros x y H;
 stepr (-y+y); try ring;
 stepl (-y+x); try ring;
 apply Qlt_plus; assumption.
Qed. 

Lemma Qlt_Zero_Qminus_neg: forall x y : Q, x-y < Zero -> x < y.
Proof.
 intros x y H;
 stepl (y+(x-y)); try ring;
 stepr (y+Zero); try ring.
 apply Qle_lt_reg; trivial. 
Qed.

Lemma Qlt_reg_mult_pos_l: forall x y z : Q, Zero < x -> y < z -> x * y < x * z.
Proof.
 intros x y z Hx Hyz;
 apply Qlt_Zero_Qminus;
 stepr (x*(z-y)); try ring;
 apply Qlt_mult_pos_pos; trivial;
 apply Qlt_Qminus_Zero; assumption.
Qed. 

Lemma Qlt_reg_mult_pos_r: forall x y z : Q, Zero < x -> y < z -> y * x < z * x.
Proof.
 intros x y z Hx Hyz;
 apply Qlt_Zero_Qminus;
 stepr (x*(z-y)); try ring;
 apply Qlt_mult_pos_pos; trivial;
 apply Qlt_Qminus_Zero; assumption.
Qed. 

Lemma Qlt_reg_mult_neg_l: forall x y z : Q, x < Zero -> y < z -> x * z < x * y.
Proof.
 intros x y z Hx Hyz;
 apply Qlt_Zero_Qminus_neg;
 stepl (x*(z-y)); try ring;
 apply Qlt_mult_neg_pos; trivial;
 apply Qlt_Qminus_Zero; assumption.
Qed. 

Lemma Qlt_reg_mult_neg_r: forall x y z : Q, x < Zero -> y < z -> z * x < y * x.
Proof.
 intros x y z Hx Hyz;
 apply Qlt_Zero_Qminus_neg;
 stepl (x*(z-y)); try ring;
 apply Qlt_mult_neg_pos; trivial;
 apply Qlt_Qminus_Zero; assumption.
Qed. 

Lemma Qdiv_Qmult_pos:forall x y z t: Q, Zero < z*t -> x/z < y/t -> x*t < y*z. 
Proof.
 abstract (intros x y z t Hzt Hxyzt;
 stepl (z*t*(x/z)); [stepr (z*t*(y/t)) | idtac];
 [apply (Qlt_reg_mult_pos_l (z*t) (x/z) (y/t) Hzt Hxyzt) | field | field ];
 [ apply Qmult_absorb_nonzero_r with z
 | apply Qmult_absorb_nonzero_l with t
 ];
 apply Qlt_not_eq; assumption).
Qed.

Lemma Qinv_involutive:forall x:Q, x<>Zero -> Qinv (Qinv x) = x.
Proof.
 intros x Hx; field; auto. 
Qed.

Lemma Qmult_Qdiv_pos:forall x y z t: Q, Zero < z*t -> x*t < y*z -> x/z < y/t.
Proof.
 intros x y z t Hzt Hxyzt;
 generalize (Qlt_not_eq _ _ Hzt); intro H_zt_nonzero;
 unfold Qdiv;
 apply Qdiv_Qmult_pos;
 [ stepr (Qinv (z*t));  [apply Qinv_pos; assumption|field]; split 
 | unfold Qdiv;
   repeat rewrite Qinv_involutive; trivial
 ];
 solve[apply Qmult_absorb_nonzero_r with z; trivial] || apply Qmult_absorb_nonzero_l with t; trivial.
Qed.

Lemma Qlt_Qopp_pos: forall x: Q, x < Zero -> Zero < - x.
Proof.
 abstract (intros x Hx; apply Qlt_opp; stepl x; auto; try ring).
Qed.

Lemma Qlt_Qopp_neg: forall x: Q, Zero < x -> -x < Zero.
Proof.
 intros x Hx; apply Qlt_opp; stepr x; auto; try ring.
Qed.

Lemma Qmult_one_left:forall x : Q, Qone * x = x.
Proof.
 intros; field.
Qed.

Lemma Qdiv_Qone_Qone: Qdiv Qone Qone = Qone.
Proof.
 unfold Qdiv; rewrite Qmult_one_right; trivial.
Qed.

Lemma Qinv_Qdiv_Qone:forall x, Qinv x = Qone/x. 
Proof.
 intro x; unfold Qdiv; rewrite Qmult_one_left; reflexivity.
Qed.

Lemma Qminus_Qdiv:forall x y z t, z<>Zero -> t<>Zero -> x/z - y/t = (x*t-y*z)/(z*t).
Proof.
 intros x y z t Hz Ht; field; split; assumption. 
Qed.

Lemma Qplus_Qdiv:forall x y z t, z<>Zero -> t<>Zero -> x/z + y/t = (x*t+y*z)/(z*t).
Proof.
 intros x y z t Hz Ht; field; split; assumption.
Qed.

Definition Qmult_Qinv_l:= Qinv_defT. 

Lemma Qmult_Qinv_r:forall x, x <> Zero -> x * (Qinv x) = Qone.
Proof.
 intros x Hx; field; trivial.
Qed.

Lemma Qinv_Qmult:forall x y, x<>Zero -> y <> Zero -> Qinv (x*y) = (Qinv x)*(Qinv y).
Proof.
 intros x y Hx Hy; field; split; assumption. 
Qed.

Lemma Qplus_Qdiv_one:forall p q, q<> Zero -> (p+q) / q = p/q + Qone.
Proof.
 intros p q Hq; field; trivial.
Qed.

Lemma Qdiv_Qopp_numerator: forall x y : Q, y<> Zero -> Qdiv (-x) y = - (Qdiv x  y).
Proof.
 intros x y Hy; field; trivial.
Qed.

Lemma Qdiv_Qopp_denomintor: forall x y : Q, y<> Zero -> Qdiv x (-y) = - (Qdiv x  y).
Proof.
 intros x y Hy; field; split; trivial; apply Qopp_resp_nonzero; trivial.
Qed.

Lemma Qdiv_Qdiv_simplify:forall x y z, z<> Zero -> y<> Zero -> (x/z)/(y/z) = x/y.
Proof.
 intros x y z Hz Hy; field; split; trivial; apply Qinv_resp_nonzero; trivial. 
Qed.

Lemma Qdiv_Qmult_Qone_denominator:forall x y z, z<>Zero -> y<>Zero -> x/(y*z) = (x/y)*(Qone/z).
Proof.
 intros x y z Hx Hy; field; split; assumption. 
Qed.


Lemma Qdiv_Qmult_numerator_l: forall (x y z:Q), y<>Zero -> z*(x/y)=(z*x)/y.
Proof.
 intros x y z Hy; field; auto.
Qed.

Lemma Qdiv_Qmult_numerator_r: forall (x y z:Q), y<>Zero -> (x/y)*z=(x*z)/y.
Proof.
 intros x y z Hy; field; auto.
Qed.


Lemma Qlt_Qmult_cancel_l: forall x y z : Q, Zero < x -> x * y < x * z -> y < z.
Proof.
 intros x y z Hx Hxy;
 apply Qlt_Zero_Qminus;
 apply Qsgn_9;
 transitivity (Zmult (Qsgn x) (Qsgn (z-y)));
 [ rewrite (Qsgn_7 _ Hx); auto with zarith
 | rewrite <- Qsgn_15;
   apply Qsgn_7;
   stepr (x*z - x*y); try ring;
   apply Qlt_Qminus_Zero; trivial
 ].
Qed.

Lemma Qlt_Qmult_cancel_r: forall x y z : Q, Zero < x -> y * x< z * x -> y < z.
Proof.
 intros x y z Hx Hxy;
 apply Qlt_Zero_Qminus;
 apply Qsgn_9;
 transitivity (Zmult (Qsgn x) (Qsgn (z-y)));
 [ rewrite (Qsgn_7 _ Hx); auto with zarith
 | rewrite <- Qsgn_15;
   apply Qsgn_7;
   stepr (z*x - y*x); try ring;
   apply Qlt_Qminus_Zero; trivial
 ].
Qed.

Definition Qmult_resp_Qlt_pos_r:= Qlt_Qmult_cancel_r :  forall t x y : Q, Zero < t -> x * t < y * t -> x < y.

Definition Qmult_resp_Qlt_pos_l:= Qlt_Qmult_cancel_l: forall t x y : Q, Zero < t -> t * x < t * y -> x < y.

Lemma Qmult_resp_Qlt_neg_r: forall t x y : Q, t < Zero -> x * t < y * t -> y < x.
Proof.
 intros t x y Ht Hxt; destruct (Qtrichotomy_inf x y) as [[Hxy|Hxy]|Hxy]; trivial; contradiction (Qlt_irreflexive (x*t));
 [ apply Qlt_transitive with (y*t); trivial; apply Qlt_reg_mult_neg_r
 | rewrite <- Hxy in Hxt]
 ; trivial. 
Qed.

Lemma Qmult_resp_Qlt_neg_l: forall t x y : Q, t < Zero -> t * x < t * y -> y < x.
Proof.
 intros t x y Ht Hxt; destruct (Qtrichotomy_inf x y) as [[Hxy|Hxy]|Hxy]; trivial; contradiction (Qlt_irreflexive (t*x));
 [ apply Qlt_transitive with (t*y); trivial; apply Qlt_reg_mult_neg_l
 | rewrite <- Hxy in Hxt]
 ; trivial. 
Qed.


Lemma Qeq_Qminus : forall x y, x=y -> x-y=Zero.
Proof.
 intros x y Hxy; rewrite Hxy; ring.
Qed.

Lemma Qminus_Qeq : forall x y, x-y=Zero -> x=y.
Proof.
 intros x y Hxy; transitivity (y+(x-y)); solve [ring] || (rewrite Hxy; auto).
Qed.

Lemma Qlt_not_eq': forall x y : Q, x < y -> x <> y.
Proof.
 intros x y Hxy; apply sym_not_eq; apply Qlt_not_eq; assumption. 
Qed.

Lemma Qinv_neg: forall q : Q, q<Zero -> Qinv q< Zero.
Proof.
 intros q Hq; apply Qinv_2; rewrite Qinv_involutive; trivial; apply Qlt_not_eq'; assumption. 
Qed. 

Lemma Qle_Qopp_pos:forall q : Q, q<= Zero -> Zero<= Qopp q.
Proof.
 intros q Hq; stepr (Zero-q);[|ring]; apply Qle_Qminus_Zero; assumption.
Qed.

Lemma Qopp_Qone_Qlt_Qone: Qopp Qone < Qone.
Proof.
 apply Qlt_transitive with Zero; auto.
Qed.

Hint Resolve Qinv_pos Qinv_resp_nonzero Qminus_Qeq Qeq_Qminus
             Qlt_not_eq' Qinv_neg Qle_Qopp_pos Qlt_Qopp_pos 
             Qlt_Qopp_neg Qopp_Qone_Qlt_Qone.

Lemma Qle_mult_nonneg_pos: forall x y : Q, Zero <= x -> Zero < y -> Zero <= x * y.
Proof.
 intros x y Hx Hy; apply Qle_mult_nonneg_nonneg; auto.
Qed.

Lemma Qle_mult_pos_nonneg: forall x y : Q, Zero<x -> Zero <= y -> Zero <= x * y.
Proof.
 intros x y Hx Hy; apply Qle_mult_nonneg_nonneg; auto.
Qed.

Lemma Qle_mult_nonpos_neg: forall x y : Q, x<=Zero -> y<Zero -> Zero <= x * y.
Proof.
 intros x y Hx Hy; stepr ((-x)*(-y));[|ring]; apply Qle_mult_nonneg_pos; auto.
Qed.

Lemma Qle_mult_neg_nonpos: forall x y : Q, x<Zero -> y<=Zero -> Zero <= x * y.
Proof.
 intros x y Hx Hy; stepr ((-x)*(-y));[|ring]; apply Qle_mult_pos_nonneg; auto.
Qed.

Lemma Qle_Qdiv_nonpos_pos: forall x y : Q, x <= Zero -> Zero < y -> x / y <= Zero.
Proof.
 intros x y Hx Hy; unfold Qdiv; apply general_Q.Qle_mult_nonpos_pos; auto.
Qed.

Lemma Qle_Qdiv_nonneg_neg: forall x y : Q, Zero <= x -> y < Zero -> x / y <= Zero.
Proof.
 intros x y Hx Hy; unfold Qdiv; rewrite Qmult_sym; apply Qle_mult_neg_nonneg; auto.
Qed.

Lemma Qle_Qdiv_nonneg_pos: forall x y : Q, Zero<=x -> Zero < y -> Zero<=x / y.
Proof.
 intros x y Hx Hy; unfold Qdiv; apply Qle_mult_nonneg_pos; auto.
Qed.

Lemma Qle_Qdiv_nonpos_neg: forall x y : Q, x<=Zero -> y<Zero -> Zero<=x / y.
Proof.
 intros x y Hx Hy; unfold Qdiv; apply Qle_mult_nonpos_neg; auto.
Qed.

Lemma Qlt_mult_neg_neg: forall x y : Q, x<Zero-> y<Zero -> Zero < x * y.
Proof.
 intros x y Hx Hy; stepr ((-x)*(-y));[|ring]; apply Qlt_mult_pos_pos; auto.
Qed.

Lemma Qmult_reg_l: forall x y z: Q, z <> Zero -> z*x = z*y -> x=y.
Proof.
 intros x y z Hz Hzxy;
 apply Qminus_Qeq;
 assert (H:z*(x-y)=Zero);
 [ transitivity (z*x-z*y);
   [ ring
   | apply Qeq_Qminus; auto
   ]
 | case (Q_integral _ _ H); trivial; intro H'; contradiction
 ].
Qed.

Lemma Qmult_reg_r: forall x y z: Q, z <> Zero -> x*z = y*z -> x=y.
Proof.
 intros x y z Hz; rewrite (Qmult_sym x z); rewrite (Qmult_sym y z); exact (Qmult_reg_l x y z Hz).
Qed.

Lemma Qmult_Qdiv: forall x y z t : Q,  z <> Zero  -> t <> Zero -> x * t = y * z -> x / z = y / t.
Proof.
 intros x y z t Hz Ht Hxtyz; 
 apply Qmult_reg_l with (z*t); auto;
 transitivity (x*t);
 [|transitivity (y*z); trivial]; field; trivial.
Qed.

Lemma Qdiv_Qmult: forall x y z t : Q,  z <> Zero  -> t <> Zero -> x / z = y / t -> x * t = y * z.
Proof.
 intros x y z t Hz Ht Hxtyz;
 apply Qmult_reg_l with ((Qinv z)*(Qinv t)); auto;
 transitivity (x/z);
  [ | transitivity (y/t); trivial]; field; auto.
Qed.

Lemma Qdiv_Qdiv_Qmult_numerator: forall x y z, y<>Zero -> z<>Zero ->(x/y)/z = x/(y*z).
Proof.
 intros x y z Hy Hz; field; auto.
Qed.

Lemma Qdiv_Qdiv_Qmult_denominator: forall x y z, y<>Zero -> z<>Zero -> x/(y/z) = (x*z)/y.
Proof.
 intros x y z Hy Hz; field; auto.
Qed.

Lemma Qdiv_Qplus_Qmult: forall x y z, y<>Zero -> x/y + z = (x+y*z)/y.
Proof.
 intros x y z Hy; field; auto.
Qed.

Lemma Qdiv_Qminus_Qmult: forall x y z, y<>Zero -> x/y - z = (x-y*z)/y.
Proof.
 intros x y z Hy; field; auto.
Qed.

Lemma Qminus_Qdiv_Qmult: forall x y z, ~(y=Zero)->z-x/y=(y*z-x)/y.
Proof.
Proof.
 intros x y z Hy; field; auto.
Qed.

Lemma Qplus_Qdiv_Qmult: forall x y z, ~(y=Zero)->z+x/y=(y*z+x)/y.
Proof.
Proof.
 intros x y z Hy; field; auto.
Qed.

Lemma Qle_reg_mult_r: forall x y z : Q, Zero < x -> y <=z -> y * x <=z * x.
Proof.
 intros x y z Hx Hyz; apply Qle_Zero_Qminus; stepr (x*(z-y)); [|ring]; apply Qle_mult_nonneg_nonneg; auto; apply Qle_Qminus_Zero; assumption.
Qed. 

Lemma Qle_reg_mult_l: forall x y z : Q, Zero < x -> y <= z -> x * y <= x * z.
Proof.
 intros x y z Hx Hyz; apply Qle_Zero_Qminus; stepr (x*(z-y)); [|ring]; apply Qle_mult_nonneg_nonneg; auto; apply Qle_Qminus_Zero; assumption.
Qed. 

Lemma Qmult_resp_Qle_pos_r: forall t x y : Q, Zero < t -> x * t <= y * t -> x <= y.
Proof.
 intros t x y Ht Hxt; case (Q_le_lt_dec x y); trivial; intro Hxy; apply False_ind; apply (Qlt_irreflexive (x*t)); 
 apply Qle_lt_trans with (y*t); trivial; apply Qlt_reg_mult_pos_r; assumption.
Qed.

Lemma Qmult_resp_Qle_pos_l: forall t x y : Q, Zero < t -> t * x <= t * y -> x <= y.
Proof.
 intros t x y Ht Hxt; case (Q_le_lt_dec x y); trivial; intro Hxy; apply False_ind; apply (Qlt_irreflexive (t*x)); 
 apply Qle_lt_trans with (t*y); trivial; apply Qlt_reg_mult_pos_l; assumption.
Qed.

Lemma Qmult_resp_Qle_neg_r: forall t x y : Q, t < Zero -> x * t <= y * t -> y <= x.
Proof.
 intros t x y Ht Hxt; case (Q_le_lt_dec y x); trivial; intro Hxy; apply False_ind; apply (Qlt_irreflexive (x*t)); 
 apply Qle_lt_trans with (y*t); trivial; apply Qlt_reg_mult_neg_r; assumption.
Qed.

Lemma Qmult_resp_Qle_neg_l: forall t x y : Q, t < Zero -> t * x <= t * y -> y <= x.
Proof.
 intros t x y Ht Hxt; case (Q_le_lt_dec y x); trivial; intro Hxy; apply False_ind; apply (Qlt_irreflexive (t*x)); 
 apply Qle_lt_trans with (t*y); trivial; apply Qlt_reg_mult_neg_l; assumption.
Qed.

Lemma Qmult_Qdiv_pos_Qle: forall x y z t : Q, Zero < z -> Zero < t -> x * t <= y * z -> x / z <= y / t.
Proof.
 intros x y z t Hz Ht Hxyzt;
 apply Qmult_resp_Qle_pos_r with (z*t);
  [ apply Qlt_mult_pos_pos
  | stepl (x*t);
    [ stepr (y*z) | idtac];
    trivial;
    field; apply Qlt_not_eq
  ]; 
  trivial.
Qed.

Lemma Qmult_Qle_compat: forall n m p q : Q, n <= p -> m <= q -> Zero <= n -> Zero <= m -> n * m <= p * q.
Proof.
 intros n m p a Hnp Hmq Hn Hm;
 case (Qle_lt_eq_dec _ _ Hm); clear Hm; intro Hm;
  [case (Qle_lt_eq_dec _ _ Hn); clear Hn; intro Hn;
    [ apply Qle_trans with (p*m);
      [ apply Qle_reg_mult_r
      | apply Qle_reg_mult_l; trivial; apply Qlt_le_trans with n
      ]
    | subst n; stepl Zero; auto; apply Qle_mult_nonneg_nonneg; trivial;
     match goal with | [ id: (Qlt Zero ?X1) |- _ ] => apply Qle_trans with X1; trivial; apply Qlt_le_weak end
    ]
  |subst m; stepl Zero; try ring; apply Qle_mult_nonneg_nonneg; trivial; apply Qle_trans with n
  ] 
  ;trivial.
Qed.

Lemma Qdiv_num_denom_explicit: forall q1 q2 p : Q, q2 <> Zero -> p <> Zero -> q1 / q2 = (q1 * p)/ (q2 * p).
Proof.
 intros q1 q2 p Hq1 Hp; field; split; trivial. 
Qed.

Lemma Qle_opp: forall x y : Q, - x <= - y -> y <= x.
Proof.
 intros x y Hxy; apply Qmult_resp_Qle_neg_r with (- Qone); auto; stepl (-x); [stepr (-y); trivial|]; ring.
Qed.

Lemma Qmult_pos_Qle_Qdiv: forall x y z : Q, Zero<z -> x * z<=y -> x <= y / z.
Proof.
 intros x y z Hz Hxyz; apply Qmult_resp_Qle_pos_r with z; trivial; stepr y; trivial; field; auto.
Qed.

Lemma Qmult_neg_Qle_Qdiv: forall x y z : Q, z <Zero -> y <= x * z -> x <= y / z.
Proof.
 intros x y z Hz Hxyz; apply Qmult_resp_Qle_neg_r with z; trivial; stepl y; trivial; field; auto.
Qed.

Lemma Qmult_pos_Qdiv_Qle: forall x y z : Q, Zero<z -> y<=x*z -> y/z <= x.
Proof.
 intros x y z Hz Hxyz; apply Qmult_resp_Qle_pos_r with z; trivial; stepl y; trivial; field; auto.
Qed.

Lemma Qmult_neg_Qdiv_Qle: forall x y z : Q, z <Zero -> x*z<=y -> y/z<=x.
Proof.
 intros x y z Hz Hxyz; apply Qmult_resp_Qle_neg_r with z; trivial; stepr y; trivial; field; auto.
Qed.

Lemma Qmult_pos_Qlt_Qdiv: forall x y z : Q, Zero<z -> x * z<y -> x < y/z.
Proof.
 intros x y z Hz Hxyz; apply Qmult_resp_Qlt_pos_r with z; trivial; stepr y; trivial; field; auto.
Qed.

Lemma Qmult_neg_Qlt_Qdiv: forall x y z : Q, z <Zero -> y < x * z -> x < y / z.
Proof.
 intros x y z Hz Hxyz; apply Qmult_resp_Qlt_neg_r with z; trivial; stepl y; trivial; field; auto.
Qed.

Lemma Qmult_pos_Qdiv_Qlt: forall x y z : Q, Zero<z -> y<x*z -> y/z < x.
Proof.
 intros x y z Hz Hxyz; apply Qmult_resp_Qlt_pos_r with z; trivial; stepl y; trivial; field; auto.
Qed.

Lemma Qmult_neg_Qdiv_Qlt: forall x y z : Q, z <Zero -> x*z<y -> y/z<x.
Proof.
 intros x y z Hz Hxyz; apply Qmult_resp_Qlt_neg_r with z; trivial; stepr y; trivial; field; auto.
Qed.

Lemma Qmult_Qdiv_pos_neg_Qle:forall x y z t : Q,  Zero < z -> t<Zero -> y * z <= x * t -> x / z <= y / t.
Proof.
 intros x y z t Hz Ht Hxyzt;
 apply Qmult_resp_Qle_neg_r with (z*t).
  rewrite Qmult_sym; apply Qlt_mult_neg_pos; trivial.
  stepr (x*t); [ stepl (y*z) |]; trivial; field; auto. 
Qed.

Lemma Qmult_Qdiv_neg_pos_Qle:forall x y z t : Q,  z<Zero -> Zero<t -> y * z <= x * t -> x / z <= y / t.
Proof.
 intros x y z t Hz Ht Hxyzt;
 apply Qmult_resp_Qle_neg_r with (z*t).
  apply Qlt_mult_neg_pos; trivial.
  stepr (x*t); [ stepl (y*z) |]; trivial; field; auto. 
Qed.

Lemma Qmult_Qdiv_neg_Qle:forall x y z t : Q,  z<Zero -> t<Zero -> x * t<=y * z -> x / z <= y / t.
Proof.
 intros x y z t Hz Ht Hxyzt;
 apply Qmult_resp_Qle_pos_r with (z*t).
  apply Qlt_mult_neg_neg; trivial.
  stepl (x*t); [ stepr (y*z) |]; trivial; field; auto. 
Qed.

Lemma Qopp_involutive: forall q, Qopp (Qopp q) = q.
Proof.
 intros [|qp|qp]; trivial. 
Qed.

Lemma Qopp_Qle: forall x y, y <= x -> - x <= - y.
Proof.
 intros x y Hxy; apply Qle_opp; repeat rewrite Qopp_involutive; assumption.
Qed.

Lemma Qopp_Qlt: forall x y, y < x -> - x < - y.
Proof.
 intros x y Hxy; apply Qlt_opp; repeat rewrite Qopp_involutive; assumption.
Qed.

Lemma Qle_reg_mult_r_strong: forall x y z : Q, Zero <= x -> y <= z -> y * x <= z * x.
Proof.
  intros x y z Hx Hyz; apply Qle_Zero_Qminus; stepr (x*(z-y)); [|ring]; apply Qle_mult_nonneg_nonneg; auto; apply Qle_Qminus_Zero; assumption.
Qed.

Lemma Qle_reg_mult_l_strong: forall x y z : Q, Zero <= x -> y <= z -> x * y <= x * z.
Proof.
 intros x y z Hx Hyz; apply Qle_Zero_Qminus; stepr (x*(z-y)); [|ring]; apply Qle_mult_nonneg_nonneg; auto; apply Qle_Qminus_Zero; assumption.
Qed. 

Lemma Qlt_Qdiv_denom_neg_neg: forall x y:Q, y<Zero -> x / y < Zero ->  Zero < x.
Proof.
 intros x y Hy Hxy; stepr (y*(x/y)); [|field; auto]; apply Qlt_mult_neg_neg; assumption.
Qed. 

Lemma Qlt_Qdiv_denom_neg_pos: forall x y:Q, y<Zero ->  Zero< x / y  -> x<Zero.
Proof.
 intros x y Hy Hxy; stepl (y*(x/y)); [|field; auto]; apply Qlt_mult_neg_pos; assumption.
Qed. 

Lemma Qlt_Qdiv_denom_pos_neg: forall x y:Q, Zero<y -> x / y < Zero ->  x<Zero.
Proof.
 intros x y Hy Hxy; stepl ((x/y)*y); [|field; auto]; apply Qlt_mult_neg_pos; assumption.
Qed. 

Lemma Qlt_Qdiv_denom_pos_pos: forall x y:Q, Zero<y ->  Zero< x / y  -> Zero<x.
Proof.
 intros x y Hy Hxy; stepr (y*(x/y)); [|field; auto]; apply Qlt_mult_pos_pos; assumption.
Qed. 

Lemma Qle_Qdiv_denom_neg_nonpos: forall x y:Q, y<Zero -> x / y <= Zero ->  Zero <= x.
Proof.
 intros x y Hy Hxy; stepr (y*(x/y)); [|field; auto]; apply Qle_mult_neg_nonpos; assumption.
Qed. 

Lemma Qle_Qdiv_denom_neg_nonneg: forall x y:Q, y<Zero ->  Zero<= x / y  -> x<=Zero.
Proof.
 intros x y Hy Hxy; stepl (y*(x/y)); [|field; auto]; apply Qle_mult_neg_nonneg; assumption.
Qed. 

Lemma Qle_Qdiv_denom_pos_nonpos: forall x y:Q, Zero<y -> x / y <= Zero ->  x<=Zero.
Proof.
 intros x y Hy Hxy; stepl ((x/y)*y); [|field; auto]; apply Qle_mult_nonpos_pos; assumption.
Qed. 

Lemma Qle_Qdiv_denom_pos_nonneg: forall x y:Q, Zero<y ->  Zero<= x / y  -> Zero<=x.
Proof.
 intros x y Hy Hxy; stepr (y*(x/y)); [|field; auto]; apply Qle_mult_pos_nonneg; assumption.
Qed. 

Lemma Qlt_neg_Qopp: forall x : Q, - x < Zero->Zero < x.
Proof.
 intros x Hx; apply Qlt_opp; simpl; assumption.
Qed.

Lemma Qlt_pos_Qopp: forall x : Q, Zero < - x->x<Zero.
Proof.
 intros x Hx; apply Qlt_opp; simpl; assumption.
Qed.

Lemma Qmult_mult_Qle_Qone_Qopp_Qone: forall q, -Qone<=q -> q<= Qone -> q*q <= Qone. 
Proof.
 intros q H1 H2.
 destruct (Q_le_lt_dec Zero q).
  stepr (Qone*Qone); trivial; apply Qmult_Qle_compat; assumption.
  stepl ((-q)*(-q)); [|ring]; stepr (Qone*Qone); trivial; apply Qmult_Qle_compat; auto; 
   apply Qle_opp; stepr q; auto; ring. 
Qed.

Lemma Qinv_resp_nonzero_Qdiv:forall q, q <> Zero -> (Qone/q)<>Zero. 
Proof.
 intros q Hq; rewrite <- Qinv_Qdiv_Qone; apply Qinv_resp_nonzero; assumption.
Qed.

Lemma Qmult_Qlt_Qle_nonneg_pos_compat: forall n m p q, n < p -> m <= q -> Zero <= n -> Zero < q -> n * m < p * q.
Proof.
 intros n m p q H1 H2 H3 H4; apply Qle_lt_trans with (n*q);
 [ apply Qle_reg_mult_l_strong|apply Qlt_reg_mult_pos_r; trivial; apply Qlt_le_trans with m]; trivial.  
Qed.

Lemma Qmult_Qlt_Qle_pos_nonneg_compat: forall n m p q, n <= p -> m < q -> Zero < p -> Zero <= m -> n * m < p * q.
Proof.
 intros n m p q H1 H2 H3 H4; apply Qle_lt_trans with (p*m);
 [ apply Qle_reg_mult_r_strong|apply Qlt_reg_mult_pos_l; trivial; apply Qlt_le_trans with n]; trivial.  
Qed.

Ltac qZ_numerals_one  :=replace (Z_to_Q 1) with Qone;  trivial. 

Ltac qZ_numerals  := 
 match goal with 
 | [ |- context [(Z_to_Q (Z_of_nat ?X1))] ] => unfold Z_of_nat; qZ_numerals
 | [ |- context [(Z_to_Q Z0)] ] => replace (Z_to_Q Z0) with Zero; trivial; qZ_numerals
 | [ |- context [(Z_to_Q (Zpos ?X1))] ] => progress  let v:= eval compute in (Z.pred (Zpos X1)) in 
         replace (Z_to_Q (Zpos X1)) with (Qplus Qone (Z_to_Q v)); trivial; qZ_numerals
 | [ |- context [(Z_to_Q (Zneg ?X1))] ] => let v:= eval compute in (Z.succ (Zneg X1)) in 
        replace (Z_to_Q (Zneg X1)) with (Qminus (Z_to_Q v) Qone); trivial; qZ_numerals
 | [ |- context [(Qplus Zero ?X1)] ] => rewrite Qplus_zero_left; qZ_numerals
 | [ |- context [(Qplus ?X1 Zero)] ] => rewrite Qplus_zero_right; qZ_numerals
 | [ |- context [(Qminus Zero ?X1)] ] => unfold Qminus; rewrite Qplus_zero_left; qZ_numerals
 | [ |- context [(Qminus ?X1 Zero)] ] => unfold Qminus; rewrite Qplus_zero_right; qZ_numerals
 | [ |- context [(Qmult Qone ?X1)] ] => rewrite Qmult_one_left; qZ_numerals
 | [ |- context [(Qmult ?X1 Qone)] ] => rewrite Qmult_one_right; qZ_numerals
 | [ |- _ ] => idtac
 end.

Ltac ring_exact_Q hyp := 
 match type of hyp with 
 | Qlt ?X1 ?X2 => stepl X1;[|qZ_numerals;ring];stepr X2;[|qZ_numerals;ring]; trivial
 | Qle ?X1 ?X2 => stepl X1;[|qZ_numerals;ring];stepr X2;[|qZ_numerals;ring]; trivial
 | ~(@eq Q ?X1 ?X2) => stepl X1;[|qZ_numerals;ring];stepr X2;[|qZ_numerals;ring]; trivial
 | ?X3 => fail 1
 end.


