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



Require Export homographicAcc_Qhomographic_sign.
Require Import ZArithRing.



(** note that ~(`c=0`/\`d=0`)<->`c<>0`\/`c<>d` *)

Lemma Qhomographic_sg_denom_nonzero_nonzero :
 forall (c d : Z) (p : Qpositive),
 c = 0%Z -> d = 0%Z -> ~ Qhomographic_sg_denom_nonzero c d p.
Proof.
 intros c d p Hc Hd H_Qhomographic_sg_denom_nonzero.
 generalize Hc Hd.
 elim H_Qhomographic_sg_denom_nonzero; intros; apply H0; first
  [ assumption | rewrite Hc0; rewrite Hd0; constructor ].
Defined.


Lemma Qhomographic_sg_denom_nonzero_nonzero_2 :
 forall (c d : Z) (p : Qpositive),
 Qhomographic_sg_denom_nonzero c d p -> c <> d \/ c <> 0%Z.
Proof.
 intros.
 apply double_not_equal_zero.
 intros (Hc, Hd).
 apply (Qhomographic_sg_denom_nonzero_nonzero c d p); assumption.
Defined.


Lemma Qhomographic_sg_denom_nonzero_nonzero_3 :
 forall (c d : Z) (p : Qpositive),
 Qhomographic_sg_denom_nonzero c d p -> c <> 0%Z \/ d <> 0%Z.
Proof.
 intros c d p H_Qhomographic_sg_denom_nonzero.
 generalize
  (Qhomographic_sg_denom_nonzero_nonzero_2 c d p
     H_Qhomographic_sg_denom_nonzero); intros [Hcd| Hd];
  [ case (Z_zerop c); intro Hc;
     [ right; apply sym_not_equal; rewrite Hc in Hcd | left ]
  | left ]; try assumption.
Defined.

Definition Qhomographic_Qpositive_to_Q (a b c d : Z) 
  (p : Qpositive) (H_hsign : Qhomographic_sg_denom_nonzero c d p) : Q.
case (Z.eq_dec (a * d) (b * c)).
 (* a d = b c *)
 intro ad_eq_bc.
 case (Z_zerop d).
  (* d = 0 *)
  intro d_eq_zero. 
  refine (fraction_encoding a c _).
  case (Qhomographic_sg_denom_nonzero_nonzero_2 c d p H_hsign).
   rewrite d_eq_zero.
   intros H; assumption.
   
   intros H; assumption.
  (* d <> 0 *)
  intro d_neq_zero.  
  exact (fraction_encoding b d d_neq_zero).
 (* a d <> b c *)
 intro ad_neq_bc. 
 case (sg_sign_dec a b c d p H_hsign).
  intro l1_not_minus_one.  
  case l1_not_minus_one.
    (* (h_sign a b c d p) = 0 *)
    intro l1_eq_zero.    
    exact Zero.
    (* (h_sign a b c d p) = 1 *)
    intro l1_eq_one.
      case
       (Z_lt_le_dec 0
          (Z.sgn (new_a a b c d p H_hsign + new_b a b c d p H_hsign))).
      (* 0<s_ab *)
      intro z.
      refine
       (Qpos
          (Qhomographic_Qpositive_to_Qpositive (new_a a b c d p H_hsign)
             (new_b a b c d p H_hsign) (new_c a b c d p H_hsign)
             (new_d a b c d p H_hsign) (new_p a b c d p H_hsign) _)).
      abstract apply
                (Qhomographic_Qpositive_to_Q_homographicAcc_pos_1 _ _ _ _ _
                   H_hsign ad_neq_bc l1_eq_one z).
      (* s_ab <= 0 *)
      intro z.
      refine
       (Qpos
          (Qhomographic_Qpositive_to_Qpositive (- new_a a b c d p H_hsign)
             (- new_b a b c d p H_hsign) (- new_c a b c d p H_hsign)
             (- new_d a b c d p H_hsign) (new_p a b c d p H_hsign) _)).
      abstract apply
                (Qhomographic_Qpositive_to_Q_homographicAcc_pos_2 _ _ _ _ _
                   H_hsign ad_neq_bc l1_eq_one z).
    (* (h_sign a b c d p) = (-1) *)
    intro l1_eq__minus_one.
     case
      (Z_lt_le_dec (Z.sgn (new_a a b c d p H_hsign + new_b a b c d p H_hsign))
         0).
      (* s_ab<0 *)
      intro z.
      refine
       (Qneg
          (Qhomographic_Qpositive_to_Qpositive (- new_a a b c d p H_hsign)
             (- new_b a b c d p H_hsign) (new_c a b c d p H_hsign)
             (new_d a b c d p H_hsign) (new_p a b c d p H_hsign) _)).
      abstract apply
                (Qhomographic_Qpositive_to_Q_homographicAcc_neg_1 _ _ _ _ _
                   H_hsign ad_neq_bc l1_eq__minus_one z).
      (* 0 <= s_ab *)
      intro z.
      refine
       (Qneg
          (Qhomographic_Qpositive_to_Qpositive (new_a a b c d p H_hsign)
             (new_b a b c d p H_hsign) (- new_c a b c d p H_hsign)
             (- new_d a b c d p H_hsign) (new_p a b c d p H_hsign) _)).
      abstract apply
                (Qhomographic_Qpositive_to_Q_homographicAcc_neg_2 _ _ _ _ _
                   H_hsign ad_neq_bc l1_eq__minus_one z).
Defined.


Inductive Qhomographic_denom_nonzero : Z -> Z -> Q -> Prop :=
  | Qhomographicok0 :
      forall (c d : Z) (s : Q),
      s = Zero -> d <> 0%Z -> Qhomographic_denom_nonzero c d s
  | Qhomographicok1 :
      forall (c d : Z) (s : Q) (p : Qpositive),
      s = Qpos p ->
      Qhomographic_sg_denom_nonzero c d p -> Qhomographic_denom_nonzero c d s
  | Qhomographicok2 :
      forall (c d : Z) (s : Q) (p : Qpositive),
      s = Qneg p ->
      Qhomographic_sg_denom_nonzero (- c) d p ->
      Qhomographic_denom_nonzero c d s.


Lemma Qhomographic_denom_nonzero_0 :
 forall c d : Z, Qhomographic_denom_nonzero c d Zero -> d <> 0%Z.  
Proof.
 intros; abstract (inversion_clear H; assumption || discriminate H0).
Defined.

Lemma Qhomographic_denom_nonzero_1 :
 forall (c d : Z) (p : Qpositive),
 Qhomographic_denom_nonzero c d (Qpos p) ->
 Qhomographic_sg_denom_nonzero c d p.
Proof.
 intros;
  abstract (inversion_clear H; solve
             [ assumption
             | match goal with
               | id1:(?X1 = ?X2) |- ?X3 => try discriminate id1; clear id1
               end
             | match goal with
               | id1:(?X1 = ?X2) |- ?X3 =>
                   injection id1; intro H_injected; rewrite H_injected;
                    assumption
               end ]).
Defined.

Lemma Qhomographic_denom_nonzero_2 :
 forall (c d : Z) (p : Qpositive),
 Qhomographic_denom_nonzero c d (Qneg p) ->
 Qhomographic_sg_denom_nonzero (- c) d p.
Proof.
 intros;
  abstract (inversion_clear H; solve
             [ assumption
             | match goal with
               | id1:(?X1 = ?X2) |- ?X3 => try discriminate id1; clear id1
               end
             | match goal with
               | id1:(?X1 = ?X2) |- ?X3 =>
                   injection id1; intro H_injected; rewrite H_injected;
                    assumption
               end ]).
Defined.


Definition Qhomographic (a b c d : Z) (s : Q)
  (H_Qhomographic_denom_nonzero : Qhomographic_denom_nonzero c d s) : Q.
destruct s as [| p| p].
refine (fraction_encoding b d _).
apply Qhomographic_denom_nonzero_0 with c; assumption.
refine (Qhomographic_Qpositive_to_Q a b c d p _).
apply Qhomographic_denom_nonzero_1; assumption.
refine (Qhomographic_Qpositive_to_Q (- a) b (- c) d p _).
apply Qhomographic_denom_nonzero_2; assumption.
Defined.


Lemma Qhomographic_sg_denom_nonzero_always_1 :
 forall (d k k' : Z) (p : Qpositive),
 d <> 0%Z ->
 (0 < k)%Z -> (0 < k')%Z -> Qhomographic_sg_denom_nonzero (k * d) (k' * d) p.
Proof.
 intros.
 generalize k k' H0 H1.  
 induction p.
 intros.
 apply Qhomographic_signok1.
 replace (k0 * d + k'0 * d)%Z with ((k0 + k'0) * d)%Z.
 apply IHp.
 assumption.
 replace 0%Z with (0 + 0)%Z.
 apply Zlt_plus_plus.
 assumption.
 assumption.
 constructor.
 rewrite Zmult_plus_distr_l; reflexivity.
 intros.
 apply Qhomographic_signok2.
 replace (k0 * d + k'0 * d)%Z with ((k0 + k'0) * d)%Z.
 apply IHp.
 replace 0%Z with (0 + 0)%Z.
 apply Zlt_plus_plus.
 assumption.
 assumption.
 constructor.
 assumption.
 rewrite Zmult_plus_distr_l; reflexivity.
 intros.
 apply Qhomographic_signok0.
 reflexivity.
 replace (k0 * d + k'0 * d)%Z with ((k0 + k'0) * d)%Z.
 intro.
 apply H.
 apply Zmult_integral_l with (k0 + k'0)%Z.
 apply Zgt_not_eq.  
 apply Z.lt_gt.
 replace 0%Z with (0 + 0)%Z.
 apply Zlt_plus_plus.
 assumption.
 assumption.
 constructor.
 rewrite Zmult_comm.
 assumption.
 rewrite Zmult_plus_distr_l; reflexivity.
Defined.


Lemma Qhomographic_sg_denom_nonzero_Zero_always :
 forall (d : Z) (p : Qpositive),
 d <> 0%Z -> Qhomographic_sg_denom_nonzero 0 d p.
Proof.
 intros.
 induction p.
 apply Qhomographic_signok1.
 simpl in |- *.
 assumption.
 apply Qhomographic_signok2.
 simpl in |- *.
 replace d with (1 * d)%Z.
 apply Qhomographic_sg_denom_nonzero_always_1.
 assumption.
 constructor.
 constructor.
 rewrite Zmult_1_l.
 reflexivity.  
 apply Qhomographic_signok0.
 reflexivity.
 simpl in |- *.
 assumption.
Defined.

Lemma Qhomographic_sg_denom_nonzero_always_Zero :
 forall (c : Z) (p : Qpositive),
 c <> 0%Z -> Qhomographic_sg_denom_nonzero c 0 p.
Proof.
 intros.
 induction p.
 apply Qhomographic_signok1.
 rewrite Zplus_0_r.
 replace c with (1 * c)%Z.
 apply Qhomographic_sg_denom_nonzero_always_1.
 assumption.
 constructor.
 constructor.
 rewrite Zmult_1_l.
 reflexivity.
 apply Qhomographic_signok2.
 rewrite Zplus_0_r.
 assumption.
 apply Qhomographic_signok0.
 reflexivity.
 rewrite Zplus_0_r.
 assumption.
Defined.


Lemma always_nonzero_Qhomographic_sg_denom_nonzero :
 forall (d : Z) (p : Qpositive),
 Qhomographic_sg_denom_nonzero 0 d p -> d <> 0%Z.
Proof.
 intros.
 intro.
 apply (Qhomographic_sg_denom_nonzero_nonzero 0 d p); solve
  [ constructor | assumption ].
Defined.


Lemma Qhomographic_denom_nonzero_Zero_always :
 forall (d : Z) (s : Q), d <> 0%Z -> Qhomographic_denom_nonzero 0 d s.
Proof.
 abstract (intros; destruct s as [| p| p];
            [ apply Qhomographicok0
            | apply Qhomographicok1 with p
            | apply Qhomographicok2 with p ];
            reflexivity ||
              (try apply Qhomographic_sg_denom_nonzero_Zero_always);
            assumption).
Defined. 

Lemma Qhomographic_denom_nonzero_Zero_ONE :
 forall s : Q, Qhomographic_denom_nonzero 0 1 s.
Proof.
 intros.
 apply Qhomographic_denom_nonzero_Zero_always.
 abstract discriminate.
Defined. 

Lemma Qhomographic_denom_nonzero_always_Zero :
 forall (c : Z) (s : Q) (H_nonzero_s : s <> Zero :>Q),
 c <> 0%Z -> Qhomographic_denom_nonzero c 0 s.
Proof.
 abstract (intros; destruct s as [| p| p];
            [ Falsum
            | apply Qhomographicok1 with p
            | apply Qhomographicok2 with p ]; try reflexivity;
            apply Qhomographic_sg_denom_nonzero_always_Zero;
            try
             match goal with
             | id1:?X2 |- ((- ?X1)%Z <> 0%Z) => apply Zopp_app
             end; assumption).
Defined. 

Lemma Qhomographic_denom_nonzero_ONE_Zero :
 forall (s : Q) (H_nonzero_s : s <> Zero :>Q),
 Qhomographic_denom_nonzero 1 0 s.
Proof.
 intros; apply Qhomographic_denom_nonzero_always_Zero;
  assumption || (abstract discriminate).
Defined. 


(** Example: h(x)=2x   i.e. a=2 b=0 c=0 d=1 *)
Definition Qhomographic_2x (x : Q) : Q :=
  Qhomographic 2 0 0 1 x (Qhomographic_denom_nonzero_Zero_ONE x).

(** Example h(x)=-x i.e. a=`-1` b=0 c=0 d=1 *)
(** This is the additive opposite function *)
Definition Qopp_lazy (x : Q) : Q :=
  Qhomographic (-1) 0 0 1 x (Qhomographic_denom_nonzero_Zero_ONE x).

(** Example h(x)=kx i.e. a=k b=0 c=0 d=1 *)
Definition Qhomographic_kx (k : Z) (x : Q) : Q :=
  Qhomographic k 0 0 1 x (Qhomographic_denom_nonzero_Zero_ONE x).

(** Example h(x)=x/k i.e. a=1 b=0 c=0 d=k<>0 *)
Definition Qhomographic_x_over_k (k : Z) (Hk : k <> 0%Z) 
  (x : Q) : Q :=
  Qhomographic 1 0 0 k x (Qhomographic_denom_nonzero_Zero_always k x Hk).

(** Example h(x)=1/x i.e. a=0 b=1 c=1 d=0 *)
(** This is the multiplicative inverse function *)
Definition Qinv_lazy (x : Q) (Hx : x <> Zero) : Q :=
  Qhomographic 0 1 1 0 x (Qhomographic_denom_nonzero_ONE_Zero x Hx).
