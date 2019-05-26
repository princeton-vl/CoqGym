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

Require Import FunInd.
Require Export Qhomographic.

Functional Scheme fraction_encoding_ind := 
  Induction for fraction_encoding Sort Prop.

Lemma fraction_encoding_equal :
 forall (m n : Z) (Hn1 Hn2 : n <> 0%Z),
 fraction_encoding m n Hn1 = fraction_encoding m n Hn2.
Proof.
 intros m n Hn1.
 unfold fraction_encoding at 2; fold fraction_encoding. 
 functional induction (fraction_encoding m n Hn1); intros Hn2;
 rewrite e;
   trivial || (
 f_equal;
 apply positive_fraction_encoding_equal).
Defined. 


Ltac Rewrite_eq_ :=
  repeat
   match goal with
   | id1:(_ = left _ _) |- _ => rewrite id1; clear id1
   | id1:(_ = right _ _) |- _ => rewrite id1; clear id1
   | id1:(_ = inleft _ _) |- _ =>
       rewrite id1; clear id1
   | id1:(_ = inright _ _) |- _ => rewrite id1; clear id1
   end.



Ltac Clear_eq_ :=
  repeat
   match goal with
   | id1:(_ = left _ _) |- _ => clear id1
   | id1:(_ = right _ _) |- _ => clear id1
   | id1:(_ = inleft _ _) |- _ => clear id1
   | id1:(_ = inright _ _) |- _ => clear id1
   end.

               
Ltac Sign_mismatch :=
  Clear_eq_;
   match goal with
   | id1:(?X1 = 1%Z),id2:(?X1 = 0%Z) |- _ =>
       rewrite id2 in id1; discriminate id1
   | id1:(?X1 = 0%Z),id2:(?X1 = 1%Z) |- _ =>
       rewrite id2 in id1; discriminate id1
   | id1:(?X1 = (-1)%Z),id2:(?X1 = 0%Z) |- _ =>
       rewrite id2 in id1; discriminate id1
   | id1:(?X1 = 0%Z),id2:(?X1 = (-1)%Z) |- _ =>
       rewrite id2 in id1; discriminate id1
   | id1:(?X1 = 1%Z),id2:(?X1 = (-1)%Z) |- _ =>
       rewrite id2 in id1; discriminate id1
   | id1:(?X1 = (-1)%Z),id2:(?X1 = 1%Z) |- _ =>
       rewrite id2 in id1; discriminate id1
   end.


Functional Scheme Qhomographic_Qpositive_to_Q_ind := 
  Induction for Qhomographic_Qpositive_to_Q Sort Prop.

Lemma Qhomographic_Qpositive_to_Q_0 :
 forall (a b c d : Z) (p : Qpositive)
   (H_Qhomographic_sg_denom_nonzero : Qhomographic_sg_denom_nonzero c d p)
   (Hc : c <> 0%Z),
 (a * d)%Z = (b * c)%Z ->
 d = 0%Z ->
 Qhomographic_Qpositive_to_Q a b c d p H_Qhomographic_sg_denom_nonzero =
 fraction_encoding a c Hc. 
Proof.
 intros a b c d p H_Qhomographic_sg_denom_nonzero.
 functional induction ( Qhomographic_Qpositive_to_Q a b c d p H_Qhomographic_sg_denom_nonzero);
   intros;
     try solve [ Falsum ]; unfold Qhomographic_Qpositive_to_Q in |- *.
 apply fraction_encoding_equal.
 apply fraction_encoding_equal.
Defined.



Lemma Qhomographic_Qpositive_to_Q_1 :
 forall (a b c d : Z) (p : Qpositive)
   (H_Qhomographic_sg_denom_nonzero : Qhomographic_sg_denom_nonzero c d p)
   (Hd : d <> 0%Z),
 (a * d)%Z = (b * c)%Z ->
 Qhomographic_Qpositive_to_Q a b c d p H_Qhomographic_sg_denom_nonzero =
 fraction_encoding b d Hd. 
Proof.
  intros a b c d p H_Qhomographic_sg_denom_nonzero.
  functional induction (Qhomographic_Qpositive_to_Q a b c d p H_Qhomographic_sg_denom_nonzero);intros;
    try solve [ Falsum ]; unfold Qhomographic_Qpositive_to_Q in |- *.
      apply fraction_encoding_equal.
Defined.


Lemma Qhomographic_Qpositive_to_Q_2 :
 forall (a b c d : Z) (p : Qpositive)
   (H_Qhomographic_sg_denom_nonzero : Qhomographic_sg_denom_nonzero c d p),
 (a * d)%Z <> (b * c)%Z ->
 h_sign a b c d p H_Qhomographic_sg_denom_nonzero = 0%Z ->
 Qhomographic_Qpositive_to_Q a b c d p H_Qhomographic_sg_denom_nonzero = Zero.
Proof.
 intros a b c d p H_Qhomographic_sg_denom_nonzero.
 functional induction (Qhomographic_Qpositive_to_Q a b c d p H_Qhomographic_sg_denom_nonzero);intros;
   try solve [Falsum|Sign_mismatch];
   reflexivity.
Qed.


(** This tactic solves the goal by contradiction, if in the hypothesis there are two terms `a<c` and `c<=a` *)
Ltac Order_mismatch :=
  Clear_eq_;
   match goal with
   | id1:(?X1 < ?X2)%Z,id2:(?X2 <= ?X1)%Z |- _ =>
       match goal with
       | id1:(?X1 < ?X2)%Z,id2:(?X2 <= ?X1)%Z |- _ =>
           first [ apply False_ind | apply False_rec ]; apply (Z.lt_irrefl X1);
            apply Z.lt_le_trans with X2; assumption
       end
   | id2:(?X1 <= ?X2)%Z,id1:(?X2 < ?X1)%Z |- _ =>
       match goal with
       | id1:(?X1 < ?X2)%Z,id2:(?X2 <= ?X1)%Z |- _ =>
           first [ apply False_ind | apply False_rec ]; apply (Z.lt_irrefl X1);
            apply Z.lt_le_trans with X2; assumption
       end
   end. 

Lemma Qhomographic_Qpositive_to_Q_3 :
 forall (a b c d : Z) (p : Qpositive)
   (H_Qhomographic_sg_denom_nonzero : Qhomographic_sg_denom_nonzero c d p),
 (a * d)%Z <> (b * c)%Z ->
 h_sign a b c d p H_Qhomographic_sg_denom_nonzero = 1%Z ->
 forall
   hyp_homographicAcc : homographicAcc
                          (new_a a b c d p H_Qhomographic_sg_denom_nonzero)
                          (new_b a b c d p H_Qhomographic_sg_denom_nonzero)
                          (new_c a b c d p H_Qhomographic_sg_denom_nonzero)
                          (new_d a b c d p H_Qhomographic_sg_denom_nonzero)
                          (new_p a b c d p H_Qhomographic_sg_denom_nonzero),
 (0 <
  Z.sgn
    (new_a a b c d p H_Qhomographic_sg_denom_nonzero +
     new_b a b c d p H_Qhomographic_sg_denom_nonzero))%Z ->
 Qhomographic_Qpositive_to_Q a b c d p H_Qhomographic_sg_denom_nonzero =
 Qpos
   (Qhomographic_Qpositive_to_Qpositive
      (new_a a b c d p H_Qhomographic_sg_denom_nonzero)
      (new_b a b c d p H_Qhomographic_sg_denom_nonzero)
      (new_c a b c d p H_Qhomographic_sg_denom_nonzero)
      (new_d a b c d p H_Qhomographic_sg_denom_nonzero)
      (new_p a b c d p H_Qhomographic_sg_denom_nonzero) hyp_homographicAcc).
Proof.
 intros a b c d p H_Qhomographic_sg_denom_nonzero.
 functional induction (Qhomographic_Qpositive_to_Q a b c d p H_Qhomographic_sg_denom_nonzero);intros; 
             try solve [ Falsum | Sign_mismatch | Order_mismatch ];
             unfold Qhomographic_Qpositive_to_Q in |- *; 
             apply f_equal with Qpositive;
             apply Qhomographic_Qpositive_to_Qpositive_equal.
Qed.


Lemma Qhomographic_Qpositive_to_Q_4 :
 forall (a b c d : Z) (p : Qpositive)
   (H_Qhomographic_sg_denom_nonzero : Qhomographic_sg_denom_nonzero c d p),
 (a * d)%Z <> (b * c)%Z ->
 h_sign a b c d p H_Qhomographic_sg_denom_nonzero = 1%Z ->
 forall
   hyp_homographicAcc : homographicAcc
                          (- new_a a b c d p H_Qhomographic_sg_denom_nonzero)
                          (- new_b a b c d p H_Qhomographic_sg_denom_nonzero)
                          (- new_c a b c d p H_Qhomographic_sg_denom_nonzero)
                          (- new_d a b c d p H_Qhomographic_sg_denom_nonzero)
                          (new_p a b c d p H_Qhomographic_sg_denom_nonzero),
 (Z.sgn
    (new_a a b c d p H_Qhomographic_sg_denom_nonzero +
     new_b a b c d p H_Qhomographic_sg_denom_nonzero) <= 0)%Z ->
 Qhomographic_Qpositive_to_Q a b c d p H_Qhomographic_sg_denom_nonzero =
 Qpos
   (Qhomographic_Qpositive_to_Qpositive
      (- new_a a b c d p H_Qhomographic_sg_denom_nonzero)
      (- new_b a b c d p H_Qhomographic_sg_denom_nonzero)
      (- new_c a b c d p H_Qhomographic_sg_denom_nonzero)
      (- new_d a b c d p H_Qhomographic_sg_denom_nonzero)
      (new_p a b c d p H_Qhomographic_sg_denom_nonzero) hyp_homographicAcc).
Proof.
 intros a b c d p H_Qhomographic_sg_denom_nonzero.
 functional induction 
   (Qhomographic_Qpositive_to_Q a b c d p H_Qhomographic_sg_denom_nonzero);intros;
   try solve [ Falsum | Sign_mismatch | Order_mismatch ];
     unfold Qhomographic_Qpositive_to_Q in |- *; 
       apply f_equal with Qpositive;
         apply Qhomographic_Qpositive_to_Qpositive_equal.
Qed.


Lemma Qhomographic_Qpositive_to_Q_5 :
 forall (a b c d : Z) (p : Qpositive)
   (H_Qhomographic_sg_denom_nonzero : Qhomographic_sg_denom_nonzero c d p),
 (a * d)%Z <> (b * c)%Z ->
 h_sign a b c d p H_Qhomographic_sg_denom_nonzero = (-1)%Z ->
 forall
   hyp_homographicAcc : homographicAcc
                          (- new_a a b c d p H_Qhomographic_sg_denom_nonzero)
                          (- new_b a b c d p H_Qhomographic_sg_denom_nonzero)
                          (new_c a b c d p H_Qhomographic_sg_denom_nonzero)
                          (new_d a b c d p H_Qhomographic_sg_denom_nonzero)
                          (new_p a b c d p H_Qhomographic_sg_denom_nonzero),
 (Z.sgn
    (new_a a b c d p H_Qhomographic_sg_denom_nonzero +
     new_b a b c d p H_Qhomographic_sg_denom_nonzero) < 0)%Z ->
 Qhomographic_Qpositive_to_Q a b c d p H_Qhomographic_sg_denom_nonzero =
 Qneg
   (Qhomographic_Qpositive_to_Qpositive
      (- new_a a b c d p H_Qhomographic_sg_denom_nonzero)
      (- new_b a b c d p H_Qhomographic_sg_denom_nonzero)
      (new_c a b c d p H_Qhomographic_sg_denom_nonzero)
      (new_d a b c d p H_Qhomographic_sg_denom_nonzero)
      (new_p a b c d p H_Qhomographic_sg_denom_nonzero) hyp_homographicAcc).
Proof.
 intros a b c d p H_Qhomographic_sg_denom_nonzero.
 functional induction 
   (Qhomographic_Qpositive_to_Q a b c d p H_Qhomographic_sg_denom_nonzero); 
   intros;
     try solve [ Falsum | Sign_mismatch | Order_mismatch ];
        (unfold Qhomographic_Qpositive_to_Q in |- *; 
         apply f_equal with Qpositive;
           apply Qhomographic_Qpositive_to_Qpositive_equal).
Qed.

Lemma Qhomographic_Qpositive_to_Q_6 :
 forall (a b c d : Z) (p : Qpositive)
   (H_Qhomographic_sg_denom_nonzero : Qhomographic_sg_denom_nonzero c d p),
 (a * d)%Z <> (b * c)%Z ->
 h_sign a b c d p H_Qhomographic_sg_denom_nonzero = (-1)%Z ->
 forall
   hyp_homographicAcc : homographicAcc
                          (new_a a b c d p H_Qhomographic_sg_denom_nonzero)
                          (new_b a b c d p H_Qhomographic_sg_denom_nonzero)
                          (- new_c a b c d p H_Qhomographic_sg_denom_nonzero)
                          (- new_d a b c d p H_Qhomographic_sg_denom_nonzero)
                          (new_p a b c d p H_Qhomographic_sg_denom_nonzero),
 (0 <=
  Z.sgn
    (new_a a b c d p H_Qhomographic_sg_denom_nonzero +
     new_b a b c d p H_Qhomographic_sg_denom_nonzero))%Z ->
 Qhomographic_Qpositive_to_Q a b c d p H_Qhomographic_sg_denom_nonzero =
 Qneg
   (Qhomographic_Qpositive_to_Qpositive
      (new_a a b c d p H_Qhomographic_sg_denom_nonzero)
      (new_b a b c d p H_Qhomographic_sg_denom_nonzero)
      (- new_c a b c d p H_Qhomographic_sg_denom_nonzero)
      (- new_d a b c d p H_Qhomographic_sg_denom_nonzero)
      (new_p a b c d p H_Qhomographic_sg_denom_nonzero) hyp_homographicAcc).
Proof.
 intros a b c d p H_Qhomographic_sg_denom_nonzero.
 functional induction 
   (Qhomographic_Qpositive_to_Q a b c d p H_Qhomographic_sg_denom_nonzero);intros;
             try solve [ Falsum | Sign_mismatch | Order_mismatch ];
             unfold Qhomographic_Qpositive_to_Q in |- *; 
             apply f_equal with Qpositive;
             apply Qhomographic_Qpositive_to_Qpositive_equal.
Qed.


Lemma h_sign_equal :
 forall (a b c d : Z) (p : Qpositive)
   (H_Qhomographic_sg_denom_nonzero1
    H_Qhomographic_sg_denom_nonzero2 : Qhomographic_sg_denom_nonzero c d p),
 h_sign a b c d p H_Qhomographic_sg_denom_nonzero1 =
 h_sign a b c d p H_Qhomographic_sg_denom_nonzero2.
Proof.
 abstract (intros a b c d p H_Qhomographic_sg_denom_nonzero1
            H_Qhomographic_sg_denom_nonzero2;
            change
              (fst
                 (Qhomographic_sign a b c d p
                    H_Qhomographic_sg_denom_nonzero1) =
               fst
                 (Qhomographic_sign a b c d p
                    H_Qhomographic_sg_denom_nonzero2)) 
             in |- *;
            apply f_equal with (Z * (Z * (Z * (Z * Z)) * Qpositive))%type;
            apply Qhomographic_sign_equal).
Defined.

Lemma new_a_equal :
 forall (a b c d : Z) (p : Qpositive)
   (H_Qhomographic_sg_denom_nonzero1
    H_Qhomographic_sg_denom_nonzero2 : Qhomographic_sg_denom_nonzero c d p),
 new_a a b c d p H_Qhomographic_sg_denom_nonzero1 =
 new_a a b c d p H_Qhomographic_sg_denom_nonzero2.
Proof.
 abstract (intros a b c d p H_Qhomographic_sg_denom_nonzero1
            H_Qhomographic_sg_denom_nonzero2; unfold new_a in |- *;
            apply f_equal with (Z * (Z * (Z * Z)))%type;
            apply f_equal with (Z * (Z * (Z * Z)) * Qpositive)%type;
            apply f_equal with (Z * (Z * (Z * (Z * Z)) * Qpositive))%type;
            apply Qhomographic_sign_equal).
Defined.

Lemma new_b_equal :
 forall (a b c d : Z) (p : Qpositive)
   (H_Qhomographic_sg_denom_nonzero1
    H_Qhomographic_sg_denom_nonzero2 : Qhomographic_sg_denom_nonzero c d p),
 new_b a b c d p H_Qhomographic_sg_denom_nonzero1 =
 new_b a b c d p H_Qhomographic_sg_denom_nonzero2.
Proof.
 abstract (intros a b c d p H_Qhomographic_sg_denom_nonzero1
            H_Qhomographic_sg_denom_nonzero2; unfold new_b in |- *;
            apply f_equal with (Z * (Z * Z))%type;
            apply f_equal with (Z * (Z * (Z * Z)))%type;
            apply f_equal with (Z * (Z * (Z * Z)) * Qpositive)%type;
            apply f_equal with (Z * (Z * (Z * (Z * Z)) * Qpositive))%type;
            apply Qhomographic_sign_equal).
Defined.

Lemma new_c_equal :
 forall (a b c d : Z) (p : Qpositive)
   (H_Qhomographic_sg_denom_nonzero1
    H_Qhomographic_sg_denom_nonzero2 : Qhomographic_sg_denom_nonzero c d p),
 new_c a b c d p H_Qhomographic_sg_denom_nonzero1 =
 new_c a b c d p H_Qhomographic_sg_denom_nonzero2.
Proof.
 abstract (intros a b c d p H_Qhomographic_sg_denom_nonzero1
            H_Qhomographic_sg_denom_nonzero2; unfold new_c in |- *;
            apply f_equal with (Z * Z)%type;
            apply f_equal with (Z * (Z * Z))%type;
            apply f_equal with (Z * (Z * (Z * Z)))%type;
            apply f_equal with (Z * (Z * (Z * Z)) * Qpositive)%type;
            apply f_equal with (Z * (Z * (Z * (Z * Z)) * Qpositive))%type;
            apply Qhomographic_sign_equal).
Defined.

Lemma new_d_equal :
 forall (a b c d : Z) (p : Qpositive)
   (H_Qhomographic_sg_denom_nonzero1
    H_Qhomographic_sg_denom_nonzero2 : Qhomographic_sg_denom_nonzero c d p),
 new_d a b c d p H_Qhomographic_sg_denom_nonzero1 =
 new_d a b c d p H_Qhomographic_sg_denom_nonzero2.
Proof.
 abstract (intros a b c d p H_Qhomographic_sg_denom_nonzero1
            H_Qhomographic_sg_denom_nonzero2; unfold new_d in |- *;
            apply f_equal with (Z * Z)%type;
            apply f_equal with (Z * (Z * Z))%type;
            apply f_equal with (Z * (Z * (Z * Z)))%type;
            apply f_equal with (Z * (Z * (Z * Z)) * Qpositive)%type;
            apply f_equal with (Z * (Z * (Z * (Z * Z)) * Qpositive))%type;
            apply Qhomographic_sign_equal).
Defined.

Lemma new_p_equal :
 forall (a b c d : Z) (p : Qpositive)
   (H_Qhomographic_sg_denom_nonzero1
    H_Qhomographic_sg_denom_nonzero2 : Qhomographic_sg_denom_nonzero c d p),
 new_p a b c d p H_Qhomographic_sg_denom_nonzero1 =
 new_p a b c d p H_Qhomographic_sg_denom_nonzero2.
Proof.
 abstract (intros a b c d p H_Qhomographic_sg_denom_nonzero1
            H_Qhomographic_sg_denom_nonzero2; unfold new_p in |- *;
            apply f_equal with (Z * (Z * (Z * Z)) * Qpositive)%type;
            apply f_equal with (Z * (Z * (Z * (Z * Z)) * Qpositive))%type;
            apply Qhomographic_sign_equal).
Defined.

Lemma Qhomographic_Qpositive_to_Q_equal :
 forall (a b c d : Z) (p : Qpositive)
   (H_Qhomographic_sg_denom_nonzero1
    H_Qhomographic_sg_denom_nonzero2 : Qhomographic_sg_denom_nonzero c d p),
 Qhomographic_Qpositive_to_Q a b c d p H_Qhomographic_sg_denom_nonzero1 =
 Qhomographic_Qpositive_to_Q a b c d p H_Qhomographic_sg_denom_nonzero2.
Proof.
 intros a b c d p H_Qhomographic_sg_denom_nonzero1.

 functional induction 
   (Qhomographic_Qpositive_to_Q a b c d p H_Qhomographic_sg_denom_nonzero1);intros.

 (* 1 *)
generalize
 (Qhomographic_sg_denom_nonzero_nonzero_3 _ _ _
    H_Qhomographic_sg_denom_nonzero1).
 intros [Hc| Hd].

 rewrite
  (Qhomographic_Qpositive_to_Q_0 a b c 0 p H_Qhomographic_sg_denom_nonzero2
     Hc _x (refl_equal 0%Z)).
 apply fraction_encoding_equal.
 Falsum.
generalize
 (Qhomographic_sg_denom_nonzero_nonzero_3 _ _ _
    H_Qhomographic_sg_denom_nonzero1).
 intros [Hc| Hd].

 rewrite
  (Qhomographic_Qpositive_to_Q_0 a b c 0 p H_Qhomographic_sg_denom_nonzero2
     Hc _x (refl_equal 0%Z)).
 apply fraction_encoding_equal.
 Falsum.

 (* 2 *)
 rewrite
  (Qhomographic_Qpositive_to_Q_1 a b c d p H_Qhomographic_sg_denom_nonzero2
     d_neq_zero _x).
 apply fraction_encoding_equal.
 (* 3 *)
 clear e0.
 rewrite
  (h_sign_equal a b c d p H_Qhomographic_sg_denom_nonzero1
     H_Qhomographic_sg_denom_nonzero2) in _x.
 rewrite
  (Qhomographic_Qpositive_to_Q_2 a b c d p H_Qhomographic_sg_denom_nonzero2
     ad_neq_bc _x).
 reflexivity.
 (* 4 *)

 Clear_eq_.
 generalize
  (Qhomographic_Qpositive_to_Q_homographicAcc_pos_1 a b c d p
     H_Qhomographic_sg_denom_nonzero1 ad_neq_bc l1_eq_one z).
 assert (l1_eq_one0 := l1_eq_one).
 rewrite
  (h_sign_equal a b c d p H_Qhomographic_sg_denom_nonzero1
     H_Qhomographic_sg_denom_nonzero2) in l1_eq_one0.
 change
   (0 <
    Z.sgn
      (new_a a b c d p H_Qhomographic_sg_denom_nonzero1 +
       new_b a b c d p H_Qhomographic_sg_denom_nonzero1))%Z 
  in z. 
 assert (z0 := z).
 rewrite (new_a_equal a b c d p H_Qhomographic_sg_denom_nonzero1
     H_Qhomographic_sg_denom_nonzero2) in z0.
 rewrite
  (new_b_equal a b c d p H_Qhomographic_sg_denom_nonzero1
     H_Qhomographic_sg_denom_nonzero2) in z0.
 rewrite
  (Qhomographic_Qpositive_to_Q_3 a b c d p H_Qhomographic_sg_denom_nonzero2
     ad_neq_bc l1_eq_one0
     (Qhomographic_Qpositive_to_Q_homographicAcc_pos_1 a b c d p
        H_Qhomographic_sg_denom_nonzero2 ad_neq_bc l1_eq_one0 z0) z0)
  .
 intro H_any_homographicAcc.
 apply f_equal with Qpositive.
 apply Qhomographic_Qpositive_to_Qpositive_equal_strong;
  [ rewrite
     (new_a_equal a b c d p H_Qhomographic_sg_denom_nonzero1
        H_Qhomographic_sg_denom_nonzero2)
  | rewrite
     (new_b_equal a b c d p H_Qhomographic_sg_denom_nonzero1
        H_Qhomographic_sg_denom_nonzero2)
  | rewrite
     (new_c_equal a b c d p H_Qhomographic_sg_denom_nonzero1
        H_Qhomographic_sg_denom_nonzero2)
  | rewrite
     (new_d_equal a b c d p H_Qhomographic_sg_denom_nonzero1
        H_Qhomographic_sg_denom_nonzero2)
  | rewrite
     (new_p_equal a b c d p H_Qhomographic_sg_denom_nonzero1
        H_Qhomographic_sg_denom_nonzero2) ]; reflexivity.

 (* 5 *)
 Clear_eq_.
 generalize
  (Qhomographic_Qpositive_to_Q_homographicAcc_pos_2 a b c d p
     H_Qhomographic_sg_denom_nonzero1 ad_neq_bc l1_eq_one z).
 assert (l1_eq_one0 := l1_eq_one).
 rewrite
  (h_sign_equal a b c d p H_Qhomographic_sg_denom_nonzero1
     H_Qhomographic_sg_denom_nonzero2) in l1_eq_one0.
 change
   (Z.sgn
      (new_a a b c d p H_Qhomographic_sg_denom_nonzero1 +
       new_b a b c d p H_Qhomographic_sg_denom_nonzero1) <= 0)%Z 
  in z. 
 assert (z0 := z).
 rewrite
  (new_a_equal a b c d p H_Qhomographic_sg_denom_nonzero1
     H_Qhomographic_sg_denom_nonzero2) in z0.
 rewrite
  (new_b_equal a b c d p H_Qhomographic_sg_denom_nonzero1
     H_Qhomographic_sg_denom_nonzero2) in z0.
 rewrite
  (Qhomographic_Qpositive_to_Q_4 a b c d p H_Qhomographic_sg_denom_nonzero2
     ad_neq_bc l1_eq_one0
     (Qhomographic_Qpositive_to_Q_homographicAcc_pos_2 a b c d p
        H_Qhomographic_sg_denom_nonzero2 ad_neq_bc l1_eq_one0 z0) z0)
  .
 intro H_any_homographicAcc.
 apply f_equal with Qpositive.
 apply Qhomographic_Qpositive_to_Qpositive_equal_strong;
  [ rewrite
     (new_a_equal a b c d p H_Qhomographic_sg_denom_nonzero1
        H_Qhomographic_sg_denom_nonzero2)
  | rewrite
     (new_b_equal a b c d p H_Qhomographic_sg_denom_nonzero1
        H_Qhomographic_sg_denom_nonzero2)
  | rewrite
     (new_c_equal a b c d p H_Qhomographic_sg_denom_nonzero1
        H_Qhomographic_sg_denom_nonzero2)
  | rewrite
     (new_d_equal a b c d p H_Qhomographic_sg_denom_nonzero1
        H_Qhomographic_sg_denom_nonzero2)
  | rewrite
     (new_p_equal a b c d p H_Qhomographic_sg_denom_nonzero1
        H_Qhomographic_sg_denom_nonzero2) ]; reflexivity.
 (* 6 *)
 Clear_eq_.
 generalize
  (Qhomographic_Qpositive_to_Q_homographicAcc_neg_1 a b c d p
     H_Qhomographic_sg_denom_nonzero1 ad_neq_bc l1_eq__minus_one z).
 assert (l1_eq__minus_one0 := l1_eq__minus_one).
 rewrite
  (h_sign_equal a b c d p H_Qhomographic_sg_denom_nonzero1
     H_Qhomographic_sg_denom_nonzero2) in l1_eq__minus_one0.
 change
   (Z.sgn
      (new_a a b c d p H_Qhomographic_sg_denom_nonzero1 +
       new_b a b c d p H_Qhomographic_sg_denom_nonzero1) < 0)%Z 
  in z. 
 assert (z0 := z).
 rewrite
  (new_a_equal a b c d p H_Qhomographic_sg_denom_nonzero1
     H_Qhomographic_sg_denom_nonzero2) in z0.
 rewrite
  (new_b_equal a b c d p H_Qhomographic_sg_denom_nonzero1
     H_Qhomographic_sg_denom_nonzero2) in z0.
 rewrite
  (Qhomographic_Qpositive_to_Q_5 a b c d p H_Qhomographic_sg_denom_nonzero2
     ad_neq_bc l1_eq__minus_one0
     (Qhomographic_Qpositive_to_Q_homographicAcc_neg_1 a b c d p
        H_Qhomographic_sg_denom_nonzero2 ad_neq_bc l1_eq__minus_one0 z0) z0)
  .
 intro H_any_homographicAcc.
 apply f_equal with Qpositive.
 apply Qhomographic_Qpositive_to_Qpositive_equal_strong;
  [ rewrite
     (new_a_equal a b c d p H_Qhomographic_sg_denom_nonzero1
        H_Qhomographic_sg_denom_nonzero2)
  | rewrite
     (new_b_equal a b c d p H_Qhomographic_sg_denom_nonzero1
        H_Qhomographic_sg_denom_nonzero2)
  | rewrite
     (new_c_equal a b c d p H_Qhomographic_sg_denom_nonzero1
        H_Qhomographic_sg_denom_nonzero2)
  | rewrite
     (new_d_equal a b c d p H_Qhomographic_sg_denom_nonzero1
        H_Qhomographic_sg_denom_nonzero2)
  | rewrite
     (new_p_equal a b c d p H_Qhomographic_sg_denom_nonzero1
        H_Qhomographic_sg_denom_nonzero2) ]; reflexivity.
 (* 7 *)
 Clear_eq_.
 generalize
  (Qhomographic_Qpositive_to_Q_homographicAcc_neg_2 a b c d p
     H_Qhomographic_sg_denom_nonzero1 ad_neq_bc l1_eq__minus_one z).
 assert (l1_eq__minus_one0 := l1_eq__minus_one).
 rewrite
  (h_sign_equal a b c d p H_Qhomographic_sg_denom_nonzero1
     H_Qhomographic_sg_denom_nonzero2) in l1_eq__minus_one0.
 change
   (0 <=
    Z.sgn
      (new_a a b c d p H_Qhomographic_sg_denom_nonzero1 +
       new_b a b c d p H_Qhomographic_sg_denom_nonzero1))%Z 
  in z. 
 assert (z0:=z).
 rewrite
  (new_a_equal a b c d p H_Qhomographic_sg_denom_nonzero1
     H_Qhomographic_sg_denom_nonzero2) in z0.
 rewrite
  (new_b_equal a b c d p H_Qhomographic_sg_denom_nonzero1
     H_Qhomographic_sg_denom_nonzero2) in z0.
 rewrite
  (Qhomographic_Qpositive_to_Q_6 a b c d p H_Qhomographic_sg_denom_nonzero2
     ad_neq_bc l1_eq__minus_one0
     (Qhomographic_Qpositive_to_Q_homographicAcc_neg_2 a b c d p
        H_Qhomographic_sg_denom_nonzero2 ad_neq_bc l1_eq__minus_one0 z0) z0)
  .
 intro H_any_homographicAcc.
 apply f_equal with Qpositive.
 apply Qhomographic_Qpositive_to_Qpositive_equal_strong;
  [ rewrite
     (new_a_equal a b c d p H_Qhomographic_sg_denom_nonzero1
        H_Qhomographic_sg_denom_nonzero2)
  | rewrite
     (new_b_equal a b c d p H_Qhomographic_sg_denom_nonzero1
        H_Qhomographic_sg_denom_nonzero2)
  | rewrite
     (new_c_equal a b c d p H_Qhomographic_sg_denom_nonzero1
        H_Qhomographic_sg_denom_nonzero2)
  | rewrite
     (new_d_equal a b c d p H_Qhomographic_sg_denom_nonzero1
        H_Qhomographic_sg_denom_nonzero2)
  | rewrite
     (new_p_equal a b c d p H_Qhomographic_sg_denom_nonzero1
        H_Qhomographic_sg_denom_nonzero2) ]; reflexivity.
Defined.

