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
Require Export homographic_correctness.
Require Import Field_Theory_Q. 
Require Export Qquadratic_sign.
Require Export Qquadratic_Qpositive_to_Qpositive.
Require Export Qquadratic_sign_properties.
Require Export Qquadratic.
Require Export quadraticAcc_Qquadratic_sign.
Require Export Qquadratic_Qpositive_to_Q_properties.

Definition spec_q (a b c d e f g h : Z) (q1 q2 : Q) : Q :=
  Qmult
    (Qplus (Qplus (Qplus (Qmult (Qmult a q1) q2) (Qmult b q1)) (Qmult c q2))
       d)
    (Qinv
       (Qplus
          (Qplus (Qplus (Qmult (Qmult e q1) q2) (Qmult f q1)) (Qmult g q2)) h)).


Definition spec_Qquadratic_Qpositive_to_Q (a b c d e f g h : Z)
  (p1 p2 : Qpositive) : Q :=
  Qmult
    (Qplus
       (Qplus
          (Qplus (Qmult (Qmult a (Qpos p1)) (Qpos p2)) (Qmult b (Qpos p1)))
          (Qmult c (Qpos p2))) d)
    (Qinv
       (Qplus
          (Qplus
             (Qplus (Qmult (Qmult e (Qpos p1)) (Qpos p2)) (Qmult f (Qpos p1)))
             (Qmult g (Qpos p2))) h)).


(* Here we should expect that ap1p2+bp1+cp2+d > 0 and ep1p1+fp1+gp2+h > 0, this follow - hopefully - from quadraticAcc *)
Definition spec_Qquadratic_Qpositive_to_Qpositive2 
  (a b c d e f g h : Z) (p1 p2 : Qpositive) : Qpositive :=
  Qpositive_mult
    (Q_tail
       (Qplus
          (Qplus
             (Qplus (Qmult (Qmult a (Qpos p1)) (Qpos p2)) (Qmult b (Qpos p1)))
             (Qmult c (Qpos p2))) d))
    (Qpositive_inv
       (Q_tail
          (Qplus
             (Qplus
                (Qplus (Qmult (Qmult e (Qpos p1)) (Qpos p2))
                   (Qmult f (Qpos p1))) (Qmult g (Qpos p2))) h))).



Lemma spec_Qquadratic_Qpositive_to_Q_commut :
 forall (a b c d e f g h : Z) (p1 p2 : Qpositive),
 spec_Qquadratic_Qpositive_to_Q a b c d e f g h p1 p2 =
 spec_Qquadratic_Qpositive_to_Q a c b d e g f h p2 p1.
Proof.
 intros a b c d e f g h p1 p2.
 unfold spec_Qquadratic_Qpositive_to_Q in |- *. 
 abstract (apply f_equal2 with Q Q; solve
            [ ring | apply f_equal with Q; ring ]).
Qed. 

Lemma spec_Qquadratic_Qpositive_to_Qpositive2_commut :
 forall (a b c d e f g h : Z) (p1 p2 : Qpositive),
 spec_Qquadratic_Qpositive_to_Qpositive2 a b c d e f g h p1 p2 =
 spec_Qquadratic_Qpositive_to_Qpositive2 a c b d e g f h p2 p1.
Proof.
 intros a b c d e f g h p1 p2.
 unfold spec_Qquadratic_Qpositive_to_Qpositive2 in |- *. 
 abstract (apply f_equal2 with Qpositive Qpositive;
            try apply f_equal with Qpositive; apply f_equal with Q; 
            ring). 
Qed. 


Lemma spec_Qquadratic_Qpositive_to_Q_p_One :
 forall (a b c d e f g h : Z) (p : Qpositive),
 spec_Qquadratic_Qpositive_to_Q a b c d e f g h p One =
 spec_Qhomographic_Qpositive_to_Q (a + b) (c + d) (e + f) (g + h) p.
Proof.
 intros a b c d e f g h p;
  unfold spec_Qhomographic_Qpositive_to_Q, spec_Qquadratic_Qpositive_to_Q
   in |- *; repeat rewrite Z_to_Qplus; apply f_equal2 with Q Q;
  [ ring | apply f_equal with Q; ring ].
Qed.


Lemma spec_Qquadratic_Qpositive_to_Q_p_One_unfolded :
 forall (a b c d e f g h : Z) (p : Qpositive),
 Qmult
   (Qplus
      (Qplus (Qplus (Qmult (Qmult a (Qpos p)) (Qpos One)) (Qmult b (Qpos p)))
         (Qmult c (Qpos One))) d)
   (Qinv
      (Qplus
         (Qplus
            (Qplus (Qmult (Qmult e (Qpos p)) (Qpos One)) (Qmult f (Qpos p)))
            (Qmult g (Qpos One))) h)) =
 Qmult (Qplus (Qmult (a + b)%Z (Qpos p)) (c + d)%Z)
   (Qinv (Qplus (Qmult (e + f)%Z (Qpos p)) (g + h)%Z)).
Proof spec_Qquadratic_Qpositive_to_Q_p_One.


Lemma spec_Qquadratic_Qpositive_to_Q_One_p :
 forall (a b c d e f g h : Z) (p : Qpositive),
 spec_Qquadratic_Qpositive_to_Q a b c d e f g h One p =
 spec_Qhomographic_Qpositive_to_Q (a + c) (b + d) (e + g) (f + h) p.
Proof.
 intros a b c d e f g h p;
  unfold spec_Qhomographic_Qpositive_to_Q, spec_Qquadratic_Qpositive_to_Q
   in |- *; repeat rewrite Z_to_Qplus; apply f_equal2 with Q Q;
  [ ring | apply f_equal with Q; ring ].
Qed.


Lemma spec_Qquadratic_Qpositive_to_Q_One_p_unfolded :
 forall (a b c d e f g h : Z) (p : Qpositive),
 Qmult
   (Qplus
      (Qplus
         (Qplus (Qmult (Qmult a (Qpos One)) (Qpos p)) (Qmult b (Qpos One)))
         (Qmult c (Qpos p))) d)
   (Qinv
      (Qplus
         (Qplus
            (Qplus (Qmult (Qmult e (Qpos One)) (Qpos p)) (Qmult f (Qpos One)))
            (Qmult g (Qpos p))) h)) =
 Qmult (Qplus (Qmult (a + c)%Z (Qpos p)) (b + d)%Z)
   (Qinv (Qplus (Qmult (e + g)%Z (Qpos p)) (f + h)%Z)).
Proof spec_Qquadratic_Qpositive_to_Q_One_p.


Lemma spec_Qquadratic_Qpositive_to_Q_nR_nR :
 forall (a b c d e f g h : Z) (p1 p2 : Qpositive),
 spec_Qquadratic_Qpositive_to_Q a b c d e f g h (nR p1) (nR p2) =
 spec_Qquadratic_Qpositive_to_Q a (a + b) (a + c) (a + b + c + d) e 
   (e + f) (e + g) (e + f + g + h) p1 p2.
Proof.
 intros.
 unfold spec_Qquadratic_Qpositive_to_Q in |- *.
 do 6 rewrite Qmult_Z_nR.
 rewrite Qpos_nR.
 repeat rewrite <- Qplus_assoc. 
 repeat rewrite Z_to_Qplus.
 apply f_equal2 with Q Q.
 abstract ring.
 apply f_equal with Q.
 abstract ring.
Qed.

Lemma spec_Qquadratic_Qpositive_to_Q_nR_nR_unfolded :
 forall (a b c d e f g h : Z) (p1 p2 : Qpositive),
 Qmult
   (Qplus
      (Qplus
         (Qplus (Qmult (Qmult a (Qpos (nR p1))) (Qpos (nR p2)))
            (Qmult b (Qpos (nR p1)))) (Qmult c (Qpos (nR p2)))) d)
   (Qinv
      (Qplus
         (Qplus
            (Qplus (Qmult (Qmult e (Qpos (nR p1))) (Qpos (nR p2)))
               (Qmult f (Qpos (nR p1)))) (Qmult g (Qpos (nR p2)))) h)) =
 Qmult
   (Qplus
      (Qplus
         (Qplus (Qmult (Qmult a (Qpos p1)) (Qpos p2))
            (Qmult (a + b)%Z (Qpos p1))) (Qmult (a + c)%Z (Qpos p2)))
      (a + b + c + d)%Z)
   (Qinv
      (Qplus
         (Qplus
            (Qplus (Qmult (Qmult e (Qpos p1)) (Qpos p2))
               (Qmult (e + f)%Z (Qpos p1))) (Qmult (e + g)%Z (Qpos p2)))
         (e + f + g + h)%Z)).
Proof spec_Qquadratic_Qpositive_to_Q_nR_nR.


Lemma spec_Qquadratic_Qpositive_to_Q_nR_dL :
 forall (a b c d e f g h : Z) (p1 p2 : Qpositive),
 spec_Qquadratic_Qpositive_to_Q a b c d e f g h (nR p1) (dL p2) =
 spec_Qquadratic_Qpositive_to_Q (a + b) b (a + b + c + d) 
   (b + d) (e + f) f (e + f + g + h) (f + h) p1 p2.
Proof.
Opaque Qmult Qplus Qinv Qone.
 abstract (intros a b c d e f g h p1 p2;
            unfold spec_Qquadratic_Qpositive_to_Q at 1 in |- *;
            rewrite Qdiv_num_denom with (p := Qplus (Qpos p2) Qone);
            [ idtac | discriminate ];
            unfold spec_Qquadratic_Qpositive_to_Q in |- *;
            repeat rewrite Z_to_Qplus; rewrite Qpos_nR; 
            rewrite Qpos_dL; apply f_equal2 with Q Q;
            [ field | apply f_equal with Q; field ]; 
            discriminate).
Qed.


Lemma spec_Qquadratic_Qpositive_to_Q_nR_dL_unfolded :
 forall (a b c d e f g h : Z) (p1 p2 : Qpositive),
 Qmult
   (Qplus
      (Qplus
         (Qplus (Qmult (Qmult a (Qpos (nR p1))) (Qpos (dL p2)))
            (Qmult b (Qpos (nR p1)))) (Qmult c (Qpos (dL p2)))) d)
   (Qinv
      (Qplus
         (Qplus
            (Qplus (Qmult (Qmult e (Qpos (nR p1))) (Qpos (dL p2)))
               (Qmult f (Qpos (nR p1)))) (Qmult g (Qpos (dL p2)))) h)) =
 Qmult
   (Qplus
      (Qplus
         (Qplus (Qmult (Qmult (a + b)%Z (Qpos p1)) (Qpos p2))
            (Qmult b (Qpos p1))) (Qmult (a + b + c + d)%Z (Qpos p2)))
      (b + d)%Z)
   (Qinv
      (Qplus
         (Qplus
            (Qplus (Qmult (Qmult (e + f)%Z (Qpos p1)) (Qpos p2))
               (Qmult f (Qpos p1))) (Qmult (e + f + g + h)%Z (Qpos p2)))
         (f + h)%Z)).
Proof spec_Qquadratic_Qpositive_to_Q_nR_dL.



Lemma spec_Qquadratic_Qpositive_to_Q_dL_nR :
 forall (a b c d e f g h : Z) (p1 p2 : Qpositive),
 spec_Qquadratic_Qpositive_to_Q a b c d e f g h (dL p1) (nR p2) =
 spec_Qquadratic_Qpositive_to_Q (a + c) (a + b + c + d) c 
   (c + d) (e + g) (e + f + g + h) g (g + h) p1 p2.
Proof.
 abstract (intros a b c d e f g h p1 p2;
            rewrite spec_Qquadratic_Qpositive_to_Q_commut;
            rewrite spec_Qquadratic_Qpositive_to_Q_nR_dL;
            rewrite spec_Qquadratic_Qpositive_to_Q_commut;
            replace (a + b + c + d)%Z with (a + c + b + d)%Z;
            [ replace (e + f + g + h)%Z with (e + g + f + h)%Z;
               [ reflexivity | ring ]
            | ring ]).
Qed.


Lemma spec_Qquadratic_Qpositive_to_Q_dL_nR_unfolded :
 forall (a b c d e f g h : Z) (p1 p2 : Qpositive),
 Qmult
   (Qplus
      (Qplus
         (Qplus (Qmult (Qmult a (Qpos (dL p1))) (Qpos (nR p2)))
            (Qmult b (Qpos (dL p1)))) (Qmult c (Qpos (nR p2)))) d)
   (Qinv
      (Qplus
         (Qplus
            (Qplus (Qmult (Qmult e (Qpos (dL p1))) (Qpos (nR p2)))
               (Qmult f (Qpos (dL p1)))) (Qmult g (Qpos (nR p2)))) h)) =
 Qmult
   (Qplus
      (Qplus
         (Qplus (Qmult (Qmult (a + c)%Z (Qpos p1)) (Qpos p2))
            (Qmult (a + b + c + d)%Z (Qpos p1))) (Qmult c (Qpos p2)))
      (c + d)%Z)
   (Qinv
      (Qplus
         (Qplus
            (Qplus (Qmult (Qmult (e + g)%Z (Qpos p1)) (Qpos p2))
               (Qmult (e + f + g + h)%Z (Qpos p1))) 
            (Qmult g (Qpos p2))) (g + h)%Z)).
Proof spec_Qquadratic_Qpositive_to_Q_dL_nR.



Lemma spec_Qquadratic_Qpositive_to_Q_dL_dL :
 forall (a b c d e f g h : Z) (p1 p2 : Qpositive),
 spec_Qquadratic_Qpositive_to_Q a b c d e f g h (dL p1) (dL p2) =
 spec_Qquadratic_Qpositive_to_Q (a + b + c + d) (b + d) 
   (c + d) d (e + f + g + h) (f + h) (g + h) h p1 p2.
Proof.
 abstract (intros a b c d e f g h p1 p2;
            unfold spec_Qquadratic_Qpositive_to_Q at 1 in |- *;
            rewrite
             Qdiv_num_denom
                            with
                            (p := 
                              Qmult (Qplus (Qpos p1) Qone)
                                (Qplus (Qpos p2) Qone));
            [ idtac | discriminate ];
            unfold spec_Qquadratic_Qpositive_to_Q in |- *;
            repeat rewrite Z_to_Qplus; do 2 rewrite Qpos_dL;
            apply f_equal2 with Q Q; [ field | apply f_equal with Q; field ];
            split; discriminate).
Qed.


Lemma spec_Qquadratic_Qpositive_to_Q_dL_dL_unfolded :
 forall (a b c d e f g h : Z) (p1 p2 : Qpositive),
 Qmult
   (Qplus
      (Qplus
         (Qplus (Qmult (Qmult a (Qpos (dL p1))) (Qpos (dL p2)))
            (Qmult b (Qpos (dL p1)))) (Qmult c (Qpos (dL p2)))) d)
   (Qinv
      (Qplus
         (Qplus
            (Qplus (Qmult (Qmult e (Qpos (dL p1))) (Qpos (dL p2)))
               (Qmult f (Qpos (dL p1)))) (Qmult g (Qpos (dL p2)))) h)) =
 Qmult
   (Qplus
      (Qplus
         (Qplus (Qmult (Qmult (a + b + c + d)%Z (Qpos p1)) (Qpos p2))
            (Qmult (b + d)%Z (Qpos p1))) (Qmult (c + d)%Z (Qpos p2))) d)
   (Qinv
      (Qplus
         (Qplus
            (Qplus (Qmult (Qmult (e + f + g + h)%Z (Qpos p1)) (Qpos p2))
               (Qmult (f + h)%Z (Qpos p1))) (Qmult (g + h)%Z (Qpos p2))) h)).
Proof spec_Qquadratic_Qpositive_to_Q_dL_dL.


Lemma spec_Qquadratic_Qpositive_to_Qpositive2_nR_nR :
 forall (a b c d e f g h : Z) (p1 p2 : Qpositive),
 spec_Qquadratic_Qpositive_to_Qpositive2 a b c d e f g h (nR p1) (nR p2) =
 spec_Qquadratic_Qpositive_to_Qpositive2 a (a + b) 
   (a + c) (a + b + c + d) e (e + f) (e + g) (e + f + g + h) p1 p2.
Proof.
 abstract (intros a b c d e f g h p1 p2;
            unfold spec_Qquadratic_Qpositive_to_Qpositive2 in |- *;
            do 6 rewrite Qmult_Z_nR; rewrite Qpos_nR;
            repeat rewrite Z_to_Qplus;
            apply f_equal2 with Qpositive Qpositive;
            try apply f_equal with Qpositive; apply f_equal with Q;
            abstract ring).
Qed.


Lemma spec_Qquadratic_Qpositive_to_Qpositive2_nR_dL :
 forall (a b c d e f g h : Z) (p1 p2 : Qpositive),
 Qplus
   (Qplus
      (Qplus (Qmult (Qmult (Qplus a b) (Qpos p1)) (Qpos p2))
         (Qmult b (Qpos p1)))
      (Qmult (Qplus (Qplus (Qplus a b) c) d) (Qpos p2))) 
   (Qplus b d) <> Zero ->
 Qplus
   (Qplus
      (Qplus (Qmult (Qmult (Qplus e f) (Qpos p1)) (Qpos p2))
         (Qmult f (Qpos p1)))
      (Qmult (Qplus (Qplus (Qplus e f) g) h) (Qpos p2))) 
   (Qplus f h) <> Zero ->
 spec_Qquadratic_Qpositive_to_Qpositive2 a b c d e f g h (nR p1) (dL p2) =
 spec_Qquadratic_Qpositive_to_Qpositive2 (a + b) b 
   (a + b + c + d) (b + d) (e + f) f (e + f + g + h) 
   (f + h) p1 p2.
Proof.
 abstract (intros a b c d e f g h p1 p2 H_num H_denom;
            unfold spec_Qquadratic_Qpositive_to_Qpositive2 at 1 in |- *;
            rewrite <- Q_tail_Qinv; rewrite <- Q_tail_Qmult; 
            rewrite Qpos_nR; rewrite Qpos_dL;
            [ idtac
            | intro H;
               apply
                (Qmult_resp_nonzero _ (Qinv (Qplus (Qpos p2) Qone)) H_num);
               [ discriminate | rewrite <- H; field; discriminate ]
            | apply Qinv_resp_nonzero; intro H;
               apply
                (Qmult_resp_nonzero _ (Qinv (Qplus (Qpos p2) Qone)) H_denom);
               [ discriminate | rewrite <- H; field; discriminate ] ];
            rewrite Qdiv_num_denom with (p := Qplus (Qpos p2) Qone);
            [ idtac | discriminate ];
            unfold spec_Qquadratic_Qpositive_to_Qpositive2 in |- *;
            repeat rewrite Z_to_Qplus; rewrite <- Q_tail_Qinv;
            rewrite <- Q_tail_Qmult;
            [ idtac | assumption | apply Qinv_resp_nonzero; assumption ];
            apply f_equal with Q; apply f_equal2 with Q Q;
            [ field | apply f_equal with Q; field ]; 
            discriminate).
Qed.  



Lemma spec_Qquadratic_Qpositive_to_Qpositive2_dL_nR :
 forall (a b c d e f g h : Z) (p1 p2 : Qpositive),
 Qplus
   (Qplus
      (Qplus (Qmult (Qmult (Qplus a c) (Qpos p1)) (Qpos p2))
         (Qmult (Qplus (Qplus (Qplus a b) c) d) (Qpos p1)))
      (Qmult c (Qpos p2))) (Qplus c d) <> Zero ->
 Qplus
   (Qplus
      (Qplus (Qmult (Qmult (Qplus e g) (Qpos p1)) (Qpos p2))
         (Qmult (Qplus (Qplus (Qplus e f) g) h) (Qpos p1)))
      (Qmult g (Qpos p2))) (Qplus g h) <> Zero ->
 spec_Qquadratic_Qpositive_to_Qpositive2 a b c d e f g h (dL p1) (nR p2) =
 spec_Qquadratic_Qpositive_to_Qpositive2 (a + c) (a + b + c + d) c 
   (c + d) (e + g) (e + f + g + h) g (g + h) p1 p2.
Proof.
 intros a b c d e f g h p1 p2 H_num H_denom;
  rewrite spec_Qquadratic_Qpositive_to_Qpositive2_commut;
  rewrite spec_Qquadratic_Qpositive_to_Qpositive2_nR_dL;
  [ idtac
  | intro H; apply H_num; rewrite <- H; ring
  | intro H; apply H_denom; rewrite <- H; ring ];
  rewrite spec_Qquadratic_Qpositive_to_Qpositive2_commut;
  replace (a + b + c + d)%Z with (a + c + b + d)%Z;
  [ replace (e + f + g + h)%Z with (e + g + f + h)%Z; [ reflexivity | ring ]
  | ring ].
Qed.


Lemma spec_Qquadratic_Qpositive_to_Qpositive2_dL_dL :
 forall (a b c d e f g h : Z) (p1 p2 : Qpositive),
 Qplus
   (Qplus
      (Qplus
         (Qmult (Qmult (Qplus (Qplus (Qplus a b) c) d) (Qpos p1)) (Qpos p2))
         (Qmult (Qplus b d) (Qpos p1))) (Qmult (Qplus c d) (Qpos p2))) d <>
 Zero ->
 Qplus
   (Qplus
      (Qplus
         (Qmult (Qmult (Qplus (Qplus (Qplus e f) g) h) (Qpos p1)) (Qpos p2))
         (Qmult (Qplus f h) (Qpos p1))) (Qmult (Qplus g h) (Qpos p2))) h <>
 Zero ->
 spec_Qquadratic_Qpositive_to_Qpositive2 a b c d e f g h (dL p1) (dL p2) =
 spec_Qquadratic_Qpositive_to_Qpositive2 (a + b + c + d) 
   (b + d) (c + d) d (e + f + g + h) (f + h) (g + h) h p1 p2.
Proof.
 abstract (intros a b c d e f g h p1 p2 H_num H_denom;
            unfold spec_Qquadratic_Qpositive_to_Qpositive2 at 1 in |- *;
            rewrite <- Q_tail_Qinv; rewrite <- Q_tail_Qmult;
            repeat rewrite Qpos_dL;
            [ idtac
            | intro H;
               apply
                (Qmult_resp_nonzero _
                   (Qinv
                      (Qmult (Qplus (Qpos p1) Qone) (Qplus (Qpos p2) Qone)))
                   H_num);
               [ discriminate | rewrite <- H; field; split; discriminate ]
            | apply Qinv_resp_nonzero; intro H;
               apply
                (Qmult_resp_nonzero _
                   (Qinv
                      (Qmult (Qplus (Qpos p1) Qone) (Qplus (Qpos p2) Qone)))
                   H_denom);
               [ discriminate | rewrite <- H; field; split; discriminate ] ];
            rewrite
             Qdiv_num_denom
                            with
                            (p := 
                              Qmult (Qplus (Qpos p1) Qone)
                                (Qplus (Qpos p2) Qone));
            [ idtac | discriminate ];
            unfold spec_Qquadratic_Qpositive_to_Qpositive2 in |- *;
            repeat rewrite Z_to_Qplus; rewrite <- Q_tail_Qinv;
            rewrite <- Q_tail_Qmult;
            [ idtac | assumption | apply Qinv_resp_nonzero; assumption ];
            apply f_equal with Q; apply f_equal2 with Q Q;
            [ field | apply f_equal with Q; field ]; 
            split; discriminate).
Qed.


Lemma spec_Qquadratic_Qpositive_to_Qpositive2_nR_emission :
 forall (a b c d e f g h : Z) (p1 p2 : Qpositive),
 Qlt Zero
   (Qplus
      (Qplus
         (Qplus (Qmult (Qmult a (Qpos p1)) (Qpos p2)) (Qmult b (Qpos p1)))
         (Qmult c (Qpos p2))) d) ->
 Qlt Zero
   (Qplus
      (Qplus
         (Qplus (Qmult (Qmult e (Qpos p1)) (Qpos p2)) (Qmult f (Qpos p1)))
         (Qmult g (Qpos p2))) h) ->
 Qlt Zero
   (Qplus
      (Qplus
         (Qplus (Qmult (Qmult (a - e)%Z (Qpos p1)) (Qpos p2))
            (Qmult (b - f)%Z (Qpos p1))) (Qmult (c - g)%Z (Qpos p2)))
      (d - h)%Z) ->
 nR
   (spec_Qquadratic_Qpositive_to_Qpositive2 (a - e) 
      (b - f) (c - g) (d - h) e f g h p1 p2) =
 spec_Qquadratic_Qpositive_to_Qpositive2 a b c d e f g h p1 p2.
Proof.
 intros a b c d e f g h p1 p2 Habcd Hefgh Habcdefgh;
  generalize (Qlt_not_eq _ _ Habcd) (Qlt_not_eq _ _ Hefgh)
   (Qlt_not_eq _ _ Habcdefgh); intros Habcd' Hefgh' Habcdefgh'.
 rewrite what_nR_does.
 unfold spec_Qquadratic_Qpositive_to_Qpositive2 in |- *.
 rewrite <- Q_tail_Qinv.
 repeat rewrite <- Q_tail_Qmult;
  match goal with
  |  |- (Qinv _ <> _) => apply Qinv_resp_nonzero
  |  |- _ => idtac
  end; try assumption.
 replace One with (Q_tail Qone); trivial.
 rewrite <- Q_tail_Qplus_pos.
 apply f_equal with Q.
 repeat rewrite Z_to_Qminus. 
 abstract (field; assumption).
 apply Qlt_mult_pos_pos; try apply Qinv_pos; assumption.
 apply Qlt_zero_one.
Qed.


Lemma spec_Qquadratic_Qpositive_to_Qpositive2_dL_emission :
 forall (a b c d e f g h : Z) (p1 p2 : Qpositive),
 Qlt Zero
   (Qplus
      (Qplus
         (Qplus (Qmult (Qmult a (Qpos p1)) (Qpos p2)) (Qmult b (Qpos p1)))
         (Qmult c (Qpos p2))) d) ->
 Qlt Zero
   (Qplus
      (Qplus
         (Qplus (Qmult (Qmult e (Qpos p1)) (Qpos p2)) (Qmult f (Qpos p1)))
         (Qmult g (Qpos p2))) h) ->
 Qlt Zero
   (Qplus
      (Qplus
         (Qplus (Qmult (Qmult (e - a)%Z (Qpos p1)) (Qpos p2))
            (Qmult (f - b)%Z (Qpos p1))) (Qmult (g - c)%Z (Qpos p2)))
      (h - d)%Z) ->
 dL
   (spec_Qquadratic_Qpositive_to_Qpositive2 a b c d 
      (e - a) (f - b) (g - c) (h - d) p1 p2) =
 spec_Qquadratic_Qpositive_to_Qpositive2 a b c d e f g h p1 p2.
Proof.
 intros a b c d e f g h p1 p2 Habcd Hefgh Habcdefgh;
  generalize (Qlt_not_eq _ _ Habcd) (Qlt_not_eq _ _ Hefgh)
   (Qlt_not_eq _ _ Habcdefgh); intros Habcd' Hefgh' Habcdefgh'.
 rewrite what_dL_does.
 unfold spec_Qquadratic_Qpositive_to_Qpositive2 in |- *.
 repeat rewrite <- Q_tail_Qinv.
 repeat rewrite <- Q_tail_Qmult;
  match goal with
  |  |- (Qinv _ <> _) => apply Qinv_resp_nonzero
  |  |- _ => idtac
  end; try assumption.
 replace One with (Q_tail Qone); trivial.
 rewrite <- Q_tail_Qplus_pos;
  [ idtac
  | apply Qlt_mult_pos_pos; try apply Qinv_pos; assumption
  | apply Qlt_zero_one ].
 rewrite <- Q_tail_Qinv.
 repeat rewrite <- Q_tail_Qmult;
  repeat
   match goal with
   |  |- (Qinv _ <> _) => apply Qinv_resp_nonzero
   |  |- (Qmult _ _ <> _) => apply Qmult_resp_nonzero
   end;
  [ idtac
  | assumption
  | assumption
  | apply Qlt_not_eq; apply Qlt_plus_pos_pos;
     [ apply Qlt_mult_pos_pos; try apply Qinv_pos; assumption
     | apply Qlt_zero_one ] ].

 apply f_equal with Q.
 repeat rewrite Z_to_Qminus.
 repeat rewrite Z_to_Qminus in Habcdefgh'.
 replace
  (Qplus
     (Qmult
        (Qplus
           (Qplus
              (Qplus (Qmult (Qmult a (Qpos p1)) (Qpos p2))
                 (Qmult b (Qpos p1))) (Qmult c (Qpos p2))) d)
        (Qinv
           (Qplus
              (Qplus
                 (Qplus (Qmult (Qmult (Qminus e a) (Qpos p1)) (Qpos p2))
                    (Qmult (Qminus f b) (Qpos p1)))
                 (Qmult (Qminus g c) (Qpos p2))) (Qminus h d)))) Qone) with
  (Qmult
     (Qplus
        (Qplus
           (Qplus (Qmult (Qmult e (Qpos p1)) (Qpos p2)) (Qmult f (Qpos p1)))
           (Qmult g (Qpos p2))) h)
     (Qinv
        (Qplus
           (Qplus
              (Qplus (Qmult (Qmult (Qminus e a) (Qpos p1)) (Qpos p2))
                 (Qmult (Qminus f b) (Qpos p1)))
              (Qmult (Qminus g c) (Qpos p2))) (Qminus h d)))).
 symmetry  in |- *.
 apply Qdiv_num_denom.
 apply Qinv_resp_nonzero.
 assumption.

 abstract (field; repeat rewrite Z_to_Qminus in Habcdefgh'; assumption).
Qed.


Lemma outside_square_correct_1 :
 forall (a b c d : Z) (p1 p2 : Qpositive),
 (2 < outside_square a b c d)%Z ->
 ~ (b = 0%Z /\ c = 0%Z /\ d = 0%Z) ->
 Qlt Zero
   (Qplus
      (Qplus
         (Qplus (Qmult (Qmult a (Qpos p1)) (Qpos p2)) (Qmult b (Qpos p1)))
         (Qmult c (Qpos p2))) d).
Proof.
 intros a b c d p1 p2 H_o2_gt_2 Hbcd;
  generalize (outside_square_3 _ _ _ _ H_o2_gt_2)
   (outside_square_4 _ _ _ _ H_o2_gt_2) (outside_square_5 _ _ _ _ H_o2_gt_2)
   (outside_square_6 _ _ _ _ H_o2_gt_2); intros Ha Hb Hc Hd;
  generalize (triple_not_equal_zero _ _ _ Hbcd); intros [H_| [H_| H_]];
  match goal with
  | id1:(?X1 <> 0%Z),id2:(0 <= ?X1)%Z |- _ =>
      generalize (Zle_neq_Zlt 0 X1 id2 id1); intro H_lt
  end.
 (* b<>0 *)
 abstract (apply Qlt_le_reg_pos;
            [ apply Qlt_le_reg_pos;
               [ apply Qle_lt_reg_pos; [ idtac | apply Qlt_mult_pos_pos ]
               | idtac ]
            | idtac ];
            try (repeat apply Qle_mult_nonneg_nonneg; try auto with *);
            replace Zero with (Z_to_Q 0); trivial;
            apply Z_to_Qle || apply Z_to_Qlt; assumption).
 (* c<>0 *)
 abstract (apply Qlt_le_reg_pos;
            [ apply Qle_lt_reg_pos;
               [ idtac | apply Qlt_mult_pos_pos; try auto with * ]
            | idtac ]; try apply Qle_plus_pos_pos;
            try (repeat apply Qle_mult_nonneg_nonneg; try auto with *);
            replace Zero with (Z_to_Q 0); trivial;
            apply Z_to_Qle || apply Z_to_Qlt; assumption).
 (* d<>0 *)
 abstract (apply Qle_lt_reg_pos; try repeat apply Qle_plus_pos_pos;
            try (repeat apply Qle_mult_nonneg_nonneg; try auto with *);
            replace Zero with (Z_to_Q 0); trivial;
            apply Z_to_Qle || apply Z_to_Qlt; assumption).
Qed.

Lemma outside_square_correct_2 :
 forall (a b c d : Z) (p1 p2 : Qpositive),
 (outside_square a b c d < -2)%Z ->
 ~ (b = 0%Z /\ c = 0%Z /\ d = 0%Z) ->
 Qlt
   (Qplus
      (Qplus
         (Qplus (Qmult (Qmult a (Qpos p1)) (Qpos p2)) (Qmult b (Qpos p1)))
         (Qmult c (Qpos p2))) d) Zero.
Proof.
 intros a b c d p1 p2 H_o2_lt_min_2 Hbcd;
  generalize (outside_square_7 _ _ _ _ H_o2_lt_min_2)
   (outside_square_8 _ _ _ _ H_o2_lt_min_2)
   (outside_square_9 _ _ _ _ H_o2_lt_min_2)
   (outside_square_10 _ _ _ _ H_o2_lt_min_2); intros Ha Hb Hc Hd;
  generalize (triple_not_equal_zero _ _ _ Hbcd); intros [H_| [H_| H_]];
  match goal with
  | id1:(?X1 <> 0%Z),id2:(?X1 <= 0)%Z |- _ =>
      generalize (sym_not_eq id1); clear id1; intro id1;
       generalize (Zle_neq_Zlt X1 0 id2 id1); intro H_lt
  end.
 (* b<>0 *)
 abstract (apply Qlt_le_reg_neg;
            [ apply Qlt_le_reg_neg;
               [ apply Qle_lt_reg_neg; [ idtac | apply Qlt_mult_neg_pos ]
               | idtac ]
            | idtac ];
            try (repeat apply Qle_mult_nonpos_nonneg; try auto with *);
            replace Zero with (Z_to_Q 0); trivial;
            apply Z_to_Qle || apply Z_to_Qlt; assumption).
 (* c<>0 *)
 abstract (apply Qlt_le_reg_neg;
            [ apply Qle_lt_reg_neg;
               [ idtac | apply Qlt_mult_neg_pos; try auto with * ]
            | idtac ]; try apply Qle_plus_neg_neg;
            try (repeat apply Qle_mult_nonpos_nonneg; try auto with *);
            replace Zero with (Z_to_Q 0); trivial;
            apply Z_to_Qle || apply Z_to_Qlt; assumption).
 (* d<>0 *)
 abstract (apply Qle_lt_reg_neg; try repeat apply Qle_plus_neg_neg;
            try (repeat apply Qle_mult_nonpos_nonneg; try auto with *);
            replace Zero with (Z_to_Q 0); trivial;
            apply Z_to_Qle || apply Z_to_Qlt; assumption).
Qed.


Ltac Inside_Square_Qsgn_ p1 p2 :=
  repeat
   match goal with
   | id1:(?X1 < ?X2)%Z |- _ =>
       unfold X2 in id1 || unfold X1 in id1;
        repeat
         match goal with
         | id1:(2 < outside_square ?X1 ?X2 ?X3 ?X4)%Z,id2:
         (~ (?X2 = 0%Z /\ ?X3 = 0%Z /\ ?X4 = 0%Z)) |- _ =>
             generalize
              (Qsgn_7 _ (outside_square_correct_1 X1 X2 X3 X4 p1 p2 id1 id2));
              clear id1
         | id1:(outside_square ?X1 ?X2 ?X3 ?X4 < -2)%Z,id2:
         (~ (?X2 = 0%Z /\ ?X3 = 0%Z /\ ?X4 = 0%Z)) |- _ =>
             generalize
              (Qsgn_8 _ (outside_square_correct_2 X1 X2 X3 X4 p1 p2 id1 id2));
              clear id1
         end
   end.



Lemma quadratic_sign :
 forall (a b c d e f g h : Z) (p1 p2 : Qpositive)
   (H_Qquadratic_sg_denom_nonzero : Qquadratic_sg_denom_nonzero e f g h p1 p2),
 q_sign a b c d e f g h p1 p2 H_Qquadratic_sg_denom_nonzero =
 Qsgn (spec_Qquadratic_Qpositive_to_Q a b c d e f g h p1 p2).
Proof.
 fix quadratic_sign 9.
 intros a b c d e f g h.
 unfold q_sign in |- *.
 set (o1 := outside_square a b c d) in *.
 set (o2 := outside_square e f g h) in *.
 intros [xs| xs| ].
  (* p1=(nR xs) *)
  intros [ys| ys| ] H_Qquadratic_sg_denom_nonzero.
(*####################################################################################################*)
(* Begin CHUNK 1 *)
   (* p2=(dL ys) *)
   case (three_integers_dec_inf b c d).
    (* `b = 0`/\`c = 0`/\`d = 0` *)
    intros (Hb, (Hc, Hd)).
    case (three_integers_dec_inf f g h).  
     (* nR_nR_1: `f = 0`/\`g = 0`/\`h = 0` *)
     clear o1 o2 quadratic_sign; intros (Hf, (Hg, Hh));
      rewrite
       (Qquadratic_sign_nRdL_nRdL_1 a b c d e f g h 
          (nR xs) (nR ys) H_Qquadratic_sg_denom_nonzero)
       ; discriminate || (try (repeat split; assumption)); 
      subst; unfold spec_Qquadratic_Qpositive_to_Q in |- *; 
      simpl in |- *;
      transitivity
       (Qsgn
          (Qmult (Qmult (Qmult a (Qpos (nR xs))) (Qpos (nR ys)))
             (Qinv (Qmult (Qmult e (Qpos (nR xs))) (Qpos (nR ys))))));
      [ idtac
      | apply f_equal with Q; apply f_equal2 with Q Q;
         [ idtac | apply f_equal with Q ]; abstract 
         ring ]; rewrite Qsgn_15; rewrite Qsgn_28; 
      repeat rewrite Qsgn_15; simpl in |- *; do 2 rewrite Qsgn_29;
      abstract ring.
     (* ~(`f = 0`/\`g = 0`/\`h = 0`) *)
     case (Z_lt_dec 2 o2).
      (*  nR_nR_2: `2 < o2` *)
      clear quadratic_sign; intros H_o2_gt_2 Hfgh';
       rewrite
        (Qquadratic_sign_nRdL_nRdL_2 a b c d e f g h 
           (nR xs) (nR ys) H_Qquadratic_sg_denom_nonzero)
        ; discriminate || (try (repeat split; assumption)); 
       subst; unfold spec_Qquadratic_Qpositive_to_Q in |- *; 
       rewrite Qsgn_15; rewrite Qsgn_28;
       rewrite
        (Qsgn_7 _
           (outside_square_correct_1 _ _ _ _ (nR xs) (nR ys) H_o2_gt_2 Hfgh'))
        ; clear o1 o2 H_o2_gt_2;
       replace
        (Qplus
           (Qplus
              (Qplus (Qmult (Qmult a (Qpos (nR xs))) (Qpos (nR ys)))
                 (Qmult 0%Z (Qpos (nR xs)))) (Qmult 0%Z (Qpos (nR ys)))) 0%Z)
        with (Qmult (Qmult a (Qpos (nR xs))) (Qpos (nR ys)));
       [ idtac | simpl; ring ]; repeat rewrite Qsgn_15; 
       simpl in |- *; rewrite Qsgn_29; abstract ring.
      case (Z_lt_dec o2 (-2)).
       (* nR_nR_3: `o2<(-2)` *)
       clear quadratic_sign; intros H_o2_lt_min_2 H_o2_gt_2' Hfgh';
        rewrite
         (Qquadratic_sign_nRdL_nRdL_3 a b c d e f g h 
            (nR xs) (nR ys) H_Qquadratic_sg_denom_nonzero)
         ; discriminate || (try (repeat split; assumption)); 
        subst; unfold spec_Qquadratic_Qpositive_to_Q in |- *; 
        rewrite Qsgn_15; rewrite Qsgn_28;
        rewrite
         (Qsgn_8 _
            (outside_square_correct_2 _ _ _ _ (nR xs) 
               (nR ys) H_o2_lt_min_2 Hfgh'));
        clear o1 o2 H_o2_lt_min_2 H_o2_gt_2';
        replace
         (Qplus
            (Qplus
               (Qplus (Qmult (Qmult a (Qpos (nR xs))) (Qpos (nR ys)))
                  (Qmult 0%Z (Qpos (nR xs)))) (Qmult 0%Z (Qpos (nR ys)))) 0%Z)
         with (Qmult (Qmult a (Qpos (nR xs))) (Qpos (nR ys)));
        [ idtac | simpl; ring ]; repeat rewrite Qsgn_15; 
        simpl in |- *; rewrite Qsgn_29; abstract ring.
       (* nR_nR_4:   ~`o2 < (-2)` /\ ~`2 < o2`/\~(`f = 0`/\`g = 0`/\`h = 0`) *) 
       intros H_o2_lt_min_2' H_o2_gt_2' Hfgh';
        rewrite
         (Qquadratic_sign_nR_nR_4 a b c d e f g h (nR xs) xs 
            (nR ys) ys H_Qquadratic_sg_denom_nonzero
            (Qquadratic_signok_1 _ _ _ _ _ _ H_Qquadratic_sg_denom_nonzero)
            (refl_equal (nR xs)) (refl_equal (nR ys)))
         ; discriminate || (try (repeat split; assumption));
        rewrite spec_Qquadratic_Qpositive_to_Q_nR_nR;
        rewrite <-
         (quadratic_sign a (a + b)%Z (a + c)%Z (a + b + c + d)%Z e 
            (e + f)%Z (e + g)%Z (e + f + g + h)%Z xs ys
            (Qquadratic_signok_1 e f g h xs ys H_Qquadratic_sg_denom_nonzero))
         ; reflexivity.
       (* ~(`b = 0`/\`c = 0`/\`d = 0`) *)
       intro Hbcd'.  
       case (three_integers_dec_inf f g h).  
        (* `f = 0`/\`g = 0`/\`h = 0` *)
        intros (Hf, (Hg, Hh)).
        case (Z_lt_dec 2 o1).
         (*  nR_nR_5: `2 < o1` *)
         clear quadratic_sign; intros H_o1_gt_2;
          rewrite
           (Qquadratic_sign_nRdL_nRdL_5 a b c d e f g h 
              (nR xs) (nR ys) H_Qquadratic_sg_denom_nonzero)
           ; discriminate || (try (repeat split; assumption)); 
          subst; unfold spec_Qquadratic_Qpositive_to_Q in |- *;
          rewrite Qsgn_15; rewrite Qsgn_28;
          rewrite
           (Qsgn_7 _
              (outside_square_correct_1 _ _ _ _ (nR xs) 
                 (nR ys) H_o1_gt_2 Hbcd')); clear o1 o2 H_o1_gt_2;
          replace
           (Qplus
              (Qplus
                 (Qplus (Qmult (Qmult e (Qpos (nR xs))) (Qpos (nR ys)))
                    (Qmult 0%Z (Qpos (nR xs)))) (Qmult 0%Z (Qpos (nR ys))))
              0%Z) with (Qmult (Qmult e (Qpos (nR xs))) (Qpos (nR ys)));
          [ idtac | simpl; ring ]; repeat rewrite Qsgn_15; 
          rewrite Qsgn_29; unfold Qsgn in |- *; abstract 
          ring.
         case (Z_lt_dec o1 (-2)).
          (* nR_nR_6: `o1<(-2)` *)
          clear quadratic_sign; intros H_o1_lt_min_2 H_o1_gt_2';
           rewrite
            (Qquadratic_sign_nRdL_nRdL_6 a b c d e f g h 
               (nR xs) (nR ys) H_Qquadratic_sg_denom_nonzero)
            ; discriminate || (try (repeat split; assumption)); 
           subst; unfold spec_Qquadratic_Qpositive_to_Q in |- *;
           rewrite Qsgn_15; rewrite Qsgn_28;
           rewrite
            (Qsgn_8 _
               (outside_square_correct_2 _ _ _ _ (nR xs) 
                  (nR ys) H_o1_lt_min_2 Hbcd'));
           clear o1 o2 H_o1_gt_2' H_o1_lt_min_2;
           replace
            (Qplus
               (Qplus
                  (Qplus (Qmult (Qmult e (Qpos (nR xs))) (Qpos (nR ys)))
                     (Qmult 0%Z (Qpos (nR xs)))) (Qmult 0%Z (Qpos (nR ys))))
               0%Z) with (Qmult (Qmult e (Qpos (nR xs))) (Qpos (nR ys)));
           [ idtac | simpl; ring ]; repeat rewrite Qsgn_15; 
           rewrite Qsgn_29; unfold Qsgn in |- *; abstract 
           ring.
          (* nR_nR_7:   ~`o1 < (-2)` /\ ~`2 < o1` *)
          intros H_o1_lt_min_2' H_o1_gt_2';
           rewrite
            (Qquadratic_sign_nR_nR_7 a b c d e f g h 
               (nR xs) xs (nR ys) ys H_Qquadratic_sg_denom_nonzero
               (Qquadratic_signok_1 _ _ _ _ _ _ H_Qquadratic_sg_denom_nonzero)
               (refl_equal (nR xs)) (refl_equal (nR ys)))
            ; discriminate || (try (repeat split; assumption));
           rewrite spec_Qquadratic_Qpositive_to_Q_nR_nR;
           rewrite <-
            (quadratic_sign a (a + b)%Z (a + c)%Z (a + b + c + d)%Z e
               (e + f)%Z (e + g)%Z (e + f + g + h)%Z xs ys
               (Qquadratic_signok_1 e f g h xs ys
                  H_Qquadratic_sg_denom_nonzero)); 
           reflexivity.
        (* ~(`f = 0`/\`g = 0`/\`h = 0`) *)
        intro Hfgh'.
        case (inside_square_1_dec_inf o1 o2).    
         (* nR_nR_8: (inside_square_1 o1 o2) *)
         clear quadratic_sign; intro H_inside_1;
          (rewrite
            (Qquadratic_sign_nRdL_nRdL_8 a b c d e f g h 
               (nR xs) (nR ys) H_Qquadratic_sg_denom_nonzero)
            ; discriminate || (try (repeat split; assumption)));
          generalize H_inside_1; intros [(H_o1, H_o2)| (H_o1, H_o2)];
          Inside_Square_Qsgn_ (nR xs) (nR ys); intros H_num H_denom;
          unfold spec_Qquadratic_Qpositive_to_Q in |- *; 
          rewrite Qsgn_15; rewrite Qsgn_28; rewrite H_num; 
          rewrite H_denom; constructor.
         (* ~(inside_square_1 o1 o2) *)
         intro H_inside_1'.
         case (inside_square_2_dec_inf o1 o2).    
          (* nR_nR_9: (inside_square_2 o1 o2) *)
          clear quadratic_sign; intro H_inside_2;
           (rewrite
             (Qquadratic_sign_nRdL_nRdL_9 a b c d e f g h 
                (nR xs) (nR ys) H_Qquadratic_sg_denom_nonzero)
             ; discriminate || (try (repeat split; assumption)));
           generalize H_inside_2; intros [(H_o1, H_o2)| (H_o1, H_o2)];
           Inside_Square_Qsgn_ (nR xs) (nR ys); intros H_num H_denom;
           unfold spec_Qquadratic_Qpositive_to_Q in |- *; 
           rewrite Qsgn_15; rewrite Qsgn_28; rewrite H_num; 
           rewrite H_denom; constructor.
          (*  nR_nR_10: ~(inside_square_1 o1 o2)/\~(inside_square_2 o1 o2) *)
          intros H_inside_2'. 
          rewrite
           (Qquadratic_sign_nR_nR_10 a b c d e f g h 
              (nR xs) xs (nR ys) ys H_Qquadratic_sg_denom_nonzero
              (Qquadratic_signok_1 _ _ _ _ _ _ H_Qquadratic_sg_denom_nonzero)
              (refl_equal (nR xs)) (refl_equal (nR ys)))
           ; discriminate || (try (repeat split; assumption));
           rewrite spec_Qquadratic_Qpositive_to_Q_nR_nR;
           rewrite <-
            (quadratic_sign a (a + b)%Z (a + c)%Z (a + b + c + d)%Z e
               (e + f)%Z (e + g)%Z (e + f + g + h)%Z xs ys
               (Qquadratic_signok_1 e f g h xs ys
                  H_Qquadratic_sg_denom_nonzero)); 
           reflexivity.
(* End CHUNK 1 *)
(*####################################################################################################*)
(* Begin CHUNK 2 *)
(* We copy CHUNK 1 and query replace
nR_nR with nR_dL 
(nR ys) with (dL ys)
a `a+b` `a+c` `a+b+c+d` e `e+f` `e+g` `e+f+g+h` xs ys (Qquadratic_signok_1 e f g h xs ys H_Qquadratic_sg_denom_nonzero) with 
`a+b` b `a+b+c+d` `b+d` `e+f` f `e+f+g+h` `f+h` xs ys (Qquadratic_signok_2 e f g h xs ys H_Qquadratic_sg_denom_nonzero)
Qquadratic_signok_1 with Qquadratic_signok_2
*)

   (* p2=(dL ys) *)
   case (three_integers_dec_inf b c d).
    (* `b = 0`/\`c = 0`/\`d = 0` *)
    intros (Hb, (Hc, Hd)). 
    case (three_integers_dec_inf f g h).  
     (* nR_dL_1: `f = 0`/\`g = 0`/\`h = 0` *)
     clear o1 o2 quadratic_sign; intros (Hf, (Hg, Hh));
      rewrite
       (Qquadratic_sign_nRdL_nRdL_1 a b c d e f g h 
          (nR xs) (dL ys) H_Qquadratic_sg_denom_nonzero)
       ; discriminate || (try (repeat split; assumption)); 
      subst; unfold spec_Qquadratic_Qpositive_to_Q in |- *; 
      simpl in |- *;
      transitivity
       (Qsgn
          (Qmult (Qmult (Qmult a (Qpos (nR xs))) (Qpos (dL ys)))
             (Qinv (Qmult (Qmult e (Qpos (nR xs))) (Qpos (dL ys))))));
      [ idtac
      | apply f_equal with Q; apply f_equal2 with Q Q;
         [ idtac | apply f_equal with Q ]; abstract 
         ring ]; rewrite Qsgn_15; rewrite Qsgn_28; 
      repeat rewrite Qsgn_15; simpl in |- *; do 2 rewrite Qsgn_29;
      abstract ring.
     (* ~(`f = 0`/\`g = 0`/\`h = 0`) *)
     case (Z_lt_dec 2 o2).
      (*  nR_dL_2: `2 < o2` *)
      clear quadratic_sign; intros H_o2_gt_2 Hfgh';
       rewrite
        (Qquadratic_sign_nRdL_nRdL_2 a b c d e f g h 
           (nR xs) (dL ys) H_Qquadratic_sg_denom_nonzero)
        ; discriminate || (try (repeat split; assumption)); 
       subst; unfold spec_Qquadratic_Qpositive_to_Q in |- *; 
       rewrite Qsgn_15; rewrite Qsgn_28;
       rewrite
        (Qsgn_7 _
           (outside_square_correct_1 _ _ _ _ (nR xs) (dL ys) H_o2_gt_2 Hfgh'))
        ; clear o1 o2 H_o2_gt_2;
       replace
        (Qplus
           (Qplus
              (Qplus (Qmult (Qmult a (Qpos (nR xs))) (Qpos (dL ys)))
                 (Qmult 0%Z (Qpos (nR xs)))) (Qmult 0%Z (Qpos (dL ys)))) 0%Z)
        with (Qmult (Qmult a (Qpos (nR xs))) (Qpos (dL ys)));
       [ idtac | simpl; ring ]; repeat rewrite Qsgn_15; 
       simpl in |- *; rewrite Qsgn_29; abstract ring.
      case (Z_lt_dec o2 (-2)).
       (* nR_dL_3: `o2<(-2)` *)
       clear quadratic_sign; intros H_o2_lt_min_2 H_o2_gt_2' Hfgh';
        rewrite
         (Qquadratic_sign_nRdL_nRdL_3 a b c d e f g h 
            (nR xs) (dL ys) H_Qquadratic_sg_denom_nonzero)
         ; discriminate || (try (repeat split; assumption)); 
        subst; unfold spec_Qquadratic_Qpositive_to_Q in |- *; 
        rewrite Qsgn_15; rewrite Qsgn_28;
        rewrite
         (Qsgn_8 _
            (outside_square_correct_2 _ _ _ _ (nR xs) 
               (dL ys) H_o2_lt_min_2 Hfgh'));
        clear o1 o2 H_o2_lt_min_2 H_o2_gt_2';
        replace
         (Qplus
            (Qplus
               (Qplus (Qmult (Qmult a (Qpos (nR xs))) (Qpos (dL ys)))
                  (Qmult 0%Z (Qpos (nR xs)))) (Qmult 0%Z (Qpos (dL ys)))) 0%Z)
         with (Qmult (Qmult a (Qpos (nR xs))) (Qpos (dL ys)));
        [ idtac | simpl; ring ]; repeat rewrite Qsgn_15; 
        simpl in |- *; rewrite Qsgn_29; abstract ring.
       (* nR_dL_4:   ~`o2 < (-2)` /\ ~`2 < o2`/\~(`f = 0`/\`g = 0`/\`h = 0`) *) 
       intros H_o2_lt_min_2' H_o2_gt_2' Hfgh';
        rewrite
         (Qquadratic_sign_nR_dL_4 a b c d e f g h (nR xs) xs 
            (dL ys) ys H_Qquadratic_sg_denom_nonzero
            (Qquadratic_signok_2 _ _ _ _ _ _ H_Qquadratic_sg_denom_nonzero)
            (refl_equal (nR xs)) (refl_equal (dL ys)))
         ; discriminate || (try (repeat split; assumption));
        rewrite spec_Qquadratic_Qpositive_to_Q_nR_dL;
        rewrite <-
         (quadratic_sign (a + b)%Z b (a + b + c + d)%Z 
            (b + d)%Z (e + f)%Z f (e + f + g + h)%Z 
            (f + h)%Z xs ys
            (Qquadratic_signok_2 e f g h xs ys H_Qquadratic_sg_denom_nonzero))
         ; reflexivity.
       (* ~(`b = 0`/\`c = 0`/\`d = 0`) *)
       intro Hbcd'.  
       case (three_integers_dec_inf f g h).  
        (* `f = 0`/\`g = 0`/\`h = 0` *)
        intros (Hf, (Hg, Hh)).
        case (Z_lt_dec 2 o1).
         (*  nR_dL_5: `2 < o1` *)
         clear quadratic_sign; intros H_o1_gt_2;
          rewrite
           (Qquadratic_sign_nRdL_nRdL_5 a b c d e f g h 
              (nR xs) (dL ys) H_Qquadratic_sg_denom_nonzero)
           ; discriminate || (try (repeat split; assumption)); 
          subst; unfold spec_Qquadratic_Qpositive_to_Q in |- *;
          rewrite Qsgn_15; rewrite Qsgn_28;
          rewrite
           (Qsgn_7 _
              (outside_square_correct_1 _ _ _ _ (nR xs) 
                 (dL ys) H_o1_gt_2 Hbcd')); clear o1 o2 H_o1_gt_2;
          replace
           (Qplus
              (Qplus
                 (Qplus (Qmult (Qmult e (Qpos (nR xs))) (Qpos (dL ys)))
                    (Qmult 0%Z (Qpos (nR xs)))) (Qmult 0%Z (Qpos (dL ys))))
              0%Z) with (Qmult (Qmult e (Qpos (nR xs))) (Qpos (dL ys)));
          [ idtac | simpl; ring ]; repeat rewrite Qsgn_15; 
          rewrite Qsgn_29; unfold Qsgn in |- *; ring.
         case (Z_lt_dec o1 (-2)).
          (* nR_dL_6: `o1<(-2)` *)
          clear quadratic_sign; intros H_o1_lt_min_2 H_o1_gt_2';
           rewrite
            (Qquadratic_sign_nRdL_nRdL_6 a b c d e f g h 
               (nR xs) (dL ys) H_Qquadratic_sg_denom_nonzero)
            ; discriminate || (try (repeat split; assumption)); 
           subst; unfold spec_Qquadratic_Qpositive_to_Q in |- *;
           rewrite Qsgn_15; rewrite Qsgn_28;
           rewrite
            (Qsgn_8 _
               (outside_square_correct_2 _ _ _ _ (nR xs) 
                  (dL ys) H_o1_lt_min_2 Hbcd'));
           clear o1 o2 H_o1_gt_2' H_o1_lt_min_2;
           replace
            (Qplus
               (Qplus
                  (Qplus (Qmult (Qmult e (Qpos (nR xs))) (Qpos (dL ys)))
                     (Qmult 0%Z (Qpos (nR xs)))) (Qmult 0%Z (Qpos (dL ys))))
               0%Z) with (Qmult (Qmult e (Qpos (nR xs))) (Qpos (dL ys)));
           [ idtac | simpl; ring ]; repeat rewrite Qsgn_15; 
           rewrite Qsgn_29; unfold Qsgn in |- *; ring.
          (* nR_dL_7:   ~`o1 < (-2)` /\ ~`2 < o1` *)
          intros H_o1_lt_min_2' H_o1_gt_2';
           rewrite
            (Qquadratic_sign_nR_dL_7 a b c d e f g h 
               (nR xs) xs (dL ys) ys H_Qquadratic_sg_denom_nonzero
               (Qquadratic_signok_2 _ _ _ _ _ _ H_Qquadratic_sg_denom_nonzero)
               (refl_equal (nR xs)) (refl_equal (dL ys)))
            ; discriminate || (try (repeat split; assumption));
           rewrite spec_Qquadratic_Qpositive_to_Q_nR_dL;
           rewrite <-
            (quadratic_sign (a + b)%Z b (a + b + c + d)%Z 
               (b + d)%Z (e + f)%Z f (e + f + g + h)%Z 
               (f + h)%Z xs ys
               (Qquadratic_signok_2 e f g h xs ys
                  H_Qquadratic_sg_denom_nonzero)); 
           reflexivity.
        (* ~(`f = 0`/\`g = 0`/\`h = 0`) *)
        intro Hfgh'.
        case (inside_square_1_dec_inf o1 o2).    
         (* nR_dL_8: (inside_square_1 o1 o2) *)
         clear quadratic_sign; intro H_inside_1;
          (rewrite
            (Qquadratic_sign_nRdL_nRdL_8 a b c d e f g h 
               (nR xs) (dL ys) H_Qquadratic_sg_denom_nonzero)
            ; discriminate || (try (repeat split; assumption)));
          generalize H_inside_1; intros [(H_o1, H_o2)| (H_o1, H_o2)];
          Inside_Square_Qsgn_ (nR xs) (dL ys); intros H_num H_denom;
          unfold spec_Qquadratic_Qpositive_to_Q in |- *; 
          rewrite Qsgn_15; rewrite Qsgn_28; rewrite H_num; 
          rewrite H_denom; constructor.
         (* ~(inside_square_1 o1 o2) *)
         intro H_inside_1'.
         case (inside_square_2_dec_inf o1 o2).    
          (* nR_dL_9: (inside_square_2 o1 o2) *)
          clear quadratic_sign; intro H_inside_2;
           (rewrite
             (Qquadratic_sign_nRdL_nRdL_9 a b c d e f g h 
                (nR xs) (dL ys) H_Qquadratic_sg_denom_nonzero)
             ; discriminate || (try (repeat split; assumption)));
           generalize H_inside_2; intros [(H_o1, H_o2)| (H_o1, H_o2)];
           Inside_Square_Qsgn_ (nR xs) (dL ys); intros H_num H_denom;
           unfold spec_Qquadratic_Qpositive_to_Q in |- *; 
           rewrite Qsgn_15; rewrite Qsgn_28; rewrite H_num; 
           rewrite H_denom; constructor.
          (*  nR_dL_10: ~(inside_square_1 o1 o2)/\~(inside_square_2 o1 o2) *)
          intros H_inside_2'. 
          rewrite
           (Qquadratic_sign_nR_dL_10 a b c d e f g h 
              (nR xs) xs (dL ys) ys H_Qquadratic_sg_denom_nonzero
              (Qquadratic_signok_2 _ _ _ _ _ _ H_Qquadratic_sg_denom_nonzero)
              (refl_equal (nR xs)) (refl_equal (dL ys)))
           ; discriminate || (try (repeat split; assumption));
           rewrite spec_Qquadratic_Qpositive_to_Q_nR_dL;
           rewrite <-
            (quadratic_sign (a + b)%Z b (a + b + c + d)%Z 
               (b + d)%Z (e + f)%Z f (e + f + g + h)%Z 
               (f + h)%Z xs ys
               (Qquadratic_signok_2 e f g h xs ys
                  H_Qquadratic_sg_denom_nonzero)); 
           reflexivity.
(* End CHUNK 2 *)
(*####################################################################################################*)
(* Begin CHUNK 3 *)
  (* p2=One *)
  clear quadratic_sign.
  generalize (Qquadratic_signok_0' _ _ _ _ _ H_Qquadratic_sg_denom_nonzero).
  intro H_Qhomographic_sg_denom_nonzero.
  set
   (L3 :=
    Qhomographic_sign (a + b) (c + d) (e + f) (g + h) 
      (nR xs) H_Qhomographic_sg_denom_nonzero) in *.
  set (l1 := fst L3) in *.
  set (l2 := fst (snd L3)) in *.
  set (l3 := snd (snd L3)) in *.
  set (na := fst l2) in *.
  set (nb := fst (snd l2)) in *.
  set (nc := fst (snd (snd l2))) in *.
  set (nd := snd (snd (snd l2))) in *.
  rewrite
   (Qquadratic_sign_nRdL_One a b c d e f g h (nR xs) One
      H_Qquadratic_sg_denom_nonzero l1 na nb nc nd l3
      H_Qhomographic_sg_denom_nonzero);
   [ idtac
   | fold L3 in |- *; repeat (apply pair_2; try reflexivity)
   | discriminate
   | reflexivity ]. 
  rewrite spec_Qquadratic_Qpositive_to_Q_p_One.
  rewrite <-
   (homographic_sign (a + b) (c + d) (e + f) (g + h) 
      (nR xs) H_Qhomographic_sg_denom_nonzero).
  reflexivity.
(* End CHUNK 3 *)
  (* p1=(dL xs) *)
  intros [ys| ys| ] H_Qquadratic_sg_denom_nonzero.
(*####################################################################################################*)
(* Begin CHUNK 4 *)
(* We copy CHUNK 1 and query replace
nR_nR with dL_nR 
(nR xs) with (dL xs)
a `a+b` `a+c` `a+b+c+d` e `e+f` `e+g` `e+f+g+h` with `a+c` `a+b+c+d` c `c+d` `e+g` `e+f+g+h` g `g+h` 
Qquadratic_signok_1 with Qquadratic_signok_3
*)

   (* p2=(dL ys) *)
   case (three_integers_dec_inf b c d).
    (* `b = 0`/\`c = 0`/\`d = 0` *)
    intros (Hb, (Hc, Hd)). 
    case (three_integers_dec_inf f g h).  
     (* dL_nR_1: `f = 0`/\`g = 0`/\`h = 0` *)
     clear o1 o2 quadratic_sign; intros (Hf, (Hg, Hh));
      rewrite
       (Qquadratic_sign_nRdL_nRdL_1 a b c d e f g h 
          (dL xs) (nR ys) H_Qquadratic_sg_denom_nonzero)
       ; discriminate || (try (repeat split; assumption)); 
      subst; unfold spec_Qquadratic_Qpositive_to_Q in |- *; 
      simpl in |- *;
      transitivity
       (Qsgn
          (Qmult (Qmult (Qmult a (Qpos (dL xs))) (Qpos (nR ys)))
             (Qinv (Qmult (Qmult e (Qpos (dL xs))) (Qpos (nR ys))))));
      [ idtac
      | apply f_equal with Q; apply f_equal2 with Q Q;
         [ idtac | apply f_equal with Q ]; simpl; ring ];
         rewrite Qsgn_15; rewrite Qsgn_28; 
      repeat rewrite Qsgn_15; simpl in |- *; do 2 rewrite Qsgn_29;
      ring.
     (* ~(`f = 0`/\`g = 0`/\`h = 0`) *)
     case (Z_lt_dec 2 o2).
      (*  dL_nR_2: `2 < o2` *)
      clear quadratic_sign; intros H_o2_gt_2 Hfgh';
       rewrite
        (Qquadratic_sign_nRdL_nRdL_2 a b c d e f g h 
           (dL xs) (nR ys) H_Qquadratic_sg_denom_nonzero)
        ; discriminate || (try (repeat split; assumption)); 
       subst; unfold spec_Qquadratic_Qpositive_to_Q in |- *; 
       rewrite Qsgn_15; rewrite Qsgn_28;
       rewrite
        (Qsgn_7 _
           (outside_square_correct_1 _ _ _ _ (dL xs) (nR ys) H_o2_gt_2 Hfgh'))
        ; clear o1 o2 H_o2_gt_2;
       replace
        (Qplus
           (Qplus
              (Qplus (Qmult (Qmult a (Qpos (dL xs))) (Qpos (nR ys)))
                 (Qmult 0%Z (Qpos (dL xs)))) (Qmult 0%Z (Qpos (nR ys)))) 0%Z)
        with (Qmult (Qmult a (Qpos (dL xs))) (Qpos (nR ys)));
       [ idtac | simpl; ring ]; repeat rewrite Qsgn_15; 
       simpl in |- *; rewrite Qsgn_29; ring.
      case (Z_lt_dec o2 (-2)).
       (* dL_nR_3: `o2<(-2)` *)
       clear quadratic_sign; intros H_o2_lt_min_2 H_o2_gt_2' Hfgh';
        rewrite
         (Qquadratic_sign_nRdL_nRdL_3 a b c d e f g h 
            (dL xs) (nR ys) H_Qquadratic_sg_denom_nonzero)
         ; discriminate || (try (repeat split; assumption)); 
        subst; unfold spec_Qquadratic_Qpositive_to_Q in |- *; 
        rewrite Qsgn_15; rewrite Qsgn_28;
        rewrite
         (Qsgn_8 _
            (outside_square_correct_2 _ _ _ _ (dL xs) 
               (nR ys) H_o2_lt_min_2 Hfgh'));
        clear o1 o2 H_o2_lt_min_2 H_o2_gt_2';
        replace
         (Qplus
            (Qplus
               (Qplus (Qmult (Qmult a (Qpos (dL xs))) (Qpos (nR ys)))
                  (Qmult 0%Z (Qpos (dL xs)))) (Qmult 0%Z (Qpos (nR ys)))) 0%Z)
         with (Qmult (Qmult a (Qpos (dL xs))) (Qpos (nR ys)));
        [ idtac | simpl; ring ]; repeat rewrite Qsgn_15; 
        simpl in |- *; rewrite Qsgn_29; ring.
       (* dL_nR_4:   ~`o2 < (-2)` /\ ~`2 < o2`/\~(`f = 0`/\`g = 0`/\`h = 0`) *) 
       intros H_o2_lt_min_2' H_o2_gt_2' Hfgh';
        rewrite
         (Qquadratic_sign_dL_nR_4 a b c d e f g h (dL xs) xs 
            (nR ys) ys H_Qquadratic_sg_denom_nonzero
            (Qquadratic_signok_3 _ _ _ _ _ _ H_Qquadratic_sg_denom_nonzero)
            (refl_equal (dL xs)) (refl_equal (nR ys)))
         ; discriminate || (try (repeat split; assumption));
        rewrite spec_Qquadratic_Qpositive_to_Q_dL_nR;
        rewrite <-
         (quadratic_sign (a + c)%Z (a + b + c + d)%Z c 
            (c + d)%Z (e + g)%Z (e + f + g + h)%Z g 
            (g + h)%Z xs ys
            (Qquadratic_signok_3 e f g h xs ys H_Qquadratic_sg_denom_nonzero))
         ; reflexivity.
       (* ~(`b = 0`/\`c = 0`/\`d = 0`) *)
       intro Hbcd'.  
       case (three_integers_dec_inf f g h).  
        (* `f = 0`/\`g = 0`/\`h = 0` *)
        intros (Hf, (Hg, Hh)).
        case (Z_lt_dec 2 o1).
         (*  dL_nR_5: `2 < o1` *)
         clear quadratic_sign; intros H_o1_gt_2;
          rewrite
           (Qquadratic_sign_nRdL_nRdL_5 a b c d e f g h 
              (dL xs) (nR ys) H_Qquadratic_sg_denom_nonzero)
           ; discriminate || (try (repeat split; assumption)); 
          subst; unfold spec_Qquadratic_Qpositive_to_Q in |- *;
          rewrite Qsgn_15; rewrite Qsgn_28;
          rewrite
           (Qsgn_7 _
              (outside_square_correct_1 _ _ _ _ (dL xs) 
                 (nR ys) H_o1_gt_2 Hbcd')); clear o1 o2 H_o1_gt_2;
          replace
           (Qplus
              (Qplus
                 (Qplus (Qmult (Qmult e (Qpos (dL xs))) (Qpos (nR ys)))
                    (Qmult 0%Z (Qpos (dL xs)))) (Qmult 0%Z (Qpos (nR ys))))
              0%Z) with (Qmult (Qmult e (Qpos (dL xs))) (Qpos (nR ys)));
          [ idtac | simpl; ring ]; repeat rewrite Qsgn_15; 
          rewrite Qsgn_29; unfold Qsgn in |- *; ring.
         case (Z_lt_dec o1 (-2)).
          (* dL_nR_6: `o1<(-2)` *)
          clear quadratic_sign; intros H_o1_lt_min_2 H_o1_gt_2';
           rewrite
            (Qquadratic_sign_nRdL_nRdL_6 a b c d e f g h 
               (dL xs) (nR ys) H_Qquadratic_sg_denom_nonzero)
            ; discriminate || (try (repeat split; assumption)); 
           subst; unfold spec_Qquadratic_Qpositive_to_Q in |- *;
           rewrite Qsgn_15; rewrite Qsgn_28;
           rewrite
            (Qsgn_8 _
               (outside_square_correct_2 _ _ _ _ (dL xs) 
                  (nR ys) H_o1_lt_min_2 Hbcd'));
           clear o1 o2 H_o1_gt_2' H_o1_lt_min_2;
           replace
            (Qplus
               (Qplus
                  (Qplus (Qmult (Qmult e (Qpos (dL xs))) (Qpos (nR ys)))
                     (Qmult 0%Z (Qpos (dL xs)))) (Qmult 0%Z (Qpos (nR ys))))
               0%Z) with (Qmult (Qmult e (Qpos (dL xs))) (Qpos (nR ys)));
           [ idtac | simpl; ring ]; repeat rewrite Qsgn_15; 
           rewrite Qsgn_29; unfold Qsgn in |- *; ring.
          (* dL_nR_7:   ~`o1 < (-2)` /\ ~`2 < o1` *)
          intros H_o1_lt_min_2' H_o1_gt_2';
           rewrite
            (Qquadratic_sign_dL_nR_7 a b c d e f g h 
               (dL xs) xs (nR ys) ys H_Qquadratic_sg_denom_nonzero
               (Qquadratic_signok_3 _ _ _ _ _ _ H_Qquadratic_sg_denom_nonzero)
               (refl_equal (dL xs)) (refl_equal (nR ys)))
            ; discriminate || (try (repeat split; assumption));
           rewrite spec_Qquadratic_Qpositive_to_Q_dL_nR;
           rewrite <-
            (quadratic_sign (a + c)%Z (a + b + c + d)%Z c 
               (c + d)%Z (e + g)%Z (e + f + g + h)%Z g 
               (g + h)%Z xs ys
               (Qquadratic_signok_3 e f g h xs ys
                  H_Qquadratic_sg_denom_nonzero)); 
           reflexivity.
        (* ~(`f = 0`/\`g = 0`/\`h = 0`) *)
        intro Hfgh'.
        case (inside_square_1_dec_inf o1 o2).    
         (* dL_nR_8: (inside_square_1 o1 o2) *)
         clear quadratic_sign; intro H_inside_1;
          (rewrite
            (Qquadratic_sign_nRdL_nRdL_8 a b c d e f g h 
               (dL xs) (nR ys) H_Qquadratic_sg_denom_nonzero)
            ; discriminate || (try (repeat split; assumption)));
          generalize H_inside_1; intros [(H_o1, H_o2)| (H_o1, H_o2)];
          Inside_Square_Qsgn_ (dL xs) (nR ys); intros H_num H_denom;
          unfold spec_Qquadratic_Qpositive_to_Q in |- *; 
          rewrite Qsgn_15; rewrite Qsgn_28; rewrite H_num; 
          rewrite H_denom; constructor.
         (* ~(inside_square_1 o1 o2) *)
         intro H_inside_1'.
         case (inside_square_2_dec_inf o1 o2).    
          (* dL_nR_9: (inside_square_2 o1 o2) *)
          clear quadratic_sign; intro H_inside_2;
           (rewrite
             (Qquadratic_sign_nRdL_nRdL_9 a b c d e f g h 
                (dL xs) (nR ys) H_Qquadratic_sg_denom_nonzero)
             ; discriminate || (try (repeat split; assumption)));
           generalize H_inside_2; intros [(H_o1, H_o2)| (H_o1, H_o2)];
           Inside_Square_Qsgn_ (dL xs) (nR ys); intros H_num H_denom;
           unfold spec_Qquadratic_Qpositive_to_Q in |- *; 
           rewrite Qsgn_15; rewrite Qsgn_28; rewrite H_num; 
           rewrite H_denom; constructor.
          (*  dL_nR_10: ~(inside_square_1 o1 o2)/\~(inside_square_2 o1 o2) *)
          intros H_inside_2'. 
          rewrite
           (Qquadratic_sign_dL_nR_10 a b c d e f g h 
              (dL xs) xs (nR ys) ys H_Qquadratic_sg_denom_nonzero
              (Qquadratic_signok_3 _ _ _ _ _ _ H_Qquadratic_sg_denom_nonzero)
              (refl_equal (dL xs)) (refl_equal (nR ys)))
           ; discriminate || (try (repeat split; assumption));
           rewrite spec_Qquadratic_Qpositive_to_Q_dL_nR;
           rewrite <-
            (quadratic_sign (a + c)%Z (a + b + c + d)%Z c 
               (c + d)%Z (e + g)%Z (e + f + g + h)%Z g 
               (g + h)%Z xs ys
               (Qquadratic_signok_3 e f g h xs ys
                  H_Qquadratic_sg_denom_nonzero)); 
           reflexivity.
(* End CHUNK 4 *)
(*####################################################################################################*)
(* Begin CHUNK 5 *)
(* update: it is actualy better to copy CHUNK 1 & 2 &3 all together *)
(* outdated: We copy CHUNK 4 and query replace
dL_nR with dL_dL 
nRdL_dLdL with nRdL_nRdL
(nR ys) with (dL ys)
`a+c` `a+b+c+d` c `c+d` `e+g` `e+f+g+h` g `g+h` with  `a+b+c+d` `b+d` `c+d` d `e+f+g+h` `f+h` `g+h` h
Qquadratic_signok_3 with Qquadratic_signok_4
*)

   (* p2=(dL ys) *)
   case (three_integers_dec_inf b c d).
    (* `b = 0`/\`c = 0`/\`d = 0` *)
    intros (Hb, (Hc, Hd)). 
    case (three_integers_dec_inf f g h).  
     (* dL_dL_1: `f = 0`/\`g = 0`/\`h = 0` *)
     clear o1 o2 quadratic_sign; intros (Hf, (Hg, Hh));
      rewrite
       (Qquadratic_sign_nRdL_nRdL_1 a b c d e f g h 
          (dL xs) (dL ys) H_Qquadratic_sg_denom_nonzero)
       ; discriminate || (try (repeat split; assumption)); 
      subst; unfold spec_Qquadratic_Qpositive_to_Q in |- *; 
      simpl in |- *;
      transitivity
       (Qsgn
          (Qmult (Qmult (Qmult a (Qpos (dL xs))) (Qpos (dL ys)))
             (Qinv (Qmult (Qmult e (Qpos (dL xs))) (Qpos (dL ys))))));
      [ idtac
      | apply f_equal with Q; apply f_equal2 with Q Q;
         [ idtac | apply f_equal with Q ]; simpl; ring ];
         rewrite Qsgn_15; rewrite Qsgn_28; 
      repeat rewrite Qsgn_15; simpl in |- *; do 2 rewrite Qsgn_29;
      ring.
     (* ~(`f = 0`/\`g = 0`/\`h = 0`) *)
     case (Z_lt_dec 2 o2).
      (*  dL_dL_2: `2 < o2` *)
      clear quadratic_sign; intros H_o2_gt_2 Hfgh';
       rewrite
        (Qquadratic_sign_nRdL_nRdL_2 a b c d e f g h 
           (dL xs) (dL ys) H_Qquadratic_sg_denom_nonzero)
        ; discriminate || (try (repeat split; assumption)); 
       subst; unfold spec_Qquadratic_Qpositive_to_Q in |- *; 
       rewrite Qsgn_15; rewrite Qsgn_28;
       rewrite
        (Qsgn_7 _
           (outside_square_correct_1 _ _ _ _ (dL xs) (dL ys) H_o2_gt_2 Hfgh'))
        ; clear o1 o2 H_o2_gt_2;
       replace
        (Qplus
           (Qplus
              (Qplus (Qmult (Qmult a (Qpos (dL xs))) (Qpos (dL ys)))
                 (Qmult 0%Z (Qpos (dL xs)))) (Qmult 0%Z (Qpos (dL ys)))) 0%Z)
        with (Qmult (Qmult a (Qpos (dL xs))) (Qpos (dL ys)));
       [ idtac | simpl; ring ]; repeat rewrite Qsgn_15; 
       simpl in |- *; rewrite Qsgn_29; ring.
      case (Z_lt_dec o2 (-2)).
       (* dL_dL_3: `o2<(-2)` *)
       clear quadratic_sign; intros H_o2_lt_min_2 H_o2_gt_2' Hfgh';
        rewrite
         (Qquadratic_sign_nRdL_nRdL_3 a b c d e f g h 
            (dL xs) (dL ys) H_Qquadratic_sg_denom_nonzero)
         ; discriminate || (try (repeat split; assumption)); 
        subst; unfold spec_Qquadratic_Qpositive_to_Q in |- *; 
        rewrite Qsgn_15; rewrite Qsgn_28;
        rewrite
         (Qsgn_8 _
            (outside_square_correct_2 _ _ _ _ (dL xs) 
               (dL ys) H_o2_lt_min_2 Hfgh'));
        clear o1 o2 H_o2_lt_min_2 H_o2_gt_2';
        replace
         (Qplus
            (Qplus
               (Qplus (Qmult (Qmult a (Qpos (dL xs))) (Qpos (dL ys)))
                  (Qmult 0%Z (Qpos (dL xs)))) (Qmult 0%Z (Qpos (dL ys)))) 0%Z)
         with (Qmult (Qmult a (Qpos (dL xs))) (Qpos (dL ys)));
        [ idtac | simpl; ring ]; repeat rewrite Qsgn_15; 
        simpl in |- *; rewrite Qsgn_29; ring.
       (* dL_dL_4:   ~`o2 < (-2)` /\ ~`2 < o2`/\~(`f = 0`/\`g = 0`/\`h = 0`) *) 
       intros H_o2_lt_min_2' H_o2_gt_2' Hfgh';
        rewrite
         (Qquadratic_sign_dL_dL_4 a b c d e f g h (dL xs) xs 
            (dL ys) ys H_Qquadratic_sg_denom_nonzero
            (Qquadratic_signok_4 _ _ _ _ _ _ H_Qquadratic_sg_denom_nonzero)
            (refl_equal (dL xs)) (refl_equal (dL ys)))
         ; discriminate || (try (repeat split; assumption));
        rewrite spec_Qquadratic_Qpositive_to_Q_dL_dL;
        rewrite <-
         (quadratic_sign (a + b + c + d)%Z (b + d)%Z 
            (c + d)%Z d (e + f + g + h)%Z (f + h)%Z 
            (g + h)%Z h xs ys
            (Qquadratic_signok_4 e f g h xs ys H_Qquadratic_sg_denom_nonzero))
         ; reflexivity.
       (* ~(`b = 0`/\`c = 0`/\`d = 0`) *)
       intro Hbcd'.  
       case (three_integers_dec_inf f g h).  
        (* `f = 0`/\`g = 0`/\`h = 0` *)
        intros (Hf, (Hg, Hh)).
        case (Z_lt_dec 2 o1).
         (*  dL_dL_5: `2 < o1` *)
         clear quadratic_sign; intros H_o1_gt_2;
          rewrite
           (Qquadratic_sign_nRdL_nRdL_5 a b c d e f g h 
              (dL xs) (dL ys) H_Qquadratic_sg_denom_nonzero)
           ; discriminate || (try (repeat split; assumption)); 
          subst; unfold spec_Qquadratic_Qpositive_to_Q in |- *;
          rewrite Qsgn_15; rewrite Qsgn_28;
          rewrite
           (Qsgn_7 _
              (outside_square_correct_1 _ _ _ _ (dL xs) 
                 (dL ys) H_o1_gt_2 Hbcd')); clear o1 o2 H_o1_gt_2;
          replace
           (Qplus
              (Qplus
                 (Qplus (Qmult (Qmult e (Qpos (dL xs))) (Qpos (dL ys)))
                    (Qmult 0%Z (Qpos (dL xs)))) (Qmult 0%Z (Qpos (dL ys))))
              0%Z) with (Qmult (Qmult e (Qpos (dL xs))) (Qpos (dL ys)));
          [ idtac | simpl; ring ]; repeat rewrite Qsgn_15; 
          rewrite Qsgn_29; unfold Qsgn in |- *; ring.
         case (Z_lt_dec o1 (-2)).
          (* dL_dL_6: `o1<(-2)` *)
          clear quadratic_sign; intros H_o1_lt_min_2 H_o1_gt_2';
           rewrite
            (Qquadratic_sign_nRdL_nRdL_6 a b c d e f g h 
               (dL xs) (dL ys) H_Qquadratic_sg_denom_nonzero)
            ; discriminate || (try (repeat split; assumption)); 
           subst; unfold spec_Qquadratic_Qpositive_to_Q in |- *;
           rewrite Qsgn_15; rewrite Qsgn_28;
           rewrite
            (Qsgn_8 _
               (outside_square_correct_2 _ _ _ _ (dL xs) 
                  (dL ys) H_o1_lt_min_2 Hbcd'));
           clear o1 o2 H_o1_gt_2' H_o1_lt_min_2;
           replace
            (Qplus
               (Qplus
                  (Qplus (Qmult (Qmult e (Qpos (dL xs))) (Qpos (dL ys)))
                     (Qmult 0%Z (Qpos (dL xs)))) (Qmult 0%Z (Qpos (dL ys))))
               0%Z) with (Qmult (Qmult e (Qpos (dL xs))) (Qpos (dL ys)));
           [ idtac | simpl; ring ]; repeat rewrite Qsgn_15; 
           rewrite Qsgn_29; unfold Qsgn in |- *; ring.
          (* dL_dL_7:   ~`o1 < (-2)` /\ ~`2 < o1` *)
          intros H_o1_lt_min_2' H_o1_gt_2';
           rewrite
            (Qquadratic_sign_dL_dL_7 a b c d e f g h 
               (dL xs) xs (dL ys) ys H_Qquadratic_sg_denom_nonzero
               (Qquadratic_signok_4 _ _ _ _ _ _ H_Qquadratic_sg_denom_nonzero)
               (refl_equal (dL xs)) (refl_equal (dL ys)))
            ; discriminate || (try (repeat split; assumption));
           rewrite spec_Qquadratic_Qpositive_to_Q_dL_dL;
           rewrite <-
            (quadratic_sign (a + b + c + d)%Z (b + d)%Z 
               (c + d)%Z d (e + f + g + h)%Z (f + h)%Z 
               (g + h)%Z h xs ys
               (Qquadratic_signok_4 e f g h xs ys
                  H_Qquadratic_sg_denom_nonzero)); 
           reflexivity.
        (* ~(`f = 0`/\`g = 0`/\`h = 0`) *)
        intro Hfgh'.
        case (inside_square_1_dec_inf o1 o2).    
         (* dL_dL_8: (inside_square_1 o1 o2) *)
         clear quadratic_sign; intro H_inside_1;
          (rewrite
            (Qquadratic_sign_nRdL_nRdL_8 a b c d e f g h 
               (dL xs) (dL ys) H_Qquadratic_sg_denom_nonzero)
            ; discriminate || (try (repeat split; assumption)));
          generalize H_inside_1; intros [(H_o1, H_o2)| (H_o1, H_o2)];
          Inside_Square_Qsgn_ (dL xs) (dL ys); intros H_num H_denom;
          unfold spec_Qquadratic_Qpositive_to_Q in |- *; 
          rewrite Qsgn_15; rewrite Qsgn_28; rewrite H_num; 
          rewrite H_denom; constructor.
         (* ~(inside_square_1 o1 o2) *)
         intro H_inside_1'.
         case (inside_square_2_dec_inf o1 o2).    
          (* dL_dL_9: (inside_square_2 o1 o2) *)
          clear quadratic_sign; intro H_inside_2;
           (rewrite
             (Qquadratic_sign_nRdL_nRdL_9 a b c d e f g h 
                (dL xs) (dL ys) H_Qquadratic_sg_denom_nonzero)
             ; discriminate || (try (repeat split; assumption)));
           generalize H_inside_2; intros [(H_o1, H_o2)| (H_o1, H_o2)];
           Inside_Square_Qsgn_ (dL xs) (dL ys); intros H_num H_denom;
           unfold spec_Qquadratic_Qpositive_to_Q in |- *; 
           rewrite Qsgn_15; rewrite Qsgn_28; rewrite H_num; 
           rewrite H_denom; constructor.
          (*  dL_dL_10: ~(inside_square_1 o1 o2)/\~(inside_square_2 o1 o2) *)
          intros H_inside_2'. 
          rewrite
           (Qquadratic_sign_dL_dL_10 a b c d e f g h 
              (dL xs) xs (dL ys) ys H_Qquadratic_sg_denom_nonzero
              (Qquadratic_signok_4 _ _ _ _ _ _ H_Qquadratic_sg_denom_nonzero)
              (refl_equal (dL xs)) (refl_equal (dL ys)))
           ; discriminate || (try (repeat split; assumption));
           rewrite spec_Qquadratic_Qpositive_to_Q_dL_dL;
           rewrite <-
            (quadratic_sign (a + b + c + d)%Z (b + d)%Z 
               (c + d)%Z d (e + f + g + h)%Z (f + h)%Z 
               (g + h)%Z h xs ys
               (Qquadratic_signok_4 e f g h xs ys
                  H_Qquadratic_sg_denom_nonzero)); 
           reflexivity.
(* End CHUNK 5 *)
(*####################################################################################################*)
(* Begin CHUNK 6 *)
(* We copy CHUNK 3 and query replace:
(nR xs) with (dL xs)
*)

  (* p2=One *)
  clear quadratic_sign.
  generalize (Qquadratic_signok_0' _ _ _ _ _ H_Qquadratic_sg_denom_nonzero).
  intro H_Qhomographic_sg_denom_nonzero.
  set
   (L3 :=
    Qhomographic_sign (a + b) (c + d) (e + f) (g + h) 
      (dL xs) H_Qhomographic_sg_denom_nonzero) in *.
  set (l1 := fst L3) in *.
  set (l2 := fst (snd L3)) in *.
  set (l3 := snd (snd L3)) in *.
  set (na := fst l2) in *.
  set (nb := fst (snd l2)) in *.
  set (nc := fst (snd (snd l2))) in *.
  set (nd := snd (snd (snd l2))) in *.
  rewrite
   (Qquadratic_sign_nRdL_One a b c d e f g h (dL xs) One
      H_Qquadratic_sg_denom_nonzero l1 na nb nc nd l3
      H_Qhomographic_sg_denom_nonzero);
   [ idtac
   | fold L3 in |- *; repeat (apply pair_2; try reflexivity)
   | discriminate
   | reflexivity ]. 
  rewrite spec_Qquadratic_Qpositive_to_Q_p_One.
  rewrite <-
   (homographic_sign (a + b) (c + d) (e + f) (g + h) 
      (dL xs) H_Qhomographic_sg_denom_nonzero).
  reflexivity.
(* End CHUNK 6 *)
(*####################################################################################################*)
(* Begin CHUNK 7 *)
  (* p1=One *)
  intros p2 H_Qquadratic_sg_denom_nonzero; clear quadratic_sign.
  generalize (Qquadratic_signok_0 _ _ _ _ _ H_Qquadratic_sg_denom_nonzero).
  intro H_Qhomographic_sg_denom_nonzero.
  set
   (L3 :=
    Qhomographic_sign (a + c) (b + d) (e + g) (f + h) p2
      H_Qhomographic_sg_denom_nonzero) in *.
  set (l1 := fst L3) in *.
  set (l2 := fst (snd L3)) in *.
  set (l3 := snd (snd L3)) in *.
  set (na := fst l2) in *.
  set (nb := fst (snd l2)) in *.
  set (nc := fst (snd (snd l2))) in *.
  set (nd := snd (snd (snd l2))) in *.
  rewrite
   (Qquadratic_sign_One_y a b c d e f g h One p2
      H_Qquadratic_sg_denom_nonzero l1 na nb nc nd l3
      H_Qhomographic_sg_denom_nonzero);
   [ idtac
   | fold L3 in |- *; repeat (apply pair_2; try reflexivity)
   | reflexivity ]. 
  rewrite spec_Qquadratic_Qpositive_to_Q_One_p.
  rewrite <-
   (homographic_sign (a + c) (b + d) (e + g) (f + h) p2
      H_Qhomographic_sg_denom_nonzero).
  reflexivity.
(* End CHUNK 7 *)
Qed.



Lemma quadraticAcc_positive :
 forall (a b c d e f g h : Z) (p1 p2 : Qpositive),
 quadraticAcc a b c d e f g h p1 p2 ->
 Qlt Zero
   (Qplus
      (Qplus
         (Qplus (Qmult (Qmult a (Qpos p1)) (Qpos p2)) (Qmult b (Qpos p1)))
         (Qmult c (Qpos p2))) d) /\
 Qlt Zero
   (Qplus
      (Qplus
         (Qplus (Qmult (Qmult e (Qpos p1)) (Qpos p2)) (Qmult f (Qpos p1)))
         (Qmult g (Qpos p2))) h).
Proof.
 intros a b c d e f g h p1 p2 H.
 induction H;
  try
   match goal with
   | id1:(_ /\ _) |- _ => elim id1; clear id1; intros IHrec1 IHrec2
   end.
 (* 1 *)
 rewrite H; repeat rewrite Qmult_one_right;
  replace (Qplus (Qplus (Qplus (Qmult a (Qpos p2)) b) (Qmult c (Qpos p2))) d)
   with (Qplus (Qmult (a + c)%Z (Qpos p2)) (b + d)%Z);
  [ replace
     (Qplus (Qplus (Qplus (Qmult e (Qpos p2)) f) (Qmult g (Qpos p2))) h) with
     (Qplus (Qmult (e + g)%Z (Qpos p2)) (f + h)%Z);
     [ apply homographicAcc_positive; assumption | idtac ]
  | idtac ]; repeat rewrite Z_to_Qplus; ring.
 (* 2 *)
 rewrite H0; repeat rewrite Qmult_one_right;
  replace (Qplus (Qplus (Qplus (Qmult a (Qpos p1)) (Qmult b (Qpos p1))) c) d)
   with (Qplus (Qmult (a + b)%Z (Qpos p1)) (c + d)%Z);
  [ replace
     (Qplus (Qplus (Qplus (Qmult e (Qpos p1)) (Qmult f (Qpos p1))) g) h) with
     (Qplus (Qmult (e + f)%Z (Qpos p1)) (g + h)%Z);
     [ apply homographicAcc_positive; assumption | idtac ]
  | idtac ]; repeat rewrite Z_to_Qplus; ring.
 (* 3 *)
 split; try assumption; replace a with (a - e + e)%Z;
  [ idtac | abstract auto with zarith ]; replace b with (b - f + f)%Z;
  [ idtac | abstract auto with zarith ]; replace c with (c - g + g)%Z;
  [ idtac | abstract auto with zarith ]; replace d with (d - h + h)%Z;
  [ idtac | abstract auto with zarith ]; repeat rewrite Z_to_Qplus;
  replace
   (Qplus
      (Qplus
         (Qplus (Qmult (Qmult (Qplus (a - e)%Z e) (Qpos p1)) (Qpos p2))
            (Qmult (Qplus (b - f)%Z f) (Qpos p1)))
         (Qmult (Qplus (c - g)%Z g) (Qpos p2))) (Qplus (d - h)%Z h)) with
   (Qplus
      (Qplus
         (Qplus
            (Qplus (Qmult (Qmult (a - e)%Z (Qpos p1)) (Qpos p2))
               (Qmult (b - f)%Z (Qpos p1))) (Qmult (c - g)%Z (Qpos p2)))
         (d - h)%Z)
      (Qplus
         (Qplus
            (Qplus (Qmult (Qmult e (Qpos p1)) (Qpos p2)) (Qmult f (Qpos p1)))
            (Qmult g (Qpos p2))) h)); [ idtac | abstract ring ];
  apply Qlt_plus_pos_pos; assumption.
 (* 4 *)
 split; try assumption; replace e with (e - a + a)%Z;
  [ idtac | abstract auto with zarith ]; replace f with (f - b + b)%Z;
  [ idtac | abstract auto with zarith ]; replace g with (g - c + c)%Z;
  [ idtac | abstract auto with zarith ]; replace h with (h - d + d)%Z;
  [ idtac | abstract auto with zarith ]; repeat rewrite Z_to_Qplus;
  replace
   (Qplus
      (Qplus
         (Qplus (Qmult (Qmult (Qplus (e - a)%Z a) (Qpos p1)) (Qpos p2))
            (Qmult (Qplus (f - b)%Z b) (Qpos p1)))
         (Qmult (Qplus (g - c)%Z c) (Qpos p2))) (Qplus (h - d)%Z d)) with
   (Qplus
      (Qplus
         (Qplus
            (Qplus (Qmult (Qmult (e - a)%Z (Qpos p1)) (Qpos p2))
               (Qmult (f - b)%Z (Qpos p1))) (Qmult (g - c)%Z (Qpos p2)))
         (h - d)%Z)
      (Qplus
         (Qplus
            (Qplus (Qmult (Qmult a (Qpos p1)) (Qpos p2)) (Qmult b (Qpos p1)))
            (Qmult c (Qpos p2))) d)); [ idtac | abstract ring ];
  apply Qlt_plus_pos_pos; assumption.
 (* 5 *)
 repeat rewrite Qpos_nR;
  replace
   (Qplus
      (Qplus
         (Qplus
            (Qmult (Qmult a (Qplus (Qpos xs) Qone)) (Qplus (Qpos ys) Qone))
            (Qmult b (Qplus (Qpos xs) Qone)))
         (Qmult c (Qplus (Qpos ys) Qone))) d) with
   (Qplus
      (Qplus
         (Qplus (Qmult (Qmult a (Qpos xs)) (Qpos ys))
            (Qmult (a + b)%Z (Qpos xs))) (Qmult (a + c)%Z (Qpos ys)))
      (a + b + c + d)%Z);
  [ idtac | repeat rewrite Z_to_Qplus; abstract ring ];
  replace
   (Qplus
      (Qplus
         (Qplus
            (Qmult (Qmult e (Qplus (Qpos xs) Qone)) (Qplus (Qpos ys) Qone))
            (Qmult f (Qplus (Qpos xs) Qone)))
         (Qmult g (Qplus (Qpos ys) Qone))) h) with
   (Qplus
      (Qplus
         (Qplus (Qmult (Qmult e (Qpos xs)) (Qpos ys))
            (Qmult (e + f)%Z (Qpos xs))) (Qmult (e + g)%Z (Qpos ys)))
      (e + f + g + h)%Z);
  [ idtac | repeat rewrite Z_to_Qplus; abstract ring ]; 
  split; assumption.
 (* 6 *)
 abstract (repeat rewrite Qpos_nR; repeat rewrite Qpos_dL;
            replace
             (Qplus
                (Qplus
                   (Qplus
                      (Qmult (Qmult a (Qplus (Qpos xs) Qone))
                         (Qmult (Qpos ys) (Qinv (Qplus (Qpos ys) Qone))))
                      (Qmult b (Qplus (Qpos xs) Qone)))
                   (Qmult c (Qmult (Qpos ys) (Qinv (Qplus (Qpos ys) Qone)))))
                d) with
             (Qmult
                (Qplus
                   (Qplus
                      (Qplus (Qmult (Qmult (a + b)%Z (Qpos xs)) (Qpos ys))
                         (Qmult b (Qpos xs)))
                      (Qmult (a + b + c + d)%Z (Qpos ys))) 
                   (b + d)%Z) (Qinv (Qplus (Qpos ys) Qone)));
            [ idtac
            | repeat rewrite Z_to_Qplus; abstract (field; discriminate) ];
            replace
             (Qplus
                (Qplus
                   (Qplus
                      (Qmult (Qmult e (Qplus (Qpos xs) Qone))
                         (Qmult (Qpos ys) (Qinv (Qplus (Qpos ys) Qone))))
                      (Qmult f (Qplus (Qpos xs) Qone)))
                   (Qmult g (Qmult (Qpos ys) (Qinv (Qplus (Qpos ys) Qone)))))
                h) with
             (Qmult
                (Qplus
                   (Qplus
                      (Qplus (Qmult (Qmult (e + f)%Z (Qpos xs)) (Qpos ys))
                         (Qmult f (Qpos xs)))
                      (Qmult (e + f + g + h)%Z (Qpos ys))) 
                   (f + h)%Z) (Qinv (Qplus (Qpos ys) Qone)));
            [ idtac
            | repeat rewrite Z_to_Qplus; abstract (field; discriminate) ];
            split; apply Qlt_mult_pos_pos; try assumption; 
            apply Qinv_pos; apply Qlt_plus_pos_pos; abstract 
            auto with *).
 (* 7 *)
 abstract (repeat rewrite Qpos_nR; repeat rewrite Qpos_dL;
            replace
             (Qplus
                (Qplus
                   (Qplus
                      (Qmult
                         (Qmult a
                            (Qmult (Qpos xs) (Qinv (Qplus (Qpos xs) Qone))))
                         (Qplus (Qpos ys) Qone))
                      (Qmult b
                         (Qmult (Qpos xs) (Qinv (Qplus (Qpos xs) Qone)))))
                   (Qmult c (Qplus (Qpos ys) Qone))) d) with
             (Qmult
                (Qplus
                   (Qplus
                      (Qplus (Qmult (Qmult (a + c)%Z (Qpos xs)) (Qpos ys))
                         (Qmult (a + b + c + d)%Z (Qpos xs)))
                      (Qmult c (Qpos ys))) (c + d)%Z)
                (Qinv (Qplus (Qpos xs) Qone)));
            [ idtac
            | repeat rewrite Z_to_Qplus; abstract (field; discriminate) ];
            replace
             (Qplus
                (Qplus
                   (Qplus
                      (Qmult
                         (Qmult e
                            (Qmult (Qpos xs) (Qinv (Qplus (Qpos xs) Qone))))
                         (Qplus (Qpos ys) Qone))
                      (Qmult f
                         (Qmult (Qpos xs) (Qinv (Qplus (Qpos xs) Qone)))))
                   (Qmult g (Qplus (Qpos ys) Qone))) h) with
             (Qmult
                (Qplus
                   (Qplus
                      (Qplus (Qmult (Qmult (e + g)%Z (Qpos xs)) (Qpos ys))
                         (Qmult (e + f + g + h)%Z (Qpos xs)))
                      (Qmult g (Qpos ys))) (g + h)%Z)
                (Qinv (Qplus (Qpos xs) Qone)));
            [ idtac
            | repeat rewrite Z_to_Qplus; abstract (field; discriminate) ];
            split; apply Qlt_mult_pos_pos; try assumption; 
            apply Qinv_pos; apply Qlt_plus_pos_pos; abstract 
            auto with *).
 (* 8*)
 abstract (repeat rewrite Qpos_dL;
            replace
             (Qplus
                (Qplus
                   (Qplus
                      (Qmult
                         (Qmult a
                            (Qmult (Qpos xs) (Qinv (Qplus (Qpos xs) Qone))))
                         (Qmult (Qpos ys) (Qinv (Qplus (Qpos ys) Qone))))
                      (Qmult b
                         (Qmult (Qpos xs) (Qinv (Qplus (Qpos xs) Qone)))))
                   (Qmult c (Qmult (Qpos ys) (Qinv (Qplus (Qpos ys) Qone)))))
                d) with
             (Qmult
                (Qplus
                   (Qplus
                      (Qplus
                         (Qmult (Qmult (a + b + c + d)%Z (Qpos xs)) (Qpos ys))
                         (Qmult (b + d)%Z (Qpos xs)))
                      (Qmult (c + d)%Z (Qpos ys))) d)
                (Qinv (Qmult (Qplus (Qpos xs) Qone) (Qplus (Qpos ys) Qone))));
            [ idtac
            | repeat rewrite Z_to_Qplus; field; split; discriminate ];
            replace
             (Qplus
                (Qplus
                   (Qplus
                      (Qmult
                         (Qmult e
                            (Qmult (Qpos xs) (Qinv (Qplus (Qpos xs) Qone))))
                         (Qmult (Qpos ys) (Qinv (Qplus (Qpos ys) Qone))))
                      (Qmult f
                         (Qmult (Qpos xs) (Qinv (Qplus (Qpos xs) Qone)))))
                   (Qmult g (Qmult (Qpos ys) (Qinv (Qplus (Qpos ys) Qone)))))
                h) with
             (Qmult
                (Qplus
                   (Qplus
                      (Qplus
                         (Qmult (Qmult (e + f + g + h)%Z (Qpos xs)) (Qpos ys))
                         (Qmult (f + h)%Z (Qpos xs)))
                      (Qmult (g + h)%Z (Qpos ys))) h)
                (Qinv (Qmult (Qplus (Qpos xs) Qone) (Qplus (Qpos ys) Qone))));
            [ idtac
            | repeat rewrite Z_to_Qplus; field; split; discriminate ];
            split; apply Qlt_mult_pos_pos; try assumption; 
            apply Qinv_pos; apply Qlt_mult_pos_pos; 
            apply Qlt_plus_pos_pos; abstract auto with *).
Qed. 

Lemma quadraticAcc_positive_numerator :
 forall (a b c d e f g h : Z) (p1 p2 : Qpositive),
 quadraticAcc a b c d e f g h p1 p2 ->
 Qlt Zero
   (Qplus
      (Qplus
         (Qplus (Qmult (Qmult a (Qpos p1)) (Qpos p2)) (Qmult b (Qpos p1)))
         (Qmult c (Qpos p2))) d).
Proof.
 intros; elim (quadraticAcc_positive _ _ _ _ _ _ _ _ _ _ H); trivial.
Qed.

Lemma quadraticAcc_positive_denominator :
 forall (a b c d e f g h : Z) (p1 p2 : Qpositive),
 quadraticAcc a b c d e f g h p1 p2 ->
 Qlt Zero
   (Qplus
      (Qplus
         (Qplus (Qmult (Qmult e (Qpos p1)) (Qpos p2)) (Qmult f (Qpos p1)))
         (Qmult g (Qpos p2))) h).
Proof.
 intros; elim (quadraticAcc_positive _ _ _ _ _ _ _ _ _ _ H); trivial.
Qed.

Lemma quadratic_output_bit :
 forall (a b c d e f g h : Z) (p1 p2 : Qpositive)
   (hyp_quadraticAcc : quadraticAcc a b c d e f g h p1 p2),
 Qquadratic_Qpositive_to_Qpositive a b c d e f g h p1 p2 hyp_quadraticAcc =
 spec_Qquadratic_Qpositive_to_Qpositive2 a b c d e f g h p1 p2.
Proof.
 intros a b c d e f g h p1 p2 hyp_quadraticAcc.
 generalize
  (quadraticAcc_positive_numerator _ _ _ _ _ _ _ _ _ _ hyp_quadraticAcc).
 generalize
  (quadraticAcc_positive_denominator _ _ _ _ _ _ _ _ _ _ hyp_quadraticAcc).
 pattern a, b, c, d, e, f, g, h, p1, p2, hyp_quadraticAcc in |- *.
 elim hyp_quadraticAcc using quadraticAcc_ind_dep;
   clear a b c d e f g h p1 p2 hyp_quadraticAcc; intros;
     unfold Qquadratic_Qpositive_to_Qpositive;fold Qquadratic_Qpositive_to_Qpositive.

 (* (1) p1= One *)
 case (Qpositive_dec_One p1); intros Hp1; [ idtac | Falsum ].
 unfold spec_Qquadratic_Qpositive_to_Qpositive2 in |- *.
 rewrite output_bit.
 unfold spec_ni2 in |- *.
 rewrite e0.
 repeat rewrite Qmult_one_right.
 apply f_equal2 with Qpositive Qpositive; try apply f_equal with Qpositive;
  apply f_equal with Q; repeat rewrite Z_to_Qplus; abstract 
  ring.
 (* (2) ~p1=One & p2=One *)
 case (Qpositive_dec_One p1); intros Hp1; [ Falsum | idtac ];
  case (Qpositive_dec_One p2); intros Hp2; [ idtac | Falsum ].
 unfold spec_Qquadratic_Qpositive_to_Qpositive2 in |- *.
 rewrite output_bit.
 unfold spec_ni2 in |- *.
 rewrite e0.
 repeat rewrite Qmult_one_right.
 apply f_equal2 with Qpositive Qpositive; try apply f_equal with Qpositive;
  apply f_equal with Q; repeat rewrite Z_to_Qplus; abstract 
  ring.
 (* (3) ~p1=One ~p2=One & (quadratic_top_more a b c d e f g h) *)
 case (Qpositive_dec_One p1); intros Hp1; [ Falsum | idtac ];
  case (Qpositive_dec_One p2); intros Hp2; [ Falsum | idtac ];
  case (quadratic_top_more_informative a b c d e f g h); 
  intros Habcdefgh; [ idtac | Falsum ];
  generalize (quadraticAcc_positive_numerator _ _ _ _ _ _ _ _ _ _ q0);
  intros H_ae;simpl; rewrite H;  try assumption;
  apply spec_Qquadratic_Qpositive_to_Qpositive2_nR_emission; 
  assumption.
 (* (4) ~p1=One ~p2=One & (quadratic_top_more e f g h a b c d) *)
 case (Qpositive_dec_One p1); intros Hp1; [ Falsum | idtac ];
  case (Qpositive_dec_One p2); intros Hp2; [ Falsum | idtac ];
  case (quadratic_top_more_informative a b c d e f g h); 
  intros Habcdefgh; [ Falsum | idtac ];
  case (quadratic_top_more_informative e f g h a b c d); 
  intros Hefghabcd; [ idtac | Falsum ];
  generalize (quadraticAcc_positive_denominator _ _ _ _ _ _ _ _ _ _ q0);
  intros H_ae; simpl;rewrite H; try assumption;
  apply spec_Qquadratic_Qpositive_to_Qpositive2_dL_emission; 
  assumption.
 (* (5) nR_nR ~(top_more a b c d)&~(top_more c d a b) *) 
 case (quadratic_top_more_informative a b c d e f g h); intros Habcdefgh;
  [ Falsum | idtac ]; case (quadratic_top_more_informative e f g h a b c d);
  intros Hefghabcd; [ Falsum | idtac ];
  generalize (quadraticAcc_positive_numerator _ _ _ _ _ _ _ _ _ _ q);
  generalize (quadraticAcc_positive_denominator _ _ _ _ _ _ _ _ _ _ q);
  intros H_ae H_ae'; simpl; rewrite H; try assumption;
  rewrite spec_Qquadratic_Qpositive_to_Qpositive2_nR_nR; 
  reflexivity.
 (* (6) nR_dL ~(top_more a b c d)&~(top_more c d a b) *) 
 case (quadratic_top_more_informative a b c d e f g h); intros Habcdefgh;
  [ Falsum | idtac ]; case (quadratic_top_more_informative e f g h a b c d);
  intros Hefghabcd; [ Falsum | idtac ];
  generalize (quadraticAcc_positive_numerator _ _ _ _ _ _ _ _ _ _ q);
  generalize (quadraticAcc_positive_denominator _ _ _ _ _ _ _ _ _ _ q);
  intros H_ae H_ae'; simpl;rewrite H; try assumption;
  rewrite spec_Qquadratic_Qpositive_to_Qpositive2_nR_dL;
  reflexivity || apply Qlt_not_eq; repeat rewrite <- Z_to_Qplus; 
  assumption.
 (* (7) dL_nR ~(top_more a b c d)&~(top_more c d a b) *) 
 case (quadratic_top_more_informative a b c d e f g h); intros Habcdefgh;
  [ Falsum | idtac ]; case (quadratic_top_more_informative e f g h a b c d);
  intros Hefghabcd; [ Falsum | idtac ];
  generalize (quadraticAcc_positive_numerator _ _ _ _ _ _ _ _ _ _ q);
  generalize (quadraticAcc_positive_denominator _ _ _ _ _ _ _ _ _ _ q);
  intros H_ae H_ae'; simpl;rewrite H; try assumption;
  rewrite spec_Qquadratic_Qpositive_to_Qpositive2_dL_nR;
  reflexivity || apply Qlt_not_eq; repeat rewrite <- Z_to_Qplus; 
  assumption.
 (* (8) dL_dL ~(top_more a b c d)&~(top_more c d a b) *) 
 case (quadratic_top_more_informative a b c d e f g h); intros Habcdefgh;
  [ Falsum | idtac ]; case (quadratic_top_more_informative e f g h a b c d);
  intros Hefghabcd; [ Falsum | idtac ];
  generalize (quadraticAcc_positive_numerator _ _ _ _ _ _ _ _ _ _ q);
  generalize (quadraticAcc_positive_denominator _ _ _ _ _ _ _ _ _ _ q);
  intros H_ae H_ae'; simpl; rewrite H; try assumption;
  rewrite spec_Qquadratic_Qpositive_to_Qpositive2_dL_dL;
  reflexivity || apply Qlt_not_eq; repeat rewrite <- Z_to_Qplus; 
  assumption.
Qed.


Lemma
 spec_Qquadratic_Qpositive_to_Q_spec_Qquadratic_Qpositive_to_Qpositive2_pos :
 forall (a b c d e f g h : Z) (p1 p2 : Qpositive),
 Qsgn (spec_Qquadratic_Qpositive_to_Q a b c d e f g h p1 p2) = 1%Z ->
 spec_Qquadratic_Qpositive_to_Q a b c d e f g h p1 p2 =
 Qpos (spec_Qquadratic_Qpositive_to_Qpositive2 a b c d e f g h p1 p2).
Proof.
 intros a b c d e f g h p1 p2 H.
 unfold spec_Qquadratic_Qpositive_to_Q in |- *.
 unfold spec_Qquadratic_Qpositive_to_Qpositive2 in |- *.
 rewrite <- Q_tail_Qinv.
 rewrite <- Q_tail_Qmult.
 rewrite <- Q_tail_Q_pos.
 reflexivity.

 apply Qsgn_9.
 assumption.

 intro H_absurd.
 unfold spec_Qquadratic_Qpositive_to_Q in H.
 rewrite H_absurd in H.
 discriminate H.

 intro H_absurd.
 unfold spec_Qquadratic_Qpositive_to_Q in H.
 rewrite H_absurd in H.
 rewrite Qmult_sym in H.
 discriminate H.
Qed.

(** We use this when (Z.sgn a+b+c+d)<0 *)
Lemma
 spec_Qquadratic_Qpositive_to_Q_spec_Qquadratic_Qpositive_to_Qpositive2_neg_1
 :
 forall (a b c d e f g h : Z) (p1 p2 : Qpositive),
 Qsgn (spec_Qquadratic_Qpositive_to_Q a b c d e f g h p1 p2) = (-1)%Z ->
 spec_Qquadratic_Qpositive_to_Q a b c d e f g h p1 p2 =
 Qneg
   (spec_Qquadratic_Qpositive_to_Qpositive2 (- a) (- b) 
      (- c) (- d) e f g h p1 p2).
Proof.
 intros a b c d e f g h p1 p2 H.
 unfold spec_Qquadratic_Qpositive_to_Q in |- *.
 unfold spec_Qquadratic_Qpositive_to_Qpositive2 in |- *.
 rewrite <- Q_tail_Qinv.
 rewrite <- Q_tail_Qmult.
 repeat rewrite Qopp_Qpos.
 rewrite <- Q_tail_Q_pos.
 repeat rewrite Z_to_Qopp.
 abstract ring.

 apply Qsgn_9.
 repeat rewrite Z_to_Qopp.
 repeat rewrite Qmult_Qopp_left.
 repeat rewrite <- Qopp_plus.
 rewrite Qmult_Qopp_left.
 rewrite Qsgn_25.
 unfold spec_Qquadratic_Qpositive_to_Q in H.
 rewrite H.
 constructor.

 repeat rewrite Z_to_Qopp.
 repeat rewrite Qmult_Qopp_left.
 repeat rewrite <- Qopp_plus.
 apply Qopp_resp_nonzero.

 intro H_absurd.
 unfold spec_Qquadratic_Qpositive_to_Q in H.
 rewrite H_absurd in H.
 discriminate H.

 intro H_absurd.
 unfold spec_Qquadratic_Qpositive_to_Q in H.
 rewrite H_absurd in H.
 rewrite Qmult_sym in H.
 discriminate H.
Qed.

(** We use this when 0<=(Z.sgn a+b+c+d) *)
Lemma
 spec_Qquadratic_Qpositive_to_Q_spec_Qquadratic_Qpositive_to_Qpositive2_neg_2
 :
 forall (a b c d e f g h : Z) (p1 p2 : Qpositive),
 Qsgn (spec_Qquadratic_Qpositive_to_Q a b c d e f g h p1 p2) = (-1)%Z ->
 spec_Qquadratic_Qpositive_to_Q a b c d e f g h p1 p2 =
 Qneg
   (spec_Qquadratic_Qpositive_to_Qpositive2 a b c d 
      (- e) (- f) (- g) (- h) p1 p2).
Proof.
 intros a b c d e f g h p1 p2 H.
 unfold spec_Qquadratic_Qpositive_to_Q in |- *.
 unfold spec_Qquadratic_Qpositive_to_Qpositive2 in |- *.
 rewrite <- Q_tail_Qinv.
 rewrite <- Q_tail_Qmult.
 repeat rewrite Qopp_Qpos.
 rewrite <- Q_tail_Q_pos.
 repeat rewrite Z_to_Qopp.
 repeat rewrite Qmult_Qopp_left.
 repeat rewrite <- Qopp_plus.
 rewrite Qinv_Qopp.
 abstract ring.

 apply Qsgn_9.
 repeat rewrite Z_to_Qopp.
 repeat rewrite Qmult_Qopp_left.
 repeat rewrite <- Qopp_plus.
 rewrite Qinv_Qopp.
 rewrite Qmult_sym.
 rewrite Qmult_Qopp_left.
 rewrite Qsgn_25.
 unfold spec_Qquadratic_Qpositive_to_Q in H.
 rewrite Qmult_sym.
 rewrite H.
 constructor.

 intro H_absurd.
 unfold spec_Qquadratic_Qpositive_to_Q in H.
 rewrite H_absurd in H.
 discriminate H.


 repeat rewrite Z_to_Qopp.
 repeat rewrite Qmult_Qopp_left.
 repeat rewrite <- Qopp_plus.
 rewrite Qinv_Qopp.
 apply Qopp_resp_nonzero.

 intro H_absurd.
 unfold spec_Qquadratic_Qpositive_to_Q in H.
 rewrite H_absurd in H.
 rewrite Qmult_sym in H.
 discriminate H.
Qed.

(** Here we don't require that ap1p2+bp1+cp2+d<>0, maybe we should! but the lemma is true anyway! *) 
Lemma spec_Qquadratic_Qpositive_to_Q_Zopp :
 forall (a b c d e f g h : Z) (p1 p2 : Qpositive),
 spec_Qquadratic_Qpositive_to_Q (- a) (- b) (- c) (- d) 
   (- e) (- f) (- g) (- h) p1 p2 =
 spec_Qquadratic_Qpositive_to_Q a b c d e f g h p1 p2.
Proof.
 intros a b c d e f g h p1 p2.
 unfold spec_Qquadratic_Qpositive_to_Q in |- *.
 repeat rewrite Z_to_Qopp.
 repeat rewrite Qmult_Qopp_left.
 repeat rewrite <- Qopp_plus.
 rewrite Qinv_Qopp.
 abstract ring.
Qed. 


(** Here we don't require that ap1p2+bp1+cp2+d<>0, maybe we should! but the lemma is true anyway! *) 
Lemma spec_Qquadratic_Qpositive_to_Q_Zopp_2 :
 forall (a b c d e f g h : Z) (p1 p2 : Qpositive),
 spec_Qquadratic_Qpositive_to_Q (- a) (- b) (- c) (- d) e f g h p1 p2 =
 Qopp (spec_Qquadratic_Qpositive_to_Q a b c d e f g h p1 p2).
Proof.
 intros a b c d e f g h p1 p2.
 unfold spec_Qquadratic_Qpositive_to_Q in |- *.
 repeat rewrite Z_to_Qopp.
 repeat rewrite Qmult_Qopp_left.
 repeat rewrite <- Qopp_plus.
 apply Qmult_Qopp_left.
Qed.
 
Lemma spec_Qquadratic_Qpositive_to_Q_Zopp_3 :
 forall (a b c d e f g h : Z) (p1 p2 : Qpositive),
 spec_Qquadratic_Qpositive_to_Q a b c d (- e) (- f) (- g) (- h) p1 p2 =
 Qopp (spec_Qquadratic_Qpositive_to_Q a b c d e f g h p1 p2).
Proof.
 intros a b c d e f g h p1 p2; unfold spec_Qquadratic_Qpositive_to_Q in |- *;
  repeat rewrite Z_to_Qopp; repeat rewrite Qmult_Qopp_left;
  repeat rewrite <- Qopp_plus; rewrite Qinv_Qopp; rewrite Qmult_sym;
  rewrite Qmult_Qopp_left; rewrite Qmult_sym; reflexivity.
Qed.


Lemma Qquadratic_sign_pres_fraction :
 forall (a b c d e f g h : Z) (p1 p2 : Qpositive)
   (H_Qquadratic_sg_denom_nonzero : Qquadratic_sg_denom_nonzero e f g h p1 p2),
 Qmult
   (Qplus
      (Qplus
         (Qplus
            (Qmult
               (Qmult
                  (qnew_a a b c d e f g h p1 p2 H_Qquadratic_sg_denom_nonzero)
                  (Qpos
                     (qnew_p1 a b c d e f g h p1 p2
                        H_Qquadratic_sg_denom_nonzero)))
               (Qpos
                  (qnew_p2 a b c d e f g h p1 p2
                     H_Qquadratic_sg_denom_nonzero)))
            (Qmult
               (qnew_b a b c d e f g h p1 p2 H_Qquadratic_sg_denom_nonzero)
               (Qpos
                  (qnew_p1 a b c d e f g h p1 p2
                     H_Qquadratic_sg_denom_nonzero))))
         (Qmult (qnew_c a b c d e f g h p1 p2 H_Qquadratic_sg_denom_nonzero)
            (Qpos
               (qnew_p2 a b c d e f g h p1 p2 H_Qquadratic_sg_denom_nonzero))))
      (qnew_d a b c d e f g h p1 p2 H_Qquadratic_sg_denom_nonzero))
   (Qinv
      (Qplus
         (Qplus
            (Qplus
               (Qmult
                  (Qmult
                     (qnew_e a b c d e f g h p1 p2
                        H_Qquadratic_sg_denom_nonzero)
                     (Qpos
                        (qnew_p1 a b c d e f g h p1 p2
                           H_Qquadratic_sg_denom_nonzero)))
                  (Qpos
                     (qnew_p2 a b c d e f g h p1 p2
                        H_Qquadratic_sg_denom_nonzero)))
               (Qmult
                  (qnew_f a b c d e f g h p1 p2 H_Qquadratic_sg_denom_nonzero)
                  (Qpos
                     (qnew_p1 a b c d e f g h p1 p2
                        H_Qquadratic_sg_denom_nonzero))))
            (Qmult
               (qnew_g a b c d e f g h p1 p2 H_Qquadratic_sg_denom_nonzero)
               (Qpos
                  (qnew_p2 a b c d e f g h p1 p2
                     H_Qquadratic_sg_denom_nonzero))))
         (qnew_h a b c d e f g h p1 p2 H_Qquadratic_sg_denom_nonzero))) =
 Qmult
   (Qplus
      (Qplus
         (Qplus (Qmult (Qmult a (Qpos p1)) (Qpos p2)) (Qmult b (Qpos p1)))
         (Qmult c (Qpos p2))) d)
   (Qinv
      (Qplus
         (Qplus
            (Qplus (Qmult (Qmult e (Qpos p1)) (Qpos p2)) (Qmult f (Qpos p1)))
            (Qmult g (Qpos p2))) h)).
Proof.
 fix Qquadratic_sign_pres_fraction 9.
 intros a b c d e f g h.
 unfold qnew_a, qnew_b, qnew_c, qnew_d, qnew_e, qnew_f, qnew_g, qnew_h,
  qnew_p1, qnew_p2 in |- *.
 set (o1 := outside_square a b c d) in *.
 set (o2 := outside_square e f g h) in *.
 intros [xs| xs| ].
  (* p1=(nR xs) *)
  intros [ys| ys| ] H_Qquadratic_sg_denom_nonzero.
(*####################################################################################################*)
(* Begin CHUNK 1 *)
   (* p2=(nR ys) *)
   case (three_integers_dec_inf b c d).
    (* `b = 0`/\`c = 0`/\`d = 0` *)
    intros (Hb, (Hc, Hd)). 
    case (three_integers_dec_inf f g h).  
     (* nR_nR_1: `f = 0`/\`g = 0`/\`h = 0` *)
     clear o1 o2 Qquadratic_sign_pres_fraction; intros (Hf, (Hg, Hh));
      rewrite
       (Qquadratic_sign_nRdL_nRdL_1 a b c d e f g h 
          (nR xs) (nR ys) H_Qquadratic_sg_denom_nonzero)
       ; discriminate || (try (repeat split; assumption)).
     (* ~(`f = 0`/\`g = 0`/\`h = 0`) *)
     case (Z_lt_dec 2 o2).
      (*  nR_nR_2: `2 < o2` *)
      clear Qquadratic_sign_pres_fraction; intros H_o2_gt_2 Hfgh';
       rewrite
        (Qquadratic_sign_nRdL_nRdL_2 a b c d e f g h 
           (nR xs) (nR ys) H_Qquadratic_sg_denom_nonzero)
        ; discriminate || (try (repeat split; assumption)).
      case (Z_lt_dec o2 (-2)).
       (* nR_nR_3: `o2<(-2)` *)
       clear Qquadratic_sign_pres_fraction;
        intros H_o2_lt_min_2 H_o2_gt_2' Hfgh';
        rewrite
         (Qquadratic_sign_nRdL_nRdL_3 a b c d e f g h 
            (nR xs) (nR ys) H_Qquadratic_sg_denom_nonzero)
         ; discriminate || (try (repeat split; assumption)).
       (* nR_nR_4:   ~`o2 < (-2)` /\ ~`2 < o2`/\~(`f = 0`/\`g = 0`/\`h = 0`) *) 
       intros H_o2_lt_min_2' H_o2_gt_2' Hfgh';
        rewrite
         (Qquadratic_sign_nR_nR_4 a b c d e f g h (nR xs) xs 
            (nR ys) ys H_Qquadratic_sg_denom_nonzero
            (Qquadratic_signok_1 _ _ _ _ _ _ H_Qquadratic_sg_denom_nonzero)
            (refl_equal (nR xs)) (refl_equal (nR ys)))
         ; discriminate || (try (repeat split; assumption));
        rewrite spec_Qquadratic_Qpositive_to_Q_nR_nR_unfolded;
        rewrite <-
         Qquadratic_sign_pres_fraction
                                       with
                                       (H_Qquadratic_sg_denom_nonzero := 
                                         Qquadratic_signok_1 e f g h xs ys
                                           H_Qquadratic_sg_denom_nonzero);
        reflexivity.
       (* ~(`b = 0`/\`c = 0`/\`d = 0`) *)
       intro Hbcd'.  
       case (three_integers_dec_inf f g h).  
        (* `f = 0`/\`g = 0`/\`h = 0` *)
        intros (Hf, (Hg, Hh)).
        case (Z_lt_dec 2 o1).
         (*  nR_nR_5: `2 < o1` *)
         clear Qquadratic_sign_pres_fraction; intros H_o1_gt_2;
          rewrite
           (Qquadratic_sign_nRdL_nRdL_5 a b c d e f g h 
              (nR xs) (nR ys) H_Qquadratic_sg_denom_nonzero)
           ; discriminate || (try (repeat split; assumption)).
         case (Z_lt_dec o1 (-2)).
          (* nR_nR_6: `o1<(-2)` *)
          clear Qquadratic_sign_pres_fraction;
           intros H_o1_lt_min_2 H_o1_gt_2';
           rewrite
            (Qquadratic_sign_nRdL_nRdL_6 a b c d e f g h 
               (nR xs) (nR ys) H_Qquadratic_sg_denom_nonzero)
            ; discriminate || (try (repeat split; assumption)).
          (* nR_nR_7:   ~`o1 < (-2)` /\ ~`2 < o1` *)
          intros H_o1_lt_min_2' H_o1_gt_2';
           rewrite
            (Qquadratic_sign_nR_nR_7 a b c d e f g h 
               (nR xs) xs (nR ys) ys H_Qquadratic_sg_denom_nonzero
               (Qquadratic_signok_1 _ _ _ _ _ _ H_Qquadratic_sg_denom_nonzero)
               (refl_equal (nR xs)) (refl_equal (nR ys)))
            ; discriminate || (try (repeat split; assumption));
           rewrite spec_Qquadratic_Qpositive_to_Q_nR_nR_unfolded;
           rewrite <-
            Qquadratic_sign_pres_fraction
                                          with
                                          (H_Qquadratic_sg_denom_nonzero := 
                                            Qquadratic_signok_1 e f g h xs ys
                                              H_Qquadratic_sg_denom_nonzero);
           reflexivity.
        (* ~(`f = 0`/\`g = 0`/\`h = 0`) *)
        intro Hfgh'.
        case (inside_square_1_dec_inf o1 o2).    
         (* nR_nR_8: (inside_square_1 o1 o2) *)
         clear Qquadratic_sign_pres_fraction; intro H_inside_1;
          (rewrite
            (Qquadratic_sign_nRdL_nRdL_8 a b c d e f g h 
               (nR xs) (nR ys) H_Qquadratic_sg_denom_nonzero)
            ; discriminate || (try (repeat split; assumption))).
         (* ~(inside_square_1 o1 o2) *)
         intro H_inside_1'.
         case (inside_square_2_dec_inf o1 o2).    
          (* nR_nR_9: (inside_square_2 o1 o2) *)
          clear Qquadratic_sign_pres_fraction; intro H_inside_2;
           (rewrite
             (Qquadratic_sign_nRdL_nRdL_9 a b c d e f g h 
                (nR xs) (nR ys) H_Qquadratic_sg_denom_nonzero)
             ; discriminate || (try (repeat split; assumption))).
          (*  nR_nR_10: ~(inside_square_1 o1 o2)/\~(inside_square_2 o1 o2) *)
          intros H_inside_2'. 
          rewrite
           (Qquadratic_sign_nR_nR_10 a b c d e f g h 
              (nR xs) xs (nR ys) ys H_Qquadratic_sg_denom_nonzero
              (Qquadratic_signok_1 _ _ _ _ _ _ H_Qquadratic_sg_denom_nonzero)
              (refl_equal (nR xs)) (refl_equal (nR ys)))
           ; discriminate || (try (repeat split; assumption));
           rewrite spec_Qquadratic_Qpositive_to_Q_nR_nR_unfolded;
           rewrite <-
            Qquadratic_sign_pres_fraction
                                          with
                                          (H_Qquadratic_sg_denom_nonzero := 
                                            Qquadratic_signok_1 e f g h xs ys
                                              H_Qquadratic_sg_denom_nonzero);
           reflexivity.
(* End CHUNK 1 *)
(*####################################################################################################*)
(*####################################################################################################*)
(* Begin CHUNK 2 *)
(* We copy CHUNK 1 and query replace
nR_nR with nR_dL 
(nR ys) with (dL ys)
Qquadratic_signok_1 with Qquadratic_signok_2
*)
   (* p2=(dL ys) *)
   case (three_integers_dec_inf b c d).
    (* `b = 0`/\`c = 0`/\`d = 0` *)
    intros (Hb, (Hc, Hd)). 
    case (three_integers_dec_inf f g h).  
     (* nR_dL_1: `f = 0`/\`g = 0`/\`h = 0` *)
     clear o1 o2 Qquadratic_sign_pres_fraction; intros (Hf, (Hg, Hh));
      rewrite
       (Qquadratic_sign_nRdL_nRdL_1 a b c d e f g h 
          (nR xs) (dL ys) H_Qquadratic_sg_denom_nonzero)
       ; discriminate || (try (repeat split; assumption)).
     (* ~(`f = 0`/\`g = 0`/\`h = 0`) *)
     case (Z_lt_dec 2 o2).
      (*  nR_dL_2: `2 < o2` *)
      clear Qquadratic_sign_pres_fraction; intros H_o2_gt_2 Hfgh';
       rewrite
        (Qquadratic_sign_nRdL_nRdL_2 a b c d e f g h 
           (nR xs) (dL ys) H_Qquadratic_sg_denom_nonzero)
        ; discriminate || (try (repeat split; assumption)).
      case (Z_lt_dec o2 (-2)).
       (* nR_dL_3: `o2<(-2)` *)
       clear Qquadratic_sign_pres_fraction;
        intros H_o2_lt_min_2 H_o2_gt_2' Hfgh';
        rewrite
         (Qquadratic_sign_nRdL_nRdL_3 a b c d e f g h 
            (nR xs) (dL ys) H_Qquadratic_sg_denom_nonzero)
         ; discriminate || (try (repeat split; assumption)).
       (* nR_dL_4:   ~`o2 < (-2)` /\ ~`2 < o2`/\~(`f = 0`/\`g = 0`/\`h = 0`) *) 
       intros H_o2_lt_min_2' H_o2_gt_2' Hfgh';
        rewrite
         (Qquadratic_sign_nR_dL_4 a b c d e f g h (nR xs) xs 
            (dL ys) ys H_Qquadratic_sg_denom_nonzero
            (Qquadratic_signok_2 _ _ _ _ _ _ H_Qquadratic_sg_denom_nonzero)
            (refl_equal (nR xs)) (refl_equal (dL ys)))
         ; discriminate || (try (repeat split; assumption));
        rewrite spec_Qquadratic_Qpositive_to_Q_nR_dL_unfolded;
        rewrite <-
         Qquadratic_sign_pres_fraction
                                       with
                                       (H_Qquadratic_sg_denom_nonzero := 
                                         Qquadratic_signok_2 e f g h xs ys
                                           H_Qquadratic_sg_denom_nonzero);
        reflexivity.
       (* ~(`b = 0`/\`c = 0`/\`d = 0`) *)
       intro Hbcd'.  
       case (three_integers_dec_inf f g h).  
        (* `f = 0`/\`g = 0`/\`h = 0` *)
        intros (Hf, (Hg, Hh)).
        case (Z_lt_dec 2 o1).
         (*  nR_dL_5: `2 < o1` *)
         clear Qquadratic_sign_pres_fraction; intros H_o1_gt_2;
          rewrite
           (Qquadratic_sign_nRdL_nRdL_5 a b c d e f g h 
              (nR xs) (dL ys) H_Qquadratic_sg_denom_nonzero)
           ; discriminate || (try (repeat split; assumption)).
         case (Z_lt_dec o1 (-2)).
          (* nR_dL_6: `o1<(-2)` *)
          clear Qquadratic_sign_pres_fraction;
           intros H_o1_lt_min_2 H_o1_gt_2';
           rewrite
            (Qquadratic_sign_nRdL_nRdL_6 a b c d e f g h 
               (nR xs) (dL ys) H_Qquadratic_sg_denom_nonzero)
            ; discriminate || (try (repeat split; assumption)).
          (* nR_dL_7:   ~`o1 < (-2)` /\ ~`2 < o1` *)
          intros H_o1_lt_min_2' H_o1_gt_2';
           rewrite
            (Qquadratic_sign_nR_dL_7 a b c d e f g h 
               (nR xs) xs (dL ys) ys H_Qquadratic_sg_denom_nonzero
               (Qquadratic_signok_2 _ _ _ _ _ _ H_Qquadratic_sg_denom_nonzero)
               (refl_equal (nR xs)) (refl_equal (dL ys)))
            ; discriminate || (try (repeat split; assumption));
           rewrite spec_Qquadratic_Qpositive_to_Q_nR_dL_unfolded;
           rewrite <-
            Qquadratic_sign_pres_fraction
                                          with
                                          (H_Qquadratic_sg_denom_nonzero := 
                                            Qquadratic_signok_2 e f g h xs ys
                                              H_Qquadratic_sg_denom_nonzero);
           reflexivity.
        (* ~(`f = 0`/\`g = 0`/\`h = 0`) *)
        intro Hfgh'.
        case (inside_square_1_dec_inf o1 o2).    
         (* nR_dL_8: (inside_square_1 o1 o2) *)
         clear Qquadratic_sign_pres_fraction; intro H_inside_1;
          (rewrite
            (Qquadratic_sign_nRdL_nRdL_8 a b c d e f g h 
               (nR xs) (dL ys) H_Qquadratic_sg_denom_nonzero)
            ; discriminate || (try (repeat split; assumption))).
         (* ~(inside_square_1 o1 o2) *)
         intro H_inside_1'.
         case (inside_square_2_dec_inf o1 o2).    
          (* nR_dL_9: (inside_square_2 o1 o2) *)
          clear Qquadratic_sign_pres_fraction; intro H_inside_2;
           (rewrite
             (Qquadratic_sign_nRdL_nRdL_9 a b c d e f g h 
                (nR xs) (dL ys) H_Qquadratic_sg_denom_nonzero)
             ; discriminate || (try (repeat split; assumption))).
          (*  nR_dL_10: ~(inside_square_1 o1 o2)/\~(inside_square_2 o1 o2) *)
          intros H_inside_2'. 
          rewrite
           (Qquadratic_sign_nR_dL_10 a b c d e f g h 
              (nR xs) xs (dL ys) ys H_Qquadratic_sg_denom_nonzero
              (Qquadratic_signok_2 _ _ _ _ _ _ H_Qquadratic_sg_denom_nonzero)
              (refl_equal (nR xs)) (refl_equal (dL ys)))
           ; discriminate || (try (repeat split; assumption));
           rewrite spec_Qquadratic_Qpositive_to_Q_nR_dL_unfolded;
           rewrite <-
            Qquadratic_sign_pres_fraction
                                          with
                                          (H_Qquadratic_sg_denom_nonzero := 
                                            Qquadratic_signok_2 e f g h xs ys
                                              H_Qquadratic_sg_denom_nonzero);
           reflexivity.
(* End CHUNK 2 *)
(*####################################################################################################*)
(*####################################################################################################*)
(* Begin CHUNK 3 *)
  (* p2=One *)
  clear o1 o2 Qquadratic_sign_pres_fraction.
  generalize (Qquadratic_signok_0' _ _ _ _ _ H_Qquadratic_sg_denom_nonzero).
  intro H_Qhomographic_sg_denom_nonzero.
  set
   (L3 :=
    Qhomographic_sign (a + b) (c + d) (e + f) (g + h) 
      (nR xs) H_Qhomographic_sg_denom_nonzero) in *.
  set (l1 := fst L3) in *.
  set (l2 := fst (snd L3)) in *.
  set (l3 := snd (snd L3)) in *.
  set (na := fst l2) in *.
  set (nb := fst (snd l2)) in *.
  set (nc := fst (snd (snd l2))) in *.
  set (nd := snd (snd (snd l2))) in *.
  rewrite
   (Qquadratic_sign_nRdL_One a b c d e f g h (nR xs) One
      H_Qquadratic_sg_denom_nonzero l1 na nb nc nd l3
      H_Qhomographic_sg_denom_nonzero);
   [ idtac
   | fold L3 in |- *; repeat (apply pair_2; try reflexivity)
   | discriminate
   | reflexivity ]. 
  rewrite spec_Qquadratic_Qpositive_to_Q_p_One_unfolded.
  unfold snd in |- *.
  unfold fst in |- *.
  repeat rewrite Zplus_0_l.
  repeat rewrite Qmult_one_right. 
  replace na with
   (new_a (a + b) (c + d) (e + f) (g + h) (nR xs)
      H_Qhomographic_sg_denom_nonzero); trivial.
  replace nb with
   (new_b (a + b) (c + d) (e + f) (g + h) (nR xs)
      H_Qhomographic_sg_denom_nonzero); trivial.
  replace nc with
   (new_c (a + b) (c + d) (e + f) (g + h) (nR xs)
      H_Qhomographic_sg_denom_nonzero); trivial.
  replace nd with
   (new_d (a + b) (c + d) (e + f) (g + h) (nR xs)
      H_Qhomographic_sg_denom_nonzero); trivial.
  replace l3 with
   (new_p (a + b) (c + d) (e + f) (g + h) (nR xs)
      H_Qhomographic_sg_denom_nonzero); trivial.
  rewrite sg_pres_fraction. 
  repeat rewrite Z_to_Qplus.
  clear L3 l1 l2 l3 na nb nc nd; apply f_equal2 with Q Q;
   try apply f_equal with Q; abstract ring.
(* End CHUNK 3 *)
  (* p1=(dL xs) *)
  intros [ys| ys| ] H_Qquadratic_sg_denom_nonzero.
(*####################################################################################################*)
(* Begin CHUNK 4 *)
   (* p2=(nR ys) *)
   case (three_integers_dec_inf b c d).
    (* `b = 0`/\`c = 0`/\`d = 0` *)
    intros (Hb, (Hc, Hd)). 
    case (three_integers_dec_inf f g h).  
     (* dL_nR_1: `f = 0`/\`g = 0`/\`h = 0` *)
     clear o1 o2 Qquadratic_sign_pres_fraction; intros (Hf, (Hg, Hh));
      rewrite
       (Qquadratic_sign_nRdL_nRdL_1 a b c d e f g h 
          (dL xs) (nR ys) H_Qquadratic_sg_denom_nonzero)
       ; discriminate || (try (repeat split; assumption)).
     (* ~(`f = 0`/\`g = 0`/\`h = 0`) *)
     case (Z_lt_dec 2 o2).
      (*  dL_nR_2: `2 < o2` *)
      clear Qquadratic_sign_pres_fraction; intros H_o2_gt_2 Hfgh';
       rewrite
        (Qquadratic_sign_nRdL_nRdL_2 a b c d e f g h 
           (dL xs) (nR ys) H_Qquadratic_sg_denom_nonzero)
        ; discriminate || (try (repeat split; assumption)).
      case (Z_lt_dec o2 (-2)).
       (* dL_nR_3: `o2<(-2)` *)
       clear Qquadratic_sign_pres_fraction;
        intros H_o2_lt_min_2 H_o2_gt_2' Hfgh';
        rewrite
         (Qquadratic_sign_nRdL_nRdL_3 a b c d e f g h 
            (dL xs) (nR ys) H_Qquadratic_sg_denom_nonzero)
         ; discriminate || (try (repeat split; assumption)).
       (* dL_nR_4:   ~`o2 < (-2)` /\ ~`2 < o2`/\~(`f = 0`/\`g = 0`/\`h = 0`) *) 
       intros H_o2_lt_min_2' H_o2_gt_2' Hfgh';
        rewrite
         (Qquadratic_sign_dL_nR_4 a b c d e f g h (dL xs) xs 
            (nR ys) ys H_Qquadratic_sg_denom_nonzero
            (Qquadratic_signok_3 _ _ _ _ _ _ H_Qquadratic_sg_denom_nonzero)
            (refl_equal (dL xs)) (refl_equal (nR ys)))
         ; discriminate || (try (repeat split; assumption));
        rewrite spec_Qquadratic_Qpositive_to_Q_dL_nR_unfolded;
        rewrite <-
         Qquadratic_sign_pres_fraction
                                       with
                                       (H_Qquadratic_sg_denom_nonzero := 
                                         Qquadratic_signok_3 e f g h xs ys
                                           H_Qquadratic_sg_denom_nonzero);
        reflexivity.
       (* ~(`b = 0`/\`c = 0`/\`d = 0`) *)
       intro Hbcd'.  
       case (three_integers_dec_inf f g h).  
        (* `f = 0`/\`g = 0`/\`h = 0` *)
        intros (Hf, (Hg, Hh)).
        case (Z_lt_dec 2 o1).
         (*  dL_nR_5: `2 < o1` *)
         clear Qquadratic_sign_pres_fraction; intros H_o1_gt_2;
          rewrite
           (Qquadratic_sign_nRdL_nRdL_5 a b c d e f g h 
              (dL xs) (nR ys) H_Qquadratic_sg_denom_nonzero)
           ; discriminate || (try (repeat split; assumption)).
         case (Z_lt_dec o1 (-2)).
          (* dL_nR_6: `o1<(-2)` *)
          clear Qquadratic_sign_pres_fraction;
           intros H_o1_lt_min_2 H_o1_gt_2';
           rewrite
            (Qquadratic_sign_nRdL_nRdL_6 a b c d e f g h 
               (dL xs) (nR ys) H_Qquadratic_sg_denom_nonzero)
            ; discriminate || (try (repeat split; assumption)).
          (* dL_nR_7:   ~`o1 < (-2)` /\ ~`2 < o1` *)
          intros H_o1_lt_min_2' H_o1_gt_2';
           rewrite
            (Qquadratic_sign_dL_nR_7 a b c d e f g h 
               (dL xs) xs (nR ys) ys H_Qquadratic_sg_denom_nonzero
               (Qquadratic_signok_3 _ _ _ _ _ _ H_Qquadratic_sg_denom_nonzero)
               (refl_equal (dL xs)) (refl_equal (nR ys)))
            ; discriminate || (try (repeat split; assumption));
           rewrite spec_Qquadratic_Qpositive_to_Q_dL_nR_unfolded;
           rewrite <-
            Qquadratic_sign_pres_fraction
                                          with
                                          (H_Qquadratic_sg_denom_nonzero := 
                                            Qquadratic_signok_3 e f g h xs ys
                                              H_Qquadratic_sg_denom_nonzero);
           reflexivity.
        (* ~(`f = 0`/\`g = 0`/\`h = 0`) *)
        intro Hfgh'.
        case (inside_square_1_dec_inf o1 o2).    
         (* dL_nR_8: (inside_square_1 o1 o2) *)
         clear Qquadratic_sign_pres_fraction; intro H_inside_1;
          (rewrite
            (Qquadratic_sign_nRdL_nRdL_8 a b c d e f g h 
               (dL xs) (nR ys) H_Qquadratic_sg_denom_nonzero)
            ; discriminate || (try (repeat split; assumption))).
         (* ~(inside_square_1 o1 o2) *)
         intro H_inside_1'.
         case (inside_square_2_dec_inf o1 o2).    
          (* dL_nR_9: (inside_square_2 o1 o2) *)
          clear Qquadratic_sign_pres_fraction; intro H_inside_2;
           (rewrite
             (Qquadratic_sign_nRdL_nRdL_9 a b c d e f g h 
                (dL xs) (nR ys) H_Qquadratic_sg_denom_nonzero)
             ; discriminate || (try (repeat split; assumption))).
          (*  dL_nR_10: ~(inside_square_1 o1 o2)/\~(inside_square_2 o1 o2) *)
          intros H_inside_2'. 
          rewrite
           (Qquadratic_sign_dL_nR_10 a b c d e f g h 
              (dL xs) xs (nR ys) ys H_Qquadratic_sg_denom_nonzero
              (Qquadratic_signok_3 _ _ _ _ _ _ H_Qquadratic_sg_denom_nonzero)
              (refl_equal (dL xs)) (refl_equal (nR ys)))
           ; discriminate || (try (repeat split; assumption));
           rewrite spec_Qquadratic_Qpositive_to_Q_dL_nR_unfolded;
           rewrite <-
            Qquadratic_sign_pres_fraction
                                          with
                                          (H_Qquadratic_sg_denom_nonzero := 
                                            Qquadratic_signok_3 e f g h xs ys
                                              H_Qquadratic_sg_denom_nonzero);
           reflexivity.
(* End CHUNK 4 *)
(*####################################################################################################*)
(*####################################################################################################*)
(* Begin CHUNK 5 *)
(* We copy CHUNK 1 and query replace
dL_nR with dL_dL 
(nR ys) with (dL ys)
Qquadratic_signok_3 with Qquadratic_signok_4
*)
   (* p2=(dL ys) *)
   case (three_integers_dec_inf b c d).
    (* `b = 0`/\`c = 0`/\`d = 0` *)
    intros (Hb, (Hc, Hd)). 
    case (three_integers_dec_inf f g h).  
     (* dL_dL_1: `f = 0`/\`g = 0`/\`h = 0` *)
     clear o1 o2 Qquadratic_sign_pres_fraction; intros (Hf, (Hg, Hh));
      rewrite
       (Qquadratic_sign_nRdL_nRdL_1 a b c d e f g h 
          (dL xs) (dL ys) H_Qquadratic_sg_denom_nonzero)
       ; discriminate || (try (repeat split; assumption)).
     (* ~(`f = 0`/\`g = 0`/\`h = 0`) *)
     case (Z_lt_dec 2 o2).
      (*  dL_dL_2: `2 < o2` *)
      clear Qquadratic_sign_pres_fraction; intros H_o2_gt_2 Hfgh';
       rewrite
        (Qquadratic_sign_nRdL_nRdL_2 a b c d e f g h 
           (dL xs) (dL ys) H_Qquadratic_sg_denom_nonzero)
        ; discriminate || (try (repeat split; assumption)).
      case (Z_lt_dec o2 (-2)).
       (* dL_dL_3: `o2<(-2)` *)
       clear Qquadratic_sign_pres_fraction;
        intros H_o2_lt_min_2 H_o2_gt_2' Hfgh';
        rewrite
         (Qquadratic_sign_nRdL_nRdL_3 a b c d e f g h 
            (dL xs) (dL ys) H_Qquadratic_sg_denom_nonzero)
         ; discriminate || (try (repeat split; assumption)).
       (* dL_dL_4:   ~`o2 < (-2)` /\ ~`2 < o2`/\~(`f = 0`/\`g = 0`/\`h = 0`) *) 
       intros H_o2_lt_min_2' H_o2_gt_2' Hfgh';
        rewrite
         (Qquadratic_sign_dL_dL_4 a b c d e f g h (dL xs) xs 
            (dL ys) ys H_Qquadratic_sg_denom_nonzero
            (Qquadratic_signok_4 _ _ _ _ _ _ H_Qquadratic_sg_denom_nonzero)
            (refl_equal (dL xs)) (refl_equal (dL ys)))
         ; discriminate || (try (repeat split; assumption));
        rewrite spec_Qquadratic_Qpositive_to_Q_dL_dL_unfolded;
        rewrite <-
         Qquadratic_sign_pres_fraction
                                       with
                                       (H_Qquadratic_sg_denom_nonzero := 
                                         Qquadratic_signok_4 e f g h xs ys
                                           H_Qquadratic_sg_denom_nonzero);
        reflexivity.
       (* ~(`b = 0`/\`c = 0`/\`d = 0`) *)
       intro Hbcd'.  
       case (three_integers_dec_inf f g h).  
        (* `f = 0`/\`g = 0`/\`h = 0` *)
        intros (Hf, (Hg, Hh)).
        case (Z_lt_dec 2 o1).
         (*  dL_dL_5: `2 < o1` *)
         clear Qquadratic_sign_pres_fraction; intros H_o1_gt_2;
          rewrite
           (Qquadratic_sign_nRdL_nRdL_5 a b c d e f g h 
              (dL xs) (dL ys) H_Qquadratic_sg_denom_nonzero)
           ; discriminate || (try (repeat split; assumption)).
         case (Z_lt_dec o1 (-2)).
          (* dL_dL_6: `o1<(-2)` *)
          clear Qquadratic_sign_pres_fraction;
           intros H_o1_lt_min_2 H_o1_gt_2';
           rewrite
            (Qquadratic_sign_nRdL_nRdL_6 a b c d e f g h 
               (dL xs) (dL ys) H_Qquadratic_sg_denom_nonzero)
            ; discriminate || (try (repeat split; assumption)).
          (* dL_dL_7:   ~`o1 < (-2)` /\ ~`2 < o1` *)
          intros H_o1_lt_min_2' H_o1_gt_2';
           rewrite
            (Qquadratic_sign_dL_dL_7 a b c d e f g h 
               (dL xs) xs (dL ys) ys H_Qquadratic_sg_denom_nonzero
               (Qquadratic_signok_4 _ _ _ _ _ _ H_Qquadratic_sg_denom_nonzero)
               (refl_equal (dL xs)) (refl_equal (dL ys)))
            ; discriminate || (try (repeat split; assumption));
           rewrite spec_Qquadratic_Qpositive_to_Q_dL_dL_unfolded;
           rewrite <-
            Qquadratic_sign_pres_fraction
                                          with
                                          (H_Qquadratic_sg_denom_nonzero := 
                                            Qquadratic_signok_4 e f g h xs ys
                                              H_Qquadratic_sg_denom_nonzero);
           reflexivity.
        (* ~(`f = 0`/\`g = 0`/\`h = 0`) *)
        intro Hfgh'.
        case (inside_square_1_dec_inf o1 o2).    
         (* dL_dL_8: (inside_square_1 o1 o2) *)
         clear Qquadratic_sign_pres_fraction; intro H_inside_1;
          (rewrite
            (Qquadratic_sign_nRdL_nRdL_8 a b c d e f g h 
               (dL xs) (dL ys) H_Qquadratic_sg_denom_nonzero)
            ; discriminate || (try (repeat split; assumption))).
         (* ~(inside_square_1 o1 o2) *)
         intro H_inside_1'.
         case (inside_square_2_dec_inf o1 o2).    
          (* dL_dL_9: (inside_square_2 o1 o2) *)
          clear Qquadratic_sign_pres_fraction; intro H_inside_2;
           (rewrite
             (Qquadratic_sign_nRdL_nRdL_9 a b c d e f g h 
                (dL xs) (dL ys) H_Qquadratic_sg_denom_nonzero)
             ; discriminate || (try (repeat split; assumption))).
          (*  dL_dL_10: ~(inside_square_1 o1 o2)/\~(inside_square_2 o1 o2) *)
          intros H_inside_2'. 
          rewrite
           (Qquadratic_sign_dL_dL_10 a b c d e f g h 
              (dL xs) xs (dL ys) ys H_Qquadratic_sg_denom_nonzero
              (Qquadratic_signok_4 _ _ _ _ _ _ H_Qquadratic_sg_denom_nonzero)
              (refl_equal (dL xs)) (refl_equal (dL ys)))
           ; discriminate || (try (repeat split; assumption));
           rewrite spec_Qquadratic_Qpositive_to_Q_dL_dL_unfolded;
           rewrite <-
            Qquadratic_sign_pres_fraction
                                          with
                                          (H_Qquadratic_sg_denom_nonzero := 
                                            Qquadratic_signok_4 e f g h xs ys
                                              H_Qquadratic_sg_denom_nonzero);
           reflexivity.
(* End CHUNK 5 *)
(*####################################################################################################*)
(*####################################################################################################*)
(* Begin CHUNK 6 *)
  (* p2=One *)
  clear o1 o2 Qquadratic_sign_pres_fraction.
  generalize (Qquadratic_signok_0' _ _ _ _ _ H_Qquadratic_sg_denom_nonzero).
  intro H_Qhomographic_sg_denom_nonzero.
  set
   (L3 :=
    Qhomographic_sign (a + b) (c + d) (e + f) (g + h) 
      (dL xs) H_Qhomographic_sg_denom_nonzero) in *.
  set (l1 := fst L3) in *.
  set (l2 := fst (snd L3)) in *.
  set (l3 := snd (snd L3)) in *.
  set (na := fst l2) in *.
  set (nb := fst (snd l2)) in *.
  set (nc := fst (snd (snd l2))) in *.
  set (nd := snd (snd (snd l2))) in *.
  rewrite
   (Qquadratic_sign_nRdL_One a b c d e f g h (dL xs) One
      H_Qquadratic_sg_denom_nonzero l1 na nb nc nd l3
      H_Qhomographic_sg_denom_nonzero);
   [ idtac
   | fold L3 in |- *; repeat (apply pair_2; try reflexivity)
   | discriminate
   | reflexivity ]. 
  rewrite spec_Qquadratic_Qpositive_to_Q_p_One_unfolded.
  unfold snd in |- *.
  unfold fst in |- *.
  repeat rewrite Zplus_0_l.
  repeat rewrite Qmult_one_right. 
  replace na with
   (new_a (a + b) (c + d) (e + f) (g + h) (dL xs)
      H_Qhomographic_sg_denom_nonzero); trivial.
  replace nb with
   (new_b (a + b) (c + d) (e + f) (g + h) (dL xs)
      H_Qhomographic_sg_denom_nonzero); trivial.
  replace nc with
   (new_c (a + b) (c + d) (e + f) (g + h) (dL xs)
      H_Qhomographic_sg_denom_nonzero); trivial.
  replace nd with
   (new_d (a + b) (c + d) (e + f) (g + h) (dL xs)
      H_Qhomographic_sg_denom_nonzero); trivial.
  replace l3 with
   (new_p (a + b) (c + d) (e + f) (g + h) (dL xs)
      H_Qhomographic_sg_denom_nonzero); trivial.
  rewrite sg_pres_fraction. 
  repeat rewrite Z_to_Qplus.
  clear L3 l1 l2 l3 na nb nc nd; apply f_equal2 with Q Q;
   try apply f_equal with Q; abstract ring.
(* End CHUNK 6 *)
(*####################################################################################################*)
(* Begin CHUNK 7 *)
  (* p1=One *)
  clear o1 o2 Qquadratic_sign_pres_fraction.
  intros p2 H_Qquadratic_sg_denom_nonzero.
  generalize (Qquadratic_signok_0 _ _ _ _ _ H_Qquadratic_sg_denom_nonzero).
  intro H_Qhomographic_sg_denom_nonzero.
  set
   (L3 :=
    Qhomographic_sign (a + c) (b + d) (e + g) (f + h) p2
      H_Qhomographic_sg_denom_nonzero) in *.
  set (l1 := fst L3) in *.
  set (l2 := fst (snd L3)) in *.
  set (l3 := snd (snd L3)) in *.
  set (na := fst l2) in *.
  set (nb := fst (snd l2)) in *.
  set (nc := fst (snd (snd l2))) in *.
  set (nd := snd (snd (snd l2))) in *.
  rewrite
   (Qquadratic_sign_One_y a b c d e f g h One p2
      H_Qquadratic_sg_denom_nonzero l1 na nb nc nd l3
      H_Qhomographic_sg_denom_nonzero);
   [ idtac
   | fold L3 in |- *; repeat (apply pair_2; try reflexivity)
   | reflexivity ]. 
  rewrite spec_Qquadratic_Qpositive_to_Q_One_p_unfolded.
  unfold snd in |- *.
  unfold fst in |- *.
  repeat rewrite Zplus_0_l.
  repeat rewrite Qmult_one_right. 
  replace na with
   (new_a (a + c) (b + d) (e + g) (f + h) p2 H_Qhomographic_sg_denom_nonzero);
   trivial.
  replace nb with
   (new_b (a + c) (b + d) (e + g) (f + h) p2 H_Qhomographic_sg_denom_nonzero);
   trivial.
  replace nc with
   (new_c (a + c) (b + d) (e + g) (f + h) p2 H_Qhomographic_sg_denom_nonzero);
   trivial.
  replace nd with
   (new_d (a + c) (b + d) (e + g) (f + h) p2 H_Qhomographic_sg_denom_nonzero);
   trivial.
  replace l3 with
   (new_p (a + c) (b + d) (e + g) (f + h) p2 H_Qhomographic_sg_denom_nonzero);
   trivial.
  rewrite sg_pres_fraction. 
  repeat rewrite Z_to_Qplus.
  clear L3 l1 l2 l3 na nb nc nd; apply f_equal2 with Q Q;
   try apply f_equal with Q; abstract ring.
(* End CHUNK 7 *)
Qed.


Lemma Qquadratic_sg_denom_nonzero_correct_1 :
 forall (e f g h : Z) (p1 p2 : Qpositive),
 Qquadratic_sg_denom_nonzero e f g h p1 p2 ->
 Qplus
   (Qplus (Qplus (Qmult (Qmult e (Qpos p1)) (Qpos p2)) (Qmult f (Qpos p1)))
      (Qmult g (Qpos p2))) h <> Zero.
Proof. 
  intros e f g h p1 p2 H_Qquadratic_sg_denom_nonzero.
  induction H_Qquadratic_sg_denom_nonzero.
  (* 1 *)
  replace Zero with (Z_to_Q 0); trivial.
  rewrite H.
  repeat rewrite Qmult_one_right.
  rewrite <- Q_distr_left.
  rewrite <- Qplus_assoc.
  do 2 rewrite <- Z_to_Qplus.
  apply Qhomographic_sg_denom_nonzero_correct_1; assumption.
  (* 2 *)
  replace Zero with (Z_to_Q 0); trivial.
  rewrite H.
  repeat rewrite Qmult_one_right.
  rewrite <- Qplus_assoc with (m := Z_to_Q f).
  rewrite (Qplus_sym f). 
  rewrite Qplus_assoc.
  rewrite <- Q_distr_left.
  rewrite <- Qplus_assoc.
  do 2 rewrite <- Z_to_Qplus.
  apply Qhomographic_sg_denom_nonzero_correct_1; assumption.
  (* 3 *)
  do 2 rewrite Qpos_nR.  
  intro H.
  apply IHH_Qquadratic_sg_denom_nonzero.
  rewrite <- H.
  repeat rewrite Z_to_Qplus.
  abstract ring.
  (* 4 *)
  abstract (rewrite Qpos_nR; rewrite Qpos_dL; intro H;
             repeat rewrite Z_to_Qplus in IHH_Qquadratic_sg_denom_nonzero;
             apply
              (Qmult_resp_nonzero _ (Qinv (Qplus (Qpos p2) Qone))
                 IHH_Qquadratic_sg_denom_nonzero);
             [ discriminate | rewrite <- H; field; discriminate ]).
  (* 5 *)
  abstract (rewrite Qpos_nR; rewrite Qpos_dL; intro H;
             repeat rewrite Z_to_Qplus in IHH_Qquadratic_sg_denom_nonzero;
             apply
              (Qmult_resp_nonzero _ (Qinv (Qplus (Qpos p1) Qone))
                 IHH_Qquadratic_sg_denom_nonzero);
             [ discriminate | rewrite <- H; field; discriminate ]).
  (* 6 *)
  abstract (do 2 rewrite Qpos_dL; intro H;
             repeat rewrite Z_to_Qplus in IHH_Qquadratic_sg_denom_nonzero;
             apply
              (Qmult_resp_nonzero _
                 (Qinv (Qmult (Qplus (Qpos p1) Qone) (Qplus (Qpos p2) Qone)))
                 IHH_Qquadratic_sg_denom_nonzero);
             [ discriminate | rewrite <- H; field; split; discriminate ]).
Qed.

Lemma Qquadratic_sg_denom_nonzero_correct_2 :
 forall (e f g h : Z) (p1 p2 : Qpositive),
 Qplus
   (Qplus (Qplus (Qmult (Qmult e (Qpos p1)) (Qpos p2)) (Qmult f (Qpos p1)))
      (Qmult g (Qpos p2))) h <> Zero ->
 Qquadratic_sg_denom_nonzero e f g h p1 p2.
Proof. 
 intros e f g h p1.
 generalize e f g h.
 clear e f g h.
 induction p1 as [xs| xs| ].
  (* p1 = nR *)
  intros e f g h p2.
  generalize e f g h; clear e f g h.
  destruct p2 as [ys| ys| ].
  (* nR_nR *)
  intros e f g h H.
  apply Qquadratic_signok1.
  apply IHxs.
  intro H'; apply H.
  do 2 rewrite Qpos_nR.
  rewrite <- H'.
  repeat rewrite Z_to_Qplus.
  abstract ring.
  (* nR_dL *)
  intros e f g h H.
  apply Qquadratic_signok2.
  apply IHxs.
  repeat rewrite Z_to_Qplus.
  repeat rewrite Qpos_dL in H; repeat rewrite Qpos_nR in H.
  assert (H0 : Qplus (Qpos ys) Qone <> Zero); [ discriminate | idtac ].
  generalize (Qmult_resp_nonzero _ (Qplus (Qpos ys) Qone) H H0).
  intro H1.
  intro H'.
  apply H1.
  rewrite <- H'.
  abstract (field; discriminate).
  (* nR_One *)
  intros e f g h H.
  apply Qquadratic_signok0.
  reflexivity.
  apply Qhomographic_sg_denom_nonzero_correct_2.
  do 2 rewrite Z_to_Qplus.
  intro H'; apply H.
  rewrite <- H'.
  abstract ring.
  (* p1 = dL *)
  intros e f g h p2.
  generalize e f g h; clear e f g h.
  destruct p2 as [ys| ys| ].
  (* dL_nR *)
  intros e f g h H.
  apply Qquadratic_signok3.
  apply IHxs.
  repeat rewrite Z_to_Qplus.
  repeat rewrite Qpos_dL in H; repeat rewrite Qpos_nR in H.
  assert (H0 : Qplus (Qpos xs) Qone <> Zero); [ discriminate | idtac ].
  generalize (Qmult_resp_nonzero _ (Qplus (Qpos xs) Qone) H H0).
  intro H1.
  intro H'.
  apply H1.
  rewrite <- H'.
  abstract (field; discriminate).
  (* dL_dL *)
  intros e f g h H.
  apply Qquadratic_signok4.
  apply IHxs.
  repeat rewrite Z_to_Qplus.
  repeat rewrite Qpos_dL in H.
  assert (H0 : Qmult (Qplus (Qpos xs) Qone) (Qplus (Qpos ys) Qone) <> Zero);
   [ discriminate | idtac ].
  generalize
   (Qmult_resp_nonzero _
      (Qmult (Qplus (Qpos xs) Qone) (Qplus (Qpos ys) Qone)) H H0).
  intro H1.
  intro H'.
  apply H1.
  rewrite <- H'.
  abstract (field; split; discriminate).
  (* dL_One *)
  intros e f g h H.
  apply Qquadratic_signok0.
  reflexivity.
  apply Qhomographic_sg_denom_nonzero_correct_2.
  do 2 rewrite Z_to_Qplus.
  intro H'; apply H.
  rewrite <- H'.
  abstract ring.
  (* p1 = On *)
  (* One_y *)
  intros e f g h p2 H.
  apply Qquadratic_signok0'.
  reflexivity.
  apply Qhomographic_sg_denom_nonzero_correct_2.
  do 2 rewrite Z_to_Qplus.
  intro H'; apply H.
  rewrite <- H'.
  abstract ring.
Qed.


Lemma a_field_equality_2 :
 forall a b c d e f g h q1 q2 : Q,
 e <> Zero ->
 Qmult a h = Qmult d e ->
 Qmult a g = Qmult c e ->
 Qmult a f = Qmult b e ->
 Qplus (Qplus (Qplus (Qmult (Qmult e q1) q2) (Qmult f q1)) (Qmult g q2)) h <>
 Zero ->
 Qmult a (Qinv e) =
 Qmult
   (Qplus (Qplus (Qplus (Qmult (Qmult a q1) q2) (Qmult b q1)) (Qmult c q2)) d)
   (Qinv
      (Qplus
         (Qplus (Qplus (Qmult (Qmult e q1) q2) (Qmult f q1)) (Qmult g q2)) h)).
Proof.
 intros a b c d e f g h p1 p2 He H5 H4 H1 Hdenom.
 symmetry  in |- *.
 rewrite Qdiv_num_denom with (p := e); [ idtac | assumption ].
 rewrite Q_distr_left. (*  with z:=e. *)
 rewrite <- H5.
 rewrite Q_distr_left with (z := e).
 rewrite Q_distr_left with (z := e).
 replace (Qmult (Qmult b p1) e) with (Qmult (Qmult f p1) a).
 replace (Qmult (Qmult c p2) e) with (Qmult (Qmult g p2) a).
 replace (Qmult (Qmult (Qmult a p1) p2) e) with
  (Qmult (Qmult (Qmult e p1) p2) a).
 rewrite <- Q_distr_left with (z := a).
 rewrite <- Q_distr_left with (z := a).
 rewrite (Qmult_sym a).
 rewrite <- Q_distr_left.
 rewrite Qmult_sym with (m := a). 
 rewrite Qmult_sym with (m := e). 
 rewrite <- Qdiv_num_denom; [ reflexivity | assumption ].
 abstract ring.
 replace (Qmult (Qmult g p2) a) with (Qmult (Qmult a g) p2) by ring;
   rewrite H4; ring.
 replace (Qmult (Qmult f p1) a) with (Qmult (Qmult a f) p1) by ring;
   rewrite H1; ring.
Qed.


Lemma a_field_equality_3 :
 forall a b c d e f g h q1 q2 : Q,
 f <> Zero ->
 Qmult b h = Qmult d f ->
 Qmult b g = Qmult c f ->
 Qmult a f = Qmult b e ->
 Qplus (Qplus (Qplus (Qmult (Qmult e q1) q2) (Qmult f q1)) (Qmult g q2)) h <>
 Zero ->
 Qmult b (Qinv f) =
 Qmult
   (Qplus (Qplus (Qplus (Qmult (Qmult a q1) q2) (Qmult b q1)) (Qmult c q2)) d)
   (Qinv
      (Qplus
         (Qplus (Qplus (Qmult (Qmult e q1) q2) (Qmult f q1)) (Qmult g q2)) h)).
Proof.
 intros a b c d e f g h p1 p2 He H6 H2 H1 Hdenom.
 symmetry  in |- *.
 rewrite Qdiv_num_denom with (p := f); [ idtac | assumption ].
 rewrite Q_distr_left. (*  with z:=e. *)
 rewrite <- H6.
 rewrite Q_distr_left with (z := f).
 rewrite Q_distr_left with (z := f).
 replace (Qmult (Qmult b p1) f) with (Qmult (Qmult f p1) b).
 replace (Qmult (Qmult c p2) f) with (Qmult (Qmult g p2) b).
 replace (Qmult (Qmult (Qmult a p1) p2) f) with
  (Qmult (Qmult (Qmult e p1) p2) b).
 rewrite <- Q_distr_left with (z := b).
 rewrite <- Q_distr_left with (z := b).
 rewrite (Qmult_sym b).
 rewrite <- Q_distr_left.
 rewrite Qmult_sym with (m := b). 
 rewrite Qmult_sym with (m := f). 
 rewrite <- Qdiv_num_denom; [ reflexivity | assumption ].
 transitivity (Qmult (Qmult (Qmult b e) p1) p2);
   [ ring | rewrite <- H1; ring ].
 replace (Qmult (Qmult g p2) b) with (Qmult (Qmult b g) p2) by ring;
   rewrite H2; ring.
 ring.
Qed.


Lemma a_field_equality_4 :
 forall a b c d e f g h q1 q2 : Q,
 g <> Zero ->
 Qmult a g = Qmult c e ->
 Qmult b g = Qmult c f ->
 Qmult c h = Qmult d g ->
 Qplus (Qplus (Qplus (Qmult (Qmult e q1) q2) (Qmult f q1)) (Qmult g q2)) h <>
 Zero ->
 Qmult c (Qinv g) =
 Qmult
   (Qplus (Qplus (Qplus (Qmult (Qmult a q1) q2) (Qmult b q1)) (Qmult c q2)) d)
   (Qinv
      (Qplus
         (Qplus (Qplus (Qmult (Qmult e q1) q2) (Qmult f q1)) (Qmult g q2)) h)).
Proof.
 intros a b c d e f g h p1 p2 He H4 H3 H2 Hdenom.
 symmetry  in |- *.
 rewrite Qdiv_num_denom with (p := g); [ idtac | assumption ].
 rewrite Q_distr_left. 
 rewrite <- H2.
 rewrite Q_distr_left with (z := g).
 rewrite Q_distr_left with (z := g).
 replace (Qmult (Qmult b p1) g) with (Qmult (Qmult f p1) c).
 replace (Qmult (Qmult c p2) g) with (Qmult (Qmult g p2) c).
 replace (Qmult (Qmult (Qmult a p1) p2) g) with
  (Qmult (Qmult (Qmult e p1) p2) c).
 rewrite (Qmult_sym c h).
 rewrite <- Q_distr_left with (z := c).
 rewrite <- Q_distr_left with (z := c).
 rewrite <- Q_distr_left.
 rewrite Qmult_sym with (m := c). 
 rewrite Qmult_sym with (m := g). 
 rewrite <- Qdiv_num_denom; [ reflexivity | assumption ].
 transitivity (Qmult (Qmult (Qmult c e) p1) p2);
   [ ring | rewrite <- H4; ring ].
 ring.
 replace (Qmult (Qmult f p1) c) with (Qmult (Qmult c f) p1) by ring;
   rewrite <- H3; ring.
Qed.


Lemma a_field_equality_5 :
 forall a b c d e f g h q1 q2 : Q,
 h <> Zero ->
 Qmult b h = Qmult d f ->
 Qmult a h = Qmult d e ->
 Qmult c h = Qmult d g ->
 Qplus (Qplus (Qplus (Qmult (Qmult e q1) q2) (Qmult f q1)) (Qmult g q2)) h <>
 Zero ->
 Qmult d (Qinv h) =
 Qmult
   (Qplus (Qplus (Qplus (Qmult (Qmult a q1) q2) (Qmult b q1)) (Qmult c q2)) d)
   (Qinv
      (Qplus
         (Qplus (Qplus (Qmult (Qmult e q1) q2) (Qmult f q1)) (Qmult g q2)) h)).
Proof.
 intros a b c d e f g h p1 p2 He H6 H5 H3 Hdenom.
 symmetry  in |- *.
 rewrite Qdiv_num_denom with (p := h); [ idtac | assumption ].
 rewrite Q_distr_left. 
 rewrite Q_distr_left with (z := h).
 rewrite Q_distr_left with (z := h).
 replace (Qmult (Qmult b p1) h) with (Qmult (Qmult f p1) d).
 replace (Qmult (Qmult c p2) h) with (Qmult (Qmult g p2) d).
 replace (Qmult (Qmult (Qmult a p1) p2) h) with
  (Qmult (Qmult (Qmult e p1) p2) d).
 rewrite (Qmult_sym d h).
 rewrite <- Q_distr_left with (z := d).
 rewrite <- Q_distr_left with (z := d).
 rewrite <- Q_distr_left.
 rewrite Qmult_sym with (m := d). 
 rewrite Qmult_sym with (m := h). 
 rewrite <- Qdiv_num_denom; [ reflexivity | assumption ].
 transitivity (Qmult (Qmult (Qmult d e) p1) p2);
   [ ring | rewrite <- H5; ring ].
 replace (Qmult (Qmult g p2) d) with (Qmult (Qmult d g) p2) by ring;
   rewrite <- H3; ring.
 replace (Qmult (Qmult f p1) d) with (Qmult (Qmult d f) p1) by ring;
   rewrite <- H6; ring.
Qed.


Lemma quadratic_positive_input :
 forall (a b c d e f g h : Z) (p1 p2 : Qpositive)
   (H_Qquadratic_sg_denom_nonzero : Qquadratic_sg_denom_nonzero e f g h p1 p2),
 Qquadratic_Qpositive_to_Q a b c d e f g h p1 p2
   H_Qquadratic_sg_denom_nonzero =
 Qmult
   (Qplus
      (Qplus
         (Qplus (Qmult (Qmult a (Qpos p1)) (Qpos p2)) (Qmult b (Qpos p1)))
         (Qmult c (Qpos p2))) d)
   (Qinv
      (Qplus
         (Qplus
            (Qplus (Qmult (Qmult e (Qpos p1)) (Qpos p2)) (Qmult f (Qpos p1)))
            (Qmult g (Qpos p2))) h)).
Proof.
 intros a b c d e f g h p1 p2 H_Qquadratic_sg_denom_nonzero.
  functional induction
   (Qquadratic_Qpositive_to_Q a b c d e f g h p1 p2
                            H_Qquadratic_sg_denom_nonzero); Clear_eq_.
 (* 1 *)
 rewrite coding_Q.
 unfold spec_fraction_encoding in |- *.
 generalize _x; intros (H1, (H2, (H3, (H4, (H5, H6)))));
  repeat
   match goal with
   | id1:(_ = _ :>Z) |- _ =>
       generalize (f_equal Z_to_Q id1); clear id1; intro id1;
        do 2 rewrite Z_to_Qmult in id1
   end.
 apply a_field_equality_2;
  [ replace Zero with (Z_to_Q 0); trivial; apply Z_to_Q_not_eq; assumption
  | assumption
  | assumption
  | assumption
  | apply Qquadratic_sg_denom_nonzero_correct_1; assumption ].
 (* 2 *)
 rewrite coding_Q.
 unfold spec_fraction_encoding in |- *.
 generalize _x; intros (H1, (H2, (H3, (H4, (H5, H6)))));
  repeat
   match goal with
   | id1:(_ = _ :>Z) |- _ =>
       generalize (f_equal Z_to_Q id1); clear id1; intro id1;
        do 2 rewrite Z_to_Qmult in id1
   end.
 apply a_field_equality_3;
  [ replace Zero with (Z_to_Q 0); trivial; apply Z_to_Q_not_eq; assumption
  | assumption
  | assumption
  | assumption
  | apply Qquadratic_sg_denom_nonzero_correct_1; assumption ].
 (* 3 *)
 rewrite coding_Q.
 unfold spec_fraction_encoding in |- *.
 generalize _x; intros (H1, (H2, (H3, (H4, (H5, H6)))));
  repeat
   match goal with
   | id1:(_ = _ :>Z) |- _ =>
       generalize (f_equal Z_to_Q id1); clear id1; intro id1;
        do 2 rewrite Z_to_Qmult in id1
   end.
 apply a_field_equality_4;
  [ replace Zero with (Z_to_Q 0); trivial; apply Z_to_Q_not_eq; assumption
  | assumption
  | assumption
  | assumption
  | apply Qquadratic_sg_denom_nonzero_correct_1; assumption ].
 (* 4 *)
 rewrite coding_Q.
 unfold spec_fraction_encoding in |- *.
 generalize _x; intros (H1, (H2, (H3, (H4, (H5, H6)))));
  repeat
   match goal with
   | id1:(_ = _ :>Z) |- _ =>
       generalize (f_equal Z_to_Q id1); clear id1; intro id1;
        do 2 rewrite Z_to_Qmult in id1
   end.
 apply a_field_equality_5;
  [ replace Zero with (Z_to_Q 0); trivial; apply Z_to_Q_not_eq; assumption
  | assumption
  | assumption
  | assumption
  | apply Qquadratic_sg_denom_nonzero_correct_1; assumption ].
 (* 5 *)
 transitivity (spec_Qquadratic_Qpositive_to_Q a b c d e f g h p1 p2);
  trivial; symmetry  in |- *; apply Qsgn_2;
  rewrite <-
   (quadratic_sign a b c d e f g h p1 p2 H_Qquadratic_sg_denom_nonzero)
   ; assumption.
 (* 6 *)
 Absurd_q_sign_.
 (* 7 *)
 rewrite quadratic_output_bit;
  rewrite <-
   spec_Qquadratic_Qpositive_to_Q_spec_Qquadratic_Qpositive_to_Qpositive2_pos
   ; unfold spec_Qquadratic_Qpositive_to_Q in |- *;
  rewrite Qquadratic_sign_pres_fraction;
  [ reflexivity
  | change
      (Qsgn (spec_Qquadratic_Qpositive_to_Q a b c d e f g h p1 p2) = 1%Z)
     in |- *;
     rewrite <-
      (quadratic_sign a b c d e f g h p1 p2 H_Qquadratic_sg_denom_nonzero)
      ; assumption ].
 (* 8 *)
 rewrite quadratic_output_bit;
  rewrite <-
   spec_Qquadratic_Qpositive_to_Q_spec_Qquadratic_Qpositive_to_Qpositive2_pos
   ; rewrite spec_Qquadratic_Qpositive_to_Q_Zopp;
  unfold spec_Qquadratic_Qpositive_to_Q in |- *;
  rewrite Qquadratic_sign_pres_fraction;
  [ reflexivity
  | change
      (Qsgn (spec_Qquadratic_Qpositive_to_Q a b c d e f g h p1 p2) = 1%Z)
     in |- *;
     rewrite <-
      (quadratic_sign a b c d e f g h p1 p2 H_Qquadratic_sg_denom_nonzero)
      ; assumption ].
 (* 9 *)
 Absurd_q_sign_.
 (* 10 *)
 rewrite quadratic_output_bit;
  rewrite <-
   spec_Qquadratic_Qpositive_to_Q_spec_Qquadratic_Qpositive_to_Qpositive2_neg_2
   ; unfold spec_Qquadratic_Qpositive_to_Q in |- *;
  rewrite Qquadratic_sign_pres_fraction;
  [ reflexivity
  | change
      (Qsgn (spec_Qquadratic_Qpositive_to_Q a b c d e f g h p1 p2) = (-1)%Z)
     in |- *;
     rewrite <-
      (quadratic_sign a b c d e f g h p1 p2 H_Qquadratic_sg_denom_nonzero)
      ; assumption ].
 (* 11 *)
 rewrite quadratic_output_bit;
  rewrite <-
   spec_Qquadratic_Qpositive_to_Q_spec_Qquadratic_Qpositive_to_Qpositive2_neg_1
   ; unfold spec_Qquadratic_Qpositive_to_Q in |- *;
  rewrite Qquadratic_sign_pres_fraction;
  [ reflexivity
  | change
      (Qsgn (spec_Qquadratic_Qpositive_to_Q a b c d e f g h p1 p2) = (-1)%Z)
     in |- *;
     rewrite <-
      (quadratic_sign a b c d e f g h p1 p2 H_Qquadratic_sg_denom_nonzero)
      ; assumption ].
Qed.


Lemma quadratic :
 forall (a b c d e f g h : Z) (s1 s2 : Q)
   (H_Qquadratic_denom_nonzero : Qquadratic_denom_nonzero e f g h s1 s2),
 Qquadratic a b c d e f g h s1 s2 H_Qquadratic_denom_nonzero =
 spec_q a b c d e f g h s1 s2.
Proof.
 intros a b c d e f g h [| p1| p1] [| p2| p2] H_Qhomographic_denom_nonzero.
 (* (1) Zero_Zero*)
 unfold Qquadratic in |- *.
 rewrite homography.
 unfold spec_q, spec_h in |- *.
 repeat rewrite Qmult_zero_right.
 repeat rewrite Qplus_zero_left.
 reflexivity.
 (* (2) Zero_Qpos*)
 unfold Qquadratic in |- *.
 rewrite homography.
 unfold spec_q, spec_h in |- *.
 repeat rewrite Qmult_zero_right.
 repeat rewrite Qplus_zero_left.
 reflexivity.
 (* (3) Zero_Qneg*)
 unfold Qquadratic in |- *.
 rewrite homography.
 unfold spec_q, spec_h in |- *.
 repeat rewrite Qmult_zero_right.
 repeat rewrite Qplus_zero_left.
 reflexivity.
 (* (4) Qpos_Zero*)
 unfold Qquadratic in |- *.
 rewrite homography.
 unfold spec_q, spec_h in |- *.
 repeat rewrite Qmult_zero_right.
 repeat rewrite Qplus_zero_right.
 repeat rewrite Qplus_zero_left.
 reflexivity.
 (* (5) Qpos_Qpos *)
 unfold Qquadratic in |- *.
 unfold spec_q in |- *.
 apply quadratic_positive_input.
 (* (6) Qpos_Qneg *)
 unfold Qquadratic in |- *.
 unfold spec_q in |- *.
 rewrite quadratic_positive_input.
 apply f_equal2 with Q Q; [ idtac | apply f_equal with Q ];
  apply f_equal2 with Q Q; trivial; repeat rewrite Z_to_Qopp;
  repeat rewrite <- Qmult_neg; abstract ring.
 (* (7) Qneg_Zero*)
 unfold Qquadratic in |- *.
 rewrite homography.
 unfold spec_q, spec_h in |- *.
 repeat rewrite Qmult_zero_right.
 repeat rewrite Qplus_zero_right.
 repeat rewrite Qplus_zero_left.
 reflexivity.
 (* (8) Qneg_Qneg *)
 unfold Qquadratic in |- *.
 unfold spec_q in |- *.
 rewrite quadratic_positive_input.
 apply f_equal2 with Q Q; [ idtac | apply f_equal with Q ];
  apply f_equal2 with Q Q; trivial; repeat rewrite Z_to_Qopp;
  repeat rewrite <- Qmult_neg; abstract ring.
 (* (9) Qneg_Qpos *)
 unfold Qquadratic in |- *.
 unfold spec_q in |- *.
 rewrite quadratic_positive_input.
 apply f_equal2 with Q Q; [ idtac | apply f_equal with Q ];
  apply f_equal2 with Q Q; trivial; repeat rewrite Z_to_Qopp;
  repeat rewrite <- Qmult_neg; abstract ring.
Qed.



Lemma Qquadratic_denom_nonzero_correct_1 :
 forall (e f g h : Z) (q1 q2 : Q),
 Qquadratic_denom_nonzero e f g h q1 q2 ->
 Qplus (Qplus (Qplus (Qmult (Qmult e q1) q2) (Qmult f q1)) (Qmult g q2)) h <>
 Zero.
Proof. 
 intros e f g h q1 q2 H_Qquadratic_denom_nonzero;
  induction H_Qquadratic_denom_nonzero.
 (* 1 *)
 rewrite H.
 rewrite H0.
 repeat rewrite Qmult_zero_right.
 repeat rewrite Qplus_zero_left.
 change (Z_to_Q h <> Z_to_Q 0) in |- *.
 apply Z_to_Q_not_eq; assumption.
 (* 2 *)
 rewrite H.
 repeat rewrite Qmult_zero_right.
 repeat rewrite Qplus_zero_left.
 rewrite H0.
 apply Qhomographic_sg_denom_nonzero_correct_1; assumption.
 (* 3 *)
 rewrite H.
 repeat rewrite Qmult_zero_right.
 repeat rewrite Qplus_zero_left.
 rewrite H0.
 rewrite Qopp_Qpos.
 generalize (Qhomographic_sg_denom_nonzero_correct_1 _ _ _ H1).
 intros H' H2; apply H'.
 rewrite <- H2.
 rewrite Z_to_Qopp.
 abstract ring.
 (* 4 *)
 rewrite H.
 rewrite H0.
 repeat rewrite Qmult_zero_right.
 rewrite Qplus_zero_left.
 rewrite Qplus_zero_right.
 apply Qhomographic_sg_denom_nonzero_correct_1; assumption.
 (* 5 *)
 rewrite H.
 rewrite H0.
 repeat rewrite Qmult_zero_right.
 rewrite Qplus_zero_left.
 rewrite Qplus_zero_right.
 rewrite Qopp_Qpos.
 generalize (Qhomographic_sg_denom_nonzero_correct_1 _ _ _ H1).
 intros H' H2; apply H'.
 rewrite <- H2.
 rewrite Z_to_Qopp.
 abstract ring.
 (* 6 *)
 rewrite H.
 rewrite H0.
 apply Qquadratic_sg_denom_nonzero_correct_1; assumption.
 (* 7 *)
 rewrite H.
 rewrite H0.
 generalize (Qquadratic_sg_denom_nonzero_correct_1 _ _ _ _ _ _ H1).
 intros H' H2; apply H'.
 rewrite <- H2.
 repeat rewrite Z_to_Qopp.
 repeat rewrite Qopp_Qpos.
 abstract ring.
 (* 8 *)
 rewrite H.
 rewrite H0.
 generalize (Qquadratic_sg_denom_nonzero_correct_1 _ _ _ _ _ _ H1).
 intros H' H2; apply H'.
 rewrite <- H2.
 repeat rewrite Z_to_Qopp.
 repeat rewrite Qopp_Qpos.
 abstract ring.
 (* 9 *)
 rewrite H.
 rewrite H0.
 generalize (Qquadratic_sg_denom_nonzero_correct_1 _ _ _ _ _ _ H1).
 intros H' H2; apply H'.
 rewrite <- H2.
 repeat rewrite Z_to_Qopp.
 repeat rewrite Qopp_Qpos.
 abstract ring.
Qed. 

Lemma Qquadratic_denom_nonzero_correct_2 :
 forall (e f g h : Z) (q1 q2 : Q),
 Qplus (Qplus (Qplus (Qmult (Qmult e q1) q2) (Qmult f q1)) (Qmult g q2)) h <>
 Zero -> Qquadratic_denom_nonzero e f g h q1 q2.
Proof. 
 intros e f g h [| p1| p1] [| p2| p2] H_denom.
 (* 1 *)
 apply Qquadraticok00; trivial.
 intro H.
 apply H_denom.
 rewrite H.
 simpl in |- *.
 abstract ring.
 (* 2 *)
 apply Qquadraticok01 with p2; trivial.
 apply Qhomographic_sg_denom_nonzero_correct_2.
 intro H.
 apply H_denom.
 repeat rewrite Qmult_zero_right.
 rewrite Qmult_zero.
 repeat rewrite Qplus_zero_left.
 assumption.
 (* 3 *)
 apply Qquadraticok02 with p2; trivial.
 apply Qhomographic_sg_denom_nonzero_correct_2.
 intro H.
 apply H_denom.
 repeat rewrite Qmult_zero_right.
 rewrite Qmult_zero.
 repeat rewrite Qplus_zero_left.
 rewrite <- Qmult_neg in H.
 rewrite Z_to_Qopp in H.
 rewrite Qmult_Qopp_left in H.
 rewrite <- H.
 abstract ring.
 (* 4 *)
 apply Qquadraticok10 with p1; trivial.
 apply Qhomographic_sg_denom_nonzero_correct_2.
 intro H.
 apply H_denom.
 repeat rewrite Qmult_zero_right.
 repeat rewrite Qplus_zero_left.
 repeat rewrite Qplus_zero_right.
 assumption.
 (* 5 *)
 apply Qquadraticok11 with p1 p2; trivial.
 apply Qquadratic_sg_denom_nonzero_correct_2.
 assumption.
 (* 6 *)
 apply Qquadraticok12 with p1 p2; trivial.
 apply Qquadratic_sg_denom_nonzero_correct_2.
 repeat rewrite Z_to_Qopp.
 repeat rewrite <- Qmult_neg.
 intro H.
 apply H_denom.
 repeat rewrite <- Qmult_neg.
 rewrite <- H.
 abstract ring.
 (* 7 *)
 apply Qquadraticok20 with p1; trivial.
 apply Qhomographic_sg_denom_nonzero_correct_2.
 intro H.
 apply H_denom.
 repeat rewrite Qmult_zero_right.
 rewrite Qplus_zero_left.
 rewrite Qplus_zero_right.
 rewrite <- Qmult_neg in H.
 rewrite Z_to_Qopp in H.
 rewrite <- H.
 abstract ring.
 (* 8 *)
 apply Qquadraticok21 with p1 p2; trivial.
 apply Qquadratic_sg_denom_nonzero_correct_2.
 repeat rewrite Z_to_Qopp.
 repeat rewrite <- Qmult_neg.
 intro H.
 apply H_denom.
 repeat rewrite <- Qmult_neg.
 rewrite <- H.
 abstract ring.
 (* 9 *)
 apply Qquadraticok22 with p1 p2; trivial.
 apply Qquadratic_sg_denom_nonzero_correct_2.
 repeat rewrite Z_to_Qopp.
 repeat rewrite <- Qmult_neg.
 intro H.
 apply H_denom.
 repeat rewrite <- Qmult_neg.
 rewrite <- H.
 abstract ring.
Qed. 

 
Theorem quadratic_algorithm_is_correct :
 forall (a b c d e f g h : Z) (q1 q2 : Q)
   (H_denom : Qplus
                (Qplus (Qplus (Qmult (Qmult e q1) q2) (Qmult f q1))
                   (Qmult g q2)) h <> Zero),
 Qquadratic a b c d e f g h q1 q2
   (Qquadratic_denom_nonzero_correct_2 e f g h q1 q2 H_denom) =
 Qmult
   (Qplus (Qplus (Qplus (Qmult (Qmult a q1) q2) (Qmult b q1)) (Qmult c q2)) d)
   (Qinv
      (Qplus
         (Qplus (Qplus (Qmult (Qmult e q1) q2) (Qmult f q1)) (Qmult g q2)) h)).
Proof.
 intros a b c d e f g h q1 q2 H_denom;
  apply
   (quadratic a b c d e f g h q1 q2
      (Qquadratic_denom_nonzero_correct_2 e f g h q1 q2 H_denom)).
Qed.
