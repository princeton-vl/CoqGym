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
Require Export Qquadratic.
Require Import homographic_correctness.

Lemma fraction_encoding_reduces :
 forall (a b m n : Z) (Hb : b <> 0%Z) (Hn : n <> 0%Z),
 (a * n)%Z = (m * b)%Z -> fraction_encoding a b Hb = fraction_encoding m n Hn.
Proof.
 intros a b m n Hb Hn H.
 do 2 rewrite coding_Q.
 unfold spec_fraction_encoding in |- *.
 rewrite (Qdiv_num_denom a b n).
 rewrite <- Z_to_Qmult.
 rewrite H.
 rewrite Z_to_Qmult.
 rewrite (Qmult_sym b n).
 rewrite <- Qdiv_num_denom.
 reflexivity.
 replace Zero with (Z_to_Q 0); trivial; apply Z_to_Q_not_eq; assumption.
 replace Zero with (Z_to_Q 0); trivial; apply Z_to_Q_not_eq; assumption.
Qed.

Functional Scheme Qquadratic_Qpositive_to_Q_ind := 
  Induction for Qquadratic_Qpositive_to_Q Sort Prop.

Lemma Qquadratic_Qpositive_to_Q_0 :
 forall (a b c d e f g h : Z) (p1 p2 : Qpositive)
   (H_Qquadratic_sg_denom_nonzero : Qquadratic_sg_denom_nonzero e f g h p1 p2)
   (Hh : h <> 0%Z),
 same_ratio a b c d e f g h ->
 Qquadratic_Qpositive_to_Q a b c d e f g h p1 p2
   H_Qquadratic_sg_denom_nonzero = fraction_encoding d h Hh. 
Proof.
 intros a b c d e f g h p1 p2 H_Qquadratic_sg_denom_nonzero.
 functional induction
   (Qquadratic_Qpositive_to_Q a b c d e f g h p1 p2
                                     H_Qquadratic_sg_denom_nonzero); 
            intros; try solve [ Falsum ];
	      match goal with 
		[ id:same_ratio _ _ _ _ _ _ _ _ |- _]  => 
		  elim id; intros h1 (h2, (h3, (h4, (h5, h6))));
		    apply fraction_encoding_reduces; trivial
	      end.
Qed.


Lemma Qquadratic_Qpositive_to_Q_1 :
 forall (a b c d e f g h : Z) (p1 p2 : Qpositive)
   (H_Qquadratic_sg_denom_nonzero : Qquadratic_sg_denom_nonzero e f g h p1 p2)
   (Hg : g <> 0%Z),
 same_ratio a b c d e f g h ->
 Qquadratic_Qpositive_to_Q a b c d e f g h p1 p2
   H_Qquadratic_sg_denom_nonzero = fraction_encoding c g Hg. 
Proof.
 intros a b c d e f g h p1 p2 H_Qquadratic_sg_denom_nonzero.
 functional induction
   (Qquadratic_Qpositive_to_Q a b c d e f g h p1 p2
                                     H_Qquadratic_sg_denom_nonzero); 
            intros; try solve [ Falsum ];
	      match goal with 
		[ id:same_ratio _ _ _ _ _ _ _ _ |- _]  => 
		  elim id; intros h1 (h2, (h3, (h4, (h5, h6))));
		    apply fraction_encoding_reduces; trivial; 
		      symmetry  in |- *; assumption
	      end.
Qed.

Lemma Qquadratic_Qpositive_to_Q_2 :
 forall (a b c d e f g h : Z) (p1 p2 : Qpositive)
   (H_Qquadratic_sg_denom_nonzero : Qquadratic_sg_denom_nonzero e f g h p1 p2)
   (Hf : f <> 0%Z),
 same_ratio a b c d e f g h ->
 Qquadratic_Qpositive_to_Q a b c d e f g h p1 p2
   H_Qquadratic_sg_denom_nonzero = fraction_encoding b f Hf. 
Proof.
 intros a b c d e f g h p1 p2 H_Qquadratic_sg_denom_nonzero.
 functional induction
   (Qquadratic_Qpositive_to_Q a b c d e f g h p1 p2
     H_Qquadratic_sg_denom_nonzero); 
   intros; try solve [ Falsum ];
     match goal with 
       [ id:same_ratio _ _ _ _ _ _ _ _ |- _]  => 
       elim id; intros h1 (h2, (h3, (h4, (h5, h6))));
	 apply fraction_encoding_reduces; trivial; 
           symmetry  in |- *; assumption
     end.
Qed.


Lemma Qquadratic_Qpositive_to_Q_3 :
 forall (a b c d e f g h : Z) (p1 p2 : Qpositive)
   (H_Qquadratic_sg_denom_nonzero : Qquadratic_sg_denom_nonzero e f g h p1 p2)
   (He : e <> 0%Z),
 same_ratio a b c d e f g h ->
 Qquadratic_Qpositive_to_Q a b c d e f g h p1 p2
   H_Qquadratic_sg_denom_nonzero = fraction_encoding a e He. 
Proof.
 intros a b c d e f g h p1 p2 H_Qquadratic_sg_denom_nonzero.
  functional induction
    (Qquadratic_Qpositive_to_Q a b c d e f g h p1 p2
      H_Qquadratic_sg_denom_nonzero); 
    intros; try solve [ Falsum ];
      match goal with 
	[ id:same_ratio _ _ _ _ _ _ _ _ |- _]  => 
	elim id; intros h1 (h2, (h3, (h4, (h5, h6))));
          apply fraction_encoding_reduces; trivial; 
            symmetry  in |- *; assumption
      end.
Qed.

Ltac QSign_mismatch_ :=
  apply False_ind;
   match goal with
   | id1:(?X1 = 1%Z),id2:(?X1 = 0%Z) |- _ =>
       rewrite id2 in id1; discriminate id1
   | id1:(?X1 = (-1)%Z),id2:(?X1 = 0%Z) |- _ =>
       rewrite id2 in id1; discriminate id1
   | id1:(?X1 = 1%Z),id2:(?X1 = (-1)%Z) |- _ =>
       rewrite id2 in id1; discriminate id1

   | id2:(?X1 = 0%Z),id1:(?X1 = 1%Z) |- _ =>
       rewrite id2 in id1; discriminate id1
   | id1:(?X1 = 0%Z),id2:(?X1 = (-1)%Z) |- _ =>
       rewrite id2 in id1; discriminate id1
   | id1:(?X1 = (-1)%Z),id2:(?X1 = 1%Z) |- _ =>
       rewrite id2 in id1; discriminate id1

   end.

(* The tactique Absurd_q_sign_ solves the goal by contradiction if in the context we have:

(C1)  id1:(q_sign a b c d e f g h p1 p2 H)=1
     id2:(Z.sgn new_a+new_b+new_c+new_d)=0 
     ----------------------------------
   
or 

(C2)  id1:(q_sign a b c d e f g h p1 p2 H)=1
     id2:(Z.sgn new_e+new_f+new_g+new_h)=0 
     ----------------------------------

or

(C3)  id1:(q_sign a b c d e f g h p1 p2 H)=-1
     id2:(Z.sgn new_a+new_b+new_c+new_d)=0 
     ----------------------------------
   
or 

(C4)  id1:(q_sign a b c d e f g h p1 p2 H)=-1
     id2:(Z.sgn new_e+new_f+new_g+new_h)=0 
     ----------------------------------
   
otherwise if in the context we have 

(C5)  id1:(q_sign a b c d e f g h p1 p2 H)=0
     id2:(Z.sgn ?)=0 
     ----------------------------------

it calls the QSign_mismatch_ tactic.

and otherwise it fails.

In the next files we used this tactic 4 times and all of them are instances of case (C1) or (C3) above.
*)

Ltac Absurd_q_sign_ :=
  match goal with
  | id1:(q_sign ?X1 ?X2 ?X3 ?X4 ?X5 ?X6 ?X7 ?X8 ?X9 ?X10 ?X11 = ?X0),id2:
  (Z.sgn _ = 0%Z) |- _ =>
      match constr:(X0) with
      | 0%Z => QSign_mismatch_
      end ||
        (apply False_ind;
          assert
           (HH :
            Qquadratic_sign X1 X2 X3 X4 X5 X6 X7 X8 X9 X10 X11 =
            (X0,
            (qnew_a X1 X2 X3 X4 X5 X6 X7 X8 X9 X10 X11,
            (qnew_b X1 X2 X3 X4 X5 X6 X7 X8 X9 X10 X11,
            (qnew_c X1 X2 X3 X4 X5 X6 X7 X8 X9 X10 X11,
            qnew_d X1 X2 X3 X4 X5 X6 X7 X8 X9 X10 X11)),
            (qnew_e X1 X2 X3 X4 X5 X6 X7 X8 X9 X10 X11,
            (qnew_f X1 X2 X3 X4 X5 X6 X7 X8 X9 X10 X11,
            (qnew_g X1 X2 X3 X4 X5 X6 X7 X8 X9 X10 X11,
            qnew_h X1 X2 X3 X4 X5 X6 X7 X8 X9 X10 X11))),
            (qnew_p1 X1 X2 X3 X4 X5 X6 X7 X8 X9 X10 X11,
            qnew_p2 X1 X2 X3 X4 X5 X6 X7 X8 X9 X10 X11))));
          [ rewrite <- id1;
             unfold qnew_a, qnew_b, qnew_c, qnew_d, qnew_e, qnew_f, qnew_g,
              qnew_h, qnew_p1, qnew_p2 in |- *;
             replace (q_sign X1 X2 X3 X4 X5 X6 X7 X8 X9 X10 X11) with
              (fst (Qquadratic_sign X1 X2 X3 X4 X5 X6 X7 X8 X9 X10 X11));
             [ idtac | reflexivity ]; repeat rewrite <- pair_1; 
             reflexivity
          | idtac ];
          match constr:(X0) with
          | 1%Z =>
              generalize
               (Qquadratic_sign_pos_1 X1 X2 X3 X4 X5 X6 X7 X8 X9 X10 X11
                  (qnew_a X1 X2 X3 X4 X5 X6 X7 X8 X9 X10 X11)
                  (qnew_b X1 X2 X3 X4 X5 X6 X7 X8 X9 X10 X11)
                  (qnew_c X1 X2 X3 X4 X5 X6 X7 X8 X9 X10 X11)
                  (qnew_d X1 X2 X3 X4 X5 X6 X7 X8 X9 X10 X11)
                  (qnew_e X1 X2 X3 X4 X5 X6 X7 X8 X9 X10 X11)
                  (qnew_f X1 X2 X3 X4 X5 X6 X7 X8 X9 X10 X11)
                  (qnew_g X1 X2 X3 X4 X5 X6 X7 X8 X9 X10 X11)
                  (qnew_h X1 X2 X3 X4 X5 X6 X7 X8 X9 X10 X11)
                  (qnew_p1 X1 X2 X3 X4 X5 X6 X7 X8 X9 X10 X11)
                  (qnew_p2 X1 X2 X3 X4 X5 X6 X7 X8 X9 X10 X11) HH)
          | (-1)%Z =>
              generalize
               (Qquadratic_sign_neg_1 X1 X2 X3 X4 X5 X6 X7 X8 X9 X10 X11
                  (qnew_a X1 X2 X3 X4 X5 X6 X7 X8 X9 X10 X11)
                  (qnew_b X1 X2 X3 X4 X5 X6 X7 X8 X9 X10 X11)
                  (qnew_c X1 X2 X3 X4 X5 X6 X7 X8 X9 X10 X11)
                  (qnew_d X1 X2 X3 X4 X5 X6 X7 X8 X9 X10 X11)
                  (qnew_e X1 X2 X3 X4 X5 X6 X7 X8 X9 X10 X11)
                  (qnew_f X1 X2 X3 X4 X5 X6 X7 X8 X9 X10 X11)
                  (qnew_g X1 X2 X3 X4 X5 X6 X7 X8 X9 X10 X11)
                  (qnew_h X1 X2 X3 X4 X5 X6 X7 X8 X9 X10 X11)
                  (qnew_p1 X1 X2 X3 X4 X5 X6 X7 X8 X9 X10 X11)
                  (qnew_p2 X1 X2 X3 X4 X5 X6 X7 X8 X9 X10 X11) HH)
          end; intros [(na_nb_nc_nd_pos, _)| (na_nb_nc_nd_neg, _)];
          generalize (Zsgn_2 _ id2); [ apply sym_not_eq | idtac ];
          apply Zorder.Zlt_not_eq; assumption)
  end.


Lemma Qquadratic_Qpositive_to_Q_4 :
 forall (a b c d e f g h : Z) (p1 p2 : Qpositive)
   (H_Qquadratic_sg_denom_nonzero : Qquadratic_sg_denom_nonzero e f g h p1 p2),
 ~ same_ratio a b c d e f g h ->
 q_sign a b c d e f g h p1 p2 H_Qquadratic_sg_denom_nonzero = 0%Z ->
 Qquadratic_Qpositive_to_Q a b c d e f g h p1 p2
   H_Qquadratic_sg_denom_nonzero = Zero. 
Proof.
 intros a b c d e f g h p1 p2 H_Qquadratic_sg_denom_nonzero.
 functional induction
             (Qquadratic_Qpositive_to_Q a b c d e f g h p1 p2
                                      H_Qquadratic_sg_denom_nonzero); 
            intros; try solve [ Falsum ]; trivial;Clear_eq_;
	      match goal with 
		[ id1 : q_sign ?a ?b ?c ?d ?e ?f ?g ?h ?p1 ?p2 ?H_Qquadratic_sg_denom_nonzero = _, 
		  id2 : q_sign ?a ?b ?c ?d ?e ?f ?g ?h ?p1 ?p2 ?H_Qquadratic_sg_denom_nonzero = _ |- _ ] => 
		rewrite id1 in id2;discriminate id2
	      end.
Qed.

Lemma Qquadratic_Qpositive_to_Q_5 :
 forall (a b c d e f g h : Z) (p1 p2 : Qpositive)
   (H_Qquadratic_sg_denom_nonzero : Qquadratic_sg_denom_nonzero e f g h p1 p2),
 ~ same_ratio a b c d e f g h ->
 q_sign a b c d e f g h p1 p2 H_Qquadratic_sg_denom_nonzero = 1%Z ->
 Z.sgn
   (qnew_a a b c d e f g h p1 p2 H_Qquadratic_sg_denom_nonzero +
    qnew_b a b c d e f g h p1 p2 H_Qquadratic_sg_denom_nonzero +
    qnew_c a b c d e f g h p1 p2 H_Qquadratic_sg_denom_nonzero +
    qnew_d a b c d e f g h p1 p2 H_Qquadratic_sg_denom_nonzero) = 1%Z ->
 forall
   hyp_quadraticAcc : quadraticAcc
                        (qnew_a a b c d e f g h p1 p2
                           H_Qquadratic_sg_denom_nonzero)
                        (qnew_b a b c d e f g h p1 p2
                           H_Qquadratic_sg_denom_nonzero)
                        (qnew_c a b c d e f g h p1 p2
                           H_Qquadratic_sg_denom_nonzero)
                        (qnew_d a b c d e f g h p1 p2
                           H_Qquadratic_sg_denom_nonzero)
                        (qnew_e a b c d e f g h p1 p2
                           H_Qquadratic_sg_denom_nonzero)
                        (qnew_f a b c d e f g h p1 p2
                           H_Qquadratic_sg_denom_nonzero)
                        (qnew_g a b c d e f g h p1 p2
                           H_Qquadratic_sg_denom_nonzero)
                        (qnew_h a b c d e f g h p1 p2
                           H_Qquadratic_sg_denom_nonzero)
                        (qnew_p1 a b c d e f g h p1 p2
                           H_Qquadratic_sg_denom_nonzero)
                        (qnew_p2 a b c d e f g h p1 p2
                           H_Qquadratic_sg_denom_nonzero),
 Qquadratic_Qpositive_to_Q a b c d e f g h p1 p2
   H_Qquadratic_sg_denom_nonzero =
 Qpos
   (Qquadratic_Qpositive_to_Qpositive
      (qnew_a a b c d e f g h p1 p2 H_Qquadratic_sg_denom_nonzero)
      (qnew_b a b c d e f g h p1 p2 H_Qquadratic_sg_denom_nonzero)
      (qnew_c a b c d e f g h p1 p2 H_Qquadratic_sg_denom_nonzero)
      (qnew_d a b c d e f g h p1 p2 H_Qquadratic_sg_denom_nonzero)
      (qnew_e a b c d e f g h p1 p2 H_Qquadratic_sg_denom_nonzero)
      (qnew_f a b c d e f g h p1 p2 H_Qquadratic_sg_denom_nonzero)
      (qnew_g a b c d e f g h p1 p2 H_Qquadratic_sg_denom_nonzero)
      (qnew_h a b c d e f g h p1 p2 H_Qquadratic_sg_denom_nonzero)
      (qnew_p1 a b c d e f g h p1 p2 H_Qquadratic_sg_denom_nonzero)
      (qnew_p2 a b c d e f g h p1 p2 H_Qquadratic_sg_denom_nonzero)
      hyp_quadraticAcc).
Proof.
 intros a b c d e f g h p1 p2 H_Qquadratic_sg_denom_nonzero.
 functional induction
   (Qquadratic_Qpositive_to_Q a b c d e f g h p1 p2
     H_Qquadratic_sg_denom_nonzero); 
   intros; try solve [ Falsum ]; trivial; Clear_eq_;
     QSign_mismatch_ || apply f_equal with Qpositive;
       apply Qquadratic_Qpositive_to_Qpositive_equal.
Qed.

Lemma Qquadratic_Qpositive_to_Q_6 :
 forall (a b c d e f g h : Z) (p1 p2 : Qpositive)
   (H_Qquadratic_sg_denom_nonzero : Qquadratic_sg_denom_nonzero e f g h p1 p2),
 ~ same_ratio a b c d e f g h ->
 q_sign a b c d e f g h p1 p2 H_Qquadratic_sg_denom_nonzero = 1%Z ->
 Z.sgn
   (qnew_a a b c d e f g h p1 p2 H_Qquadratic_sg_denom_nonzero +
    qnew_b a b c d e f g h p1 p2 H_Qquadratic_sg_denom_nonzero +
    qnew_c a b c d e f g h p1 p2 H_Qquadratic_sg_denom_nonzero +
    qnew_d a b c d e f g h p1 p2 H_Qquadratic_sg_denom_nonzero) = 
 (-1)%Z ->
 forall
   hyp_quadraticAcc : quadraticAcc
                        (-
                         qnew_a a b c d e f g h p1 p2
                           H_Qquadratic_sg_denom_nonzero)
                        (-
                         qnew_b a b c d e f g h p1 p2
                           H_Qquadratic_sg_denom_nonzero)
                        (-
                         qnew_c a b c d e f g h p1 p2
                           H_Qquadratic_sg_denom_nonzero)
                        (-
                         qnew_d a b c d e f g h p1 p2
                           H_Qquadratic_sg_denom_nonzero)
                        (-
                         qnew_e a b c d e f g h p1 p2
                           H_Qquadratic_sg_denom_nonzero)
                        (-
                         qnew_f a b c d e f g h p1 p2
                           H_Qquadratic_sg_denom_nonzero)
                        (-
                         qnew_g a b c d e f g h p1 p2
                           H_Qquadratic_sg_denom_nonzero)
                        (-
                         qnew_h a b c d e f g h p1 p2
                           H_Qquadratic_sg_denom_nonzero)
                        (qnew_p1 a b c d e f g h p1 p2
                           H_Qquadratic_sg_denom_nonzero)
                        (qnew_p2 a b c d e f g h p1 p2
                           H_Qquadratic_sg_denom_nonzero),
 Qquadratic_Qpositive_to_Q a b c d e f g h p1 p2
   H_Qquadratic_sg_denom_nonzero =
 Qpos
   (Qquadratic_Qpositive_to_Qpositive
      (- qnew_a a b c d e f g h p1 p2 H_Qquadratic_sg_denom_nonzero)
      (- qnew_b a b c d e f g h p1 p2 H_Qquadratic_sg_denom_nonzero)
      (- qnew_c a b c d e f g h p1 p2 H_Qquadratic_sg_denom_nonzero)
      (- qnew_d a b c d e f g h p1 p2 H_Qquadratic_sg_denom_nonzero)
      (- qnew_e a b c d e f g h p1 p2 H_Qquadratic_sg_denom_nonzero)
      (- qnew_f a b c d e f g h p1 p2 H_Qquadratic_sg_denom_nonzero)
      (- qnew_g a b c d e f g h p1 p2 H_Qquadratic_sg_denom_nonzero)
      (- qnew_h a b c d e f g h p1 p2 H_Qquadratic_sg_denom_nonzero)
      (qnew_p1 a b c d e f g h p1 p2 H_Qquadratic_sg_denom_nonzero)
      (qnew_p2 a b c d e f g h p1 p2 H_Qquadratic_sg_denom_nonzero)
      hyp_quadraticAcc).
Proof.
 intros a b c d e f g h p1 p2 H_Qquadratic_sg_denom_nonzero.
 functional induction
   (Qquadratic_Qpositive_to_Q a b c d e f g h p1 p2
     H_Qquadratic_sg_denom_nonzero); 
            intros; try solve [ Falsum ]; trivial; Clear_eq_;
              QSign_mismatch_ || apply f_equal with Qpositive;
		apply Qquadratic_Qpositive_to_Qpositive_equal.
Qed.


Lemma Qquadratic_Qpositive_to_Q_7 :
 forall (a b c d e f g h : Z) (p1 p2 : Qpositive)
   (H_Qquadratic_sg_denom_nonzero : Qquadratic_sg_denom_nonzero e f g h p1 p2),
 ~ same_ratio a b c d e f g h ->
 q_sign a b c d e f g h p1 p2 H_Qquadratic_sg_denom_nonzero = (-1)%Z ->
 Z.sgn
   (qnew_a a b c d e f g h p1 p2 H_Qquadratic_sg_denom_nonzero +
    qnew_b a b c d e f g h p1 p2 H_Qquadratic_sg_denom_nonzero +
    qnew_c a b c d e f g h p1 p2 H_Qquadratic_sg_denom_nonzero +
    qnew_d a b c d e f g h p1 p2 H_Qquadratic_sg_denom_nonzero) = 1%Z ->
 forall
   hyp_quadraticAcc : quadraticAcc
                        (qnew_a a b c d e f g h p1 p2
                           H_Qquadratic_sg_denom_nonzero)
                        (qnew_b a b c d e f g h p1 p2
                           H_Qquadratic_sg_denom_nonzero)
                        (qnew_c a b c d e f g h p1 p2
                           H_Qquadratic_sg_denom_nonzero)
                        (qnew_d a b c d e f g h p1 p2
                           H_Qquadratic_sg_denom_nonzero)
                        (-
                         qnew_e a b c d e f g h p1 p2
                           H_Qquadratic_sg_denom_nonzero)
                        (-
                         qnew_f a b c d e f g h p1 p2
                           H_Qquadratic_sg_denom_nonzero)
                        (-
                         qnew_g a b c d e f g h p1 p2
                           H_Qquadratic_sg_denom_nonzero)
                        (-
                         qnew_h a b c d e f g h p1 p2
                           H_Qquadratic_sg_denom_nonzero)
                        (qnew_p1 a b c d e f g h p1 p2
                           H_Qquadratic_sg_denom_nonzero)
                        (qnew_p2 a b c d e f g h p1 p2
                           H_Qquadratic_sg_denom_nonzero),
 Qquadratic_Qpositive_to_Q a b c d e f g h p1 p2
   H_Qquadratic_sg_denom_nonzero =
 Qneg
   (Qquadratic_Qpositive_to_Qpositive
      (qnew_a a b c d e f g h p1 p2 H_Qquadratic_sg_denom_nonzero)
      (qnew_b a b c d e f g h p1 p2 H_Qquadratic_sg_denom_nonzero)
      (qnew_c a b c d e f g h p1 p2 H_Qquadratic_sg_denom_nonzero)
      (qnew_d a b c d e f g h p1 p2 H_Qquadratic_sg_denom_nonzero)
      (- qnew_e a b c d e f g h p1 p2 H_Qquadratic_sg_denom_nonzero)
      (- qnew_f a b c d e f g h p1 p2 H_Qquadratic_sg_denom_nonzero)
      (- qnew_g a b c d e f g h p1 p2 H_Qquadratic_sg_denom_nonzero)
      (- qnew_h a b c d e f g h p1 p2 H_Qquadratic_sg_denom_nonzero)
      (qnew_p1 a b c d e f g h p1 p2 H_Qquadratic_sg_denom_nonzero)
      (qnew_p2 a b c d e f g h p1 p2 H_Qquadratic_sg_denom_nonzero)
      hyp_quadraticAcc).
Proof.
 intros a b c d e f g h p1 p2 H_Qquadratic_sg_denom_nonzero.
 functional induction
   (Qquadratic_Qpositive_to_Q a b c d e f g h p1 p2
     H_Qquadratic_sg_denom_nonzero); 
   intros; try solve [ Falsum ]; trivial; Clear_eq_;
     QSign_mismatch_ || apply f_equal with Qpositive;
            apply Qquadratic_Qpositive_to_Qpositive_equal.
Qed.


Lemma Qquadratic_Qpositive_to_Q_8 :
 forall (a b c d e f g h : Z) (p1 p2 : Qpositive)
   (H_Qquadratic_sg_denom_nonzero : Qquadratic_sg_denom_nonzero e f g h p1 p2),
 ~ same_ratio a b c d e f g h ->
 q_sign a b c d e f g h p1 p2 H_Qquadratic_sg_denom_nonzero = (-1)%Z ->
 Z.sgn
   (qnew_a a b c d e f g h p1 p2 H_Qquadratic_sg_denom_nonzero +
    qnew_b a b c d e f g h p1 p2 H_Qquadratic_sg_denom_nonzero +
    qnew_c a b c d e f g h p1 p2 H_Qquadratic_sg_denom_nonzero +
    qnew_d a b c d e f g h p1 p2 H_Qquadratic_sg_denom_nonzero) = 
 (-1)%Z ->
 forall
   hyp_quadraticAcc : quadraticAcc
                        (-
                         qnew_a a b c d e f g h p1 p2
                           H_Qquadratic_sg_denom_nonzero)
                        (-
                         qnew_b a b c d e f g h p1 p2
                           H_Qquadratic_sg_denom_nonzero)
                        (-
                         qnew_c a b c d e f g h p1 p2
                           H_Qquadratic_sg_denom_nonzero)
                        (-
                         qnew_d a b c d e f g h p1 p2
                           H_Qquadratic_sg_denom_nonzero)
                        (qnew_e a b c d e f g h p1 p2
                           H_Qquadratic_sg_denom_nonzero)
                        (qnew_f a b c d e f g h p1 p2
                           H_Qquadratic_sg_denom_nonzero)
                        (qnew_g a b c d e f g h p1 p2
                           H_Qquadratic_sg_denom_nonzero)
                        (qnew_h a b c d e f g h p1 p2
                           H_Qquadratic_sg_denom_nonzero)
                        (qnew_p1 a b c d e f g h p1 p2
                           H_Qquadratic_sg_denom_nonzero)
                        (qnew_p2 a b c d e f g h p1 p2
                           H_Qquadratic_sg_denom_nonzero),
 Qquadratic_Qpositive_to_Q a b c d e f g h p1 p2
   H_Qquadratic_sg_denom_nonzero =
 Qneg
   (Qquadratic_Qpositive_to_Qpositive
      (- qnew_a a b c d e f g h p1 p2 H_Qquadratic_sg_denom_nonzero)
      (- qnew_b a b c d e f g h p1 p2 H_Qquadratic_sg_denom_nonzero)
      (- qnew_c a b c d e f g h p1 p2 H_Qquadratic_sg_denom_nonzero)
      (- qnew_d a b c d e f g h p1 p2 H_Qquadratic_sg_denom_nonzero)
      (qnew_e a b c d e f g h p1 p2 H_Qquadratic_sg_denom_nonzero)
      (qnew_f a b c d e f g h p1 p2 H_Qquadratic_sg_denom_nonzero)
      (qnew_g a b c d e f g h p1 p2 H_Qquadratic_sg_denom_nonzero)
      (qnew_h a b c d e f g h p1 p2 H_Qquadratic_sg_denom_nonzero)
      (qnew_p1 a b c d e f g h p1 p2 H_Qquadratic_sg_denom_nonzero)
      (qnew_p2 a b c d e f g h p1 p2 H_Qquadratic_sg_denom_nonzero)
      hyp_quadraticAcc).
Proof.
 intros a b c d e f g h p1 p2 H_Qquadratic_sg_denom_nonzero.
 functional induction
   (Qquadratic_Qpositive_to_Q a b c d e f g h p1 p2
     H_Qquadratic_sg_denom_nonzero); 
   intros; try solve [ Falsum ]; trivial; Clear_eq_;
     QSign_mismatch_ || apply f_equal with Qpositive;
       apply Qquadratic_Qpositive_to_Qpositive_equal.
Qed.


Lemma q_sign_equal :
 forall (a b c d e f g h : Z) (p1 p2 : Qpositive)
   (H_Qquadratic_sg_denom_nonzero1
    H_Qquadratic_sg_denom_nonzero2 : Qquadratic_sg_denom_nonzero e f g h p1
                                       p2),
 q_sign a b c d e f g h p1 p2 H_Qquadratic_sg_denom_nonzero1 =
 q_sign a b c d e f g h p1 p2 H_Qquadratic_sg_denom_nonzero2.
Proof.
 intros a b c d e f g h p1 p2 H_Qquadratic_sg_denom_nonzero1
            H_Qquadratic_sg_denom_nonzero2;
            change
              (fst
                 (Qquadratic_sign a b c d e f g h p1 p2
                    H_Qquadratic_sg_denom_nonzero1) =
               fst
                 (Qquadratic_sign a b c d e f g h p1 p2
                    H_Qquadratic_sg_denom_nonzero2)) 
             in |- *;
            apply
             f_equal
              with
                (Z *
                 (Z * (Z * (Z * Z)) * (Z * (Z * (Z * Z))) *
                  (Qpositive * Qpositive)))%type; apply Qquadratic_sign_equal.
Qed.

Lemma qnew_a_equal :
 forall (a b c d e f g h : Z) (p1 p2 : Qpositive)
   (H_Qquadratic_sg_denom_nonzero1
    H_Qquadratic_sg_denom_nonzero2 : Qquadratic_sg_denom_nonzero e f g h p1
                                       p2),
 qnew_a a b c d e f g h p1 p2 H_Qquadratic_sg_denom_nonzero1 =
 qnew_a a b c d e f g h p1 p2 H_Qquadratic_sg_denom_nonzero2.
Proof.
  intros a b c d e f g h p1 p2 H_Qquadratic_sg_denom_nonzero1
            H_Qquadratic_sg_denom_nonzero2; unfold qnew_a in |- *;
            apply f_equal with (Z * (Z * (Z * Z)))%type;
            apply f_equal with (Z * (Z * (Z * Z)) * (Z * (Z * (Z * Z))))%type;
            apply
             f_equal
              with
                (Z * (Z * (Z * Z)) * (Z * (Z * (Z * Z))) *
                 (Qpositive * Qpositive))%type;
            apply
             f_equal
              with
                (Z *
                 (Z * (Z * (Z * Z)) * (Z * (Z * (Z * Z))) *
                  (Qpositive * Qpositive)))%type; apply Qquadratic_sign_equal.
Qed.

Lemma qnew_b_equal :
 forall (a b c d e f g h : Z) (p1 p2 : Qpositive)
   (H_Qquadratic_sg_denom_nonzero1
    H_Qquadratic_sg_denom_nonzero2 : Qquadratic_sg_denom_nonzero e f g h p1
                                       p2),
 qnew_b a b c d e f g h p1 p2 H_Qquadratic_sg_denom_nonzero1 =
 qnew_b a b c d e f g h p1 p2 H_Qquadratic_sg_denom_nonzero2.
Proof.
 intros a b c d e f g h p1 p2 H_Qquadratic_sg_denom_nonzero1
            H_Qquadratic_sg_denom_nonzero2; unfold qnew_b in |- *;
            apply f_equal with (Z * (Z * Z))%type;
            apply f_equal with (Z * (Z * (Z * Z)))%type;
            apply f_equal with (Z * (Z * (Z * Z)) * (Z * (Z * (Z * Z))))%type;
            apply
             f_equal
              with
                (Z * (Z * (Z * Z)) * (Z * (Z * (Z * Z))) *
                 (Qpositive * Qpositive))%type;
            apply
             f_equal
              with
                (Z *
                 (Z * (Z * (Z * Z)) * (Z * (Z * (Z * Z))) *
                  (Qpositive * Qpositive)))%type; apply Qquadratic_sign_equal.
Qed.


Lemma qnew_c_equal :
 forall (a b c d e f g h : Z) (p1 p2 : Qpositive)
   (H_Qquadratic_sg_denom_nonzero1
    H_Qquadratic_sg_denom_nonzero2 : Qquadratic_sg_denom_nonzero e f g h p1
                                       p2),
 qnew_c a b c d e f g h p1 p2 H_Qquadratic_sg_denom_nonzero1 =
 qnew_c a b c d e f g h p1 p2 H_Qquadratic_sg_denom_nonzero2.
Proof.
 intros a b c d e f g h p1 p2 H_Qquadratic_sg_denom_nonzero1
   H_Qquadratic_sg_denom_nonzero2; unfold qnew_c in |- *;
     apply f_equal with (Z * Z)%type;
       apply f_equal with (Z * (Z * Z))%type;
         apply f_equal with (Z * (Z * (Z * Z)))%type;
           apply f_equal with (Z * (Z * (Z * Z)) * (Z * (Z * (Z * Z))))%type;
             apply
	       f_equal
               with
               (Z * (Z * (Z * Z)) * (Z * (Z * (Z * Z))) *
                 (Qpositive * Qpositive))%type;
               apply
		 f_equal
		 with
                 (Z *
                   (Z * (Z * (Z * Z)) * (Z * (Z * (Z * Z))) *
                     (Qpositive * Qpositive)))%type; apply Qquadratic_sign_equal.
Qed.

Lemma qnew_d_equal :
 forall (a b c d e f g h : Z) (p1 p2 : Qpositive)
   (H_Qquadratic_sg_denom_nonzero1
    H_Qquadratic_sg_denom_nonzero2 : Qquadratic_sg_denom_nonzero e f g h p1
                                       p2),
 qnew_d a b c d e f g h p1 p2 H_Qquadratic_sg_denom_nonzero1 =
 qnew_d a b c d e f g h p1 p2 H_Qquadratic_sg_denom_nonzero2.
Proof.
  intros a b c d e f g h p1 p2 H_Qquadratic_sg_denom_nonzero1
            H_Qquadratic_sg_denom_nonzero2; unfold qnew_d in |- *;
            apply f_equal with (Z * Z)%type;
            apply f_equal with (Z * (Z * Z))%type;
            apply f_equal with (Z * (Z * (Z * Z)))%type;
            apply f_equal with (Z * (Z * (Z * Z)) * (Z * (Z * (Z * Z))))%type;
            apply
             f_equal
              with
                (Z * (Z * (Z * Z)) * (Z * (Z * (Z * Z))) *
                 (Qpositive * Qpositive))%type;
            apply
             f_equal
              with
                (Z *
                 (Z * (Z * (Z * Z)) * (Z * (Z * (Z * Z))) *
                  (Qpositive * Qpositive)))%type; apply Qquadratic_sign_equal.
Qed.


Lemma qnew_e_equal :
 forall (a b c d e f g h : Z) (p1 p2 : Qpositive)
   (H_Qquadratic_sg_denom_nonzero1
    H_Qquadratic_sg_denom_nonzero2 : Qquadratic_sg_denom_nonzero e f g h p1
                                       p2),
 qnew_e a b c d e f g h p1 p2 H_Qquadratic_sg_denom_nonzero1 =
 qnew_e a b c d e f g h p1 p2 H_Qquadratic_sg_denom_nonzero2.
Proof.
  intros a b c d e f g h p1 p2 H_Qquadratic_sg_denom_nonzero1
    H_Qquadratic_sg_denom_nonzero2; unfold qnew_e in |- *;
      apply f_equal with (Z * (Z * (Z * Z)))%type;
        apply f_equal with (Z * (Z * (Z * Z)) * (Z * (Z * (Z * Z))))%type;
          apply
            f_equal
            with
            (Z * (Z * (Z * Z)) * (Z * (Z * (Z * Z))) *
              (Qpositive * Qpositive))%type;
            apply
              f_equal
              with
              (Z *
                (Z * (Z * (Z * Z)) * (Z * (Z * (Z * Z))) *
                  (Qpositive * Qpositive)))%type; apply Qquadratic_sign_equal.
Qed.


Lemma qnew_f_equal :
 forall (a b c d e f g h : Z) (p1 p2 : Qpositive)
   (H_Qquadratic_sg_denom_nonzero1
    H_Qquadratic_sg_denom_nonzero2 : Qquadratic_sg_denom_nonzero e f g h p1
                                       p2),
 qnew_f a b c d e f g h p1 p2 H_Qquadratic_sg_denom_nonzero1 =
 qnew_f a b c d e f g h p1 p2 H_Qquadratic_sg_denom_nonzero2.
Proof.
  intros a b c d e f g h p1 p2 H_Qquadratic_sg_denom_nonzero1
    H_Qquadratic_sg_denom_nonzero2; unfold qnew_f in |- *;
      apply f_equal with (Z * (Z * Z))%type;
        apply f_equal with (Z * (Z * (Z * Z)))%type;
          apply f_equal with (Z * (Z * (Z * Z)) * (Z * (Z * (Z * Z))))%type;
            apply
              f_equal
              with
              (Z * (Z * (Z * Z)) * (Z * (Z * (Z * Z))) *
                (Qpositive * Qpositive))%type;
              apply
		f_equal
		with
                (Z *
                  (Z * (Z * (Z * Z)) * (Z * (Z * (Z * Z))) *
                    (Qpositive * Qpositive)))%type; apply Qquadratic_sign_equal.
Qed.


Lemma qnew_g_equal :
 forall (a b c d e f g h : Z) (p1 p2 : Qpositive)
   (H_Qquadratic_sg_denom_nonzero1
    H_Qquadratic_sg_denom_nonzero2 : Qquadratic_sg_denom_nonzero e f g h p1
                                       p2),
 qnew_g a b c d e f g h p1 p2 H_Qquadratic_sg_denom_nonzero1 =
 qnew_g a b c d e f g h p1 p2 H_Qquadratic_sg_denom_nonzero2.
Proof.
 intros a b c d e f g h p1 p2 H_Qquadratic_sg_denom_nonzero1
            H_Qquadratic_sg_denom_nonzero2; unfold qnew_g in |- *;
            apply f_equal with (Z * Z)%type;
            apply f_equal with (Z * (Z * Z))%type;
            apply f_equal with (Z * (Z * (Z * Z)))%type;
            apply f_equal with (Z * (Z * (Z * Z)) * (Z * (Z * (Z * Z))))%type;
            apply
             f_equal
              with
                (Z * (Z * (Z * Z)) * (Z * (Z * (Z * Z))) *
                 (Qpositive * Qpositive))%type;
            apply
             f_equal
              with
                (Z *
                 (Z * (Z * (Z * Z)) * (Z * (Z * (Z * Z))) *
                  (Qpositive * Qpositive)))%type; apply Qquadratic_sign_equal.
Qed.

Lemma qnew_h_equal :
 forall (a b c d e f g h : Z) (p1 p2 : Qpositive)
   (H_Qquadratic_sg_denom_nonzero1
    H_Qquadratic_sg_denom_nonzero2 : Qquadratic_sg_denom_nonzero e f g h p1
                                       p2),
 qnew_h a b c d e f g h p1 p2 H_Qquadratic_sg_denom_nonzero1 =
 qnew_h a b c d e f g h p1 p2 H_Qquadratic_sg_denom_nonzero2.
Proof.
 intros a b c d e f g h p1 p2 H_Qquadratic_sg_denom_nonzero1
            H_Qquadratic_sg_denom_nonzero2; unfold qnew_h in |- *;
            apply f_equal with (Z * Z)%type;
            apply f_equal with (Z * (Z * Z))%type;
            apply f_equal with (Z * (Z * (Z * Z)))%type;
            apply f_equal with (Z * (Z * (Z * Z)) * (Z * (Z * (Z * Z))))%type;
            apply
             f_equal
              with
                (Z * (Z * (Z * Z)) * (Z * (Z * (Z * Z))) *
                 (Qpositive * Qpositive))%type;
            apply
             f_equal
              with
                (Z *
                 (Z * (Z * (Z * Z)) * (Z * (Z * (Z * Z))) *
                  (Qpositive * Qpositive)))%type; apply Qquadratic_sign_equal.
Qed.

Lemma qnew_p1_equal :
 forall (a b c d e f g h : Z) (p1 p2 : Qpositive)
   (H_Qquadratic_sg_denom_nonzero1
    H_Qquadratic_sg_denom_nonzero2 : Qquadratic_sg_denom_nonzero e f g h p1
                                       p2),
 qnew_p1 a b c d e f g h p1 p2 H_Qquadratic_sg_denom_nonzero1 =
 qnew_p1 a b c d e f g h p1 p2 H_Qquadratic_sg_denom_nonzero2.
Proof.
 intros a b c d e f g h p1 p2 H_Qquadratic_sg_denom_nonzero1
            H_Qquadratic_sg_denom_nonzero2; unfold qnew_p1 in |- *;
            apply f_equal with (Qpositive * Qpositive)%type;
            apply
             f_equal
              with
                (Z * (Z * (Z * Z)) * (Z * (Z * (Z * Z))) *
                 (Qpositive * Qpositive))%type;
            apply
             f_equal
              with
                (Z *
                 (Z * (Z * (Z * Z)) * (Z * (Z * (Z * Z))) *
                  (Qpositive * Qpositive)))%type; apply Qquadratic_sign_equal.
Qed.


Lemma qnew_p2_equal :
 forall (a b c d e f g h : Z) (p1 p2 : Qpositive)
   (H_Qquadratic_sg_denom_nonzero1
    H_Qquadratic_sg_denom_nonzero2 : Qquadratic_sg_denom_nonzero e f g h p1
                                       p2),
 qnew_p2 a b c d e f g h p1 p2 H_Qquadratic_sg_denom_nonzero1 =
 qnew_p2 a b c d e f g h p1 p2 H_Qquadratic_sg_denom_nonzero2.
Proof.
 intros a b c d e f g h p1 p2 H_Qquadratic_sg_denom_nonzero1
            H_Qquadratic_sg_denom_nonzero2; unfold qnew_p2 in |- *;
            apply f_equal with (Qpositive * Qpositive)%type;
            apply
             f_equal
              with
                (Z * (Z * (Z * Z)) * (Z * (Z * (Z * Z))) *
                 (Qpositive * Qpositive))%type;
            apply
             f_equal
              with
                (Z *
                 (Z * (Z * (Z * Z)) * (Z * (Z * (Z * Z))) *
                  (Qpositive * Qpositive)))%type; apply Qquadratic_sign_equal.
Qed.

Lemma Qquadratic_Qpositive_to_Q_equal :
 forall (a b c d e f g h : Z) (p1 p2 : Qpositive)
   (H_Qquadratic_sg_denom_nonzero1
    H_Qquadratic_sg_denom_nonzero2 : Qquadratic_sg_denom_nonzero e f g h p1
                                       p2),
 Qquadratic_Qpositive_to_Q a b c d e f g h p1 p2
   H_Qquadratic_sg_denom_nonzero1 =
 Qquadratic_Qpositive_to_Q a b c d e f g h p1 p2
   H_Qquadratic_sg_denom_nonzero2.
Proof.
 intros a b c d e f g h p1 p2 H_Qquadratic_sg_denom_nonzero1.

 functional induction
   (Qquadratic_Qpositive_to_Q a b c d e f g h p1 p2
                            H_Qquadratic_sg_denom_nonzero1); 
  intros; Clear_eq_.
 (* 1 *)
 rewrite
  (Qquadratic_Qpositive_to_Q_3 _ _ _ _ _ _ _ _ _ _
     H_Qquadratic_sg_denom_nonzero2 He _x); reflexivity.
 (* 2 *)
 rewrite
  (Qquadratic_Qpositive_to_Q_2 _ _ _ _ _ _ _ _ _ _
     H_Qquadratic_sg_denom_nonzero2 Hf _x); reflexivity.
 (* 3 *)
 rewrite
  (Qquadratic_Qpositive_to_Q_1 _ _ _ _ _ _ _ _ _ _
     H_Qquadratic_sg_denom_nonzero2 Hg _x); reflexivity.
 (* 4 *)
 rewrite
  (Qquadratic_Qpositive_to_Q_0 _ _ _ _ _ _ _ _ _ _
     H_Qquadratic_sg_denom_nonzero2 Hh _x); reflexivity.
 (* 5 *)
 rewrite
  (q_sign_equal a b c d _ _ _ _ _ _ H_Qquadratic_sg_denom_nonzero1
     H_Qquadratic_sg_denom_nonzero2) in _x;
  rewrite
   (Qquadratic_Qpositive_to_Q_4 _ _ _ _ _ _ _ _ _ _
      H_Qquadratic_sg_denom_nonzero2 not_same_ratio_abcdefgh _x)
   ; reflexivity.
 (* 6 *)
 Absurd_q_sign_.
 (* 7 *)
 assert
  (H :
   Z.sgn
     (qnew_a a b c d e f g h p1 p2 H_Qquadratic_sg_denom_nonzero2 +
      qnew_b a b c d e f g h p1 p2 H_Qquadratic_sg_denom_nonzero2 +
      qnew_c a b c d e f g h p1 p2 H_Qquadratic_sg_denom_nonzero2 +
      qnew_d a b c d e f g h p1 p2 H_Qquadratic_sg_denom_nonzero2) = 1%Z).
   rewrite
    (qnew_a_equal a b c d _ _ _ _ _ _ H_Qquadratic_sg_denom_nonzero2
       H_Qquadratic_sg_denom_nonzero1);
    rewrite
     (qnew_b_equal a b c d _ _ _ _ _ _ H_Qquadratic_sg_denom_nonzero2
        H_Qquadratic_sg_denom_nonzero1);
    rewrite
     (qnew_c_equal a b c d _ _ _ _ _ _ H_Qquadratic_sg_denom_nonzero2
        H_Qquadratic_sg_denom_nonzero1);
    rewrite
     (qnew_d_equal a b c d _ _ _ _ _ _ H_Qquadratic_sg_denom_nonzero2
        H_Qquadratic_sg_denom_nonzero1); assumption.
   rewrite
    (Qquadratic_Qpositive_to_Q_5 _ _ _ _ _ _ _ _ _ _
       H_Qquadratic_sg_denom_nonzero2 not_same_ratio_abcdefgh
       (trans_eq
          (q_sign_equal a b c d _ _ _ _ _ _ H_Qquadratic_sg_denom_nonzero2
             H_Qquadratic_sg_denom_nonzero1) l1_eq_one) H
       (Qquadratic_Qpositive_to_Q_quadraticAcc_pos_1 _ _ _ _ _ _ _ _ _ _
          H_Qquadratic_sg_denom_nonzero2 not_same_ratio_abcdefgh
          (trans_eq
             (q_sign_equal a b c d _ _ _ _ _ _ H_Qquadratic_sg_denom_nonzero2
                H_Qquadratic_sg_denom_nonzero1) l1_eq_one) H))
    ; apply f_equal with Qpositive;
    apply Qquadratic_Qpositive_to_Qpositive_equal_strong;
    [ apply qnew_a_equal
    | apply qnew_b_equal
    | apply qnew_c_equal
    | apply qnew_d_equal
    | apply qnew_e_equal
    | apply qnew_f_equal
    | apply qnew_g_equal
    | apply qnew_h_equal
    | apply qnew_p1_equal
    | apply qnew_p2_equal ].
 (* 8 *)
 assert
  (H :
   Z.sgn
     (qnew_a a b c d e f g h p1 p2 H_Qquadratic_sg_denom_nonzero2 +
      qnew_b a b c d e f g h p1 p2 H_Qquadratic_sg_denom_nonzero2 +
      qnew_c a b c d e f g h p1 p2 H_Qquadratic_sg_denom_nonzero2 +
      qnew_d a b c d e f g h p1 p2 H_Qquadratic_sg_denom_nonzero2) = 
   (-1)%Z).
   rewrite
    (qnew_a_equal a b c d _ _ _ _ _ _ H_Qquadratic_sg_denom_nonzero2
       H_Qquadratic_sg_denom_nonzero1);
    rewrite
     (qnew_b_equal a b c d _ _ _ _ _ _ H_Qquadratic_sg_denom_nonzero2
        H_Qquadratic_sg_denom_nonzero1);
    rewrite
     (qnew_c_equal a b c d _ _ _ _ _ _ H_Qquadratic_sg_denom_nonzero2
        H_Qquadratic_sg_denom_nonzero1);
    rewrite
     (qnew_d_equal a b c d _ _ _ _ _ _ H_Qquadratic_sg_denom_nonzero2
        H_Qquadratic_sg_denom_nonzero1); assumption.
   rewrite
    (Qquadratic_Qpositive_to_Q_6 _ _ _ _ _ _ _ _ _ _
       H_Qquadratic_sg_denom_nonzero2 not_same_ratio_abcdefgh
       (trans_eq
          (q_sign_equal a b c d _ _ _ _ _ _ H_Qquadratic_sg_denom_nonzero2
             H_Qquadratic_sg_denom_nonzero1) l1_eq_one) H
       (Qquadratic_Qpositive_to_Q_quadraticAcc_pos_2 _ _ _ _ _ _ _ _ _ _
          H_Qquadratic_sg_denom_nonzero2 not_same_ratio_abcdefgh
          (trans_eq
             (q_sign_equal a b c d _ _ _ _ _ _ H_Qquadratic_sg_denom_nonzero2
                H_Qquadratic_sg_denom_nonzero1) l1_eq_one) H))
    .
   apply f_equal with Qpositive;
    apply Qquadratic_Qpositive_to_Qpositive_equal_strong;
    try apply f_equal with Z;
    [ apply qnew_a_equal
    | apply qnew_b_equal
    | apply qnew_c_equal
    | apply qnew_d_equal
    | apply qnew_e_equal
    | apply qnew_f_equal
    | apply qnew_g_equal
    | apply qnew_h_equal
    | apply qnew_p1_equal
    | apply qnew_p2_equal ].
 (* 9 *)
 Absurd_q_sign_.
 (* 10 *)
 assert
  (H :
   Z.sgn
     (qnew_a a b c d e f g h p1 p2 H_Qquadratic_sg_denom_nonzero2 +
      qnew_b a b c d e f g h p1 p2 H_Qquadratic_sg_denom_nonzero2 +
      qnew_c a b c d e f g h p1 p2 H_Qquadratic_sg_denom_nonzero2 +
      qnew_d a b c d e f g h p1 p2 H_Qquadratic_sg_denom_nonzero2) = 1%Z).
   rewrite
    (qnew_a_equal a b c d _ _ _ _ _ _ H_Qquadratic_sg_denom_nonzero2
       H_Qquadratic_sg_denom_nonzero1);
    rewrite
     (qnew_b_equal a b c d _ _ _ _ _ _ H_Qquadratic_sg_denom_nonzero2
        H_Qquadratic_sg_denom_nonzero1);
    rewrite
     (qnew_c_equal a b c d _ _ _ _ _ _ H_Qquadratic_sg_denom_nonzero2
        H_Qquadratic_sg_denom_nonzero1);
    rewrite
     (qnew_d_equal a b c d _ _ _ _ _ _ H_Qquadratic_sg_denom_nonzero2
        H_Qquadratic_sg_denom_nonzero1); assumption.
   rewrite
    (Qquadratic_Qpositive_to_Q_7 _ _ _ _ _ _ _ _ _ _
       H_Qquadratic_sg_denom_nonzero2 not_same_ratio_abcdefgh
       (trans_eq
          (q_sign_equal a b c d _ _ _ _ _ _ H_Qquadratic_sg_denom_nonzero2
             H_Qquadratic_sg_denom_nonzero1) l1_eq_min_one) H
       (Qquadratic_Qpositive_to_Q_quadraticAcc_neg_1 _ _ _ _ _ _ _ _ _ _
          H_Qquadratic_sg_denom_nonzero2 not_same_ratio_abcdefgh
          (trans_eq
             (q_sign_equal a b c d _ _ _ _ _ _ H_Qquadratic_sg_denom_nonzero2
                H_Qquadratic_sg_denom_nonzero1) l1_eq_min_one) H))
    .
   apply f_equal with Qpositive;
    apply Qquadratic_Qpositive_to_Qpositive_equal_strong;
    try apply f_equal with Z;
    [ apply qnew_a_equal
    | apply qnew_b_equal
    | apply qnew_c_equal
    | apply qnew_d_equal
    | apply qnew_e_equal
    | apply qnew_f_equal
    | apply qnew_g_equal
    | apply qnew_h_equal
    | apply qnew_p1_equal
    | apply qnew_p2_equal ].
 (* 11 *)
 assert
  (H :
   Z.sgn
     (qnew_a a b c d e f g h p1 p2 H_Qquadratic_sg_denom_nonzero2 +
      qnew_b a b c d e f g h p1 p2 H_Qquadratic_sg_denom_nonzero2 +
      qnew_c a b c d e f g h p1 p2 H_Qquadratic_sg_denom_nonzero2 +
      qnew_d a b c d e f g h p1 p2 H_Qquadratic_sg_denom_nonzero2) = 
   (-1)%Z).
   rewrite
    (qnew_a_equal a b c d _ _ _ _ _ _ H_Qquadratic_sg_denom_nonzero2
       H_Qquadratic_sg_denom_nonzero1);
    rewrite
     (qnew_b_equal a b c d _ _ _ _ _ _ H_Qquadratic_sg_denom_nonzero2
        H_Qquadratic_sg_denom_nonzero1);
    rewrite
     (qnew_c_equal a b c d _ _ _ _ _ _ H_Qquadratic_sg_denom_nonzero2
        H_Qquadratic_sg_denom_nonzero1);
    rewrite
     (qnew_d_equal a b c d _ _ _ _ _ _ H_Qquadratic_sg_denom_nonzero2
        H_Qquadratic_sg_denom_nonzero1); assumption.
   rewrite
    (Qquadratic_Qpositive_to_Q_8 _ _ _ _ _ _ _ _ _ _
       H_Qquadratic_sg_denom_nonzero2 not_same_ratio_abcdefgh
       (trans_eq
          (q_sign_equal a b c d _ _ _ _ _ _ H_Qquadratic_sg_denom_nonzero2
             H_Qquadratic_sg_denom_nonzero1) l1_eq_min_one) H
       (Qquadratic_Qpositive_to_Q_quadraticAcc_neg_2 _ _ _ _ _ _ _ _ _ _
          H_Qquadratic_sg_denom_nonzero2 not_same_ratio_abcdefgh
          (trans_eq
             (q_sign_equal a b c d _ _ _ _ _ _ H_Qquadratic_sg_denom_nonzero2
                H_Qquadratic_sg_denom_nonzero1) l1_eq_min_one) H))
    .
   apply f_equal with Qpositive;
    apply Qquadratic_Qpositive_to_Qpositive_equal_strong;
    try apply f_equal with Z;
    [ apply qnew_a_equal
    | apply qnew_b_equal
    | apply qnew_c_equal
    | apply qnew_d_equal
    | apply qnew_e_equal
    | apply qnew_f_equal
    | apply qnew_g_equal
    | apply qnew_h_equal
    | apply qnew_p1_equal
    | apply qnew_p2_equal ].
Qed.
