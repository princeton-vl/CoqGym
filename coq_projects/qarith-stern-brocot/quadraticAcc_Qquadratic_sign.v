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



Require Export Qquadratic_sign_properties.
Require Export Qquadratic_Qpositive_to_Qpositive.
Require Export homographicAcc_Qhomographic_sign.

Definition qnew_a (a b c d e f g h : Z) (p1 p2 : Qpositive)
  (H_Qquadratic_sg_denom_nonzero : Qquadratic_sg_denom_nonzero e f g h p1 p2) :=
  fst
    (fst
       (fst
          (snd
             (Qquadratic_sign a b c d e f g h p1 p2
                H_Qquadratic_sg_denom_nonzero)))).

Definition qnew_b (a b c d e f g h : Z) (p1 p2 : Qpositive)
  (H_Qquadratic_sg_denom_nonzero : Qquadratic_sg_denom_nonzero e f g h p1 p2) :=
  fst
    (snd
       (fst
          (fst
             (snd
                (Qquadratic_sign a b c d e f g h p1 p2
                   H_Qquadratic_sg_denom_nonzero))))).

Definition qnew_c (a b c d e f g h : Z) (p1 p2 : Qpositive)
  (H_Qquadratic_sg_denom_nonzero : Qquadratic_sg_denom_nonzero e f g h p1 p2) :=
  fst
    (snd
       (snd
          (fst
             (fst
                (snd
                   (Qquadratic_sign a b c d e f g h p1 p2
                      H_Qquadratic_sg_denom_nonzero)))))).

Definition qnew_d (a b c d e f g h : Z) (p1 p2 : Qpositive)
  (H_Qquadratic_sg_denom_nonzero : Qquadratic_sg_denom_nonzero e f g h p1 p2) :=
  snd
    (snd
       (snd
          (fst
             (fst
                (snd
                   (Qquadratic_sign a b c d e f g h p1 p2
                      H_Qquadratic_sg_denom_nonzero)))))).

Definition qnew_e (a b c d e f g h : Z) (p1 p2 : Qpositive)
  (H_Qquadratic_sg_denom_nonzero : Qquadratic_sg_denom_nonzero e f g h p1 p2) :=
  fst
    (snd
       (fst
          (snd
             (Qquadratic_sign a b c d e f g h p1 p2
                H_Qquadratic_sg_denom_nonzero)))).

Definition qnew_f (a b c d e f g h : Z) (p1 p2 : Qpositive)
  (H_Qquadratic_sg_denom_nonzero : Qquadratic_sg_denom_nonzero e f g h p1 p2) :=
  fst
    (snd
       (snd
          (fst
             (snd
                (Qquadratic_sign a b c d e f g h p1 p2
                   H_Qquadratic_sg_denom_nonzero))))).

Definition qnew_g (a b c d e f g h : Z) (p1 p2 : Qpositive)
  (H_Qquadratic_sg_denom_nonzero : Qquadratic_sg_denom_nonzero e f g h p1 p2) :=
  fst
    (snd
       (snd
          (snd
             (fst
                (snd
                   (Qquadratic_sign a b c d e f g h p1 p2
                      H_Qquadratic_sg_denom_nonzero)))))).

Definition qnew_h (a b c d e f g h : Z) (p1 p2 : Qpositive)
  (H_Qquadratic_sg_denom_nonzero : Qquadratic_sg_denom_nonzero e f g h p1 p2) :=
  snd
    (snd
       (snd
          (snd
             (fst
                (snd
                   (Qquadratic_sign a b c d e f g h p1 p2
                      H_Qquadratic_sg_denom_nonzero)))))).

Definition qnew_p1 (a b c d e f g h : Z) (p1 p2 : Qpositive)
  (H_Qquadratic_sg_denom_nonzero : Qquadratic_sg_denom_nonzero e f g h p1 p2) :=
  fst
    (snd
       (snd
          (Qquadratic_sign a b c d e f g h p1 p2
             H_Qquadratic_sg_denom_nonzero))).

Definition qnew_p2 (a b c d e f g h : Z) (p1 p2 : Qpositive)
  (H_Qquadratic_sg_denom_nonzero : Qquadratic_sg_denom_nonzero e f g h p1 p2) :=
  snd
    (snd
       (snd
          (Qquadratic_sign a b c d e f g h p1 p2
             H_Qquadratic_sg_denom_nonzero))).  

Lemma Qquadratic_Qpositive_to_Q_quadraticAcc_pos_1 :
 forall (a b c d e f g h : Z) (p1 p2 : Qpositive)
   (H_Qquadratic_sg_denom_nonzero : Qquadratic_sg_denom_nonzero e f g h p1 p2),
 ~ same_ratio a b c d e f g h ->
 q_sign a b c d e f g h p1 p2 H_Qquadratic_sg_denom_nonzero = 1%Z ->
 Z.sgn
   (qnew_a a b c d e f g h p1 p2 H_Qquadratic_sg_denom_nonzero +
    qnew_b a b c d e f g h p1 p2 H_Qquadratic_sg_denom_nonzero +
    qnew_c a b c d e f g h p1 p2 H_Qquadratic_sg_denom_nonzero +
    qnew_d a b c d e f g h p1 p2 H_Qquadratic_sg_denom_nonzero) = 1%Z ->
 quadraticAcc (qnew_a a b c d e f g h p1 p2 H_Qquadratic_sg_denom_nonzero)
   (qnew_b a b c d e f g h p1 p2 H_Qquadratic_sg_denom_nonzero)
   (qnew_c a b c d e f g h p1 p2 H_Qquadratic_sg_denom_nonzero)
   (qnew_d a b c d e f g h p1 p2 H_Qquadratic_sg_denom_nonzero)
   (qnew_e a b c d e f g h p1 p2 H_Qquadratic_sg_denom_nonzero)
   (qnew_f a b c d e f g h p1 p2 H_Qquadratic_sg_denom_nonzero)
   (qnew_g a b c d e f g h p1 p2 H_Qquadratic_sg_denom_nonzero)
   (qnew_h a b c d e f g h p1 p2 H_Qquadratic_sg_denom_nonzero)
   (qnew_p1 a b c d e f g h p1 p2 H_Qquadratic_sg_denom_nonzero)
   (qnew_p2 a b c d e f g h p1 p2 H_Qquadratic_sg_denom_nonzero).
Proof.
 intros a b c d e f g h p1 p2 H_qsign not_same_ratio_abcdefgh l1_eq_one
  na_nb_nc_nd_eq_one.
 set (na := qnew_a a b c d e f g h p1 p2 H_qsign) in *.
 set (nb := qnew_b a b c d e f g h p1 p2 H_qsign) in *.
 set (nc := qnew_c a b c d e f g h p1 p2 H_qsign) in *.
 set (nd := qnew_d a b c d e f g h p1 p2 H_qsign) in *.
 set (ne := qnew_e a b c d e f g h p1 p2 H_qsign) in *.
 set (nf := qnew_f a b c d e f g h p1 p2 H_qsign) in *.
 set (ng := qnew_g a b c d e f g h p1 p2 H_qsign) in *.
 set (nh := qnew_h a b c d e f g h p1 p2 H_qsign) in *.
 set (np1 := qnew_p1 a b c d e f g h p1 p2 H_qsign) in *.
 set (np2 := qnew_p2 a b c d e f g h p1 p2 H_qsign) in *.

 assert
  (H :
   Qquadratic_sign a b c d e f g h p1 p2 H_qsign =
   (1%Z, (na, (nb, (nc, nd)), (ne, (nf, (ng, nh))), (np1, np2)))).
 unfold na, nb, nc, nd, ne, nf, ng, nh, np1, np2 in |- *.
 rewrite <- l1_eq_one.
 unfold qnew_a, qnew_b, qnew_c, qnew_d, qnew_e, qnew_f, qnew_g, qnew_h,
  qnew_p1, qnew_p2 in |- *.
 replace (q_sign a b c d e f g h p1 p2 H_qsign) with
  (fst (Qquadratic_sign a b c d e f g h p1 p2 H_qsign));
  [ idtac | reflexivity ]; repeat rewrite <- pair_1; 
  reflexivity.

 


 generalize
  (Qquadratic_sign_pos_1 a b c d e f g h p1 p2 H_qsign na nb nc nd ne nf ng
     nh np1 np2 H).
 intros [(H_nabcd, H_nefgh)| (H1, _)];
  [ idtac
  | apply False_ind; generalize (Zsgn_9 _ na_nb_nc_nd_eq_one); apply Zlt_asym;
     assumption ].
 
 destruct np1 as [p| p| ].
  (* np1 = (nR p) *)
  destruct np2 as [p0| p0| ].
   (* np2 = (nR p0) *)
   apply quadraticAcc_wf; solve
    [ assumption
    | generalize
       (Qquadratic_sign_pos_2 a b c d e f g h p1 p2 H_qsign na nb nc nd ne nf
          ng nh (nR p) (nR p0) H);
       intros
        [[[[[[(Ha, (Hb, (Hc, (Hd, (He, (Hf, (Hg, Hh)))))))|
              (Ha, (Hb, (Hc, (Hd, (He, (Hf, (Hg, Hh)))))))]|
             (H_discriminate_me, _)]|
            (H_discriminate_me, _)]|
           (H_discriminate_me, _)]|
          (_, (H_discriminate_me,_))]|
         (_, (H_discriminate_me,_))];
       [ assumption
       | apply False_ind; generalize H_nabcd; apply Zle_not_lt;
          repeat apply Zle_resp_neg; assumption
       | discriminate H_discriminate_me
       | discriminate H_discriminate_me
       | discriminate H_discriminate_me
       | discriminate H_discriminate_me
       | discriminate H_discriminate_me ] ].
   (* np2 = (dL p0) *) 
   apply quadraticAcc_wf; solve
    [ assumption
    | generalize
       (Qquadratic_sign_pos_2 a b c d e f g h p1 p2 H_qsign na nb nc nd ne nf
          ng nh (nR p) (dL p0) H);
       intros
        [[[[[[(Ha, (Hb, (Hc, (Hd, (He, (Hf, (Hg, Hh)))))))|
              (Ha, (Hb, (Hc, (Hd, (He, (Hf, (Hg, Hh)))))))]|
             (H_discriminate_me, _)]|
            (H_discriminate_me, _)]|
           (H_discriminate_me, _)]|
          (_, (H_discriminate_me,_))]|
         (_, (H_discriminate_me,_))];
       [ assumption
       | apply False_ind; generalize H_nabcd; apply Zle_not_lt;
          repeat apply Zle_resp_neg; assumption
       | discriminate H_discriminate_me
       | discriminate H_discriminate_me
       | discriminate H_discriminate_me
       | discriminate H_discriminate_me
       | discriminate H_discriminate_me ] ].
   (* np2=One *)
   apply quadraticacc0'.
   discriminate.
   reflexivity.
   apply homographicAcc_wf; solve
    [ rewrite Zplus_assoc; assumption
    | generalize
       (Qquadratic_sign_pos_2 a b c d e f g h p1 p2 H_qsign na nb nc nd ne nf
          ng nh (nR p) One H);
       intros
        [[[[[[(Ha, (Hb, (Hc, (Hd, (He, (Hf, (Hg, Hh)))))))|
              (Ha, (Hb, (Hc, (Hd, (He, (Hf, (Hg, Hh)))))))]|
             (H_discriminate_me, _)]|
            (H_discriminate_me, _)]|
           (H_discriminate_me, _)]|
          (_, (_, (Hab, (Hcd, (Hef, Hgh)))))]|
         (_, (_, (Hab, (Hcd, (Hef, Hgh)))))];
       [ apply Zplus_le_0_compat; assumption
       | apply False_ind; generalize H_nabcd; apply Zle_not_lt;
          repeat apply Zle_resp_neg; assumption
       | discriminate H_discriminate_me
       | discriminate H_discriminate_me
       | discriminate H_discriminate_me
       | assumption
       | apply False_ind; generalize H_nabcd; apply Zle_not_lt;
          rewrite <- Zplus_assoc; apply Zle_resp_neg; 
          assumption ] ].

  (* np1 = (dL p) *)
  destruct np2 as [p0| p0| ].
   (* np2 = (nR p0) *) 
   apply quadraticAcc_wf; solve
    [ assumption
    | generalize
       (Qquadratic_sign_pos_2 a b c d e f g h p1 p2 H_qsign na nb nc nd ne nf
          ng nh (dL p) (nR p0) H);
       intros
        [[[[[[(Ha, (Hb, (Hc, (Hd, (He, (Hf, (Hg, Hh)))))))|
              (Ha, (Hb, (Hc, (Hd, (He, (Hf, (Hg, Hh)))))))]|
             (H_discriminate_me, _)]|
            (H_discriminate_me, _)]|
           (H_discriminate_me, _)]|
          (_, (H_discriminate_me,_))]|
         (_, (H_discriminate_me,_))];
       [ assumption
       | apply False_ind; generalize H_nabcd; apply Zle_not_lt;
          repeat apply Zle_resp_neg; assumption
       | discriminate H_discriminate_me
       | discriminate H_discriminate_me
       | discriminate H_discriminate_me
       | discriminate H_discriminate_me
       | discriminate H_discriminate_me ] ].
   (* np2 = (dL p0) *) 
   apply quadraticAcc_wf; solve
    [ assumption
    | generalize
       (Qquadratic_sign_pos_2 a b c d e f g h p1 p2 H_qsign na nb nc nd ne nf
          ng nh (dL p) (dL p0) H);
       intros
        [[[[[[(Ha, (Hb, (Hc, (Hd, (He, (Hf, (Hg, Hh)))))))|
              (Ha, (Hb, (Hc, (Hd, (He, (Hf, (Hg, Hh)))))))]|
             (H_discriminate_me, _)]|
            (H_discriminate_me, _)]|
           (H_discriminate_me, _)]|
          (_, (H_discriminate_me,_))]|
         (_, (H_discriminate_me,_))];
       [ assumption
       | apply False_ind; generalize H_nabcd; apply Zle_not_lt;
          repeat apply Zle_resp_neg; assumption
       | discriminate H_discriminate_me
       | discriminate H_discriminate_me
       | discriminate H_discriminate_me
       | discriminate H_discriminate_me
       | discriminate H_discriminate_me ] ].
   (* np2=One *)
   apply quadraticacc0'.
   discriminate.
   reflexivity.
   apply homographicAcc_wf; solve
    [ rewrite Zplus_assoc; assumption
    | generalize
       (Qquadratic_sign_pos_2 a b c d e f g h p1 p2 H_qsign na nb nc nd ne nf
          ng nh (dL p) One H);
       intros
        [[[[[[(Ha, (Hb, (Hc, (Hd, (He, (Hf, (Hg, Hh)))))))|
              (Ha, (Hb, (Hc, (Hd, (He, (Hf, (Hg, Hh)))))))]|
             (H_discriminate_me, _)]|
            (H_discriminate_me, _)]|
           (H_discriminate_me, _)]|
          (_, (_, (Hab, (Hcd, (Hef, Hgh)))))]|
         (_, (_, (Hab, (Hcd, (Hef, Hgh)))))];
       [ apply Zplus_le_0_compat; assumption
       | apply False_ind; generalize H_nabcd; apply Zle_not_lt;
          repeat apply Zle_resp_neg; assumption
       | discriminate H_discriminate_me
       | discriminate H_discriminate_me
       | discriminate H_discriminate_me
       | assumption
       | apply False_ind; generalize H_nabcd; apply Zle_not_lt;
          rewrite <- Zplus_assoc; apply Zle_resp_neg; 
          assumption ] ].

  (* np1 = One *)
  apply quadraticacc0.
  reflexivity.
  destruct np2 as [p| p| ].
   (* np2 = (nR p) *) (* Here we use the third & forth clause in Qquadratic_sign_pos_2:  p1=One /\ .... *)
   apply homographicAcc_wf; first
    [ omega
    | generalize
       (Qquadratic_sign_pos_2 a b c d e f g h p1 p2 H_qsign na nb nc nd ne nf
          ng nh One (nR p) H);
       intros
        [[[[[[(Ha, (Hb, (Hc, (Hd, (He, (Hf, (Hg, Hh)))))))|
              (Ha, (Hb, (Hc, (Hd, (He, (Hf, (Hg, Hh)))))))]|
             (_, (Hab, (Hcd, (Hef, Hgh))))]|
            (_, (Hab, (Hcd, (Hef, Hgh))))]|
           (_, H_discriminate_me)]|
          (_, (H_discriminate_me,_))]|
         (_, (H_discriminate_me,_))];
       [ apply Zplus_le_0_compat; assumption
       | apply False_ind; generalize H_nabcd; apply Zle_not_lt;
          repeat apply Zle_resp_neg; assumption
       | assumption
       | apply False_ind; generalize H_nabcd; apply Zle_not_lt; omega
       | discriminate H_discriminate_me
       | discriminate H_discriminate_me
       | discriminate H_discriminate_me ] ].
   (* np2 = (dL p) *) (* Here we use the third & forth clause in Qquadratic_sign_pos_2:  p1=One /\ .... *)
   apply homographicAcc_wf; solve
    [ omega
    | generalize
       (Qquadratic_sign_pos_2 a b c d e f g h p1 p2 H_qsign na nb nc nd ne nf
          ng nh One (dL p) H);
       intros
        [[[[[[(Ha, (Hb, (Hc, (Hd, (He, (Hf, (Hg, Hh)))))))|
              (Ha, (Hb, (Hc, (Hd, (He, (Hf, (Hg, Hh)))))))]|
             (_, (Hab, (Hcd, (Hef, Hgh))))]|
            (_, (Hab, (Hcd, (Hef, Hgh))))]|
           (_, H_discriminate_me)]|
          (_, (H_discriminate_me,_))]|
         (_, (H_discriminate_me,_))];
       [ apply Zplus_le_0_compat; assumption
       | apply False_ind; generalize H_nabcd; apply Zle_not_lt;
          repeat apply Zle_resp_neg; assumption
       | assumption
       | apply False_ind; generalize H_nabcd; apply Zle_not_lt; omega
       | discriminate H_discriminate_me
       | discriminate H_discriminate_me
       | discriminate H_discriminate_me ] ].
   (* np2 = One *)
   apply homographicacc0; reflexivity || omega. 
Qed.




Lemma Qquadratic_Qpositive_to_Q_quadraticAcc_pos_2 :
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
 quadraticAcc (- qnew_a a b c d e f g h p1 p2 H_Qquadratic_sg_denom_nonzero)
   (- qnew_b a b c d e f g h p1 p2 H_Qquadratic_sg_denom_nonzero)
   (- qnew_c a b c d e f g h p1 p2 H_Qquadratic_sg_denom_nonzero)
   (- qnew_d a b c d e f g h p1 p2 H_Qquadratic_sg_denom_nonzero)
   (- qnew_e a b c d e f g h p1 p2 H_Qquadratic_sg_denom_nonzero)
   (- qnew_f a b c d e f g h p1 p2 H_Qquadratic_sg_denom_nonzero)
   (- qnew_g a b c d e f g h p1 p2 H_Qquadratic_sg_denom_nonzero)
   (- qnew_h a b c d e f g h p1 p2 H_Qquadratic_sg_denom_nonzero)
   (qnew_p1 a b c d e f g h p1 p2 H_Qquadratic_sg_denom_nonzero)
   (qnew_p2 a b c d e f g h p1 p2 H_Qquadratic_sg_denom_nonzero).
Proof.
 intros a b c d e f g h p1 p2 H_qsign not_same_ratio_abcdefgh l1_eq_one
  na_nb_nc_nd_eq_minus_one.
 set (na := qnew_a a b c d e f g h p1 p2 H_qsign) in *.
 set (nb := qnew_b a b c d e f g h p1 p2 H_qsign) in *.
 set (nc := qnew_c a b c d e f g h p1 p2 H_qsign) in *.
 set (nd := qnew_d a b c d e f g h p1 p2 H_qsign) in *.
 set (ne := qnew_e a b c d e f g h p1 p2 H_qsign) in *.
 set (nf := qnew_f a b c d e f g h p1 p2 H_qsign) in *.
 set (ng := qnew_g a b c d e f g h p1 p2 H_qsign) in *.
 set (nh := qnew_h a b c d e f g h p1 p2 H_qsign) in *.
 set (np1 := qnew_p1 a b c d e f g h p1 p2 H_qsign) in *.
 set (np2 := qnew_p2 a b c d e f g h p1 p2 H_qsign) in *.

 assert
  (H :
   Qquadratic_sign a b c d e f g h p1 p2 H_qsign =
   (1%Z, (na, (nb, (nc, nd)), (ne, (nf, (ng, nh))), (np1, np2)))).
 unfold na, nb, nc, nd, ne, nf, ng, nh, np1, np2 in |- *.
 rewrite <- l1_eq_one.
 unfold qnew_a, qnew_b, qnew_c, qnew_d, qnew_e, qnew_f, qnew_g, qnew_h,
  qnew_p1, qnew_p2 in |- *.
 replace (q_sign a b c d e f g h p1 p2 H_qsign) with
  (fst (Qquadratic_sign a b c d e f g h p1 p2 H_qsign));
  [ idtac | reflexivity ]; repeat rewrite <- pair_1; 
  reflexivity.


 generalize
  (Qquadratic_sign_pos_1 a b c d e f g h p1 p2 H_qsign na nb nc nd ne nf ng
     nh np1 np2 H).
 intros [(H1, _)| (H_nabcd, H_nefgh)];
  [ apply False_ind; generalize (Zsgn_10 _ na_nb_nc_nd_eq_minus_one);
     apply Zlt_asym; assumption
  | idtac ].
 
 destruct np1 as [p| p| ].
  (* np1 = (nR p) *)
  destruct np2 as [p0| p0| ].
   (* np2 = (nR p0 *) 
   apply quadraticAcc_wf; solve
    [ omega
    | generalize
       (Qquadratic_sign_pos_2 a b c d e f g h p1 p2 H_qsign na nb nc nd ne nf
          ng nh (nR p) (nR p0) H);
       intros
        [[[[[[(Ha, (Hb, (Hc, (Hd, (He, (Hf, (Hg, Hh)))))))|
              (Ha, (Hb, (Hc, (Hd, (He, (Hf, (Hg, Hh)))))))]|
             (H_discriminate_me, _)]|
            (H_discriminate_me, _)]|
           (H_discriminate_me, _)]|
          (_, (H_discriminate_me,_))]|
         (_, (H_discriminate_me,_))];
       [ apply False_ind; generalize H_nabcd; apply Zle_not_lt;
          repeat apply Zplus_le_0_compat; assumption
       | apply Zle_neg_opp; assumption
       | discriminate H_discriminate_me
       | discriminate H_discriminate_me
       | discriminate H_discriminate_me
       | discriminate H_discriminate_me
       | discriminate H_discriminate_me ] ].

   (* np2 = (dL p0) *) 
   apply quadraticAcc_wf; solve
    [ omega
    | generalize
       (Qquadratic_sign_pos_2 a b c d e f g h p1 p2 H_qsign na nb nc nd ne nf
          ng nh (nR p) (dL p0) H);
       intros
        [[[[[[(Ha, (Hb, (Hc, (Hd, (He, (Hf, (Hg, Hh)))))))|
              (Ha, (Hb, (Hc, (Hd, (He, (Hf, (Hg, Hh)))))))]|
             (H_discriminate_me, _)]|
            (H_discriminate_me, _)]|
           (H_discriminate_me, _)]|
          (_, (H_discriminate_me,_))]|
         (_, (H_discriminate_me,_))];
       [ apply False_ind; generalize H_nabcd; apply Zle_not_lt;
          repeat apply Zplus_le_0_compat; assumption
       | apply Zle_neg_opp; assumption
       | discriminate H_discriminate_me
       | discriminate H_discriminate_me
       | discriminate H_discriminate_me
       | discriminate H_discriminate_me
       | discriminate H_discriminate_me ] ].
   (* np2=One *)
   apply quadraticacc0'.
   discriminate.
   reflexivity.
   apply homographicAcc_wf; solve
    [ omega
    | generalize
       (Qquadratic_sign_pos_2 a b c d e f g h p1 p2 H_qsign na nb nc nd ne nf
          ng nh (nR p) One H);
       intros
        [[[[[[(Ha, (Hb, (Hc, (Hd, (He, (Hf, (Hg, Hh)))))))|
              (Ha, (Hb, (Hc, (Hd, (He, (Hf, (Hg, Hh)))))))]|
             (H_discriminate_me, _)]|
            (H_discriminate_me, _)]|
           (H_discriminate_me, _)]|
          (_, (_, (Hab, (Hcd, (Hef, Hgh)))))]|
         (_, (_, (Hab, (Hcd, (Hef, Hgh)))))];
       [ apply False_ind; generalize H_nabcd; apply Zle_not_lt;
          repeat apply Zplus_le_0_compat; assumption
       | omega
       | discriminate H_discriminate_me
       | discriminate H_discriminate_me
       | discriminate H_discriminate_me
       | apply False_ind; generalize H_nabcd; apply Zle_not_lt;
          rewrite <- Zplus_assoc; apply Zplus_le_0_compat; 
          assumption
       | omega ] ].

 (* np1 = (dL p) *)
  destruct np2 as [p0| p0| ].
   (* np2 = (nR p0) *) 
   apply quadraticAcc_wf; solve
    [ omega
    | generalize
       (Qquadratic_sign_pos_2 a b c d e f g h p1 p2 H_qsign na nb nc nd ne nf
          ng nh (dL p) (nR p0) H);
       intros
        [[[[[[(Ha, (Hb, (Hc, (Hd, (He, (Hf, (Hg, Hh)))))))|
              (Ha, (Hb, (Hc, (Hd, (He, (Hf, (Hg, Hh)))))))]|
             (H_discriminate_me, _)]|
            (H_discriminate_me, _)]|
           (H_discriminate_me, _)]|
          (_, (H_discriminate_me,_))]|
         (_, (H_discriminate_me,_))];
       [ apply False_ind; generalize H_nabcd; apply Zle_not_lt;
          repeat apply Zplus_le_0_compat; assumption
       | apply Zle_neg_opp; assumption
       | discriminate H_discriminate_me
       | discriminate H_discriminate_me
       | discriminate H_discriminate_me
       | discriminate H_discriminate_me
       | discriminate H_discriminate_me ] ].
   (* np2 = (dL p0) *) 
   apply quadraticAcc_wf; solve
    [ omega
    | generalize
       (Qquadratic_sign_pos_2 a b c d e f g h p1 p2 H_qsign na nb nc nd ne nf
          ng nh (dL p) (dL p0) H);
       intros
        [[[[[[(Ha, (Hb, (Hc, (Hd, (He, (Hf, (Hg, Hh)))))))|
              (Ha, (Hb, (Hc, (Hd, (He, (Hf, (Hg, Hh)))))))]|
             (H_discriminate_me, _)]|
            (H_discriminate_me, _)]|
           (H_discriminate_me, _)]|
          (_, (H_discriminate_me,_))]|
         (_, (H_discriminate_me,_))];
       [ apply False_ind; generalize H_nabcd; apply Zle_not_lt;
          repeat apply Zplus_le_0_compat; assumption
       | apply Zle_neg_opp; assumption
       | discriminate H_discriminate_me
       | discriminate H_discriminate_me
       | discriminate H_discriminate_me
       | discriminate H_discriminate_me
       | discriminate H_discriminate_me ] ].
   (* np2=One *)
   apply quadraticacc0'.
   discriminate.
   reflexivity.
   apply homographicAcc_wf; solve
    [ omega
    | generalize
       (Qquadratic_sign_pos_2 a b c d e f g h p1 p2 H_qsign na nb nc nd ne nf
          ng nh (dL p) One H);
       intros
        [[[[[[(Ha, (Hb, (Hc, (Hd, (He, (Hf, (Hg, Hh)))))))|
              (Ha, (Hb, (Hc, (Hd, (He, (Hf, (Hg, Hh)))))))]|
             (H_discriminate_me, _)]|
            (H_discriminate_me, _)]|
           (H_discriminate_me, _)]|
          (_, (_, (Hab, (Hcd, (Hef, Hgh)))))]|
         (_, (_, (Hab, (Hcd, (Hef, Hgh)))))];
       [ apply False_ind; generalize H_nabcd; apply Zle_not_lt;
          repeat apply Zplus_le_0_compat; assumption
       | omega
       | discriminate H_discriminate_me
       | discriminate H_discriminate_me
       | discriminate H_discriminate_me
       | apply False_ind; generalize H_nabcd; apply Zle_not_lt;
          rewrite <- Zplus_assoc; apply Zplus_le_0_compat; 
          assumption
       | omega ] ].
  (* np1 = One *)
  apply quadraticacc0.
  reflexivity.
  destruct np2 as [p| p| ].
   (* np2 = (nR p) *) (* Here we use the third & forth clause in Qquadratic_sign_pos_2:  p1=One /\ .... *)
   apply homographicAcc_wf; solve
    [ omega
    | generalize
       (Qquadratic_sign_pos_2 a b c d e f g h p1 p2 H_qsign na nb nc nd ne nf
          ng nh One (nR p) H);
       intros
        [[[[[[(Ha, (Hb, (Hc, (Hd, (He, (Hf, (Hg, Hh)))))))|
              (Ha, (Hb, (Hc, (Hd, (He, (Hf, (Hg, Hh)))))))]|
             (_, (Hab, (Hcd, (Hef, Hgh))))]|
            (_, (Hab, (Hcd, (Hef, Hgh))))]|
           (_, H_discriminate_me)]|
          (_, (H_discriminate_me,_))]|
         (_, (H_discriminate_me,_))];
       [ apply False_ind; generalize H_nabcd; apply Zle_not_lt;
          repeat apply Zplus_le_0_compat; assumption
       | apply Zplus_le_0_compat; apply Zle_neg_opp; assumption
       | apply False_ind; generalize H_nabcd; apply Zle_not_lt; omega
       | rewrite <- Zopp_plus_distr; apply Zle_neg_opp; assumption
       | discriminate H_discriminate_me
       | discriminate H_discriminate_me
       | discriminate H_discriminate_me ] ].
   (* np2 = (dL p) *) (* Here we use the third & forth clause in Qquadratic_sign_pos_2:  p1=One /\ .... *)
   apply homographicAcc_wf; solve
    [ omega
    | generalize
       (Qquadratic_sign_pos_2 a b c d e f g h p1 p2 H_qsign na nb nc nd ne nf
          ng nh One (dL p) H);
       intros
        [[[[[[(Ha, (Hb, (Hc, (Hd, (He, (Hf, (Hg, Hh)))))))|
              (Ha, (Hb, (Hc, (Hd, (He, (Hf, (Hg, Hh)))))))]|
             (_, (Hab, (Hcd, (Hef, Hgh))))]|
            (_, (Hab, (Hcd, (Hef, Hgh))))]|
           (_, H_discriminate_me)]|
          (_, (H_discriminate_me,_))]|
         (_, (H_discriminate_me,_))];
       [ apply False_ind; generalize H_nabcd; apply Zle_not_lt;
          repeat apply Zplus_le_0_compat; assumption
       | apply Zplus_le_0_compat; apply Zle_neg_opp; assumption
       | apply False_ind; generalize H_nabcd; apply Zle_not_lt; omega
       | rewrite <- Zopp_plus_distr; apply Zle_neg_opp; assumption
       | discriminate H_discriminate_me
       | discriminate H_discriminate_me
       | discriminate H_discriminate_me ] ].
   (* np2 = One *)
   apply homographicacc0; reflexivity || omega. 
Qed.


Lemma Qquadratic_Qpositive_to_Q_quadraticAcc_neg_1 :
 forall (a b c d e f g h : Z) (p1 p2 : Qpositive)
   (H_Qquadratic_sg_denom_nonzero : Qquadratic_sg_denom_nonzero e f g h p1 p2),
 ~ same_ratio a b c d e f g h ->
 q_sign a b c d e f g h p1 p2 H_Qquadratic_sg_denom_nonzero = (-1)%Z ->
 Z.sgn
   (qnew_a a b c d e f g h p1 p2 H_Qquadratic_sg_denom_nonzero +
    qnew_b a b c d e f g h p1 p2 H_Qquadratic_sg_denom_nonzero +
    qnew_c a b c d e f g h p1 p2 H_Qquadratic_sg_denom_nonzero +
    qnew_d a b c d e f g h p1 p2 H_Qquadratic_sg_denom_nonzero) = 1%Z ->
 quadraticAcc (qnew_a a b c d e f g h p1 p2 H_Qquadratic_sg_denom_nonzero)
   (qnew_b a b c d e f g h p1 p2 H_Qquadratic_sg_denom_nonzero)
   (qnew_c a b c d e f g h p1 p2 H_Qquadratic_sg_denom_nonzero)
   (qnew_d a b c d e f g h p1 p2 H_Qquadratic_sg_denom_nonzero)
   (- qnew_e a b c d e f g h p1 p2 H_Qquadratic_sg_denom_nonzero)
   (- qnew_f a b c d e f g h p1 p2 H_Qquadratic_sg_denom_nonzero)
   (- qnew_g a b c d e f g h p1 p2 H_Qquadratic_sg_denom_nonzero)
   (- qnew_h a b c d e f g h p1 p2 H_Qquadratic_sg_denom_nonzero)
   (qnew_p1 a b c d e f g h p1 p2 H_Qquadratic_sg_denom_nonzero)
   (qnew_p2 a b c d e f g h p1 p2 H_Qquadratic_sg_denom_nonzero).
Proof.
 intros a b c d e f g h p1 p2 H_qsign not_same_ratio_abcdefgh l1_eq_min_one
  na_nb_nc_nd_eq_one.
 set (na := qnew_a a b c d e f g h p1 p2 H_qsign) in *.
 set (nb := qnew_b a b c d e f g h p1 p2 H_qsign) in *.
 set (nc := qnew_c a b c d e f g h p1 p2 H_qsign) in *.
 set (nd := qnew_d a b c d e f g h p1 p2 H_qsign) in *.
 set (ne := qnew_e a b c d e f g h p1 p2 H_qsign) in *.
 set (nf := qnew_f a b c d e f g h p1 p2 H_qsign) in *.
 set (ng := qnew_g a b c d e f g h p1 p2 H_qsign) in *.
 set (nh := qnew_h a b c d e f g h p1 p2 H_qsign) in *.
 set (np1 := qnew_p1 a b c d e f g h p1 p2 H_qsign) in *.
 set (np2 := qnew_p2 a b c d e f g h p1 p2 H_qsign) in *.

 assert
  (H :
   Qquadratic_sign a b c d e f g h p1 p2 H_qsign =
   ((-1)%Z, (na, (nb, (nc, nd)), (ne, (nf, (ng, nh))), (np1, np2)))).
 unfold na, nb, nc, nd, ne, nf, ng, nh, np1, np2 in |- *.
 rewrite <- l1_eq_min_one.
 unfold qnew_a, qnew_b, qnew_c, qnew_d, qnew_e, qnew_f, qnew_g, qnew_h,
  qnew_p1, qnew_p2 in |- *.
 replace (q_sign a b c d e f g h p1 p2 H_qsign) with
  (fst (Qquadratic_sign a b c d e f g h p1 p2 H_qsign));
  [ idtac | reflexivity ]; repeat rewrite <- pair_1; 
  reflexivity.


 generalize
  (Qquadratic_sign_neg_1 a b c d e f g h p1 p2 H_qsign na nb nc nd ne nf ng
     nh np1 np2 H).
 intros [(H_nabcd, H_nefgh)| (H1, _)];
  [ idtac
  | apply False_ind; generalize (Zsgn_9 _ na_nb_nc_nd_eq_one); apply Zlt_asym;
     assumption ].
 
 destruct np1 as [p| p| ].
  (* np1 = (nR p) *)
 let T_local :=
  (apply quadraticAcc_wf; solve
    [ assumption
    | omega
    | match goal with
      | id1:(?X1 = (?X2, (?X3, (?X4, nR ?X5)))) |- ?X6 =>
          generalize
           (Qquadratic_sign_neg_2 a b c d e f g h p1 p2 H_qsign na nb nc nd
              ne nf ng nh (nR p) (nR p0) H)
      | id1:(?X1 = (?X2, (?X3, (?X4, dL ?X5)))) |- ?X6 =>
          generalize
           (Qquadratic_sign_neg_2 a b c d e f g h p1 p2 H_qsign na nb nc nd
              ne nf ng nh (nR p) (dL p0) H)
      end;
       intros
        [[[[[[(Ha, (Hb, (Hc, (Hd, (He, (Hf, (Hg, Hh)))))))|
              (Ha, (Hb, (Hc, (Hd, (He, (Hf, (Hg, Hh)))))))]|
             (H_discriminate_me, _)]|
            (H_discriminate_me, _)]|
           (H_discriminate_me, _)]|
          (_, (H_discriminate_me,_))]|
         (_, (H_discriminate_me,_))];
       [ try apply Zle_neg_opp; assumption
       | apply False_ind; generalize H_nabcd; apply Zle_not_lt;
          repeat apply Zle_resp_neg; assumption
       | discriminate H_discriminate_me
       | discriminate H_discriminate_me
       | discriminate H_discriminate_me
       | discriminate H_discriminate_me
       | discriminate H_discriminate_me ] ]) in
 (destruct np2 as [p0| p0| ];
   [  (* np2 = (nR p0)*) T_local |  (* np2 = (dL p0) *) T_local | idtac ]).

   (* np2=One *)
   apply quadraticacc0'.
   discriminate.
   reflexivity. 
   apply homographicAcc_wf; solve
    [ omega
    | generalize
       (Qquadratic_sign_neg_2 a b c d e f g h p1 p2 H_qsign na nb nc nd ne nf
          ng nh (nR p) One H);
       intros
        [[[[[[(Ha, (Hb, (Hc, (Hd, (He, (Hf, (Hg, Hh)))))))|
              (Ha, (Hb, (Hc, (Hd, (He, (Hf, (Hg, Hh)))))))]|
             (H_discriminate_me, _)]|
            (H_discriminate_me, _)]|
           (H_discriminate_me, _)]|
          (_, (_, (Hab, (Hcd, (Hef, Hgh)))))]|
         (_, (_, (Hab, (Hcd, (Hef, Hgh)))))];
       [ apply Zplus_le_0_compat; try apply Zle_neg_opp; assumption
       | apply False_ind; generalize H_nabcd; apply Zle_not_lt;
          repeat apply Zle_resp_neg; assumption
       | discriminate H_discriminate_me
       | discriminate H_discriminate_me
       | discriminate H_discriminate_me
       | assumption ||
           (rewrite <- Zopp_plus_distr; apply Zle_neg_opp; assumption)
       | apply False_ind; generalize H_nabcd; apply Zle_not_lt;
          rewrite <- Zplus_assoc; apply Zle_resp_neg; 
          assumption ] ].
  (* np1 = (dL p) *)
  let T_local :=
   (apply quadraticAcc_wf; solve
     [ assumption
     | omega
     | match goal with
       | id1:(?X1 = (?X2, (?X3, (?X4, nR ?X5)))) |- ?X6 =>
           generalize
            (Qquadratic_sign_neg_2 a b c d e f g h p1 p2 H_qsign na nb nc nd
               ne nf ng nh (dL p) (nR p0) H)
       | id1:(?X1 = (?X2, (?X3, (?X4, dL ?X5)))) |- ?X6 =>
           generalize
            (Qquadratic_sign_neg_2 a b c d e f g h p1 p2 H_qsign na nb nc nd
               ne nf ng nh (dL p) (dL p0) H)
       end;
        intros
         [[[[[[(Ha, (Hb, (Hc, (Hd, (He, (Hf, (Hg, Hh)))))))|
               (Ha, (Hb, (Hc, (Hd, (He, (Hf, (Hg, Hh)))))))]|
              (H_discriminate_me, _)]|
             (H_discriminate_me, _)]|
            (H_discriminate_me, _)]|
           (_, (H_discriminate_me,_))]|
          (_, (H_discriminate_me,_))];
        [ try apply Zle_neg_opp; assumption
        | apply False_ind; generalize H_nabcd; apply Zle_not_lt;
           repeat apply Zle_resp_neg; assumption
        | discriminate H_discriminate_me
        | discriminate H_discriminate_me
        | discriminate H_discriminate_me
        | discriminate H_discriminate_me
        | discriminate H_discriminate_me ] ]) in
  (destruct np2 as [p0| p0| ];
    [  (* np2 = (nR p0)*) T_local |  (* np2 = (dL p0) *) T_local | idtac ]).
  (* np2=One *)
   apply quadraticacc0'.
   discriminate.
   reflexivity.
   apply homographicAcc_wf; solve
    [ rewrite Zplus_assoc; assumption || omega
    | generalize
       (Qquadratic_sign_neg_2 a b c d e f g h p1 p2 H_qsign na nb nc nd ne nf
          ng nh (dL p) One H);
       intros
        [[[[[[(Ha, (Hb, (Hc, (Hd, (He, (Hf, (Hg, Hh)))))))|
              (Ha, (Hb, (Hc, (Hd, (He, (Hf, (Hg, Hh)))))))]|
             (H_discriminate_me, _)]|
            (H_discriminate_me, _)]|
           (H_discriminate_me, _)]|
          (_, (_, (Hab, (Hcd, (Hef, Hgh)))))]|
         (_, (_, (Hab, (Hcd, (Hef, Hgh)))))];
       [ apply Zplus_le_0_compat; try apply Zle_neg_opp; assumption
       | apply False_ind; generalize H_nabcd; apply Zle_not_lt;
          repeat apply Zle_resp_neg; assumption
       | discriminate H_discriminate_me
       | discriminate H_discriminate_me
       | discriminate H_discriminate_me
       | assumption ||
           (rewrite <- Zopp_plus_distr; apply Zle_neg_opp; assumption)
       | apply False_ind; generalize H_nabcd; apply Zle_not_lt;
          rewrite <- Zplus_assoc; apply Zle_resp_neg; 
          assumption ] ].

  (* np1 = One *)
  apply quadraticacc0.
  reflexivity.
  let T_local :=
   (apply homographicAcc_wf; solve
     [ omega
     | match goal with
       | id1:(?X1 = (?X2, (?X3, (?X4, nR ?X5)))) |- ?X6 =>
           generalize
            (Qquadratic_sign_neg_2 a b c d e f g h p1 p2 H_qsign na nb nc nd
               ne nf ng nh One (nR p) H)
       | id1:(?X1 = (?X2, (?X3, (?X4, dL ?X5)))) |- ?X6 =>
           generalize
            (Qquadratic_sign_neg_2 a b c d e f g h p1 p2 H_qsign na nb nc nd
               ne nf ng nh One (dL p) H)
       end;
        intros
         [[[[[[(Ha, (Hb, (Hc, (Hd, (He, (Hf, (Hg, Hh)))))))|
               (Ha, (Hb, (Hc, (Hd, (He, (Hf, (Hg, Hh)))))))]|
              (_, (Hab, (Hcd, (Hef, Hgh))))]|
             (_, (Hab, (Hcd, (Hef, Hgh))))]|
            (_, H_discriminate_me)]|
           (_, (H_discriminate_me,_))]|
          (_, (H_discriminate_me,_))];
        [ apply Zplus_le_0_compat; try apply Zle_neg_opp; assumption
        | apply False_ind; generalize H_nabcd; apply Zle_not_lt;
           repeat apply Zle_resp_neg; assumption
        | assumption ||
            (rewrite <- Zopp_plus_distr; apply Zle_neg_opp; assumption)
        | apply False_ind; generalize H_nabcd; apply Zle_not_lt; omega
        | discriminate H_discriminate_me
        | discriminate H_discriminate_me
        | discriminate H_discriminate_me ] ]) in
  (destruct np2 as [p| p| ];
    [  (* np2 = (nR p)*) T_local
    |  (* np2 = (dL p) *) T_local
    |  (* Here we use the third clause in Qquadratic_sign_neg_2:  p1=One /\ .... *) 
       (* np2 = One *)
       apply homographicacc0; reflexivity || omega ]). 
Qed.



Lemma Qquadratic_Qpositive_to_Q_quadraticAcc_neg_2 :
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
 quadraticAcc (- qnew_a a b c d e f g h p1 p2 H_Qquadratic_sg_denom_nonzero)
   (- qnew_b a b c d e f g h p1 p2 H_Qquadratic_sg_denom_nonzero)
   (- qnew_c a b c d e f g h p1 p2 H_Qquadratic_sg_denom_nonzero)
   (- qnew_d a b c d e f g h p1 p2 H_Qquadratic_sg_denom_nonzero)
   (qnew_e a b c d e f g h p1 p2 H_Qquadratic_sg_denom_nonzero)
   (qnew_f a b c d e f g h p1 p2 H_Qquadratic_sg_denom_nonzero)
   (qnew_g a b c d e f g h p1 p2 H_Qquadratic_sg_denom_nonzero)
   (qnew_h a b c d e f g h p1 p2 H_Qquadratic_sg_denom_nonzero)
   (qnew_p1 a b c d e f g h p1 p2 H_Qquadratic_sg_denom_nonzero)
   (qnew_p2 a b c d e f g h p1 p2 H_Qquadratic_sg_denom_nonzero).
Proof.
 intros a b c d e f g h p1 p2 H_qsign not_same_ratio_abcdefgh l1_eq_min_one
  na_nb_nc_nd_eq_minus_one.
 set (na := qnew_a a b c d e f g h p1 p2 H_qsign) in *.
 set (nb := qnew_b a b c d e f g h p1 p2 H_qsign) in *.
 set (nc := qnew_c a b c d e f g h p1 p2 H_qsign) in *.
 set (nd := qnew_d a b c d e f g h p1 p2 H_qsign) in *.
 set (ne := qnew_e a b c d e f g h p1 p2 H_qsign) in *.
 set (nf := qnew_f a b c d e f g h p1 p2 H_qsign) in *.
 set (ng := qnew_g a b c d e f g h p1 p2 H_qsign) in *.
 set (nh := qnew_h a b c d e f g h p1 p2 H_qsign) in *.
 set (np1 := qnew_p1 a b c d e f g h p1 p2 H_qsign) in *.
 set (np2 := qnew_p2 a b c d e f g h p1 p2 H_qsign) in *.

 assert
  (H :
   Qquadratic_sign a b c d e f g h p1 p2 H_qsign =
   ((-1)%Z, (na, (nb, (nc, nd)), (ne, (nf, (ng, nh))), (np1, np2)))).
 unfold na, nb, nc, nd, ne, nf, ng, nh, np1, np2 in |- *.
 rewrite <- l1_eq_min_one.
 unfold qnew_a, qnew_b, qnew_c, qnew_d, qnew_e, qnew_f, qnew_g, qnew_h,
  qnew_p1, qnew_p2 in |- *.
 replace (q_sign a b c d e f g h p1 p2 H_qsign) with
  (fst (Qquadratic_sign a b c d e f g h p1 p2 H_qsign));
  [ idtac | reflexivity ]; repeat rewrite <- pair_1; 
  reflexivity.

 generalize
  (Qquadratic_sign_neg_1 a b c d e f g h p1 p2 H_qsign na nb nc nd ne nf ng
     nh np1 np2 H).
 intros [(H1, _)| (H_nabcd, H_nefgh)];
  [ apply False_ind; generalize (Zsgn_10 _ na_nb_nc_nd_eq_minus_one);
     apply Zlt_asym; assumption
  | idtac ].
 
 destruct np1 as [p| p| ].
  (* np1 = (nR p) *)
  let T_local :=
   (apply quadraticAcc_wf; solve
     [ assumption || omega
     | match goal with
       | id1:(?X1 = (?X2, (?X3, (?X4, nR ?X5)))) |- ?X6 =>
           generalize
            (Qquadratic_sign_neg_2 a b c d e f g h p1 p2 H_qsign na nb nc nd
               ne nf ng nh (nR p) (nR p0) H)
       | id1:(?X1 = (?X2, (?X3, (?X4, dL ?X5)))) |- ?X6 =>
           generalize
            (Qquadratic_sign_neg_2 a b c d e f g h p1 p2 H_qsign na nb nc nd
               ne nf ng nh (nR p) (dL p0) H)
       end;
        intros
         [[[[[[(Ha, (Hb, (Hc, (Hd, (He, (Hf, (Hg, Hh)))))))|
               (Ha, (Hb, (Hc, (Hd, (He, (Hf, (Hg, Hh)))))))]|
              (H_discriminate_me, _)]|
             (H_discriminate_me, _)]|
            (H_discriminate_me, _)]|
           (_, (H_discriminate_me,_))]|
          (_, (H_discriminate_me,_))];
        [ apply False_ind; generalize H_nabcd; apply Zle_not_lt;
           repeat apply Zplus_le_0_compat; assumption
        | try apply Zle_neg_opp; assumption
        | discriminate H_discriminate_me
        | discriminate H_discriminate_me
        | discriminate H_discriminate_me
        | discriminate H_discriminate_me
        | discriminate H_discriminate_me ] ]) in
  (destruct np2 as [p0| p0| ];
    [  (* np2 = (nR p0)*) T_local |  (* np2 = (dL p0) *) T_local | idtac ]).

   (* np2=One *)
   apply quadraticacc0'.
   discriminate.
   reflexivity.
   apply homographicAcc_wf; solve
    [ omega
    | generalize
       (Qquadratic_sign_neg_2 a b c d e f g h p1 p2 H_qsign na nb nc nd ne nf
          ng nh (nR p) One H);
       intros
        [[[[[[(Ha, (Hb, (Hc, (Hd, (He, (Hf, (Hg, Hh)))))))|
              (Ha, (Hb, (Hc, (Hd, (He, (Hf, (Hg, Hh)))))))]|
             (H_discriminate_me, _)]|
            (H_discriminate_me, _)]|
           (H_discriminate_me, _)]|
          (_, (_, (Hab, (Hcd, (Hef, Hgh)))))]|
         (_, (_, (Hab, (Hcd, (Hef, Hgh)))))];
       [ apply False_ind; generalize H_nabcd; apply Zle_not_lt;
          repeat apply Zplus_le_0_compat; assumption
       | apply Zplus_le_0_compat; try apply Zle_neg_opp; assumption
       | discriminate H_discriminate_me
       | discriminate H_discriminate_me
       | discriminate H_discriminate_me
       | apply False_ind; generalize H_nabcd; apply Zle_not_lt;
          rewrite <- Zplus_assoc; apply Zplus_le_0_compat; 
          assumption
       | assumption ||
           (rewrite <- Zopp_plus_distr; apply Zle_neg_opp; assumption) ] ].

 (* np1 = (dL p0) *)
  let T_local :=
   (apply quadraticAcc_wf; solve
     [ assumption || omega
     | match goal with
       | id1:(?X1 = (?X2, (?X3, (?X4, nR ?X5)))) |- ?X6 =>
           generalize
            (Qquadratic_sign_neg_2 a b c d e f g h p1 p2 H_qsign na nb nc nd
               ne nf ng nh (dL p) (nR p0) H)
       | id1:(?X1 = (?X2, (?X3, (?X4, dL ?X5)))) |- ?X6 =>
           generalize
            (Qquadratic_sign_neg_2 a b c d e f g h p1 p2 H_qsign na nb nc nd
               ne nf ng nh (dL p) (dL p0) H)
       end;
        intros
         [[[[[[(Ha, (Hb, (Hc, (Hd, (He, (Hf, (Hg, Hh)))))))|
               (Ha, (Hb, (Hc, (Hd, (He, (Hf, (Hg, Hh)))))))]|
              (H_discriminate_me, _)]|
             (H_discriminate_me, _)]|
            (H_discriminate_me, _)]|
           (_, (H_discriminate_me,_))]|
          (_, (H_discriminate_me,_))];
        [ apply False_ind; generalize H_nabcd; apply Zle_not_lt;
           repeat apply Zplus_le_0_compat; assumption
        | try apply Zle_neg_opp; assumption
        | discriminate H_discriminate_me
        | discriminate H_discriminate_me
        | discriminate H_discriminate_me
        | discriminate H_discriminate_me
        | discriminate H_discriminate_me ] ]) in
  (destruct np2 as [p0| p0| ];
    [  (* np2 = (nR p0)*) T_local |  (* np2 = (dL p0) *) T_local | idtac ]).

   (* np2=One *)
   apply quadraticacc0'.
   discriminate.
   reflexivity.
   apply homographicAcc_wf; solve
    [ rewrite Zplus_assoc; assumption || omega
    | generalize
       (Qquadratic_sign_neg_2 a b c d e f g h p1 p2 H_qsign na nb nc nd ne nf
          ng nh (dL p) One H);
       intros
        [[[[[[(Ha, (Hb, (Hc, (Hd, (He, (Hf, (Hg, Hh)))))))|
              (Ha, (Hb, (Hc, (Hd, (He, (Hf, (Hg, Hh)))))))]|
             (H_discriminate_me, _)]|
            (H_discriminate_me, _)]|
           (H_discriminate_me, _)]|
          (_, (_, (Hab, (Hcd, (Hef, Hgh)))))]|
         (_, (_, (Hab, (Hcd, (Hef, Hgh)))))];
       [ apply False_ind; generalize H_nabcd; apply Zle_not_lt;
          repeat apply Zplus_le_0_compat; assumption
       | apply Zplus_le_0_compat; try apply Zle_neg_opp; assumption
       | discriminate H_discriminate_me
       | discriminate H_discriminate_me
       | discriminate H_discriminate_me
       | apply False_ind; generalize H_nabcd; apply Zle_not_lt;
          rewrite <- Zplus_assoc; apply Zplus_le_0_compat; 
          assumption
       | assumption ||
           (rewrite <- Zopp_plus_distr; apply Zle_neg_opp; assumption) ] ].

  (* np1 = One *)
  apply quadraticacc0.
  reflexivity.
  let T_local :=
   (apply homographicAcc_wf;
     try solve
      [ omega
      | match goal with
        | id1:(?X1 = (?X2, (?X3, (?X4, nR ?X5)))) |- ?X6 =>
            generalize
             (Qquadratic_sign_neg_2 a b c d e f g h p1 p2 H_qsign na nb nc nd
                ne nf ng nh One (nR p) H)
        | id1:(?X1 = (?X2, (?X3, (?X4, dL ?X5)))) |- ?X6 =>
            generalize
             (Qquadratic_sign_neg_2 a b c d e f g h p1 p2 H_qsign na nb nc nd
                ne nf ng nh One (dL p) H)
        end;
         intros
          [[[[[[(Ha, (Hb, (Hc, (Hd, (He, (Hf, (Hg, Hh)))))))|
                (Ha, (Hb, (Hc, (Hd, (He, (Hf, (Hg, Hh)))))))]|
               (_, (Hab, (Hcd, (Hef, Hgh))))]|
              (_, (Hab, (Hcd, (Hef, Hgh))))]|
             (_, H_discriminate_me)]|
            (_, (H_discriminate_me,_))]|
           (_, (H_discriminate_me,_))];
         [ apply False_ind; generalize H_nabcd; apply Zle_not_lt;
            repeat apply Zplus_le_0_compat; assumption
         | apply Zplus_le_0_compat; try apply Zle_neg_opp; assumption
         | apply False_ind; generalize H_nabcd; apply Zle_not_lt; omega
         | assumption ||
             (rewrite <- Zopp_plus_distr; apply Zle_neg_opp; assumption)
         | discriminate H_discriminate_me
         | discriminate H_discriminate_me
         | discriminate H_discriminate_me ] ]) in
  (destruct np2 as [p| p| ];
    [  (* np2 = (nR p)*) T_local
    |  (* np2 = (dL p) *) T_local
    |  (* Here we use the third clause in Qquadratic_sign_neg_2:  p1=One /\ .... *) 
       (* np2 = One *)
       apply homographicacc0; reflexivity || omega ]).
Qed.
