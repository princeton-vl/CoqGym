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



(**
-- These are arithmetic operations on signed Stern-Brocot numbers 
Qplus_lazy :: [Char] -> [Char] -> [Char]
Qplus_lazy = Qquadratic 0 1 1 0 0 0 0 1 
Qmult_lazy :: [Char] -> [Char] -> [Char]
Qmult_lazy = Qquadratic 1 0 0 0 0 0 0 1
Qdiv_lazy :: [Char] -> [Char] -> [Char]
Qdiv_lazy = Qquadratic 0 1 0 0 0 0 1 0 
Qminus_lazy :: [Char] -> [Char] -> [Char]
Qminus_lazy = Qquadratic 0 1 (-1) 0 0 0 0 1
*) 

Require Export Qhomographic.
Require Export quadraticAcc_Qquadratic_sign.
Require Import general_Q Zaux.


Lemma Qquadratic_sg_denom_nonzero_always :
 forall (k e f g h : Z) (p1 p2 : Qpositive),
 k <> 0%Z ->
 (0 < e)%Z ->
 (0 < f)%Z ->
 (0 < g)%Z ->
 (0 < h)%Z ->
 Qquadratic_sg_denom_nonzero (k * e) (k * f) (k * g) (k * h) p1 p2.
Proof.
 intros k e f g h p1 p2 Hk He Hf Hg Hh.
 generalize e f g h He Hf Hg Hh p2.  
 induction p1.
 (* p1 = (nR p1) *)
  intros.
  case p0.
  (* p2 = (nR p2) *)
  intros.
  apply Qquadratic_signok1.
  replace (k * e0 + k * f0 + k * g0 + k * h0)%Z with
   (k * (e0 + f0 + g0 + h0))%Z;
   try replace (k * e0 + k * f0)%Z with (k * (e0 + f0))%Z;
   try replace (k * e0 + k * g0)%Z with (k * (e0 + g0))%Z; 
   try apply IHp1; try first [ assumption | repeat apply Zlt_resp_pos ];
   try assumption;
   repeat match goal with
          |  |- (?X1 = ?X2) => abstract ring
          end. 
  intros.
  apply Qquadratic_signok2.
  replace (k * e0 + k * f0 + k * g0 + k * h0)%Z with
   (k * (e0 + f0 + g0 + h0))%Z;
   try replace (k * e0 + k * f0)%Z with (k * (e0 + f0))%Z;
   try replace (k * f0 + k * h0)%Z with (k * (f0 + h0))%Z; 
   try apply IHp1; try first [ assumption | repeat apply Zlt_resp_pos ];
   try assumption;
   repeat match goal with
          |  |- (?X1 = ?X2) => abstract ring
          end. 
  apply Qquadratic_signok0.
  reflexivity.
  replace (k * e0 + k * f0)%Z with ((e0 + f0) * k)%Z;
   try replace (k * g0 + k * h0)%Z with ((g0 + h0) * k)%Z;
   try apply Qhomographic_sg_denom_nonzero_always_1;
   try first [ assumption | repeat apply Zlt_resp_pos ]; 
   try assumption;
   repeat match goal with
          |  |- (?X1 = ?X2) => abstract ring
          end.
 (* p1 = (dL p1) *)
  intros.
  case p0.  
  intros.
  apply Qquadratic_signok3.
  replace (k * e0 + k * f0 + k * g0 + k * h0)%Z with
   (k * (e0 + f0 + g0 + h0))%Z;
   try replace (k * g0 + k * h0)%Z with (k * (g0 + h0))%Z;
   try replace (k * e0 + k * g0)%Z with (k * (e0 + g0))%Z; 
   try apply IHp1; try first [ assumption | repeat apply Zlt_resp_pos ];
   try assumption;
   repeat match goal with
          |  |- (?X1 = ?X2) => abstract ring
          end. 
  intros.
  apply Qquadratic_signok4.
  replace (k * e0 + k * f0 + k * g0 + k * h0)%Z with
   (k * (e0 + f0 + g0 + h0))%Z;
   try replace (k * g0 + k * h0)%Z with (k * (g0 + h0))%Z;
   try replace (k * f0 + k * h0)%Z with (k * (f0 + h0))%Z; 
   try apply IHp1; try first [ assumption | repeat apply Zlt_resp_pos ];
   try assumption;
   repeat match goal with
          |  |- (?X1 = ?X2) => abstract ring
          end. 
  apply Qquadratic_signok0.
  reflexivity.
  replace (k * e0 + k * f0)%Z with ((e0 + f0) * k)%Z;
   try replace (k * g0 + k * h0)%Z with ((g0 + h0) * k)%Z;
   try apply Qhomographic_sg_denom_nonzero_always_1;
   try first [ assumption | repeat apply Zlt_resp_pos ]; 
   try assumption;
   repeat match goal with
          |  |- (?X1 = ?X2) => abstract ring
          end.
 (* p1 = One *)
 intros. 
 apply Qquadratic_signok0'.
 reflexivity.
 replace (k * e0 + k * g0)%Z with ((e0 + g0) * k)%Z;
  try replace (k * f0 + k * h0)%Z with ((f0 + h0) * k)%Z;
  try apply Qhomographic_sg_denom_nonzero_always_1;
  try first [ assumption | repeat apply Zlt_resp_pos ]; 
  try assumption; repeat match goal with
                         |  |- (?X1 = ?X2) => abstract ring
                         end.
Defined.



Lemma Qquadratic_sg_denom_nonzero_Zero_Zero_always :
 forall (k g h : Z) (p1 p2 : Qpositive),
 k <> 0%Z ->
 (0 < g)%Z ->
 (0 < h)%Z -> Qquadratic_sg_denom_nonzero 0 0 (k * g) (k * h) p1 p2.
Proof.
 intros k g h p1 p2 Hk Hg Hh.
 generalize g h Hg Hh p2. 
 induction p1.
  (* p1 = (nR p1) *)
  intros.
  case p0.
   intro p3.
   apply Qquadratic_signok1.
   simpl in |- *.   
   replace (k * g0 + k * h0)%Z with (k * (g0 + h0))%Z;
    [ apply IHp1; try first [ assumption | repeat apply Zlt_resp_pos ];
       try assumption
    | abstract ring ].
   
   intro p3.
   apply Qquadratic_signok2.
   simpl in |- *.
   replace (k * g0 + k * h0)%Z with (k * (g0 + h0))%Z;
    [ apply IHp1; try first [ assumption | repeat apply Zlt_resp_pos ];
       try assumption
    | abstract ring ].
   
   apply Qquadratic_signok0.
   reflexivity.
   simpl in |- *.
   apply Qhomographic_sg_denom_nonzero_Zero_always.
   replace (k * g0 + k * h0)%Z with (k * (g0 + h0))%Z.
   intro.
   apply Hk.
   apply Zmult_integral_l with (g0 + h0)%Z.
   apply sym_not_eq.
   apply Zorder.Zlt_not_eq.
   apply Zlt_resp_pos; assumption.
   assumption.
   abstract ring.
   
  intros.
   case p0.
   intro p3.
   apply Qquadratic_signok3.
   simpl in |- *.   
   replace (k * g0 + k * h0)%Z with (k * (g0 + h0))%Z;
    [ apply Qquadratic_sg_denom_nonzero_always;
       try first [ assumption | repeat apply Zlt_resp_pos ]; 
       try assumption
    | abstract ring ].
   
   intro p3.
   apply Qquadratic_signok4.
   simpl in |- *.
   replace (k * g0 + k * h0)%Z with (k * (g0 + h0))%Z;
    [ apply Qquadratic_sg_denom_nonzero_always;
       try first [ assumption | repeat apply Zlt_resp_pos ]; 
       try assumption
    | abstract ring ].
   
   apply Qquadratic_signok0.
   reflexivity.
   simpl in |- *.
   apply Qhomographic_sg_denom_nonzero_Zero_always.
   replace (k * g0 + k * h0)%Z with (k * (g0 + h0))%Z.
   intro.
   apply Hk.
   apply Zmult_integral_l with (g0 + h0)%Z.
   apply sym_not_eq.
   apply Zorder.Zlt_not_eq.
   apply Zlt_resp_pos; assumption.
   assumption.
   abstract ring.

  intros.
  apply Qquadratic_signok0'.
  reflexivity.
  simpl in |- *.
  rewrite Zmult_comm with k h0.
  rewrite Zmult_comm with k g0.
  apply Qhomographic_sg_denom_nonzero_always_1; assumption.
Defined.


Lemma Qquadratic_sg_denom_nonzero_Zero_always_Zero_always :
 forall (k f h : Z) (p1 p2 : Qpositive),
 k <> 0%Z ->
 (0 < f)%Z ->
 (0 < h)%Z -> Qquadratic_sg_denom_nonzero 0 (k * f) 0 (k * h) p1 p2.
Proof.
 intros k f h p1 p2 Hk Hf Hh.
 generalize f h Hf Hh p2. 
 abstract (induction p1; intros;
            [ 
               (* p1 = (nR p1) *)
               destruct p0 as [q| q| ];
               [ apply Qquadratic_signok1; simpl in |- *; rewrite Zplus_0_r;
                  rewrite <- Zmult_plus_distr_r with k f0 h0; 
                  apply IHp1
               | apply Qquadratic_signok2; simpl in |- *; rewrite Zplus_0_r;
                  rewrite <- Zmult_plus_distr_r with k f0 h0;
                  apply Qquadratic_sg_denom_nonzero_always
               | apply Qquadratic_signok0;
                  [ reflexivity
                  | simpl in |- *; rewrite Zmult_comm;
                     rewrite Zmult_comm with k h0;
                     apply Qhomographic_sg_denom_nonzero_always_1 ] ]
            | 
               (* p1 = (dL p1) *)
               destruct p0 as [q| q| ];
               [ apply Qquadratic_signok3; simpl in |- *; rewrite Zplus_0_r;
                  rewrite <- Zmult_plus_distr_r with k f0 h0; 
                  apply IHp1
               | apply Qquadratic_signok4; simpl in |- *; rewrite Zplus_0_r;
                  rewrite <- Zmult_plus_distr_r with k f0 h0;
                  apply Qquadratic_sg_denom_nonzero_always
               | apply Qquadratic_signok0;
                  [ reflexivity
                  | simpl in |- *; rewrite Zmult_comm;
                     rewrite Zmult_comm with k h0;
                     apply Qhomographic_sg_denom_nonzero_always_1 ] ]
            | 
               (* p1 = One *)
               apply Qquadratic_signok0';
               [ reflexivity
               | simpl in |- *; rewrite <- Zmult_plus_distr_r with k f0 h0;
                  apply Qhomographic_sg_denom_nonzero_Zero_always;
                  apply Zmult_resp_nonzero;
                  [ idtac
                  | apply sym_not_eq; apply Zorder.Zlt_not_eq;
                     apply Zlt_resp_pos ] ] ];
            try first [ assumption | repeat apply Zlt_resp_pos ]; 
            assumption).
Defined.

Lemma Qquadratic_sg_denom_nonzero_always_Zero_always_Zero :
 forall (k e g : Z) (p1 p2 : Qpositive),
 k <> 0%Z ->
 (0 < e)%Z ->
 (0 < g)%Z -> Qquadratic_sg_denom_nonzero (k * e) 0 (k * g) 0 p1 p2.
Proof.
 intros k e g p1 p2 Hk He Hg.
 generalize e g He Hg p2. 
 abstract (induction p1; intros;
            [ 
               (* p1 = (nR p1) *)
               destruct p0 as [q| q| ];
               [ apply Qquadratic_signok1; simpl in |- *;
                  repeat rewrite Zplus_0_r;
                  rewrite <- Zmult_plus_distr_r with k e0 g0;
                  apply Qquadratic_sg_denom_nonzero_always
               | apply Qquadratic_signok2; simpl in |- *;
                  repeat rewrite Zplus_0_r;
                  rewrite <- Zmult_plus_distr_r with k e0 g0; 
                  apply IHp1
               | apply Qquadratic_signok0;
                  [ reflexivity
                  | repeat rewrite Zplus_0_r; rewrite Zmult_comm;
                     rewrite Zmult_comm with k g0;
                     apply Qhomographic_sg_denom_nonzero_always_1 ] ]
            | 
               (* p1 = (dL p1) *)
               destruct p0 as [q| q| ];
               [ apply Qquadratic_signok3; simpl in |- *;
                  repeat rewrite Zplus_0_r;
                  rewrite <- Zmult_plus_distr_r with k e0 g0;
                  apply Qquadratic_sg_denom_nonzero_always
               | apply Qquadratic_signok4; simpl in |- *;
                  repeat rewrite Zplus_0_r;
                  rewrite <- Zmult_plus_distr_r with k e0 g0; 
                  apply IHp1
               | apply Qquadratic_signok0;
                  [ reflexivity
                  | repeat rewrite Zplus_0_r; rewrite Zmult_comm;
                     rewrite Zmult_comm with k g0;
                     apply Qhomographic_sg_denom_nonzero_always_1 ] ]
            | 
               (* p1 = One *)
               apply Qquadratic_signok0';
               [ reflexivity
               | simpl in |- *; rewrite <- Zmult_plus_distr_r with k e0 g0;
                  apply Qhomographic_sg_denom_nonzero_always_Zero;
                  apply Zmult_resp_nonzero;
                  [ idtac
                  | apply sym_not_eq; apply Zorder.Zlt_not_eq;
                     apply Zlt_resp_pos ] ] ];
            assumption || (try apply Zlt_resp_pos); 
            assumption).
Defined.


Lemma Qquadratic_sg_denom_nonzero_Zero_Zero_Zero_always :
 forall (h : Z) (p1 p2 : Qpositive),
 h <> 0%Z -> Qquadratic_sg_denom_nonzero 0 0 0 h p1 p2.
Proof.
 intros h p1 p2 Hh.
 generalize h Hh p2. 
 abstract (induction p1; intros;
            [ (* p1 = (nR p1) *)
               destruct p0 as [q| q| ];
               [ apply Qquadratic_signok1; simpl in |- *; apply IHp1;
                  assumption
               | apply Qquadratic_signok2; simpl in |- *;
                  rewrite <- Zmult_1_r with h0;
                  apply Qquadratic_sg_denom_nonzero_Zero_Zero_always
               | apply Qquadratic_signok0 ]
            | (* p1 = (dL p1) *)
               destruct p0 as [q| q| ];
               [ apply Qquadratic_signok3; simpl in |- *;
                  rewrite <- Zmult_1_r with h0;
                  apply Qquadratic_sg_denom_nonzero_Zero_always_Zero_always
               | apply Qquadratic_signok4; simpl in |- *;
                  rewrite <- Zmult_1_r with h0;
                  apply Qquadratic_sg_denom_nonzero_always
               | apply Qquadratic_signok0 ]
            |  (* p1 = One *)
               apply Qquadratic_signok0';
               [ constructor
               | simpl in |- *;
                  apply Qhomographic_sg_denom_nonzero_Zero_always; 
                  assumption ] ]; simpl in |- *;
            try apply Qhomographic_sg_denom_nonzero_Zero_always;
            assumption || (try constructor)).
Defined.


(* Note that p2 <> 0 so the following should be provable *)
Lemma Qquadratic_sg_denom_nonzero_Zero_Zero_always_Zero :
 forall (g : Z) (p1 p2 : Qpositive),
 g <> 0%Z -> Qquadratic_sg_denom_nonzero 0 0 g 0 p1 p2.
Proof.
 intros g p1 p2 Hg.
 generalize g Hg p2. 
 abstract (induction p1; intros;
            [ (* p1 = (nR p1) *)
               destruct p0 as [q| q| ];
               [ apply Qquadratic_signok1; simpl in |- *; rewrite Zplus_0_r;
                  rewrite <- Zmult_1_r with g0;
                  apply Qquadratic_sg_denom_nonzero_Zero_Zero_always
               | apply Qquadratic_signok2; simpl in |- *; rewrite Zplus_0_r;
                  apply IHp1; assumption
               | apply Qquadratic_signok0 ]
            | (* p1 = (dL p1) *)
               destruct p0 as [q| q| ];
               [ apply Qquadratic_signok3; simpl in |- *; rewrite Zplus_0_r;
                  rewrite <- Zmult_1_r with g0;
                  apply Qquadratic_sg_denom_nonzero_always
               | apply Qquadratic_signok4; simpl in |- *; rewrite Zplus_0_r;
                  rewrite <- Zmult_1_r with g0;
                  apply Qquadratic_sg_denom_nonzero_always_Zero_always_Zero
               | apply Qquadratic_signok0 ]
            |  (* p1 = One *)
               apply Qquadratic_signok0';
               [ constructor
               | simpl in |- *;
                  apply Qhomographic_sg_denom_nonzero_always_Zero; 
                  assumption ] ]; simpl in |- *; try rewrite Zplus_0_r;
            try apply Qhomographic_sg_denom_nonzero_Zero_always;
            assumption || (try constructor)).
Defined.

Lemma Qquadratic_sg_denom_nonzero_nonzero :
 forall (e f g h : Z) (p1 p2 : Qpositive),
 e = 0%Z ->
 f = 0%Z -> g = 0%Z -> h = 0%Z -> ~ Qquadratic_sg_denom_nonzero e f g h p1 p2.
Proof.
 intros e f g h p1 p2 He Hf Hg Hh H_Qquadratic_sg_denom_nonzero.
 generalize He Hf Hg Hh.
 elim H_Qquadratic_sg_denom_nonzero; intros; first
  [ refine
     (Qhomographic_sg_denom_nonzero_nonzero (e0 + f0) (g0 + h0) p0 _ _ H0)
  | refine
     (Qhomographic_sg_denom_nonzero_nonzero (e0 + g0) (f0 + h0) p3 _ _ H0)
  | apply H0 ];
  repeat match goal with
         | id1:(?X1 = ?X2) |- ?X3 => rewrite id1
         end; constructor.
Defined.

 
Lemma Qquadratic_sg_denom_nonzero_nonzero_1 :
 forall (e f g h : Z) (p1 p2 : Qpositive),
 Qquadratic_sg_denom_nonzero e f g h p1 p2 ->
 ~ (e = 0%Z /\ f = 0%Z /\ g = 0%Z /\ h = 0%Z).
Proof.
 intros e f g h p1 p2 H_Qquadratic_sg_denom_nonzero (He, (Hf, (Hg, Hh))). 
 exact
  (Qquadratic_sg_denom_nonzero_nonzero e f g h p1 p2 He Hf Hg Hh
     H_Qquadratic_sg_denom_nonzero).
Defined. 

Lemma Qquadratic_sg_denom_nonzero_nonzero_inf :
 forall (e f g h : Z) (p1 p2 : Qpositive),
 Qquadratic_sg_denom_nonzero e f g h p1 p2 ->
 {e <> 0%Z} + {f <> 0%Z} + {g <> 0%Z} + {h <> 0%Z}.
Proof.
 intros e f g h p1 p2 H_Qquadratic_sg_denom_nonzero.
 case (Z_zerop e);
  [ case (Z_zerop f);
     [ case (Z_zerop g);
        [ case (Z_zerop h);
           [ intros; apply False_rec;
              apply
               (Qquadratic_sg_denom_nonzero_nonzero_1 e f g h p1 p2
                  H_Qquadratic_sg_denom_nonzero); repeat split; 
              assumption
           | intros ]
        | intros ]
     | intros ]
  | intros ]; [ right | left; right | left; left; right | left; left; left ];
  assumption. 
Defined.


Lemma Qquadratic_sg_denom_nonzero_nonzero_3 :
 forall (g h : Z) (p1 p2 : Qpositive),
 Qquadratic_sg_denom_nonzero 0 0 g h p1 p2 -> g <> 0%Z \/ h <> 0%Z.
Proof.
 intros.
 case (Z_zerop g);
  [ intro; case (Z_zerop h); [ intro; idtac | intro; right ] | intro; left ];
  try assumption.
 apply False_ind.
 apply (Qquadratic_sg_denom_nonzero_nonzero 0 0 g h p1 p2);
  try solve [ constructor | assumption ].
Defined. 


Definition Qquadratic_Qpositive_to_Q (a b c d e f g h : Z)
  (p1 p2 : Qpositive) (H_qsign : Qquadratic_sg_denom_nonzero e f g h p1 p2) :
  Q.
case (same_ratio_dec_inf a b c d e f g h);
 [ intros _;
    case (Qquadratic_sg_denom_nonzero_nonzero_inf e f g h p1 p2 H_qsign);
    [ intros [[He| Hf]| Hg];
       [ exact (fraction_encoding a e He)
       | exact (fraction_encoding b f Hf)
       | exact (fraction_encoding c g Hg) ]
    | intro Hh; exact (fraction_encoding d h Hh) ]
 | idtac ].


intro not_same_ratio_abcdefgh. 
case (Qquadratic_sign_sign_dec a b c d e f g h p1 p2 H_qsign).
 intros [l1_eq_zero| l1_eq_one];
  [  (* (q_sign a b c d e  f g h p1 p2) = 0 *)
  exact Zero | idtac ]. (* (q_sign a b c d e  f g h p1 p2) = 1 *)
 
   assert
    (H :
     Qquadratic_sign a b c d e f g h p1 p2 H_qsign =
     (1%Z,
     (qnew_a a b c d e f g h p1 p2 H_qsign,
     (qnew_b a b c d e f g h p1 p2 H_qsign,
     (qnew_c a b c d e f g h p1 p2 H_qsign,
     qnew_d a b c d e f g h p1 p2 H_qsign)),
     (qnew_e a b c d e f g h p1 p2 H_qsign,
     (qnew_f a b c d e f g h p1 p2 H_qsign,
     (qnew_g a b c d e f g h p1 p2 H_qsign,
     qnew_h a b c d e f g h p1 p2 H_qsign))),
     (qnew_p1 a b c d e f g h p1 p2 H_qsign,
     qnew_p2 a b c d e f g h p1 p2 H_qsign))));
    [ abstract (rewrite <- l1_eq_one;
                 unfold qnew_a, qnew_b, qnew_c, qnew_d, qnew_e, qnew_f,
                  qnew_g, qnew_h, qnew_p1, qnew_p2 
                  in |- *;
                 replace (q_sign a b c d e f g h p1 p2 H_qsign) with
                  (fst (Qquadratic_sign a b c d e f g h p1 p2 H_qsign));
                 [ idtac | reflexivity ]; repeat rewrite <- pair_1;
                 reflexivity)
    | idtac ].

 
 (* still l1=1 -> Q *)
 case
  (Zsgn_1
     (qnew_a a b c d e f g h p1 p2 H_qsign +
      qnew_b a b c d e f g h p1 p2 H_qsign +
      qnew_c a b c d e f g h p1 p2 H_qsign +
      qnew_d a b c d e f g h p1 p2 H_qsign)).
 (* Z.sgn `na+nb+nc+nd` = 0 \/ Z.sgn `na+nb+nc+nd` = 1 *)
 intros [na_nb_nc_nd_eq_zero| na_nb_nc_nd_eq_one].
 (* Z.sgn = 0 -> False *)
 abstract (apply False_rec;
            generalize
             (Qquadratic_sign_pos_1 a b c d e f g h p1 p2 H_qsign
                (qnew_a a b c d e f g h p1 p2 H_qsign)
                (qnew_b a b c d e f g h p1 p2 H_qsign)
                (qnew_c a b c d e f g h p1 p2 H_qsign)
                (qnew_d a b c d e f g h p1 p2 H_qsign)
                (qnew_e a b c d e f g h p1 p2 H_qsign)
                (qnew_f a b c d e f g h p1 p2 H_qsign)
                (qnew_g a b c d e f g h p1 p2 H_qsign)
                (qnew_h a b c d e f g h p1 p2 H_qsign)
                (qnew_p1 a b c d e f g h p1 p2 H_qsign)
                (qnew_p2 a b c d e f g h p1 p2 H_qsign) H);
            intros [(na_nb_nc_nd_pos, _)| (na_nb_nc_nd_neg, _)];
            generalize (Zsgn_2 _ na_nb_nc_nd_eq_zero);
            [ apply sym_not_eq | idtac ]; apply Zorder.Zlt_not_eq; 
            assumption).
 (* Z.sgn = 1 *)
 refine
  (Qpos
     (Qquadratic_Qpositive_to_Qpositive
        (qnew_a a b c d e f g h p1 p2 H_qsign)
        (qnew_b a b c d e f g h p1 p2 H_qsign)
        (qnew_c a b c d e f g h p1 p2 H_qsign)
        (qnew_d a b c d e f g h p1 p2 H_qsign)
        (qnew_e a b c d e f g h p1 p2 H_qsign)
        (qnew_f a b c d e f g h p1 p2 H_qsign)
        (qnew_g a b c d e f g h p1 p2 H_qsign)
        (qnew_h a b c d e f g h p1 p2 H_qsign)
        (qnew_p1 a b c d e f g h p1 p2 H_qsign)
        (qnew_p2 a b c d e f g h p1 p2 H_qsign) _)).
 abstract apply
           (Qquadratic_Qpositive_to_Q_quadraticAcc_pos_1 a b c d e f g h p1
              p2 H_qsign not_same_ratio_abcdefgh l1_eq_one na_nb_nc_nd_eq_one).
 
 (* Z.sgn = -1 *)
 intro na_nb_nc_nd_eq_minus_one.
 refine
  (Qpos
     (Qquadratic_Qpositive_to_Qpositive
        (- qnew_a a b c d e f g h p1 p2 H_qsign)
        (- qnew_b a b c d e f g h p1 p2 H_qsign)
        (- qnew_c a b c d e f g h p1 p2 H_qsign)
        (- qnew_d a b c d e f g h p1 p2 H_qsign)
        (- qnew_e a b c d e f g h p1 p2 H_qsign)
        (- qnew_f a b c d e f g h p1 p2 H_qsign)
        (- qnew_g a b c d e f g h p1 p2 H_qsign)
        (- qnew_h a b c d e f g h p1 p2 H_qsign)
        (qnew_p1 a b c d e f g h p1 p2 H_qsign)
        (qnew_p2 a b c d e f g h p1 p2 H_qsign) _)).
 abstract apply
           (Qquadratic_Qpositive_to_Q_quadraticAcc_pos_2 a b c d e f g h p1
              p2 H_qsign not_same_ratio_abcdefgh l1_eq_one
              na_nb_nc_nd_eq_minus_one).

 (* (q_sign a b c d e  f g h p1 p2) = -1 *)
 intro l1_eq_min_one.

 assert
  (H :
   Qquadratic_sign a b c d e f g h p1 p2 H_qsign =
   ((-1)%Z,
   (qnew_a a b c d e f g h p1 p2 H_qsign,
   (qnew_b a b c d e f g h p1 p2 H_qsign,
   (qnew_c a b c d e f g h p1 p2 H_qsign,
   qnew_d a b c d e f g h p1 p2 H_qsign)),
   (qnew_e a b c d e f g h p1 p2 H_qsign,
   (qnew_f a b c d e f g h p1 p2 H_qsign,
   (qnew_g a b c d e f g h p1 p2 H_qsign,
   qnew_h a b c d e f g h p1 p2 H_qsign))),
   (qnew_p1 a b c d e f g h p1 p2 H_qsign,
   qnew_p2 a b c d e f g h p1 p2 H_qsign))));
  [ abstract (rewrite <- l1_eq_min_one;
               unfold qnew_a, qnew_b, qnew_c, qnew_d, qnew_e, qnew_f, qnew_g,
                qnew_h, qnew_p1, qnew_p2 in |- *;
               replace (q_sign a b c d e f g h p1 p2 H_qsign) with
                (fst (Qquadratic_sign a b c d e f g h p1 p2 H_qsign));
               [ idtac | reflexivity ]; repeat rewrite <- pair_1; 
               reflexivity)
  | idtac ].
 
 (* still l1= -1 -> Q *)
 case
  (Zsgn_1
     (qnew_a a b c d e f g h p1 p2 H_qsign +
      qnew_b a b c d e f g h p1 p2 H_qsign +
      qnew_c a b c d e f g h p1 p2 H_qsign +
      qnew_d a b c d e f g h p1 p2 H_qsign)).
 (* Z.sgn `na+nb+nc+nd` = 0 \/ Z.sgn `na+nb+nc+nd` = 1 *)
 intros [na_nb_nc_nd_eq_zero| na_nb_nc_nd_eq_one].
 (* Z.sgn = 0 -> False *)
 abstract (apply False_rec;
            generalize
             (Qquadratic_sign_neg_1 a b c d e f g h p1 p2 H_qsign
                (qnew_a a b c d e f g h p1 p2 H_qsign)
                (qnew_b a b c d e f g h p1 p2 H_qsign)
                (qnew_c a b c d e f g h p1 p2 H_qsign)
                (qnew_d a b c d e f g h p1 p2 H_qsign)
                (qnew_e a b c d e f g h p1 p2 H_qsign)
                (qnew_f a b c d e f g h p1 p2 H_qsign)
                (qnew_g a b c d e f g h p1 p2 H_qsign)
                (qnew_h a b c d e f g h p1 p2 H_qsign)
                (qnew_p1 a b c d e f g h p1 p2 H_qsign)
                (qnew_p2 a b c d e f g h p1 p2 H_qsign) H);
            intros [(na_nb_nc_nd_pos, _)| (na_nb_nc_nd_neg, _)];
            generalize (Zsgn_2 _ na_nb_nc_nd_eq_zero);
            [ apply sym_not_eq | idtac ]; apply Zorder.Zlt_not_eq; 
            assumption).
 (* Z.sgn = 1 *)
 refine
  (Qneg
     (Qquadratic_Qpositive_to_Qpositive
        (qnew_a a b c d e f g h p1 p2 H_qsign)
        (qnew_b a b c d e f g h p1 p2 H_qsign)
        (qnew_c a b c d e f g h p1 p2 H_qsign)
        (qnew_d a b c d e f g h p1 p2 H_qsign)
        (- qnew_e a b c d e f g h p1 p2 H_qsign)
        (- qnew_f a b c d e f g h p1 p2 H_qsign)
        (- qnew_g a b c d e f g h p1 p2 H_qsign)
        (- qnew_h a b c d e f g h p1 p2 H_qsign)
        (qnew_p1 a b c d e f g h p1 p2 H_qsign)
        (qnew_p2 a b c d e f g h p1 p2 H_qsign) _)).
 abstract apply
           (Qquadratic_Qpositive_to_Q_quadraticAcc_neg_1 a b c d e f g h p1
              p2 H_qsign not_same_ratio_abcdefgh l1_eq_min_one
              na_nb_nc_nd_eq_one).

 (* Z.sgn = -1 *)
 intro na_nb_nc_nd_eq_minus_one.
 refine
  (Qneg
     (Qquadratic_Qpositive_to_Qpositive
        (- qnew_a a b c d e f g h p1 p2 H_qsign)
        (- qnew_b a b c d e f g h p1 p2 H_qsign)
        (- qnew_c a b c d e f g h p1 p2 H_qsign)
        (- qnew_d a b c d e f g h p1 p2 H_qsign)
        (qnew_e a b c d e f g h p1 p2 H_qsign)
        (qnew_f a b c d e f g h p1 p2 H_qsign)
        (qnew_g a b c d e f g h p1 p2 H_qsign)
        (qnew_h a b c d e f g h p1 p2 H_qsign)
        (qnew_p1 a b c d e f g h p1 p2 H_qsign)
        (qnew_p2 a b c d e f g h p1 p2 H_qsign) _)).
 abstract apply
           (Qquadratic_Qpositive_to_Q_quadraticAcc_neg_2 a b c d e f g h p1
              p2 H_qsign not_same_ratio_abcdefgh l1_eq_min_one
              na_nb_nc_nd_eq_minus_one).
Defined.

Inductive Qquadratic_denom_nonzero : Z -> Z -> Z -> Z -> Q -> Q -> Prop :=
  | Qquadraticok00 :
      forall (e f g h : Z) (s1 s2 : Q),
      s1 = Zero ->
      s2 = Zero -> h <> 0%Z -> Qquadratic_denom_nonzero e f g h s1 s2
  | Qquadraticok01 :
      forall (e f g h : Z) (s1 s2 : Q) (p2 : Qpositive),
      s1 = Zero ->
      s2 = Qpos p2 ->
      Qhomographic_sg_denom_nonzero g h p2 ->
      Qquadratic_denom_nonzero e f g h s1 s2
  | Qquadraticok02 :
      forall (e f g h : Z) (s1 s2 : Q) (p2 : Qpositive),
      s1 = Zero ->
      s2 = Qneg p2 ->
      Qhomographic_sg_denom_nonzero (- g) h p2 ->
      Qquadratic_denom_nonzero e f g h s1 s2
  | Qquadraticok10 :
      forall (e f g h : Z) (s1 s2 : Q) (p1 : Qpositive),
      s1 = Qpos p1 ->
      s2 = Zero ->
      Qhomographic_sg_denom_nonzero f h p1 ->
      Qquadratic_denom_nonzero e f g h s1 s2
  | Qquadraticok20 :
      forall (e f g h : Z) (s1 s2 : Q) (p1 : Qpositive),
      s1 = Qneg p1 ->
      s2 = Zero ->
      Qhomographic_sg_denom_nonzero (- f) h p1 ->
      Qquadratic_denom_nonzero e f g h s1 s2
  | Qquadraticok11 :
      forall (e f g h : Z) (s1 s2 : Q) (p1 p2 : Qpositive),
      s1 = Qpos p1 ->
      s2 = Qpos p2 ->
      Qquadratic_sg_denom_nonzero e f g h p1 p2 ->
      Qquadratic_denom_nonzero e f g h s1 s2
  | Qquadraticok12 :
      forall (e f g h : Z) (s1 s2 : Q) (p1 p2 : Qpositive),
      s1 = Qpos p1 ->
      s2 = Qneg p2 ->
      Qquadratic_sg_denom_nonzero (- e) f (- g) h p1 p2 ->
      Qquadratic_denom_nonzero e f g h s1 s2
  | Qquadraticok21 :
      forall (e f g h : Z) (s1 s2 : Q) (p1 p2 : Qpositive),
      s1 = Qneg p1 ->
      s2 = Qpos p2 ->
      Qquadratic_sg_denom_nonzero (- e) (- f) g h p1 p2 ->
      Qquadratic_denom_nonzero e f g h s1 s2
  | Qquadraticok22 :
      forall (e f g h : Z) (s1 s2 : Q) (p1 p2 : Qpositive),
      s1 = Qneg p1 ->
      s2 = Qneg p2 ->
      Qquadratic_sg_denom_nonzero e (- f) (- g) h p1 p2 ->
      Qquadratic_denom_nonzero e f g h s1 s2.


Lemma Qquadratic_00 :
 forall e f g h : Z, Qquadratic_denom_nonzero e f g h Zero Zero -> h <> 0%Z.  
Proof.
 intros.
 abstract (inversion H;
            assumption ||
              (repeat
                match goal with
                | id1:(?X1 = ?X2) |- ?X3 =>
                    try discriminate id1; clear id1
                end)).
Defined. 


Lemma Qquadratic_01 :
 forall (e f g h : Z) (p2 : Qpositive),
 Qquadratic_denom_nonzero e f g h Zero (Qpos p2) ->
 Qhomographic_sg_denom_nonzero g h p2.
Proof.
 intros.
 abstract (inversion H;
            try solve
             [ assumption
             | repeat
                match goal with
                | id1:(?X1 = ?X2) |- ?X3 =>
                    try discriminate id1; clear id1
                end ]; generalize (f_equal Q_tail H1); 
            simpl in |- *; intro H_p; rewrite H_p; 
            assumption).
Defined. 

Lemma Qquadratic_02 :
 forall (e f g h : Z) (p2 : Qpositive),
 Qquadratic_denom_nonzero e f g h Zero (Qneg p2) ->
 Qhomographic_sg_denom_nonzero (- g) h p2.
Proof.
 intros.
 abstract (inversion H;
            try solve
             [ assumption
             | repeat
                match goal with
                | id1:(?X1 = ?X2) |- ?X3 =>
                    try discriminate id1; clear id1
                end ]; generalize (f_equal Q_tail H1); 
            simpl in |- *; intro H_p; rewrite H_p; 
            assumption).
Defined. 

Lemma Qquadratic_10 :
 forall (e f g h : Z) (p1 : Qpositive),
 Qquadratic_denom_nonzero e f g h (Qpos p1) Zero ->
 Qhomographic_sg_denom_nonzero f h p1.
Proof.
 intros.
 abstract (inversion H;
            try solve
             [ assumption
             | repeat
                match goal with
                | id1:(?X1 = ?X2) |- ?X3 =>
                    try discriminate id1; clear id1
                end ]; generalize (f_equal Q_tail H0); 
            simpl in |- *; intro H_p; rewrite H_p; 
            assumption).
Defined. 

Lemma Qquadratic_20 :
 forall (e f g h : Z) (p1 : Qpositive),
 Qquadratic_denom_nonzero e f g h (Qneg p1) Zero ->
 Qhomographic_sg_denom_nonzero (- f) h p1.
Proof.
 intros.
 abstract (inversion H;
            try solve
             [ assumption
             | repeat
                match goal with
                | id1:(?X1 = ?X2) |- ?X3 =>
                    try discriminate id1; clear id1
                end ]; generalize (f_equal Q_tail H0); 
            simpl in |- *; intro H_p; rewrite H_p; 
            assumption).
Defined. 

(* attention : identical proofs for next 4 lemmata *) 

Lemma Qquadratic_11 :
 forall (e f g h : Z) (p1 p2 : Qpositive),
 Qquadratic_denom_nonzero e f g h (Qpos p1) (Qpos p2) ->
 Qquadratic_sg_denom_nonzero e f g h p1 p2.
Proof.
 intros.
 abstract (inversion H;
            try solve
             [ assumption
             | repeat
                match goal with
                | id1:(?X1 = ?X2) |- ?X3 =>
                    try discriminate id1; clear id1
                end ];
            repeat
             match goal with
             | id1:(?X1 ?X2 = ?X1 ?X3) |- ?X4 =>
                 let tt := eval compute in (f_equal Q_tail id1) in
                 rewrite tt
             end; assumption).
Defined. 

Lemma Qquadratic_12 :
 forall (e f g h : Z) (p1 p2 : Qpositive),
 Qquadratic_denom_nonzero e f g h (Qpos p1) (Qneg p2) ->
 Qquadratic_sg_denom_nonzero (- e) f (- g) h p1 p2.
Proof.
 intros.
 abstract (inversion H;
            try solve
             [ assumption
             | repeat
                match goal with
                | id1:(?X1 = ?X2) |- ?X3 =>
                    try discriminate id1; clear id1
                end ];
            repeat
             match goal with
             | id1:(?X1 ?X2 = ?X1 ?X3) |- ?X4 =>
                 let tt := eval compute in (f_equal Q_tail id1) in
                 rewrite tt
             end; assumption).
Defined. 

Lemma Qquadratic_21 :
 forall (e f g h : Z) (p1 p2 : Qpositive),
 Qquadratic_denom_nonzero e f g h (Qneg p1) (Qpos p2) ->
 Qquadratic_sg_denom_nonzero (- e) (- f) g h p1 p2.
Proof.
 intros.
 abstract (inversion H;
            try solve
             [ assumption
             | repeat
                match goal with
                | id1:(?X1 = ?X2) |- ?X3 =>
                    try discriminate id1; clear id1
                end ];
            repeat
             match goal with
             | id1:(?X1 ?X2 = ?X1 ?X3) |- ?X4 =>
                 let tt := eval compute in (f_equal Q_tail id1) in
                 rewrite tt
             end; assumption).
Defined. 

Lemma Qquadratic_22 :
 forall (e f g h : Z) (p1 p2 : Qpositive),
 Qquadratic_denom_nonzero e f g h (Qneg p1) (Qneg p2) ->
 Qquadratic_sg_denom_nonzero e (- f) (- g) h p1 p2.
Proof.
 intros.
 abstract (inversion H;
            try solve
             [ assumption
             | repeat
                match goal with
                | id1:(?X1 = ?X2) |- ?X3 =>
                    try discriminate id1; clear id1
                end ];
            repeat
             match goal with
             | id1:(?X1 ?X2 = ?X1 ?X3) |- ?X4 =>
                 let tt := eval compute in (f_equal Q_tail id1) in
                 rewrite tt
             end; assumption).
Defined. 



Definition Qquadratic :
  Z ->
  Z ->
  Z ->
  Z ->
  forall (e f g h : Z) (s1 s2 : Q)
    (H_Qquadratic_denom_nonzero : Qquadratic_denom_nonzero e f g h s1 s2), Q.
intros a b c d e f g h [| p1 | p1 ]; [ |intros [| p2| p2] | intros [| p2| p2]]. 
 (* s1 = Zero *)
 intros s2 H_Qquadratic_denom_nonzero.
 refine (Qhomographic c d g h s2 _).
 abstract (inversion_clear H_Qquadratic_denom_nonzero; solve
            [ apply Qhomographicok0; assumption
            | apply Qhomographicok1 with p2; assumption
            | apply Qhomographicok2 with p2; assumption
            | match goal with
              | id1:(?X2 = ?X3) |- ?X4 => discriminate id1
              end ]).
 (* s1 = (Qpos p1) s2 = Zero *)
 intro H_Qquadratic_denom_nonzero.
 refine (Qhomographic b d f h (Qpos p1) _);
  abstract (inversion_clear H_Qquadratic_denom_nonzero;
             try solve
              [ apply Qhomographicok1 with p2; assumption
              | match goal with
                | id1:(?X2 = ?X3) |- ?X4 => discriminate id1
                end ]; injection H; intro H_injection; 
             rewrite H_injection; apply Qhomographicok1 with p0;
             [ reflexivity | assumption ]).

 (* s1 = (Qpos p1) s2 = (Qpos p2) *)

 intro H_Qquadratic_denom_nonzero.
 exact
  (Qquadratic_Qpositive_to_Q a b c d e f g h p1 p2
     (Qquadratic_11 e f g h p1 p2 H_Qquadratic_denom_nonzero)).
 (* s1 = (Qpos p1) s2 = (Qneg p2) *)
 intro H_Qquadratic_denom_nonzero.
 exact
  (Qquadratic_Qpositive_to_Q (- a) b (- c) d (- e) f 
     (- g) h p1 p2 (Qquadratic_12 e f g h p1 p2 H_Qquadratic_denom_nonzero)).
 (* s1 = (Qneg p1) s2 = Zero *)
 intro H_Qquadratic_denom_nonzero.
 refine (Qhomographic b d f h (Qneg p1) _);
  abstract (inversion_clear H_Qquadratic_denom_nonzero;
             try solve
              [ apply Qhomographicok2 with p2; assumption
              | match goal with
                | id1:(?X2 = ?X3) |- ?X4 => discriminate id1
                end ]; injection H; intro H_injection; 
             rewrite H_injection; apply Qhomographicok2 with p0;
             [ reflexivity | assumption ]).
 (* s1 = (Qneg p1) s2 = (Qpos p2) *)
 intro H_Qquadratic_denom_nonzero.
 exact
  (Qquadratic_Qpositive_to_Q (- a) (- b) c d (- e) 
     (- f) g h p1 p2 (Qquadratic_21 e f g h p1 p2 H_Qquadratic_denom_nonzero)).
 (* s1 = (Qneg p1) s2 = (Qneg p2) *)
 intro H_Qquadratic_denom_nonzero.
 exact
  (Qquadratic_Qpositive_to_Q a (- b) (- c) d e (- f) 
     (- g) h p1 p2 (Qquadratic_22 e f g h p1 p2 H_Qquadratic_denom_nonzero)).
Defined.


Lemma Qquadratic_denom_nonzero_Zero_Zero_Zero_always :
 forall (h : Z) (s1 s2 : Q),
 h <> 0%Z -> Qquadratic_denom_nonzero 0 0 0 h s1 s2.
Proof.
 intros h s1 s2 Hh.
 generalize h Hh s2.  
  abstract (induction s1 as [| p| p]; intros; case s0;
             [  (* s1 = Zero ,s0 = Zero *)
             apply Qquadraticok00
             |  (* s1 = Zero ,s0 = (Qpos p) *)
                intro p; apply Qquadraticok01 with p
             |  (* s1 = Zero ,s0 = (Qneg p) *)
                intro p; apply Qquadraticok02 with p
             |  (* s1 = (Qpos p) ,s0 = Zero *)
             apply Qquadraticok10 with p
             |  (* s1 = (Qpos p) ,s0 = (Qpos p0) *)
                intro p0; apply Qquadraticok11 with p p0
             |  (* s1 = (Qpos p) ,s0 = (Qneg p0) *)
                intro p0; apply Qquadraticok12 with p p0
             |  (* s1 = (Qneg p)  ,s0 = Zero *)
             apply Qquadraticok20 with p
             |  (* s1 = (Qneg p)  ,s0 = (Qpos p0) *)
                intro p0; apply Qquadraticok21 with p p0
             |  (* s1 = (Qneg p)  ,s0 = (Qneg p0) *)
                intro p0; apply Qquadraticok22 with p p0 ]; 
             simpl in |- *;
             reflexivity ||
               apply Qhomographic_sg_denom_nonzero_Zero_always ||
                 (try apply Qquadratic_sg_denom_nonzero_Zero_Zero_Zero_always);
             assumption).
Defined.  

Lemma Qquadratic_denom_nonzero_Zero_Zero_Zero_ONE :
 forall s1 s2 : Q, Qquadratic_denom_nonzero 0 0 0 1 s1 s2.
Proof.
 intros.
 apply Qquadratic_denom_nonzero_Zero_Zero_Zero_always.
 abstract discriminate.
Defined.

Lemma Qquadratic_denom_nonzero_Zero_Zero_always_Zero :
 forall (g : Z) (s1 s2 : Q) (H_nonzero_s2 : s2 <> Zero :>Q),
 g <> 0%Z -> Qquadratic_denom_nonzero 0 0 g 0 s1 s2.
Proof.
 intros g s1 s2 H_nonzero_s2 Hg.
 generalize g Hg s2 H_nonzero_s2.  
  abstract (induction s1 as [| p| p]; intros; destruct s0 as [| p0| p0];
             [ Falsum
             |  (* s1 = Zero ,s0 = Zero *)
              (* s1 = Zero ,s0 = (Qpos p) *)
             apply Qquadraticok01 with p0
             |  (* s1 = Zero ,s0 = (Qneg p) *)
             apply Qquadraticok02 with p0
             | Falsum
             |  (* s1 = (Qpos p) ,s0 = Zero *)
              (* s1 = (Qpos p) ,s0 = (Qpos p0) *)
             apply Qquadraticok11 with p p0
             |  (* s1 = (Qpos p) ,s0 = (Qneg p0) *)
             apply Qquadraticok12 with p p0
             | Falsum
             |  (* s1 = (Qneg p)  ,s0 = Zero *)
              (* s1 = (Qneg p)  ,s0 = (Qpos p0) *)
             apply Qquadraticok21 with p p0
             |  (* s1 = (Qneg p)  ,s0 = (Qneg p0) *)
             apply Qquadraticok22 with p p0 ]; simpl in |- *;
             reflexivity ||
               apply Qhomographic_sg_denom_nonzero_always_Zero ||
                 (try apply Qquadratic_sg_denom_nonzero_Zero_Zero_always_Zero);
             try
              match goal with
              | id1:?X2 |- ((- ?X1)%Z <> 0%Z) => apply Zopp_app
              end; assumption).
Defined.  

Lemma Qquadratic_denom_nonzero_Zero_Zero_ONE_Zero :
 forall (s1 s2 : Q) (H_nonzero_s2 : s2 <> Zero :>Q),
 Qquadratic_denom_nonzero 0 0 1 0 s1 s2.
Proof.
 intros.
 apply (Qquadratic_denom_nonzero_Zero_Zero_always_Zero 1 s1 s2 H_nonzero_s2).
 abstract discriminate.
Defined.




Definition Qplus_lazy (x y : Q) : Q :=
  Qquadratic 0 1 1 0 0 0 0 1 x y
    (Qquadratic_denom_nonzero_Zero_Zero_Zero_ONE x y).

Definition Qmult_lazy (x y : Q) : Q :=
  Qquadratic 1 0 0 0 0 0 0 1 x y
    (Qquadratic_denom_nonzero_Zero_Zero_Zero_ONE x y).

Definition Qminus_lazy (x y : Q) : Q :=
  Qquadratic 0 1 (-1) 0 0 0 0 1 x y
    (Qquadratic_denom_nonzero_Zero_Zero_Zero_ONE x y).

Definition Qdiv_lazy (x y : Q) (Hy : y <> Zero) : Q :=
  Qquadratic 0 1 0 0 0 0 1 0 x y
    (Qquadratic_denom_nonzero_Zero_Zero_ONE_Zero x y Hy).

