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



Require Export Qhomographic_sign.
Require Export Qhomographic_Qpositive_to_Qpositive.
Require Export Qhomographic_sign_properties.

Definition new_a (a b c d : Z) (p : Qpositive)
  (H_Qhomographic_sg_denom_nonzero : Qhomographic_sg_denom_nonzero c d p) :=
  fst
    (fst (snd (Qhomographic_sign a b c d p H_Qhomographic_sg_denom_nonzero))).

Definition new_b (a b c d : Z) (p : Qpositive)
  (H_Qhomographic_sg_denom_nonzero : Qhomographic_sg_denom_nonzero c d p) :=
  fst
    (snd
       (fst
          (snd (Qhomographic_sign a b c d p H_Qhomographic_sg_denom_nonzero)))).

Definition new_c (a b c d : Z) (p : Qpositive)
  (H_Qhomographic_sg_denom_nonzero : Qhomographic_sg_denom_nonzero c d p) :=
  fst
    (snd
       (snd
          (fst
             (snd
                (Qhomographic_sign a b c d p H_Qhomographic_sg_denom_nonzero))))).

Definition new_d (a b c d : Z) (p : Qpositive)
  (H_Qhomographic_sg_denom_nonzero : Qhomographic_sg_denom_nonzero c d p) :=
  snd
    (snd
       (snd
          (fst
             (snd
                (Qhomographic_sign a b c d p H_Qhomographic_sg_denom_nonzero))))).

Definition new_p (a b c d : Z) (p : Qpositive)
  (H_Qhomographic_sg_denom_nonzero : Qhomographic_sg_denom_nonzero c d p) :=
  snd (snd (Qhomographic_sign a b c d p H_Qhomographic_sg_denom_nonzero)).

Lemma Qhomographic_Qpositive_to_Q_homographicAcc_pos_1 :
 forall (a b c d : Z) (p : Qpositive)
   (H_Qhomographic_sg_denom_nonzero : Qhomographic_sg_denom_nonzero c d p),
 (a * d)%Z <> (b * c)%Z ->
 h_sign a b c d p H_Qhomographic_sg_denom_nonzero = 1%Z ->
 (0 <
  Z.sgn
    (new_a a b c d p H_Qhomographic_sg_denom_nonzero +
     new_b a b c d p H_Qhomographic_sg_denom_nonzero))%Z ->
 homographicAcc (new_a a b c d p H_Qhomographic_sg_denom_nonzero)
   (new_b a b c d p H_Qhomographic_sg_denom_nonzero)
   (new_c a b c d p H_Qhomographic_sg_denom_nonzero)
   (new_d a b c d p H_Qhomographic_sg_denom_nonzero)
   (new_p a b c d p H_Qhomographic_sg_denom_nonzero).
Proof.
 intros a b c d p H_hsign ad_neq_bc l1_eq_one z.
 set (na := new_a a b c d p H_hsign) in *.
 set (nb := new_b a b c d p H_hsign) in *.
 set (nc := new_c a b c d p H_hsign) in *.
 set (nd := new_d a b c d p H_hsign) in *.
 set (l3 := new_p a b c d p H_hsign) in *.
 assert
  (H : Qhomographic_sign a b c d p H_hsign = (1%Z, (na, (nb, (nc, nd)), l3))).
 unfold na, nb, nc, nd, l3 in |- *.
 rewrite <- l1_eq_one.
 unfold new_a, new_b, new_c, new_d, new_p in |- *.
 replace (h_sign a b c d p H_hsign) with
  (fst (Qhomographic_sign a b c d p H_hsign)); [ idtac | reflexivity ];
  repeat rewrite <- pair_1; reflexivity.
      destruct l3 as [p0| p0| ].
      (* l3 = (nR p0) *)
      apply homographicAcc_wf.
      apply Zsgn_12.
      assumption.
     
      generalize (sg_pos_1 a b c d p H_hsign na nb nc nd (nR p0) H).        
      intros.
      case H0.             
      intro.
      elim a0.
      intros.     
      assumption.
      intros.
      apply False_ind.      
      elim a0.
      intros.
      generalize (Zsgn_12 (na + nb) z).
      intro.
      apply Z.lt_irrefl with 0%Z.
      apply Z.lt_trans with (na + nb)%Z.
      assumption.
      assumption.
      generalize (sg_pos_2 a b c d p H_hsign na nb nc nd (nR p0) H). 
      intro.
      case H0.         
      intro.
      case s.
      intro.
      elim a0. 
      intros; assumption.
      intro.
      apply False_ind.
      elim a0.
      intros.
      elim H2.
      intros.
      apply Z.lt_irrefl with 0%Z.
      apply Z.lt_le_trans with (na + nb)%Z.
      apply Zsgn_12.
      assumption.
      rewrite Zplus_0_r_reverse with 0%Z.
      apply Zplus_le_compat.
      assumption.      
      assumption.
      intro.      
      discriminate e.
      generalize (sg_pos_2 a b c d p H_hsign na nb nc nd (nR p0) H). 
      intro.
      case H0.         
      intro.
      case s.
      intro.
      elim a0. 
      intros.
      elim H2.
      intros.
      assumption.
      intro.
      apply False_ind.
      elim a0.
      intros.
      elim H2.
      intros.
      apply Z.lt_irrefl with 0%Z.
      apply Z.lt_le_trans with (na + nb)%Z.
      apply Zsgn_12.
      assumption.
      rewrite Zplus_0_r_reverse with 0%Z.
      apply Zplus_le_compat.
      assumption.      
      assumption.
      intro.      
      discriminate e.
      generalize (sg_pos_2 a b c d p H_hsign na nb nc nd (nR p0) H). 
      intro.
      case H0.         
      intro.
      case s.
      intro.
      elim a0. 
      intros.
      elim H2.
      intros.
      elim H4.
      intros.
      assumption.
      intro.
      apply False_ind.
      elim a0.
      intros.
      elim H2.
      intros.
      apply Z.lt_irrefl with 0%Z.
      apply Z.lt_le_trans with (na + nb)%Z.
      apply Zsgn_12.
      assumption.
      rewrite Zplus_0_r_reverse with 0%Z.
      apply Zplus_le_compat.
      assumption.      
      assumption.
      intro.      
      discriminate e.
      generalize (sg_pos_2 a b c d p H_hsign na nb nc nd (nR p0) H). 
      intro.
      case H0.         
      intro.
      case s.
      intro.
      elim a0. 
      intros.
      elim H2.
      intros.
      elim H4.
      intros.
      assumption.
      intro.
      apply False_ind.
      elim a0.
      intros.
      elim H2.
      intros.
      apply Z.lt_irrefl with 0%Z.
      apply Z.lt_le_trans with (na + nb)%Z.
      apply Zsgn_12.
      assumption.
      rewrite Zplus_0_r_reverse with 0%Z.
      apply Zplus_le_compat.
      assumption.      
      assumption.
      intro.      
      discriminate e.
      (* l3 = (dL p0) *)
      apply homographicAcc_wf.
      apply Zsgn_12.
      assumption.
     
      generalize (sg_pos_1 a b c d p H_hsign na nb nc nd (dL p0) H).        
      intros.
      case H0.             
      intro.
      elim a0.
      intros.     
      assumption.
      intros.
      apply False_ind.      
      elim a0.
      intros.
      generalize (Zsgn_12 (na + nb) z).
      intro.
      apply Z.lt_irrefl with 0%Z.
      apply Z.lt_trans with (na + nb)%Z.
      assumption.
      assumption.
      generalize (sg_pos_2 a b c d p H_hsign na nb nc nd (dL p0) H). 
      intro.
      case H0.         
      intro.
      case s.
      intro.
      elim a0. 
      intros; assumption.
      intro.
      apply False_ind.
      elim a0.
      intros.
      elim H2.
      intros.
      apply Z.lt_irrefl with 0%Z.
      apply Z.lt_le_trans with (na + nb)%Z.
      apply Zsgn_12.
      assumption.
      rewrite Zplus_0_r_reverse with 0%Z.
      apply Zplus_le_compat.
      assumption.      
      assumption.
      intro.      
      discriminate e.
      generalize (sg_pos_2 a b c d p H_hsign na nb nc nd (dL p0) H). 
      intro.
      case H0.         
      intro.
      case s.
      intro.
      elim a0. 
      intros.
      elim H2.
      intros.
      assumption.
      intro.
      apply False_ind.
      elim a0.
      intros.
      elim H2.
      intros.
      apply Z.lt_irrefl with 0%Z.
      apply Z.lt_le_trans with (na + nb)%Z.
      apply Zsgn_12.
      assumption.
      rewrite Zplus_0_r_reverse with 0%Z.
      apply Zplus_le_compat.
      assumption.      
      assumption.
      intro.      
      discriminate e.
      generalize (sg_pos_2 a b c d p H_hsign na nb nc nd (dL p0) H). 
      intro.
      case H0.         
      intro.
      case s.
      intro.
      elim a0. 
      intros.
      elim H2.
      intros.
      elim H4.
      intros.
      assumption.
      intro.
      apply False_ind.
      elim a0.
      intros.
      elim H2.
      intros.
      apply Z.lt_irrefl with 0%Z.
      apply Z.lt_le_trans with (na + nb)%Z.
      apply Zsgn_12.
      assumption.
      rewrite Zplus_0_r_reverse with 0%Z.
      apply Zplus_le_compat.
      assumption.      
      assumption.
      intro.      
      discriminate e.
      generalize (sg_pos_2 a b c d p H_hsign na nb nc nd (dL p0) H). 
      intro.
      case H0.         
      intro.
      case s.
      intro.
      elim a0. 
      intros.
      elim H2.
      intros.
      elim H4.
      intros.
      assumption.
      intro.
      apply False_ind.
      elim a0.
      intros.
      elim H2.
      intros.
      apply Z.lt_irrefl with 0%Z.
      apply Z.lt_le_trans with (na + nb)%Z.
      apply Zsgn_12.
      assumption.
      rewrite Zplus_0_r_reverse with 0%Z.
      apply Zplus_le_compat.
      assumption.      
      assumption.
      intro.      
      discriminate e.
      (* l3 = One *)
      apply homographicacc0.
      reflexivity.
      apply Zsgn_12.
      assumption.
      generalize (sg_pos_1 a b c d p H_hsign na nb nc nd One H).        
      intros.
      case H0.             
      intro.
      elim a0.
      intros.     
      assumption.
      intros.
      apply False_ind.      
      elim a0.
      intros.
      generalize (Zsgn_12 (na + nb) z).
      intro.
      apply Z.lt_irrefl with 0%Z.
      apply Z.lt_trans with (na + nb)%Z.
      assumption.
      assumption.
Defined.

Lemma Qhomographic_Qpositive_to_Q_homographicAcc_pos_2 :
 forall (a b c d : Z) (p : Qpositive)
   (H_Qhomographic_sg_denom_nonzero : Qhomographic_sg_denom_nonzero c d p),
 (a * d)%Z <> (b * c)%Z ->
 h_sign a b c d p H_Qhomographic_sg_denom_nonzero = 1%Z ->
 (Z.sgn
    (new_a a b c d p H_Qhomographic_sg_denom_nonzero +
     new_b a b c d p H_Qhomographic_sg_denom_nonzero) <= 0)%Z ->
 homographicAcc (- new_a a b c d p H_Qhomographic_sg_denom_nonzero)
   (- new_b a b c d p H_Qhomographic_sg_denom_nonzero)
   (- new_c a b c d p H_Qhomographic_sg_denom_nonzero)
   (- new_d a b c d p H_Qhomographic_sg_denom_nonzero)
   (new_p a b c d p H_Qhomographic_sg_denom_nonzero).
Proof.
 intros a b c d p H_hsign ad_neq_bc l1_eq_one z.
 set (na := new_a a b c d p H_hsign) in *.
 set (nb := new_b a b c d p H_hsign) in *.
 set (nc := new_c a b c d p H_hsign) in *.
 set (nd := new_d a b c d p H_hsign) in *.
 set (l3 := new_p a b c d p H_hsign) in *.
 assert
  (H : Qhomographic_sign a b c d p H_hsign = (1%Z, (na, (nb, (nc, nd)), l3))).
 unfold na, nb, nc, nd, l3 in |- *.
 rewrite <- l1_eq_one.
 unfold new_a, new_b, new_c, new_d, new_p in |- *.
 replace (h_sign a b c d p H_hsign) with
  (fst (Qhomographic_sign a b c d p H_hsign)); [ idtac | reflexivity ];
  repeat rewrite <- pair_1; reflexivity.
      destruct l3 as [p0| p0| ].
      (* l3 = (nR p0) *)
      apply homographicAcc_wf.
      generalize (sg_pos_1 a b c d p H_hsign na nb nc nd (nR p0) H).
      intro.
      case H0. 
      intros.
      apply False_ind.
      elim a0.
      intros.      
      generalize (Zsgn_14 _ z).
      intro.
      apply Z.lt_irrefl with 0%Z.
      apply Z.lt_le_trans with (na + nb)%Z.
      assumption.
      assumption.
      intro.
      elim a0.
      intros.
      rewrite <- Zopp_plus_distr.
      apply Zlt_neg_opp.
      assumption.
      generalize (sg_pos_1 a b c d p H_hsign na nb nc nd (nR p0) H).
      intro.
      case H0. 
      intros.
      apply False_ind.
      elim a0.
      intros.      
      generalize (Zsgn_14 _ z).
      intro.
      apply Z.lt_irrefl with 0%Z.
      apply Z.lt_le_trans with (na + nb)%Z.
      assumption.
      assumption.
      intro.
      elim a0.
      intros.
      rewrite <- Zopp_plus_distr.
      apply Zlt_neg_opp.
      assumption.
      generalize (sg_pos_2 a b c d p H_hsign na nb nc nd (nR p0) H). 
      intro.
      case H0.         
      intro.
      case s.
      intro.
      elim a0.
      intros.
      case (Z_le_lt_eq_dec 0 na H1).
      intro.
      apply False_ind.
      elim H2.
      intros.
      apply Z.lt_irrefl with 0%Z.
      apply Z.lt_le_trans with (na + nb)%Z.
      rewrite Zplus_0_r_reverse with 0%Z.
      apply Zplus_lt_le_compat.
      assumption.      
      assumption.
      apply (Zsgn_14 _ z).
      intro.
      rewrite <- e.
      simpl in |- *.
      apply Z.le_refl.
      intro.
      elim a0.
      intros.
      apply Zle_neg_opp.      
      assumption.
      intro.      
      discriminate e.
      generalize (sg_pos_2 a b c d p H_hsign na nb nc nd (nR p0) H). 
      intro.
      case H0.         
      intro.
      case s.
      intro.
      elim a0.
      intros.
      elim H2.
      intros.
      case (Z_le_lt_eq_dec 0 nb H3).
      intro.
      apply False_ind.
      apply Z.lt_irrefl with 0%Z.
      apply Z.lt_le_trans with (na + nb)%Z.
      rewrite Zplus_0_r_reverse with 0%Z.
      apply Zplus_le_lt_compat.
      assumption.      
      assumption.
      apply (Zsgn_14 _ z).
      intro.
      rewrite <- e.
      simpl in |- *.
      apply Z.le_refl.
      intro.
      elim a0.
      intros.
      elim H2.
      intros.
      apply Zle_neg_opp.      
      assumption.
      intro.      
      discriminate e.
      generalize (sg_pos_2 a b c d p H_hsign na nb nc nd (nR p0) H). 
      intro.
      case H0.         
      intro.
      case s.
      intro.
      elim a0.
      intros.
      elim H2.
      intros.
      elim H4.
      intros.
      case (Z_le_lt_eq_dec 0 nc H5).
      intro.
      apply False_ind.
      apply Z.lt_irrefl with 0%Z.
      apply Z.lt_le_trans with (nc + nd)%Z.
      rewrite Zplus_0_r_reverse with 0%Z.
      apply Zplus_lt_le_compat.
      assumption.      
      assumption.
      case (sg_pos_1 a b c d p H_hsign na nb nc nd (nR p0) H).
      intro. 
      apply False_ind.
      elim a1.
      intros.
      apply Z.lt_irrefl with 0%Z.
      apply Z.lt_le_trans with (na + nb)%Z.
      assumption.
      apply (Zsgn_14 _ z).
      intros.
      elim a1.
      intros.
      apply Zlt_le_weak.      
      assumption.
      intro.
      rewrite <- e.
      simpl in |- *.
      apply Z.le_refl.
      intro.
      elim a0.
      intros.
      elim H2.
      intros.
      elim H4. 
      intros.
      apply Zle_neg_opp.      
      assumption.
      intro.      
      discriminate e.
      generalize (sg_pos_2 a b c d p H_hsign na nb nc nd (nR p0) H). 
      intro.
      case H0.         
      intro.
      case s.
      intro.
      elim a0.
      intros.
      elim H2.
      intros.
      elim H4.
      intros.
      case (Z_le_lt_eq_dec 0 nd H6).
      intro.
      apply False_ind.
      apply Z.lt_irrefl with 0%Z.
      apply Z.lt_le_trans with (nc + nd)%Z.
      rewrite Zplus_0_r_reverse with 0%Z.
      apply Zplus_le_lt_compat.
      assumption.      
      assumption.
      case (sg_pos_1 a b c d p H_hsign na nb nc nd (nR p0) H).
      intro. 
      apply False_ind.
      elim a1.
      intros.
      apply Z.lt_irrefl with 0%Z.
      apply Z.lt_le_trans with (na + nb)%Z.
      assumption.
      apply (Zsgn_14 _ z).
      intros.
      elim a1.
      intros.
      apply Zlt_le_weak.      
      assumption.
      intro.
      rewrite <- e.
      simpl in |- *.
      apply Z.le_refl.
      intro.
      elim a0.
      intros.
      elim H2.
      intros.
      elim H4. 
      intros.
      apply Zle_neg_opp.      
      assumption.
      intro.      
      discriminate e.
      (* l3 = (dL p0) *)
      apply homographicAcc_wf.
      generalize (sg_pos_1 a b c d p H_hsign na nb nc nd (dL p0) H).
      intro.
      case H0. 
      intros.
      apply False_ind.
      elim a0.
      intros.      
      generalize (Zsgn_14 _ z).
      intro.
      apply Z.lt_irrefl with 0%Z.
      apply Z.lt_le_trans with (na + nb)%Z.
      assumption.
      assumption.
      intro.
      elim a0.
      intros.
      rewrite <- Zopp_plus_distr.
      apply Zlt_neg_opp.
      assumption.
      generalize (sg_pos_1 a b c d p H_hsign na nb nc nd (dL p0) H).
      intro.
      case H0. 
      intros.
      apply False_ind.
      elim a0.
      intros.      
      generalize (Zsgn_14 _ z).
      intro.
      apply Z.lt_irrefl with 0%Z.
      apply Z.lt_le_trans with (na + nb)%Z.
      assumption.
      assumption.
      intro.
      elim a0.
      intros.
      rewrite <- Zopp_plus_distr.
      apply Zlt_neg_opp.
      assumption.
      generalize (sg_pos_2 a b c d p H_hsign na nb nc nd (dL p0) H). 
      intro.
      case H0.         
      intro.
      case s.
      intro.
      elim a0.
      intros.
      case (Z_le_lt_eq_dec 0 na H1).
      intro.
      apply False_ind.
      elim H2.
      intros.
      apply Z.lt_irrefl with 0%Z.
      apply Z.lt_le_trans with (na + nb)%Z.
      rewrite Zplus_0_r_reverse with 0%Z.
      apply Zplus_lt_le_compat.
      assumption.      
      assumption.
      apply (Zsgn_14 _ z).
      intro.
      rewrite <- e.
      simpl in |- *.
      apply Z.le_refl.
      intro.
      elim a0.
      intros.
      apply Zle_neg_opp.      
      assumption.
      intro.      
      discriminate e.
      generalize (sg_pos_2 a b c d p H_hsign na nb nc nd (dL p0) H). 
      intro.
      case H0.         
      intro.
      case s.
      intro.
      elim a0.
      intros.
      elim H2.
      intros.
      case (Z_le_lt_eq_dec 0 nb H3).
      intro.
      apply False_ind.
      apply Z.lt_irrefl with 0%Z.
      apply Z.lt_le_trans with (na + nb)%Z.
      rewrite Zplus_0_r_reverse with 0%Z.
      apply Zplus_le_lt_compat.
      assumption.      
      assumption.
      apply (Zsgn_14 _ z).
      intro.
      rewrite <- e.
      simpl in |- *.
      apply Z.le_refl.
      intro.
      elim a0.
      intros.
      elim H2.
      intros.
      apply Zle_neg_opp.      
      assumption.
      intro.      
      discriminate e.
      generalize (sg_pos_2 a b c d p H_hsign na nb nc nd (dL p0) H). 
      intro.
      case H0.         
      intro.
      case s.
      intro.
      elim a0.
      intros.
      elim H2.
      intros.
      elim H4.
      intros.
      case (Z_le_lt_eq_dec 0 nc H5).
      intro.
      apply False_ind.
      apply Z.lt_irrefl with 0%Z.
      apply Z.lt_le_trans with (nc + nd)%Z.
      rewrite Zplus_0_r_reverse with 0%Z.
      apply Zplus_lt_le_compat.
      assumption.      
      assumption.
      case (sg_pos_1 a b c d p H_hsign na nb nc nd (dL p0) H).
      intro. 
      apply False_ind.
      elim a1.
      intros.
      apply Z.lt_irrefl with 0%Z.
      apply Z.lt_le_trans with (na + nb)%Z.
      assumption.
      apply (Zsgn_14 _ z).
      intros.
      elim a1.
      intros.
      apply Zlt_le_weak.      
      assumption.
      intro.
      rewrite <- e.
      simpl in |- *.
      apply Z.le_refl.
      intro.
      elim a0.
      intros.
      elim H2.
      intros.
      elim H4. 
      intros.
      apply Zle_neg_opp.      
      assumption.
      intro.      
      discriminate e.
      generalize (sg_pos_2 a b c d p H_hsign na nb nc nd (dL p0) H). 
      intro.
      case H0.         
      intro.
      case s.
      intro.
      elim a0.
      intros.
      elim H2.
      intros.
      elim H4.
      intros.
      case (Z_le_lt_eq_dec 0 nd H6).
      intro.
      apply False_ind.
      apply Z.lt_irrefl with 0%Z.
      apply Z.lt_le_trans with (nc + nd)%Z.
      rewrite Zplus_0_r_reverse with 0%Z.
      apply Zplus_le_lt_compat.
      assumption.      
      assumption.
      case (sg_pos_1 a b c d p H_hsign na nb nc nd (dL p0) H).
      intro. 
      apply False_ind.
      elim a1.
      intros.
      apply Z.lt_irrefl with 0%Z.
      apply Z.lt_le_trans with (na + nb)%Z.
      assumption.
      apply (Zsgn_14 _ z).
      intros.
      elim a1.
      intros.
      apply Zlt_le_weak.      
      assumption.
      intro.
      rewrite <- e.
      simpl in |- *.
      apply Z.le_refl.
      intro.
      elim a0.
      intros.
      elim H2.
      intros.
      elim H4. 
      intros.
      apply Zle_neg_opp.      
      assumption.
      intro.      
      discriminate e.
      (* l3 = One *)
      apply homographicacc0.
      reflexivity.
      generalize (sg_pos_1 a b c d p H_hsign na nb nc nd One H).
      intro.
      case H0. 
      intros.
      apply False_ind.
      elim a0.
      intros.      
      generalize (Zsgn_14 _ z).
      intro.
      apply Z.lt_irrefl with 0%Z.
      apply Z.lt_le_trans with (na + nb)%Z.
      assumption.
      assumption.
      intro.
      elim a0.
      intros.
      rewrite <- Zopp_plus_distr.
      apply Zlt_neg_opp.
      assumption.
      generalize (sg_pos_1 a b c d p H_hsign na nb nc nd One H).
      intro.
      case H0. 
      intros.
      apply False_ind.
      elim a0.
      intros.      
      generalize (Zsgn_14 _ z).
      intro.
      apply Z.lt_irrefl with 0%Z.
      apply Z.lt_le_trans with (na + nb)%Z.
      assumption.
      assumption.
      intro.
      elim a0.
      intros.
      rewrite <- Zopp_plus_distr.
      apply Zlt_neg_opp.
      assumption.
Defined.


Lemma Qhomographic_Qpositive_to_Q_homographicAcc_neg_1 :
 forall (a b c d : Z) (p : Qpositive)
   (H_hsign : Qhomographic_sg_denom_nonzero c d p),
 (a * d)%Z <> (b * c)%Z ->
 h_sign a b c d p H_hsign = (-1)%Z ->
 (Z.sgn (new_a a b c d p H_hsign + new_b a b c d p H_hsign) < 0)%Z ->
 homographicAcc (- new_a a b c d p H_hsign) (- new_b a b c d p H_hsign)
   (new_c a b c d p H_hsign) (new_d a b c d p H_hsign)
   (new_p a b c d p H_hsign).
Proof.
 intros a b c d p H_hsign ad_neq_bc l1_eq__minus_one z.
 set (na := new_a a b c d p H_hsign) in *.
 set (nb := new_b a b c d p H_hsign) in *.
 set (nc := new_c a b c d p H_hsign) in *.
 set (nd := new_d a b c d p H_hsign) in *.
 set (l3 := new_p a b c d p H_hsign) in *.
 assert
  (H :
   Qhomographic_sign a b c d p H_hsign = ((-1)%Z, (na, (nb, (nc, nd)), l3))).
 unfold na, nb, nc, nd, l3 in |- *.
 rewrite <- l1_eq__minus_one.
 unfold new_a, new_b, new_c, new_d, new_p in |- *.
 replace (h_sign a b c d p H_hsign) with
  (fst (Qhomographic_sign a b c d p H_hsign)); [ idtac | reflexivity ];
  repeat rewrite <- pair_1; reflexivity.
      destruct l3 as [p0| p0| ].
      (* l3 = (nR p0) *)
      apply homographicAcc_wf.
      rewrite <- Zopp_plus_distr.
      apply Zlt_neg_opp.
      apply Zsgn_11.
      assumption.
     
      generalize (sg_neg_1 a b c d p H_hsign na nb nc nd (nR p0) H).        
      intros.
      case H0.             
      intro.
      elim a0.
      intros.     
      apply False_ind.      
      generalize (Zsgn_11 (na + nb) z).
      intro.
      apply Z.lt_irrefl with 0%Z.
      apply Z.lt_trans with (na + nb)%Z.
      assumption.
      assumption.
      intros.
      elim a0.    
      intros.  
      assumption.
      generalize (sg_neg_2 a b c d p H_hsign na nb nc nd (nR p0) H). 
      intro.
      case H0.         
      intro.
      case s.
      intro.
      apply False_ind.
      elim a0.
      intros.
      elim H2.
      intros.
      apply Z.lt_irrefl with 0%Z.
      apply Z.le_lt_trans with (na + nb)%Z.
      rewrite Zplus_0_r_reverse with 0%Z.
      apply Zplus_le_compat.
      assumption.      
      assumption.
      apply Zsgn_11.
      assumption.
      intro.
      elim a0.
      intros.
      apply Zle_neg_opp.
      assumption.
      intro.      
      discriminate e.
      generalize (sg_neg_2 a b c d p H_hsign na nb nc nd (nR p0) H). 
      intro.
      case H0.         
      intro.
      case s.
      intro.
      elim a0. 
      intros.
      elim H2.
      intros.
      apply False_ind.
      apply Z.lt_irrefl with 0%Z.
      apply Z.le_lt_trans with (na + nb)%Z.
      rewrite Zplus_0_r_reverse with 0%Z.
      apply Zplus_le_compat.
      assumption.      
      assumption.
      apply Zsgn_11.
      assumption.
      intros.
      elim a0.
      intros.
      elim H2.
      intros.
      apply Zle_neg_opp.
      assumption.
      intro.
      discriminate e.
      generalize (sg_neg_2 a b c d p H_hsign na nb nc nd (nR p0) H). 
      intro.
      case H0.         
      intro.
      case s.
      intro.
      elim a0. 
      intros.
      elim H2.
      intros.
      apply False_ind.
      apply Z.lt_irrefl with 0%Z.
      apply Z.le_lt_trans with (na + nb)%Z.
      rewrite Zplus_0_r_reverse with 0%Z.
      apply Zplus_le_compat.
      assumption.      
      assumption.
      apply Zsgn_11.
      assumption.
      intros.
      elim a0.
      intros.
      elim H2.
      intros.
      elim H4.
      intros.
      assumption.
      intro.      
      discriminate e.
      generalize (sg_neg_2 a b c d p H_hsign na nb nc nd (nR p0) H). 
      intro.
      case H0.         
      intro.
      case s.
      intro.
      elim a0. 
      intros.
      elim H2.
      intros.
      apply False_ind.
      apply Z.lt_irrefl with 0%Z.
      apply Z.le_lt_trans with (na + nb)%Z.
      rewrite Zplus_0_r_reverse with 0%Z.
      apply Zplus_le_compat.
      assumption.      
      assumption.
      apply Zsgn_11.
      assumption.
      intro.
      elim a0. 
      intros.
      elim H2.
      intros.
      elim H4.
      intros.
      assumption.
      intro.      
      discriminate e.
      (* l3 = (dL p0) *)
      apply homographicAcc_wf.
      rewrite <- Zopp_plus_distr.
      apply Zlt_neg_opp.
      apply Zsgn_11.
      assumption.
     
      generalize (sg_neg_1 a b c d p H_hsign na nb nc nd (dL p0) H).        
      intros.
      case H0.             
      intro.
      elim a0.
      intros.     
      apply False_ind.      
      generalize (Zsgn_11 (na + nb) z).
      intro.
      apply Z.lt_irrefl with 0%Z.
      apply Z.lt_trans with (na + nb)%Z.
      assumption.
      assumption.
      intros.
      elim a0.    
      intros.  
      assumption.
      generalize (sg_neg_2 a b c d p H_hsign na nb nc nd (dL p0) H). 
      intro.
      case H0.         
      intro.
      case s.
      intro.
      apply False_ind.
      elim a0.
      intros.
      elim H2.
      intros.
      apply Z.lt_irrefl with 0%Z.
      apply Z.le_lt_trans with (na + nb)%Z.
      rewrite Zplus_0_r_reverse with 0%Z.
      apply Zplus_le_compat.
      assumption.      
      assumption.
      apply Zsgn_11.
      assumption.
      intro.
      elim a0.
      intros.
      apply Zle_neg_opp.
      assumption.
      intro.      
      discriminate e.
      generalize (sg_neg_2 a b c d p H_hsign na nb nc nd (dL p0) H). 
      intro.
      case H0.         
      intro.
      case s.
      intro.
      elim a0. 
      intros.
      elim H2.
      intros.
      apply False_ind.
      apply Z.lt_irrefl with 0%Z.
      apply Z.le_lt_trans with (na + nb)%Z.
      rewrite Zplus_0_r_reverse with 0%Z.
      apply Zplus_le_compat.
      assumption.      
      assumption.
      apply Zsgn_11.
      assumption.
      intros.
      elim a0.
      intros.
      elim H2.
      intros.
      apply Zle_neg_opp.
      assumption.
      intro.
      discriminate e.
      generalize (sg_neg_2 a b c d p H_hsign na nb nc nd (dL p0) H). 
      intro.
      case H0.         
      intro.
      case s.
      intro.
      elim a0. 
      intros.
      elim H2.
      intros.
      apply False_ind.
      apply Z.lt_irrefl with 0%Z.
      apply Z.le_lt_trans with (na + nb)%Z.
      rewrite Zplus_0_r_reverse with 0%Z.
      apply Zplus_le_compat.
      assumption.      
      assumption.
      apply Zsgn_11.
      assumption.
      intros.
      elim a0.
      intros.
      elim H2.
      intros.
      elim H4.
      intros.
      assumption.
      intro.      
      discriminate e.
      generalize (sg_neg_2 a b c d p H_hsign na nb nc nd (dL p0) H). 
      intro.
      case H0.         
      intro.
      case s.
      intro.
      elim a0. 
      intros.
      elim H2.
      intros.
      apply False_ind.
      apply Z.lt_irrefl with 0%Z.
      apply Z.le_lt_trans with (na + nb)%Z.
      rewrite Zplus_0_r_reverse with 0%Z.
      apply Zplus_le_compat.
      assumption.      
      assumption.
      apply Zsgn_11.
      assumption.
      intro.
      elim a0. 
      intros.
      elim H2.
      intros.
      elim H4.
      intros.
      assumption.
      intro.      
      discriminate e.
      (* l3 = One *)
      apply homographicacc0.
      reflexivity.
      rewrite <- Zopp_plus_distr.
      apply Zlt_neg_opp.
      apply Zsgn_11.
      assumption.
      generalize (sg_neg_1 a b c d p H_hsign na nb nc nd One H).        
      intros.
      case H0.             
      intro.
      elim a0.
      intros.     
      apply False_ind.      
      generalize (Zsgn_11 (na + nb) z).
      intro.
      apply Z.lt_irrefl with 0%Z.
      apply Z.lt_trans with (na + nb)%Z.
      assumption.
      assumption.
      intro.
      elim a0.
      intros.
      assumption.
Defined.


Lemma Qhomographic_Qpositive_to_Q_homographicAcc_neg_2 :
 forall (a b c d : Z) (p : Qpositive)
   (H_hsign : Qhomographic_sg_denom_nonzero c d p),
 (a * d)%Z <> (b * c)%Z ->
 h_sign a b c d p H_hsign = (-1)%Z ->
 (0 <= Z.sgn (new_a a b c d p H_hsign + new_b a b c d p H_hsign))%Z ->
 homographicAcc (new_a a b c d p H_hsign) (new_b a b c d p H_hsign)
   (- new_c a b c d p H_hsign) (- new_d a b c d p H_hsign)
   (new_p a b c d p H_hsign).
Proof.
 intros a b c d p H_hsign ad_neq_bc l1_eq__minus_one z.
 set (na := new_a a b c d p H_hsign) in *.
 set (nb := new_b a b c d p H_hsign) in *.
 set (nc := new_c a b c d p H_hsign) in *.
 set (nd := new_d a b c d p H_hsign) in *.
 set (l3 := new_p a b c d p H_hsign) in *.
 assert
  (H :
   Qhomographic_sign a b c d p H_hsign = ((-1)%Z, (na, (nb, (nc, nd)), l3))).
 unfold na, nb, nc, nd, l3 in |- *.
 rewrite <- l1_eq__minus_one.
 unfold new_a, new_b, new_c, new_d, new_p in |- *.
 replace (h_sign a b c d p H_hsign) with
  (fst (Qhomographic_sign a b c d p H_hsign)); [ idtac | reflexivity ];
  repeat rewrite <- pair_1; reflexivity.
      destruct l3 as [p0| p0| ].
      (* l3 = (nR p0) *)
      apply homographicAcc_wf.
      generalize (sg_neg_1 a b c d p H_hsign na nb nc nd (nR p0) H).
      intro.
      case H0. 
      intros.
      elim a0.
      intros.
      assumption.
      intros.
      apply False_ind.
      elim a0.
      intros.      
      generalize (Zsgn_13 _ z).
      intro.
      apply Z.lt_irrefl with 0%Z.
      apply Z.le_lt_trans with (na + nb)%Z.
      assumption.
      assumption.
      generalize (sg_neg_1 a b c d p H_hsign na nb nc nd (nR p0) H).
      intro.
      case H0. 
      intros.
      elim a0.
      intros.
      rewrite <- Zopp_plus_distr.      
      apply Zlt_neg_opp.
      assumption.
      intros.
      apply False_ind.
      elim a0.
      intros.      
      generalize (Zsgn_13 _ z).
      intro.
      apply Z.lt_irrefl with 0%Z.
      apply Z.le_lt_trans with (na + nb)%Z.
      assumption.
      assumption.
      generalize (sg_neg_2 a b c d p H_hsign na nb nc nd (nR p0) H). 
      intro.
      case H0.         
      intro.
      case s.
      intro.
      elim a0.
      intros.
      assumption.
      intros.
      elim a0.
      intros.
      case (Z_le_lt_eq_dec na 0 H1).
      intro.
      apply False_ind.
      elim H2.
      intros.
      apply Z.lt_irrefl with 0%Z.
      apply Z.le_lt_trans with (na + nb)%Z.
      apply (Zsgn_13 _ z).
      rewrite Zplus_0_r_reverse with 0%Z.
      apply Zplus_lt_le_compat.
      assumption.      
      assumption.
      intro.
      rewrite e.
      apply Z.le_refl.
      intro.      
      discriminate e.
      generalize (sg_neg_2 a b c d p H_hsign na nb nc nd (nR p0) H). 
      intro.
      case H0.         
      intro.
      case s.
      intro.
      elim a0.
      intros.
      elim H2.
      intros.
      assumption.
      intros.
      elim a0.
      intros.
      elim H2.
      intros.
      case (Z_le_lt_eq_dec nb 0 H3).
      intro.
      apply False_ind.
      apply Z.lt_irrefl with 0%Z.
      apply Z.le_lt_trans with (na + nb)%Z.
      apply (Zsgn_13 _ z).
      rewrite Zplus_0_r_reverse with 0%Z.
      apply Zplus_le_lt_compat.
      assumption.      
      assumption.
      intro.
      rewrite e.
      apply Z.le_refl.
      intro.      
      discriminate e.
      generalize (sg_neg_2 a b c d p H_hsign na nb nc nd (nR p0) H). 
      intro.
      case H0.         
      intro.
      case s.
      intro.
      elim a0.
      intros.
      elim H2.
      intros.
      elim H4.
      intros.
      apply Zle_neg_opp.
      assumption.
      intro.
      elim a0.
      intros.
      elim H2.
      intros.
      elim H4.
      intros.
      case (Z_le_lt_eq_dec 0 nc H5).
      intro.
      apply False_ind.
      apply Z.lt_irrefl with 0%Z.
      apply Z.lt_trans with (nc + nd)%Z.
      rewrite Zplus_0_r_reverse with 0%Z.
      apply Zplus_lt_le_compat.
      assumption.      
      assumption.
      case (sg_neg_1 a b c d p H_hsign na nb nc nd (nR p0) H).
      intro. 
      elim a1.
      intros.
      assumption.
      intro.
      apply False_ind.
      apply Z.lt_irrefl with 0%Z.
      apply Z.le_lt_trans with (na + nb)%Z.
      apply (Zsgn_13 _ z). 
      elim a1.
      intros.
      assumption.
      intro.
      rewrite <- e.
      simpl in |- *.
      apply Z.le_refl.
      intro.      
      discriminate e.
      generalize (sg_neg_2 a b c d p H_hsign na nb nc nd (nR p0) H). 
      intro.
      case H0.         
      intro.
      case s.
      intro.
      elim a0.
      intros.
      elim H2.
      intros.
      elim H4.
      intros.
      apply Zle_neg_opp.
      assumption.
      intro.
      elim a0.
      intros.
      elim H2.
      intros.
      elim H4.
      intros.
      case (Z_le_lt_eq_dec 0 nd H6).
      intro.
      apply False_ind.
      apply Z.lt_irrefl with 0%Z.
      apply Z.lt_trans with (nc + nd)%Z.
      rewrite Zplus_0_r_reverse with 0%Z.
      apply Zplus_le_lt_compat.
      assumption.      
      assumption.
      case (sg_neg_1 a b c d p H_hsign na nb nc nd (nR p0) H).
      intro. 
      elim a1.
      intros.
      assumption.
      intro.
      apply False_ind.
      apply Z.lt_irrefl with 0%Z.
      apply Z.le_lt_trans with (na + nb)%Z.
      apply (Zsgn_13 _ z). 
      elim a1.
      intros.
      assumption.
      intro.
      rewrite <- e.
      simpl in |- *.
      apply Z.le_refl.
      intro.      
      discriminate e.
      (* l3 = (dL p0) *)
      apply homographicAcc_wf.
      generalize (sg_neg_1 a b c d p H_hsign na nb nc nd (dL p0) H).
      intro.
      case H0. 
      intros.
      elim a0.
      intros.
      assumption.
      intros.
      apply False_ind.
      elim a0.
      intros.      
      generalize (Zsgn_13 _ z).
      intro.
      apply Z.lt_irrefl with 0%Z.
      apply Z.le_lt_trans with (na + nb)%Z.
      assumption.
      assumption.
      generalize (sg_neg_1 a b c d p H_hsign na nb nc nd (dL p0) H).
      intro.
      case H0. 
      intros.
      elim a0.
      intros.
      rewrite <- Zopp_plus_distr.      
      apply Zlt_neg_opp.
      assumption.
      intros.
      apply False_ind.
      elim a0.
      intros.      
      generalize (Zsgn_13 _ z).
      intro.
      apply Z.lt_irrefl with 0%Z.
      apply Z.le_lt_trans with (na + nb)%Z.
      assumption.
      assumption.
      generalize (sg_neg_2 a b c d p H_hsign na nb nc nd (dL p0) H). 
      intro.
      case H0.         
      intro.
      case s.
      intro.
      elim a0.
      intros.
      assumption.
      intros.
      elim a0.
      intros.
      case (Z_le_lt_eq_dec na 0 H1).
      intro.
      apply False_ind.
      elim H2.
      intros.
      apply Z.lt_irrefl with 0%Z.
      apply Z.le_lt_trans with (na + nb)%Z.
      apply (Zsgn_13 _ z).
      rewrite Zplus_0_r_reverse with 0%Z.
      apply Zplus_lt_le_compat.
      assumption.      
      assumption.
      intro.
      rewrite e.
      apply Z.le_refl.
      intro.      
      discriminate e.
      generalize (sg_neg_2 a b c d p H_hsign na nb nc nd (dL p0) H). 
      intro.
      case H0.         
      intro.
      case s.
      intro.
      elim a0.
      intros.
      elim H2.
      intros.
      assumption.
      intros.
      elim a0.
      intros.
      elim H2.
      intros.
      case (Z_le_lt_eq_dec nb 0 H3).
      intro.
      apply False_ind.
      apply Z.lt_irrefl with 0%Z.
      apply Z.le_lt_trans with (na + nb)%Z.
      apply (Zsgn_13 _ z).
      rewrite Zplus_0_r_reverse with 0%Z.
      apply Zplus_le_lt_compat.
      assumption.      
      assumption.
      intro.
      rewrite e.
      apply Z.le_refl.
      intro.      
      discriminate e.
      generalize (sg_neg_2 a b c d p H_hsign na nb nc nd (dL p0) H). 
      intro.
      case H0.         
      intro.
      case s.
      intro.
      elim a0.
      intros.
      elim H2.
      intros.
      elim H4.
      intros.
      apply Zle_neg_opp.
      assumption.
      intro.
      elim a0.
      intros.
      elim H2.
      intros.
      elim H4.
      intros.
      case (Z_le_lt_eq_dec 0 nc H5).
      intro.
      apply False_ind.
      apply Z.lt_irrefl with 0%Z.
      apply Z.lt_trans with (nc + nd)%Z.
      rewrite Zplus_0_r_reverse with 0%Z.
      apply Zplus_lt_le_compat.
      assumption.      
      assumption.
      case (sg_neg_1 a b c d p H_hsign na nb nc nd (dL p0) H).
      intro. 
      elim a1.
      intros.
      assumption.
      intro.
      apply False_ind.
      apply Z.lt_irrefl with 0%Z.
      apply Z.le_lt_trans with (na + nb)%Z.
      apply (Zsgn_13 _ z). 
      elim a1.
      intros.
      assumption.
      intro.
      rewrite <- e.
      simpl in |- *.
      apply Z.le_refl.
      intro.      
      discriminate e.
      generalize (sg_neg_2 a b c d p H_hsign na nb nc nd (dL p0) H). 
      intro.
      case H0.         
      intro.
      case s.
      intro.
      elim a0.
      intros.
      elim H2.
      intros.
      elim H4.
      intros.
      apply Zle_neg_opp.
      assumption.
      intro.
      elim a0.
      intros.
      elim H2.
      intros.
      elim H4.
      intros.
      case (Z_le_lt_eq_dec 0 nd H6).
      intro.
      apply False_ind.
      apply Z.lt_irrefl with 0%Z.
      apply Z.lt_trans with (nc + nd)%Z.
      rewrite Zplus_0_r_reverse with 0%Z.
      apply Zplus_le_lt_compat.
      assumption.      
      assumption.
      case (sg_neg_1 a b c d p H_hsign na nb nc nd (dL p0) H).
      intro. 
      elim a1.
      intros.
      assumption.
      intro.
      apply False_ind.
      apply Z.lt_irrefl with 0%Z.
      apply Z.le_lt_trans with (na + nb)%Z.
      apply (Zsgn_13 _ z). 
      elim a1.
      intros.
      assumption.
      intro.
      rewrite <- e.
      simpl in |- *.
      apply Z.le_refl.
      intro.      
      discriminate e.
      (* l3 = One *)
      apply homographicacc0.
      reflexivity.
      generalize (sg_neg_1 a b c d p H_hsign na nb nc nd One H).
      intro.
      case H0. 
      intros.
      elim a0.
      intros.
      assumption.
      intro.
      apply False_ind.
      elim a0.
      intros.      
      generalize (Zsgn_13 _ z).
      intro.
      apply Z.lt_irrefl with 0%Z.
      apply Z.le_lt_trans with (na + nb)%Z.
      assumption.
      assumption.
      rewrite <- Zopp_plus_distr.
      apply Zlt_neg_opp.
      generalize (sg_neg_1 a b c d p H_hsign na nb nc nd One H).
      intro.
      case H0. 
      intros.
      elim a0.
      intros.
      assumption.
      intro.
      apply False_ind.
      elim a0.
      intros.      
      generalize (Zsgn_13 _ z).
      intro.
      apply Z.lt_irrefl with 0%Z.
      apply Z.le_lt_trans with (na + nb)%Z.
      assumption.
      assumption.
Defined.
