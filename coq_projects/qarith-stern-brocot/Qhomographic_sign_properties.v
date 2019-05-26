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
Require Import ZArithRing Zaux.

Lemma sg_tuple_equal :
 forall (l1 a1 b1 c1 d1 : Z) (p1 : Qpositive) (l2 a2 b2 c2 d2 : Z)
   (p2 : Qpositive),
 (l1, (a1, (b1, (c1, d1)), p1)) = (l2, (a2, (b2, (c2, d2)), p2)) ->
 l1 = l2 /\ (a1 = a2 /\ b1 = b2 /\ c1 = c2 /\ d1 = d2) /\ p1 = p2.
Proof.
 intros.
 inversion H; (repeat split; reflexivity).
Qed.

Lemma inside_interval_1_inf :
 forall o1 o2 : Z,
 inside_interval_1 o1 o2 ->
 {(0 < o1)%Z /\ (0 < o2)%Z} + {(o1 < 0)%Z /\ (o2 < 0)%Z}.
Proof.
 intros o1 o2 H.
 case (Z_lt_dec 0 o1); intros Ho1;
            [ case (Z_lt_dec 0 o2); intros Ho2;
               [ left; split; assumption | idtac ]
            | case (Z_lt_dec o1 0); intros Ho1';
               [ case (Z_lt_dec o2 0); intros Ho2;
                  [ right; split; assumption | idtac ]
               | idtac ] ]; apply False_rec; case H; 
            intros (Ho1_, Ho2_);
            repeat
             match goal with
             | id1:(~ (?X1 < ?X2)%Z) |- ?X3 => apply id1; assumption
             end ||
               match goal with
               | id1:(0 < ?X2)%Z,id2:(?X2 < 0)%Z |- ?X3 =>
                   apply (Z.lt_irrefl 0); apply Z.lt_trans with X2; assumption
               end.
Qed.       
   

Lemma inside_interval_2_inf :
 forall o1 o2 : Z,
 inside_interval_2 o1 o2 ->
 {(0 < o1)%Z /\ (o2 < 0)%Z} + {(o1 < 0)%Z /\ (0 < o2)%Z}.
Proof.
 intros o1 o2 H.
 case (Z_lt_dec 0 o1); intros Ho1;
            [ case (Z_lt_dec o2 0); intros Ho2;
               [ left; split; assumption | idtac ]
            | case (Z_lt_dec o1 0); intros Ho1';
               [ case (Z_lt_dec 0 o2); intros Ho2;
                  [ right; split; assumption | idtac ]
               | idtac ] ]; apply False_rec; case H; 
            intros (Ho1_, Ho2_);
            repeat
             match goal with
             | id1:(~ (?X1 < ?X2)%Z) |- ?X3 => apply id1; assumption
             end ||
               match goal with
               | id1:(0 < ?X2)%Z,id2:(?X2 < 0)%Z |- ?X3 =>
                   apply (Z.lt_irrefl 0); apply Z.lt_trans with X2; assumption
               end.
Qed.       
   

Lemma sg_pos_1 :
 forall (a b c d : Z) (p : Qpositive)
   (H_Qhomographic_sg_denom_nonzero : Qhomographic_sg_denom_nonzero c d p)
   (na nb nc nd : Z) (np : Qpositive),
 Qhomographic_sign a b c d p H_Qhomographic_sg_denom_nonzero =
 (1%Z, (na, (nb, (nc, nd)), np)) ->
 {(0 < na + nb)%Z /\ (0 < nc + nd)%Z} + {(na + nb < 0)%Z /\ (nc + nd < 0)%Z}.
Proof.
 fix sg_pos_1 5.
 intros a b c d p H_Qhomographic_sg_denom_nonzero na nb nc nd np H_sg.
 set (o1 := outside_interval a b) in *.
 set (o2 := outside_interval c d) in *.
 destruct p as [p| p| ].
 (* p = (nR p) *) 
 case (Z_zerop b); intro Hb.
  case (Z_zerop d); intro Hd.
   generalize
    (Qhomographic_sign_nR_1 a b c d (nR p) p H_Qhomographic_sg_denom_nonzero
       (refl_equal (nR p)) Hb Hd); intro;
    assert
     (H6 :
      (1%Z, (na, (nb, (nc, nd)), np)) =
      ((Z.sgn a * Z.sgn c)%Z, (a, (b, (c, d)), nR p)));
    [ apply
       trans_eq
        with
          (Qhomographic_sign a b c d (nR p) H_Qhomographic_sg_denom_nonzero);
       assumption || symmetry  in |- *; assumption
    | elim
       (sg_tuple_equal 1 na nb nc nd np (Z.sgn a * Z.sgn c) a b c d (nR p) H6);
       intros H_ac ((H8, (H9, (H10, H11))), H12);
       repeat match goal with
              | id1:(?X1 = ?X2) |- ?X3 => rewrite id1
              end; repeat rewrite Zplus_0_r; apply Zsgn_16; 
       rewrite Zsgn_15; symmetry  in |- *; assumption ].
  
   case (Z_lt_dec 0 o2); intros Ho2.
    generalize
     (Qhomographic_sign_nR_2 a b c d (nR p) p H_Qhomographic_sg_denom_nonzero
        (refl_equal (nR p)) Hb Hd Ho2); intro;
     assert
      (H6 :
       (1%Z, (na, (nb, (nc, nd)), np)) = (Z.sgn a, (a, (b, (c, d)), nR p)));
     [ apply
        trans_eq
         with
           (Qhomographic_sign a b c d (nR p) H_Qhomographic_sg_denom_nonzero);
        assumption || symmetry  in |- *; assumption
     | elim (sg_tuple_equal 1 na nb nc nd np (Z.sgn a) a b c d (nR p) H6);
        intros H_a ((H8, (H9, (H10, H11))), H12);
        repeat match goal with
               | id1:(?X1 = ?X2) |- ?X3 => rewrite id1
               end; repeat rewrite Zplus_0_r; left; 
        split; [ apply Zsgn_9; symmetry  in |- * | apply Zsgn_19 ];
        assumption ].
    
    case (Z_lt_dec o2 0); intros Ho2'.
     generalize
      (Qhomographic_sign_nR_3 a b c d (nR p) p
         H_Qhomographic_sg_denom_nonzero (refl_equal (nR p)) Hb Hd Ho2 Ho2');
      intro;
      assert
       (H6 :
        (1%Z, (na, (nb, (nc, nd)), np)) =
        ((- Z.sgn a)%Z, (a, (b, (c, d)), nR p)));
      [ apply
         trans_eq
          with
            (Qhomographic_sign a b c d (nR p) H_Qhomographic_sg_denom_nonzero);
         assumption || symmetry  in |- *; assumption
      | elim (sg_tuple_equal 1 na nb nc nd np (- Z.sgn a) a b c d (nR p) H6);
         intros H_a ((H8, (H9, (H10, H11))), H12);
         repeat match goal with
                | id1:(?X1 = ?X2) |- ?X3 => rewrite id1
                end; repeat rewrite Zplus_0_r; right; 
         split;
         [ apply Zsgn_10; symmetry  in |- *; apply Z.opp_inj | apply Zsgn_20 ];
         assumption ].
 
     generalize
      (Qhomographic_sign_nR_4 a b c d (nR p) p
         (Qhomographic_signok_2 c d p H_Qhomographic_sg_denom_nonzero)
         H_Qhomographic_sg_denom_nonzero Hb Hd Ho2 Ho2'); 
      intro;
      apply
       (sg_pos_1 a (a + b)%Z c (c + d)%Z p
          (Qhomographic_signok_2 c d p H_Qhomographic_sg_denom_nonzero) na nb
          nc nd np);
      apply
       trans_eq
        with
          (Qhomographic_sign a b c d (nR p) H_Qhomographic_sg_denom_nonzero);
      assumption || symmetry  in |- *; assumption.


  case (Z_zerop d); intro Hd. 
   case (Z_lt_dec 0 o1); intro Ho1. 
    generalize
     (Qhomographic_sign_nR_5 a b c d (nR p) p H_Qhomographic_sg_denom_nonzero
        (refl_equal (nR p)) Hb Hd Ho1); intro;
     assert
      (H6 :
       (1%Z, (na, (nb, (nc, nd)), np)) = (Z.sgn c, (a, (b, (c, d)), nR p)));
     [ apply
        trans_eq
         with
           (Qhomographic_sign a b c d (nR p) H_Qhomographic_sg_denom_nonzero);
        assumption || symmetry  in |- *; assumption
     | elim (sg_tuple_equal 1 na nb nc nd np (Z.sgn c) a b c d (nR p) H6);
        intros H_a ((H8, (H9, (H10, H11))), H12);
        repeat match goal with
               | id1:(?X1 = ?X2) |- ?X3 => rewrite id1
               end; repeat rewrite Zplus_0_r; left; 
        split; [ apply Zsgn_19 | apply Zsgn_9; symmetry  in |- * ];
        assumption ].
    
    case (Z_lt_dec o1 0); intros Ho1'.
     generalize
      (Qhomographic_sign_nR_6 a b c d (nR p) p
         H_Qhomographic_sg_denom_nonzero (refl_equal (nR p)) Hb Hd Ho1 Ho1');
      intro;
      assert
       (H6 :
        (1%Z, (na, (nb, (nc, nd)), np)) =
        ((- Z.sgn c)%Z, (a, (b, (c, d)), nR p)));
      [ apply
         trans_eq
          with
            (Qhomographic_sign a b c d (nR p) H_Qhomographic_sg_denom_nonzero);
         assumption || symmetry  in |- *; assumption
      | elim (sg_tuple_equal 1 na nb nc nd np (- Z.sgn c) a b c d (nR p) H6);
         intros H_a ((H8, (H9, (H10, H11))), H12);
         repeat match goal with
                | id1:(?X1 = ?X2) |- ?X3 => rewrite id1
                end; repeat rewrite Zplus_0_r; right; 
         split;
         [ apply Zsgn_20 | apply Zsgn_10; symmetry  in |- *; apply Z.opp_inj ];
         assumption ].
 
     generalize
      (Qhomographic_sign_nR_7 a b c d (nR p) p
         (Qhomographic_signok_2 c d p H_Qhomographic_sg_denom_nonzero)
         H_Qhomographic_sg_denom_nonzero Hb Hd Ho1 Ho1'); 
      intro;
      apply
       (sg_pos_1 a (a + b)%Z c (c + d)%Z p
          (Qhomographic_signok_2 c d p H_Qhomographic_sg_denom_nonzero) na nb
          nc nd np);
      apply
       trans_eq
        with
          (Qhomographic_sign a b c d (nR p) H_Qhomographic_sg_denom_nonzero);
      assumption || symmetry  in |- *; assumption.

  case (inside_interval_1_dec_inf o1 o2); intro H_inside_1;
   [ generalize
      (Qhomographic_sign_nR_8 a b c d (nR p) p
         H_Qhomographic_sg_denom_nonzero (refl_equal (nR p)) Hb Hd H_inside_1);
      intro;
      assert
       (H6 : (1%Z, (na, (nb, (nc, nd)), np)) = (1%Z, (a, (b, (c, d)), nR p)));
      [ apply
         trans_eq
          with
            (Qhomographic_sign a b c d (nR p) H_Qhomographic_sg_denom_nonzero);
         assumption || symmetry  in |- *; assumption
      | elim (sg_tuple_equal 1 na nb nc nd np 1 a b c d (nR p) H6);
         intros _ ((H8, (H9, (H10, H11))), H12);
         repeat match goal with
                | id1:(?X1 = ?X2) |- ?X3 => rewrite id1
                end; case (inside_interval_1_inf _ _ H_inside_1);
         intros (Ho1, Ho2);
         [ left; split; apply Zsgn_19 | right; split; apply Zsgn_20 ];
         assumption ]
   | case (inside_interval_2_dec_inf o1 o2); intro H_inside_2;
      [ generalize
         (Qhomographic_sign_nR_9 a b c d (nR p) p
            H_Qhomographic_sg_denom_nonzero (refl_equal (nR p)) Hb Hd
            H_inside_1 H_inside_2); intro; apply False_rec;
         assert
          (H6 :
           (1%Z, (na, (nb, (nc, nd)), np)) = ((-1)%Z, (a, (b, (c, d)), nR p)));
         [ apply
            trans_eq
             with
               (Qhomographic_sign a b c d (nR p)
                  H_Qhomographic_sg_denom_nonzero);
            assumption || symmetry  in |- *; assumption
         | elim (sg_tuple_equal 1 na nb nc nd np (-1) a b c d (nR p) H6);
            intros H7 H8; discriminate H7 ]
      | generalize
         (Qhomographic_sign_nR_10 a b c d (nR p) p
            (Qhomographic_signok_2 c d p H_Qhomographic_sg_denom_nonzero)
            H_Qhomographic_sg_denom_nonzero Hb Hd H_inside_1 H_inside_2);
         intro;
         apply
          (sg_pos_1 a (a + b)%Z c (c + d)%Z p
             (Qhomographic_signok_2 c d p H_Qhomographic_sg_denom_nonzero) na
             nb nc nd np);
         apply
          trans_eq
           with
             (Qhomographic_sign a b c d (nR p)
                H_Qhomographic_sg_denom_nonzero);
         assumption || symmetry  in |- *; assumption ] ].
 (* p = (dL p) *) 
 case (Z_zerop b); intro Hb.
  case (Z_zerop d); intro Hd.
   generalize
    (Qhomographic_sign_dL_1 a b c d (dL p) p H_Qhomographic_sg_denom_nonzero
       (refl_equal (dL p)) Hb Hd); intro;
    assert
     (H6 :
      (1%Z, (na, (nb, (nc, nd)), np)) =
      ((Z.sgn a * Z.sgn c)%Z, (a, (b, (c, d)), dL p)));
    [ apply
       trans_eq
        with
          (Qhomographic_sign a b c d (dL p) H_Qhomographic_sg_denom_nonzero);
       assumption || symmetry  in |- *; assumption
    | elim
       (sg_tuple_equal 1 na nb nc nd np (Z.sgn a * Z.sgn c) a b c d (dL p) H6);
       intros H_ac ((H8, (H9, (H10, H11))), H12);
       repeat match goal with
              | id1:(?X1 = ?X2) |- ?X3 => rewrite id1
              end; repeat rewrite Zplus_0_r; apply Zsgn_16; 
       rewrite Zsgn_15; symmetry  in |- *; assumption ].
  
   case (Z_lt_dec 0 o2); intros Ho2.
    generalize
     (Qhomographic_sign_dL_2 a b c d (dL p) p H_Qhomographic_sg_denom_nonzero
        (refl_equal (dL p)) Hb Hd Ho2); intro;
     assert
      (H6 :
       (1%Z, (na, (nb, (nc, nd)), np)) = (Z.sgn a, (a, (b, (c, d)), dL p)));
     [ apply
        trans_eq
         with
           (Qhomographic_sign a b c d (dL p) H_Qhomographic_sg_denom_nonzero);
        assumption || symmetry  in |- *; assumption
     | elim (sg_tuple_equal 1 na nb nc nd np (Z.sgn a) a b c d (dL p) H6);
        intros H_a ((H8, (H9, (H10, H11))), H12);
        repeat match goal with
               | id1:(?X1 = ?X2) |- ?X3 => rewrite id1
               end; repeat rewrite Zplus_0_r; left; 
        split; [ apply Zsgn_9; symmetry  in |- * | apply Zsgn_19 ];
        assumption ].
    
    case (Z_lt_dec o2 0); intros Ho2'.
     generalize
      (Qhomographic_sign_dL_3 a b c d (dL p) p
         H_Qhomographic_sg_denom_nonzero (refl_equal (dL p)) Hb Hd Ho2 Ho2');
      intro;
      assert
       (H6 :
        (1%Z, (na, (nb, (nc, nd)), np)) =
        ((- Z.sgn a)%Z, (a, (b, (c, d)), dL p)));
      [ apply
         trans_eq
          with
            (Qhomographic_sign a b c d (dL p) H_Qhomographic_sg_denom_nonzero);
         assumption || symmetry  in |- *; assumption
      | elim (sg_tuple_equal 1 na nb nc nd np (- Z.sgn a) a b c d (dL p) H6);
         intros H_a ((H8, (H9, (H10, H11))), H12);
         repeat match goal with
                | id1:(?X1 = ?X2) |- ?X3 => rewrite id1
                end; repeat rewrite Zplus_0_r; right; 
         split;
         [ apply Zsgn_10; symmetry  in |- *; apply Z.opp_inj | apply Zsgn_20 ];
         assumption ].
 
     generalize
      (Qhomographic_sign_dL_4 a b c d (dL p) p
         (Qhomographic_signok_3 c d p H_Qhomographic_sg_denom_nonzero)
         H_Qhomographic_sg_denom_nonzero Hb Hd Ho2 Ho2'); 
      intro;
      apply
       (sg_pos_1 (a + b)%Z b (c + d)%Z d p
          (Qhomographic_signok_3 c d p H_Qhomographic_sg_denom_nonzero) na nb
          nc nd np);
      apply
       trans_eq
        with
          (Qhomographic_sign a b c d (dL p) H_Qhomographic_sg_denom_nonzero);
      assumption || symmetry  in |- *; assumption.


  case (Z_zerop d); intro Hd. 
   case (Z_lt_dec 0 o1); intro Ho1. 
    generalize
     (Qhomographic_sign_dL_5 a b c d (dL p) p H_Qhomographic_sg_denom_nonzero
        (refl_equal (dL p)) Hb Hd Ho1); intro;
     assert
      (H6 :
       (1%Z, (na, (nb, (nc, nd)), np)) = (Z.sgn c, (a, (b, (c, d)), dL p)));
     [ apply
        trans_eq
         with
           (Qhomographic_sign a b c d (dL p) H_Qhomographic_sg_denom_nonzero);
        assumption || symmetry  in |- *; assumption
     | elim (sg_tuple_equal 1 na nb nc nd np (Z.sgn c) a b c d (dL p) H6);
        intros H_a ((H8, (H9, (H10, H11))), H12);
        repeat match goal with
               | id1:(?X1 = ?X2) |- ?X3 => rewrite id1
               end; repeat rewrite Zplus_0_r; left; 
        split; [ apply Zsgn_19 | apply Zsgn_9; symmetry  in |- * ];
        assumption ].
    
    case (Z_lt_dec o1 0); intros Ho1'.
     generalize
      (Qhomographic_sign_dL_6 a b c d (dL p) p
         H_Qhomographic_sg_denom_nonzero (refl_equal (dL p)) Hb Hd Ho1 Ho1');
      intro;
      assert
       (H6 :
        (1%Z, (na, (nb, (nc, nd)), np)) =
        ((- Z.sgn c)%Z, (a, (b, (c, d)), dL p)));
      [ apply
         trans_eq
          with
            (Qhomographic_sign a b c d (dL p) H_Qhomographic_sg_denom_nonzero);
         assumption || symmetry  in |- *; assumption
      | elim (sg_tuple_equal 1 na nb nc nd np (- Z.sgn c) a b c d (dL p) H6);
         intros H_a ((H8, (H9, (H10, H11))), H12);
         repeat match goal with
                | id1:(?X1 = ?X2) |- ?X3 => rewrite id1
                end; repeat rewrite Zplus_0_r; right; 
         split;
         [ apply Zsgn_20 | apply Zsgn_10; symmetry  in |- *; apply Z.opp_inj ];
         assumption ].
 
     generalize
      (Qhomographic_sign_dL_7 a b c d (dL p) p
         (Qhomographic_signok_3 c d p H_Qhomographic_sg_denom_nonzero)
         H_Qhomographic_sg_denom_nonzero Hb Hd Ho1 Ho1'); 
      intro;
      apply
       (sg_pos_1 (a + b)%Z b (c + d)%Z d p
          (Qhomographic_signok_3 c d p H_Qhomographic_sg_denom_nonzero) na nb
          nc nd np);
      apply
       trans_eq
        with
          (Qhomographic_sign a b c d (dL p) H_Qhomographic_sg_denom_nonzero);
      assumption || symmetry  in |- *; assumption.

  case (inside_interval_1_dec_inf o1 o2); intro H_inside_1;
   [ generalize
      (Qhomographic_sign_dL_8 a b c d (dL p) p
         H_Qhomographic_sg_denom_nonzero (refl_equal (dL p)) Hb Hd H_inside_1);
      intro;
      assert
       (H6 : (1%Z, (na, (nb, (nc, nd)), np)) = (1%Z, (a, (b, (c, d)), dL p)));
      [ apply
         trans_eq
          with
            (Qhomographic_sign a b c d (dL p) H_Qhomographic_sg_denom_nonzero);
         assumption || symmetry  in |- *; assumption
      | elim (sg_tuple_equal 1 na nb nc nd np 1 a b c d (dL p) H6);
         intros _ ((H8, (H9, (H10, H11))), H12);
         repeat match goal with
                | id1:(?X1 = ?X2) |- ?X3 => rewrite id1
                end; case (inside_interval_1_inf _ _ H_inside_1);
         intros (Ho1, Ho2);
         [ left; split; apply Zsgn_19 | right; split; apply Zsgn_20 ];
         assumption ]
   | case (inside_interval_2_dec_inf o1 o2); intro H_inside_2;
      [ generalize
         (Qhomographic_sign_dL_9 a b c d (dL p) p
            H_Qhomographic_sg_denom_nonzero (refl_equal (dL p)) Hb Hd
            H_inside_1 H_inside_2); intro; apply False_rec;
         assert
          (H6 :
           (1%Z, (na, (nb, (nc, nd)), np)) = ((-1)%Z, (a, (b, (c, d)), dL p)));
         [ apply
            trans_eq
             with
               (Qhomographic_sign a b c d (dL p)
                  H_Qhomographic_sg_denom_nonzero);
            assumption || symmetry  in |- *; assumption
         | elim (sg_tuple_equal 1 na nb nc nd np (-1) a b c d (dL p) H6);
            intros H7 H8; discriminate H7 ]
      | generalize
         (Qhomographic_sign_dL_10 a b c d (dL p) p
            (Qhomographic_signok_3 c d p H_Qhomographic_sg_denom_nonzero)
            H_Qhomographic_sg_denom_nonzero Hb Hd H_inside_1 H_inside_2);
         intro;
         apply
          (sg_pos_1 (a + b)%Z b (c + d)%Z d p
             (Qhomographic_signok_3 c d p H_Qhomographic_sg_denom_nonzero) na
             nb nc nd np);
         apply
          trans_eq
           with
             (Qhomographic_sign a b c d (dL p)
                H_Qhomographic_sg_denom_nonzero);
         assumption || symmetry  in |- *; assumption ] ].

 (* p = One *)
 case (Z_zerop (Z.sgn (a + b))); intro Hab.  
  apply False_rec;
   generalize
    (sg_One_2 a b c d One H_Qhomographic_sg_denom_nonzero 
       (refl_equal One) Hab); intro;
   assert
    (H2 : (1%Z, (na, (nb, (nc, nd)), np)) = (0%Z, (a, (b, (c, d)), One)));
   [ apply
      trans_eq
       with (Qhomographic_sign a b c d One H_Qhomographic_sg_denom_nonzero);
      assumption || symmetry  in |- *; assumption
   | elim (sg_tuple_equal 1 na nb nc nd np 0 a b c d One H2); intros H3 H4;
      discriminate H3 ].
 
  case (Z.eq_dec (Z.sgn (a + b)) (Z.sgn (c + d))); intro Habcd.  
   generalize
    (sg_One_3 a b c d One H_Qhomographic_sg_denom_nonzero 
       (refl_equal One) Hab Habcd); intro;
    assert
     (H2 : (1%Z, (na, (nb, (nc, nd)), np)) = (1%Z, (a, (b, (c, d)), One)));
    [ apply
       trans_eq
        with (Qhomographic_sign a b c d One H_Qhomographic_sg_denom_nonzero);
       assumption || symmetry  in |- *; assumption
    | elim (sg_tuple_equal 1 na nb nc nd np 1 a b c d One H2);
       intros _ ((H8, (H9, (H10, H11))), H12);
       repeat match goal with
              | id1:(?X1 = ?X2) |- ?X3 => rewrite id1
              end; case (not_Zeq_inf (Z.sgn (a + b)) 0 Hab); 
       intro Hab';
       [ right; split; apply Zsgn_11; [ idtac | rewrite Habcd in Hab' ]
       | left; split; apply Zsgn_12; [ idtac | rewrite Habcd in Hab' ] ];
       assumption ].

   generalize
    (sg_One_4 a b c d One H_Qhomographic_sg_denom_nonzero 
       (refl_equal One) Hab Habcd); intro; apply False_rec;
    assert
     (H2 : (1%Z, (na, (nb, (nc, nd)), np)) = ((-1)%Z, (a, (b, (c, d)), One)));
    [ apply
       trans_eq
        with (Qhomographic_sign a b c d One H_Qhomographic_sg_denom_nonzero);
       assumption || symmetry  in |- *; assumption
    | elim (sg_tuple_equal 1 na nb nc nd np (-1) a b c d One H2);
       intros H3 H4; discriminate H3 ].
Qed.

Lemma sg_pos_2 :
 forall (a b c d : Z) (p : Qpositive)
   (H_Qhomographic_sg_denom_nonzero : Qhomographic_sg_denom_nonzero c d p)
   (na nb nc nd : Z) (np : Qpositive),
 Qhomographic_sign a b c d p H_Qhomographic_sg_denom_nonzero =
 (1%Z, (na, (nb, (nc, nd)), np)) ->
 {(0 <= na)%Z /\ (0 <= nb)%Z /\ (0 <= nc)%Z /\ (0 <= nd)%Z} +
 {(na <= 0)%Z /\ (nb <= 0)%Z /\ (nc <= 0)%Z /\ (nd <= 0)%Z} + 
 {np = One}.
Proof.
 fix sg_pos_2 5.
 intros a b c d p H_Qhomographic_sg_denom_nonzero na nb nc nd np H_sg.
 set (o1 := outside_interval a b) in *.
 set (o2 := outside_interval c d) in *.
 destruct p as [p| p| ].
 (* p = (nR p) *) 
 case (Z_zerop b); intro Hb.
  case (Z_zerop d); intro Hd.
   generalize
    (Qhomographic_sign_nR_1 a b c d (nR p) p H_Qhomographic_sg_denom_nonzero
       (refl_equal (nR p)) Hb Hd); intro;
    assert
     (H6 :
      (1%Z, (na, (nb, (nc, nd)), np)) =
      ((Z.sgn a * Z.sgn c)%Z, (a, (b, (c, d)), nR p)));
    [ apply
       trans_eq
        with
          (Qhomographic_sign a b c d (nR p) H_Qhomographic_sg_denom_nonzero);
       assumption || symmetry  in |- *; assumption
    | elim
       (sg_tuple_equal 1 na nb nc nd np (Z.sgn a * Z.sgn c) a b c d (nR p) H6);
       intros H_ac ((H8, (H9, (H10, H11))), H12);
       repeat match goal with
              | id1:(?X1 = ?X2) |- ?X3 => rewrite id1
              end; left; rewrite <- Zsgn_15 in H_ac;
       case (Zsgn_16 _ _ (sym_eq H_ac)); intros (Ha, Hc); 
       [ left | right ]; repeat split;
       apply Z.le_refl || (apply Zlt_le_weak; assumption) ].
  
   case (Z_lt_dec 0 o2); intros Ho2.
    generalize
     (Qhomographic_sign_nR_2 a b c d (nR p) p H_Qhomographic_sg_denom_nonzero
        (refl_equal (nR p)) Hb Hd Ho2); intro;
     assert
      (H6 :
       (1%Z, (na, (nb, (nc, nd)), np)) = (Z.sgn a, (a, (b, (c, d)), nR p)));
     [ apply
        trans_eq
         with
           (Qhomographic_sign a b c d (nR p) H_Qhomographic_sg_denom_nonzero);
        assumption || symmetry  in |- *; assumption
     | elim (sg_tuple_equal 1 na nb nc nd np (Z.sgn a) a b c d (nR p) H6);
        intros H_a ((H8, (H9, (H10, H11))), H12);
        repeat match goal with
               | id1:(?X1 = ?X2) |- ?X3 => rewrite id1
               end; left; left; repeat split; first
        [ apply Z.le_refl
        | match goal with
          |  |- (0 <= ?X1)%Z => apply Zlt_le_weak; apply Zsgn_9
          |  |- (?X1 <= 0)%Z =>
              apply Zlt_le_weak; apply Zsgn_10; apply Z.opp_inj
          end; apply sym_eq; assumption
        | unfold o2 in Ho2;
           match goal with
           | id1:(0 < outside_interval ?X1 ?X2)%Z |- 
           (0 <= ?X1)%Z =>
               apply Zsgn_21 with X2
           | id1:(0 < outside_interval ?X1 ?X2)%Z |- 
           (0 <= ?X2)%Z =>
               apply Zsgn_23 with X1
           | id1:(outside_interval ?X1 ?X2 < 0)%Z |- 
           (?X1 <= 0)%Z =>
               apply Zsgn_22 with X2
           | id1:(outside_interval ?X1 ?X2 < 0)%Z |- 
           (?X2 <= 0)%Z => apply Zsgn_24 with X1
           end; assumption ] ].
    
    case (Z_lt_dec o2 0); intros Ho2'.
     generalize
      (Qhomographic_sign_nR_3 a b c d (nR p) p
         H_Qhomographic_sg_denom_nonzero (refl_equal (nR p)) Hb Hd Ho2 Ho2');
      intro;
      assert
       (H6 :
        (1%Z, (na, (nb, (nc, nd)), np)) =
        ((- Z.sgn a)%Z, (a, (b, (c, d)), nR p)));
      [ apply
         trans_eq
          with
            (Qhomographic_sign a b c d (nR p) H_Qhomographic_sg_denom_nonzero);
         assumption || symmetry  in |- *; assumption
      | elim (sg_tuple_equal 1 na nb nc nd np (- Z.sgn a) a b c d (nR p) H6);
         intros H_a ((H8, (H9, (H10, H11))), H12);
         repeat match goal with
                | id1:(?X1 = ?X2) |- ?X3 => rewrite id1
                end; left; right; repeat split; first
         [ apply Z.le_refl
         | match goal with
           |  |- (0 <= ?X1)%Z => apply Zlt_le_weak; apply Zsgn_9
           |  |- (?X1 <= 0)%Z =>
               apply Zlt_le_weak; apply Zsgn_10; apply Z.opp_inj
           end; apply sym_eq; assumption
         | unfold o2 in Ho2, Ho2';
            match goal with
            | id1:(0 < outside_interval ?X1 ?X2)%Z |- 
            (0 <= ?X1)%Z =>
                apply Zsgn_21 with X2
            | id1:(0 < outside_interval ?X1 ?X2)%Z |- 
            (0 <= ?X2)%Z =>
                apply Zsgn_23 with X1
            | id1:(outside_interval ?X1 ?X2 < 0)%Z |- 
            (?X1 <= 0)%Z =>
                apply Zsgn_22 with X2
            | id1:(outside_interval ?X1 ?X2 < 0)%Z |- 
            (?X2 <= 0)%Z => apply Zsgn_24 with X1
            end; assumption ] ].
 
     generalize
      (Qhomographic_sign_nR_4 a b c d (nR p) p
         (Qhomographic_signok_2 c d p H_Qhomographic_sg_denom_nonzero)
         H_Qhomographic_sg_denom_nonzero Hb Hd Ho2 Ho2'); 
      intro;
      apply
       (sg_pos_2 a (a + b)%Z c (c + d)%Z p
          (Qhomographic_signok_2 c d p H_Qhomographic_sg_denom_nonzero) na nb
          nc nd np);
      apply
       trans_eq
        with
          (Qhomographic_sign a b c d (nR p) H_Qhomographic_sg_denom_nonzero);
      assumption || symmetry  in |- *; assumption.

  case (Z_zerop d); intro Hd. 
   case (Z_lt_dec 0 o1); intro Ho1. 
    generalize
     (Qhomographic_sign_nR_5 a b c d (nR p) p H_Qhomographic_sg_denom_nonzero
        (refl_equal (nR p)) Hb Hd Ho1); intro;
     assert
      (H6 :
       (1%Z, (na, (nb, (nc, nd)), np)) = (Z.sgn c, (a, (b, (c, d)), nR p)));
     [ apply
        trans_eq
         with
           (Qhomographic_sign a b c d (nR p) H_Qhomographic_sg_denom_nonzero);
        assumption || symmetry  in |- *; assumption
     | elim (sg_tuple_equal 1 na nb nc nd np (Z.sgn c) a b c d (nR p) H6);
        intros H_a ((H8, (H9, (H10, H11))), H12);
        repeat match goal with
               | id1:(?X1 = ?X2) |- ?X3 => rewrite id1
               end; left; left; repeat split; first
        [ apply Z.le_refl
        | match goal with
          |  |- (0 <= ?X1)%Z => apply Zlt_le_weak; apply Zsgn_9
          |  |- (?X1 <= 0)%Z =>
              apply Zlt_le_weak; apply Zsgn_10; apply Z.opp_inj
          end; apply sym_eq; assumption
        | unfold o1 in Ho1;
           match goal with
           | id1:(0 < outside_interval ?X1 ?X2)%Z |- 
           (0 <= ?X1)%Z =>
               apply Zsgn_21 with X2
           | id1:(0 < outside_interval ?X1 ?X2)%Z |- 
           (0 <= ?X2)%Z =>
               apply Zsgn_23 with X1
           | id1:(outside_interval ?X1 ?X2 < 0)%Z |- 
           (?X1 <= 0)%Z =>
               apply Zsgn_22 with X2
           | id1:(outside_interval ?X1 ?X2 < 0)%Z |- 
           (?X2 <= 0)%Z => apply Zsgn_24 with X1
           end; assumption ] ].
    
    case (Z_lt_dec o1 0); intros Ho1'.
     generalize
      (Qhomographic_sign_nR_6 a b c d (nR p) p
         H_Qhomographic_sg_denom_nonzero (refl_equal (nR p)) Hb Hd Ho1 Ho1');
      intro;
      assert
       (H6 :
        (1%Z, (na, (nb, (nc, nd)), np)) =
        ((- Z.sgn c)%Z, (a, (b, (c, d)), nR p)));
      [ apply
         trans_eq
          with
            (Qhomographic_sign a b c d (nR p) H_Qhomographic_sg_denom_nonzero);
         assumption || symmetry  in |- *; assumption
      | elim (sg_tuple_equal 1 na nb nc nd np (- Z.sgn c) a b c d (nR p) H6);
         intros H_a ((H8, (H9, (H10, H11))), H12);
         repeat match goal with
                | id1:(?X1 = ?X2) |- ?X3 => rewrite id1
                end; left; right; repeat split; first
         [ apply Z.le_refl
         | match goal with
           |  |- (0 <= ?X1)%Z => apply Zlt_le_weak; apply Zsgn_9
           |  |- (?X1 <= 0)%Z =>
               apply Zlt_le_weak; apply Zsgn_10; apply Z.opp_inj
           end; apply sym_eq; assumption
         | unfold o1 in Ho1, Ho1';
            match goal with
            | id1:(0 < outside_interval ?X1 ?X2)%Z |- 
            (0 <= ?X1)%Z =>
                apply Zsgn_21 with X2
            | id1:(0 < outside_interval ?X1 ?X2)%Z |- 
            (0 <= ?X2)%Z =>
                apply Zsgn_23 with X1
            | id1:(outside_interval ?X1 ?X2 < 0)%Z |- 
            (?X1 <= 0)%Z =>
                apply Zsgn_22 with X2
            | id1:(outside_interval ?X1 ?X2 < 0)%Z |- 
            (?X2 <= 0)%Z => apply Zsgn_24 with X1
            end; assumption ] ].
 
     generalize
      (Qhomographic_sign_nR_7 a b c d (nR p) p
         (Qhomographic_signok_2 c d p H_Qhomographic_sg_denom_nonzero)
         H_Qhomographic_sg_denom_nonzero Hb Hd Ho1 Ho1'); 
      intro;
      apply
       (sg_pos_2 a (a + b)%Z c (c + d)%Z p
          (Qhomographic_signok_2 c d p H_Qhomographic_sg_denom_nonzero) na nb
          nc nd np);
      apply
       trans_eq
        with
          (Qhomographic_sign a b c d (nR p) H_Qhomographic_sg_denom_nonzero);
      assumption || symmetry  in |- *; assumption.

  case (inside_interval_1_dec_inf o1 o2); intro H_inside_1.
    generalize
     (Qhomographic_sign_nR_8 a b c d (nR p) p H_Qhomographic_sg_denom_nonzero
        (refl_equal (nR p)) Hb Hd H_inside_1); intro;
     assert
      (H6 : (1%Z, (na, (nb, (nc, nd)), np)) = (1%Z, (a, (b, (c, d)), nR p)));
     [ apply
        trans_eq
         with
           (Qhomographic_sign a b c d (nR p) H_Qhomographic_sg_denom_nonzero);
        assumption || symmetry  in |- *; assumption
     | elim (sg_tuple_equal 1 na nb nc nd np 1 a b c d (nR p) H6);
        intros _ ((H8, (H9, (H10, H11))), H12);
        repeat match goal with
               | id1:(?X1 = ?X2) |- ?X3 => rewrite id1
               end; left; case (inside_interval_1_inf _ _ H_inside_1);
        intros (Ho1, Ho2); [ left | right ]; repeat split; 
        unfold o1 in Ho1; unfold o2 in Ho2;
        match goal with
        | id1:(0 < outside_interval ?X1 ?X2)%Z |- (0 <= ?X1)%Z =>
            apply Zsgn_21 with X2
        | id1:(0 < outside_interval ?X1 ?X2)%Z |- (0 <= ?X2)%Z =>
            apply Zsgn_23 with X1
        | id1:(outside_interval ?X1 ?X2 < 0)%Z |- (?X1 <= 0)%Z =>
            apply Zsgn_22 with X2
        | id1:(outside_interval ?X1 ?X2 < 0)%Z |- (?X2 <= 0)%Z =>
            apply Zsgn_24 with X1
        end; assumption ].

    case (inside_interval_2_dec_inf o1 o2); intro H_inside_2;
     [ generalize
        (Qhomographic_sign_nR_9 a b c d (nR p) p
           H_Qhomographic_sg_denom_nonzero (refl_equal (nR p)) Hb Hd
           H_inside_1 H_inside_2); intro; apply False_rec;
        assert
         (H6 :
          (1%Z, (na, (nb, (nc, nd)), np)) = ((-1)%Z, (a, (b, (c, d)), nR p)));
        [ apply
           trans_eq
            with
              (Qhomographic_sign a b c d (nR p)
                 H_Qhomographic_sg_denom_nonzero);
           assumption || symmetry  in |- *; assumption
        | elim (sg_tuple_equal 1 na nb nc nd np (-1) a b c d (nR p) H6);
           intros H7 H8; discriminate H7 ]
     | generalize
        (Qhomographic_sign_nR_10 a b c d (nR p) p
           (Qhomographic_signok_2 c d p H_Qhomographic_sg_denom_nonzero)
           H_Qhomographic_sg_denom_nonzero Hb Hd H_inside_1 H_inside_2);
        intro;
        apply
         (sg_pos_2 a (a + b)%Z c (c + d)%Z p
            (Qhomographic_signok_2 c d p H_Qhomographic_sg_denom_nonzero) na
            nb nc nd np);
        apply
         trans_eq
          with
            (Qhomographic_sign a b c d (nR p) H_Qhomographic_sg_denom_nonzero);
        assumption || symmetry  in |- *; assumption ].

 (* p = (dL p) *)
 case (Z_zerop b); intro Hb.
  case (Z_zerop d); intro Hd.
   generalize
    (Qhomographic_sign_dL_1 a b c d (dL p) p H_Qhomographic_sg_denom_nonzero
       (refl_equal (dL p)) Hb Hd); intro;
    assert
     (H6 :
      (1%Z, (na, (nb, (nc, nd)), np)) =
      ((Z.sgn a * Z.sgn c)%Z, (a, (b, (c, d)), dL p)));
    [ apply
       trans_eq
        with
          (Qhomographic_sign a b c d (dL p) H_Qhomographic_sg_denom_nonzero);
       assumption || symmetry  in |- *; assumption
    | elim
       (sg_tuple_equal 1 na nb nc nd np (Z.sgn a * Z.sgn c) a b c d (dL p) H6);
       intros H_ac ((H8, (H9, (H10, H11))), H12);
       repeat match goal with
              | id1:(?X1 = ?X2) |- ?X3 => rewrite id1
              end; left; rewrite <- Zsgn_15 in H_ac;
       case (Zsgn_16 _ _ (sym_eq H_ac)); intros (Ha, Hc); 
       [ left | right ]; repeat split;
       apply Z.le_refl || (apply Zlt_le_weak; assumption) ].
  
   case (Z_lt_dec 0 o2); intros Ho2.
    generalize
     (Qhomographic_sign_dL_2 a b c d (dL p) p H_Qhomographic_sg_denom_nonzero
        (refl_equal (dL p)) Hb Hd Ho2); intro;
     assert
      (H6 :
       (1%Z, (na, (nb, (nc, nd)), np)) = (Z.sgn a, (a, (b, (c, d)), dL p)));
     [ apply
        trans_eq
         with
           (Qhomographic_sign a b c d (dL p) H_Qhomographic_sg_denom_nonzero);
        assumption || symmetry  in |- *; assumption
     | elim (sg_tuple_equal 1 na nb nc nd np (Z.sgn a) a b c d (dL p) H6);
        intros H_a ((H8, (H9, (H10, H11))), H12);
        repeat match goal with
               | id1:(?X1 = ?X2) |- ?X3 => rewrite id1
               end; left; left; repeat split; first
        [ apply Z.le_refl
        | match goal with
          |  |- (0 <= ?X1)%Z => apply Zlt_le_weak; apply Zsgn_9
          |  |- (?X1 <= 0)%Z =>
              apply Zlt_le_weak; apply Zsgn_10; apply Z.opp_inj
          end; apply sym_eq; assumption
        | unfold o2 in Ho2;
           match goal with
           | id1:(0 < outside_interval ?X1 ?X2)%Z |- 
           (0 <= ?X1)%Z =>
               apply Zsgn_21 with X2
           | id1:(0 < outside_interval ?X1 ?X2)%Z |- 
           (0 <= ?X2)%Z =>
               apply Zsgn_23 with X1
           | id1:(outside_interval ?X1 ?X2 < 0)%Z |- 
           (?X1 <= 0)%Z =>
               apply Zsgn_22 with X2
           | id1:(outside_interval ?X1 ?X2 < 0)%Z |- 
           (?X2 <= 0)%Z => apply Zsgn_24 with X1
           end; assumption ] ].
    
    case (Z_lt_dec o2 0); intros Ho2'.
     generalize
      (Qhomographic_sign_dL_3 a b c d (dL p) p
         H_Qhomographic_sg_denom_nonzero (refl_equal (dL p)) Hb Hd Ho2 Ho2');
      intro;
      assert
       (H6 :
        (1%Z, (na, (nb, (nc, nd)), np)) =
        ((- Z.sgn a)%Z, (a, (b, (c, d)), dL p)));
      [ apply
         trans_eq
          with
            (Qhomographic_sign a b c d (dL p) H_Qhomographic_sg_denom_nonzero);
         assumption || symmetry  in |- *; assumption
      | elim (sg_tuple_equal 1 na nb nc nd np (- Z.sgn a) a b c d (dL p) H6);
         intros H_a ((H8, (H9, (H10, H11))), H12);
         repeat match goal with
                | id1:(?X1 = ?X2) |- ?X3 => rewrite id1
                end; left; right; repeat split; first
         [ apply Z.le_refl
         | match goal with
           |  |- (0 <= ?X1)%Z => apply Zlt_le_weak; apply Zsgn_9
           |  |- (?X1 <= 0)%Z =>
               apply Zlt_le_weak; apply Zsgn_10; apply Z.opp_inj
           end; apply sym_eq; assumption
         | unfold o2 in Ho2, Ho2';
            match goal with
            | id1:(0 < outside_interval ?X1 ?X2)%Z |- 
            (0 <= ?X1)%Z =>
                apply Zsgn_21 with X2
            | id1:(0 < outside_interval ?X1 ?X2)%Z |- 
            (0 <= ?X2)%Z =>
                apply Zsgn_23 with X1
            | id1:(outside_interval ?X1 ?X2 < 0)%Z |- 
            (?X1 <= 0)%Z =>
                apply Zsgn_22 with X2
            | id1:(outside_interval ?X1 ?X2 < 0)%Z |- 
            (?X2 <= 0)%Z => apply Zsgn_24 with X1
            end; assumption ] ].
 
     generalize
      (Qhomographic_sign_dL_4 a b c d (dL p) p
         (Qhomographic_signok_3 c d p H_Qhomographic_sg_denom_nonzero)
         H_Qhomographic_sg_denom_nonzero Hb Hd Ho2 Ho2'); 
      intro;
      apply
       (sg_pos_2 (a + b)%Z b (c + d)%Z d p
          (Qhomographic_signok_3 c d p H_Qhomographic_sg_denom_nonzero) na nb
          nc nd np);
      apply
       trans_eq
        with
          (Qhomographic_sign a b c d (dL p) H_Qhomographic_sg_denom_nonzero);
      assumption || symmetry  in |- *; assumption.

  case (Z_zerop d); intro Hd. 
   case (Z_lt_dec 0 o1); intro Ho1. 
    generalize
     (Qhomographic_sign_dL_5 a b c d (dL p) p H_Qhomographic_sg_denom_nonzero
        (refl_equal (dL p)) Hb Hd Ho1); intro;
     assert
      (H6 :
       (1%Z, (na, (nb, (nc, nd)), np)) = (Z.sgn c, (a, (b, (c, d)), dL p)));
     [ apply
        trans_eq
         with
           (Qhomographic_sign a b c d (dL p) H_Qhomographic_sg_denom_nonzero);
        assumption || symmetry  in |- *; assumption
     | elim (sg_tuple_equal 1 na nb nc nd np (Z.sgn c) a b c d (dL p) H6);
        intros H_a ((H8, (H9, (H10, H11))), H12);
        repeat match goal with
               | id1:(?X1 = ?X2) |- ?X3 => rewrite id1
               end; left; left; repeat split; first
        [ apply Z.le_refl
        | match goal with
          |  |- (0 <= ?X1)%Z => apply Zlt_le_weak; apply Zsgn_9
          |  |- (?X1 <= 0)%Z =>
              apply Zlt_le_weak; apply Zsgn_10; apply Z.opp_inj
          end; apply sym_eq; assumption
        | unfold o1 in Ho1;
           match goal with
           | id1:(0 < outside_interval ?X1 ?X2)%Z |- 
           (0 <= ?X1)%Z =>
               apply Zsgn_21 with X2
           | id1:(0 < outside_interval ?X1 ?X2)%Z |- 
           (0 <= ?X2)%Z =>
               apply Zsgn_23 with X1
           | id1:(outside_interval ?X1 ?X2 < 0)%Z |- 
           (?X1 <= 0)%Z =>
               apply Zsgn_22 with X2
           | id1:(outside_interval ?X1 ?X2 < 0)%Z |- 
           (?X2 <= 0)%Z => apply Zsgn_24 with X1
           end; assumption ] ].
    
    case (Z_lt_dec o1 0); intros Ho1'.
     generalize
      (Qhomographic_sign_dL_6 a b c d (dL p) p
         H_Qhomographic_sg_denom_nonzero (refl_equal (dL p)) Hb Hd Ho1 Ho1');
      intro;
      assert
       (H6 :
        (1%Z, (na, (nb, (nc, nd)), np)) =
        ((- Z.sgn c)%Z, (a, (b, (c, d)), dL p)));
      [ apply
         trans_eq
          with
            (Qhomographic_sign a b c d (dL p) H_Qhomographic_sg_denom_nonzero);
         assumption || symmetry  in |- *; assumption
      | elim (sg_tuple_equal 1 na nb nc nd np (- Z.sgn c) a b c d (dL p) H6);
         intros H_a ((H8, (H9, (H10, H11))), H12);
         repeat match goal with
                | id1:(?X1 = ?X2) |- ?X3 => rewrite id1
                end; left; right; repeat split; first
         [ apply Z.le_refl
         | match goal with
           |  |- (0 <= ?X1)%Z => apply Zlt_le_weak; apply Zsgn_9
           |  |- (?X1 <= 0)%Z =>
               apply Zlt_le_weak; apply Zsgn_10; apply Z.opp_inj
           end; apply sym_eq; assumption
         | unfold o1 in Ho1, Ho1';
            match goal with
            | id1:(0 < outside_interval ?X1 ?X2)%Z |- 
            (0 <= ?X1)%Z =>
                apply Zsgn_21 with X2
            | id1:(0 < outside_interval ?X1 ?X2)%Z |- 
            (0 <= ?X2)%Z =>
                apply Zsgn_23 with X1
            | id1:(outside_interval ?X1 ?X2 < 0)%Z |- 
            (?X1 <= 0)%Z =>
                apply Zsgn_22 with X2
            | id1:(outside_interval ?X1 ?X2 < 0)%Z |- 
            (?X2 <= 0)%Z => apply Zsgn_24 with X1
            end; assumption ] ].
 
     generalize
      (Qhomographic_sign_dL_7 a b c d (dL p) p
         (Qhomographic_signok_3 c d p H_Qhomographic_sg_denom_nonzero)
         H_Qhomographic_sg_denom_nonzero Hb Hd Ho1 Ho1'); 
      intro;
      apply
       (sg_pos_2 (a + b)%Z b (c + d)%Z d p
          (Qhomographic_signok_3 c d p H_Qhomographic_sg_denom_nonzero) na nb
          nc nd np);
      apply
       trans_eq
        with
          (Qhomographic_sign a b c d (dL p) H_Qhomographic_sg_denom_nonzero);
      assumption || symmetry  in |- *; assumption.

  case (inside_interval_1_dec_inf o1 o2); intro H_inside_1.
    generalize
     (Qhomographic_sign_dL_8 a b c d (dL p) p H_Qhomographic_sg_denom_nonzero
        (refl_equal (dL p)) Hb Hd H_inside_1); intro;
     assert
      (H6 : (1%Z, (na, (nb, (nc, nd)), np)) = (1%Z, (a, (b, (c, d)), dL p)));
     [ apply
        trans_eq
         with
           (Qhomographic_sign a b c d (dL p) H_Qhomographic_sg_denom_nonzero);
        assumption || symmetry  in |- *; assumption
     | elim (sg_tuple_equal 1 na nb nc nd np 1 a b c d (dL p) H6);
        intros _ ((H8, (H9, (H10, H11))), H12);
        repeat match goal with
               | id1:(?X1 = ?X2) |- ?X3 => rewrite id1
               end; left; case (inside_interval_1_inf _ _ H_inside_1);
        intros (Ho1, Ho2); [ left | right ]; repeat split; 
        unfold o1 in Ho1; unfold o2 in Ho2;
        match goal with
        | id1:(0 < outside_interval ?X1 ?X2)%Z |- (0 <= ?X1)%Z =>
            apply Zsgn_21 with X2
        | id1:(0 < outside_interval ?X1 ?X2)%Z |- (0 <= ?X2)%Z =>
            apply Zsgn_23 with X1
        | id1:(outside_interval ?X1 ?X2 < 0)%Z |- (?X1 <= 0)%Z =>
            apply Zsgn_22 with X2
        | id1:(outside_interval ?X1 ?X2 < 0)%Z |- (?X2 <= 0)%Z =>
            apply Zsgn_24 with X1
        end; assumption ].

    case (inside_interval_2_dec_inf o1 o2); intro H_inside_2;
     [ generalize
        (Qhomographic_sign_dL_9 a b c d (dL p) p
           H_Qhomographic_sg_denom_nonzero (refl_equal (dL p)) Hb Hd
           H_inside_1 H_inside_2); intro; apply False_rec;
        assert
         (H6 :
          (1%Z, (na, (nb, (nc, nd)), np)) = ((-1)%Z, (a, (b, (c, d)), dL p)));
        [ apply
           trans_eq
            with
              (Qhomographic_sign a b c d (dL p)
                 H_Qhomographic_sg_denom_nonzero);
           assumption || symmetry  in |- *; assumption
        | elim (sg_tuple_equal 1 na nb nc nd np (-1) a b c d (dL p) H6);
           intros H7 H8; discriminate H7 ]
     | generalize
        (Qhomographic_sign_dL_10 a b c d (dL p) p
           (Qhomographic_signok_3 c d p H_Qhomographic_sg_denom_nonzero)
           H_Qhomographic_sg_denom_nonzero Hb Hd H_inside_1 H_inside_2);
        intro;
        apply
         (sg_pos_2 (a + b)%Z b (c + d)%Z d p
            (Qhomographic_signok_3 c d p H_Qhomographic_sg_denom_nonzero) na
            nb nc nd np);
        apply
         trans_eq
          with
            (Qhomographic_sign a b c d (dL p) H_Qhomographic_sg_denom_nonzero);
        assumption || symmetry  in |- *; assumption ].
 (* p = One *)
 case (Z_zerop (Z.sgn (a + b))); intro Hab.  
  apply False_rec;
   generalize
    (sg_One_2 a b c d One H_Qhomographic_sg_denom_nonzero 
       (refl_equal One) Hab); intro;
   assert
    (H2 : (1%Z, (na, (nb, (nc, nd)), np)) = (0%Z, (a, (b, (c, d)), One)));
   [ apply
      trans_eq
       with (Qhomographic_sign a b c d One H_Qhomographic_sg_denom_nonzero);
      assumption || symmetry  in |- *; assumption
   | elim (sg_tuple_equal 1 na nb nc nd np 0 a b c d One H2); intros H3 H4;
      discriminate H3 ].
 
  case (Z.eq_dec (Z.sgn (a + b)) (Z.sgn (c + d))); intro Habcd.  
   generalize
    (sg_One_3 a b c d One H_Qhomographic_sg_denom_nonzero 
       (refl_equal One) Hab Habcd); intro;
    assert
     (H2 : (1%Z, (na, (nb, (nc, nd)), np)) = (1%Z, (a, (b, (c, d)), One)));
    [ apply
       trans_eq
        with (Qhomographic_sign a b c d One H_Qhomographic_sg_denom_nonzero);
       assumption || symmetry  in |- *; assumption
    | elim (sg_tuple_equal 1 na nb nc nd np 1 a b c d One H2);
       intros _ ((H8, (H9, (H10, H11))), H12);
       repeat match goal with
              | id1:(?X1 = ?X2) |- ?X3 => rewrite id1
              end; right; reflexivity ].

   generalize
    (sg_One_4 a b c d One H_Qhomographic_sg_denom_nonzero 
       (refl_equal One) Hab Habcd); intro; apply False_rec;
    assert
     (H2 : (1%Z, (na, (nb, (nc, nd)), np)) = ((-1)%Z, (a, (b, (c, d)), One)));
    [ apply
       trans_eq
        with (Qhomographic_sign a b c d One H_Qhomographic_sg_denom_nonzero);
       assumption || symmetry  in |- *; assumption
    | elim (sg_tuple_equal 1 na nb nc nd np (-1) a b c d One H2);
       intro H_discrim; discriminate H_discrim ].
Qed.


Lemma sg_neg_1 :
 forall (a b c d : Z) (p : Qpositive)
   (H_Qhomographic_sg_denom_nonzero : Qhomographic_sg_denom_nonzero c d p)
   (na nb nc nd : Z) (np : Qpositive),
 Qhomographic_sign a b c d p H_Qhomographic_sg_denom_nonzero =
 ((-1)%Z, (na, (nb, (nc, nd)), np)) ->
 {(0 < na + nb)%Z /\ (nc + nd < 0)%Z} + {(na + nb < 0)%Z /\ (0 < nc + nd)%Z}.
Proof.
 fix sg_neg_1 5.
 intros a b c d p H_Qhomographic_sg_denom_nonzero na nb nc nd np H_sg.
 set (o1 := outside_interval a b) in *.
 set (o2 := outside_interval c d) in *.
 destruct p as [p| p| ].
 (* p = (nR p) *) 
 case (Z_zerop b); intro Hb.
  case (Z_zerop d); intro Hd.
   generalize
    (Qhomographic_sign_nR_1 a b c d (nR p) p H_Qhomographic_sg_denom_nonzero
       (refl_equal (nR p)) Hb Hd); intro;
    assert
     (H6 :
      ((-1)%Z, (na, (nb, (nc, nd)), np)) =
      ((Z.sgn a * Z.sgn c)%Z, (a, (b, (c, d)), nR p)));
    [ apply
       trans_eq
        with
          (Qhomographic_sign a b c d (nR p) H_Qhomographic_sg_denom_nonzero);
       assumption || symmetry  in |- *; assumption
    | elim
       (sg_tuple_equal (-1) na nb nc nd np (Z.sgn a * Z.sgn c) a b c d 
          (nR p) H6); intros H_ac ((H8, (H9, (H10, H11))), H12);
       repeat match goal with
              | id1:(?X1 = ?X2) |- ?X3 => rewrite id1
              end; repeat rewrite Zplus_0_r; apply Zsgn_17; 
       rewrite Zsgn_15; symmetry  in |- *; assumption ].
  
   case (Z_lt_dec 0 o2); intros Ho2.
    generalize
     (Qhomographic_sign_nR_2 a b c d (nR p) p H_Qhomographic_sg_denom_nonzero
        (refl_equal (nR p)) Hb Hd Ho2); intro;
     assert
      (H6 :
       ((-1)%Z, (na, (nb, (nc, nd)), np)) = (Z.sgn a, (a, (b, (c, d)), nR p)));
     [ apply
        trans_eq
         with
           (Qhomographic_sign a b c d (nR p) H_Qhomographic_sg_denom_nonzero);
        assumption || symmetry  in |- *; assumption
     | elim (sg_tuple_equal (-1) na nb nc nd np (Z.sgn a) a b c d (nR p) H6);
        intros H_a ((H8, (H9, (H10, H11))), H12);
        repeat match goal with
               | id1:(?X1 = ?X2) |- ?X3 => rewrite id1
               end; repeat rewrite Zplus_0_r; right; 
        split; [ apply Zsgn_10; symmetry  in |- * | apply Zsgn_19 ];
        assumption ].
    
    case (Z_lt_dec o2 0); intros Ho2'.
     generalize
      (Qhomographic_sign_nR_3 a b c d (nR p) p
         H_Qhomographic_sg_denom_nonzero (refl_equal (nR p)) Hb Hd Ho2 Ho2');
      intro;
      assert
       (H6 :
        ((-1)%Z, (na, (nb, (nc, nd)), np)) =
        ((- Z.sgn a)%Z, (a, (b, (c, d)), nR p)));
      [ apply
         trans_eq
          with
            (Qhomographic_sign a b c d (nR p) H_Qhomographic_sg_denom_nonzero);
         assumption || symmetry  in |- *; assumption
      | elim
         (sg_tuple_equal (-1) na nb nc nd np (- Z.sgn a) a b c d (nR p) H6);
         intros H_a ((H8, (H9, (H10, H11))), H12);
         repeat match goal with
                | id1:(?X1 = ?X2) |- ?X3 => rewrite id1
                end; repeat rewrite Zplus_0_r; left; 
         split;
         [ apply Zsgn_9; symmetry  in |- *; apply Z.opp_inj | apply Zsgn_20 ];
         assumption ].
 
     generalize
      (Qhomographic_sign_nR_4 a b c d (nR p) p
         (Qhomographic_signok_2 c d p H_Qhomographic_sg_denom_nonzero)
         H_Qhomographic_sg_denom_nonzero Hb Hd Ho2 Ho2'); 
      intro;
      apply
       (sg_neg_1 a (a + b)%Z c (c + d)%Z p
          (Qhomographic_signok_2 c d p H_Qhomographic_sg_denom_nonzero) na nb
          nc nd np);
      apply
       trans_eq
        with
          (Qhomographic_sign a b c d (nR p) H_Qhomographic_sg_denom_nonzero);
      assumption || symmetry  in |- *; assumption.


  case (Z_zerop d); intro Hd. 
   case (Z_lt_dec 0 o1); intro Ho1. 
    generalize
     (Qhomographic_sign_nR_5 a b c d (nR p) p H_Qhomographic_sg_denom_nonzero
        (refl_equal (nR p)) Hb Hd Ho1); intro;
     assert
      (H6 :
       ((-1)%Z, (na, (nb, (nc, nd)), np)) = (Z.sgn c, (a, (b, (c, d)), nR p)));
     [ apply
        trans_eq
         with
           (Qhomographic_sign a b c d (nR p) H_Qhomographic_sg_denom_nonzero);
        assumption || symmetry  in |- *; assumption
     | elim (sg_tuple_equal (-1) na nb nc nd np (Z.sgn c) a b c d (nR p) H6);
        intros H_a ((H8, (H9, (H10, H11))), H12);
        repeat match goal with
               | id1:(?X1 = ?X2) |- ?X3 => rewrite id1
               end; repeat rewrite Zplus_0_r; left; 
        split; [ apply Zsgn_19 | apply Zsgn_10; symmetry  in |- * ];
        assumption ].
    
    case (Z_lt_dec o1 0); intros Ho1'.
     generalize
      (Qhomographic_sign_nR_6 a b c d (nR p) p
         H_Qhomographic_sg_denom_nonzero (refl_equal (nR p)) Hb Hd Ho1 Ho1');
      intro;
      assert
       (H6 :
        ((-1)%Z, (na, (nb, (nc, nd)), np)) =
        ((- Z.sgn c)%Z, (a, (b, (c, d)), nR p)));
      [ apply
         trans_eq
          with
            (Qhomographic_sign a b c d (nR p) H_Qhomographic_sg_denom_nonzero);
         assumption || symmetry  in |- *; assumption
      | elim
         (sg_tuple_equal (-1) na nb nc nd np (- Z.sgn c) a b c d (nR p) H6);
         intros H_a ((H8, (H9, (H10, H11))), H12);
         repeat match goal with
                | id1:(?X1 = ?X2) |- ?X3 => rewrite id1
                end; repeat rewrite Zplus_0_r; right; 
         split;
         [ apply Zsgn_20 | apply Zsgn_9; symmetry  in |- *; apply Z.opp_inj ];
         assumption ].
 
     generalize
      (Qhomographic_sign_nR_7 a b c d (nR p) p
         (Qhomographic_signok_2 c d p H_Qhomographic_sg_denom_nonzero)
         H_Qhomographic_sg_denom_nonzero Hb Hd Ho1 Ho1'); 
      intro;
      apply
       (sg_neg_1 a (a + b)%Z c (c + d)%Z p
          (Qhomographic_signok_2 c d p H_Qhomographic_sg_denom_nonzero) na nb
          nc nd np);
      apply
       trans_eq
        with
          (Qhomographic_sign a b c d (nR p) H_Qhomographic_sg_denom_nonzero);
      assumption || symmetry  in |- *; assumption.

  case (inside_interval_1_dec_inf o1 o2); intro H_inside_1.
    generalize
     (Qhomographic_sign_nR_8 a b c d (nR p) p H_Qhomographic_sg_denom_nonzero
        (refl_equal (nR p)) Hb Hd H_inside_1); intro;
     assert
      (H6 :
       ((-1)%Z, (na, (nb, (nc, nd)), np)) = (1%Z, (a, (b, (c, d)), nR p)));
     [ apply
        trans_eq
         with
           (Qhomographic_sign a b c d (nR p) H_Qhomographic_sg_denom_nonzero);
        assumption || symmetry  in |- *; assumption
     | elim (sg_tuple_equal (-1) na nb nc nd np 1 a b c d (nR p) H6);
        intros hl H_rest; discriminate hl ].

    case (inside_interval_2_dec_inf o1 o2); intro H_inside_2.
      generalize
       (Qhomographic_sign_nR_9 a b c d (nR p) p
          H_Qhomographic_sg_denom_nonzero (refl_equal (nR p)) Hb Hd
          H_inside_1 H_inside_2); intro;
       assert
        (H6 :
         ((-1)%Z, (na, (nb, (nc, nd)), np)) =
         ((-1)%Z, (a, (b, (c, d)), nR p)));
       [ apply
          trans_eq
           with
             (Qhomographic_sign a b c d (nR p)
                H_Qhomographic_sg_denom_nonzero);
          assumption || symmetry  in |- *; assumption
       | elim (sg_tuple_equal (-1) na nb nc nd np (-1) a b c d (nR p) H6);
          intros _ ((H8, (H9, (H10, H11))), H12);
          repeat match goal with
                 | id1:(?X1 = ?X2) |- ?X3 => rewrite id1
                 end; case (inside_interval_2_inf _ _ H_inside_2);
          intros (Ho1, Ho2);
          [ left; split; [ apply Zsgn_19 | apply Zsgn_20 ]
          | right; split; [ apply Zsgn_20 | apply Zsgn_19 ] ]; 
          assumption ].

      generalize
       (Qhomographic_sign_nR_10 a b c d (nR p) p
          (Qhomographic_signok_2 c d p H_Qhomographic_sg_denom_nonzero)
          H_Qhomographic_sg_denom_nonzero Hb Hd H_inside_1 H_inside_2); 
       intro;
       apply
        (sg_neg_1 a (a + b)%Z c (c + d)%Z p
           (Qhomographic_signok_2 c d p H_Qhomographic_sg_denom_nonzero) na
           nb nc nd np);
       apply
        trans_eq
         with
           (Qhomographic_sign a b c d (nR p) H_Qhomographic_sg_denom_nonzero);
       assumption || symmetry  in |- *; assumption.

 (* p = (dL p) *) 
 case (Z_zerop b); intro Hb.
  case (Z_zerop d); intro Hd.
   generalize
    (Qhomographic_sign_dL_1 a b c d (dL p) p H_Qhomographic_sg_denom_nonzero
       (refl_equal (dL p)) Hb Hd); intro;
    assert
     (H6 :
      ((-1)%Z, (na, (nb, (nc, nd)), np)) =
      ((Z.sgn a * Z.sgn c)%Z, (a, (b, (c, d)), dL p)));
    [ apply
       trans_eq
        with
          (Qhomographic_sign a b c d (dL p) H_Qhomographic_sg_denom_nonzero);
       assumption || symmetry  in |- *; assumption
    | elim
       (sg_tuple_equal (-1) na nb nc nd np (Z.sgn a * Z.sgn c) a b c d 
          (dL p) H6); intros H_ac ((H8, (H9, (H10, H11))), H12);
       repeat match goal with
              | id1:(?X1 = ?X2) |- ?X3 => rewrite id1
              end; repeat rewrite Zplus_0_r; apply Zsgn_17; 
       rewrite Zsgn_15; symmetry  in |- *; assumption ].
  
   case (Z_lt_dec 0 o2); intros Ho2.
    generalize
     (Qhomographic_sign_dL_2 a b c d (dL p) p H_Qhomographic_sg_denom_nonzero
        (refl_equal (dL p)) Hb Hd Ho2); intro;
     assert
      (H6 :
       ((-1)%Z, (na, (nb, (nc, nd)), np)) = (Z.sgn a, (a, (b, (c, d)), dL p)));
     [ apply
        trans_eq
         with
           (Qhomographic_sign a b c d (dL p) H_Qhomographic_sg_denom_nonzero);
        assumption || symmetry  in |- *; assumption
     | elim (sg_tuple_equal (-1) na nb nc nd np (Z.sgn a) a b c d (dL p) H6);
        intros H_a ((H8, (H9, (H10, H11))), H12);
        repeat match goal with
               | id1:(?X1 = ?X2) |- ?X3 => rewrite id1
               end; repeat rewrite Zplus_0_r; right; 
        split; [ apply Zsgn_10; symmetry  in |- * | apply Zsgn_19 ];
        assumption ].
    
    case (Z_lt_dec o2 0); intros Ho2'.
     generalize
      (Qhomographic_sign_dL_3 a b c d (dL p) p
         H_Qhomographic_sg_denom_nonzero (refl_equal (dL p)) Hb Hd Ho2 Ho2');
      intro;
      assert
       (H6 :
        ((-1)%Z, (na, (nb, (nc, nd)), np)) =
        ((- Z.sgn a)%Z, (a, (b, (c, d)), dL p)));
      [ apply
         trans_eq
          with
            (Qhomographic_sign a b c d (dL p) H_Qhomographic_sg_denom_nonzero);
         assumption || symmetry  in |- *; assumption
      | elim
         (sg_tuple_equal (-1) na nb nc nd np (- Z.sgn a) a b c d (dL p) H6);
         intros H_a ((H8, (H9, (H10, H11))), H12);
         repeat match goal with
                | id1:(?X1 = ?X2) |- ?X3 => rewrite id1
                end; repeat rewrite Zplus_0_r; left; 
         split;
         [ apply Zsgn_9; symmetry  in |- *; apply Z.opp_inj | apply Zsgn_20 ];
         assumption ].
 
     generalize
      (Qhomographic_sign_dL_4 a b c d (dL p) p
         (Qhomographic_signok_3 c d p H_Qhomographic_sg_denom_nonzero)
         H_Qhomographic_sg_denom_nonzero Hb Hd Ho2 Ho2'); 
      intro;
      apply
       (sg_neg_1 (a + b)%Z b (c + d)%Z d p
          (Qhomographic_signok_3 c d p H_Qhomographic_sg_denom_nonzero) na nb
          nc nd np);
      apply
       trans_eq
        with
          (Qhomographic_sign a b c d (dL p) H_Qhomographic_sg_denom_nonzero);
      assumption || symmetry  in |- *; assumption.


  case (Z_zerop d); intro Hd. 
   case (Z_lt_dec 0 o1); intro Ho1. 
    generalize
     (Qhomographic_sign_dL_5 a b c d (dL p) p H_Qhomographic_sg_denom_nonzero
        (refl_equal (dL p)) Hb Hd Ho1); intro;
     assert
      (H6 :
       ((-1)%Z, (na, (nb, (nc, nd)), np)) = (Z.sgn c, (a, (b, (c, d)), dL p)));
     [ apply
        trans_eq
         with
           (Qhomographic_sign a b c d (dL p) H_Qhomographic_sg_denom_nonzero);
        assumption || symmetry  in |- *; assumption
     | elim (sg_tuple_equal (-1) na nb nc nd np (Z.sgn c) a b c d (dL p) H6);
        intros H_a ((H8, (H9, (H10, H11))), H12);
        repeat match goal with
               | id1:(?X1 = ?X2) |- ?X3 => rewrite id1
               end; repeat rewrite Zplus_0_r; left; 
        split; [ apply Zsgn_19 | apply Zsgn_10; symmetry  in |- * ];
        assumption ].
    
    case (Z_lt_dec o1 0); intros Ho1'.
     generalize
      (Qhomographic_sign_dL_6 a b c d (dL p) p
         H_Qhomographic_sg_denom_nonzero (refl_equal (dL p)) Hb Hd Ho1 Ho1');
      intro;
      assert
       (H6 :
        ((-1)%Z, (na, (nb, (nc, nd)), np)) =
        ((- Z.sgn c)%Z, (a, (b, (c, d)), dL p)));
      [ apply
         trans_eq
          with
            (Qhomographic_sign a b c d (dL p) H_Qhomographic_sg_denom_nonzero);
         assumption || symmetry  in |- *; assumption
      | elim
         (sg_tuple_equal (-1) na nb nc nd np (- Z.sgn c) a b c d (dL p) H6);
         intros H_a ((H8, (H9, (H10, H11))), H12);
         repeat match goal with
                | id1:(?X1 = ?X2) |- ?X3 => rewrite id1
                end; repeat rewrite Zplus_0_r; right; 
         split;
         [ apply Zsgn_20 | apply Zsgn_9; symmetry  in |- *; apply Z.opp_inj ];
         assumption ].
 
     generalize
      (Qhomographic_sign_dL_7 a b c d (dL p) p
         (Qhomographic_signok_3 c d p H_Qhomographic_sg_denom_nonzero)
         H_Qhomographic_sg_denom_nonzero Hb Hd Ho1 Ho1'); 
      intro;
      apply
       (sg_neg_1 (a + b)%Z b (c + d)%Z d p
          (Qhomographic_signok_3 c d p H_Qhomographic_sg_denom_nonzero) na nb
          nc nd np);
      apply
       trans_eq
        with
          (Qhomographic_sign a b c d (dL p) H_Qhomographic_sg_denom_nonzero);
      assumption || symmetry  in |- *; assumption.

  case (inside_interval_1_dec_inf o1 o2); intro H_inside_1.
    generalize
     (Qhomographic_sign_dL_8 a b c d (dL p) p H_Qhomographic_sg_denom_nonzero
        (refl_equal (dL p)) Hb Hd H_inside_1); intro;
     assert
      (H6 :
       ((-1)%Z, (na, (nb, (nc, nd)), np)) = (1%Z, (a, (b, (c, d)), dL p)));
     [ apply
        trans_eq
         with
           (Qhomographic_sign a b c d (dL p) H_Qhomographic_sg_denom_nonzero);
        assumption || symmetry  in |- *; assumption
     | elim (sg_tuple_equal (-1) na nb nc nd np 1 a b c d (dL p) H6);
        intros hl H_rest; discriminate hl ].

    case (inside_interval_2_dec_inf o1 o2); intro H_inside_2.
      generalize
       (Qhomographic_sign_dL_9 a b c d (dL p) p
          H_Qhomographic_sg_denom_nonzero (refl_equal (dL p)) Hb Hd
          H_inside_1 H_inside_2); intro;
       assert
        (H6 :
         ((-1)%Z, (na, (nb, (nc, nd)), np)) =
         ((-1)%Z, (a, (b, (c, d)), dL p)));
       [ apply
          trans_eq
           with
             (Qhomographic_sign a b c d (dL p)
                H_Qhomographic_sg_denom_nonzero);
          assumption || symmetry  in |- *; assumption
       | elim (sg_tuple_equal (-1) na nb nc nd np (-1) a b c d (dL p) H6);
          intros _ ((H8, (H9, (H10, H11))), H12);
          repeat match goal with
                 | id1:(?X1 = ?X2) |- ?X3 => rewrite id1
                 end; case (inside_interval_2_inf _ _ H_inside_2);
          intros (Ho1, Ho2);
          [ left; split; [ apply Zsgn_19 | apply Zsgn_20 ]
          | right; split; [ apply Zsgn_20 | apply Zsgn_19 ] ]; 
          assumption ].

      generalize
       (Qhomographic_sign_dL_10 a b c d (dL p) p
          (Qhomographic_signok_3 c d p H_Qhomographic_sg_denom_nonzero)
          H_Qhomographic_sg_denom_nonzero Hb Hd H_inside_1 H_inside_2); 
       intro;
       apply
        (sg_neg_1 (a + b)%Z b (c + d)%Z d p
           (Qhomographic_signok_3 c d p H_Qhomographic_sg_denom_nonzero) na
           nb nc nd np);
       apply
        trans_eq
         with
           (Qhomographic_sign a b c d (dL p) H_Qhomographic_sg_denom_nonzero);
       assumption || symmetry  in |- *; assumption.

(* p = One *)
 case (Z_zerop (Z.sgn (a + b))); intro Hab.  
  apply False_rec;
   generalize
    (sg_One_2 a b c d One H_Qhomographic_sg_denom_nonzero 
       (refl_equal One) Hab); intro;
   assert
    (H2 : ((-1)%Z, (na, (nb, (nc, nd)), np)) = (0%Z, (a, (b, (c, d)), One)));
   [ apply
      trans_eq
       with (Qhomographic_sign a b c d One H_Qhomographic_sg_denom_nonzero);
      assumption || symmetry  in |- *; assumption
   | elim (sg_tuple_equal (-1) na nb nc nd np 0 a b c d One H2); intros H3 H4;
      discriminate H3 ].
 
  case (Z.eq_dec (Z.sgn (a + b)) (Z.sgn (c + d))); intro Habcd.  
   generalize
    (sg_One_3 a b c d One H_Qhomographic_sg_denom_nonzero 
       (refl_equal One) Hab Habcd); intro;
    assert
     (H2 : ((-1)%Z, (na, (nb, (nc, nd)), np)) = (1%Z, (a, (b, (c, d)), One)));
    [ apply
       trans_eq
        with (Qhomographic_sign a b c d One H_Qhomographic_sg_denom_nonzero);
       assumption || symmetry  in |- *; assumption
    | elim (sg_tuple_equal (-1) na nb nc nd np 1 a b c d One H2);
       intros H3 H4; discriminate H3 ].

   generalize
    (sg_One_4 a b c d One H_Qhomographic_sg_denom_nonzero 
       (refl_equal One) Hab Habcd); intro;
    assert
     (H2 :
      ((-1)%Z, (na, (nb, (nc, nd)), np)) = ((-1)%Z, (a, (b, (c, d)), One)));
    [ apply
       trans_eq
        with (Qhomographic_sign a b c d One H_Qhomographic_sg_denom_nonzero);
       assumption || symmetry  in |- *; assumption
    | elim (sg_tuple_equal (-1) na nb nc nd np (-1) a b c d One H2);
       intros _ ((H8, (H9, (H10, H11))), H12);
       repeat match goal with
              | id1:(?X1 = ?X2) |- ?X3 => rewrite id1
              end ].
   case (not_Zeq_inf (Z.sgn (a + b)) 0 Hab); intro Hab';
    [ right; split; [ apply Zsgn_11; assumption | apply Zsgn_12 ];
       generalize (Zsgn_1 (c + d)); intros [[Hcd| Hcd]| Hcd];
       [ apply False_ind;
          apply (Qhomographic_signok_1 c d H_Qhomographic_sg_denom_nonzero);
          apply Zsgn_2
       | rewrite Hcd; constructor
       | apply False_ind; apply Habcd; rewrite Hcd; apply Zsgn_8;
          apply Zsgn_11 ]; assumption
    | left; split; [ apply Zsgn_12; assumption | apply Zsgn_11 ];
       generalize (Zsgn_1 (c + d)); intros [[Hcd| Hcd]| Hcd];
       [ apply False_ind;
          apply (Qhomographic_signok_1 c d H_Qhomographic_sg_denom_nonzero);
          apply Zsgn_2
       | apply False_ind; apply Habcd; rewrite Hcd; apply Zsgn_7;
          apply Z.lt_gt; apply Zsgn_12
       | rewrite Hcd; constructor ]; assumption ].
Qed.


Lemma sg_neg_2 :
 forall (a b c d : Z) (p : Qpositive)
   (H_Qhomographic_sg_denom_nonzero : Qhomographic_sg_denom_nonzero c d p)
   (na nb nc nd : Z) (np : Qpositive),
 Qhomographic_sign a b c d p H_Qhomographic_sg_denom_nonzero =
 ((-1)%Z, (na, (nb, (nc, nd)), np)) ->
 {(0 <= na)%Z /\ (0 <= nb)%Z /\ (nc <= 0)%Z /\ (nd <= 0)%Z} +
 {(na <= 0)%Z /\ (nb <= 0)%Z /\ (0 <= nc)%Z /\ (0 <= nd)%Z} + 
 {np = One}.
Proof.
 fix sg_neg_2 5.
 intros a b c d p H_Qhomographic_sg_denom_nonzero na nb nc nd np H_sg.
 set (o1 := outside_interval a b) in *.
 set (o2 := outside_interval c d) in *.
 destruct p as [p| p| ].
 (* p = (nR p) *) 
 case (Z_zerop b); intro Hb.
  case (Z_zerop d); intro Hd.
   generalize
    (Qhomographic_sign_nR_1 a b c d (nR p) p H_Qhomographic_sg_denom_nonzero
       (refl_equal (nR p)) Hb Hd); intro;
    assert
     (H6 :
      ((-1)%Z, (na, (nb, (nc, nd)), np)) =
      ((Z.sgn a * Z.sgn c)%Z, (a, (b, (c, d)), nR p)));
    [ apply
       trans_eq
        with
          (Qhomographic_sign a b c d (nR p) H_Qhomographic_sg_denom_nonzero);
       assumption || symmetry  in |- *; assumption
    | elim
       (sg_tuple_equal (-1) na nb nc nd np (Z.sgn a * Z.sgn c) a b c d 
          (nR p) H6); intros H_ac ((H8, (H9, (H10, H11))), H12);
       repeat match goal with
              | id1:(?X1 = ?X2) |- ?X3 => rewrite id1
              end ]; left; rewrite <- Zsgn_15 in H_ac;
    case (Zsgn_17 _ _ (sym_eq H_ac)); intros (Ha, Hc); 
    [ left | right ]; repeat split;
    apply Z.le_refl || (apply Zlt_le_weak; assumption).

  
   case (Z_lt_dec 0 o2); intros Ho2.
    generalize
     (Qhomographic_sign_nR_2 a b c d (nR p) p H_Qhomographic_sg_denom_nonzero
        (refl_equal (nR p)) Hb Hd Ho2); intro;
     assert
      (H6 :
       ((-1)%Z, (na, (nb, (nc, nd)), np)) = (Z.sgn a, (a, (b, (c, d)), nR p)));
     [ apply
        trans_eq
         with
           (Qhomographic_sign a b c d (nR p) H_Qhomographic_sg_denom_nonzero);
        assumption || symmetry  in |- *; assumption
     | elim (sg_tuple_equal (-1) na nb nc nd np (Z.sgn a) a b c d (nR p) H6);
        intros H_a ((H8, (H9, (H10, H11))), H12);
        repeat match goal with
               | id1:(?X1 = ?X2) |- ?X3 => rewrite id1
               end ]; left; right; repeat split; first
     [ apply Z.le_refl
     | match goal with
       |  |- (0 <= ?X1)%Z =>
           apply Zlt_le_weak; apply Zsgn_9; apply Z.opp_inj
       |  |- (?X1 <= 0)%Z => apply Zlt_le_weak; apply Zsgn_10
       end; apply sym_eq; assumption
     | unfold o2 in Ho2;
        match goal with
        | id1:(0 < outside_interval ?X1 ?X2)%Z |- (0 <= ?X1)%Z =>
            apply Zsgn_21 with X2
        | id1:(0 < outside_interval ?X1 ?X2)%Z |- (0 <= ?X2)%Z =>
            apply Zsgn_23 with X1
        | id1:(outside_interval ?X1 ?X2 < 0)%Z |- (?X1 <= 0)%Z =>
            apply Zsgn_22 with X2
        | id1:(outside_interval ?X1 ?X2 < 0)%Z |- (?X2 <= 0)%Z =>
            apply Zsgn_24 with X1
        end; assumption ].
    
    case (Z_lt_dec o2 0); intros Ho2'.
     generalize
      (Qhomographic_sign_nR_3 a b c d (nR p) p
         H_Qhomographic_sg_denom_nonzero (refl_equal (nR p)) Hb Hd Ho2 Ho2');
      intro;
      assert
       (H6 :
        ((-1)%Z, (na, (nb, (nc, nd)), np)) =
        ((- Z.sgn a)%Z, (a, (b, (c, d)), nR p)));
      [ apply
         trans_eq
          with
            (Qhomographic_sign a b c d (nR p) H_Qhomographic_sg_denom_nonzero);
         assumption || symmetry  in |- *; assumption
      | elim
         (sg_tuple_equal (-1) na nb nc nd np (- Z.sgn a) a b c d (nR p) H6);
         intros H_a ((H8, (H9, (H10, H11))), H12);
         repeat match goal with
                | id1:(?X1 = ?X2) |- ?X3 => rewrite id1
                end ]; left; left; repeat split; first
      [ apply Z.le_refl
      | match goal with
        |  |- (0 <= ?X1)%Z =>
            apply Zlt_le_weak; apply Zsgn_9; apply Z.opp_inj
        |  |- (?X1 <= 0)%Z => apply Zlt_le_weak; apply Zsgn_10
        end; apply sym_eq; assumption
      | unfold o2 in Ho2, Ho2';
         match goal with
         | id1:(0 < outside_interval ?X1 ?X2)%Z |- 
         (0 <= ?X1)%Z =>
             apply Zsgn_21 with X2
         | id1:(0 < outside_interval ?X1 ?X2)%Z |- 
         (0 <= ?X2)%Z =>
             apply Zsgn_23 with X1
         | id1:(outside_interval ?X1 ?X2 < 0)%Z |- 
         (?X1 <= 0)%Z =>
             apply Zsgn_22 with X2
         | id1:(outside_interval ?X1 ?X2 < 0)%Z |- 
         (?X2 <= 0)%Z => apply Zsgn_24 with X1
         end; assumption ].

 
     generalize
      (Qhomographic_sign_nR_4 a b c d (nR p) p
         (Qhomographic_signok_2 c d p H_Qhomographic_sg_denom_nonzero)
         H_Qhomographic_sg_denom_nonzero Hb Hd Ho2 Ho2'); 
      intro;
      apply
       (sg_neg_2 a (a + b)%Z c (c + d)%Z p
          (Qhomographic_signok_2 c d p H_Qhomographic_sg_denom_nonzero) na nb
          nc nd np);
      apply
       trans_eq
        with
          (Qhomographic_sign a b c d (nR p) H_Qhomographic_sg_denom_nonzero);
      assumption || symmetry  in |- *; assumption.

  case (Z_zerop d); intro Hd. 
   case (Z_lt_dec 0 o1); intro Ho1. 
    generalize
     (Qhomographic_sign_nR_5 a b c d (nR p) p H_Qhomographic_sg_denom_nonzero
        (refl_equal (nR p)) Hb Hd Ho1); intro;
     assert
      (H6 :
       ((-1)%Z, (na, (nb, (nc, nd)), np)) = (Z.sgn c, (a, (b, (c, d)), nR p)));
     [ apply
        trans_eq
         with
           (Qhomographic_sign a b c d (nR p) H_Qhomographic_sg_denom_nonzero);
        assumption || symmetry  in |- *; assumption
     | elim (sg_tuple_equal (-1) na nb nc nd np (Z.sgn c) a b c d (nR p) H6);
        intros H_a ((H8, (H9, (H10, H11))), H12);
        repeat match goal with
               | id1:(?X1 = ?X2) |- ?X3 => rewrite id1
               end ]; left; left; repeat split; first
     [ apply Z.le_refl
     | match goal with
       |  |- (0 <= ?X1)%Z =>
           apply Zlt_le_weak; apply Zsgn_9; apply Z.opp_inj
       |  |- (?X1 <= 0)%Z => apply Zlt_le_weak; apply Zsgn_10
       end; apply sym_eq; assumption
     | unfold o1 in Ho1;
        match goal with
        | id1:(0 < outside_interval ?X1 ?X2)%Z |- (0 <= ?X1)%Z =>
            apply Zsgn_21 with X2
        | id1:(0 < outside_interval ?X1 ?X2)%Z |- (0 <= ?X2)%Z =>
            apply Zsgn_23 with X1
        | id1:(outside_interval ?X1 ?X2 < 0)%Z |- (?X1 <= 0)%Z =>
            apply Zsgn_22 with X2
        | id1:(outside_interval ?X1 ?X2 < 0)%Z |- (?X2 <= 0)%Z =>
            apply Zsgn_24 with X1
        end; assumption ].

    
    case (Z_lt_dec o1 0); intros Ho1'.
     generalize
      (Qhomographic_sign_nR_6 a b c d (nR p) p
         H_Qhomographic_sg_denom_nonzero (refl_equal (nR p)) Hb Hd Ho1 Ho1');
      intro;
      assert
       (H6 :
        ((-1)%Z, (na, (nb, (nc, nd)), np)) =
        ((- Z.sgn c)%Z, (a, (b, (c, d)), nR p)));
      [ apply
         trans_eq
          with
            (Qhomographic_sign a b c d (nR p) H_Qhomographic_sg_denom_nonzero);
         assumption || symmetry  in |- *; assumption
      | elim
         (sg_tuple_equal (-1) na nb nc nd np (- Z.sgn c) a b c d (nR p) H6);
         intros H_a ((H8, (H9, (H10, H11))), H12);
         repeat match goal with
                | id1:(?X1 = ?X2) |- ?X3 => rewrite id1
                end ]; left; right; repeat split; first
      [ apply Z.le_refl
      | match goal with
        |  |- (0 <= ?X1)%Z =>
            apply Zlt_le_weak; apply Zsgn_9; apply Z.opp_inj
        |  |- (?X1 <= 0)%Z => apply Zlt_le_weak; apply Zsgn_10
        end; apply sym_eq; assumption
      | unfold o1 in Ho1, Ho1';
         match goal with
         | id1:(0 < outside_interval ?X1 ?X2)%Z |- 
         (0 <= ?X1)%Z =>
             apply Zsgn_21 with X2
         | id1:(0 < outside_interval ?X1 ?X2)%Z |- 
         (0 <= ?X2)%Z =>
             apply Zsgn_23 with X1
         | id1:(outside_interval ?X1 ?X2 < 0)%Z |- 
         (?X1 <= 0)%Z =>
             apply Zsgn_22 with X2
         | id1:(outside_interval ?X1 ?X2 < 0)%Z |- 
         (?X2 <= 0)%Z => apply Zsgn_24 with X1
         end; assumption ].

 
     generalize
      (Qhomographic_sign_nR_7 a b c d (nR p) p
         (Qhomographic_signok_2 c d p H_Qhomographic_sg_denom_nonzero)
         H_Qhomographic_sg_denom_nonzero Hb Hd Ho1 Ho1'); 
      intro;
      apply
       (sg_neg_2 a (a + b)%Z c (c + d)%Z p
          (Qhomographic_signok_2 c d p H_Qhomographic_sg_denom_nonzero) na nb
          nc nd np);
      apply
       trans_eq
        with
          (Qhomographic_sign a b c d (nR p) H_Qhomographic_sg_denom_nonzero);
      assumption || symmetry  in |- *; assumption.

  case (inside_interval_1_dec_inf o1 o2); intro H_inside_1.
    generalize
     (Qhomographic_sign_nR_8 a b c d (nR p) p H_Qhomographic_sg_denom_nonzero
        (refl_equal (nR p)) Hb Hd H_inside_1); intro;
     assert
      (H6 :
       ((-1)%Z, (na, (nb, (nc, nd)), np)) = (1%Z, (a, (b, (c, d)), nR p)));
     [ apply
        trans_eq
         with
           (Qhomographic_sign a b c d (nR p) H_Qhomographic_sg_denom_nonzero);
        assumption || symmetry  in |- *; assumption
     | elim (sg_tuple_equal (-1) na nb nc nd np 1 a b c d (nR p) H6);
        intros hl ((H8, (H9, (H10, H11))), H12); discriminate hl ].

    case (inside_interval_2_dec_inf o1 o2); intro H_inside_2.

      generalize
       (Qhomographic_sign_nR_9 a b c d (nR p) p
          H_Qhomographic_sg_denom_nonzero (refl_equal (nR p)) Hb Hd
          H_inside_1 H_inside_2); intro;
       assert
        (H6 :
         ((-1)%Z, (na, (nb, (nc, nd)), np)) =
         ((-1)%Z, (a, (b, (c, d)), nR p)));
       [ apply
          trans_eq
           with
             (Qhomographic_sign a b c d (nR p)
                H_Qhomographic_sg_denom_nonzero);
          assumption || symmetry  in |- *; assumption
       | elim (sg_tuple_equal (-1) na nb nc nd np (-1) a b c d (nR p) H6);
          intros _ ((H8, (H9, (H10, H11))), H12);
          repeat match goal with
                 | id1:(?X1 = ?X2) |- ?X3 => rewrite id1
                 end ].
      left; case (inside_interval_2_inf _ _ H_inside_2); intros (Ho1, Ho2);
       [ left | right ]; repeat split; unfold o1 in Ho1; 
       unfold o2 in Ho2;
       match goal with
       | id1:(0 < outside_interval ?X1 ?X2)%Z |- (0 <= ?X1)%Z =>
           apply Zsgn_21 with X2
       | id1:(0 < outside_interval ?X1 ?X2)%Z |- (0 <= ?X2)%Z =>
           apply Zsgn_23 with X1
       | id1:(outside_interval ?X1 ?X2 < 0)%Z |- (?X1 <= 0)%Z =>
           apply Zsgn_22 with X2
       | id1:(outside_interval ?X1 ?X2 < 0)%Z |- (?X2 <= 0)%Z =>
           apply Zsgn_24 with X1
       end; assumption.

      generalize
       (Qhomographic_sign_nR_10 a b c d (nR p) p
          (Qhomographic_signok_2 c d p H_Qhomographic_sg_denom_nonzero)
          H_Qhomographic_sg_denom_nonzero Hb Hd H_inside_1 H_inside_2); 
       intro;
       apply
        (sg_neg_2 a (a + b)%Z c (c + d)%Z p
           (Qhomographic_signok_2 c d p H_Qhomographic_sg_denom_nonzero) na
           nb nc nd np);
       apply
        trans_eq
         with
           (Qhomographic_sign a b c d (nR p) H_Qhomographic_sg_denom_nonzero);
       assumption || symmetry  in |- *; assumption.

(* p = (dL p) *) 
 case (Z_zerop b); intro Hb.
  case (Z_zerop d); intro Hd.
   generalize
    (Qhomographic_sign_dL_1 a b c d (dL p) p H_Qhomographic_sg_denom_nonzero
       (refl_equal (dL p)) Hb Hd); intro;
    assert
     (H6 :
      ((-1)%Z, (na, (nb, (nc, nd)), np)) =
      ((Z.sgn a * Z.sgn c)%Z, (a, (b, (c, d)), dL p)));
    [ apply
       trans_eq
        with
          (Qhomographic_sign a b c d (dL p) H_Qhomographic_sg_denom_nonzero);
       assumption || symmetry  in |- *; assumption
    | elim
       (sg_tuple_equal (-1) na nb nc nd np (Z.sgn a * Z.sgn c) a b c d 
          (dL p) H6); intros H_ac ((H8, (H9, (H10, H11))), H12);
       repeat match goal with
              | id1:(?X1 = ?X2) |- ?X3 => rewrite id1
              end ]; left; rewrite <- Zsgn_15 in H_ac;
    case (Zsgn_17 _ _ (sym_eq H_ac)); intros (Ha, Hc); 
    [ left | right ]; repeat split;
    apply Z.le_refl || (apply Zlt_le_weak; assumption).

  
   case (Z_lt_dec 0 o2); intros Ho2.
    generalize
     (Qhomographic_sign_dL_2 a b c d (dL p) p H_Qhomographic_sg_denom_nonzero
        (refl_equal (dL p)) Hb Hd Ho2); intro;
     assert
      (H6 :
       ((-1)%Z, (na, (nb, (nc, nd)), np)) = (Z.sgn a, (a, (b, (c, d)), dL p)));
     [ apply
        trans_eq
         with
           (Qhomographic_sign a b c d (dL p) H_Qhomographic_sg_denom_nonzero);
        assumption || symmetry  in |- *; assumption
     | elim (sg_tuple_equal (-1) na nb nc nd np (Z.sgn a) a b c d (dL p) H6);
        intros H_a ((H8, (H9, (H10, H11))), H12);
        repeat match goal with
               | id1:(?X1 = ?X2) |- ?X3 => rewrite id1
               end ]; left; right; repeat split; first
     [ apply Z.le_refl
     | match goal with
       |  |- (0 <= ?X1)%Z =>
           apply Zlt_le_weak; apply Zsgn_9; apply Z.opp_inj
       |  |- (?X1 <= 0)%Z => apply Zlt_le_weak; apply Zsgn_10
       end; apply sym_eq; assumption
     | unfold o2 in Ho2;
        match goal with
        | id1:(0 < outside_interval ?X1 ?X2)%Z |- (0 <= ?X1)%Z =>
            apply Zsgn_21 with X2
        | id1:(0 < outside_interval ?X1 ?X2)%Z |- (0 <= ?X2)%Z =>
            apply Zsgn_23 with X1
        | id1:(outside_interval ?X1 ?X2 < 0)%Z |- (?X1 <= 0)%Z =>
            apply Zsgn_22 with X2
        | id1:(outside_interval ?X1 ?X2 < 0)%Z |- (?X2 <= 0)%Z =>
            apply Zsgn_24 with X1
        end; assumption ].
    
    case (Z_lt_dec o2 0); intros Ho2'.
     generalize
      (Qhomographic_sign_dL_3 a b c d (dL p) p
         H_Qhomographic_sg_denom_nonzero (refl_equal (dL p)) Hb Hd Ho2 Ho2');
      intro;
      assert
       (H6 :
        ((-1)%Z, (na, (nb, (nc, nd)), np)) =
        ((- Z.sgn a)%Z, (a, (b, (c, d)), dL p)));
      [ apply
         trans_eq
          with
            (Qhomographic_sign a b c d (dL p) H_Qhomographic_sg_denom_nonzero);
         assumption || symmetry  in |- *; assumption
      | elim
         (sg_tuple_equal (-1) na nb nc nd np (- Z.sgn a) a b c d (dL p) H6);
         intros H_a ((H8, (H9, (H10, H11))), H12);
         repeat match goal with
                | id1:(?X1 = ?X2) |- ?X3 => rewrite id1
                end ]; left; left; repeat split; first
      [ apply Z.le_refl
      | match goal with
        |  |- (0 <= ?X1)%Z =>
            apply Zlt_le_weak; apply Zsgn_9; apply Z.opp_inj
        |  |- (?X1 <= 0)%Z => apply Zlt_le_weak; apply Zsgn_10
        end; apply sym_eq; assumption
      | unfold o2 in Ho2, Ho2';
         match goal with
         | id1:(0 < outside_interval ?X1 ?X2)%Z |- 
         (0 <= ?X1)%Z =>
             apply Zsgn_21 with X2
         | id1:(0 < outside_interval ?X1 ?X2)%Z |- 
         (0 <= ?X2)%Z =>
             apply Zsgn_23 with X1
         | id1:(outside_interval ?X1 ?X2 < 0)%Z |- 
         (?X1 <= 0)%Z =>
             apply Zsgn_22 with X2
         | id1:(outside_interval ?X1 ?X2 < 0)%Z |- 
         (?X2 <= 0)%Z => apply Zsgn_24 with X1
         end; assumption ].

 
     generalize
      (Qhomographic_sign_dL_4 a b c d (dL p) p
         (Qhomographic_signok_3 c d p H_Qhomographic_sg_denom_nonzero)
         H_Qhomographic_sg_denom_nonzero Hb Hd Ho2 Ho2'); 
      intro;
      apply
       (sg_neg_2 (a + b)%Z b (c + d)%Z d p
          (Qhomographic_signok_3 c d p H_Qhomographic_sg_denom_nonzero) na nb
          nc nd np);
      apply
       trans_eq
        with
          (Qhomographic_sign a b c d (dL p) H_Qhomographic_sg_denom_nonzero);
      assumption || symmetry  in |- *; assumption.

  case (Z_zerop d); intro Hd. 
   case (Z_lt_dec 0 o1); intro Ho1. 
    generalize
     (Qhomographic_sign_dL_5 a b c d (dL p) p H_Qhomographic_sg_denom_nonzero
        (refl_equal (dL p)) Hb Hd Ho1); intro;
     assert
      (H6 :
       ((-1)%Z, (na, (nb, (nc, nd)), np)) = (Z.sgn c, (a, (b, (c, d)), dL p)));
     [ apply
        trans_eq
         with
           (Qhomographic_sign a b c d (dL p) H_Qhomographic_sg_denom_nonzero);
        assumption || symmetry  in |- *; assumption
     | elim (sg_tuple_equal (-1) na nb nc nd np (Z.sgn c) a b c d (dL p) H6);
        intros H_a ((H8, (H9, (H10, H11))), H12);
        repeat match goal with
               | id1:(?X1 = ?X2) |- ?X3 => rewrite id1
               end ]; left; left; repeat split; first
     [ apply Z.le_refl
     | match goal with
       |  |- (0 <= ?X1)%Z =>
           apply Zlt_le_weak; apply Zsgn_9; apply Z.opp_inj
       |  |- (?X1 <= 0)%Z => apply Zlt_le_weak; apply Zsgn_10
       end; apply sym_eq; assumption
     | unfold o1 in Ho1;
        match goal with
        | id1:(0 < outside_interval ?X1 ?X2)%Z |- (0 <= ?X1)%Z =>
            apply Zsgn_21 with X2
        | id1:(0 < outside_interval ?X1 ?X2)%Z |- (0 <= ?X2)%Z =>
            apply Zsgn_23 with X1
        | id1:(outside_interval ?X1 ?X2 < 0)%Z |- (?X1 <= 0)%Z =>
            apply Zsgn_22 with X2
        | id1:(outside_interval ?X1 ?X2 < 0)%Z |- (?X2 <= 0)%Z =>
            apply Zsgn_24 with X1
        end; assumption ].

    
    case (Z_lt_dec o1 0); intros Ho1'.
     generalize
      (Qhomographic_sign_dL_6 a b c d (dL p) p
         H_Qhomographic_sg_denom_nonzero (refl_equal (dL p)) Hb Hd Ho1 Ho1');
      intro;
      assert
       (H6 :
        ((-1)%Z, (na, (nb, (nc, nd)), np)) =
        ((- Z.sgn c)%Z, (a, (b, (c, d)), dL p)));
      [ apply
         trans_eq
          with
            (Qhomographic_sign a b c d (dL p) H_Qhomographic_sg_denom_nonzero);
         assumption || symmetry  in |- *; assumption
      | elim
         (sg_tuple_equal (-1) na nb nc nd np (- Z.sgn c) a b c d (dL p) H6);
         intros H_a ((H8, (H9, (H10, H11))), H12);
         repeat match goal with
                | id1:(?X1 = ?X2) |- ?X3 => rewrite id1
                end ]; left; right; repeat split; first
      [ apply Z.le_refl
      | match goal with
        |  |- (0 <= ?X1)%Z =>
            apply Zlt_le_weak; apply Zsgn_9; apply Z.opp_inj
        |  |- (?X1 <= 0)%Z => apply Zlt_le_weak; apply Zsgn_10
        end; apply sym_eq; assumption
      | unfold o1 in Ho1, Ho1';
         match goal with
         | id1:(0 < outside_interval ?X1 ?X2)%Z |- 
         (0 <= ?X1)%Z =>
             apply Zsgn_21 with X2
         | id1:(0 < outside_interval ?X1 ?X2)%Z |- 
         (0 <= ?X2)%Z =>
             apply Zsgn_23 with X1
         | id1:(outside_interval ?X1 ?X2 < 0)%Z |- 
         (?X1 <= 0)%Z =>
             apply Zsgn_22 with X2
         | id1:(outside_interval ?X1 ?X2 < 0)%Z |- 
         (?X2 <= 0)%Z => apply Zsgn_24 with X1
         end; assumption ].

 
     generalize
      (Qhomographic_sign_dL_7 a b c d (dL p) p
         (Qhomographic_signok_3 c d p H_Qhomographic_sg_denom_nonzero)
         H_Qhomographic_sg_denom_nonzero Hb Hd Ho1 Ho1'); 
      intro;
      apply
       (sg_neg_2 (a + b)%Z b (c + d)%Z d p
          (Qhomographic_signok_3 c d p H_Qhomographic_sg_denom_nonzero) na nb
          nc nd np);
      apply
       trans_eq
        with
          (Qhomographic_sign a b c d (dL p) H_Qhomographic_sg_denom_nonzero);
      assumption || symmetry  in |- *; assumption.

  case (inside_interval_1_dec_inf o1 o2); intro H_inside_1.
    generalize
     (Qhomographic_sign_dL_8 a b c d (dL p) p H_Qhomographic_sg_denom_nonzero
        (refl_equal (dL p)) Hb Hd H_inside_1); intro;
     assert
      (H6 :
       ((-1)%Z, (na, (nb, (nc, nd)), np)) = (1%Z, (a, (b, (c, d)), dL p)));
     [ apply
        trans_eq
         with
           (Qhomographic_sign a b c d (dL p) H_Qhomographic_sg_denom_nonzero);
        assumption || symmetry  in |- *; assumption
     | elim (sg_tuple_equal (-1) na nb nc nd np 1 a b c d (dL p) H6);
        intros hl ((H8, (H9, (H10, H11))), H12); discriminate hl ].

    case (inside_interval_2_dec_inf o1 o2); intro H_inside_2.

      generalize
       (Qhomographic_sign_dL_9 a b c d (dL p) p
          H_Qhomographic_sg_denom_nonzero (refl_equal (dL p)) Hb Hd
          H_inside_1 H_inside_2); intro;
       assert
        (H6 :
         ((-1)%Z, (na, (nb, (nc, nd)), np)) =
         ((-1)%Z, (a, (b, (c, d)), dL p)));
       [ apply
          trans_eq
           with
             (Qhomographic_sign a b c d (dL p)
                H_Qhomographic_sg_denom_nonzero);
          assumption || symmetry  in |- *; assumption
       | elim (sg_tuple_equal (-1) na nb nc nd np (-1) a b c d (dL p) H6);
          intros _ ((H8, (H9, (H10, H11))), H12);
          repeat match goal with
                 | id1:(?X1 = ?X2) |- ?X3 => rewrite id1
                 end ].
      left; case (inside_interval_2_inf _ _ H_inside_2); intros (Ho1, Ho2);
       [ left | right ]; repeat split; unfold o1 in Ho1; 
       unfold o2 in Ho2;
       match goal with
       | id1:(0 < outside_interval ?X1 ?X2)%Z |- (0 <= ?X1)%Z =>
           apply Zsgn_21 with X2
       | id1:(0 < outside_interval ?X1 ?X2)%Z |- (0 <= ?X2)%Z =>
           apply Zsgn_23 with X1
       | id1:(outside_interval ?X1 ?X2 < 0)%Z |- (?X1 <= 0)%Z =>
           apply Zsgn_22 with X2
       | id1:(outside_interval ?X1 ?X2 < 0)%Z |- (?X2 <= 0)%Z =>
           apply Zsgn_24 with X1
       end; assumption.

      generalize
       (Qhomographic_sign_dL_10 a b c d (dL p) p
          (Qhomographic_signok_3 c d p H_Qhomographic_sg_denom_nonzero)
          H_Qhomographic_sg_denom_nonzero Hb Hd H_inside_1 H_inside_2); 
       intro;
       apply
        (sg_neg_2 (a + b)%Z b (c + d)%Z d p
           (Qhomographic_signok_3 c d p H_Qhomographic_sg_denom_nonzero) na
           nb nc nd np);
       apply
        trans_eq
         with
           (Qhomographic_sign a b c d (dL p) H_Qhomographic_sg_denom_nonzero);
       assumption || symmetry  in |- *; assumption.

 (* p = One *)
 case (Z_zerop (Z.sgn (a + b))); intro Hab.  
  apply False_rec;
   generalize
    (sg_One_2 a b c d One H_Qhomographic_sg_denom_nonzero 
       (refl_equal One) Hab); intro;
   assert
    (H2 : ((-1)%Z, (na, (nb, (nc, nd)), np)) = (0%Z, (a, (b, (c, d)), One)));
   [ apply
      trans_eq
       with (Qhomographic_sign a b c d One H_Qhomographic_sg_denom_nonzero);
      assumption || symmetry  in |- *; assumption
   | elim (sg_tuple_equal (-1) na nb nc nd np 0 a b c d One H2); intros H3 H4;
      discriminate H3 ].
 
  case (Z.eq_dec (Z.sgn (a + b)) (Z.sgn (c + d))); intro Habcd.
   generalize
    (sg_One_3 a b c d One H_Qhomographic_sg_denom_nonzero 
       (refl_equal One) Hab Habcd); intro; apply False_rec;
    assert
     (H2 : ((-1)%Z, (na, (nb, (nc, nd)), np)) = (1%Z, (a, (b, (c, d)), One)));
    [ apply
       trans_eq
        with (Qhomographic_sign a b c d One H_Qhomographic_sg_denom_nonzero);
       assumption || symmetry  in |- *; assumption
    | elim (sg_tuple_equal (-1) na nb nc nd np 1 a b c d One H2);
       intro H_discrim; discriminate H_discrim ].

 
   generalize
    (sg_One_4 a b c d One H_Qhomographic_sg_denom_nonzero 
       (refl_equal One) Hab Habcd); intro;
    assert
     (H2 :
      ((-1)%Z, (na, (nb, (nc, nd)), np)) = ((-1)%Z, (a, (b, (c, d)), One)));
    [ apply
       trans_eq
        with (Qhomographic_sign a b c d One H_Qhomographic_sg_denom_nonzero);
       assumption || symmetry  in |- *; assumption
    | elim (sg_tuple_equal (-1) na nb nc nd np (-1) a b c d One H2);
       intros _ ((H8, (H9, (H10, H11))), H12);
       repeat match goal with
              | id1:(?X1 = ?X2) |- ?X3 => rewrite id1
              end; right; reflexivity ].
Qed.
