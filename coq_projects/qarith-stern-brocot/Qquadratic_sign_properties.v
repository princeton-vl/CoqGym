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


Require Import ZArithRing.
Require Export Qhomographic_sign.
Require Export Qquadratic_sign.
Require Export Qhomographic_sign_properties.

Definition same_ratio (a b c d e f g h : Z) :=
  (a * f)%Z = (b * e)%Z /\
  (b * g)%Z = (c * f)%Z /\
  (c * h)%Z = (d * g)%Z /\
  (a * g)%Z = (c * e)%Z /\ (a * h)%Z = (d * e)%Z /\ (b * h)%Z = (d * f)%Z.

Lemma same_ratio_dec_inf :
 forall a b c d e f g h : Z,
 {same_ratio a b c d e f g h} + {~ same_ratio a b c d e f g h}.
Proof. 
 intros.
 case (Z.eq_dec (a * f) (b * e));
  [ case (Z.eq_dec (b * g) (c * f));
     [ case (Z.eq_dec (c * h) (d * g));
        [ case (Z.eq_dec (a * g) (c * e));
           [ case (Z.eq_dec (a * h) (d * e));
              [ case (Z.eq_dec (b * h) (d * f));
                 [ left; repeat split; assumption | idtac ]
              | idtac ]
           | idtac ]
        | idtac ]
     | idtac ]
  | idtac ]; intro H'; try intros; right;
  intros (Hafbe, (Hbgcf, (Hchgd, (Hagce, (Hahde, Hbhdf))))); 
  apply H'; assumption.
Qed.

Lemma Qquadratic_sign_tuple_equal :
 forall (l1 a1 b1 c1 d1 e1 f1 g1 h1 : Z) (x1 y1 : Qpositive)
   (l2 a2 b2 c2 d2 e2 f2 g2 h2 : Z) (x2 y2 : Qpositive),
 (l1, (a1, (b1, (c1, d1)), (e1, (f1, (g1, h1))), (x1, y1))) =
 (l2, (a2, (b2, (c2, d2)), (e2, (f2, (g2, h2))), (x2, y2))) ->
 l1 = l2 /\
 (a1 = a2 /\
  b1 = b2 /\ c1 = c2 /\ d1 = d2 /\ e1 = e2 /\ f1 = f2 /\ g1 = g2 /\ h1 = h2) /\
 x1 = x2 /\ y1 = y2.
Proof.
 intros.
 inversion H; (repeat split; reflexivity).
Qed.

(* Proof by case analysis: 81 cases in 6 line :-) *)

Lemma outside_square_1 :
 forall a b c d : Z, (2 < outside_square a b c d)%Z -> (0 < a + b + c + d)%Z.
Proof.
intros [| pa| pa] [| pb| pb] [| pc| pc] [| pd| pd];
            repeat rewrite Zplus_0_r; repeat rewrite Zplus_0_l; 
            intro H; first [ discriminate H | repeat constructor ].
Qed.

Lemma outside_square_2 :
 forall a b c d : Z, (outside_square a b c d < -2)%Z -> (a + b + c + d < 0)%Z.
Proof.
intros [| pa| pa] [| pb| pb] [| pc| pc] [| pd| pd];
            repeat rewrite Zplus_0_r; repeat rewrite Zplus_0_l; 
            intro H; first [ discriminate H | repeat constructor ].
Qed.

Lemma outside_square_3 :
 forall a b c d : Z, (2 < outside_square a b c d)%Z -> (0 <= a)%Z.
Proof.
intros [| pa| pa] [| pb| pb] [| pc| pc] [| pd| pd];
            repeat rewrite Zplus_0_r; repeat rewrite Zplus_0_l; 
            intro H; first
            [ intro H_discriminate_me; discriminate H_discriminate_me
            | discriminate H
            | repeat constructor
            | apply Zero_le_Qpos ].
Qed.

Lemma outside_square_4 :
 forall a b c d : Z, (2 < outside_square a b c d)%Z -> (0 <= b)%Z.
Proof.
intros [| pa| pa] [| pb| pb] [| pc| pc] [| pd| pd];
            repeat rewrite Zplus_0_r; repeat rewrite Zplus_0_l; 
            intro H; first
            [ intro H_discriminate_me; discriminate H_discriminate_me
            | discriminate H
            | repeat constructor
            | apply Zero_le_Qpos ].
Qed.

Lemma outside_square_5 :
 forall a b c d : Z, (2 < outside_square a b c d)%Z -> (0 <= c)%Z.
Proof.
intros [| pa| pa] [| pb| pb] [| pc| pc] [| pd| pd];
            repeat rewrite Zplus_0_r; repeat rewrite Zplus_0_l; 
            intro H; first
            [ intro H_discriminate_me; discriminate H_discriminate_me
            | discriminate H
            | repeat constructor
            | apply Zero_le_Qpos ].
Qed.

Lemma outside_square_6 :
 forall a b c d : Z, (2 < outside_square a b c d)%Z -> (0 <= d)%Z.
Proof.
intros [| pa| pa] [| pb| pb] [| pc| pc] [| pd| pd];
            repeat rewrite Zplus_0_r; repeat rewrite Zplus_0_l; 
            intro H; first
            [ intro H_discriminate_me; discriminate H_discriminate_me
            | discriminate H
            | repeat constructor
            | apply Zero_le_Qpos ].
Qed.

Lemma outside_square_7 :
 forall a b c d : Z, (outside_square a b c d < -2)%Z -> (a <= 0)%Z.
Proof.
intros [| pa| pa] [| pb| pb] [| pc| pc] [| pd| pd];
            repeat rewrite Zplus_0_r; repeat rewrite Zplus_0_l; 
            intro H; first
            [ intro H_discriminate_me; discriminate H_discriminate_me
            | discriminate H
            | repeat constructor
            | apply Zero_le_Qpos ].
Qed.

Lemma outside_square_8 :
 forall a b c d : Z, (outside_square a b c d < -2)%Z -> (b <= 0)%Z.
Proof.
intros [| pa| pa] [| pb| pb] [| pc| pc] [| pd| pd];
            repeat rewrite Zplus_0_r; repeat rewrite Zplus_0_l; 
            intro H; first
            [ intro H_discriminate_me; discriminate H_discriminate_me
            | discriminate H
            | repeat constructor
            | apply Zero_le_Qpos ].
Qed.

Lemma outside_square_9 :
 forall a b c d : Z, (outside_square a b c d < -2)%Z -> (c <= 0)%Z.
Proof.
intros [| pa| pa] [| pb| pb] [| pc| pc] [| pd| pd];
            repeat rewrite Zplus_0_r; repeat rewrite Zplus_0_l; 
            intro H; first
            [ intro H_discriminate_me; discriminate H_discriminate_me
            | discriminate H
            | repeat constructor
            | apply Zero_le_Qpos ].
Qed.

Lemma outside_square_10 :
 forall a b c d : Z, (outside_square a b c d < -2)%Z -> (d <= 0)%Z.
Proof.
intros [| pa| pa] [| pb| pb] [| pc| pc] [| pd| pd];
            repeat rewrite Zplus_0_r; repeat rewrite Zplus_0_l; 
            intro H; first
            [ intro H_discriminate_me; discriminate H_discriminate_me
            | discriminate H
            | repeat constructor
            | apply Zero_le_Qpos ].
Qed.

Lemma inside_square_1_inf :
 forall o1 o2 : Z,
 inside_square_1 o1 o2 ->
 {(2 < o1)%Z /\ (2 < o2)%Z} + {(o1 < -2)%Z /\ (o2 < -2)%Z}.
Proof.
 intros o1 o2 H.
 case (Z_lt_dec 2 o1); intros Ho1;
            [ case (Z_lt_dec 2 o2); intros Ho2;
               [ left; split; assumption | idtac ]
            | case (Z_lt_dec o1 (-2)); intros Ho1';
               [ case (Z_lt_dec o2 (-2)); intros Ho2;
                  [ right; split; assumption | idtac ]
               | idtac ] ]; apply False_rec; case H; 
            intros (Ho1_, Ho2_);
            repeat
             match goal with
             | id1:(~ (?X1 < ?X2)%Z) |- ?X3 => apply id1; assumption
             end ||
               match goal with
               | id1:(Zpos ?X1 < ?X2)%Z,id2:(?X2 < Zneg ?X1)%Z |- ?X3 =>
                   apply (Z.lt_irrefl (Zpos X1));
                    apply Z.lt_trans with (Zneg X1);
                    constructor || apply Z.lt_trans with X2; 
                    assumption
               end.
Qed.

Lemma inside_square_2_inf :
 forall o1 o2 : Z,
 inside_square_2 o1 o2 ->
 {(2 < o1)%Z /\ (o2 < -2)%Z} + {(o1 < -2)%Z /\ (2 < o2)%Z}.
Proof.
 intros o1 o2 H.
 case (Z_lt_dec 2 o1); intros Ho1;
            [ case (Z_lt_dec o2 (-2)); intros Ho2;
               [ left; split; assumption | idtac ]
            | case (Z_lt_dec o1 (-2)); intros Ho1';
               [ case (Z_lt_dec 2 o2); intros Ho2;
                  [ right; split; assumption | idtac ]
               | idtac ] ]; apply False_rec; case H; 
            intros (Ho1_, Ho2_);
            repeat
             match goal with
             | id1:(~ (?X1 < ?X2)%Z) |- ?X3 => apply id1; assumption
             end ||
               match goal with
               | id1:(Zpos ?X1 < ?X2)%Z,id2:(?X2 < Zneg ?X1)%Z |- ?X3 =>
                   apply (Z.lt_irrefl (Zpos X1));
                    apply Z.lt_trans with (Zneg X1);
                    constructor || apply Z.lt_trans with X2; 
                    assumption
               end.
Qed.

Lemma Qquadratic_sign_pos_1 :
 forall (a b c d e f g h : Z) (p1 p2 : Qpositive)
   (H_Qquadratic_sg_denom_nonzero : Qquadratic_sg_denom_nonzero e f g h p1 p2)
   (na nb nc nd ne nf ng nh : Z) (np1 np2 : Qpositive),
 Qquadratic_sign a b c d e f g h p1 p2 H_Qquadratic_sg_denom_nonzero =
 (1%Z, (na, (nb, (nc, nd)), (ne, (nf, (ng, nh))), (np1, np2))) ->
 {(0 < na + nb + nc + nd)%Z /\ (0 < ne + nf + ng + nh)%Z} +
 {(na + nb + nc + nd < 0)%Z /\ (ne + nf + ng + nh < 0)%Z}.
Proof. 
 fix Qquadratic_sign_pos_1 9.
 intros.
 set (o1 := outside_square a b c d) in *.
 set (o2 := outside_square e f g h) in *.
 destruct p1 as [xs| xs| ].
 (* p1 = (nR xs) *)
 destruct p2 as [ys| ys| ].
  (*  p1 = (nR xs) & p2 = (nR ys) *)
  case (three_integers_dec_inf b c d).  
   (* `b = 0`/\`c = 0`/\`d = 0` *)
   intros (Hb, (Hc, Hd)).
   (* Intros [Hb [Hc] Hd]. *)
   case (three_integers_dec_inf f g h).   
    (* `f = 0`/\`g = 0`/\`h = 0` *)
    intros (Hf, (Hg, Hh)).
    generalize
     (Qquadratic_sign_nRdL_nRdL_1 a b c d e f g h (nR xs) 
        (nR ys) H_Qquadratic_sg_denom_nonzero).
    intros H1.
    assert
     (H_tuple_eq :
      (1%Z, (na, (nb, (nc, nd)), (ne, (nf, (ng, nh))), (np1, np2))) =
      ((Z.sgn a * Z.sgn e)%Z,
      (a, (b, (c, d)), (e, (f, (g, h))), (nR xs, nR ys))));
     [ apply
        trans_eq
         with
           (Qquadratic_sign a b c d e f g h (nR xs) 
              (nR ys) H_Qquadratic_sg_denom_nonzero);
        [ apply sym_eq | apply H1; discriminate || (repeat split) ];
        assumption
     | generalize
        (Qquadratic_sign_tuple_equal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
           _ _ H_tuple_eq);
        intros
         (hl,
          ((hna, (hnb, (hnc, (hnd, (hne, (hnf, (hng, hnh))))))),
           (hp1, hp2)));
        do 10
         match goal with
         | id1:(?X1 = ?X2) |- ?X3 => try rewrite id1; clear id1
         end ].
    rewrite <- Zsgn_15 in hl.
    case (Zsgn_16 _ _ (sym_eq hl)); intros (Ha, He); [ left | right ];
     repeat split;
     repeat
      match goal with
      | id1:(?X1 = 0%Z) |- ?X2 => rewrite id1; clear id1
      end; repeat rewrite Zplus_0_r; assumption.
    (* ~(`f = 0`/\`g = 0`/\`h = 0`) *)
    intros H_fgh'.
    case (Z_lt_dec 2 o2).
     (*  `2 < o2` *)
     intro Ho2.
     generalize
      (Qquadratic_sign_nRdL_nRdL_2 a b c d e f g h 
         (nR xs) (nR ys) H_Qquadratic_sg_denom_nonzero).
     intros H1.
     assert
      (H_tuple_eq :
       (1%Z, (na, (nb, (nc, nd)), (ne, (nf, (ng, nh))), (np1, np2))) =
       (Z.sgn a, (a, (b, (c, d)), (e, (f, (g, h))), (nR xs, nR ys))));
      [ apply
         trans_eq
          with
            (Qquadratic_sign a b c d e f g h (nR xs) 
               (nR ys) H_Qquadratic_sg_denom_nonzero);
         [ apply sym_eq | apply H1; discriminate || (repeat split) ];
         assumption
      | generalize
         (Qquadratic_sign_tuple_equal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
            _ _ H_tuple_eq);
         intros
          (hl,
           ((hna, (hnb, (hnc, (hnd, (hne, (hnf, (hng, hnh))))))),
            (hp1, hp2)));
         do 10
          match goal with
          | id1:(?X1 = ?X2) |- ?X3 => try rewrite id1; clear id1
          end ].
     left; split;
      repeat
       match goal with
       | id1:(?X1 = 0%Z) |- ?X2 => rewrite id1; clear id1
       end; repeat rewrite Zplus_0_r;
      [ apply Zsgn_9; apply sym_eq; assumption
      | apply outside_square_1; assumption ].
     (*  ~`2 < o2` *)
     case (Z_lt_dec o2 (-2)).     
     (* `(-2) < o2` *)
      intros Ho2' Ho2.
      generalize
       (Qquadratic_sign_nRdL_nRdL_3 a b c d e f g h 
          (nR xs) (nR ys) H_Qquadratic_sg_denom_nonzero).
      intros H1.
      assert
       (H_tuple_eq :
        (1%Z, (na, (nb, (nc, nd)), (ne, (nf, (ng, nh))), (np1, np2))) =
        ((- Z.sgn a)%Z, (a, (b, (c, d)), (e, (f, (g, h))), (nR xs, nR ys))));
       [ apply
          trans_eq
           with
             (Qquadratic_sign a b c d e f g h (nR xs) 
                (nR ys) H_Qquadratic_sg_denom_nonzero);
          [ apply sym_eq | apply H1; discriminate || (repeat split) ];
          assumption
       | generalize
          (Qquadratic_sign_tuple_equal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
             _ _ _ H_tuple_eq);
          intros
           (hl,
            ((hna, (hnb, (hnc, (hnd, (hne, (hnf, (hng, hnh))))))),
             (hp1, hp2)));
          do 10
           match goal with
           | id1:(?X1 = ?X2) |- ?X3 => try rewrite id1; clear id1
           end ].
      right; split;
       repeat
        match goal with
        | id1:(?X1 = 0%Z) |- ?X2 => rewrite id1; clear id1
        end; repeat rewrite Zplus_0_r;
       [ apply Zsgn_10; apply sym_eq; apply Z.opp_inj; assumption
       | apply outside_square_2; assumption ]. 
     (* ~`o1 < (-2)` /\ ~`2 < o1` *)
      intros Ho2' Ho2.
      generalize
       (Qquadratic_sign_nR_nR_4 a b c d e f g h (nR xs) xs 
          (nR ys) ys H_Qquadratic_sg_denom_nonzero
          (Qquadratic_signok_1 _ _ _ _ _ _ H_Qquadratic_sg_denom_nonzero)
          (refl_equal _) (refl_equal _)).
      intros H1.
      assert
       (H_tuple_eq :
        Qquadratic_sign a (a + b) (a + c) (a + b + c + d) e 
          (e + f) (e + g) (e + f + g + h) xs ys
          (Qquadratic_signok_1 e f g h xs ys H_Qquadratic_sg_denom_nonzero) =
        (1%Z, (na, (nb, (nc, nd)), (ne, (nf, (ng, nh))), (np1, np2))));
       [ apply
          trans_eq
           with
             (Qquadratic_sign a b c d e f g h (nR xs) 
                (nR ys) H_Qquadratic_sg_denom_nonzero);
          [ apply sym_eq; apply H1; repeat split | idtac ]
       | apply
          (Qquadratic_sign_pos_1 a (a + b)%Z (a + c)%Z 
             (a + b + c + d)%Z e (e + f)%Z (e + g)%Z 
             (e + f + g + h)%Z xs ys
             (Qquadratic_signok_1 e f g h xs ys H_Qquadratic_sg_denom_nonzero)
             na nb nc nd ne nf ng nh np1 np2) ]; assumption.
   (* ~ `b = 0`/\`c = 0`/\`d = 0` *)
   intros Hbcd'.
   (* Intros [Hb [Hc] Hd]. *)
   case (three_integers_dec_inf f g h).   
    (* `f = 0`/\`g = 0`/\`h = 0` *)
    intros (Hf, (Hg, Hh)).
    case (Z_lt_dec 2 o1).
     (*  `2 < o1` *)
     intro Ho1.
     generalize
      (Qquadratic_sign_nRdL_nRdL_5 a b c d e f g h 
         (nR xs) (nR ys) H_Qquadratic_sg_denom_nonzero).
     intros H1.
     assert
      (H_tuple_eq :
       (1%Z, (na, (nb, (nc, nd)), (ne, (nf, (ng, nh))), (np1, np2))) =
       (Z.sgn e, (a, (b, (c, d)), (e, (f, (g, h))), (nR xs, nR ys))));
      [ apply
         trans_eq
          with
            (Qquadratic_sign a b c d e f g h (nR xs) 
               (nR ys) H_Qquadratic_sg_denom_nonzero);
         [ apply sym_eq | apply H1; discriminate || (repeat split) ];
         assumption
      | generalize
         (Qquadratic_sign_tuple_equal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
            _ _ H_tuple_eq);
         intros
          (hl,
           ((hna, (hnb, (hnc, (hnd, (hne, (hnf, (hng, hnh))))))),
            (hp1, hp2)));
         do 10
          match goal with
          | id1:(?X1 = ?X2) |- ?X3 => try rewrite id1; clear id1
          end ].
     left; split;
      repeat
       match goal with
       | id1:(?X1 = 0%Z) |- ?X2 => rewrite id1; clear id1
       end; repeat rewrite Zplus_0_r;
      [ apply outside_square_1 | apply Zsgn_9; apply sym_eq ]; 
      assumption.
     (*  ~`2 < o1` *)
     case (Z_lt_dec o1 (-2)).
      (* `(-2) < o1` *)
      intros Ho1' Ho1.
      generalize
       (Qquadratic_sign_nRdL_nRdL_6 a b c d e f g h 
          (nR xs) (nR ys) H_Qquadratic_sg_denom_nonzero).
      intros H1.
      assert
       (H_tuple_eq :
        (1%Z, (na, (nb, (nc, nd)), (ne, (nf, (ng, nh))), (np1, np2))) =
        ((- Z.sgn e)%Z, (a, (b, (c, d)), (e, (f, (g, h))), (nR xs, nR ys))));
       [ apply
          trans_eq
           with
             (Qquadratic_sign a b c d e f g h (nR xs) 
                (nR ys) H_Qquadratic_sg_denom_nonzero);
          [ apply sym_eq | apply H1; discriminate || (repeat split) ];
          assumption
       | generalize
          (Qquadratic_sign_tuple_equal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
             _ _ _ H_tuple_eq);
          intros
           (hl,
            ((hna, (hnb, (hnc, (hnd, (hne, (hnf, (hng, hnh))))))),
             (hp1, hp2)));
          do 10
           match goal with
           | id1:(?X1 = ?X2) |- ?X3 => try rewrite id1; clear id1
           end ].
      right; split;
       repeat
        match goal with
        | id1:(?X1 = 0%Z) |- ?X2 => rewrite id1; clear id1
        end; repeat rewrite Zplus_0_r;
       [ apply outside_square_2
       | apply Zsgn_10; apply sym_eq; apply Z.opp_inj ]; 
       assumption.
      (* ~`o1 < (-2)` /\ ~`2 < o1` *)
      intros Ho2' Ho2.
      generalize
       (Qquadratic_sign_nR_nR_7 a b c d e f g h (nR xs) xs 
          (nR ys) ys H_Qquadratic_sg_denom_nonzero
          (Qquadratic_signok_1 _ _ _ _ _ _ H_Qquadratic_sg_denom_nonzero)
          (refl_equal _) (refl_equal _)).
      intros H1.
      assert
       (H_tuple_eq :
        Qquadratic_sign a (a + b) (a + c) (a + b + c + d) e 
          (e + f) (e + g) (e + f + g + h) xs ys
          (Qquadratic_signok_1 e f g h xs ys H_Qquadratic_sg_denom_nonzero) =
        (1%Z, (na, (nb, (nc, nd)), (ne, (nf, (ng, nh))), (np1, np2))));
       [ apply
          trans_eq
           with
             (Qquadratic_sign a b c d e f g h (nR xs) 
                (nR ys) H_Qquadratic_sg_denom_nonzero);
          [ apply sym_eq; apply H1; repeat split | idtac ]
       | apply
          (Qquadratic_sign_pos_1 a (a + b)%Z (a + c)%Z 
             (a + b + c + d)%Z e (e + f)%Z (e + g)%Z 
             (e + f + g + h)%Z xs ys
             (Qquadratic_signok_1 e f g h xs ys H_Qquadratic_sg_denom_nonzero)
             na nb nc nd ne nf ng nh np1 np2) ]; assumption.
    (* ~(`f = 0`/\`g = 0`/\`h = 0`) *)
    intro Hfgh'.
    case (inside_square_1_dec_inf o1 o2).    
     (* (inside_square_1 o1 o2) *)
     intro H_inside_1.
     generalize
      (Qquadratic_sign_nRdL_nRdL_8 a b c d e f g h 
         (nR xs) (nR ys) H_Qquadratic_sg_denom_nonzero).
     intros H1.
     assert
      (H_tuple_eq :
       (1%Z, (na, (nb, (nc, nd)), (ne, (nf, (ng, nh))), (np1, np2))) =
       (1%Z, (a, (b, (c, d)), (e, (f, (g, h))), (nR xs, nR ys))));
      [ apply
         trans_eq
          with
            (Qquadratic_sign a b c d e f g h (nR xs) 
               (nR ys) H_Qquadratic_sg_denom_nonzero);
         [ apply sym_eq | apply H1; discriminate || (repeat split) ];
         assumption
      | generalize
         (Qquadratic_sign_tuple_equal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
            _ _ H_tuple_eq);
         intros
          (hl,
           ((hna, (hnb, (hnc, (hnd, (hne, (hnf, (hng, hnh))))))),
            (hp1, hp2)));
         do 10
          match goal with
          | id1:(?X1 = ?X2) |- ?X3 => try rewrite id1; clear id1
          end ].
     case (inside_square_1_inf _ _ H_inside_1); intros (Ho1, Ho2);
      [ left; split; apply outside_square_1
      | right; split; apply outside_square_2 ]; assumption.
     (* ~(inside_square_1 o1 o2) *)    
     intro H_inside_1'.
     case (inside_square_2_dec_inf o1 o2).    
      (* (inside_square_2 o1 o2) *)
      intro H_inside_2.
      generalize
       (Qquadratic_sign_nRdL_nRdL_9 a b c d e f g h 
          (nR xs) (nR ys) H_Qquadratic_sg_denom_nonzero).
      intros H1.
      apply False_rec.
      assert
       (H_tuple_eq :
        (1%Z, (na, (nb, (nc, nd)), (ne, (nf, (ng, nh))), (np1, np2))) =
        ((-1)%Z, (a, (b, (c, d)), (e, (f, (g, h))), (nR xs, nR ys))));
       [ apply
          trans_eq
           with
             (Qquadratic_sign a b c d e f g h (nR xs) 
                (nR ys) H_Qquadratic_sg_denom_nonzero);
          [ apply sym_eq | apply H1; discriminate || (repeat split) ];
          assumption
       | generalize
          (Qquadratic_sign_tuple_equal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
             _ _ _ H_tuple_eq);
          intros
           (hl,
            ((hna, (hnb, (hnc, (hnd, (hne, (hnf, (hng, hnh))))))),
             (hp1, hp2)));
          do 10
           match goal with
           | id1:(?X1 = ?X2) |- ?X3 => try rewrite id1; clear id1
           end ].
      discriminate hl.
      (*  ~(inside_square_1 o1 o2)/\~(inside_square_2 o1 o2) *)
      intros H_inside_2'. 
      generalize
       (Qquadratic_sign_nR_nR_10 a b c d e f g h (nR xs) xs 
          (nR ys) ys H_Qquadratic_sg_denom_nonzero
          (Qquadratic_signok_1 _ _ _ _ _ _ H_Qquadratic_sg_denom_nonzero)
          (refl_equal _) (refl_equal _)).
      intros H1.
      assert
       (H_tuple_eq :
        Qquadratic_sign a (a + b) (a + c) (a + b + c + d) e 
          (e + f) (e + g) (e + f + g + h) xs ys
          (Qquadratic_signok_1 e f g h xs ys H_Qquadratic_sg_denom_nonzero) =
        (1%Z, (na, (nb, (nc, nd)), (ne, (nf, (ng, nh))), (np1, np2))));
       [ apply
          trans_eq
           with
             (Qquadratic_sign a b c d e f g h (nR xs) 
                (nR ys) H_Qquadratic_sg_denom_nonzero);
          [ apply sym_eq; apply H1; repeat split | idtac ]
       | apply
          (Qquadratic_sign_pos_1 a (a + b)%Z (a + c)%Z 
             (a + b + c + d)%Z e (e + f)%Z (e + g)%Z 
             (e + f + g + h)%Z xs ys
             (Qquadratic_signok_1 e f g h xs ys H_Qquadratic_sg_denom_nonzero)
             na nb nc nd ne nf ng nh np1 np2) ]; assumption.

  (*  p1 = (nR xs) & p2 = (dL ys) *)
  case (three_integers_dec_inf b c d).  
   (* `b = 0`/\`c = 0`/\`d = 0` *)
   intros (Hb, (Hc, Hd)).
   (* Intros [Hb [Hc] Hd]. *)
   case (three_integers_dec_inf f g h).   
    (* `f = 0`/\`g = 0`/\`h = 0` *)
    intros (Hf, (Hg, Hh)).
    generalize
     (Qquadratic_sign_nRdL_nRdL_1 a b c d e f g h (nR xs) 
        (dL ys) H_Qquadratic_sg_denom_nonzero).
    intros H1.
    assert
     (H_tuple_eq :
      (1%Z, (na, (nb, (nc, nd)), (ne, (nf, (ng, nh))), (np1, np2))) =
      ((Z.sgn a * Z.sgn e)%Z,
      (a, (b, (c, d)), (e, (f, (g, h))), (nR xs, dL ys))));
     [ apply
        trans_eq
         with
           (Qquadratic_sign a b c d e f g h (nR xs) 
              (dL ys) H_Qquadratic_sg_denom_nonzero);
        [ apply sym_eq | apply H1; discriminate || (repeat split) ];
        assumption
     | generalize
        (Qquadratic_sign_tuple_equal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
           _ _ H_tuple_eq);
        intros
         (hl,
          ((hna, (hnb, (hnc, (hnd, (hne, (hnf, (hng, hnh))))))),
           (hp1,
            hp2)));
        do 10
         match goal with
         | id1:(?X1 = ?X2) |- ?X3 => try rewrite id1; clear id1
         end ].
    rewrite <- Zsgn_15 in hl.
    case (Zsgn_16 _ _ (sym_eq hl)); intros (Ha, He); [ left | right ];
     repeat split;
     repeat
      match goal with
      | id1:(?X1 = 0%Z) |- ?X2 => rewrite id1; clear id1
      end; repeat rewrite Zplus_0_r; assumption.
    (* ~(`f = 0`/\`g = 0`/\`h = 0`) *)
    intros H_fgh'.
    case (Z_lt_dec 2 o2).
     (*  `2 < o2` *)
     intro Ho2.
     generalize
      (Qquadratic_sign_nRdL_nRdL_2 a b c d e f g h 
         (nR xs) (dL ys) H_Qquadratic_sg_denom_nonzero).
     intros H1.
     assert
      (H_tuple_eq :
       (1%Z, (na, (nb, (nc, nd)), (ne, (nf, (ng, nh))), (np1, np2))) =
       (Z.sgn a, (a, (b, (c, d)), (e, (f, (g, h))), (nR xs, dL ys))));
      [ apply
         trans_eq
          with
            (Qquadratic_sign a b c d e f g h (nR xs) 
               (dL ys) H_Qquadratic_sg_denom_nonzero);
         [ apply sym_eq | apply H1; discriminate || (repeat split) ];
         assumption
      | generalize
         (Qquadratic_sign_tuple_equal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
            _ _ H_tuple_eq);
         intros
          (hl,
           ((hna, (hnb, (hnc, (hnd, (hne, (hnf, (hng, hnh))))))),
           (hp1,
            hp2)));
         do 10
          match goal with
          | id1:(?X1 = ?X2) |- ?X3 => try rewrite id1; clear id1
          end ].
     left; split;
      repeat
       match goal with
       | id1:(?X1 = 0%Z) |- ?X2 => rewrite id1; clear id1
       end; repeat rewrite Zplus_0_r;
      [ apply Zsgn_9; apply sym_eq; assumption
      | apply outside_square_1; assumption ].
     (*  ~`2 < o2` *)
     case (Z_lt_dec o2 (-2)).     
     (* `(-2) < o2` *)
      intros Ho2' Ho2.
      generalize
       (Qquadratic_sign_nRdL_nRdL_3 a b c d e f g h 
          (nR xs) (dL ys) H_Qquadratic_sg_denom_nonzero).
      intros H1.
      assert
       (H_tuple_eq :
        (1%Z, (na, (nb, (nc, nd)), (ne, (nf, (ng, nh))), (np1, np2))) =
        ((- Z.sgn a)%Z, (a, (b, (c, d)), (e, (f, (g, h))), (nR xs, dL ys))));
       [ apply
          trans_eq
           with
             (Qquadratic_sign a b c d e f g h (nR xs) 
                (dL ys) H_Qquadratic_sg_denom_nonzero);
          [ apply sym_eq | apply H1; discriminate || (repeat split) ];
          assumption
       | generalize
          (Qquadratic_sign_tuple_equal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
             _ _ _ H_tuple_eq);
          intros
           (hl,
            ((hna, (hnb, (hnc, (hnd, (hne, (hnf, (hng, hnh))))))),
            (hp1,
             hp2)));
          do 10
           match goal with
           | id1:(?X1 = ?X2) |- ?X3 => try rewrite id1; clear id1
           end ].
      right; split;
       repeat
        match goal with
        | id1:(?X1 = 0%Z) |- ?X2 => rewrite id1; clear id1
        end; repeat rewrite Zplus_0_r;
       [ apply Zsgn_10; apply sym_eq; apply Z.opp_inj; assumption
       | apply outside_square_2; assumption ]. 
     (* ~`o1 < (-2)` /\ ~`2 < o1` *)
      intros Ho2' Ho2.
      generalize
       (Qquadratic_sign_nR_dL_4 a b c d e f g h (nR xs) xs 
          (dL ys) ys H_Qquadratic_sg_denom_nonzero
          (Qquadratic_signok_2 _ _ _ _ _ _ H_Qquadratic_sg_denom_nonzero)
          (refl_equal _) (refl_equal _)).
      intros H1.
      assert
       (H_tuple_eq :
        Qquadratic_sign (a + b) b (a + b + c + d) (b + d) 
          (e + f) f (e + f + g + h) (f + h) xs ys
          (Qquadratic_signok_2 e f g h xs ys H_Qquadratic_sg_denom_nonzero) =
        (1%Z, (na, (nb, (nc, nd)), (ne, (nf, (ng, nh))), (np1, np2))));
       [ apply
          trans_eq
           with
             (Qquadratic_sign a b c d e f g h (nR xs) 
                (dL ys) H_Qquadratic_sg_denom_nonzero);
          [ apply sym_eq; apply H1; repeat split | idtac ]
       | apply
          (Qquadratic_sign_pos_1 (a + b)%Z b (a + b + c + d)%Z 
             (b + d)%Z (e + f)%Z f (e + f + g + h)%Z 
             (f + h)%Z xs ys
             (Qquadratic_signok_2 e f g h xs ys H_Qquadratic_sg_denom_nonzero)
             na nb nc nd ne nf ng nh np1 np2) ]; assumption.
   (* ~ `b = 0`/\`c = 0`/\`d = 0` *)
   intros Hbcd'.
   (* Intros [Hb [Hc] Hd]. *)
   case (three_integers_dec_inf f g h).   
    (* `f = 0`/\`g = 0`/\`h = 0` *)
    intros (Hf, (Hg, Hh)).
    case (Z_lt_dec 2 o1).
     (*  `2 < o1` *)
     intro Ho1.
     generalize
      (Qquadratic_sign_nRdL_nRdL_5 a b c d e f g h 
         (nR xs) (dL ys) H_Qquadratic_sg_denom_nonzero).
     intros H1.
     assert
      (H_tuple_eq :
       (1%Z, (na, (nb, (nc, nd)), (ne, (nf, (ng, nh))), (np1, np2))) =
       (Z.sgn e, (a, (b, (c, d)), (e, (f, (g, h))), (nR xs, dL ys))));
      [ apply
         trans_eq
          with
            (Qquadratic_sign a b c d e f g h (nR xs) 
               (dL ys) H_Qquadratic_sg_denom_nonzero);
         [ apply sym_eq | apply H1; discriminate || (repeat split) ];
         assumption
      | generalize
         (Qquadratic_sign_tuple_equal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
            _ _ H_tuple_eq);
         intros
          (hl,
           ((hna, (hnb, (hnc, (hnd, (hne, (hnf, (hng, hnh))))))),
           (hp1,
            hp2)));
         do 10
          match goal with
          | id1:(?X1 = ?X2) |- ?X3 => try rewrite id1; clear id1
          end ].
     left; split;
      repeat
       match goal with
       | id1:(?X1 = 0%Z) |- ?X2 => rewrite id1; clear id1
       end; repeat rewrite Zplus_0_r;
      [ apply outside_square_1 | apply Zsgn_9; apply sym_eq ]; 
      assumption.
     (*  ~`2 < o1` *)
     case (Z_lt_dec o1 (-2)).
      (* `(-2) < o1` *)
      intros Ho1' Ho1.
      generalize
       (Qquadratic_sign_nRdL_nRdL_6 a b c d e f g h 
          (nR xs) (dL ys) H_Qquadratic_sg_denom_nonzero).
      intros H1.
      assert
       (H_tuple_eq :
        (1%Z, (na, (nb, (nc, nd)), (ne, (nf, (ng, nh))), (np1, np2))) =
        ((- Z.sgn e)%Z, (a, (b, (c, d)), (e, (f, (g, h))), (nR xs, dL ys))));
       [ apply
          trans_eq
           with
             (Qquadratic_sign a b c d e f g h (nR xs) 
                (dL ys) H_Qquadratic_sg_denom_nonzero);
          [ apply sym_eq | apply H1; discriminate || (repeat split) ];
          assumption
       | generalize
          (Qquadratic_sign_tuple_equal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
             _ _ _ H_tuple_eq);
          intros
           (hl,
            ((hna, (hnb, (hnc, (hnd, (hne, (hnf, (hng, hnh))))))),
            (hp1,
             hp2)));
          do 10
           match goal with
           | id1:(?X1 = ?X2) |- ?X3 => try rewrite id1; clear id1
           end ].
      right; split;
       repeat
        match goal with
        | id1:(?X1 = 0%Z) |- ?X2 => rewrite id1; clear id1
        end; repeat rewrite Zplus_0_r;
       [ apply outside_square_2
       | apply Zsgn_10; apply sym_eq; apply Z.opp_inj ]; 
       assumption.
      (* ~`o1 < (-2)` /\ ~`2 < o1` *)
      intros Ho2' Ho2.
      generalize
       (Qquadratic_sign_nR_dL_7 a b c d e f g h (nR xs) xs 
          (dL ys) ys H_Qquadratic_sg_denom_nonzero
          (Qquadratic_signok_2 _ _ _ _ _ _ H_Qquadratic_sg_denom_nonzero)
          (refl_equal _) (refl_equal _)).
      intros H1.
      assert
       (H_tuple_eq :
        Qquadratic_sign (a + b) b (a + b + c + d) (b + d) 
          (e + f) f (e + f + g + h) (f + h) xs ys
          (Qquadratic_signok_2 e f g h xs ys H_Qquadratic_sg_denom_nonzero) =
        (1%Z, (na, (nb, (nc, nd)), (ne, (nf, (ng, nh))), (np1, np2))));
       [ apply
          trans_eq
           with
             (Qquadratic_sign a b c d e f g h (nR xs) 
                (dL ys) H_Qquadratic_sg_denom_nonzero);
          [ apply sym_eq; apply H1; repeat split | idtac ]
       | apply
          (Qquadratic_sign_pos_1 (a + b)%Z b (a + b + c + d)%Z 
             (b + d)%Z (e + f)%Z f (e + f + g + h)%Z 
             (f + h)%Z xs ys
             (Qquadratic_signok_2 e f g h xs ys H_Qquadratic_sg_denom_nonzero)
             na nb nc nd ne nf ng nh np1 np2) ]; assumption.
    (* ~(`f = 0`/\`g = 0`/\`h = 0`) *)
    intro Hfgh'.
    case (inside_square_1_dec_inf o1 o2).    
     (* (inside_square_1 o1 o2) *)
     intro H_inside_1.
     generalize
      (Qquadratic_sign_nRdL_nRdL_8 a b c d e f g h 
         (nR xs) (dL ys) H_Qquadratic_sg_denom_nonzero).
     intros H1.
     assert
      (H_tuple_eq :
       (1%Z, (na, (nb, (nc, nd)), (ne, (nf, (ng, nh))), (np1, np2))) =
       (1%Z, (a, (b, (c, d)), (e, (f, (g, h))), (nR xs, dL ys))));
      [ apply
         trans_eq
          with
            (Qquadratic_sign a b c d e f g h (nR xs) 
               (dL ys) H_Qquadratic_sg_denom_nonzero);
         [ apply sym_eq | apply H1; discriminate || (repeat split) ];
         assumption
      | generalize
         (Qquadratic_sign_tuple_equal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
            _ _ H_tuple_eq);
         intros
          (hl,
           ((hna, (hnb, (hnc, (hnd, (hne, (hnf, (hng, hnh))))))),
           (hp1,
            hp2)));
         do 10
          match goal with
          | id1:(?X1 = ?X2) |- ?X3 => try rewrite id1; clear id1
          end ].
     case (inside_square_1_inf _ _ H_inside_1); intros (Ho1, Ho2);
      [ left; split; apply outside_square_1
      | right; split; apply outside_square_2 ]; assumption.
     (* ~(inside_square_1 o1 o2) *)    
     intro H_inside_1'.
     case (inside_square_2_dec_inf o1 o2).    
      (* (inside_square_2 o1 o2) *)
      intro H_inside_2.
      generalize
       (Qquadratic_sign_nRdL_nRdL_9 a b c d e f g h 
          (nR xs) (dL ys) H_Qquadratic_sg_denom_nonzero).
      intros H1.
      apply False_rec.
      assert
       (H_tuple_eq :
        (1%Z, (na, (nb, (nc, nd)), (ne, (nf, (ng, nh))), (np1, np2))) =
        ((-1)%Z, (a, (b, (c, d)), (e, (f, (g, h))), (nR xs, dL ys))));
       [ apply
          trans_eq
           with
             (Qquadratic_sign a b c d e f g h (nR xs) 
                (dL ys) H_Qquadratic_sg_denom_nonzero);
          [ apply sym_eq | apply H1; discriminate || (repeat split) ];
          assumption
       | generalize
          (Qquadratic_sign_tuple_equal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
             _ _ _ H_tuple_eq);
          intros
           (hl,
            ((hna, (hnb, (hnc, (hnd, (hne, (hnf, (hng, hnh))))))),
            (hp1,
             hp2)));
          do 10
           match goal with
           | id1:(?X1 = ?X2) |- ?X3 => try rewrite id1; clear id1
           end ].
      discriminate hl.
      (*  ~(inside_square_1 o1 o2)/\~(inside_square_2 o1 o2) *)
      intros H_inside_2'. 
      generalize
       (Qquadratic_sign_nR_dL_10 a b c d e f g h (nR xs) xs 
          (dL ys) ys H_Qquadratic_sg_denom_nonzero
          (Qquadratic_signok_2 _ _ _ _ _ _ H_Qquadratic_sg_denom_nonzero)
          (refl_equal _) (refl_equal _)).
      intros H1.
      assert
       (H_tuple_eq :
        Qquadratic_sign (a + b) b (a + b + c + d) (b + d) 
          (e + f) f (e + f + g + h) (f + h) xs ys
          (Qquadratic_signok_2 e f g h xs ys H_Qquadratic_sg_denom_nonzero) =
        (1%Z, (na, (nb, (nc, nd)), (ne, (nf, (ng, nh))), (np1, np2))));
       [ apply
          trans_eq
           with
             (Qquadratic_sign a b c d e f g h (nR xs) 
                (dL ys) H_Qquadratic_sg_denom_nonzero);
          [ apply sym_eq; apply H1; repeat split | idtac ]
       | apply
          (Qquadratic_sign_pos_1 (a + b)%Z b (a + b + c + d)%Z 
             (b + d)%Z (e + f)%Z f (e + f + g + h)%Z 
             (f + h)%Z xs ys
             (Qquadratic_signok_2 e f g h xs ys H_Qquadratic_sg_denom_nonzero)
             na nb nc nd ne nf ng nh np1 np2) ]; assumption.

  (*  p1 = (nR xs) & p2 = One *)
  generalize (Qquadratic_signok_0' _ _ _ _ _ H_Qquadratic_sg_denom_nonzero).
  intros H_Qhomographic_sg_denom_nonzero.
  set
   (L3 :=
    Qhomographic_sign (a + b) (c + d) (e + f) (g + h) 
      (nR xs) H_Qhomographic_sg_denom_nonzero) in *.
  set (l1 := fst L3) in *.
  set (l2 := fst (snd L3)) in *.
  set (l3 := snd (snd L3)) in *.
  set (na_ := fst l2) in *.
  set (nb_ := fst (snd l2)) in *.
  set (nc_ := fst (snd (snd l2))) in *.
  set (nd_ := snd (snd (snd l2))) in *.
  generalize
   (Qquadratic_sign_nRdL_One a b c d e f g h (nR xs) One
      H_Qquadratic_sg_denom_nonzero l1 na_ nb_ nc_ nd_ l3
      H_Qhomographic_sg_denom_nonzero); intros H1.
  assert
   (H_tuple_eq :
    (1%Z, (na, (nb, (nc, nd)), (ne, (nf, (ng, nh))), (np1, np2))) =
    (l1, (0%Z, (na_, (0%Z, nb_)), (0%Z, (nc_, (0%Z, nd_))), (l3, One))));
   [ apply
      trans_eq
       with
         (Qquadratic_sign a b c d e f g h (nR xs) One
            H_Qquadratic_sg_denom_nonzero);
      [ apply sym_eq; assumption
      | apply H1; fold L3 in |- *; repeat (apply pair_2; try reflexivity);
         discriminate || reflexivity ]
   | generalize
      (Qquadratic_sign_tuple_equal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
         _ H_tuple_eq);
      intros
       (hl,
        ((hna, (hnb, (hnc, (hnd, (hne, (hnf, (hng, hnh))))))),
        (hp1,
         hp2)));
      do 10
       match goal with
       | id1:(?X1 = ?X2) |- ?X3 => try rewrite id1; clear id1
       end; repeat rewrite Zplus_0_l; repeat rewrite Zplus_0_r ];
   apply
    (sg_pos_1 (a + b) (c + d) (e + f) (g + h) (nR xs)
       H_Qhomographic_sg_denom_nonzero na_ nb_ nc_ nd_ l3); 
   rewrite hl; fold L3 in |- *; repeat (apply pair_2; try reflexivity);
   discriminate || reflexivity.

 (* p1 = (dL xs) *)
 destruct p2 as [ys| ys| ].
  (*  p1 = (dL xs) & p2 = (nR ys) *)
  case (three_integers_dec_inf b c d).  
   (* `b = 0`/\`c = 0`/\`d = 0` *)
   intros (Hb, (Hc, Hd)).
   (* Intros [Hb [Hc] Hd]. *)
   case (three_integers_dec_inf f g h).   
    (* `f = 0`/\`g = 0`/\`h = 0` *)
    intros (Hf, (Hg, Hh)).
    generalize
     (Qquadratic_sign_nRdL_nRdL_1 a b c d e f g h (dL xs) 
        (nR ys) H_Qquadratic_sg_denom_nonzero).
    intros H1.
    assert
     (H_tuple_eq :
      (1%Z, (na, (nb, (nc, nd)), (ne, (nf, (ng, nh))), (np1, np2))) =
      ((Z.sgn a * Z.sgn e)%Z,
      (a, (b, (c, d)), (e, (f, (g, h))), (dL xs, nR ys))));
     [ apply
        trans_eq
         with
           (Qquadratic_sign a b c d e f g h (dL xs) 
              (nR ys) H_Qquadratic_sg_denom_nonzero);
        [ apply sym_eq | apply H1; discriminate || (repeat split) ];
        assumption
     | generalize
        (Qquadratic_sign_tuple_equal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
           _ _ H_tuple_eq);
        intros
         (hl,
          ((hna, (hnb, (hnc, (hnd, (hne, (hnf, (hng, hnh))))))),
          (hp1,
           hp2)));
        do 10
         match goal with
         | id1:(?X1 = ?X2) |- ?X3 => try rewrite id1; clear id1
         end ].
    rewrite <- Zsgn_15 in hl.
    case (Zsgn_16 _ _ (sym_eq hl)); intros (Ha, He); [ left | right ];
     repeat split;
     repeat
      match goal with
      | id1:(?X1 = 0%Z) |- ?X2 => rewrite id1; clear id1
      end; repeat rewrite Zplus_0_r; assumption.
    (* ~(`f = 0`/\`g = 0`/\`h = 0`) *)
    intros H_fgh'.
    case (Z_lt_dec 2 o2).
     (*  `2 < o2` *)
     intro Ho2.
     generalize
      (Qquadratic_sign_nRdL_nRdL_2 a b c d e f g h 
         (dL xs) (nR ys) H_Qquadratic_sg_denom_nonzero).
     intros H1.
     assert
      (H_tuple_eq :
       (1%Z, (na, (nb, (nc, nd)), (ne, (nf, (ng, nh))), (np1, np2))) =
       (Z.sgn a, (a, (b, (c, d)), (e, (f, (g, h))), (dL xs, nR ys))));
      [ apply
         trans_eq
          with
            (Qquadratic_sign a b c d e f g h (dL xs) 
               (nR ys) H_Qquadratic_sg_denom_nonzero);
         [ apply sym_eq | apply H1; discriminate || (repeat split) ];
         assumption
      | generalize
         (Qquadratic_sign_tuple_equal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
            _ _ H_tuple_eq);
         intros
          (hl,
           ((hna, (hnb, (hnc, (hnd, (hne, (hnf, (hng, hnh))))))),
           (hp1,
            hp2)));
         do 10
          match goal with
          | id1:(?X1 = ?X2) |- ?X3 => try rewrite id1; clear id1
          end ].
     left; split;
      repeat
       match goal with
       | id1:(?X1 = 0%Z) |- ?X2 => rewrite id1; clear id1
       end; repeat rewrite Zplus_0_r;
      [ apply Zsgn_9; apply sym_eq; assumption
      | apply outside_square_1; assumption ].
     (*  ~`2 < o2` *)
     case (Z_lt_dec o2 (-2)).     
     (* `(-2) < o2` *)
      intros Ho2' Ho2.
      generalize
       (Qquadratic_sign_nRdL_nRdL_3 a b c d e f g h 
          (dL xs) (nR ys) H_Qquadratic_sg_denom_nonzero).
      intros H1.
      assert
       (H_tuple_eq :
        (1%Z, (na, (nb, (nc, nd)), (ne, (nf, (ng, nh))), (np1, np2))) =
        ((- Z.sgn a)%Z, (a, (b, (c, d)), (e, (f, (g, h))), (dL xs, nR ys))));
       [ apply
          trans_eq
           with
             (Qquadratic_sign a b c d e f g h (dL xs) 
                (nR ys) H_Qquadratic_sg_denom_nonzero);
          [ apply sym_eq | apply H1; discriminate || (repeat split) ];
          assumption
       | generalize
          (Qquadratic_sign_tuple_equal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
             _ _ _ H_tuple_eq);
          intros
           (hl,
            ((hna, (hnb, (hnc, (hnd, (hne, (hnf, (hng, hnh))))))),
            (hp1,
             hp2)));
          do 10
           match goal with
           | id1:(?X1 = ?X2) |- ?X3 => try rewrite id1; clear id1
           end ].
      right; split;
       repeat
        match goal with
        | id1:(?X1 = 0%Z) |- ?X2 => rewrite id1; clear id1
        end; repeat rewrite Zplus_0_r;
       [ apply Zsgn_10; apply sym_eq; apply Z.opp_inj; assumption
       | apply outside_square_2; assumption ]. 
     (* ~`o1 < (-2)` /\ ~`2 < o1` *)
      intros Ho2' Ho2.
      generalize
       (Qquadratic_sign_dL_nR_4 a b c d e f g h (dL xs) xs 
          (nR ys) ys H_Qquadratic_sg_denom_nonzero
          (Qquadratic_signok_3 _ _ _ _ _ _ H_Qquadratic_sg_denom_nonzero)
          (refl_equal _) (refl_equal _)).
      intros H1.
      assert
       (H_tuple_eq :
        Qquadratic_sign (a + c) (a + b + c + d) c (c + d) 
          (e + g) (e + f + g + h) g (g + h) xs ys
          (Qquadratic_signok_3 e f g h xs ys H_Qquadratic_sg_denom_nonzero) =
        (1%Z, (na, (nb, (nc, nd)), (ne, (nf, (ng, nh))), (np1, np2))));
       [ apply
          trans_eq
           with
             (Qquadratic_sign a b c d e f g h (dL xs) 
                (nR ys) H_Qquadratic_sg_denom_nonzero);
          [ apply sym_eq; apply H1; repeat split | idtac ]
       | apply
          (Qquadratic_sign_pos_1 (a + c)%Z (a + b + c + d)%Z c 
             (c + d)%Z (e + g)%Z (e + f + g + h)%Z g 
             (g + h)%Z xs ys
             (Qquadratic_signok_3 e f g h xs ys H_Qquadratic_sg_denom_nonzero)
             na nb nc nd ne nf ng nh np1 np2) ]; assumption.
   (* ~ `b = 0`/\`c = 0`/\`d = 0` *)
   intros Hbcd'.
   (* Intros [Hb [Hc] Hd]. *)
   case (three_integers_dec_inf f g h).   
    (* `f = 0`/\`g = 0`/\`h = 0` *)
    intros (Hf, (Hg, Hh)).
    case (Z_lt_dec 2 o1).
     (*  `2 < o1` *)
     intro Ho1.
     generalize
      (Qquadratic_sign_nRdL_nRdL_5 a b c d e f g h 
         (dL xs) (nR ys) H_Qquadratic_sg_denom_nonzero).
     intros H1.
     assert
      (H_tuple_eq :
       (1%Z, (na, (nb, (nc, nd)), (ne, (nf, (ng, nh))), (np1, np2))) =
       (Z.sgn e, (a, (b, (c, d)), (e, (f, (g, h))), (dL xs, nR ys))));
      [ apply
         trans_eq
          with
            (Qquadratic_sign a b c d e f g h (dL xs) 
               (nR ys) H_Qquadratic_sg_denom_nonzero);
         [ apply sym_eq | apply H1; discriminate || (repeat split) ];
         assumption
      | generalize
         (Qquadratic_sign_tuple_equal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
            _ _ H_tuple_eq);
         intros
          (hl,
           ((hna, (hnb, (hnc, (hnd, (hne, (hnf, (hng, hnh))))))),
           (hp1,
            hp2)));
         do 10
          match goal with
          | id1:(?X1 = ?X2) |- ?X3 => try rewrite id1; clear id1
          end ].
     left; split;
      repeat
       match goal with
       | id1:(?X1 = 0%Z) |- ?X2 => rewrite id1; clear id1
       end; repeat rewrite Zplus_0_r;
      [ apply outside_square_1 | apply Zsgn_9; apply sym_eq ]; 
      assumption.
     (*  ~`2 < o1` *)
     case (Z_lt_dec o1 (-2)).
      (* `(-2) < o1` *)
      intros Ho1' Ho1.
      generalize
       (Qquadratic_sign_nRdL_nRdL_6 a b c d e f g h 
          (dL xs) (nR ys) H_Qquadratic_sg_denom_nonzero).
      intros H1.
      assert
       (H_tuple_eq :
        (1%Z, (na, (nb, (nc, nd)), (ne, (nf, (ng, nh))), (np1, np2))) =
        ((- Z.sgn e)%Z, (a, (b, (c, d)), (e, (f, (g, h))), (dL xs, nR ys))));
       [ apply
          trans_eq
           with
             (Qquadratic_sign a b c d e f g h (dL xs) 
                (nR ys) H_Qquadratic_sg_denom_nonzero);
          [ apply sym_eq | apply H1; discriminate || (repeat split) ];
          assumption
       | generalize
          (Qquadratic_sign_tuple_equal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
             _ _ _ H_tuple_eq);
          intros
           (hl,
            ((hna, (hnb, (hnc, (hnd, (hne, (hnf, (hng, hnh))))))),
            (hp1,
             hp2)));
          do 10
           match goal with
           | id1:(?X1 = ?X2) |- ?X3 => try rewrite id1; clear id1
           end ].
      right; split;
       repeat
        match goal with
        | id1:(?X1 = 0%Z) |- ?X2 => rewrite id1; clear id1
        end; repeat rewrite Zplus_0_r;
       [ apply outside_square_2
       | apply Zsgn_10; apply sym_eq; apply Z.opp_inj ]; 
       assumption.
      (* ~`o1 < (-2)` /\ ~`2 < o1` *)
      intros Ho2' Ho2.
      generalize
       (Qquadratic_sign_dL_nR_7 a b c d e f g h (dL xs) xs 
          (nR ys) ys H_Qquadratic_sg_denom_nonzero
          (Qquadratic_signok_3 _ _ _ _ _ _ H_Qquadratic_sg_denom_nonzero)
          (refl_equal _) (refl_equal _)).
      intros H1.
      assert
       (H_tuple_eq :
        Qquadratic_sign (a + c) (a + b + c + d) c (c + d) 
          (e + g) (e + f + g + h) g (g + h) xs ys
          (Qquadratic_signok_3 e f g h xs ys H_Qquadratic_sg_denom_nonzero) =
        (1%Z, (na, (nb, (nc, nd)), (ne, (nf, (ng, nh))), (np1, np2))));
       [ apply
          trans_eq
           with
             (Qquadratic_sign a b c d e f g h (dL xs) 
                (nR ys) H_Qquadratic_sg_denom_nonzero);
          [ apply sym_eq; apply H1; repeat split | idtac ]
       | apply
          (Qquadratic_sign_pos_1 (a + c)%Z (a + b + c + d)%Z c 
             (c + d)%Z (e + g)%Z (e + f + g + h)%Z g 
             (g + h)%Z xs ys
             (Qquadratic_signok_3 e f g h xs ys H_Qquadratic_sg_denom_nonzero)
             na nb nc nd ne nf ng nh np1 np2) ]; assumption.
    (* ~(`f = 0`/\`g = 0`/\`h = 0`) *)
    intro Hfgh'.
    case (inside_square_1_dec_inf o1 o2).    
     (* (inside_square_1 o1 o2) *)
     intro H_inside_1.
     generalize
      (Qquadratic_sign_nRdL_nRdL_8 a b c d e f g h 
         (dL xs) (nR ys) H_Qquadratic_sg_denom_nonzero).
     intros H1.
     assert
      (H_tuple_eq :
       (1%Z, (na, (nb, (nc, nd)), (ne, (nf, (ng, nh))), (np1, np2))) =
       (1%Z, (a, (b, (c, d)), (e, (f, (g, h))), (dL xs, nR ys))));
      [ apply
         trans_eq
          with
            (Qquadratic_sign a b c d e f g h (dL xs) 
               (nR ys) H_Qquadratic_sg_denom_nonzero);
         [ apply sym_eq | apply H1; discriminate || (repeat split) ];
         assumption
      | generalize
         (Qquadratic_sign_tuple_equal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
            _ _ H_tuple_eq);
         intros
          (hl,
           ((hna, (hnb, (hnc, (hnd, (hne, (hnf, (hng, hnh))))))),
           (hp1,
            hp2)));
         do 10
          match goal with
          | id1:(?X1 = ?X2) |- ?X3 => try rewrite id1; clear id1
          end ].
     case (inside_square_1_inf _ _ H_inside_1); intros (Ho1, Ho2);
      [ left; split; apply outside_square_1
      | right; split; apply outside_square_2 ]; assumption.
     (* ~(inside_square_1 o1 o2) *)    
     intro H_inside_1'.
     case (inside_square_2_dec_inf o1 o2).    
      (* (inside_square_2 o1 o2) *)
      intro H_inside_2.
      generalize
       (Qquadratic_sign_nRdL_nRdL_9 a b c d e f g h 
          (dL xs) (nR ys) H_Qquadratic_sg_denom_nonzero).
      intros H1.
      apply False_rec.
      assert
       (H_tuple_eq :
        (1%Z, (na, (nb, (nc, nd)), (ne, (nf, (ng, nh))), (np1, np2))) =
        ((-1)%Z, (a, (b, (c, d)), (e, (f, (g, h))), (dL xs, nR ys))));
       [ apply
          trans_eq
           with
             (Qquadratic_sign a b c d e f g h (dL xs) 
                (nR ys) H_Qquadratic_sg_denom_nonzero);
          [ apply sym_eq | apply H1; discriminate || (repeat split) ];
          assumption
       | generalize
          (Qquadratic_sign_tuple_equal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
             _ _ _ H_tuple_eq);
          intros
           (hl,
            ((hna, (hnb, (hnc, (hnd, (hne, (hnf, (hng, hnh))))))),
            (hp1,
             hp2)));
          do 10
           match goal with
           | id1:(?X1 = ?X2) |- ?X3 => try rewrite id1; clear id1
           end ].
      discriminate hl.
      (*  ~(inside_square_1 o1 o2)/\~(inside_square_2 o1 o2) *)
      intros H_inside_2'. 
      generalize
       (Qquadratic_sign_dL_nR_10 a b c d e f g h (dL xs) xs 
          (nR ys) ys H_Qquadratic_sg_denom_nonzero
          (Qquadratic_signok_3 _ _ _ _ _ _ H_Qquadratic_sg_denom_nonzero)
          (refl_equal _) (refl_equal _)).
      intros H1.
      assert
       (H_tuple_eq :
        Qquadratic_sign (a + c) (a + b + c + d) c (c + d) 
          (e + g) (e + f + g + h) g (g + h) xs ys
          (Qquadratic_signok_3 e f g h xs ys H_Qquadratic_sg_denom_nonzero) =
        (1%Z, (na, (nb, (nc, nd)), (ne, (nf, (ng, nh))), (np1, np2))));
       [ apply
          trans_eq
           with
             (Qquadratic_sign a b c d e f g h (dL xs) 
                (nR ys) H_Qquadratic_sg_denom_nonzero);
          [ apply sym_eq; apply H1; repeat split | idtac ]
       | apply
          (Qquadratic_sign_pos_1 (a + c)%Z (a + b + c + d)%Z c 
             (c + d)%Z (e + g)%Z (e + f + g + h)%Z g 
             (g + h)%Z xs ys
             (Qquadratic_signok_3 e f g h xs ys H_Qquadratic_sg_denom_nonzero)
             na nb nc nd ne nf ng nh np1 np2) ]; assumption.

  (*  p1 = (dL xs) & p2 = (dL ys) *)
  case (three_integers_dec_inf b c d).  
   (* `b = 0`/\`c = 0`/\`d = 0` *)
   intros (Hb, (Hc, Hd)).
   (* Intros [Hb [Hc] Hd]. *)
   case (three_integers_dec_inf f g h).   
    (* `f = 0`/\`g = 0`/\`h = 0` *)
    intros (Hf, (Hg, Hh)).
    generalize
     (Qquadratic_sign_nRdL_nRdL_1 a b c d e f g h (dL xs) 
        (dL ys) H_Qquadratic_sg_denom_nonzero).
    intros H1.
    assert
     (H_tuple_eq :
      (1%Z, (na, (nb, (nc, nd)), (ne, (nf, (ng, nh))), (np1, np2))) =
      ((Z.sgn a * Z.sgn e)%Z,
      (a, (b, (c, d)), (e, (f, (g, h))), (dL xs, dL ys))));
     [ apply
        trans_eq
         with
           (Qquadratic_sign a b c d e f g h (dL xs) 
              (dL ys) H_Qquadratic_sg_denom_nonzero);
        [ apply sym_eq | apply H1; discriminate || (repeat split) ];
        assumption
     | generalize
        (Qquadratic_sign_tuple_equal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
           _ _ H_tuple_eq);
        intros
         (hl,
          ((hna, (hnb, (hnc, (hnd, (hne, (hnf, (hng, hnh))))))),
          (hp1,
           hp2)));
        do 10
         match goal with
         | id1:(?X1 = ?X2) |- ?X3 => try rewrite id1; clear id1
         end ].
    rewrite <- Zsgn_15 in hl.
    case (Zsgn_16 _ _ (sym_eq hl)); intros (Ha, He); [ left | right ];
     repeat split;
     repeat
      match goal with
      | id1:(?X1 = 0%Z) |- ?X2 => rewrite id1; clear id1
      end; repeat rewrite Zplus_0_r; assumption.
    (* ~(`f = 0`/\`g = 0`/\`h = 0`) *)
    intros H_fgh'.
    case (Z_lt_dec 2 o2).
     (*  `2 < o2` *)
     intro Ho2.
     generalize
      (Qquadratic_sign_nRdL_nRdL_2 a b c d e f g h 
         (dL xs) (dL ys) H_Qquadratic_sg_denom_nonzero).
     intros H1.
     assert
      (H_tuple_eq :
       (1%Z, (na, (nb, (nc, nd)), (ne, (nf, (ng, nh))), (np1, np2))) =
       (Z.sgn a, (a, (b, (c, d)), (e, (f, (g, h))), (dL xs, dL ys))));
      [ apply
         trans_eq
          with
            (Qquadratic_sign a b c d e f g h (dL xs) 
               (dL ys) H_Qquadratic_sg_denom_nonzero);
         [ apply sym_eq | apply H1; discriminate || (repeat split) ];
         assumption
      | generalize
         (Qquadratic_sign_tuple_equal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
            _ _ H_tuple_eq);
         intros
          (hl,
           ((hna, (hnb, (hnc, (hnd, (hne, (hnf, (hng, hnh))))))),
           (hp1,
            hp2)));
         do 10
          match goal with
          | id1:(?X1 = ?X2) |- ?X3 => try rewrite id1; clear id1
          end ].
     left; split;
      repeat
       match goal with
       | id1:(?X1 = 0%Z) |- ?X2 => rewrite id1; clear id1
       end; repeat rewrite Zplus_0_r;
      [ apply Zsgn_9; apply sym_eq; assumption
      | apply outside_square_1; assumption ].
     (*  ~`2 < o2` *)
     case (Z_lt_dec o2 (-2)).     
     (* `(-2) < o2` *)
      intros Ho2' Ho2.
      generalize
       (Qquadratic_sign_nRdL_nRdL_3 a b c d e f g h 
          (dL xs) (dL ys) H_Qquadratic_sg_denom_nonzero).
      intros H1.
      assert
       (H_tuple_eq :
        (1%Z, (na, (nb, (nc, nd)), (ne, (nf, (ng, nh))), (np1, np2))) =
        ((- Z.sgn a)%Z, (a, (b, (c, d)), (e, (f, (g, h))), (dL xs, dL ys))));
       [ apply
          trans_eq
           with
             (Qquadratic_sign a b c d e f g h (dL xs) 
                (dL ys) H_Qquadratic_sg_denom_nonzero);
          [ apply sym_eq | apply H1; discriminate || (repeat split) ];
          assumption
       | generalize
          (Qquadratic_sign_tuple_equal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
             _ _ _ H_tuple_eq);
          intros
           (hl,
            ((hna, (hnb, (hnc, (hnd, (hne, (hnf, (hng, hnh))))))),
            (hp1,
             hp2)));
          do 10
           match goal with
           | id1:(?X1 = ?X2) |- ?X3 => try rewrite id1; clear id1
           end ].
      right; split;
       repeat
        match goal with
        | id1:(?X1 = 0%Z) |- ?X2 => rewrite id1; clear id1
        end; repeat rewrite Zplus_0_r;
       [ apply Zsgn_10; apply sym_eq; apply Z.opp_inj; assumption
       | apply outside_square_2; assumption ]. 
     (* ~`o1 < (-2)` /\ ~`2 < o1` *)
      intros Ho2' Ho2.
      generalize
       (Qquadratic_sign_dL_dL_4 a b c d e f g h (dL xs) xs 
          (dL ys) ys H_Qquadratic_sg_denom_nonzero
          (Qquadratic_signok_4 _ _ _ _ _ _ H_Qquadratic_sg_denom_nonzero)
          (refl_equal _) (refl_equal _)).
      intros H1.
      assert
       (H_tuple_eq :
        Qquadratic_sign (a + b + c + d) (b + d) (c + d) d 
          (e + f + g + h) (f + h) (g + h) h xs ys
          (Qquadratic_signok_4 e f g h xs ys H_Qquadratic_sg_denom_nonzero) =
        (1%Z, (na, (nb, (nc, nd)), (ne, (nf, (ng, nh))), (np1, np2))));
       [ apply
          trans_eq
           with
             (Qquadratic_sign a b c d e f g h (dL xs) 
                (dL ys) H_Qquadratic_sg_denom_nonzero);
          [ apply sym_eq; apply H1; repeat split | idtac ]
       | apply
          (Qquadratic_sign_pos_1 (a + b + c + d)%Z 
             (b + d)%Z (c + d)%Z d (e + f + g + h)%Z 
             (f + h)%Z (g + h)%Z h xs ys
             (Qquadratic_signok_4 e f g h xs ys H_Qquadratic_sg_denom_nonzero)
             na nb nc nd ne nf ng nh np1 np2) ]; assumption.
   (* ~ `b = 0`/\`c = 0`/\`d = 0` *)
   intros Hbcd'.
   (* Intros [Hb [Hc] Hd]. *)
   case (three_integers_dec_inf f g h).   
    (* `f = 0`/\`g = 0`/\`h = 0` *)
    intros (Hf, (Hg, Hh)).
    case (Z_lt_dec 2 o1).
     (*  `2 < o1` *)
     intro Ho1.
     generalize
      (Qquadratic_sign_nRdL_nRdL_5 a b c d e f g h 
         (dL xs) (dL ys) H_Qquadratic_sg_denom_nonzero).
     intros H1.
     assert
      (H_tuple_eq :
       (1%Z, (na, (nb, (nc, nd)), (ne, (nf, (ng, nh))), (np1, np2))) =
       (Z.sgn e, (a, (b, (c, d)), (e, (f, (g, h))), (dL xs, dL ys))));
      [ apply
         trans_eq
          with
            (Qquadratic_sign a b c d e f g h (dL xs) 
               (dL ys) H_Qquadratic_sg_denom_nonzero);
         [ apply sym_eq | apply H1; discriminate || (repeat split) ];
         assumption
      | generalize
         (Qquadratic_sign_tuple_equal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
            _ _ H_tuple_eq);
         intros
          (hl,
           ((hna, (hnb, (hnc, (hnd, (hne, (hnf, (hng, hnh))))))),
           (hp1,
            hp2)));
         do 10
          match goal with
          | id1:(?X1 = ?X2) |- ?X3 => try rewrite id1; clear id1
          end ].
     left; split;
      repeat
       match goal with
       | id1:(?X1 = 0%Z) |- ?X2 => rewrite id1; clear id1
       end; repeat rewrite Zplus_0_r;
      [ apply outside_square_1 | apply Zsgn_9; apply sym_eq ]; 
      assumption.
     (*  ~`2 < o1` *)
     case (Z_lt_dec o1 (-2)).
      (* `(-2) < o1` *)
      intros Ho1' Ho1.
      generalize
       (Qquadratic_sign_nRdL_nRdL_6 a b c d e f g h 
          (dL xs) (dL ys) H_Qquadratic_sg_denom_nonzero).
      intros H1.
      assert
       (H_tuple_eq :
        (1%Z, (na, (nb, (nc, nd)), (ne, (nf, (ng, nh))), (np1, np2))) =
        ((- Z.sgn e)%Z, (a, (b, (c, d)), (e, (f, (g, h))), (dL xs, dL ys))));
       [ apply
          trans_eq
           with
             (Qquadratic_sign a b c d e f g h (dL xs) 
                (dL ys) H_Qquadratic_sg_denom_nonzero);
          [ apply sym_eq | apply H1; discriminate || (repeat split) ];
          assumption
       | generalize
          (Qquadratic_sign_tuple_equal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
             _ _ _ H_tuple_eq);
          intros
           (hl,
            ((hna, (hnb, (hnc, (hnd, (hne, (hnf, (hng, hnh))))))),
            (hp1,
             hp2)));
          do 10
           match goal with
           | id1:(?X1 = ?X2) |- ?X3 => try rewrite id1; clear id1
           end ].
      right; split;
       repeat
        match goal with
        | id1:(?X1 = 0%Z) |- ?X2 => rewrite id1; clear id1
        end; repeat rewrite Zplus_0_r;
       [ apply outside_square_2
       | apply Zsgn_10; apply sym_eq; apply Z.opp_inj ]; 
       assumption.
      (* ~`o1 < (-2)` /\ ~`2 < o1` *)
      intros Ho2' Ho2.
      generalize
       (Qquadratic_sign_dL_dL_7 a b c d e f g h (dL xs) xs 
          (dL ys) ys H_Qquadratic_sg_denom_nonzero
          (Qquadratic_signok_4 _ _ _ _ _ _ H_Qquadratic_sg_denom_nonzero)
          (refl_equal _) (refl_equal _)).
      intros H1.
      assert
       (H_tuple_eq :
        Qquadratic_sign (a + b + c + d) (b + d) (c + d) d 
          (e + f + g + h) (f + h) (g + h) h xs ys
          (Qquadratic_signok_4 e f g h xs ys H_Qquadratic_sg_denom_nonzero) =
        (1%Z, (na, (nb, (nc, nd)), (ne, (nf, (ng, nh))), (np1, np2))));
       [ apply
          trans_eq
           with
             (Qquadratic_sign a b c d e f g h (dL xs) 
                (dL ys) H_Qquadratic_sg_denom_nonzero);
          [ apply sym_eq; apply H1; repeat split | idtac ]
       | apply
          (Qquadratic_sign_pos_1 (a + b + c + d)%Z 
             (b + d)%Z (c + d)%Z d (e + f + g + h)%Z 
             (f + h)%Z (g + h)%Z h xs ys
             (Qquadratic_signok_4 e f g h xs ys H_Qquadratic_sg_denom_nonzero)
             na nb nc nd ne nf ng nh np1 np2) ]; assumption.
    (* ~(`f = 0`/\`g = 0`/\`h = 0`) *)
    intro Hfgh'.
    case (inside_square_1_dec_inf o1 o2).    
     (* (inside_square_1 o1 o2) *)
     intro H_inside_1.
     generalize
      (Qquadratic_sign_nRdL_nRdL_8 a b c d e f g h 
         (dL xs) (dL ys) H_Qquadratic_sg_denom_nonzero).
     intros H1.
     assert
      (H_tuple_eq :
       (1%Z, (na, (nb, (nc, nd)), (ne, (nf, (ng, nh))), (np1, np2))) =
       (1%Z, (a, (b, (c, d)), (e, (f, (g, h))), (dL xs, dL ys))));
      [ apply
         trans_eq
          with
            (Qquadratic_sign a b c d e f g h (dL xs) 
               (dL ys) H_Qquadratic_sg_denom_nonzero);
         [ apply sym_eq | apply H1; discriminate || (repeat split) ];
         assumption
      | generalize
         (Qquadratic_sign_tuple_equal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
            _ _ H_tuple_eq);
         intros
          (hl,
           ((hna, (hnb, (hnc, (hnd, (hne, (hnf, (hng, hnh))))))),
           (hp1,
            hp2)));
         do 10
          match goal with
          | id1:(?X1 = ?X2) |- ?X3 => try rewrite id1; clear id1
          end ].
     case (inside_square_1_inf _ _ H_inside_1); intros (Ho1, Ho2);
      [ left; split; apply outside_square_1
      | right; split; apply outside_square_2 ]; assumption.
     (* ~(inside_square_1 o1 o2) *)    
     intro H_inside_1'.
     case (inside_square_2_dec_inf o1 o2).    
      (* (inside_square_2 o1 o2) *)
      intro H_inside_2.
      generalize
       (Qquadratic_sign_nRdL_nRdL_9 a b c d e f g h 
          (dL xs) (dL ys) H_Qquadratic_sg_denom_nonzero).
      intros H1.
      apply False_rec.
      assert
       (H_tuple_eq :
        (1%Z, (na, (nb, (nc, nd)), (ne, (nf, (ng, nh))), (np1, np2))) =
        ((-1)%Z, (a, (b, (c, d)), (e, (f, (g, h))), (dL xs, dL ys))));
       [ apply
          trans_eq
           with
             (Qquadratic_sign a b c d e f g h (dL xs) 
                (dL ys) H_Qquadratic_sg_denom_nonzero);
          [ apply sym_eq | apply H1; discriminate || (repeat split) ];
          assumption
       | generalize
          (Qquadratic_sign_tuple_equal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
             _ _ _ H_tuple_eq);
          intros
           (hl,
            ((hna, (hnb, (hnc, (hnd, (hne, (hnf, (hng, hnh))))))),
            (hp1,
             hp2)));
          do 10
           match goal with
           | id1:(?X1 = ?X2) |- ?X3 => try rewrite id1; clear id1
           end ].
      discriminate hl.
      (*  ~(inside_square_1 o1 o2)/\~(inside_square_2 o1 o2) *)
      intros H_inside_2'. 
      generalize
       (Qquadratic_sign_dL_dL_10 a b c d e f g h (dL xs) xs 
          (dL ys) ys H_Qquadratic_sg_denom_nonzero
          (Qquadratic_signok_4 _ _ _ _ _ _ H_Qquadratic_sg_denom_nonzero)
          (refl_equal _) (refl_equal _)).
      intros H1.
      assert
       (H_tuple_eq :
        Qquadratic_sign (a + b + c + d) (b + d) (c + d) d 
          (e + f + g + h) (f + h) (g + h) h xs ys
          (Qquadratic_signok_4 e f g h xs ys H_Qquadratic_sg_denom_nonzero) =
        (1%Z, (na, (nb, (nc, nd)), (ne, (nf, (ng, nh))), (np1, np2))));
       [ apply
          trans_eq
           with
             (Qquadratic_sign a b c d e f g h (dL xs) 
                (dL ys) H_Qquadratic_sg_denom_nonzero);
          [ apply sym_eq; apply H1; repeat split | idtac ]
       | apply
          (Qquadratic_sign_pos_1 (a + b + c + d)%Z 
             (b + d)%Z (c + d)%Z d (e + f + g + h)%Z 
             (f + h)%Z (g + h)%Z h xs ys
             (Qquadratic_signok_4 e f g h xs ys H_Qquadratic_sg_denom_nonzero)
             na nb nc nd ne nf ng nh np1 np2) ]; assumption.

  (*  p1 = (dL xs) & p2 = One *)
  generalize (Qquadratic_signok_0' _ _ _ _ _ H_Qquadratic_sg_denom_nonzero).
  intros H_Qhomographic_sg_denom_nonzero.
  set
   (L3 :=
    Qhomographic_sign (a + b) (c + d) (e + f) (g + h) 
      (dL xs) H_Qhomographic_sg_denom_nonzero) in *.
  set (l1 := fst L3) in *.
  set (l2 := fst (snd L3)) in *.
  set (l3 := snd (snd L3)) in *.
  set (na_ := fst l2) in *.
  set (nb_ := fst (snd l2)) in *.
  set (nc_ := fst (snd (snd l2))) in *.
  set (nd_ := snd (snd (snd l2))) in *.
  generalize
   (Qquadratic_sign_nRdL_One a b c d e f g h (dL xs) One
      H_Qquadratic_sg_denom_nonzero l1 na_ nb_ nc_ nd_ l3
      H_Qhomographic_sg_denom_nonzero); intros H1.
  assert
   (H_tuple_eq :
    (1%Z, (na, (nb, (nc, nd)), (ne, (nf, (ng, nh))), (np1, np2))) =
    (l1, (0%Z, (na_, (0%Z, nb_)), (0%Z, (nc_, (0%Z, nd_))), (l3, One))));
   [ apply
      trans_eq
       with
         (Qquadratic_sign a b c d e f g h (dL xs) One
            H_Qquadratic_sg_denom_nonzero);
      [ apply sym_eq; assumption
      | apply H1; fold L3 in |- *; repeat (apply pair_2; try reflexivity);
         discriminate || reflexivity ]
   | generalize
      (Qquadratic_sign_tuple_equal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
         _ H_tuple_eq);
      intros
       (hl,
        ((hna, (hnb, (hnc, (hnd, (hne, (hnf, (hng, hnh))))))),
        (hp1,
         hp2)));
      do 10
       match goal with
       | id1:(?X1 = ?X2) |- ?X3 => try rewrite id1; clear id1
       end; repeat rewrite Zplus_0_l; repeat rewrite Zplus_0_r ];
   apply
    (sg_pos_1 (a + b) (c + d) (e + f) (g + h) (dL xs)
       H_Qhomographic_sg_denom_nonzero na_ nb_ nc_ nd_ l3); 
   rewrite hl; fold L3 in |- *; repeat (apply pair_2; try reflexivity);
   discriminate || reflexivity.

 (* p1 = One *)
  generalize (Qquadratic_signok_0 _ _ _ _ _ H_Qquadratic_sg_denom_nonzero).
  intros H_Qhomographic_sg_denom_nonzero.
  set
   (L3 :=
    Qhomographic_sign (a + c) (b + d) (e + g) (f + h) p2
      H_Qhomographic_sg_denom_nonzero) in *.
  set (l1 := fst L3) in *.
  set (l2 := fst (snd L3)) in *.
  set (l3 := snd (snd L3)) in *.
  set (na_ := fst l2) in *.
  set (nb_ := fst (snd l2)) in *.
  set (nc_ := fst (snd (snd l2))) in *.
  set (nd_ := snd (snd (snd l2))) in *.
  generalize
   (Qquadratic_sign_One_y a b c d e f g h One p2
      H_Qquadratic_sg_denom_nonzero l1 na_ nb_ nc_ nd_ l3
      H_Qhomographic_sg_denom_nonzero); intros H1.
  assert
   (H_tuple_eq :
    (1%Z, (na, (nb, (nc, nd)), (ne, (nf, (ng, nh))), (np1, np2))) =
    (l1, (0%Z, (0%Z, (na_, nb_)), (0%Z, (0%Z, (nc_, nd_))), (One, l3))));
   [ apply
      trans_eq
       with
         (Qquadratic_sign a b c d e f g h One p2
            H_Qquadratic_sg_denom_nonzero);
      [ apply sym_eq; assumption
      | apply H1; fold L3 in |- *; repeat (apply pair_2; try reflexivity);
         discriminate || reflexivity ]
   | generalize
      (Qquadratic_sign_tuple_equal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
         _ H_tuple_eq);
      intros
       (hl,
        ((hna, (hnb, (hnc, (hnd, (hne, (hnf, (hng, hnh))))))),
        (hp1,
         hp2)));
      do 10
       match goal with
       | id1:(?X1 = ?X2) |- ?X3 => try rewrite id1; clear id1
       end; repeat rewrite Zplus_0_l; repeat rewrite Zplus_0_r ];
   apply
    (sg_pos_1 (a + c) (b + d) (e + g) (f + h) p2
       H_Qhomographic_sg_denom_nonzero na_ nb_ nc_ nd_ l3); 
   rewrite hl; fold L3 in |- *; repeat (apply pair_2; try reflexivity);
   discriminate || reflexivity.
Qed.

Lemma Qquadratic_sign_pos_2 :
 forall (a b c d e f g h : Z) (p1 p2 : Qpositive)
   (H_Qquadratic_sg_denom_nonzero : Qquadratic_sg_denom_nonzero e f g h p1 p2)
   (na nb nc nd ne nf ng nh : Z) (np1 np2 : Qpositive),
 Qquadratic_sign a b c d e f g h p1 p2 H_Qquadratic_sg_denom_nonzero =
 (1%Z, (na, (nb, (nc, nd)), (ne, (nf, (ng, nh))), (np1, np2))) ->
 {(0 <= na)%Z /\
  (0 <= nb)%Z /\
  (0 <= nc)%Z /\
  (0 <= nd)%Z /\ (0 <= ne)%Z /\ (0 <= nf)%Z /\ (0 <= ng)%Z /\ (0 <= nh)%Z} +
 {(na <= 0)%Z /\
  (nb <= 0)%Z /\
  (nc <= 0)%Z /\
  (nd <= 0)%Z /\ (ne <= 0)%Z /\ (nf <= 0)%Z /\ (ng <= 0)%Z /\ (nh <= 0)%Z} +
 {np1 = One /\
  (0 <= na + nc)%Z /\
  (0 <= nb + nd)%Z /\ (0 <= ne + ng)%Z /\ (0 <= nf + nh)%Z} +
 {np1 = One /\
  (na + nc <= 0)%Z /\
  (nb + nd <= 0)%Z /\ (ne + ng <= 0)%Z /\ (nf + nh <= 0)%Z} +
 {np1 = One /\ np2 = One} +
 {np1 <> One /\
  np2 = One /\
  (0 <= na + nb)%Z /\
  (0 <= nc + nd)%Z /\ (0 <= ne + nf)%Z /\ (0 <= ng + nh)%Z} +
 {np1 <> One /\
  np2 = One /\
  (na + nb <= 0)%Z /\
  (nc + nd <= 0)%Z /\ (ne + nf <= 0)%Z /\ (ng + nh <= 0)%Z}.
Proof.
 fix Qquadratic_sign_pos_2 9.
 intros.
 set (o1 := outside_square a b c d) in *.
 set (o2 := outside_square e f g h) in *.
 destruct p1 as [xs| xs| ].
 (* p1 = (nR xs) *)
 destruct p2 as [ys| ys| ].
  (*  p1 = (nR xs) & p2 = (nR ys) *)
  case (three_integers_dec_inf b c d).  
   (* `b = 0`/\`c = 0`/\`d = 0` *)
   intros (Hb, (Hc, Hd)).
   (* Intros [Hb [Hc] Hd]. *)
   case (three_integers_dec_inf f g h).   
    (* `f = 0`/\`g = 0`/\`h = 0` *)
    intros (Hf, (Hg, Hh)).
    generalize
     (Qquadratic_sign_nRdL_nRdL_1 a b c d e f g h (nR xs) 
        (nR ys) H_Qquadratic_sg_denom_nonzero).
    intros H1.
    assert
     (H_tuple_eq :
      (1%Z, (na, (nb, (nc, nd)), (ne, (nf, (ng, nh))), (np1, np2))) =
      ((Z.sgn a * Z.sgn e)%Z,
      (a, (b, (c, d)), (e, (f, (g, h))), (nR xs, nR ys))));
     [ apply
        trans_eq
         with
           (Qquadratic_sign a b c d e f g h (nR xs) 
              (nR ys) H_Qquadratic_sg_denom_nonzero);
        [ apply sym_eq | apply H1; discriminate || (repeat split) ];
        assumption
     | generalize
        (Qquadratic_sign_tuple_equal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
           _ _ H_tuple_eq);
        intros
         (hl,
          ((hna, (hnb, (hnc, (hnd, (hne, (hnf, (hng, hnh))))))),
          (hp1,
           hp2)));
        do 10
         match goal with
         | id1:(?X1 = ?X2) |- ?X3 => try rewrite id1; clear id1
         end ].
    left; left; left; left; left; rewrite <- Zsgn_15 in hl.
    case (Zsgn_16 _ _ (sym_eq hl)); intros (Ha, He); [ left | right ];
     repeat split;
     repeat
      match goal with
      | id1:(?X1 = 0%Z) |- ?X2 => rewrite id1; clear id1
      end; first [ apply Z.le_refl | apply Zlt_le_weak ]; 
     assumption.
    (* ~(`f = 0`/\`g = 0`/\`h = 0`) *)
    intros H_fgh'.
    case (Z_lt_dec 2 o2).
     (*  `2 < o2` *)
     intro Ho2.
     generalize
      (Qquadratic_sign_nRdL_nRdL_2 a b c d e f g h 
         (nR xs) (nR ys) H_Qquadratic_sg_denom_nonzero).
     intros H1.
     assert
      (H_tuple_eq :
       (1%Z, (na, (nb, (nc, nd)), (ne, (nf, (ng, nh))), (np1, np2))) =
       (Z.sgn a, (a, (b, (c, d)), (e, (f, (g, h))), (nR xs, nR ys))));
      [ apply
         trans_eq
          with
            (Qquadratic_sign a b c d e f g h (nR xs) 
               (nR ys) H_Qquadratic_sg_denom_nonzero);
         [ apply sym_eq | apply H1; discriminate || (repeat split) ];
         assumption
      | generalize
         (Qquadratic_sign_tuple_equal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
            _ _ H_tuple_eq);
         intros
          (hl,
           ((hna, (hnb, (hnc, (hnd, (hne, (hnf, (hng, hnh))))))),
           (hp1,
            hp2)));
         do 10
          match goal with
          | id1:(?X1 = ?X2) |- ?X3 => try rewrite id1; clear id1
          end ].
     left; left; left; left; left; left; repeat split;
      repeat
       match goal with
       | id1:(?X1 = 0%Z) |- ?X2 => rewrite id1; clear id1
       end; first
      [ apply Z.le_refl
      | match goal with
        |  |- (0 <= ?X1)%Z => apply Zlt_le_weak; apply Zsgn_9
        |  |- (?X1 <= 0)%Z =>
            apply Zlt_le_weak; apply Zsgn_10; apply Z.opp_inj
        end; apply sym_eq; assumption
      | unfold o2 in Ho2;
         match goal with
         | id1:(2 < outside_square ?X1 ?X2 ?X3 ?X4)%Z |- 
         (0 <= ?X1)%Z =>
             apply outside_square_3 with X2 X3 X4
         | id1:(2 < outside_square ?X1 ?X2 ?X3 ?X4)%Z |- 
         (0 <= ?X2)%Z =>
             apply outside_square_4 with X1 X3 X4
         | id1:(2 < outside_square ?X1 ?X2 ?X3 ?X4)%Z |- 
         (0 <= ?X3)%Z =>
             apply outside_square_5 with X1 X2 X4
         | id1:(2 < outside_square ?X1 ?X2 ?X3 ?X4)%Z |- 
         (0 <= ?X4)%Z =>
             apply outside_square_6 with X1 X2 X3
         | id1:(outside_square ?X1 ?X2 ?X3 ?X4 < -2)%Z |- 
         (?X1 <= 0)%Z =>
             apply outside_square_7 with X2 X3 X4
         | id1:(outside_square ?X1 ?X2 ?X3 ?X4 < -2)%Z |- 
         (?X2 <= 0)%Z =>
             apply outside_square_8 with X1 X3 X4
         | id1:(outside_square ?X1 ?X2 ?X3 ?X4 < -2)%Z |- 
         (?X3 <= 0)%Z =>
             apply outside_square_9 with X1 X2 X4
         | id1:(outside_square ?X1 ?X2 ?X3 ?X4 < -2)%Z |- 
         (?X4 <= 0)%Z => apply outside_square_10 with X1 X2 X3
         end; assumption ].
     
     (*  ~`2 < o2` *)
     case (Z_lt_dec o2 (-2)).     
     (* `(-2) < o2` *)
      intros Ho2' Ho2.
      generalize
       (Qquadratic_sign_nRdL_nRdL_3 a b c d e f g h 
          (nR xs) (nR ys) H_Qquadratic_sg_denom_nonzero).
      intros H1.
      assert
       (H_tuple_eq :
        (1%Z, (na, (nb, (nc, nd)), (ne, (nf, (ng, nh))), (np1, np2))) =
        ((- Z.sgn a)%Z, (a, (b, (c, d)), (e, (f, (g, h))), (nR xs, nR ys))));
       [ apply
          trans_eq
           with
             (Qquadratic_sign a b c d e f g h (nR xs) 
                (nR ys) H_Qquadratic_sg_denom_nonzero);
          [ apply sym_eq | apply H1; discriminate || (repeat split) ];
          assumption
       | generalize
          (Qquadratic_sign_tuple_equal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
             _ _ _ H_tuple_eq);
          intros
           (hl,
            ((hna, (hnb, (hnc, (hnd, (hne, (hnf, (hng, hnh))))))),
            (hp1,
             hp2)));
          do 10
           match goal with
           | id1:(?X1 = ?X2) |- ?X3 => try rewrite id1; clear id1
           end ].
      left; left; left; left; left; right; repeat split;
       repeat
        match goal with
        | id1:(?X1 = 0%Z) |- ?X2 => rewrite id1; clear id1
        end; first
       [ apply Z.le_refl
       | match goal with
         |  |- (0 <= ?X1)%Z => apply Zlt_le_weak; apply Zsgn_9
         |  |- (?X1 <= 0)%Z =>
             apply Zlt_le_weak; apply Zsgn_10; apply Z.opp_inj
         end; apply sym_eq; assumption
       | unfold o2 in Ho2';
          match goal with
          | id1:(2 < outside_square ?X1 ?X2 ?X3 ?X4)%Z |- 
          (0 <= ?X1)%Z =>
              apply outside_square_3 with X2 X3 X4
          | id1:(2 < outside_square ?X1 ?X2 ?X3 ?X4)%Z |- 
          (0 <= ?X2)%Z =>
              apply outside_square_4 with X1 X3 X4
          | id1:(2 < outside_square ?X1 ?X2 ?X3 ?X4)%Z |- 
          (0 <= ?X3)%Z =>
              apply outside_square_5 with X1 X2 X4
          | id1:(2 < outside_square ?X1 ?X2 ?X3 ?X4)%Z |- 
          (0 <= ?X4)%Z =>
              apply outside_square_6 with X1 X2 X3
          | id1:(outside_square ?X1 ?X2 ?X3 ?X4 < -2)%Z |- 
          (?X1 <= 0)%Z =>
              apply outside_square_7 with X2 X3 X4
          | id1:(outside_square ?X1 ?X2 ?X3 ?X4 < -2)%Z |- 
          (?X2 <= 0)%Z =>
              apply outside_square_8 with X1 X3 X4
          | id1:(outside_square ?X1 ?X2 ?X3 ?X4 < -2)%Z |- 
          (?X3 <= 0)%Z =>
              apply outside_square_9 with X1 X2 X4
          | id1:(outside_square ?X1 ?X2 ?X3 ?X4 < -2)%Z |- 
          (?X4 <= 0)%Z => apply outside_square_10 with X1 X2 X3
          end; assumption ].
     (* ~`o1 < (-2)` /\ ~`2 < o1` *)
      intros Ho2' Ho2.
      generalize
       (Qquadratic_sign_nR_nR_4 a b c d e f g h (nR xs) xs 
          (nR ys) ys H_Qquadratic_sg_denom_nonzero
          (Qquadratic_signok_1 _ _ _ _ _ _ H_Qquadratic_sg_denom_nonzero)
          (refl_equal _) (refl_equal _)).
      intros H1.
      assert
       (H_tuple_eq :
        Qquadratic_sign a (a + b) (a + c) (a + b + c + d) e 
          (e + f) (e + g) (e + f + g + h) xs ys
          (Qquadratic_signok_1 e f g h xs ys H_Qquadratic_sg_denom_nonzero) =
        (1%Z, (na, (nb, (nc, nd)), (ne, (nf, (ng, nh))), (np1, np2))));
       [ apply
          trans_eq
           with
             (Qquadratic_sign a b c d e f g h (nR xs) 
                (nR ys) H_Qquadratic_sg_denom_nonzero);
          [ apply sym_eq; apply H1; repeat split | idtac ]
       | apply
          (Qquadratic_sign_pos_2 a (a + b)%Z (a + c)%Z 
             (a + b + c + d)%Z e (e + f)%Z (e + g)%Z 
             (e + f + g + h)%Z xs ys
             (Qquadratic_signok_1 e f g h xs ys H_Qquadratic_sg_denom_nonzero)
             na nb nc nd ne nf ng nh np1 np2) ]; assumption.
   (* ~ `b = 0`/\`c = 0`/\`d = 0` *)
   intros Hbcd'.
   (* Intros [Hb [Hc] Hd]. *)
   case (three_integers_dec_inf f g h).   
    (* `f = 0`/\`g = 0`/\`h = 0` *)
    intros (Hf, (Hg, Hh)).
    case (Z_lt_dec 2 o1).
     (*  `2 < o1` *)
     intro Ho1.
     generalize
      (Qquadratic_sign_nRdL_nRdL_5 a b c d e f g h 
         (nR xs) (nR ys) H_Qquadratic_sg_denom_nonzero).
     intros H1.
     assert
      (H_tuple_eq :
       (1%Z, (na, (nb, (nc, nd)), (ne, (nf, (ng, nh))), (np1, np2))) =
       (Z.sgn e, (a, (b, (c, d)), (e, (f, (g, h))), (nR xs, nR ys))));
      [ apply
         trans_eq
          with
            (Qquadratic_sign a b c d e f g h (nR xs) 
               (nR ys) H_Qquadratic_sg_denom_nonzero);
         [ apply sym_eq | apply H1; discriminate || (repeat split) ];
         assumption
      | generalize
         (Qquadratic_sign_tuple_equal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
            _ _ H_tuple_eq);
         intros
          (hl,
           ((hna, (hnb, (hnc, (hnd, (hne, (hnf, (hng, hnh))))))),
           (hp1,
            hp2)));
         do 10
          match goal with
          | id1:(?X1 = ?X2) |- ?X3 => try rewrite id1; clear id1
          end ].
     left; left; left; left; left; left; repeat split;
      repeat
       match goal with
       | id1:(?X1 = 0%Z) |- ?X2 => rewrite id1; clear id1
       end; first
      [ apply Z.le_refl
      | match goal with
        |  |- (0 <= ?X1)%Z => apply Zlt_le_weak; apply Zsgn_9
        |  |- (?X1 <= 0)%Z =>
            apply Zlt_le_weak; apply Zsgn_10; apply Z.opp_inj
        end; apply sym_eq; assumption
      | unfold o1 in Ho1;
         match goal with
         | id1:(2 < outside_square ?X1 ?X2 ?X3 ?X4)%Z |- 
         (0 <= ?X1)%Z =>
             apply outside_square_3 with X2 X3 X4
         | id1:(2 < outside_square ?X1 ?X2 ?X3 ?X4)%Z |- 
         (0 <= ?X2)%Z =>
             apply outside_square_4 with X1 X3 X4
         | id1:(2 < outside_square ?X1 ?X2 ?X3 ?X4)%Z |- 
         (0 <= ?X3)%Z =>
             apply outside_square_5 with X1 X2 X4
         | id1:(2 < outside_square ?X1 ?X2 ?X3 ?X4)%Z |- 
         (0 <= ?X4)%Z =>
             apply outside_square_6 with X1 X2 X3
         | id1:(outside_square ?X1 ?X2 ?X3 ?X4 < -2)%Z |- 
         (?X1 <= 0)%Z =>
             apply outside_square_7 with X2 X3 X4
         | id1:(outside_square ?X1 ?X2 ?X3 ?X4 < -2)%Z |- 
         (?X2 <= 0)%Z =>
             apply outside_square_8 with X1 X3 X4
         | id1:(outside_square ?X1 ?X2 ?X3 ?X4 < -2)%Z |- 
         (?X3 <= 0)%Z =>
             apply outside_square_9 with X1 X2 X4
         | id1:(outside_square ?X1 ?X2 ?X3 ?X4 < -2)%Z |- 
         (?X4 <= 0)%Z => apply outside_square_10 with X1 X2 X3
         end; assumption ].
     (*  ~`2 < o1` *)
     case (Z_lt_dec o1 (-2)).
      (* `(-2) < o1` *)
      intros Ho1' Ho1.
      generalize
       (Qquadratic_sign_nRdL_nRdL_6 a b c d e f g h 
          (nR xs) (nR ys) H_Qquadratic_sg_denom_nonzero).
      intros H1.
      assert
       (H_tuple_eq :
        (1%Z, (na, (nb, (nc, nd)), (ne, (nf, (ng, nh))), (np1, np2))) =
        ((- Z.sgn e)%Z, (a, (b, (c, d)), (e, (f, (g, h))), (nR xs, nR ys))));
       [ apply
          trans_eq
           with
             (Qquadratic_sign a b c d e f g h (nR xs) 
                (nR ys) H_Qquadratic_sg_denom_nonzero);
          [ apply sym_eq | apply H1; discriminate || (repeat split) ];
          assumption
       | generalize
          (Qquadratic_sign_tuple_equal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
             _ _ _ H_tuple_eq);
          intros
           (hl,
            ((hna, (hnb, (hnc, (hnd, (hne, (hnf, (hng, hnh))))))),
            (hp1,
             hp2)));
          do 10
           match goal with
           | id1:(?X1 = ?X2) |- ?X3 => try rewrite id1; clear id1
           end ].
      left; left; left; left; left; right; repeat split;
       repeat
        match goal with
        | id1:(?X1 = 0%Z) |- ?X2 => rewrite id1; clear id1
        end; first
       [ apply Z.le_refl
       | match goal with
         |  |- (0 <= ?X1)%Z => apply Zlt_le_weak; apply Zsgn_9
         |  |- (?X1 <= 0)%Z =>
             apply Zlt_le_weak; apply Zsgn_10; apply Z.opp_inj
         end; apply sym_eq; assumption
       | unfold o1 in Ho1';
          match goal with
          | id1:(2 < outside_square ?X1 ?X2 ?X3 ?X4)%Z |- 
          (0 <= ?X1)%Z =>
              apply outside_square_3 with X2 X3 X4
          | id1:(2 < outside_square ?X1 ?X2 ?X3 ?X4)%Z |- 
          (0 <= ?X2)%Z =>
              apply outside_square_4 with X1 X3 X4
          | id1:(2 < outside_square ?X1 ?X2 ?X3 ?X4)%Z |- 
          (0 <= ?X3)%Z =>
              apply outside_square_5 with X1 X2 X4
          | id1:(2 < outside_square ?X1 ?X2 ?X3 ?X4)%Z |- 
          (0 <= ?X4)%Z =>
              apply outside_square_6 with X1 X2 X3
          | id1:(outside_square ?X1 ?X2 ?X3 ?X4 < -2)%Z |- 
          (?X1 <= 0)%Z =>
              apply outside_square_7 with X2 X3 X4
          | id1:(outside_square ?X1 ?X2 ?X3 ?X4 < -2)%Z |- 
          (?X2 <= 0)%Z =>
              apply outside_square_8 with X1 X3 X4
          | id1:(outside_square ?X1 ?X2 ?X3 ?X4 < -2)%Z |- 
          (?X3 <= 0)%Z =>
              apply outside_square_9 with X1 X2 X4
          | id1:(outside_square ?X1 ?X2 ?X3 ?X4 < -2)%Z |- 
          (?X4 <= 0)%Z => apply outside_square_10 with X1 X2 X3
          end; assumption ].

      (* ~`o1 < (-2)` /\ ~`2 < o1` *)
      intros Ho2' Ho2.
      generalize
       (Qquadratic_sign_nR_nR_7 a b c d e f g h (nR xs) xs 
          (nR ys) ys H_Qquadratic_sg_denom_nonzero
          (Qquadratic_signok_1 _ _ _ _ _ _ H_Qquadratic_sg_denom_nonzero)
          (refl_equal _) (refl_equal _)).
      intros H1.
      assert
       (H_tuple_eq :
        Qquadratic_sign a (a + b) (a + c) (a + b + c + d) e 
          (e + f) (e + g) (e + f + g + h) xs ys
          (Qquadratic_signok_1 e f g h xs ys H_Qquadratic_sg_denom_nonzero) =
        (1%Z, (na, (nb, (nc, nd)), (ne, (nf, (ng, nh))), (np1, np2))));
       [ apply
          trans_eq
           with
             (Qquadratic_sign a b c d e f g h (nR xs) 
                (nR ys) H_Qquadratic_sg_denom_nonzero);
          [ apply sym_eq; apply H1; repeat split | idtac ]
       | apply
          (Qquadratic_sign_pos_2 a (a + b)%Z (a + c)%Z 
             (a + b + c + d)%Z e (e + f)%Z (e + g)%Z 
             (e + f + g + h)%Z xs ys
             (Qquadratic_signok_1 e f g h xs ys H_Qquadratic_sg_denom_nonzero)
             na nb nc nd ne nf ng nh np1 np2) ]; assumption.
    (* ~(`f = 0`/\`g = 0`/\`h = 0`) *)
    intro Hfgh'.
    case (inside_square_1_dec_inf o1 o2).    
     (* (inside_square_1 o1 o2) *)
     intro H_inside_1.
     generalize
      (Qquadratic_sign_nRdL_nRdL_8 a b c d e f g h 
         (nR xs) (nR ys) H_Qquadratic_sg_denom_nonzero).
     intros H1.
     assert
      (H_tuple_eq :
       (1%Z, (na, (nb, (nc, nd)), (ne, (nf, (ng, nh))), (np1, np2))) =
       (1%Z, (a, (b, (c, d)), (e, (f, (g, h))), (nR xs, nR ys))));
      [ apply
         trans_eq
          with
            (Qquadratic_sign a b c d e f g h (nR xs) 
               (nR ys) H_Qquadratic_sg_denom_nonzero);
         [ apply sym_eq | apply H1; discriminate || (repeat split) ];
         assumption
      | generalize
         (Qquadratic_sign_tuple_equal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
            _ _ H_tuple_eq);
         intros
          (hl,
           ((hna, (hnb, (hnc, (hnd, (hne, (hnf, (hng, hnh))))))),
           (hp1,
            hp2)));
         do 10
          match goal with
          | id1:(?X1 = ?X2) |- ?X3 => try rewrite id1; clear id1
          end ].
     left; left; left; left; left; case (inside_square_1_inf _ _ H_inside_1);
      intros (Ho1, Ho2); [ left | right ]; repeat split; first
      [ apply Z.le_refl
      | match goal with
        |  |- (0 <= ?X1)%Z => apply Zlt_le_weak; apply Zsgn_9
        |  |- (?X1 <= 0)%Z =>
            apply Zlt_le_weak; apply Zsgn_10; apply Z.opp_inj
        end; apply sym_eq; assumption
      | unfold o1 in Ho1; unfold o2 in Ho2;
         match goal with
         | id1:(2 < outside_square ?X1 ?X2 ?X3 ?X4)%Z |- 
         (0 <= ?X1)%Z =>
             apply outside_square_3 with X2 X3 X4
         | id1:(2 < outside_square ?X1 ?X2 ?X3 ?X4)%Z |- 
         (0 <= ?X2)%Z =>
             apply outside_square_4 with X1 X3 X4
         | id1:(2 < outside_square ?X1 ?X2 ?X3 ?X4)%Z |- 
         (0 <= ?X3)%Z =>
             apply outside_square_5 with X1 X2 X4
         | id1:(2 < outside_square ?X1 ?X2 ?X3 ?X4)%Z |- 
         (0 <= ?X4)%Z =>
             apply outside_square_6 with X1 X2 X3
         | id1:(outside_square ?X1 ?X2 ?X3 ?X4 < -2)%Z |- 
         (?X1 <= 0)%Z =>
             apply outside_square_7 with X2 X3 X4
         | id1:(outside_square ?X1 ?X2 ?X3 ?X4 < -2)%Z |- 
         (?X2 <= 0)%Z =>
             apply outside_square_8 with X1 X3 X4
         | id1:(outside_square ?X1 ?X2 ?X3 ?X4 < -2)%Z |- 
         (?X3 <= 0)%Z =>
             apply outside_square_9 with X1 X2 X4
         | id1:(outside_square ?X1 ?X2 ?X3 ?X4 < -2)%Z |- 
         (?X4 <= 0)%Z => apply outside_square_10 with X1 X2 X3
         end; assumption ].
      (* ~(inside_square_1 o1 o2) *)    
     intro H_inside_1'.
     case (inside_square_2_dec_inf o1 o2).    
      (* (inside_square_2 o1 o2) *)
      intro H_inside_2.
      generalize
       (Qquadratic_sign_nRdL_nRdL_9 a b c d e f g h 
          (nR xs) (nR ys) H_Qquadratic_sg_denom_nonzero).
      intros H1.
      apply False_rec.
      assert
       (H_tuple_eq :
        (1%Z, (na, (nb, (nc, nd)), (ne, (nf, (ng, nh))), (np1, np2))) =
        ((-1)%Z, (a, (b, (c, d)), (e, (f, (g, h))), (nR xs, nR ys))));
       [ apply
          trans_eq
           with
             (Qquadratic_sign a b c d e f g h (nR xs) 
                (nR ys) H_Qquadratic_sg_denom_nonzero);
          [ apply sym_eq | apply H1; discriminate || (repeat split) ];
          assumption
       | generalize
          (Qquadratic_sign_tuple_equal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
             _ _ _ H_tuple_eq);
          intros
           (hl,
            ((hna, (hnb, (hnc, (hnd, (hne, (hnf, (hng, hnh))))))),
            (hp1,
             hp2)));
          do 10
           match goal with
           | id1:(?X1 = ?X2) |- ?X3 => try rewrite id1; clear id1
           end ].
      discriminate hl.
      (*  ~(inside_square_1 o1 o2)/\~(inside_square_2 o1 o2) *)
      intros H_inside_2'. 
      generalize
       (Qquadratic_sign_nR_nR_10 a b c d e f g h (nR xs) xs 
          (nR ys) ys H_Qquadratic_sg_denom_nonzero
          (Qquadratic_signok_1 _ _ _ _ _ _ H_Qquadratic_sg_denom_nonzero)
          (refl_equal _) (refl_equal _)).
      intros H1.
      assert
       (H_tuple_eq :
        Qquadratic_sign a (a + b) (a + c) (a + b + c + d) e 
          (e + f) (e + g) (e + f + g + h) xs ys
          (Qquadratic_signok_1 e f g h xs ys H_Qquadratic_sg_denom_nonzero) =
        (1%Z, (na, (nb, (nc, nd)), (ne, (nf, (ng, nh))), (np1, np2))));
       [ apply
          trans_eq
           with
             (Qquadratic_sign a b c d e f g h (nR xs) 
                (nR ys) H_Qquadratic_sg_denom_nonzero);
          [ apply sym_eq; apply H1; repeat split | idtac ]
       | apply
          (Qquadratic_sign_pos_2 a (a + b)%Z (a + c)%Z 
             (a + b + c + d)%Z e (e + f)%Z (e + g)%Z 
             (e + f + g + h)%Z xs ys
             (Qquadratic_signok_1 e f g h xs ys H_Qquadratic_sg_denom_nonzero)
             na nb nc nd ne nf ng nh np1 np2) ]; assumption.

 (*  p1 = (nR xs) & p2 = (dL ys) *)
  case (three_integers_dec_inf b c d).  
   (* `b = 0`/\`c = 0`/\`d = 0` *)
   intros (Hb, (Hc, Hd)).
   (* Intros [Hb [Hc] Hd]. *)
   case (three_integers_dec_inf f g h).   
    (* `f = 0`/\`g = 0`/\`h = 0` *)
    intros (Hf, (Hg, Hh)).
    generalize
     (Qquadratic_sign_nRdL_nRdL_1 a b c d e f g h (nR xs) 
        (dL ys) H_Qquadratic_sg_denom_nonzero).
    intros H1.
    assert
     (H_tuple_eq :
      (1%Z, (na, (nb, (nc, nd)), (ne, (nf, (ng, nh))), (np1, np2))) =
      ((Z.sgn a * Z.sgn e)%Z,
      (a, (b, (c, d)), (e, (f, (g, h))), (nR xs, dL ys))));
     [ apply
        trans_eq
         with
           (Qquadratic_sign a b c d e f g h (nR xs) 
              (dL ys) H_Qquadratic_sg_denom_nonzero);
        [ apply sym_eq | apply H1; discriminate || (repeat split) ];
        assumption
     | generalize
        (Qquadratic_sign_tuple_equal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
           _ _ H_tuple_eq);
        intros
         (hl,
          ((hna, (hnb, (hnc, (hnd, (hne, (hnf, (hng, hnh))))))),
          (hp1,
           hp2)));
        do 10
         match goal with
         | id1:(?X1 = ?X2) |- ?X3 => try rewrite id1; clear id1
         end ].
    left; left; left; left; left; rewrite <- Zsgn_15 in hl.
    case (Zsgn_16 _ _ (sym_eq hl)); intros (Ha, He); [ left | right ];
     repeat split;
     repeat
      match goal with
      | id1:(?X1 = 0%Z) |- ?X2 => rewrite id1; clear id1
      end; first [ apply Z.le_refl | apply Zlt_le_weak ]; 
     assumption.
    (* ~(`f = 0`/\`g = 0`/\`h = 0`) *)
    intros H_fgh'.
    case (Z_lt_dec 2 o2).
     (*  `2 < o2` *)
     intro Ho2.
     generalize
      (Qquadratic_sign_nRdL_nRdL_2 a b c d e f g h 
         (nR xs) (dL ys) H_Qquadratic_sg_denom_nonzero).
     intros H1.
     assert
      (H_tuple_eq :
       (1%Z, (na, (nb, (nc, nd)), (ne, (nf, (ng, nh))), (np1, np2))) =
       (Z.sgn a, (a, (b, (c, d)), (e, (f, (g, h))), (nR xs, dL ys))));
      [ apply
         trans_eq
          with
            (Qquadratic_sign a b c d e f g h (nR xs) 
               (dL ys) H_Qquadratic_sg_denom_nonzero);
         [ apply sym_eq | apply H1; discriminate || (repeat split) ];
         assumption
      | generalize
         (Qquadratic_sign_tuple_equal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
            _ _ H_tuple_eq);
         intros
          (hl,
           ((hna, (hnb, (hnc, (hnd, (hne, (hnf, (hng, hnh))))))),
           (hp1,
            hp2)));
         do 10
          match goal with
          | id1:(?X1 = ?X2) |- ?X3 => try rewrite id1; clear id1
          end ].
     left; left; left; left; left; left; repeat split;
      repeat
       match goal with
       | id1:(?X1 = 0%Z) |- ?X2 => rewrite id1; clear id1
       end; first
      [ apply Z.le_refl
      | match goal with
        |  |- (0 <= ?X1)%Z => apply Zlt_le_weak; apply Zsgn_9
        |  |- (?X1 <= 0)%Z =>
            apply Zlt_le_weak; apply Zsgn_10; apply Z.opp_inj
        end; apply sym_eq; assumption
      | unfold o2 in Ho2;
         match goal with
         | id1:(2 < outside_square ?X1 ?X2 ?X3 ?X4)%Z |- 
         (0 <= ?X1)%Z =>
             apply outside_square_3 with X2 X3 X4
         | id1:(2 < outside_square ?X1 ?X2 ?X3 ?X4)%Z |- 
         (0 <= ?X2)%Z =>
             apply outside_square_4 with X1 X3 X4
         | id1:(2 < outside_square ?X1 ?X2 ?X3 ?X4)%Z |- 
         (0 <= ?X3)%Z =>
             apply outside_square_5 with X1 X2 X4
         | id1:(2 < outside_square ?X1 ?X2 ?X3 ?X4)%Z |- 
         (0 <= ?X4)%Z =>
             apply outside_square_6 with X1 X2 X3
         | id1:(outside_square ?X1 ?X2 ?X3 ?X4 < -2)%Z |- 
         (?X1 <= 0)%Z =>
             apply outside_square_7 with X2 X3 X4
         | id1:(outside_square ?X1 ?X2 ?X3 ?X4 < -2)%Z |- 
         (?X2 <= 0)%Z =>
             apply outside_square_8 with X1 X3 X4
         | id1:(outside_square ?X1 ?X2 ?X3 ?X4 < -2)%Z |- 
         (?X3 <= 0)%Z =>
             apply outside_square_9 with X1 X2 X4
         | id1:(outside_square ?X1 ?X2 ?X3 ?X4 < -2)%Z |- 
         (?X4 <= 0)%Z => apply outside_square_10 with X1 X2 X3
         end; assumption ].
     
     (*  ~`2 < o2` *)
     case (Z_lt_dec o2 (-2)).     
     (* `(-2) < o2` *)
      intros Ho2' Ho2.
      generalize
       (Qquadratic_sign_nRdL_nRdL_3 a b c d e f g h 
          (nR xs) (dL ys) H_Qquadratic_sg_denom_nonzero).
      intros H1.
      assert
       (H_tuple_eq :
        (1%Z, (na, (nb, (nc, nd)), (ne, (nf, (ng, nh))), (np1, np2))) =
        ((- Z.sgn a)%Z, (a, (b, (c, d)), (e, (f, (g, h))), (nR xs, dL ys))));
       [ apply
          trans_eq
           with
             (Qquadratic_sign a b c d e f g h (nR xs) 
                (dL ys) H_Qquadratic_sg_denom_nonzero);
          [ apply sym_eq | apply H1; discriminate || (repeat split) ];
          assumption
       | generalize
          (Qquadratic_sign_tuple_equal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
             _ _ _ H_tuple_eq);
          intros
           (hl,
            ((hna, (hnb, (hnc, (hnd, (hne, (hnf, (hng, hnh))))))),
            (hp1,
             hp2)));
          do 10
           match goal with
           | id1:(?X1 = ?X2) |- ?X3 => try rewrite id1; clear id1
           end ].
      left; left; left; left; left; right; repeat split;
       repeat
        match goal with
        | id1:(?X1 = 0%Z) |- ?X2 => rewrite id1; clear id1
        end; first
       [ apply Z.le_refl
       | match goal with
         |  |- (0 <= ?X1)%Z => apply Zlt_le_weak; apply Zsgn_9
         |  |- (?X1 <= 0)%Z =>
             apply Zlt_le_weak; apply Zsgn_10; apply Z.opp_inj
         end; apply sym_eq; assumption
       | unfold o2 in Ho2';
          match goal with
          | id1:(2 < outside_square ?X1 ?X2 ?X3 ?X4)%Z |- 
          (0 <= ?X1)%Z =>
              apply outside_square_3 with X2 X3 X4
          | id1:(2 < outside_square ?X1 ?X2 ?X3 ?X4)%Z |- 
          (0 <= ?X2)%Z =>
              apply outside_square_4 with X1 X3 X4
          | id1:(2 < outside_square ?X1 ?X2 ?X3 ?X4)%Z |- 
          (0 <= ?X3)%Z =>
              apply outside_square_5 with X1 X2 X4
          | id1:(2 < outside_square ?X1 ?X2 ?X3 ?X4)%Z |- 
          (0 <= ?X4)%Z =>
              apply outside_square_6 with X1 X2 X3
          | id1:(outside_square ?X1 ?X2 ?X3 ?X4 < -2)%Z |- 
          (?X1 <= 0)%Z =>
              apply outside_square_7 with X2 X3 X4
          | id1:(outside_square ?X1 ?X2 ?X3 ?X4 < -2)%Z |- 
          (?X2 <= 0)%Z =>
              apply outside_square_8 with X1 X3 X4
          | id1:(outside_square ?X1 ?X2 ?X3 ?X4 < -2)%Z |- 
          (?X3 <= 0)%Z =>
              apply outside_square_9 with X1 X2 X4
          | id1:(outside_square ?X1 ?X2 ?X3 ?X4 < -2)%Z |- 
          (?X4 <= 0)%Z => apply outside_square_10 with X1 X2 X3
          end; assumption ].
     (* ~`o1 < (-2)` /\ ~`2 < o1` *)
      intros Ho2' Ho2.
      generalize
       (Qquadratic_sign_nR_dL_4 a b c d e f g h (nR xs) xs 
          (dL ys) ys H_Qquadratic_sg_denom_nonzero
          (Qquadratic_signok_2 _ _ _ _ _ _ H_Qquadratic_sg_denom_nonzero)
          (refl_equal _) (refl_equal _)).
      intros H1.
      assert
       (H_tuple_eq :
        Qquadratic_sign (a + b) b (a + b + c + d) (b + d) 
          (e + f) f (e + f + g + h) (f + h) xs ys
          (Qquadratic_signok_2 e f g h xs ys H_Qquadratic_sg_denom_nonzero) =
        (1%Z, (na, (nb, (nc, nd)), (ne, (nf, (ng, nh))), (np1, np2))));
       [ apply
          trans_eq
           with
             (Qquadratic_sign a b c d e f g h (nR xs) 
                (dL ys) H_Qquadratic_sg_denom_nonzero);
          [ apply sym_eq; apply H1; repeat split | idtac ]
       | apply
          (Qquadratic_sign_pos_2 (a + b)%Z b (a + b + c + d)%Z 
             (b + d)%Z (e + f)%Z f (e + f + g + h)%Z 
             (f + h)%Z xs ys
             (Qquadratic_signok_2 e f g h xs ys H_Qquadratic_sg_denom_nonzero)
             na nb nc nd ne nf ng nh np1 np2) ]; assumption.
   (* ~ `b = 0`/\`c = 0`/\`d = 0` *)
   intros Hbcd'.
   (* Intros [Hb [Hc] Hd]. *)
   case (three_integers_dec_inf f g h).   
    (* `f = 0`/\`g = 0`/\`h = 0` *)
    intros (Hf, (Hg, Hh)).
    case (Z_lt_dec 2 o1).
     (*  `2 < o1` *)
     intro Ho1.
     generalize
      (Qquadratic_sign_nRdL_nRdL_5 a b c d e f g h 
         (nR xs) (dL ys) H_Qquadratic_sg_denom_nonzero).
     intros H1.
     assert
      (H_tuple_eq :
       (1%Z, (na, (nb, (nc, nd)), (ne, (nf, (ng, nh))), (np1, np2))) =
       (Z.sgn e, (a, (b, (c, d)), (e, (f, (g, h))), (nR xs, dL ys))));
      [ apply
         trans_eq
          with
            (Qquadratic_sign a b c d e f g h (nR xs) 
               (dL ys) H_Qquadratic_sg_denom_nonzero);
         [ apply sym_eq | apply H1; discriminate || (repeat split) ];
         assumption
      | generalize
         (Qquadratic_sign_tuple_equal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
            _ _ H_tuple_eq);
         intros
          (hl,
           ((hna, (hnb, (hnc, (hnd, (hne, (hnf, (hng, hnh))))))),
           (hp1,
            hp2)));
         do 10
          match goal with
          | id1:(?X1 = ?X2) |- ?X3 => try rewrite id1; clear id1
          end ].
     left; left; left; left; left; left; repeat split;
      repeat
       match goal with
       | id1:(?X1 = 0%Z) |- ?X2 => rewrite id1; clear id1
       end; first
      [ apply Z.le_refl
      | match goal with
        |  |- (0 <= ?X1)%Z => apply Zlt_le_weak; apply Zsgn_9
        |  |- (?X1 <= 0)%Z =>
            apply Zlt_le_weak; apply Zsgn_10; apply Z.opp_inj
        end; apply sym_eq; assumption
      | unfold o1 in Ho1;
         match goal with
         | id1:(2 < outside_square ?X1 ?X2 ?X3 ?X4)%Z |- 
         (0 <= ?X1)%Z =>
             apply outside_square_3 with X2 X3 X4
         | id1:(2 < outside_square ?X1 ?X2 ?X3 ?X4)%Z |- 
         (0 <= ?X2)%Z =>
             apply outside_square_4 with X1 X3 X4
         | id1:(2 < outside_square ?X1 ?X2 ?X3 ?X4)%Z |- 
         (0 <= ?X3)%Z =>
             apply outside_square_5 with X1 X2 X4
         | id1:(2 < outside_square ?X1 ?X2 ?X3 ?X4)%Z |- 
         (0 <= ?X4)%Z =>
             apply outside_square_6 with X1 X2 X3
         | id1:(outside_square ?X1 ?X2 ?X3 ?X4 < -2)%Z |- 
         (?X1 <= 0)%Z =>
             apply outside_square_7 with X2 X3 X4
         | id1:(outside_square ?X1 ?X2 ?X3 ?X4 < -2)%Z |- 
         (?X2 <= 0)%Z =>
             apply outside_square_8 with X1 X3 X4
         | id1:(outside_square ?X1 ?X2 ?X3 ?X4 < -2)%Z |- 
         (?X3 <= 0)%Z =>
             apply outside_square_9 with X1 X2 X4
         | id1:(outside_square ?X1 ?X2 ?X3 ?X4 < -2)%Z |- 
         (?X4 <= 0)%Z => apply outside_square_10 with X1 X2 X3
         end; assumption ].
     (*  ~`2 < o1` *)
     case (Z_lt_dec o1 (-2)).
      (* `(-2) < o1` *)
      intros Ho1' Ho1.
      generalize
       (Qquadratic_sign_nRdL_nRdL_6 a b c d e f g h 
          (nR xs) (dL ys) H_Qquadratic_sg_denom_nonzero).
      intros H1.
      assert
       (H_tuple_eq :
        (1%Z, (na, (nb, (nc, nd)), (ne, (nf, (ng, nh))), (np1, np2))) =
        ((- Z.sgn e)%Z, (a, (b, (c, d)), (e, (f, (g, h))), (nR xs, dL ys))));
       [ apply
          trans_eq
           with
             (Qquadratic_sign a b c d e f g h (nR xs) 
                (dL ys) H_Qquadratic_sg_denom_nonzero);
          [ apply sym_eq | apply H1; discriminate || (repeat split) ];
          assumption
       | generalize
          (Qquadratic_sign_tuple_equal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
             _ _ _ H_tuple_eq);
          intros
           (hl,
            ((hna, (hnb, (hnc, (hnd, (hne, (hnf, (hng, hnh))))))),
            (hp1,
             hp2)));
          do 10
           match goal with
           | id1:(?X1 = ?X2) |- ?X3 => try rewrite id1; clear id1
           end ].
      left; left; left; left; left; right; repeat split;
       repeat
        match goal with
        | id1:(?X1 = 0%Z) |- ?X2 => rewrite id1; clear id1
        end; first
       [ apply Z.le_refl
       | match goal with
         |  |- (0 <= ?X1)%Z => apply Zlt_le_weak; apply Zsgn_9
         |  |- (?X1 <= 0)%Z =>
             apply Zlt_le_weak; apply Zsgn_10; apply Z.opp_inj
         end; apply sym_eq; assumption
       | unfold o1 in Ho1';
          match goal with
          | id1:(2 < outside_square ?X1 ?X2 ?X3 ?X4)%Z |- 
          (0 <= ?X1)%Z =>
              apply outside_square_3 with X2 X3 X4
          | id1:(2 < outside_square ?X1 ?X2 ?X3 ?X4)%Z |- 
          (0 <= ?X2)%Z =>
              apply outside_square_4 with X1 X3 X4
          | id1:(2 < outside_square ?X1 ?X2 ?X3 ?X4)%Z |- 
          (0 <= ?X3)%Z =>
              apply outside_square_5 with X1 X2 X4
          | id1:(2 < outside_square ?X1 ?X2 ?X3 ?X4)%Z |- 
          (0 <= ?X4)%Z =>
              apply outside_square_6 with X1 X2 X3
          | id1:(outside_square ?X1 ?X2 ?X3 ?X4 < -2)%Z |- 
          (?X1 <= 0)%Z =>
              apply outside_square_7 with X2 X3 X4
          | id1:(outside_square ?X1 ?X2 ?X3 ?X4 < -2)%Z |- 
          (?X2 <= 0)%Z =>
              apply outside_square_8 with X1 X3 X4
          | id1:(outside_square ?X1 ?X2 ?X3 ?X4 < -2)%Z |- 
          (?X3 <= 0)%Z =>
              apply outside_square_9 with X1 X2 X4
          | id1:(outside_square ?X1 ?X2 ?X3 ?X4 < -2)%Z |- 
          (?X4 <= 0)%Z => apply outside_square_10 with X1 X2 X3
          end; assumption ].

      (* ~`o1 < (-2)` /\ ~`2 < o1` *)
      intros Ho2' Ho2.
      generalize
       (Qquadratic_sign_nR_dL_7 a b c d e f g h (nR xs) xs 
          (dL ys) ys H_Qquadratic_sg_denom_nonzero
          (Qquadratic_signok_2 _ _ _ _ _ _ H_Qquadratic_sg_denom_nonzero)
          (refl_equal _) (refl_equal _)).
      intros H1.
      assert
       (H_tuple_eq :
        Qquadratic_sign (a + b) b (a + b + c + d) (b + d) 
          (e + f) f (e + f + g + h) (f + h) xs ys
          (Qquadratic_signok_2 e f g h xs ys H_Qquadratic_sg_denom_nonzero) =
        (1%Z, (na, (nb, (nc, nd)), (ne, (nf, (ng, nh))), (np1, np2))));
       [ apply
          trans_eq
           with
             (Qquadratic_sign a b c d e f g h (nR xs) 
                (dL ys) H_Qquadratic_sg_denom_nonzero);
          [ apply sym_eq; apply H1; repeat split | idtac ]
       | apply
          (Qquadratic_sign_pos_2 (a + b)%Z b (a + b + c + d)%Z 
             (b + d)%Z (e + f)%Z f (e + f + g + h)%Z 
             (f + h)%Z xs ys
             (Qquadratic_signok_2 e f g h xs ys H_Qquadratic_sg_denom_nonzero)
             na nb nc nd ne nf ng nh np1 np2) ]; assumption.
    (* ~(`f = 0`/\`g = 0`/\`h = 0`) *)
    intro Hfgh'.
    case (inside_square_1_dec_inf o1 o2).    
     (* (inside_square_1 o1 o2) *)
     intro H_inside_1.
     generalize
      (Qquadratic_sign_nRdL_nRdL_8 a b c d e f g h 
         (nR xs) (dL ys) H_Qquadratic_sg_denom_nonzero).
     intros H1.
     assert
      (H_tuple_eq :
       (1%Z, (na, (nb, (nc, nd)), (ne, (nf, (ng, nh))), (np1, np2))) =
       (1%Z, (a, (b, (c, d)), (e, (f, (g, h))), (nR xs, dL ys))));
      [ apply
         trans_eq
          with
            (Qquadratic_sign a b c d e f g h (nR xs) 
               (dL ys) H_Qquadratic_sg_denom_nonzero);
         [ apply sym_eq | apply H1; discriminate || (repeat split) ];
         assumption
      | generalize
         (Qquadratic_sign_tuple_equal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
            _ _ H_tuple_eq);
         intros
          (hl,
           ((hna, (hnb, (hnc, (hnd, (hne, (hnf, (hng, hnh))))))),
           (hp1,
            hp2)));
         do 10
          match goal with
          | id1:(?X1 = ?X2) |- ?X3 => try rewrite id1; clear id1
          end ].
     left; left; left; left; left; case (inside_square_1_inf _ _ H_inside_1);
      intros (Ho1, Ho2); [ left | right ]; repeat split; first
      [ apply Z.le_refl
      | match goal with
        |  |- (0 <= ?X1)%Z => apply Zlt_le_weak; apply Zsgn_9
        |  |- (?X1 <= 0)%Z =>
            apply Zlt_le_weak; apply Zsgn_10; apply Z.opp_inj
        end; apply sym_eq; assumption
      | unfold o1 in Ho1; unfold o2 in Ho2;
         match goal with
         | id1:(2 < outside_square ?X1 ?X2 ?X3 ?X4)%Z |- 
         (0 <= ?X1)%Z =>
             apply outside_square_3 with X2 X3 X4
         | id1:(2 < outside_square ?X1 ?X2 ?X3 ?X4)%Z |- 
         (0 <= ?X2)%Z =>
             apply outside_square_4 with X1 X3 X4
         | id1:(2 < outside_square ?X1 ?X2 ?X3 ?X4)%Z |- 
         (0 <= ?X3)%Z =>
             apply outside_square_5 with X1 X2 X4
         | id1:(2 < outside_square ?X1 ?X2 ?X3 ?X4)%Z |- 
         (0 <= ?X4)%Z =>
             apply outside_square_6 with X1 X2 X3
         | id1:(outside_square ?X1 ?X2 ?X3 ?X4 < -2)%Z |- 
         (?X1 <= 0)%Z =>
             apply outside_square_7 with X2 X3 X4
         | id1:(outside_square ?X1 ?X2 ?X3 ?X4 < -2)%Z |- 
         (?X2 <= 0)%Z =>
             apply outside_square_8 with X1 X3 X4
         | id1:(outside_square ?X1 ?X2 ?X3 ?X4 < -2)%Z |- 
         (?X3 <= 0)%Z =>
             apply outside_square_9 with X1 X2 X4
         | id1:(outside_square ?X1 ?X2 ?X3 ?X4 < -2)%Z |- 
         (?X4 <= 0)%Z => apply outside_square_10 with X1 X2 X3
         end; assumption ].
      (* ~(inside_square_1 o1 o2) *)    
     intro H_inside_1'.
     case (inside_square_2_dec_inf o1 o2).    
      (* (inside_square_2 o1 o2) *)
      intro H_inside_2.
      generalize
       (Qquadratic_sign_nRdL_nRdL_9 a b c d e f g h 
          (nR xs) (dL ys) H_Qquadratic_sg_denom_nonzero).
      intros H1.
      apply False_rec.
      assert
       (H_tuple_eq :
        (1%Z, (na, (nb, (nc, nd)), (ne, (nf, (ng, nh))), (np1, np2))) =
        ((-1)%Z, (a, (b, (c, d)), (e, (f, (g, h))), (nR xs, dL ys))));
       [ apply
          trans_eq
           with
             (Qquadratic_sign a b c d e f g h (nR xs) 
                (dL ys) H_Qquadratic_sg_denom_nonzero);
          [ apply sym_eq | apply H1; discriminate || (repeat split) ];
          assumption
       | generalize
          (Qquadratic_sign_tuple_equal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
             _ _ _ H_tuple_eq);
          intros
           (hl,
            ((hna, (hnb, (hnc, (hnd, (hne, (hnf, (hng, hnh))))))),
            (hp1,
             hp2)));
          do 10
           match goal with
           | id1:(?X1 = ?X2) |- ?X3 => try rewrite id1; clear id1
           end ].
      discriminate hl.
      (*  ~(inside_square_1 o1 o2)/\~(inside_square_2 o1 o2) *)
      intros H_inside_2'. 
      generalize
       (Qquadratic_sign_nR_dL_10 a b c d e f g h (nR xs) xs 
          (dL ys) ys H_Qquadratic_sg_denom_nonzero
          (Qquadratic_signok_2 _ _ _ _ _ _ H_Qquadratic_sg_denom_nonzero)
          (refl_equal _) (refl_equal _)).
      intros H1.
      assert
       (H_tuple_eq :
        Qquadratic_sign (a + b) b (a + b + c + d) (b + d) 
          (e + f) f (e + f + g + h) (f + h) xs ys
          (Qquadratic_signok_2 e f g h xs ys H_Qquadratic_sg_denom_nonzero) =
        (1%Z, (na, (nb, (nc, nd)), (ne, (nf, (ng, nh))), (np1, np2))));
       [ apply
          trans_eq
           with
             (Qquadratic_sign a b c d e f g h (nR xs) 
                (dL ys) H_Qquadratic_sg_denom_nonzero);
          [ apply sym_eq; apply H1; repeat split | idtac ]
       | apply
          (Qquadratic_sign_pos_2 (a + b)%Z b (a + b + c + d)%Z 
             (b + d)%Z (e + f)%Z f (e + f + g + h)%Z 
             (f + h)%Z xs ys
             (Qquadratic_signok_2 e f g h xs ys H_Qquadratic_sg_denom_nonzero)
             na nb nc nd ne nf ng nh np1 np2) ]; assumption.
 (*  p1 = (nR xs) & p2 = One *)
  generalize (Qquadratic_signok_0' _ _ _ _ _ H_Qquadratic_sg_denom_nonzero).
  intros H_Qhomographic_sg_denom_nonzero.
  set
   (L3 :=
    Qhomographic_sign (a + b) (c + d) (e + f) (g + h) 
      (nR xs) H_Qhomographic_sg_denom_nonzero) in *.
  set (l1 := fst L3) in *.
  set (l2 := fst (snd L3)) in *.
  set (l3 := snd (snd L3)) in *.
  set (na_ := fst l2) in *.
  set (nb_ := fst (snd l2)) in *.
  set (nc_ := fst (snd (snd l2))) in *.
  set (nd_ := snd (snd (snd l2))) in *.
  generalize
   (Qquadratic_sign_nRdL_One a b c d e f g h (nR xs) One
      H_Qquadratic_sg_denom_nonzero l1 na_ nb_ nc_ nd_ l3
      H_Qhomographic_sg_denom_nonzero); intros H1.
  assert
   (H_tuple_eq :
    (1%Z, (na, (nb, (nc, nd)), (ne, (nf, (ng, nh))), (np1, np2))) =
    (l1, (0%Z, (na_, (0%Z, nb_)), (0%Z, (nc_, (0%Z, nd_))), (l3, One))));
   [ apply
      trans_eq
       with
         (Qquadratic_sign a b c d e f g h (nR xs) One
            H_Qquadratic_sg_denom_nonzero);
      [ apply sym_eq; assumption
      | apply H1; fold L3 in |- *; repeat (apply pair_2; try reflexivity);
         discriminate || reflexivity ]
   | generalize
      (Qquadratic_sign_tuple_equal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
         _ H_tuple_eq);
      intros
       (hl,
        ((hna, (hnb, (hnc, (hnd, (hne, (hnf, (hng, hnh))))))),
        (hp1,
         hp2)));
      do 10
       match goal with
       | id1:(?X1 = ?X2) |- ?X3 => try rewrite id1; clear id1
       end; repeat rewrite ZERO_left; repeat rewrite ZERO_right ].
  assert
   (H_sg_unfolded :
    Qhomographic_sign (a + b) (c + d) (e + f) (g + h) 
      (nR xs) H_Qhomographic_sg_denom_nonzero =
    (1%Z, (na_, (nb_, (nc_, nd_)), l3))).
  rewrite hl; fold L3 in |- *; repeat (apply pair_2; try reflexivity);
   discriminate || reflexivity.
  generalize
   (sg_pos_2 (a + b) (c + d) (e + f) (g + h) (nR xs)
      H_Qhomographic_sg_denom_nonzero na_ nb_ nc_ nd_ l3 H_sg_unfolded).
  intros [[(H_a, (H_b, (H_c, H_d)))| (H_a, (H_b, (H_c, H_d)))]| H_l3];
   [ case l3; left;
      [ right; repeat split; assumption || discriminate
      | right; repeat split; assumption || discriminate
      | left; right; repeat split ]
   | case l3;
      [ right; repeat split; assumption || discriminate
      | right; repeat split; assumption || discriminate
      | left; left; right; repeat split ]
   | left; left; right; repeat split; assumption ].

 (* p1 = (dL xs) *)
 destruct p2 as [ys| ys| ].
  (*  p1 = (dL xs) & p2 = (nR ys) *)
  case (three_integers_dec_inf b c d).  
   (* `b = 0`/\`c = 0`/\`d = 0` *)
   intros (Hb, (Hc, Hd)).
   (* Intros [Hb [Hc] Hd]. *)
   case (three_integers_dec_inf f g h).   
    (* `f = 0`/\`g = 0`/\`h = 0` *)
    intros (Hf, (Hg, Hh)).
    generalize
     (Qquadratic_sign_nRdL_nRdL_1 a b c d e f g h (dL xs) 
        (nR ys) H_Qquadratic_sg_denom_nonzero).
    intros H1.
    assert
     (H_tuple_eq :
      (1%Z, (na, (nb, (nc, nd)), (ne, (nf, (ng, nh))), (np1, np2))) =
      ((Z.sgn a * Z.sgn e)%Z,
      (a, (b, (c, d)), (e, (f, (g, h))), (dL xs, nR ys))));
     [ apply
        trans_eq
         with
           (Qquadratic_sign a b c d e f g h (dL xs) 
              (nR ys) H_Qquadratic_sg_denom_nonzero);
        [ apply sym_eq | apply H1; discriminate || (repeat split) ];
        assumption
     | generalize
        (Qquadratic_sign_tuple_equal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
           _ _ H_tuple_eq);
        intros
         (hl,
          ((hna, (hnb, (hnc, (hnd, (hne, (hnf, (hng, hnh))))))),
          (hp1,
           hp2)));
        do 10
         match goal with
         | id1:(?X1 = ?X2) |- ?X3 => try rewrite id1; clear id1
         end ].
    left; left; left; left; left; rewrite <- Zsgn_15 in hl.
    case (Zsgn_16 _ _ (sym_eq hl)); intros (Ha, He); [ left | right ];
     repeat split;
     repeat
      match goal with
      | id1:(?X1 = 0%Z) |- ?X2 => rewrite id1; clear id1
      end; first [ apply Z.le_refl | apply Zlt_le_weak ]; 
     assumption.
    (* ~(`f = 0`/\`g = 0`/\`h = 0`) *)
    intros H_fgh'.
    case (Z_lt_dec 2 o2).
     (*  `2 < o2` *)
     intro Ho2.
     generalize
      (Qquadratic_sign_nRdL_nRdL_2 a b c d e f g h 
         (dL xs) (nR ys) H_Qquadratic_sg_denom_nonzero).
     intros H1.
     assert
      (H_tuple_eq :
       (1%Z, (na, (nb, (nc, nd)), (ne, (nf, (ng, nh))), (np1, np2))) =
       (Z.sgn a, (a, (b, (c, d)), (e, (f, (g, h))), (dL xs, nR ys))));
      [ apply
         trans_eq
          with
            (Qquadratic_sign a b c d e f g h (dL xs) 
               (nR ys) H_Qquadratic_sg_denom_nonzero);
         [ apply sym_eq | apply H1; discriminate || (repeat split) ];
         assumption
      | generalize
         (Qquadratic_sign_tuple_equal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
            _ _ H_tuple_eq);
         intros
          (hl,
           ((hna, (hnb, (hnc, (hnd, (hne, (hnf, (hng, hnh))))))),
           (hp1,
            hp2)));
         do 10
          match goal with
          | id1:(?X1 = ?X2) |- ?X3 => try rewrite id1; clear id1
          end ].
     left; left; left; left; left; left; repeat split;
      repeat
       match goal with
       | id1:(?X1 = 0%Z) |- ?X2 => rewrite id1; clear id1
       end; first
      [ apply Z.le_refl
      | match goal with
        |  |- (0 <= ?X1)%Z => apply Zlt_le_weak; apply Zsgn_9
        |  |- (?X1 <= 0)%Z =>
            apply Zlt_le_weak; apply Zsgn_10; apply Z.opp_inj
        end; apply sym_eq; assumption
      | unfold o2 in Ho2;
         match goal with
         | id1:(2 < outside_square ?X1 ?X2 ?X3 ?X4)%Z |- 
         (0 <= ?X1)%Z =>
             apply outside_square_3 with X2 X3 X4
         | id1:(2 < outside_square ?X1 ?X2 ?X3 ?X4)%Z |- 
         (0 <= ?X2)%Z =>
             apply outside_square_4 with X1 X3 X4
         | id1:(2 < outside_square ?X1 ?X2 ?X3 ?X4)%Z |- 
         (0 <= ?X3)%Z =>
             apply outside_square_5 with X1 X2 X4
         | id1:(2 < outside_square ?X1 ?X2 ?X3 ?X4)%Z |- 
         (0 <= ?X4)%Z =>
             apply outside_square_6 with X1 X2 X3
         | id1:(outside_square ?X1 ?X2 ?X3 ?X4 < -2)%Z |- 
         (?X1 <= 0)%Z =>
             apply outside_square_7 with X2 X3 X4
         | id1:(outside_square ?X1 ?X2 ?X3 ?X4 < -2)%Z |- 
         (?X2 <= 0)%Z =>
             apply outside_square_8 with X1 X3 X4
         | id1:(outside_square ?X1 ?X2 ?X3 ?X4 < -2)%Z |- 
         (?X3 <= 0)%Z =>
             apply outside_square_9 with X1 X2 X4
         | id1:(outside_square ?X1 ?X2 ?X3 ?X4 < -2)%Z |- 
         (?X4 <= 0)%Z => apply outside_square_10 with X1 X2 X3
         end; assumption ].
     
     (*  ~`2 < o2` *)
     case (Z_lt_dec o2 (-2)).     
     (* `(-2) < o2` *)
      intros Ho2' Ho2.
      generalize
       (Qquadratic_sign_nRdL_nRdL_3 a b c d e f g h 
          (dL xs) (nR ys) H_Qquadratic_sg_denom_nonzero).
      intros H1.
      assert
       (H_tuple_eq :
        (1%Z, (na, (nb, (nc, nd)), (ne, (nf, (ng, nh))), (np1, np2))) =
        ((- Z.sgn a)%Z, (a, (b, (c, d)), (e, (f, (g, h))), (dL xs, nR ys))));
       [ apply
          trans_eq
           with
             (Qquadratic_sign a b c d e f g h (dL xs) 
                (nR ys) H_Qquadratic_sg_denom_nonzero);
          [ apply sym_eq | apply H1; discriminate || (repeat split) ];
          assumption
       | generalize
          (Qquadratic_sign_tuple_equal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
             _ _ _ H_tuple_eq);
          intros
           (hl,
            ((hna, (hnb, (hnc, (hnd, (hne, (hnf, (hng, hnh))))))),
            (hp1,
             hp2)));
          do 10
           match goal with
           | id1:(?X1 = ?X2) |- ?X3 => try rewrite id1; clear id1
           end ].
      left; left; left; left; left; right; repeat split;
       repeat
        match goal with
        | id1:(?X1 = 0%Z) |- ?X2 => rewrite id1; clear id1
        end; first
       [ apply Z.le_refl
       | match goal with
         |  |- (0 <= ?X1)%Z => apply Zlt_le_weak; apply Zsgn_9
         |  |- (?X1 <= 0)%Z =>
             apply Zlt_le_weak; apply Zsgn_10; apply Z.opp_inj
         end; apply sym_eq; assumption
       | unfold o2 in Ho2';
          match goal with
          | id1:(2 < outside_square ?X1 ?X2 ?X3 ?X4)%Z |- 
          (0 <= ?X1)%Z =>
              apply outside_square_3 with X2 X3 X4
          | id1:(2 < outside_square ?X1 ?X2 ?X3 ?X4)%Z |- 
          (0 <= ?X2)%Z =>
              apply outside_square_4 with X1 X3 X4
          | id1:(2 < outside_square ?X1 ?X2 ?X3 ?X4)%Z |- 
          (0 <= ?X3)%Z =>
              apply outside_square_5 with X1 X2 X4
          | id1:(2 < outside_square ?X1 ?X2 ?X3 ?X4)%Z |- 
          (0 <= ?X4)%Z =>
              apply outside_square_6 with X1 X2 X3
          | id1:(outside_square ?X1 ?X2 ?X3 ?X4 < -2)%Z |- 
          (?X1 <= 0)%Z =>
              apply outside_square_7 with X2 X3 X4
          | id1:(outside_square ?X1 ?X2 ?X3 ?X4 < -2)%Z |- 
          (?X2 <= 0)%Z =>
              apply outside_square_8 with X1 X3 X4
          | id1:(outside_square ?X1 ?X2 ?X3 ?X4 < -2)%Z |- 
          (?X3 <= 0)%Z =>
              apply outside_square_9 with X1 X2 X4
          | id1:(outside_square ?X1 ?X2 ?X3 ?X4 < -2)%Z |- 
          (?X4 <= 0)%Z => apply outside_square_10 with X1 X2 X3
          end; assumption ].
     (* ~`o1 < (-2)` /\ ~`2 < o1` *)
      intros Ho2' Ho2.
      generalize
       (Qquadratic_sign_dL_nR_4 a b c d e f g h (dL xs) xs 
          (nR ys) ys H_Qquadratic_sg_denom_nonzero
          (Qquadratic_signok_3 _ _ _ _ _ _ H_Qquadratic_sg_denom_nonzero)
          (refl_equal _) (refl_equal _)).
      intros H1.
      assert
       (H_tuple_eq :
        Qquadratic_sign (a + c) (a + b + c + d) c (c + d) 
          (e + g) (e + f + g + h) g (g + h) xs ys
          (Qquadratic_signok_3 e f g h xs ys H_Qquadratic_sg_denom_nonzero) =
        (1%Z, (na, (nb, (nc, nd)), (ne, (nf, (ng, nh))), (np1, np2))));
       [ apply
          trans_eq
           with
             (Qquadratic_sign a b c d e f g h (dL xs) 
                (nR ys) H_Qquadratic_sg_denom_nonzero);
          [ apply sym_eq; apply H1; repeat split | idtac ]
       | apply
          (Qquadratic_sign_pos_2 (a + c)%Z (a + b + c + d)%Z c 
             (c + d)%Z (e + g)%Z (e + f + g + h)%Z g 
             (g + h)%Z xs ys
             (Qquadratic_signok_3 e f g h xs ys H_Qquadratic_sg_denom_nonzero)
             na nb nc nd ne nf ng nh np1 np2) ]; assumption.
   (* ~ `b = 0`/\`c = 0`/\`d = 0` *)
   intros Hbcd'.
   (* Intros [Hb [Hc] Hd]. *)
   case (three_integers_dec_inf f g h).   
    (* `f = 0`/\`g = 0`/\`h = 0` *)
    intros (Hf, (Hg, Hh)).
    case (Z_lt_dec 2 o1).
     (*  `2 < o1` *)
     intro Ho1.
     generalize
      (Qquadratic_sign_nRdL_nRdL_5 a b c d e f g h 
         (dL xs) (nR ys) H_Qquadratic_sg_denom_nonzero).
     intros H1.
     assert
      (H_tuple_eq :
       (1%Z, (na, (nb, (nc, nd)), (ne, (nf, (ng, nh))), (np1, np2))) =
       (Z.sgn e, (a, (b, (c, d)), (e, (f, (g, h))), (dL xs, nR ys))));
      [ apply
         trans_eq
          with
            (Qquadratic_sign a b c d e f g h (dL xs) 
               (nR ys) H_Qquadratic_sg_denom_nonzero);
         [ apply sym_eq | apply H1; discriminate || (repeat split) ];
         assumption
      | generalize
         (Qquadratic_sign_tuple_equal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
            _ _ H_tuple_eq);
         intros
          (hl,
           ((hna, (hnb, (hnc, (hnd, (hne, (hnf, (hng, hnh))))))),
           (hp1,
            hp2)));
         do 10
          match goal with
          | id1:(?X1 = ?X2) |- ?X3 => try rewrite id1; clear id1
          end ].
     left; left; left; left; left; left; repeat split;
      repeat
       match goal with
       | id1:(?X1 = 0%Z) |- ?X2 => rewrite id1; clear id1
       end; first
      [ apply Z.le_refl
      | match goal with
        |  |- (0 <= ?X1)%Z => apply Zlt_le_weak; apply Zsgn_9
        |  |- (?X1 <= 0)%Z =>
            apply Zlt_le_weak; apply Zsgn_10; apply Z.opp_inj
        end; apply sym_eq; assumption
      | unfold o1 in Ho1;
         match goal with
         | id1:(2 < outside_square ?X1 ?X2 ?X3 ?X4)%Z |- 
         (0 <= ?X1)%Z =>
             apply outside_square_3 with X2 X3 X4
         | id1:(2 < outside_square ?X1 ?X2 ?X3 ?X4)%Z |- 
         (0 <= ?X2)%Z =>
             apply outside_square_4 with X1 X3 X4
         | id1:(2 < outside_square ?X1 ?X2 ?X3 ?X4)%Z |- 
         (0 <= ?X3)%Z =>
             apply outside_square_5 with X1 X2 X4
         | id1:(2 < outside_square ?X1 ?X2 ?X3 ?X4)%Z |- 
         (0 <= ?X4)%Z =>
             apply outside_square_6 with X1 X2 X3
         | id1:(outside_square ?X1 ?X2 ?X3 ?X4 < -2)%Z |- 
         (?X1 <= 0)%Z =>
             apply outside_square_7 with X2 X3 X4
         | id1:(outside_square ?X1 ?X2 ?X3 ?X4 < -2)%Z |- 
         (?X2 <= 0)%Z =>
             apply outside_square_8 with X1 X3 X4
         | id1:(outside_square ?X1 ?X2 ?X3 ?X4 < -2)%Z |- 
         (?X3 <= 0)%Z =>
             apply outside_square_9 with X1 X2 X4
         | id1:(outside_square ?X1 ?X2 ?X3 ?X4 < -2)%Z |- 
         (?X4 <= 0)%Z => apply outside_square_10 with X1 X2 X3
         end; assumption ].
     (*  ~`2 < o1` *)
     case (Z_lt_dec o1 (-2)).
      (* `(-2) < o1` *)
      intros Ho1' Ho1.
      generalize
       (Qquadratic_sign_nRdL_nRdL_6 a b c d e f g h 
          (dL xs) (nR ys) H_Qquadratic_sg_denom_nonzero).
      intros H1.
      assert
       (H_tuple_eq :
        (1%Z, (na, (nb, (nc, nd)), (ne, (nf, (ng, nh))), (np1, np2))) =
        ((- Z.sgn e)%Z, (a, (b, (c, d)), (e, (f, (g, h))), (dL xs, nR ys))));
       [ apply
          trans_eq
           with
             (Qquadratic_sign a b c d e f g h (dL xs) 
                (nR ys) H_Qquadratic_sg_denom_nonzero);
          [ apply sym_eq | apply H1; discriminate || (repeat split) ];
          assumption
       | generalize
          (Qquadratic_sign_tuple_equal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
             _ _ _ H_tuple_eq);
          intros
           (hl,
            ((hna, (hnb, (hnc, (hnd, (hne, (hnf, (hng, hnh))))))),
            (hp1,
             hp2)));
          do 10
           match goal with
           | id1:(?X1 = ?X2) |- ?X3 => try rewrite id1; clear id1
           end ].
      left; left; left; left; left; right; repeat split;
       repeat
        match goal with
        | id1:(?X1 = 0%Z) |- ?X2 => rewrite id1; clear id1
        end; first
       [ apply Z.le_refl
       | match goal with
         |  |- (0 <= ?X1)%Z => apply Zlt_le_weak; apply Zsgn_9
         |  |- (?X1 <= 0)%Z =>
             apply Zlt_le_weak; apply Zsgn_10; apply Z.opp_inj
         end; apply sym_eq; assumption
       | unfold o1 in Ho1';
          match goal with
          | id1:(2 < outside_square ?X1 ?X2 ?X3 ?X4)%Z |- 
          (0 <= ?X1)%Z =>
              apply outside_square_3 with X2 X3 X4
          | id1:(2 < outside_square ?X1 ?X2 ?X3 ?X4)%Z |- 
          (0 <= ?X2)%Z =>
              apply outside_square_4 with X1 X3 X4
          | id1:(2 < outside_square ?X1 ?X2 ?X3 ?X4)%Z |- 
          (0 <= ?X3)%Z =>
              apply outside_square_5 with X1 X2 X4
          | id1:(2 < outside_square ?X1 ?X2 ?X3 ?X4)%Z |- 
          (0 <= ?X4)%Z =>
              apply outside_square_6 with X1 X2 X3
          | id1:(outside_square ?X1 ?X2 ?X3 ?X4 < -2)%Z |- 
          (?X1 <= 0)%Z =>
              apply outside_square_7 with X2 X3 X4
          | id1:(outside_square ?X1 ?X2 ?X3 ?X4 < -2)%Z |- 
          (?X2 <= 0)%Z =>
              apply outside_square_8 with X1 X3 X4
          | id1:(outside_square ?X1 ?X2 ?X3 ?X4 < -2)%Z |- 
          (?X3 <= 0)%Z =>
              apply outside_square_9 with X1 X2 X4
          | id1:(outside_square ?X1 ?X2 ?X3 ?X4 < -2)%Z |- 
          (?X4 <= 0)%Z => apply outside_square_10 with X1 X2 X3
          end; assumption ].

      (* ~`o1 < (-2)` /\ ~`2 < o1` *)
      intros Ho2' Ho2.
      generalize
       (Qquadratic_sign_dL_nR_7 a b c d e f g h (dL xs) xs 
          (nR ys) ys H_Qquadratic_sg_denom_nonzero
          (Qquadratic_signok_3 _ _ _ _ _ _ H_Qquadratic_sg_denom_nonzero)
          (refl_equal _) (refl_equal _)).
      intros H1.
      assert
       (H_tuple_eq :
        Qquadratic_sign (a + c) (a + b + c + d) c (c + d) 
          (e + g) (e + f + g + h) g (g + h) xs ys
          (Qquadratic_signok_3 e f g h xs ys H_Qquadratic_sg_denom_nonzero) =
        (1%Z, (na, (nb, (nc, nd)), (ne, (nf, (ng, nh))), (np1, np2))));
       [ apply
          trans_eq
           with
             (Qquadratic_sign a b c d e f g h (dL xs) 
                (nR ys) H_Qquadratic_sg_denom_nonzero);
          [ apply sym_eq; apply H1; repeat split | idtac ]
       | apply
          (Qquadratic_sign_pos_2 (a + c)%Z (a + b + c + d)%Z c 
             (c + d)%Z (e + g)%Z (e + f + g + h)%Z g 
             (g + h)%Z xs ys
             (Qquadratic_signok_3 e f g h xs ys H_Qquadratic_sg_denom_nonzero)
             na nb nc nd ne nf ng nh np1 np2) ]; assumption.
    (* ~(`f = 0`/\`g = 0`/\`h = 0`) *)
    intro Hfgh'.
    case (inside_square_1_dec_inf o1 o2).    
     (* (inside_square_1 o1 o2) *)
     intro H_inside_1.
     generalize
      (Qquadratic_sign_nRdL_nRdL_8 a b c d e f g h 
         (dL xs) (nR ys) H_Qquadratic_sg_denom_nonzero).
     intros H1.
     assert
      (H_tuple_eq :
       (1%Z, (na, (nb, (nc, nd)), (ne, (nf, (ng, nh))), (np1, np2))) =
       (1%Z, (a, (b, (c, d)), (e, (f, (g, h))), (dL xs, nR ys))));
      [ apply
         trans_eq
          with
            (Qquadratic_sign a b c d e f g h (dL xs) 
               (nR ys) H_Qquadratic_sg_denom_nonzero);
         [ apply sym_eq | apply H1; discriminate || (repeat split) ];
         assumption
      | generalize
         (Qquadratic_sign_tuple_equal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
            _ _ H_tuple_eq);
         intros
          (hl,
           ((hna, (hnb, (hnc, (hnd, (hne, (hnf, (hng, hnh))))))),
           (hp1,
            hp2)));
         do 10
          match goal with
          | id1:(?X1 = ?X2) |- ?X3 => try rewrite id1; clear id1
          end ].
     left; left; left; left; left; case (inside_square_1_inf _ _ H_inside_1);
      intros (Ho1, Ho2); [ left | right ]; repeat split; first
      [ apply Z.le_refl
      | match goal with
        |  |- (0 <= ?X1)%Z => apply Zlt_le_weak; apply Zsgn_9
        |  |- (?X1 <= 0)%Z =>
            apply Zlt_le_weak; apply Zsgn_10; apply Z.opp_inj
        end; apply sym_eq; assumption
      | unfold o1 in Ho1; unfold o2 in Ho2;
         match goal with
         | id1:(2 < outside_square ?X1 ?X2 ?X3 ?X4)%Z |- 
         (0 <= ?X1)%Z =>
             apply outside_square_3 with X2 X3 X4
         | id1:(2 < outside_square ?X1 ?X2 ?X3 ?X4)%Z |- 
         (0 <= ?X2)%Z =>
             apply outside_square_4 with X1 X3 X4
         | id1:(2 < outside_square ?X1 ?X2 ?X3 ?X4)%Z |- 
         (0 <= ?X3)%Z =>
             apply outside_square_5 with X1 X2 X4
         | id1:(2 < outside_square ?X1 ?X2 ?X3 ?X4)%Z |- 
         (0 <= ?X4)%Z =>
             apply outside_square_6 with X1 X2 X3
         | id1:(outside_square ?X1 ?X2 ?X3 ?X4 < -2)%Z |- 
         (?X1 <= 0)%Z =>
             apply outside_square_7 with X2 X3 X4
         | id1:(outside_square ?X1 ?X2 ?X3 ?X4 < -2)%Z |- 
         (?X2 <= 0)%Z =>
             apply outside_square_8 with X1 X3 X4
         | id1:(outside_square ?X1 ?X2 ?X3 ?X4 < -2)%Z |- 
         (?X3 <= 0)%Z =>
             apply outside_square_9 with X1 X2 X4
         | id1:(outside_square ?X1 ?X2 ?X3 ?X4 < -2)%Z |- 
         (?X4 <= 0)%Z => apply outside_square_10 with X1 X2 X3
         end; assumption ].
      (* ~(inside_square_1 o1 o2) *)    
     intro H_inside_1'.
     case (inside_square_2_dec_inf o1 o2).    
      (* (inside_square_2 o1 o2) *)
      intro H_inside_2.
      generalize
       (Qquadratic_sign_nRdL_nRdL_9 a b c d e f g h 
          (dL xs) (nR ys) H_Qquadratic_sg_denom_nonzero).
      intros H1.
      apply False_rec.
      assert
       (H_tuple_eq :
        (1%Z, (na, (nb, (nc, nd)), (ne, (nf, (ng, nh))), (np1, np2))) =
        ((-1)%Z, (a, (b, (c, d)), (e, (f, (g, h))), (dL xs, nR ys))));
       [ apply
          trans_eq
           with
             (Qquadratic_sign a b c d e f g h (dL xs) 
                (nR ys) H_Qquadratic_sg_denom_nonzero);
          [ apply sym_eq | apply H1; discriminate || (repeat split) ];
          assumption
       | generalize
          (Qquadratic_sign_tuple_equal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
             _ _ _ H_tuple_eq);
          intros
           (hl,
            ((hna, (hnb, (hnc, (hnd, (hne, (hnf, (hng, hnh))))))),
            (hp1,
             hp2)));
          do 10
           match goal with
           | id1:(?X1 = ?X2) |- ?X3 => try rewrite id1; clear id1
           end ].
      discriminate hl.
      (*  ~(inside_square_1 o1 o2)/\~(inside_square_2 o1 o2) *)
      intros H_inside_2'. 
      generalize
       (Qquadratic_sign_dL_nR_10 a b c d e f g h (dL xs) xs 
          (nR ys) ys H_Qquadratic_sg_denom_nonzero
          (Qquadratic_signok_3 _ _ _ _ _ _ H_Qquadratic_sg_denom_nonzero)
          (refl_equal _) (refl_equal _)).
      intros H1.
      assert
       (H_tuple_eq :
        Qquadratic_sign (a + c) (a + b + c + d) c (c + d) 
          (e + g) (e + f + g + h) g (g + h) xs ys
          (Qquadratic_signok_3 e f g h xs ys H_Qquadratic_sg_denom_nonzero) =
        (1%Z, (na, (nb, (nc, nd)), (ne, (nf, (ng, nh))), (np1, np2))));
       [ apply
          trans_eq
           with
             (Qquadratic_sign a b c d e f g h (dL xs) 
                (nR ys) H_Qquadratic_sg_denom_nonzero);
          [ apply sym_eq; apply H1; repeat split | idtac ]
       | apply
          (Qquadratic_sign_pos_2 (a + c)%Z (a + b + c + d)%Z c 
             (c + d)%Z (e + g)%Z (e + f + g + h)%Z g 
             (g + h)%Z xs ys
             (Qquadratic_signok_3 e f g h xs ys H_Qquadratic_sg_denom_nonzero)
             na nb nc nd ne nf ng nh np1 np2) ]; assumption.

 (*  p1 = (dL xs) & p2 = (dL ys) *)
  case (three_integers_dec_inf b c d).  
   (* `b = 0`/\`c = 0`/\`d = 0` *)
   intros (Hb, (Hc, Hd)).
   (* Intros [Hb [Hc] Hd]. *)
   case (three_integers_dec_inf f g h).   
    (* `f = 0`/\`g = 0`/\`h = 0` *)
    intros (Hf, (Hg, Hh)).
    generalize
     (Qquadratic_sign_nRdL_nRdL_1 a b c d e f g h (dL xs) 
        (dL ys) H_Qquadratic_sg_denom_nonzero).
    intros H1.
    assert
     (H_tuple_eq :
      (1%Z, (na, (nb, (nc, nd)), (ne, (nf, (ng, nh))), (np1, np2))) =
      ((Z.sgn a * Z.sgn e)%Z,
      (a, (b, (c, d)), (e, (f, (g, h))), (dL xs, dL ys))));
     [ apply
        trans_eq
         with
           (Qquadratic_sign a b c d e f g h (dL xs) 
              (dL ys) H_Qquadratic_sg_denom_nonzero);
        [ apply sym_eq | apply H1; discriminate || (repeat split) ];
        assumption
     | generalize
        (Qquadratic_sign_tuple_equal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
           _ _ H_tuple_eq);
        intros
         (hl,
          ((hna, (hnb, (hnc, (hnd, (hne, (hnf, (hng, hnh))))))),
          (hp1,
           hp2)));
        do 10
         match goal with
         | id1:(?X1 = ?X2) |- ?X3 => try rewrite id1; clear id1
         end ].
    left; left; left; left; left; rewrite <- Zsgn_15 in hl.
    case (Zsgn_16 _ _ (sym_eq hl)); intros (Ha, He); [ left | right ];
     repeat split;
     repeat
      match goal with
      | id1:(?X1 = 0%Z) |- ?X2 => rewrite id1; clear id1
      end; first [ apply Z.le_refl | apply Zlt_le_weak ]; 
     assumption.
    (* ~(`f = 0`/\`g = 0`/\`h = 0`) *)
    intros H_fgh'.
    case (Z_lt_dec 2 o2).
     (*  `2 < o2` *)
     intro Ho2.
     generalize
      (Qquadratic_sign_nRdL_nRdL_2 a b c d e f g h 
         (dL xs) (dL ys) H_Qquadratic_sg_denom_nonzero).
     intros H1.
     assert
      (H_tuple_eq :
       (1%Z, (na, (nb, (nc, nd)), (ne, (nf, (ng, nh))), (np1, np2))) =
       (Z.sgn a, (a, (b, (c, d)), (e, (f, (g, h))), (dL xs, dL ys))));
      [ apply
         trans_eq
          with
            (Qquadratic_sign a b c d e f g h (dL xs) 
               (dL ys) H_Qquadratic_sg_denom_nonzero);
         [ apply sym_eq | apply H1; discriminate || (repeat split) ];
         assumption
      | generalize
         (Qquadratic_sign_tuple_equal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
            _ _ H_tuple_eq);
         intros
          (hl,
           ((hna, (hnb, (hnc, (hnd, (hne, (hnf, (hng, hnh))))))),
           (hp1,
            hp2)));
         do 10
          match goal with
          | id1:(?X1 = ?X2) |- ?X3 => try rewrite id1; clear id1
          end ].
     left; left; left; left; left; left; repeat split;
      repeat
       match goal with
       | id1:(?X1 = 0%Z) |- ?X2 => rewrite id1; clear id1
       end; first
      [ apply Z.le_refl
      | match goal with
        |  |- (0 <= ?X1)%Z => apply Zlt_le_weak; apply Zsgn_9
        |  |- (?X1 <= 0)%Z =>
            apply Zlt_le_weak; apply Zsgn_10; apply Z.opp_inj
        end; apply sym_eq; assumption
      | unfold o2 in Ho2;
         match goal with
         | id1:(2 < outside_square ?X1 ?X2 ?X3 ?X4)%Z |- 
         (0 <= ?X1)%Z =>
             apply outside_square_3 with X2 X3 X4
         | id1:(2 < outside_square ?X1 ?X2 ?X3 ?X4)%Z |- 
         (0 <= ?X2)%Z =>
             apply outside_square_4 with X1 X3 X4
         | id1:(2 < outside_square ?X1 ?X2 ?X3 ?X4)%Z |- 
         (0 <= ?X3)%Z =>
             apply outside_square_5 with X1 X2 X4
         | id1:(2 < outside_square ?X1 ?X2 ?X3 ?X4)%Z |- 
         (0 <= ?X4)%Z =>
             apply outside_square_6 with X1 X2 X3
         | id1:(outside_square ?X1 ?X2 ?X3 ?X4 < -2)%Z |- 
         (?X1 <= 0)%Z =>
             apply outside_square_7 with X2 X3 X4
         | id1:(outside_square ?X1 ?X2 ?X3 ?X4 < -2)%Z |- 
         (?X2 <= 0)%Z =>
             apply outside_square_8 with X1 X3 X4
         | id1:(outside_square ?X1 ?X2 ?X3 ?X4 < -2)%Z |- 
         (?X3 <= 0)%Z =>
             apply outside_square_9 with X1 X2 X4
         | id1:(outside_square ?X1 ?X2 ?X3 ?X4 < -2)%Z |- 
         (?X4 <= 0)%Z => apply outside_square_10 with X1 X2 X3
         end; assumption ].
     
     (*  ~`2 < o2` *)
     case (Z_lt_dec o2 (-2)).     
     (* `(-2) < o2` *)
      intros Ho2' Ho2.
      generalize
       (Qquadratic_sign_nRdL_nRdL_3 a b c d e f g h 
          (dL xs) (dL ys) H_Qquadratic_sg_denom_nonzero).
      intros H1.
      assert
       (H_tuple_eq :
        (1%Z, (na, (nb, (nc, nd)), (ne, (nf, (ng, nh))), (np1, np2))) =
        ((- Z.sgn a)%Z, (a, (b, (c, d)), (e, (f, (g, h))), (dL xs, dL ys))));
       [ apply
          trans_eq
           with
             (Qquadratic_sign a b c d e f g h (dL xs) 
                (dL ys) H_Qquadratic_sg_denom_nonzero);
          [ apply sym_eq | apply H1; discriminate || (repeat split) ];
          assumption
       | generalize
          (Qquadratic_sign_tuple_equal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
             _ _ _ H_tuple_eq);
          intros
           (hl,
            ((hna, (hnb, (hnc, (hnd, (hne, (hnf, (hng, hnh))))))),
            (hp1,
             hp2)));
          do 10
           match goal with
           | id1:(?X1 = ?X2) |- ?X3 => try rewrite id1; clear id1
           end ].
      left; left; left; left; left; right; repeat split;
       repeat
        match goal with
        | id1:(?X1 = 0%Z) |- ?X2 => rewrite id1; clear id1
        end; first
       [ apply Z.le_refl
       | match goal with
         |  |- (0 <= ?X1)%Z => apply Zlt_le_weak; apply Zsgn_9
         |  |- (?X1 <= 0)%Z =>
             apply Zlt_le_weak; apply Zsgn_10; apply Z.opp_inj
         end; apply sym_eq; assumption
       | unfold o2 in Ho2';
          match goal with
          | id1:(2 < outside_square ?X1 ?X2 ?X3 ?X4)%Z |- 
          (0 <= ?X1)%Z =>
              apply outside_square_3 with X2 X3 X4
          | id1:(2 < outside_square ?X1 ?X2 ?X3 ?X4)%Z |- 
          (0 <= ?X2)%Z =>
              apply outside_square_4 with X1 X3 X4
          | id1:(2 < outside_square ?X1 ?X2 ?X3 ?X4)%Z |- 
          (0 <= ?X3)%Z =>
              apply outside_square_5 with X1 X2 X4
          | id1:(2 < outside_square ?X1 ?X2 ?X3 ?X4)%Z |- 
          (0 <= ?X4)%Z =>
              apply outside_square_6 with X1 X2 X3
          | id1:(outside_square ?X1 ?X2 ?X3 ?X4 < -2)%Z |- 
          (?X1 <= 0)%Z =>
              apply outside_square_7 with X2 X3 X4
          | id1:(outside_square ?X1 ?X2 ?X3 ?X4 < -2)%Z |- 
          (?X2 <= 0)%Z =>
              apply outside_square_8 with X1 X3 X4
          | id1:(outside_square ?X1 ?X2 ?X3 ?X4 < -2)%Z |- 
          (?X3 <= 0)%Z =>
              apply outside_square_9 with X1 X2 X4
          | id1:(outside_square ?X1 ?X2 ?X3 ?X4 < -2)%Z |- 
          (?X4 <= 0)%Z => apply outside_square_10 with X1 X2 X3
          end; assumption ].
     (* ~`o1 < (-2)` /\ ~`2 < o1` *)
      intros Ho2' Ho2.
      generalize
       (Qquadratic_sign_dL_dL_4 a b c d e f g h (dL xs) xs 
          (dL ys) ys H_Qquadratic_sg_denom_nonzero
          (Qquadratic_signok_4 _ _ _ _ _ _ H_Qquadratic_sg_denom_nonzero)
          (refl_equal _) (refl_equal _)).
      intros H1.
      assert
       (H_tuple_eq :
        Qquadratic_sign (a + b + c + d) (b + d) (c + d) d 
          (e + f + g + h) (f + h) (g + h) h xs ys
          (Qquadratic_signok_4 e f g h xs ys H_Qquadratic_sg_denom_nonzero) =
        (1%Z, (na, (nb, (nc, nd)), (ne, (nf, (ng, nh))), (np1, np2))));
       [ apply
          trans_eq
           with
             (Qquadratic_sign a b c d e f g h (dL xs) 
                (dL ys) H_Qquadratic_sg_denom_nonzero);
          [ apply sym_eq; apply H1; repeat split | idtac ]
       | apply
          (Qquadratic_sign_pos_2 (a + b + c + d)%Z 
             (b + d)%Z (c + d)%Z d (e + f + g + h)%Z 
             (f + h)%Z (g + h)%Z h xs ys
             (Qquadratic_signok_4 e f g h xs ys H_Qquadratic_sg_denom_nonzero)
             na nb nc nd ne nf ng nh np1 np2) ]; assumption.
   (* ~ `b = 0`/\`c = 0`/\`d = 0` *)
   intros Hbcd'.
   (* Intros [Hb [Hc] Hd]. *)
   case (three_integers_dec_inf f g h).   
    (* `f = 0`/\`g = 0`/\`h = 0` *)
    intros (Hf, (Hg, Hh)).
    case (Z_lt_dec 2 o1).
     (*  `2 < o1` *)
     intro Ho1.
     generalize
      (Qquadratic_sign_nRdL_nRdL_5 a b c d e f g h 
         (dL xs) (dL ys) H_Qquadratic_sg_denom_nonzero).
     intros H1.
     assert
      (H_tuple_eq :
       (1%Z, (na, (nb, (nc, nd)), (ne, (nf, (ng, nh))), (np1, np2))) =
       (Z.sgn e, (a, (b, (c, d)), (e, (f, (g, h))), (dL xs, dL ys))));
      [ apply
         trans_eq
          with
            (Qquadratic_sign a b c d e f g h (dL xs) 
               (dL ys) H_Qquadratic_sg_denom_nonzero);
         [ apply sym_eq | apply H1; discriminate || (repeat split) ];
         assumption
      | generalize
         (Qquadratic_sign_tuple_equal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
            _ _ H_tuple_eq);
         intros
          (hl,
           ((hna, (hnb, (hnc, (hnd, (hne, (hnf, (hng, hnh))))))),
           (hp1,
            hp2)));
         do 10
          match goal with
          | id1:(?X1 = ?X2) |- ?X3 => try rewrite id1; clear id1
          end ].
     left; left; left; left; left; left; repeat split;
      repeat
       match goal with
       | id1:(?X1 = 0%Z) |- ?X2 => rewrite id1; clear id1
       end; first
      [ apply Z.le_refl
      | match goal with
        |  |- (0 <= ?X1)%Z => apply Zlt_le_weak; apply Zsgn_9
        |  |- (?X1 <= 0)%Z =>
            apply Zlt_le_weak; apply Zsgn_10; apply Z.opp_inj
        end; apply sym_eq; assumption
      | unfold o1 in Ho1;
         match goal with
         | id1:(2 < outside_square ?X1 ?X2 ?X3 ?X4)%Z |- 
         (0 <= ?X1)%Z =>
             apply outside_square_3 with X2 X3 X4
         | id1:(2 < outside_square ?X1 ?X2 ?X3 ?X4)%Z |- 
         (0 <= ?X2)%Z =>
             apply outside_square_4 with X1 X3 X4
         | id1:(2 < outside_square ?X1 ?X2 ?X3 ?X4)%Z |- 
         (0 <= ?X3)%Z =>
             apply outside_square_5 with X1 X2 X4
         | id1:(2 < outside_square ?X1 ?X2 ?X3 ?X4)%Z |- 
         (0 <= ?X4)%Z =>
             apply outside_square_6 with X1 X2 X3
         | id1:(outside_square ?X1 ?X2 ?X3 ?X4 < -2)%Z |- 
         (?X1 <= 0)%Z =>
             apply outside_square_7 with X2 X3 X4
         | id1:(outside_square ?X1 ?X2 ?X3 ?X4 < -2)%Z |- 
         (?X2 <= 0)%Z =>
             apply outside_square_8 with X1 X3 X4
         | id1:(outside_square ?X1 ?X2 ?X3 ?X4 < -2)%Z |- 
         (?X3 <= 0)%Z =>
             apply outside_square_9 with X1 X2 X4
         | id1:(outside_square ?X1 ?X2 ?X3 ?X4 < -2)%Z |- 
         (?X4 <= 0)%Z => apply outside_square_10 with X1 X2 X3
         end; assumption ].
     (*  ~`2 < o1` *)
     case (Z_lt_dec o1 (-2)).
      (* `(-2) < o1` *)
      intros Ho1' Ho1.
      generalize
       (Qquadratic_sign_nRdL_nRdL_6 a b c d e f g h 
          (dL xs) (dL ys) H_Qquadratic_sg_denom_nonzero).
      intros H1.
      assert
       (H_tuple_eq :
        (1%Z, (na, (nb, (nc, nd)), (ne, (nf, (ng, nh))), (np1, np2))) =
        ((- Z.sgn e)%Z, (a, (b, (c, d)), (e, (f, (g, h))), (dL xs, dL ys))));
       [ apply
          trans_eq
           with
             (Qquadratic_sign a b c d e f g h (dL xs) 
                (dL ys) H_Qquadratic_sg_denom_nonzero);
          [ apply sym_eq | apply H1; discriminate || (repeat split) ];
          assumption
       | generalize
          (Qquadratic_sign_tuple_equal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
             _ _ _ H_tuple_eq);
          intros
           (hl,
            ((hna, (hnb, (hnc, (hnd, (hne, (hnf, (hng, hnh))))))),
            (hp1,
             hp2)));
          do 10
           match goal with
           | id1:(?X1 = ?X2) |- ?X3 => try rewrite id1; clear id1
           end ].
      left; left; left; left; left; right; repeat split;
       repeat
        match goal with
        | id1:(?X1 = 0%Z) |- ?X2 => rewrite id1; clear id1
        end; first
       [ apply Z.le_refl
       | match goal with
         |  |- (0 <= ?X1)%Z => apply Zlt_le_weak; apply Zsgn_9
         |  |- (?X1 <= 0)%Z =>
             apply Zlt_le_weak; apply Zsgn_10; apply Z.opp_inj
         end; apply sym_eq; assumption
       | unfold o1 in Ho1';
          match goal with
          | id1:(2 < outside_square ?X1 ?X2 ?X3 ?X4)%Z |- 
          (0 <= ?X1)%Z =>
              apply outside_square_3 with X2 X3 X4
          | id1:(2 < outside_square ?X1 ?X2 ?X3 ?X4)%Z |- 
          (0 <= ?X2)%Z =>
              apply outside_square_4 with X1 X3 X4
          | id1:(2 < outside_square ?X1 ?X2 ?X3 ?X4)%Z |- 
          (0 <= ?X3)%Z =>
              apply outside_square_5 with X1 X2 X4
          | id1:(2 < outside_square ?X1 ?X2 ?X3 ?X4)%Z |- 
          (0 <= ?X4)%Z =>
              apply outside_square_6 with X1 X2 X3
          | id1:(outside_square ?X1 ?X2 ?X3 ?X4 < -2)%Z |- 
          (?X1 <= 0)%Z =>
              apply outside_square_7 with X2 X3 X4
          | id1:(outside_square ?X1 ?X2 ?X3 ?X4 < -2)%Z |- 
          (?X2 <= 0)%Z =>
              apply outside_square_8 with X1 X3 X4
          | id1:(outside_square ?X1 ?X2 ?X3 ?X4 < -2)%Z |- 
          (?X3 <= 0)%Z =>
              apply outside_square_9 with X1 X2 X4
          | id1:(outside_square ?X1 ?X2 ?X3 ?X4 < -2)%Z |- 
          (?X4 <= 0)%Z => apply outside_square_10 with X1 X2 X3
          end; assumption ].

      (* ~`o1 < (-2)` /\ ~`2 < o1` *)
      intros Ho2' Ho2.
      generalize
       (Qquadratic_sign_dL_dL_7 a b c d e f g h (dL xs) xs 
          (dL ys) ys H_Qquadratic_sg_denom_nonzero
          (Qquadratic_signok_4 _ _ _ _ _ _ H_Qquadratic_sg_denom_nonzero)
          (refl_equal _) (refl_equal _)).
      intros H1.
      assert
       (H_tuple_eq :
        Qquadratic_sign (a + b + c + d) (b + d) (c + d) d 
          (e + f + g + h) (f + h) (g + h) h xs ys
          (Qquadratic_signok_4 e f g h xs ys H_Qquadratic_sg_denom_nonzero) =
        (1%Z, (na, (nb, (nc, nd)), (ne, (nf, (ng, nh))), (np1, np2))));
       [ apply
          trans_eq
           with
             (Qquadratic_sign a b c d e f g h (dL xs) 
                (dL ys) H_Qquadratic_sg_denom_nonzero);
          [ apply sym_eq; apply H1; repeat split | idtac ]
       | apply
          (Qquadratic_sign_pos_2 (a + b + c + d)%Z 
             (b + d)%Z (c + d)%Z d (e + f + g + h)%Z 
             (f + h)%Z (g + h)%Z h xs ys
             (Qquadratic_signok_4 e f g h xs ys H_Qquadratic_sg_denom_nonzero)
             na nb nc nd ne nf ng nh np1 np2) ]; assumption.
    (* ~(`f = 0`/\`g = 0`/\`h = 0`) *)
    intro Hfgh'.
    case (inside_square_1_dec_inf o1 o2).    
     (* (inside_square_1 o1 o2) *)
     intro H_inside_1.
     generalize
      (Qquadratic_sign_nRdL_nRdL_8 a b c d e f g h 
         (dL xs) (dL ys) H_Qquadratic_sg_denom_nonzero).
     intros H1.
     assert
      (H_tuple_eq :
       (1%Z, (na, (nb, (nc, nd)), (ne, (nf, (ng, nh))), (np1, np2))) =
       (1%Z, (a, (b, (c, d)), (e, (f, (g, h))), (dL xs, dL ys))));
      [ apply
         trans_eq
          with
            (Qquadratic_sign a b c d e f g h (dL xs) 
               (dL ys) H_Qquadratic_sg_denom_nonzero);
         [ apply sym_eq | apply H1; discriminate || (repeat split) ];
         assumption
      | generalize
         (Qquadratic_sign_tuple_equal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
            _ _ H_tuple_eq);
         intros
          (hl,
           ((hna, (hnb, (hnc, (hnd, (hne, (hnf, (hng, hnh))))))),
           (hp1,
            hp2)));
         do 10
          match goal with
          | id1:(?X1 = ?X2) |- ?X3 => try rewrite id1; clear id1
          end ].
     left; left; left; left; left; case (inside_square_1_inf _ _ H_inside_1);
      intros (Ho1, Ho2); [ left | right ]; repeat split; first
      [ apply Z.le_refl
      | match goal with
        |  |- (0 <= ?X1)%Z => apply Zlt_le_weak; apply Zsgn_9
        |  |- (?X1 <= 0)%Z =>
            apply Zlt_le_weak; apply Zsgn_10; apply Z.opp_inj
        end; apply sym_eq; assumption
      | unfold o1 in Ho1; unfold o2 in Ho2;
         match goal with
         | id1:(2 < outside_square ?X1 ?X2 ?X3 ?X4)%Z |- 
         (0 <= ?X1)%Z =>
             apply outside_square_3 with X2 X3 X4
         | id1:(2 < outside_square ?X1 ?X2 ?X3 ?X4)%Z |- 
         (0 <= ?X2)%Z =>
             apply outside_square_4 with X1 X3 X4
         | id1:(2 < outside_square ?X1 ?X2 ?X3 ?X4)%Z |- 
         (0 <= ?X3)%Z =>
             apply outside_square_5 with X1 X2 X4
         | id1:(2 < outside_square ?X1 ?X2 ?X3 ?X4)%Z |- 
         (0 <= ?X4)%Z =>
             apply outside_square_6 with X1 X2 X3
         | id1:(outside_square ?X1 ?X2 ?X3 ?X4 < -2)%Z |- 
         (?X1 <= 0)%Z =>
             apply outside_square_7 with X2 X3 X4
         | id1:(outside_square ?X1 ?X2 ?X3 ?X4 < -2)%Z |- 
         (?X2 <= 0)%Z =>
             apply outside_square_8 with X1 X3 X4
         | id1:(outside_square ?X1 ?X2 ?X3 ?X4 < -2)%Z |- 
         (?X3 <= 0)%Z =>
             apply outside_square_9 with X1 X2 X4
         | id1:(outside_square ?X1 ?X2 ?X3 ?X4 < -2)%Z |- 
         (?X4 <= 0)%Z => apply outside_square_10 with X1 X2 X3
         end; assumption ].
      (* ~(inside_square_1 o1 o2) *)    
     intro H_inside_1'.
     case (inside_square_2_dec_inf o1 o2).    
      (* (inside_square_2 o1 o2) *)
      intro H_inside_2.
      generalize
       (Qquadratic_sign_nRdL_nRdL_9 a b c d e f g h 
          (dL xs) (dL ys) H_Qquadratic_sg_denom_nonzero).
      intros H1.
      apply False_rec.
      assert
       (H_tuple_eq :
        (1%Z, (na, (nb, (nc, nd)), (ne, (nf, (ng, nh))), (np1, np2))) =
        ((-1)%Z, (a, (b, (c, d)), (e, (f, (g, h))), (dL xs, dL ys))));
       [ apply
          trans_eq
           with
             (Qquadratic_sign a b c d e f g h (dL xs) 
                (dL ys) H_Qquadratic_sg_denom_nonzero);
          [ apply sym_eq | apply H1; discriminate || (repeat split) ];
          assumption
       | generalize
          (Qquadratic_sign_tuple_equal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
             _ _ _ H_tuple_eq);
          intros
           (hl,
            ((hna, (hnb, (hnc, (hnd, (hne, (hnf, (hng, hnh))))))),
            (hp1,
             hp2)));
          do 10
           match goal with
           | id1:(?X1 = ?X2) |- ?X3 => try rewrite id1; clear id1
           end ].
      discriminate hl.
      (*  ~(inside_square_1 o1 o2)/\~(inside_square_2 o1 o2) *)
      intros H_inside_2'. 
      generalize
       (Qquadratic_sign_dL_dL_10 a b c d e f g h (dL xs) xs 
          (dL ys) ys H_Qquadratic_sg_denom_nonzero
          (Qquadratic_signok_4 _ _ _ _ _ _ H_Qquadratic_sg_denom_nonzero)
          (refl_equal _) (refl_equal _)).
      intros H1.
      assert
       (H_tuple_eq :
        Qquadratic_sign (a + b + c + d) (b + d) (c + d) d 
          (e + f + g + h) (f + h) (g + h) h xs ys
          (Qquadratic_signok_4 e f g h xs ys H_Qquadratic_sg_denom_nonzero) =
        (1%Z, (na, (nb, (nc, nd)), (ne, (nf, (ng, nh))), (np1, np2))));
       [ apply
          trans_eq
           with
             (Qquadratic_sign a b c d e f g h (dL xs) 
                (dL ys) H_Qquadratic_sg_denom_nonzero);
          [ apply sym_eq; apply H1; repeat split | idtac ]
       | apply
          (Qquadratic_sign_pos_2 (a + b + c + d)%Z 
             (b + d)%Z (c + d)%Z d (e + f + g + h)%Z 
             (f + h)%Z (g + h)%Z h xs ys
             (Qquadratic_signok_4 e f g h xs ys H_Qquadratic_sg_denom_nonzero)
             na nb nc nd ne nf ng nh np1 np2) ]; assumption.
 (*  p1 = (dL xs) & p2 = One *)
  generalize (Qquadratic_signok_0' _ _ _ _ _ H_Qquadratic_sg_denom_nonzero).
  intros H_Qhomographic_sg_denom_nonzero.
  set
   (L3 :=
    Qhomographic_sign (a + b) (c + d) (e + f) (g + h) 
      (dL xs) H_Qhomographic_sg_denom_nonzero) in *.
  set (l1 := fst L3) in *.
  set (l2 := fst (snd L3)) in *.
  set (l3 := snd (snd L3)) in *.
  set (na_ := fst l2) in *.
  set (nb_ := fst (snd l2)) in *.
  set (nc_ := fst (snd (snd l2))) in *.
  set (nd_ := snd (snd (snd l2))) in *.
  generalize
   (Qquadratic_sign_nRdL_One a b c d e f g h (dL xs) One
      H_Qquadratic_sg_denom_nonzero l1 na_ nb_ nc_ nd_ l3
      H_Qhomographic_sg_denom_nonzero); intros H1.
  assert
   (H_tuple_eq :
    (1%Z, (na, (nb, (nc, nd)), (ne, (nf, (ng, nh))), (np1, np2))) =
    (l1, (0%Z, (na_, (0%Z, nb_)), (0%Z, (nc_, (0%Z, nd_))), (l3, One))));
   [ apply
      trans_eq
       with
         (Qquadratic_sign a b c d e f g h (dL xs) One
            H_Qquadratic_sg_denom_nonzero);
      [ apply sym_eq; assumption
      | apply H1; fold L3 in |- *; repeat (apply pair_2; try reflexivity);
         discriminate || reflexivity ]
   | generalize
      (Qquadratic_sign_tuple_equal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
         _ H_tuple_eq);
      intros
       (hl,
        ((hna, (hnb, (hnc, (hnd, (hne, (hnf, (hng, hnh))))))),
        (hp1,
         hp2)));
      do 10
       match goal with
       | id1:(?X1 = ?X2) |- ?X3 => try rewrite id1; clear id1
       end; repeat rewrite ZERO_left; repeat rewrite ZERO_right ].
  assert
   (H_sg_unfolded :
    Qhomographic_sign (a + b) (c + d) (e + f) (g + h) 
      (dL xs) H_Qhomographic_sg_denom_nonzero =
    (1%Z, (na_, (nb_, (nc_, nd_)), l3))).
  rewrite hl; fold L3 in |- *; repeat (apply pair_2; try reflexivity);
   discriminate || reflexivity.
  generalize
   (sg_pos_2 (a + b) (c + d) (e + f) (g + h) (dL xs)
      H_Qhomographic_sg_denom_nonzero na_ nb_ nc_ nd_ l3 H_sg_unfolded).
  intros [[(H_a, (H_b, (H_c, H_d)))| (H_a, (H_b, (H_c, H_d)))]| H_l3];
   [ case l3; left;
      [ right; repeat split; assumption || discriminate
      | right; repeat split; assumption || discriminate
      | left; right; repeat split ]
   | case l3;
      [ right; repeat split; assumption || discriminate
      | right; repeat split; assumption || discriminate
      | left; left; right; repeat split ]
   | left; left; right; repeat split; assumption ].

 (* p1 = One *)
  generalize (Qquadratic_signok_0 _ _ _ _ _ H_Qquadratic_sg_denom_nonzero).
  intros H_Qhomographic_sg_denom_nonzero.
  set
   (L3 :=
    Qhomographic_sign (a + c) (b + d) (e + g) (f + h) p2
      H_Qhomographic_sg_denom_nonzero) in *.
  set (l1 := fst L3) in *.
  set (l2 := fst (snd L3)) in *.
  set (l3 := snd (snd L3)) in *.
  set (na_ := fst l2) in *.
  set (nb_ := fst (snd l2)) in *.
  set (nc_ := fst (snd (snd l2))) in *.
  set (nd_ := snd (snd (snd l2))) in *.
  generalize
   (Qquadratic_sign_One_y a b c d e f g h One p2
      H_Qquadratic_sg_denom_nonzero l1 na_ nb_ nc_ nd_ l3
      H_Qhomographic_sg_denom_nonzero); intros H1.
  assert
   (H_tuple_eq :
    (1%Z, (na, (nb, (nc, nd)), (ne, (nf, (ng, nh))), (np1, np2))) =
    (l1, (0%Z, (0%Z, (na_, nb_)), (0%Z, (0%Z, (nc_, nd_))), (One, l3))));
   [ apply
      trans_eq
       with
         (Qquadratic_sign a b c d e f g h One p2
            H_Qquadratic_sg_denom_nonzero);
      [ apply sym_eq; assumption
      | apply H1; fold L3 in |- *; repeat (apply pair_2; try reflexivity);
         discriminate || reflexivity ]
   | generalize
      (Qquadratic_sign_tuple_equal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
         _ H_tuple_eq);
      intros
       (hl,
        ((hna, (hnb, (hnc, (hnd, (hne, (hnf, (hng, hnh))))))),
        (hp1,
         hp2)));
      do 10
       match goal with
       | id1:(?X1 = ?X2) |- ?X3 => try rewrite id1; clear id1
       end; repeat rewrite ZERO_left; repeat rewrite ZERO_right ].
  assert
   (H_sg_unfolded :
    Qhomographic_sign (a + c) (b + d) (e + g) (f + h) p2
      H_Qhomographic_sg_denom_nonzero = (1%Z, (na_, (nb_, (nc_, nd_)), l3))).
  rewrite hl; fold L3 in |- *; repeat (apply pair_2; try reflexivity);
   discriminate || reflexivity.
  generalize
   (sg_pos_2 (a + c) (b + d) (e + g) (f + h) p2
      H_Qhomographic_sg_denom_nonzero na_ nb_ nc_ nd_ l3 H_sg_unfolded).
  intros [[(H_a, (H_b, (H_c, H_d)))| (H_a, (H_b, (H_c, H_d)))]| H_l3]; left;
   left; [ left; left; right | left; right | right ]; 
   repeat split; assumption.
Qed.

Lemma Qquadratic_sign_neg_1 :
 forall (a b c d e f g h : Z) (p1 p2 : Qpositive)
   (H_Qquadratic_sg_denom_nonzero : Qquadratic_sg_denom_nonzero e f g h p1 p2)
   (na nb nc nd ne nf ng nh : Z) (np1 np2 : Qpositive),
 Qquadratic_sign a b c d e f g h p1 p2 H_Qquadratic_sg_denom_nonzero =
 ((-1)%Z, (na, (nb, (nc, nd)), (ne, (nf, (ng, nh))), (np1, np2))) ->
 {(0 < na + nb + nc + nd)%Z /\ (ne + nf + ng + nh < 0)%Z} +
 {(na + nb + nc + nd < 0 < ne + nf + ng + nh)%Z}.
Proof.
 fix Qquadratic_sign_neg_1 9.
 intros.
 set (o1 := outside_square a b c d) in *.
 set (o2 := outside_square e f g h) in *.
 destruct p1 as [xs| xs| ].
 (* p1 = (nR xs) *)
 destruct p2 as [ys| ys| ].
  (*  p1 = (nR xs) & p2 = (nR ys) *)
  case (three_integers_dec_inf b c d).  
   (* `b = 0`/\`c = 0`/\`d = 0` *)
   intros (Hb, (Hc, Hd)).
   (* Intros [Hb [Hc] Hd]. *)
   case (three_integers_dec_inf f g h).   
    (* `f = 0`/\`g = 0`/\`h = 0` *)
    intros (Hf, (Hg, Hh)).
    generalize
     (Qquadratic_sign_nRdL_nRdL_1 a b c d e f g h (nR xs) 
        (nR ys) H_Qquadratic_sg_denom_nonzero).
    intros H1.
    assert
     (H_tuple_eq :
      ((-1)%Z, (na, (nb, (nc, nd)), (ne, (nf, (ng, nh))), (np1, np2))) =
      ((Z.sgn a * Z.sgn e)%Z,
      (a, (b, (c, d)), (e, (f, (g, h))), (nR xs, nR ys))));
     [ apply
        trans_eq
         with
           (Qquadratic_sign a b c d e f g h (nR xs) 
              (nR ys) H_Qquadratic_sg_denom_nonzero);
        [ apply sym_eq | apply H1; discriminate || (repeat split) ];
        assumption
     | generalize
        (Qquadratic_sign_tuple_equal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
           _ _ H_tuple_eq);
        intros
         (hl,
          ((hna, (hnb, (hnc, (hnd, (hne, (hnf, (hng, hnh))))))),
          (hp1,
           hp2)));
        do 10
         match goal with
         | id1:(?X1 = ?X2) |- ?X3 => try rewrite id1; clear id1
         end ].
    rewrite <- Zsgn_15 in hl.
    case (Zsgn_17 _ _ (sym_eq hl)); intros (Ha, He); [ left | right ];
     repeat split;
     repeat
      match goal with
      | id1:(?X1 = 0%Z) |- ?X2 => rewrite id1; clear id1
      end; repeat rewrite Zplus_0_r; assumption.
    (* ~(`f = 0`/\`g = 0`/\`h = 0`) *)
    intros H_fgh'.
    case (Z_lt_dec 2 o2).
     (*  `2 < o2` *)
     intro Ho2.
     generalize
      (Qquadratic_sign_nRdL_nRdL_2 a b c d e f g h 
         (nR xs) (nR ys) H_Qquadratic_sg_denom_nonzero).
     intros H1.
     assert
      (H_tuple_eq :
       ((-1)%Z, (na, (nb, (nc, nd)), (ne, (nf, (ng, nh))), (np1, np2))) =
       (Z.sgn a, (a, (b, (c, d)), (e, (f, (g, h))), (nR xs, nR ys))));
      [ apply
         trans_eq
          with
            (Qquadratic_sign a b c d e f g h (nR xs) 
               (nR ys) H_Qquadratic_sg_denom_nonzero);
         [ apply sym_eq | apply H1; discriminate || (repeat split) ];
         assumption
      | generalize
         (Qquadratic_sign_tuple_equal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
            _ _ H_tuple_eq);
         intros
          (hl,
           ((hna, (hnb, (hnc, (hnd, (hne, (hnf, (hng, hnh))))))),
           (hp1,
            hp2)));
         do 10
          match goal with
          | id1:(?X1 = ?X2) |- ?X3 => try rewrite id1; clear id1
          end ].
     right; split;
      repeat
       match goal with
       | id1:(?X1 = 0%Z) |- ?X2 => rewrite id1; clear id1
       end; repeat rewrite Zplus_0_r;
      [ apply Zsgn_10; apply sym_eq | apply outside_square_1 ]; 
      assumption.
     (*  ~`2 < o2` *)
     case (Z_lt_dec o2 (-2)).     
     (* `(-2) < o2` *)
      intros Ho2' Ho2.
      generalize
       (Qquadratic_sign_nRdL_nRdL_3 a b c d e f g h 
          (nR xs) (nR ys) H_Qquadratic_sg_denom_nonzero).
      intros H1.
      assert
       (H_tuple_eq :
        ((-1)%Z, (na, (nb, (nc, nd)), (ne, (nf, (ng, nh))), (np1, np2))) =
        ((- Z.sgn a)%Z, (a, (b, (c, d)), (e, (f, (g, h))), (nR xs, nR ys))));
       [ apply
          trans_eq
           with
             (Qquadratic_sign a b c d e f g h (nR xs) 
                (nR ys) H_Qquadratic_sg_denom_nonzero);
          [ apply sym_eq | apply H1; discriminate || (repeat split) ];
          assumption
       | generalize
          (Qquadratic_sign_tuple_equal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
             _ _ _ H_tuple_eq);
          intros
           (hl,
            ((hna, (hnb, (hnc, (hnd, (hne, (hnf, (hng, hnh))))))),
            (hp1,
             hp2)));
          do 10
           match goal with
           | id1:(?X1 = ?X2) |- ?X3 => try rewrite id1; clear id1
           end ].
      left; split;
       repeat
        match goal with
        | id1:(?X1 = 0%Z) |- ?X2 => rewrite id1; clear id1
        end; repeat rewrite Zplus_0_r;
       [ apply Zsgn_9; apply sym_eq; apply Z.opp_inj; assumption
       | apply outside_square_2; assumption ]. 
     (* ~`o1 < (-2)` /\ ~`2 < o1` *)
      intros Ho2' Ho2.
      generalize
       (Qquadratic_sign_nR_nR_4 a b c d e f g h (nR xs) xs 
          (nR ys) ys H_Qquadratic_sg_denom_nonzero
          (Qquadratic_signok_1 _ _ _ _ _ _ H_Qquadratic_sg_denom_nonzero)
          (refl_equal _) (refl_equal _)).
      intros H1.
      assert
       (H_tuple_eq :
        Qquadratic_sign a (a + b) (a + c) (a + b + c + d) e 
          (e + f) (e + g) (e + f + g + h) xs ys
          (Qquadratic_signok_1 e f g h xs ys H_Qquadratic_sg_denom_nonzero) =
        ((-1)%Z, (na, (nb, (nc, nd)), (ne, (nf, (ng, nh))), (np1, np2))));
       [ apply
          trans_eq
           with
             (Qquadratic_sign a b c d e f g h (nR xs) 
                (nR ys) H_Qquadratic_sg_denom_nonzero);
          [ apply sym_eq; apply H1; repeat split | idtac ]
       | apply
          (Qquadratic_sign_neg_1 a (a + b)%Z (a + c)%Z 
             (a + b + c + d)%Z e (e + f)%Z (e + g)%Z 
             (e + f + g + h)%Z xs ys
             (Qquadratic_signok_1 e f g h xs ys H_Qquadratic_sg_denom_nonzero)
             na nb nc nd ne nf ng nh np1 np2) ]; assumption.
   (* ~ `b = 0`/\`c = 0`/\`d = 0` *)
   intros Hbcd'.
   (* Intros [Hb [Hc] Hd]. *)
   case (three_integers_dec_inf f g h).   
    (* `f = 0`/\`g = 0`/\`h = 0` *)
    intros (Hf, (Hg, Hh)).
    case (Z_lt_dec 2 o1).
     (*  `2 < o1` *)
     intro Ho1.
     generalize
      (Qquadratic_sign_nRdL_nRdL_5 a b c d e f g h 
         (nR xs) (nR ys) H_Qquadratic_sg_denom_nonzero).
     intros H1.
     assert
      (H_tuple_eq :
       ((-1)%Z, (na, (nb, (nc, nd)), (ne, (nf, (ng, nh))), (np1, np2))) =
       (Z.sgn e, (a, (b, (c, d)), (e, (f, (g, h))), (nR xs, nR ys))));
      [ apply
         trans_eq
          with
            (Qquadratic_sign a b c d e f g h (nR xs) 
               (nR ys) H_Qquadratic_sg_denom_nonzero);
         [ apply sym_eq | apply H1; discriminate || (repeat split) ];
         assumption
      | generalize
         (Qquadratic_sign_tuple_equal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
            _ _ H_tuple_eq);
         intros
          (hl,
           ((hna, (hnb, (hnc, (hnd, (hne, (hnf, (hng, hnh))))))),
           (hp1,
            hp2)));
         do 10
          match goal with
          | id1:(?X1 = ?X2) |- ?X3 => try rewrite id1; clear id1
          end ].
     left; split;
      repeat
       match goal with
       | id1:(?X1 = 0%Z) |- ?X2 => rewrite id1; clear id1
       end; repeat rewrite Zplus_0_r;
      [ apply outside_square_1 | apply Zsgn_10; apply sym_eq ]; 
      assumption.
     (*  ~`2 < o1` *)
     case (Z_lt_dec o1 (-2)).
      (* `(-2) < o1` *)
      intros Ho1' Ho1.
      generalize
       (Qquadratic_sign_nRdL_nRdL_6 a b c d e f g h 
          (nR xs) (nR ys) H_Qquadratic_sg_denom_nonzero).
      intros H1.
      assert
       (H_tuple_eq :
        ((-1)%Z, (na, (nb, (nc, nd)), (ne, (nf, (ng, nh))), (np1, np2))) =
        ((- Z.sgn e)%Z, (a, (b, (c, d)), (e, (f, (g, h))), (nR xs, nR ys))));
       [ apply
          trans_eq
           with
             (Qquadratic_sign a b c d e f g h (nR xs) 
                (nR ys) H_Qquadratic_sg_denom_nonzero);
          [ apply sym_eq | apply H1; discriminate || (repeat split) ];
          assumption
       | generalize
          (Qquadratic_sign_tuple_equal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
             _ _ _ H_tuple_eq);
          intros
           (hl,
            ((hna, (hnb, (hnc, (hnd, (hne, (hnf, (hng, hnh))))))),
            (hp1,
             hp2)));
          do 10
           match goal with
           | id1:(?X1 = ?X2) |- ?X3 => try rewrite id1; clear id1
           end ].
      right; split;
       repeat
        match goal with
        | id1:(?X1 = 0%Z) |- ?X2 => rewrite id1; clear id1
        end; repeat rewrite Zplus_0_r;
       [ apply outside_square_2
       | apply Zsgn_9; apply sym_eq; apply Z.opp_inj ]; 
       assumption.
      (* ~`o1 < (-2)` /\ ~`2 < o1` *)
      intros Ho2' Ho2.
      generalize
       (Qquadratic_sign_nR_nR_7 a b c d e f g h (nR xs) xs 
          (nR ys) ys H_Qquadratic_sg_denom_nonzero
          (Qquadratic_signok_1 _ _ _ _ _ _ H_Qquadratic_sg_denom_nonzero)
          (refl_equal _) (refl_equal _)).
      intros H1.
      assert
       (H_tuple_eq :
        Qquadratic_sign a (a + b) (a + c) (a + b + c + d) e 
          (e + f) (e + g) (e + f + g + h) xs ys
          (Qquadratic_signok_1 e f g h xs ys H_Qquadratic_sg_denom_nonzero) =
        ((-1)%Z, (na, (nb, (nc, nd)), (ne, (nf, (ng, nh))), (np1, np2))));
       [ apply
          trans_eq
           with
             (Qquadratic_sign a b c d e f g h (nR xs) 
                (nR ys) H_Qquadratic_sg_denom_nonzero);
          [ apply sym_eq; apply H1; repeat split | idtac ]
       | apply
          (Qquadratic_sign_neg_1 a (a + b)%Z (a + c)%Z 
             (a + b + c + d)%Z e (e + f)%Z (e + g)%Z 
             (e + f + g + h)%Z xs ys
             (Qquadratic_signok_1 e f g h xs ys H_Qquadratic_sg_denom_nonzero)
             na nb nc nd ne nf ng nh np1 np2) ]; assumption.
    (* ~(`f = 0`/\`g = 0`/\`h = 0`) *)
    intro Hfgh'.
    case (inside_square_1_dec_inf o1 o2).    
     (* (inside_square_1 o1 o2) *)
     intro H_inside_1.
     generalize
      (Qquadratic_sign_nRdL_nRdL_8 a b c d e f g h 
         (nR xs) (nR ys) H_Qquadratic_sg_denom_nonzero).
     intros H1.
     assert
      (H_tuple_eq :
       ((-1)%Z, (na, (nb, (nc, nd)), (ne, (nf, (ng, nh))), (np1, np2))) =
       (1%Z, (a, (b, (c, d)), (e, (f, (g, h))), (nR xs, nR ys))));
      [ apply
         trans_eq
          with
            (Qquadratic_sign a b c d e f g h (nR xs) 
               (nR ys) H_Qquadratic_sg_denom_nonzero);
         [ apply sym_eq | apply H1; discriminate || (repeat split) ];
         assumption
      | generalize
         (Qquadratic_sign_tuple_equal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
            _ _ H_tuple_eq);
         intros
          (hl,
           ((hna, (hnb, (hnc, (hnd, (hne, (hnf, (hng, hnh))))))),
           (hp1,
            hp2)));
         do 10
          match goal with
          | id1:(?X1 = ?X2) |- ?X3 => try rewrite id1; clear id1
          end ].
     discriminate hl.
     (* ~(inside_square_1 o1 o2) *)    
     intro H_inside_1'.
     case (inside_square_2_dec_inf o1 o2).    
      (* (inside_square_2 o1 o2) *)
      intro H_inside_2.
      generalize
       (Qquadratic_sign_nRdL_nRdL_9 a b c d e f g h 
          (nR xs) (nR ys) H_Qquadratic_sg_denom_nonzero).
      intros H1.
      assert
       (H_tuple_eq :
        ((-1)%Z, (na, (nb, (nc, nd)), (ne, (nf, (ng, nh))), (np1, np2))) =
        ((-1)%Z, (a, (b, (c, d)), (e, (f, (g, h))), (nR xs, nR ys))));
       [ apply
          trans_eq
           with
             (Qquadratic_sign a b c d e f g h (nR xs) 
                (nR ys) H_Qquadratic_sg_denom_nonzero);
          [ apply sym_eq | apply H1; discriminate || (repeat split) ];
          assumption
       | generalize
          (Qquadratic_sign_tuple_equal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
             _ _ _ H_tuple_eq);
          intros
           (hl,
            ((hna, (hnb, (hnc, (hnd, (hne, (hnf, (hng, hnh))))))),
            (hp1,
             hp2)));
          do 10
           match goal with
           | id1:(?X1 = ?X2) |- ?X3 => try rewrite id1; clear id1
           end ].
     case (inside_square_2_inf _ _ H_inside_2); intros (Ho1, Ho2);
      [ left; split; [ apply outside_square_1 | apply outside_square_2 ]
      | right; split; [ apply outside_square_2 | apply outside_square_1 ] ];
      assumption.
      (*  ~(inside_square_1 o1 o2)/\~(inside_square_2 o1 o2) *)
      intros H_inside_2'. 
      generalize
       (Qquadratic_sign_nR_nR_10 a b c d e f g h (nR xs) xs 
          (nR ys) ys H_Qquadratic_sg_denom_nonzero
          (Qquadratic_signok_1 _ _ _ _ _ _ H_Qquadratic_sg_denom_nonzero)
          (refl_equal _) (refl_equal _)).
      intros H1.
      assert
       (H_tuple_eq :
        Qquadratic_sign a (a + b) (a + c) (a + b + c + d) e 
          (e + f) (e + g) (e + f + g + h) xs ys
          (Qquadratic_signok_1 e f g h xs ys H_Qquadratic_sg_denom_nonzero) =
        ((-1)%Z, (na, (nb, (nc, nd)), (ne, (nf, (ng, nh))), (np1, np2))));
       [ apply
          trans_eq
           with
             (Qquadratic_sign a b c d e f g h (nR xs) 
                (nR ys) H_Qquadratic_sg_denom_nonzero);
          [ apply sym_eq; apply H1; repeat split | idtac ]
       | apply
          (Qquadratic_sign_neg_1 a (a + b)%Z (a + c)%Z 
             (a + b + c + d)%Z e (e + f)%Z (e + g)%Z 
             (e + f + g + h)%Z xs ys
             (Qquadratic_signok_1 e f g h xs ys H_Qquadratic_sg_denom_nonzero)
             na nb nc nd ne nf ng nh np1 np2) ]; assumption.

  (*  p1 = (nR xs) & p2 = (dL ys) *)
  case (three_integers_dec_inf b c d).  
   (* `b = 0`/\`c = 0`/\`d = 0` *)
   intros (Hb, (Hc, Hd)).
   (* Intros [Hb [Hc] Hd]. *)
   case (three_integers_dec_inf f g h).   
    (* `f = 0`/\`g = 0`/\`h = 0` *)
    intros (Hf, (Hg, Hh)).
    generalize
     (Qquadratic_sign_nRdL_nRdL_1 a b c d e f g h (nR xs) 
        (dL ys) H_Qquadratic_sg_denom_nonzero).
    intros H1.
    assert
     (H_tuple_eq :
      ((-1)%Z, (na, (nb, (nc, nd)), (ne, (nf, (ng, nh))), (np1, np2))) =
      ((Z.sgn a * Z.sgn e)%Z,
      (a, (b, (c, d)), (e, (f, (g, h))), (nR xs, dL ys))));
     [ apply
        trans_eq
         with
           (Qquadratic_sign a b c d e f g h (nR xs) 
              (dL ys) H_Qquadratic_sg_denom_nonzero);
        [ apply sym_eq | apply H1; discriminate || (repeat split) ];
        assumption
     | generalize
        (Qquadratic_sign_tuple_equal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
           _ _ H_tuple_eq);
        intros
         (hl,
          ((hna, (hnb, (hnc, (hnd, (hne, (hnf, (hng, hnh))))))),
          (hp1,
           hp2)));
        do 10
         match goal with
         | id1:(?X1 = ?X2) |- ?X3 => try rewrite id1; clear id1
         end ].
    rewrite <- Zsgn_15 in hl.
    case (Zsgn_17 _ _ (sym_eq hl)); intros (Ha, He); [ left | right ];
     repeat split;
     repeat
      match goal with
      | id1:(?X1 = 0%Z) |- ?X2 => rewrite id1; clear id1
      end; repeat rewrite Zplus_0_r; assumption.
    (* ~(`f = 0`/\`g = 0`/\`h = 0`) *)
    intros H_fgh'.
    case (Z_lt_dec 2 o2).
     (*  `2 < o2` *)
     intro Ho2.
     generalize
      (Qquadratic_sign_nRdL_nRdL_2 a b c d e f g h 
         (nR xs) (dL ys) H_Qquadratic_sg_denom_nonzero).
     intros H1.
     assert
      (H_tuple_eq :
       ((-1)%Z, (na, (nb, (nc, nd)), (ne, (nf, (ng, nh))), (np1, np2))) =
       (Z.sgn a, (a, (b, (c, d)), (e, (f, (g, h))), (nR xs, dL ys))));
      [ apply
         trans_eq
          with
            (Qquadratic_sign a b c d e f g h (nR xs) 
               (dL ys) H_Qquadratic_sg_denom_nonzero);
         [ apply sym_eq | apply H1; discriminate || (repeat split) ];
         assumption
      | generalize
         (Qquadratic_sign_tuple_equal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
            _ _ H_tuple_eq);
         intros
          (hl,
           ((hna, (hnb, (hnc, (hnd, (hne, (hnf, (hng, hnh))))))),
           (hp1,
            hp2)));
         do 10
          match goal with
          | id1:(?X1 = ?X2) |- ?X3 => try rewrite id1; clear id1
          end ].
     right; split;
      repeat
       match goal with
       | id1:(?X1 = 0%Z) |- ?X2 => rewrite id1; clear id1
       end; repeat rewrite Zplus_0_r;
      [ apply Zsgn_10; apply sym_eq; assumption
      | apply outside_square_1; assumption ].
     (*  ~`2 < o2` *)
     case (Z_lt_dec o2 (-2)).     
     (* `(-2) < o2` *)
      intros Ho2' Ho2.
      generalize
       (Qquadratic_sign_nRdL_nRdL_3 a b c d e f g h 
          (nR xs) (dL ys) H_Qquadratic_sg_denom_nonzero).
      intros H1.
      assert
       (H_tuple_eq :
        ((-1)%Z, (na, (nb, (nc, nd)), (ne, (nf, (ng, nh))), (np1, np2))) =
        ((- Z.sgn a)%Z, (a, (b, (c, d)), (e, (f, (g, h))), (nR xs, dL ys))));
       [ apply
          trans_eq
           with
             (Qquadratic_sign a b c d e f g h (nR xs) 
                (dL ys) H_Qquadratic_sg_denom_nonzero);
          [ apply sym_eq | apply H1; discriminate || (repeat split) ];
          assumption
       | generalize
          (Qquadratic_sign_tuple_equal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
             _ _ _ H_tuple_eq);
          intros
           (hl,
            ((hna, (hnb, (hnc, (hnd, (hne, (hnf, (hng, hnh))))))),
            (hp1,
             hp2)));
          do 10
           match goal with
           | id1:(?X1 = ?X2) |- ?X3 => try rewrite id1; clear id1
           end ].
      left; split;
       repeat
        match goal with
        | id1:(?X1 = 0%Z) |- ?X2 => rewrite id1; clear id1
        end; repeat rewrite Zplus_0_r;
       [ apply Zsgn_9; apply sym_eq; apply Z.opp_inj; assumption
       | apply outside_square_2; assumption ]. 
     (* ~`o1 < (-2)` /\ ~`2 < o1` *)
      intros Ho2' Ho2.
      generalize
       (Qquadratic_sign_nR_dL_4 a b c d e f g h (nR xs) xs 
          (dL ys) ys H_Qquadratic_sg_denom_nonzero
          (Qquadratic_signok_2 _ _ _ _ _ _ H_Qquadratic_sg_denom_nonzero)
          (refl_equal _) (refl_equal _)).
      intros H1.
      assert
       (H_tuple_eq :
        Qquadratic_sign (a + b) b (a + b + c + d) (b + d) 
          (e + f) f (e + f + g + h) (f + h) xs ys
          (Qquadratic_signok_2 e f g h xs ys H_Qquadratic_sg_denom_nonzero) =
        ((-1)%Z, (na, (nb, (nc, nd)), (ne, (nf, (ng, nh))), (np1, np2))));
       [ apply
          trans_eq
           with
             (Qquadratic_sign a b c d e f g h (nR xs) 
                (dL ys) H_Qquadratic_sg_denom_nonzero);
          [ apply sym_eq; apply H1; repeat split | idtac ]
       | apply
          (Qquadratic_sign_neg_1 (a + b)%Z b (a + b + c + d)%Z 
             (b + d)%Z (e + f)%Z f (e + f + g + h)%Z 
             (f + h)%Z xs ys
             (Qquadratic_signok_2 e f g h xs ys H_Qquadratic_sg_denom_nonzero)
             na nb nc nd ne nf ng nh np1 np2) ]; assumption.
   (* ~ `b = 0`/\`c = 0`/\`d = 0` *)
   intros Hbcd'.
   (* Intros [Hb [Hc] Hd]. *)
   case (three_integers_dec_inf f g h).   
    (* `f = 0`/\`g = 0`/\`h = 0` *)
    intros (Hf, (Hg, Hh)).
    case (Z_lt_dec 2 o1).
     (*  `2 < o1` *)
     intro Ho1.
     generalize
      (Qquadratic_sign_nRdL_nRdL_5 a b c d e f g h 
         (nR xs) (dL ys) H_Qquadratic_sg_denom_nonzero).
     intros H1.
     assert
      (H_tuple_eq :
       ((-1)%Z, (na, (nb, (nc, nd)), (ne, (nf, (ng, nh))), (np1, np2))) =
       (Z.sgn e, (a, (b, (c, d)), (e, (f, (g, h))), (nR xs, dL ys))));
      [ apply
         trans_eq
          with
            (Qquadratic_sign a b c d e f g h (nR xs) 
               (dL ys) H_Qquadratic_sg_denom_nonzero);
         [ apply sym_eq | apply H1; discriminate || (repeat split) ];
         assumption
      | generalize
         (Qquadratic_sign_tuple_equal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
            _ _ H_tuple_eq);
         intros
          (hl,
           ((hna, (hnb, (hnc, (hnd, (hne, (hnf, (hng, hnh))))))),
           (hp1,
            hp2)));
         do 10
          match goal with
          | id1:(?X1 = ?X2) |- ?X3 => try rewrite id1; clear id1
          end ].
     left; split;
      repeat
       match goal with
       | id1:(?X1 = 0%Z) |- ?X2 => rewrite id1; clear id1
       end; repeat rewrite Zplus_0_r;
      [ apply outside_square_1 | apply Zsgn_10; apply sym_eq ]; 
      assumption.
     (*  ~`2 < o1` *)
     case (Z_lt_dec o1 (-2)).
      (* `(-2) < o1` *)
      intros Ho1' Ho1.
      generalize
       (Qquadratic_sign_nRdL_nRdL_6 a b c d e f g h 
          (nR xs) (dL ys) H_Qquadratic_sg_denom_nonzero).
      intros H1.
      assert
       (H_tuple_eq :
        ((-1)%Z, (na, (nb, (nc, nd)), (ne, (nf, (ng, nh))), (np1, np2))) =
        ((- Z.sgn e)%Z, (a, (b, (c, d)), (e, (f, (g, h))), (nR xs, dL ys))));
       [ apply
          trans_eq
           with
             (Qquadratic_sign a b c d e f g h (nR xs) 
                (dL ys) H_Qquadratic_sg_denom_nonzero);
          [ apply sym_eq | apply H1; discriminate || (repeat split) ];
          assumption
       | generalize
          (Qquadratic_sign_tuple_equal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
             _ _ _ H_tuple_eq);
          intros
           (hl,
            ((hna, (hnb, (hnc, (hnd, (hne, (hnf, (hng, hnh))))))),
            (hp1,
             hp2)));
          do 10
           match goal with
           | id1:(?X1 = ?X2) |- ?X3 => try rewrite id1; clear id1
           end ].
      right; split;
       repeat
        match goal with
        | id1:(?X1 = 0%Z) |- ?X2 => rewrite id1; clear id1
        end; repeat rewrite Zplus_0_r;
       [ apply outside_square_2
       | apply Zsgn_9; apply sym_eq; apply Z.opp_inj ]; 
       assumption.
      (* ~`o1 < (-2)` /\ ~`2 < o1` *)
      intros Ho2' Ho2.
      generalize
       (Qquadratic_sign_nR_dL_7 a b c d e f g h (nR xs) xs 
          (dL ys) ys H_Qquadratic_sg_denom_nonzero
          (Qquadratic_signok_2 _ _ _ _ _ _ H_Qquadratic_sg_denom_nonzero)
          (refl_equal _) (refl_equal _)).
      intros H1.
      assert
       (H_tuple_eq :
        Qquadratic_sign (a + b) b (a + b + c + d) (b + d) 
          (e + f) f (e + f + g + h) (f + h) xs ys
          (Qquadratic_signok_2 e f g h xs ys H_Qquadratic_sg_denom_nonzero) =
        ((-1)%Z, (na, (nb, (nc, nd)), (ne, (nf, (ng, nh))), (np1, np2))));
       [ apply
          trans_eq
           with
             (Qquadratic_sign a b c d e f g h (nR xs) 
                (dL ys) H_Qquadratic_sg_denom_nonzero);
          [ apply sym_eq; apply H1; repeat split | idtac ]
       | apply
          (Qquadratic_sign_neg_1 (a + b)%Z b (a + b + c + d)%Z 
             (b + d)%Z (e + f)%Z f (e + f + g + h)%Z 
             (f + h)%Z xs ys
             (Qquadratic_signok_2 e f g h xs ys H_Qquadratic_sg_denom_nonzero)
             na nb nc nd ne nf ng nh np1 np2) ]; assumption.
    (* ~(`f = 0`/\`g = 0`/\`h = 0`) *)
    intro Hfgh'.
    case (inside_square_1_dec_inf o1 o2).    
     (* (inside_square_1 o1 o2) *)
     intro H_inside_1.
     generalize
      (Qquadratic_sign_nRdL_nRdL_8 a b c d e f g h 
         (nR xs) (dL ys) H_Qquadratic_sg_denom_nonzero).
     intros H1.
     assert
      (H_tuple_eq :
       ((-1)%Z, (na, (nb, (nc, nd)), (ne, (nf, (ng, nh))), (np1, np2))) =
       (1%Z, (a, (b, (c, d)), (e, (f, (g, h))), (nR xs, dL ys))));
      [ apply
         trans_eq
          with
            (Qquadratic_sign a b c d e f g h (nR xs) 
               (dL ys) H_Qquadratic_sg_denom_nonzero);
         [ apply sym_eq | apply H1; discriminate || (repeat split) ];
         assumption
      | generalize
         (Qquadratic_sign_tuple_equal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
            _ _ H_tuple_eq);
         intros
          (hl,
           ((hna, (hnb, (hnc, (hnd, (hne, (hnf, (hng, hnh))))))),
           (hp1,
            hp2)));
         do 10
          match goal with
          | id1:(?X1 = ?X2) |- ?X3 => try rewrite id1; clear id1
          end ].
     discriminate hl.
     (* ~(inside_square_1 o1 o2) *)    
     intro H_inside_1'.
     case (inside_square_2_dec_inf o1 o2).    
      (* (inside_square_2 o1 o2) *)
      intro H_inside_2.
      generalize
       (Qquadratic_sign_nRdL_nRdL_9 a b c d e f g h 
          (nR xs) (dL ys) H_Qquadratic_sg_denom_nonzero).
      intros H1.
      assert
       (H_tuple_eq :
        ((-1)%Z, (na, (nb, (nc, nd)), (ne, (nf, (ng, nh))), (np1, np2))) =
        ((-1)%Z, (a, (b, (c, d)), (e, (f, (g, h))), (nR xs, dL ys))));
       [ apply
          trans_eq
           with
             (Qquadratic_sign a b c d e f g h (nR xs) 
                (dL ys) H_Qquadratic_sg_denom_nonzero);
          [ apply sym_eq | apply H1; discriminate || (repeat split) ];
          assumption
       | generalize
          (Qquadratic_sign_tuple_equal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
             _ _ _ H_tuple_eq);
          intros
           (hl,
            ((hna, (hnb, (hnc, (hnd, (hne, (hnf, (hng, hnh))))))),
            (hp1,
             hp2)));
          do 10
           match goal with
           | id1:(?X1 = ?X2) |- ?X3 => try rewrite id1; clear id1
           end ].
      case (inside_square_2_inf _ _ H_inside_2); intros (Ho1, Ho2);
       [ left; split; [ apply outside_square_1 | apply outside_square_2 ]
       | right; split; [ apply outside_square_2 | apply outside_square_1 ] ];
       assumption.
      (*  ~(inside_square_1 o1 o2)/\~(inside_square_2 o1 o2) *)
      intros H_inside_2'. 
      generalize
       (Qquadratic_sign_nR_dL_10 a b c d e f g h (nR xs) xs 
          (dL ys) ys H_Qquadratic_sg_denom_nonzero
          (Qquadratic_signok_2 _ _ _ _ _ _ H_Qquadratic_sg_denom_nonzero)
          (refl_equal _) (refl_equal _)).
      intros H1.
      assert
       (H_tuple_eq :
        Qquadratic_sign (a + b) b (a + b + c + d) (b + d) 
          (e + f) f (e + f + g + h) (f + h) xs ys
          (Qquadratic_signok_2 e f g h xs ys H_Qquadratic_sg_denom_nonzero) =
        ((-1)%Z, (na, (nb, (nc, nd)), (ne, (nf, (ng, nh))), (np1, np2))));
       [ apply
          trans_eq
           with
             (Qquadratic_sign a b c d e f g h (nR xs) 
                (dL ys) H_Qquadratic_sg_denom_nonzero);
          [ apply sym_eq; apply H1; repeat split | idtac ]
       | apply
          (Qquadratic_sign_neg_1 (a + b)%Z b (a + b + c + d)%Z 
             (b + d)%Z (e + f)%Z f (e + f + g + h)%Z 
             (f + h)%Z xs ys
             (Qquadratic_signok_2 e f g h xs ys H_Qquadratic_sg_denom_nonzero)
             na nb nc nd ne nf ng nh np1 np2) ]; assumption.

  (*  p1 = (nR xs) & p2 = One *)
  generalize (Qquadratic_signok_0' _ _ _ _ _ H_Qquadratic_sg_denom_nonzero).
  intros H_Qhomographic_sg_denom_nonzero.
  set
   (L3 :=
    Qhomographic_sign (a + b) (c + d) (e + f) (g + h) 
      (nR xs) H_Qhomographic_sg_denom_nonzero) in *.
  set (l1 := fst L3) in *.
  set (l2 := fst (snd L3)) in *.
  set (l3 := snd (snd L3)) in *.
  set (na_ := fst l2) in *.
  set (nb_ := fst (snd l2)) in *.
  set (nc_ := fst (snd (snd l2))) in *.
  set (nd_ := snd (snd (snd l2))) in *.
  generalize
   (Qquadratic_sign_nRdL_One a b c d e f g h (nR xs) One
      H_Qquadratic_sg_denom_nonzero l1 na_ nb_ nc_ nd_ l3
      H_Qhomographic_sg_denom_nonzero); intros H1.
  assert
   (H_tuple_eq :
    ((-1)%Z, (na, (nb, (nc, nd)), (ne, (nf, (ng, nh))), (np1, np2))) =
    (l1, (0%Z, (na_, (0%Z, nb_)), (0%Z, (nc_, (0%Z, nd_))), (l3, One))));
   [ apply
      trans_eq
       with
         (Qquadratic_sign a b c d e f g h (nR xs) One
            H_Qquadratic_sg_denom_nonzero);
      [ apply sym_eq; assumption
      | apply H1; fold L3 in |- *; repeat (apply pair_2; try reflexivity);
         discriminate || reflexivity ]
   | generalize
      (Qquadratic_sign_tuple_equal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
         _ H_tuple_eq);
      intros
       (hl,
        ((hna, (hnb, (hnc, (hnd, (hne, (hnf, (hng, hnh))))))),
        (hp1,
         hp2)));
      do 10
       match goal with
       | id1:(?X1 = ?X2) |- ?X3 => try rewrite id1; clear id1
       end; repeat rewrite ZERO_left; repeat rewrite Zplus_0_r ];
   apply
    (sg_neg_1 (a + b) (c + d) (e + f) (g + h) (nR xs)
       H_Qhomographic_sg_denom_nonzero na_ nb_ nc_ nd_ l3); 
   rewrite hl; fold L3 in |- *; repeat (apply pair_2; try reflexivity);
   discriminate || reflexivity.

 (* p1 = (dL xs) *)
 destruct p2 as [ys| ys| ].
  (*  p1 = (nR xs) & p2 = (nR ys) *)
  case (three_integers_dec_inf b c d).  
   (* `b = 0`/\`c = 0`/\`d = 0` *)
   intros (Hb, (Hc, Hd)).
   (* Intros [Hb [Hc] Hd]. *)
   case (three_integers_dec_inf f g h).   
    (* `f = 0`/\`g = 0`/\`h = 0` *)
    intros (Hf, (Hg, Hh)).
    generalize
     (Qquadratic_sign_nRdL_nRdL_1 a b c d e f g h (dL xs) 
        (nR ys) H_Qquadratic_sg_denom_nonzero).
    intros H1.
    assert
     (H_tuple_eq :
      ((-1)%Z, (na, (nb, (nc, nd)), (ne, (nf, (ng, nh))), (np1, np2))) =
      ((Z.sgn a * Z.sgn e)%Z,
      (a, (b, (c, d)), (e, (f, (g, h))), (dL xs, nR ys))));
     [ apply
        trans_eq
         with
           (Qquadratic_sign a b c d e f g h (dL xs) 
              (nR ys) H_Qquadratic_sg_denom_nonzero);
        [ apply sym_eq | apply H1; discriminate || (repeat split) ];
        assumption
     | generalize
        (Qquadratic_sign_tuple_equal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
           _ _ H_tuple_eq);
        intros
         (hl,
          ((hna, (hnb, (hnc, (hnd, (hne, (hnf, (hng, hnh))))))),
          (hp1,
           hp2)));
        do 10
         match goal with
         | id1:(?X1 = ?X2) |- ?X3 => try rewrite id1; clear id1
         end ].
    rewrite <- Zsgn_15 in hl.
    case (Zsgn_17 _ _ (sym_eq hl)); intros (Ha, He); [ left | right ];
     repeat split;
     repeat
      match goal with
      | id1:(?X1 = 0%Z) |- ?X2 => rewrite id1; clear id1
      end; repeat rewrite Zplus_0_r; assumption.
    (* ~(`f = 0`/\`g = 0`/\`h = 0`) *)
    intros H_fgh'.
    case (Z_lt_dec 2 o2).
     (*  `2 < o2` *)
     intro Ho2.
     generalize
      (Qquadratic_sign_nRdL_nRdL_2 a b c d e f g h 
         (dL xs) (nR ys) H_Qquadratic_sg_denom_nonzero).
     intros H1.
     assert
      (H_tuple_eq :
       ((-1)%Z, (na, (nb, (nc, nd)), (ne, (nf, (ng, nh))), (np1, np2))) =
       (Z.sgn a, (a, (b, (c, d)), (e, (f, (g, h))), (dL xs, nR ys))));
      [ apply
         trans_eq
          with
            (Qquadratic_sign a b c d e f g h (dL xs) 
               (nR ys) H_Qquadratic_sg_denom_nonzero);
         [ apply sym_eq | apply H1; discriminate || (repeat split) ];
         assumption
      | generalize
         (Qquadratic_sign_tuple_equal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
            _ _ H_tuple_eq);
         intros
          (hl,
           ((hna, (hnb, (hnc, (hnd, (hne, (hnf, (hng, hnh))))))),
           (hp1,
            hp2)));
         do 10
          match goal with
          | id1:(?X1 = ?X2) |- ?X3 => try rewrite id1; clear id1
          end ].
     right; split;
      repeat
       match goal with
       | id1:(?X1 = 0%Z) |- ?X2 => rewrite id1; clear id1
       end; repeat rewrite Zplus_0_r;
      [ apply Zsgn_10; apply sym_eq | apply outside_square_1 ]; 
      assumption.
     (*  ~`2 < o2` *)
     case (Z_lt_dec o2 (-2)).     
     (* `(-2) < o2` *)
      intros Ho2' Ho2.
      generalize
       (Qquadratic_sign_nRdL_nRdL_3 a b c d e f g h 
          (dL xs) (nR ys) H_Qquadratic_sg_denom_nonzero).
      intros H1.
      assert
       (H_tuple_eq :
        ((-1)%Z, (na, (nb, (nc, nd)), (ne, (nf, (ng, nh))), (np1, np2))) =
        ((- Z.sgn a)%Z, (a, (b, (c, d)), (e, (f, (g, h))), (dL xs, nR ys))));
       [ apply
          trans_eq
           with
             (Qquadratic_sign a b c d e f g h (dL xs) 
                (nR ys) H_Qquadratic_sg_denom_nonzero);
          [ apply sym_eq | apply H1; discriminate || (repeat split) ];
          assumption
       | generalize
          (Qquadratic_sign_tuple_equal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
             _ _ _ H_tuple_eq);
          intros
           (hl,
            ((hna, (hnb, (hnc, (hnd, (hne, (hnf, (hng, hnh))))))),
            (hp1,
             hp2)));
          do 10
           match goal with
           | id1:(?X1 = ?X2) |- ?X3 => try rewrite id1; clear id1
           end ].
      left; split;
       repeat
        match goal with
        | id1:(?X1 = 0%Z) |- ?X2 => rewrite id1; clear id1
        end; repeat rewrite Zplus_0_r;
       [ apply Zsgn_9; apply sym_eq; apply Z.opp_inj; assumption
       | apply outside_square_2; assumption ]. 
     (* ~`o1 < (-2)` /\ ~`2 < o1` *)
      intros Ho2' Ho2.
      generalize
       (Qquadratic_sign_dL_nR_4 a b c d e f g h (dL xs) xs 
          (nR ys) ys H_Qquadratic_sg_denom_nonzero
          (Qquadratic_signok_3 _ _ _ _ _ _ H_Qquadratic_sg_denom_nonzero)
          (refl_equal _) (refl_equal _)).
      intros H1.
      assert
       (H_tuple_eq :
        Qquadratic_sign (a + c) (a + b + c + d) c (c + d) 
          (e + g) (e + f + g + h) g (g + h) xs ys
          (Qquadratic_signok_3 e f g h xs ys H_Qquadratic_sg_denom_nonzero) =
        ((-1)%Z, (na, (nb, (nc, nd)), (ne, (nf, (ng, nh))), (np1, np2))));
       [ apply
          trans_eq
           with
             (Qquadratic_sign a b c d e f g h (dL xs) 
                (nR ys) H_Qquadratic_sg_denom_nonzero);
          [ apply sym_eq; apply H1; repeat split | idtac ]
       | apply
          (Qquadratic_sign_neg_1 (a + c)%Z (a + b + c + d)%Z c 
             (c + d)%Z (e + g)%Z (e + f + g + h)%Z g 
             (g + h)%Z xs ys
             (Qquadratic_signok_3 e f g h xs ys H_Qquadratic_sg_denom_nonzero)
             na nb nc nd ne nf ng nh np1 np2) ]; assumption.
   (* ~ `b = 0`/\`c = 0`/\`d = 0` *)
   intros Hbcd'.
   (* Intros [Hb [Hc] Hd]. *)
   case (three_integers_dec_inf f g h).   
    (* `f = 0`/\`g = 0`/\`h = 0` *)
    intros (Hf, (Hg, Hh)).
    case (Z_lt_dec 2 o1).
     (*  `2 < o1` *)
     intro Ho1.
     generalize
      (Qquadratic_sign_nRdL_nRdL_5 a b c d e f g h 
         (dL xs) (nR ys) H_Qquadratic_sg_denom_nonzero).
     intros H1.
     assert
      (H_tuple_eq :
       ((-1)%Z, (na, (nb, (nc, nd)), (ne, (nf, (ng, nh))), (np1, np2))) =
       (Z.sgn e, (a, (b, (c, d)), (e, (f, (g, h))), (dL xs, nR ys))));
      [ apply
         trans_eq
          with
            (Qquadratic_sign a b c d e f g h (dL xs) 
               (nR ys) H_Qquadratic_sg_denom_nonzero);
         [ apply sym_eq | apply H1; discriminate || (repeat split) ];
         assumption
      | generalize
         (Qquadratic_sign_tuple_equal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
            _ _ H_tuple_eq);
         intros
          (hl,
           ((hna, (hnb, (hnc, (hnd, (hne, (hnf, (hng, hnh))))))),
           (hp1,
            hp2)));
         do 10
          match goal with
          | id1:(?X1 = ?X2) |- ?X3 => try rewrite id1; clear id1
          end ].
     left; split;
      repeat
       match goal with
       | id1:(?X1 = 0%Z) |- ?X2 => rewrite id1; clear id1
       end; repeat rewrite Zplus_0_r;
      [ apply outside_square_1 | apply Zsgn_10; apply sym_eq ]; 
      assumption.
     (*  ~`2 < o1` *)
     case (Z_lt_dec o1 (-2)).
      (* `(-2) < o1` *)
      intros Ho1' Ho1.
      generalize
       (Qquadratic_sign_nRdL_nRdL_6 a b c d e f g h 
          (dL xs) (nR ys) H_Qquadratic_sg_denom_nonzero).
      intros H1.
      assert
       (H_tuple_eq :
        ((-1)%Z, (na, (nb, (nc, nd)), (ne, (nf, (ng, nh))), (np1, np2))) =
        ((- Z.sgn e)%Z, (a, (b, (c, d)), (e, (f, (g, h))), (dL xs, nR ys))));
       [ apply
          trans_eq
           with
             (Qquadratic_sign a b c d e f g h (dL xs) 
                (nR ys) H_Qquadratic_sg_denom_nonzero);
          [ apply sym_eq | apply H1; discriminate || (repeat split) ];
          assumption
       | generalize
          (Qquadratic_sign_tuple_equal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
             _ _ _ H_tuple_eq);
          intros
           (hl,
            ((hna, (hnb, (hnc, (hnd, (hne, (hnf, (hng, hnh))))))),
            (hp1,
             hp2)));
          do 10
           match goal with
           | id1:(?X1 = ?X2) |- ?X3 => try rewrite id1; clear id1
           end ].
      right; split;
       repeat
        match goal with
        | id1:(?X1 = 0%Z) |- ?X2 => rewrite id1; clear id1
        end; repeat rewrite Zplus_0_r;
       [ apply outside_square_2
       | apply Zsgn_9; apply sym_eq; apply Z.opp_inj ]; 
       assumption.
      (* ~`o1 < (-2)` /\ ~`2 < o1` *)
      intros Ho2' Ho2.
      generalize
       (Qquadratic_sign_dL_nR_7 a b c d e f g h (dL xs) xs 
          (nR ys) ys H_Qquadratic_sg_denom_nonzero
          (Qquadratic_signok_3 _ _ _ _ _ _ H_Qquadratic_sg_denom_nonzero)
          (refl_equal _) (refl_equal _)).
      intros H1.
      assert
       (H_tuple_eq :
        Qquadratic_sign (a + c) (a + b + c + d) c (c + d) 
          (e + g) (e + f + g + h) g (g + h) xs ys
          (Qquadratic_signok_3 e f g h xs ys H_Qquadratic_sg_denom_nonzero) =
        ((-1)%Z, (na, (nb, (nc, nd)), (ne, (nf, (ng, nh))), (np1, np2))));
       [ apply
          trans_eq
           with
             (Qquadratic_sign a b c d e f g h (dL xs) 
                (nR ys) H_Qquadratic_sg_denom_nonzero);
          [ apply sym_eq; apply H1; repeat split | idtac ]
       | apply
          (Qquadratic_sign_neg_1 (a + c)%Z (a + b + c + d)%Z c 
             (c + d)%Z (e + g)%Z (e + f + g + h)%Z g 
             (g + h)%Z xs ys
             (Qquadratic_signok_3 e f g h xs ys H_Qquadratic_sg_denom_nonzero)
             na nb nc nd ne nf ng nh np1 np2) ]; assumption.
    (* ~(`f = 0`/\`g = 0`/\`h = 0`) *)
    intro Hfgh'.
    case (inside_square_1_dec_inf o1 o2).    
     (* (inside_square_1 o1 o2) *)
     intro H_inside_1.
     generalize
      (Qquadratic_sign_nRdL_nRdL_8 a b c d e f g h 
         (dL xs) (nR ys) H_Qquadratic_sg_denom_nonzero).
     intros H1.
     assert
      (H_tuple_eq :
       ((-1)%Z, (na, (nb, (nc, nd)), (ne, (nf, (ng, nh))), (np1, np2))) =
       (1%Z, (a, (b, (c, d)), (e, (f, (g, h))), (dL xs, nR ys))));
      [ apply
         trans_eq
          with
            (Qquadratic_sign a b c d e f g h (dL xs) 
               (nR ys) H_Qquadratic_sg_denom_nonzero);
         [ apply sym_eq | apply H1; discriminate || (repeat split) ];
         assumption
      | generalize
         (Qquadratic_sign_tuple_equal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
            _ _ H_tuple_eq);
         intros
          (hl,
           ((hna, (hnb, (hnc, (hnd, (hne, (hnf, (hng, hnh))))))),
           (hp1,
            hp2)));
         do 10
          match goal with
          | id1:(?X1 = ?X2) |- ?X3 => try rewrite id1; clear id1
          end ].
     discriminate hl.
     (* ~(inside_square_1 o1 o2) *)    
     intro H_inside_1'.
     case (inside_square_2_dec_inf o1 o2).    
      (* (inside_square_2 o1 o2) *)
      intro H_inside_2.
      generalize
       (Qquadratic_sign_nRdL_nRdL_9 a b c d e f g h 
          (dL xs) (nR ys) H_Qquadratic_sg_denom_nonzero).
      intros H1.
      assert
       (H_tuple_eq :
        ((-1)%Z, (na, (nb, (nc, nd)), (ne, (nf, (ng, nh))), (np1, np2))) =
        ((-1)%Z, (a, (b, (c, d)), (e, (f, (g, h))), (dL xs, nR ys))));
       [ apply
          trans_eq
           with
             (Qquadratic_sign a b c d e f g h (dL xs) 
                (nR ys) H_Qquadratic_sg_denom_nonzero);
          [ apply sym_eq | apply H1; discriminate || (repeat split) ];
          assumption
       | generalize
          (Qquadratic_sign_tuple_equal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
             _ _ _ H_tuple_eq);
          intros
           (hl,
            ((hna, (hnb, (hnc, (hnd, (hne, (hnf, (hng, hnh))))))),
            (hp1,
             hp2)));
          do 10
           match goal with
           | id1:(?X1 = ?X2) |- ?X3 => try rewrite id1; clear id1
           end ].
     case (inside_square_2_inf _ _ H_inside_2); intros (Ho1, Ho2);
      [ left; split; [ apply outside_square_1 | apply outside_square_2 ]
      | right; split; [ apply outside_square_2 | apply outside_square_1 ] ];
      assumption.
      (*  ~(inside_square_1 o1 o2)/\~(inside_square_2 o1 o2) *)
      intros H_inside_2'. 
      generalize
       (Qquadratic_sign_dL_nR_10 a b c d e f g h (dL xs) xs 
          (nR ys) ys H_Qquadratic_sg_denom_nonzero
          (Qquadratic_signok_3 _ _ _ _ _ _ H_Qquadratic_sg_denom_nonzero)
          (refl_equal _) (refl_equal _)).
      intros H1.
      assert
       (H_tuple_eq :
        Qquadratic_sign (a + c) (a + b + c + d) c (c + d) 
          (e + g) (e + f + g + h) g (g + h) xs ys
          (Qquadratic_signok_3 e f g h xs ys H_Qquadratic_sg_denom_nonzero) =
        ((-1)%Z, (na, (nb, (nc, nd)), (ne, (nf, (ng, nh))), (np1, np2))));
       [ apply
          trans_eq
           with
             (Qquadratic_sign a b c d e f g h (dL xs) 
                (nR ys) H_Qquadratic_sg_denom_nonzero);
          [ apply sym_eq; apply H1; repeat split | idtac ]
       | apply
          (Qquadratic_sign_neg_1 (a + c)%Z (a + b + c + d)%Z c 
             (c + d)%Z (e + g)%Z (e + f + g + h)%Z g 
             (g + h)%Z xs ys
             (Qquadratic_signok_3 e f g h xs ys H_Qquadratic_sg_denom_nonzero)
             na nb nc nd ne nf ng nh np1 np2) ]; assumption.

  (*  p1 = (dL xs) & p2 = (dL ys) *)
  case (three_integers_dec_inf b c d).  
   (* `b = 0`/\`c = 0`/\`d = 0` *)
   intros (Hb, (Hc, Hd)).
   (* Intros [Hb [Hc] Hd]. *)
   case (three_integers_dec_inf f g h).   
    (* `f = 0`/\`g = 0`/\`h = 0` *)
    intros (Hf, (Hg, Hh)).
    generalize
     (Qquadratic_sign_nRdL_nRdL_1 a b c d e f g h (dL xs) 
        (dL ys) H_Qquadratic_sg_denom_nonzero).
    intros H1.
    assert
     (H_tuple_eq :
      ((-1)%Z, (na, (nb, (nc, nd)), (ne, (nf, (ng, nh))), (np1, np2))) =
      ((Z.sgn a * Z.sgn e)%Z,
      (a, (b, (c, d)), (e, (f, (g, h))), (dL xs, dL ys))));
     [ apply
        trans_eq
         with
           (Qquadratic_sign a b c d e f g h (dL xs) 
              (dL ys) H_Qquadratic_sg_denom_nonzero);
        [ apply sym_eq | apply H1; discriminate || (repeat split) ];
        assumption
     | generalize
        (Qquadratic_sign_tuple_equal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
           _ _ H_tuple_eq);
        intros
         (hl,
          ((hna, (hnb, (hnc, (hnd, (hne, (hnf, (hng, hnh))))))),
          (hp1,
           hp2)));
        do 10
         match goal with
         | id1:(?X1 = ?X2) |- ?X3 => try rewrite id1; clear id1
         end ].
    rewrite <- Zsgn_15 in hl.
    case (Zsgn_17 _ _ (sym_eq hl)); intros (Ha, He); [ left | right ];
     repeat split;
     repeat
      match goal with
      | id1:(?X1 = 0%Z) |- ?X2 => rewrite id1; clear id1
      end; repeat rewrite Zplus_0_r; assumption.
    (* ~(`f = 0`/\`g = 0`/\`h = 0`) *)
    intros H_fgh'.
    case (Z_lt_dec 2 o2).
     (*  `2 < o2` *)
     intro Ho2.
     generalize
      (Qquadratic_sign_nRdL_nRdL_2 a b c d e f g h 
         (dL xs) (dL ys) H_Qquadratic_sg_denom_nonzero).
     intros H1.
     assert
      (H_tuple_eq :
       ((-1)%Z, (na, (nb, (nc, nd)), (ne, (nf, (ng, nh))), (np1, np2))) =
       (Z.sgn a, (a, (b, (c, d)), (e, (f, (g, h))), (dL xs, dL ys))));
      [ apply
         trans_eq
          with
            (Qquadratic_sign a b c d e f g h (dL xs) 
               (dL ys) H_Qquadratic_sg_denom_nonzero);
         [ apply sym_eq | apply H1; discriminate || (repeat split) ];
         assumption
      | generalize
         (Qquadratic_sign_tuple_equal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
            _ _ H_tuple_eq);
         intros
          (hl,
           ((hna, (hnb, (hnc, (hnd, (hne, (hnf, (hng, hnh))))))),
           (hp1,
            hp2)));
         do 10
          match goal with
          | id1:(?X1 = ?X2) |- ?X3 => try rewrite id1; clear id1
          end ].
     right; split;
      repeat
       match goal with
       | id1:(?X1 = 0%Z) |- ?X2 => rewrite id1; clear id1
       end; repeat rewrite Zplus_0_r;
      [ apply Zsgn_10; apply sym_eq; assumption
      | apply outside_square_1; assumption ].
     (*  ~`2 < o2` *)
     case (Z_lt_dec o2 (-2)).     
     (* `(-2) < o2` *)
      intros Ho2' Ho2.
      generalize
       (Qquadratic_sign_nRdL_nRdL_3 a b c d e f g h 
          (dL xs) (dL ys) H_Qquadratic_sg_denom_nonzero).
      intros H1.
      assert
       (H_tuple_eq :
        ((-1)%Z, (na, (nb, (nc, nd)), (ne, (nf, (ng, nh))), (np1, np2))) =
        ((- Z.sgn a)%Z, (a, (b, (c, d)), (e, (f, (g, h))), (dL xs, dL ys))));
       [ apply
          trans_eq
           with
             (Qquadratic_sign a b c d e f g h (dL xs) 
                (dL ys) H_Qquadratic_sg_denom_nonzero);
          [ apply sym_eq | apply H1; discriminate || (repeat split) ];
          assumption
       | generalize
          (Qquadratic_sign_tuple_equal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
             _ _ _ H_tuple_eq);
          intros
           (hl,
            ((hna, (hnb, (hnc, (hnd, (hne, (hnf, (hng, hnh))))))),
            (hp1,
             hp2)));
          do 10
           match goal with
           | id1:(?X1 = ?X2) |- ?X3 => try rewrite id1; clear id1
           end ].
      left; split;
       repeat
        match goal with
        | id1:(?X1 = 0%Z) |- ?X2 => rewrite id1; clear id1
        end; repeat rewrite Zplus_0_r;
       [ apply Zsgn_9; apply sym_eq; apply Z.opp_inj; assumption
       | apply outside_square_2; assumption ]. 
     (* ~`o1 < (-2)` /\ ~`2 < o1` *)
      intros Ho2' Ho2.
      generalize
       (Qquadratic_sign_dL_dL_4 a b c d e f g h (dL xs) xs 
          (dL ys) ys H_Qquadratic_sg_denom_nonzero
          (Qquadratic_signok_4 _ _ _ _ _ _ H_Qquadratic_sg_denom_nonzero)
          (refl_equal _) (refl_equal _)).
      intros H1.
      assert
       (H_tuple_eq :
        Qquadratic_sign (a + b + c + d) (b + d) (c + d) d 
          (e + f + g + h) (f + h) (g + h) h xs ys
          (Qquadratic_signok_4 e f g h xs ys H_Qquadratic_sg_denom_nonzero) =
        ((-1)%Z, (na, (nb, (nc, nd)), (ne, (nf, (ng, nh))), (np1, np2))));
       [ apply
          trans_eq
           with
             (Qquadratic_sign a b c d e f g h (dL xs) 
                (dL ys) H_Qquadratic_sg_denom_nonzero);
          [ apply sym_eq; apply H1; repeat split | idtac ]
       | apply
          (Qquadratic_sign_neg_1 (a + b + c + d)%Z 
             (b + d)%Z (c + d)%Z d (e + f + g + h)%Z 
             (f + h)%Z (g + h)%Z h xs ys
             (Qquadratic_signok_4 e f g h xs ys H_Qquadratic_sg_denom_nonzero)
             na nb nc nd ne nf ng nh np1 np2) ]; assumption.
   (* ~ `b = 0`/\`c = 0`/\`d = 0` *)
   intros Hbcd'.
   (* Intros [Hb [Hc] Hd]. *)
   case (three_integers_dec_inf f g h).   
    (* `f = 0`/\`g = 0`/\`h = 0` *)
    intros (Hf, (Hg, Hh)).
    case (Z_lt_dec 2 o1).
     (*  `2 < o1` *)
     intro Ho1.
     generalize
      (Qquadratic_sign_nRdL_nRdL_5 a b c d e f g h 
         (dL xs) (dL ys) H_Qquadratic_sg_denom_nonzero).
     intros H1.
     assert
      (H_tuple_eq :
       ((-1)%Z, (na, (nb, (nc, nd)), (ne, (nf, (ng, nh))), (np1, np2))) =
       (Z.sgn e, (a, (b, (c, d)), (e, (f, (g, h))), (dL xs, dL ys))));
      [ apply
         trans_eq
          with
            (Qquadratic_sign a b c d e f g h (dL xs) 
               (dL ys) H_Qquadratic_sg_denom_nonzero);
         [ apply sym_eq | apply H1; discriminate || (repeat split) ];
         assumption
      | generalize
         (Qquadratic_sign_tuple_equal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
            _ _ H_tuple_eq);
         intros
          (hl,
           ((hna, (hnb, (hnc, (hnd, (hne, (hnf, (hng, hnh))))))),
           (hp1,
            hp2)));
         do 10
          match goal with
          | id1:(?X1 = ?X2) |- ?X3 => try rewrite id1; clear id1
          end ].
     left; split;
      repeat
       match goal with
       | id1:(?X1 = 0%Z) |- ?X2 => rewrite id1; clear id1
       end; repeat rewrite Zplus_0_r;
      [ apply outside_square_1 | apply Zsgn_10; apply sym_eq ]; 
      assumption.
     (*  ~`2 < o1` *)
     case (Z_lt_dec o1 (-2)).
      (* `(-2) < o1` *)
      intros Ho1' Ho1.
      generalize
       (Qquadratic_sign_nRdL_nRdL_6 a b c d e f g h 
          (dL xs) (dL ys) H_Qquadratic_sg_denom_nonzero).
      intros H1.
      assert
       (H_tuple_eq :
        ((-1)%Z, (na, (nb, (nc, nd)), (ne, (nf, (ng, nh))), (np1, np2))) =
        ((- Z.sgn e)%Z, (a, (b, (c, d)), (e, (f, (g, h))), (dL xs, dL ys))));
       [ apply
          trans_eq
           with
             (Qquadratic_sign a b c d e f g h (dL xs) 
                (dL ys) H_Qquadratic_sg_denom_nonzero);
          [ apply sym_eq | apply H1; discriminate || (repeat split) ];
          assumption
       | generalize
          (Qquadratic_sign_tuple_equal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
             _ _ _ H_tuple_eq);
          intros
           (hl,
            ((hna, (hnb, (hnc, (hnd, (hne, (hnf, (hng, hnh))))))),
            (hp1,
             hp2)));
          do 10
           match goal with
           | id1:(?X1 = ?X2) |- ?X3 => try rewrite id1; clear id1
           end ].
      right; split;
       repeat
        match goal with
        | id1:(?X1 = 0%Z) |- ?X2 => rewrite id1; clear id1
        end; repeat rewrite Zplus_0_r;
       [ apply outside_square_2
       | apply Zsgn_9; apply sym_eq; apply Z.opp_inj ]; 
       assumption.
      (* ~`o1 < (-2)` /\ ~`2 < o1` *)
      intros Ho2' Ho2.
      generalize
       (Qquadratic_sign_dL_dL_7 a b c d e f g h (dL xs) xs 
          (dL ys) ys H_Qquadratic_sg_denom_nonzero
          (Qquadratic_signok_4 _ _ _ _ _ _ H_Qquadratic_sg_denom_nonzero)
          (refl_equal _) (refl_equal _)).
      intros H1.
      assert
       (H_tuple_eq :
        Qquadratic_sign (a + b + c + d) (b + d) (c + d) d 
          (e + f + g + h) (f + h) (g + h) h xs ys
          (Qquadratic_signok_4 e f g h xs ys H_Qquadratic_sg_denom_nonzero) =
        ((-1)%Z, (na, (nb, (nc, nd)), (ne, (nf, (ng, nh))), (np1, np2))));
       [ apply
          trans_eq
           with
             (Qquadratic_sign a b c d e f g h (dL xs) 
                (dL ys) H_Qquadratic_sg_denom_nonzero);
          [ apply sym_eq; apply H1; repeat split | idtac ]
       | apply
          (Qquadratic_sign_neg_1 (a + b + c + d)%Z 
             (b + d)%Z (c + d)%Z d (e + f + g + h)%Z 
             (f + h)%Z (g + h)%Z h xs ys
             (Qquadratic_signok_4 e f g h xs ys H_Qquadratic_sg_denom_nonzero)
             na nb nc nd ne nf ng nh np1 np2) ]; assumption.
    (* ~(`f = 0`/\`g = 0`/\`h = 0`) *)
    intro Hfgh'.
    case (inside_square_1_dec_inf o1 o2).    
     (* (inside_square_1 o1 o2) *)
     intro H_inside_1.
     generalize
      (Qquadratic_sign_nRdL_nRdL_8 a b c d e f g h 
         (dL xs) (dL ys) H_Qquadratic_sg_denom_nonzero).
     intros H1.
     assert
      (H_tuple_eq :
       ((-1)%Z, (na, (nb, (nc, nd)), (ne, (nf, (ng, nh))), (np1, np2))) =
       (1%Z, (a, (b, (c, d)), (e, (f, (g, h))), (dL xs, dL ys))));
      [ apply
         trans_eq
          with
            (Qquadratic_sign a b c d e f g h (dL xs) 
               (dL ys) H_Qquadratic_sg_denom_nonzero);
         [ apply sym_eq | apply H1; discriminate || (repeat split) ];
         assumption
      | generalize
         (Qquadratic_sign_tuple_equal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
            _ _ H_tuple_eq);
         intros
          (hl,
           ((hna, (hnb, (hnc, (hnd, (hne, (hnf, (hng, hnh))))))),
           (hp1,
            hp2)));
         do 10
          match goal with
          | id1:(?X1 = ?X2) |- ?X3 => try rewrite id1; clear id1
          end ].
     discriminate hl.
     (* ~(inside_square_1 o1 o2) *)    
     intro H_inside_1'.
     case (inside_square_2_dec_inf o1 o2).    
      (* (inside_square_2 o1 o2) *)
      intro H_inside_2.
      generalize
       (Qquadratic_sign_nRdL_nRdL_9 a b c d e f g h 
          (dL xs) (dL ys) H_Qquadratic_sg_denom_nonzero).
      intros H1.
      assert
       (H_tuple_eq :
        ((-1)%Z, (na, (nb, (nc, nd)), (ne, (nf, (ng, nh))), (np1, np2))) =
        ((-1)%Z, (a, (b, (c, d)), (e, (f, (g, h))), (dL xs, dL ys))));
       [ apply
          trans_eq
           with
             (Qquadratic_sign a b c d e f g h (dL xs) 
                (dL ys) H_Qquadratic_sg_denom_nonzero);
          [ apply sym_eq | apply H1; discriminate || (repeat split) ];
          assumption
       | generalize
          (Qquadratic_sign_tuple_equal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
             _ _ _ H_tuple_eq);
          intros
           (hl,
            ((hna, (hnb, (hnc, (hnd, (hne, (hnf, (hng, hnh))))))),
            (hp1,
             hp2)));
          do 10
           match goal with
           | id1:(?X1 = ?X2) |- ?X3 => try rewrite id1; clear id1
           end ].
      case (inside_square_2_inf _ _ H_inside_2); intros (Ho1, Ho2);
       [ left; split; [ apply outside_square_1 | apply outside_square_2 ]
       | right; split; [ apply outside_square_2 | apply outside_square_1 ] ];
       assumption.
      (*  ~(inside_square_1 o1 o2)/\~(inside_square_2 o1 o2) *)
      intros H_inside_2'. 
      generalize
       (Qquadratic_sign_dL_dL_10 a b c d e f g h (dL xs) xs 
          (dL ys) ys H_Qquadratic_sg_denom_nonzero
          (Qquadratic_signok_4 _ _ _ _ _ _ H_Qquadratic_sg_denom_nonzero)
          (refl_equal _) (refl_equal _)).
      intros H1.
      assert
       (H_tuple_eq :
        Qquadratic_sign (a + b + c + d) (b + d) (c + d) d 
          (e + f + g + h) (f + h) (g + h) h xs ys
          (Qquadratic_signok_4 e f g h xs ys H_Qquadratic_sg_denom_nonzero) =
        ((-1)%Z, (na, (nb, (nc, nd)), (ne, (nf, (ng, nh))), (np1, np2))));
       [ apply
          trans_eq
           with
             (Qquadratic_sign a b c d e f g h (dL xs) 
                (dL ys) H_Qquadratic_sg_denom_nonzero);
          [ apply sym_eq; apply H1; repeat split | idtac ]
       | apply
          (Qquadratic_sign_neg_1 (a + b + c + d)%Z 
             (b + d)%Z (c + d)%Z d (e + f + g + h)%Z 
             (f + h)%Z (g + h)%Z h xs ys
             (Qquadratic_signok_4 e f g h xs ys H_Qquadratic_sg_denom_nonzero)
             na nb nc nd ne nf ng nh np1 np2) ]; assumption.

  (*  p1 = (dL xs) & p2 = One *)
  generalize (Qquadratic_signok_0' _ _ _ _ _ H_Qquadratic_sg_denom_nonzero).
  intros H_Qhomographic_sg_denom_nonzero.
  set
   (L3 :=
    Qhomographic_sign (a + b) (c + d) (e + f) (g + h) 
      (dL xs) H_Qhomographic_sg_denom_nonzero) in *.
  set (l1 := fst L3) in *.
  set (l2 := fst (snd L3)) in *.
  set (l3 := snd (snd L3)) in *.
  set (na_ := fst l2) in *.
  set (nb_ := fst (snd l2)) in *.
  set (nc_ := fst (snd (snd l2))) in *.
  set (nd_ := snd (snd (snd l2))) in *.
  generalize
   (Qquadratic_sign_nRdL_One a b c d e f g h (dL xs) One
      H_Qquadratic_sg_denom_nonzero l1 na_ nb_ nc_ nd_ l3
      H_Qhomographic_sg_denom_nonzero); intros H1.
  assert
   (H_tuple_eq :
    ((-1)%Z, (na, (nb, (nc, nd)), (ne, (nf, (ng, nh))), (np1, np2))) =
    (l1, (0%Z, (na_, (0%Z, nb_)), (0%Z, (nc_, (0%Z, nd_))), (l3, One))));
   [ apply
      trans_eq
       with
         (Qquadratic_sign a b c d e f g h (dL xs) One
            H_Qquadratic_sg_denom_nonzero);
      [ apply sym_eq; assumption
      | apply H1; fold L3 in |- *; repeat (apply pair_2; try reflexivity);
         discriminate || reflexivity ]
   | generalize
      (Qquadratic_sign_tuple_equal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
         _ H_tuple_eq);
      intros
       (hl,
        ((hna, (hnb, (hnc, (hnd, (hne, (hnf, (hng, hnh))))))),
        (hp1,
         hp2)));
      do 10
       match goal with
       | id1:(?X1 = ?X2) |- ?X3 => try rewrite id1; clear id1
       end; repeat rewrite ZERO_left; repeat rewrite Zplus_0_r ];
   apply
    (sg_neg_1 (a + b) (c + d) (e + f) (g + h) (dL xs)
       H_Qhomographic_sg_denom_nonzero na_ nb_ nc_ nd_ l3); 
   rewrite hl; fold L3 in |- *; repeat (apply pair_2; try reflexivity);
   discriminate || reflexivity.

 (* p1 = One *)
  generalize (Qquadratic_signok_0 _ _ _ _ _ H_Qquadratic_sg_denom_nonzero).
  intros H_Qhomographic_sg_denom_nonzero.
  set
   (L3 :=
    Qhomographic_sign (a + c) (b + d) (e + g) (f + h) p2
      H_Qhomographic_sg_denom_nonzero) in *.
  set (l1 := fst L3) in *.
  set (l2 := fst (snd L3)) in *.
  set (l3 := snd (snd L3)) in *.
  set (na_ := fst l2) in *.
  set (nb_ := fst (snd l2)) in *.
  set (nc_ := fst (snd (snd l2))) in *.
  set (nd_ := snd (snd (snd l2))) in *.
  generalize
   (Qquadratic_sign_One_y a b c d e f g h One p2
      H_Qquadratic_sg_denom_nonzero l1 na_ nb_ nc_ nd_ l3
      H_Qhomographic_sg_denom_nonzero); intros H1.
  assert
   (H_tuple_eq :
    ((-1)%Z, (na, (nb, (nc, nd)), (ne, (nf, (ng, nh))), (np1, np2))) =
    (l1, (0%Z, (0%Z, (na_, nb_)), (0%Z, (0%Z, (nc_, nd_))), (One, l3))));
   [ apply
      trans_eq
       with
         (Qquadratic_sign a b c d e f g h One p2
            H_Qquadratic_sg_denom_nonzero);
      [ apply sym_eq; assumption
      | apply H1; fold L3 in |- *; repeat (apply pair_2; try reflexivity);
         discriminate || reflexivity ]
   | generalize
      (Qquadratic_sign_tuple_equal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
         _ H_tuple_eq);
      intros
       (hl,
        ((hna, (hnb, (hnc, (hnd, (hne, (hnf, (hng, hnh))))))),
        (hp1,
         hp2)));
      do 10
       match goal with
       | id1:(?X1 = ?X2) |- ?X3 => try rewrite id1; clear id1
       end; repeat rewrite ZERO_left; repeat rewrite Zplus_0_r ];
   apply
    (sg_neg_1 (a + c) (b + d) (e + g) (f + h) p2
       H_Qhomographic_sg_denom_nonzero na_ nb_ nc_ nd_ l3); 
   rewrite hl; fold L3 in |- *; repeat (apply pair_2; try reflexivity);
   discriminate || reflexivity.
Qed.

Lemma Qquadratic_sign_neg_2 :
 forall (a b c d e f g h : Z) (p1 p2 : Qpositive)
   (H_Qquadratic_sg_denom_nonzero : Qquadratic_sg_denom_nonzero e f g h p1 p2)
   (na nb nc nd ne nf ng nh : Z) (np1 np2 : Qpositive),
 Qquadratic_sign a b c d e f g h p1 p2 H_Qquadratic_sg_denom_nonzero =
 ((-1)%Z, (na, (nb, (nc, nd)), (ne, (nf, (ng, nh))), (np1, np2))) ->
 {(0 <= na)%Z /\
  (0 <= nb)%Z /\
  (0 <= nc)%Z /\
  (0 <= nd)%Z /\ (ne <= 0)%Z /\ (nf <= 0)%Z /\ (ng <= 0)%Z /\ (nh <= 0)%Z} +
 {(na <= 0)%Z /\
  (nb <= 0)%Z /\
  (nc <= 0)%Z /\
  (nd <= 0)%Z /\ (0 <= ne)%Z /\ (0 <= nf)%Z /\ (0 <= ng)%Z /\ (0 <= nh)%Z} +
 {np1 = One /\
  (0 <= na + nc)%Z /\
  (0 <= nb + nd)%Z /\ (ne + ng <= 0)%Z /\ (nf + nh <= 0)%Z} +
 {np1 = One /\
  (na + nc <= 0)%Z /\
  (nb + nd <= 0)%Z /\ (0 <= ne + ng)%Z /\ (0 <= nf + nh)%Z} +
 {np1 = One /\ np2 = One} +
 {np1 <> One /\
  np2 = One /\
  (0 <= na + nb)%Z /\
  (0 <= nc + nd)%Z /\ (ne + nf <= 0)%Z /\ (ng + nh <= 0)%Z} +
 {np1 <> One /\
  np2 = One /\
  (na + nb <= 0)%Z /\
  (nc + nd <= 0)%Z /\ (0 <= ne + nf)%Z /\ (0 <= ng + nh)%Z}.
Proof.
 fix Qquadratic_sign_neg_2 9.
 intros.
 set (o1 := outside_square a b c d) in *.
 set (o2 := outside_square e f g h) in *.
 destruct p1 as [xs| xs| ].
 (* p1 = (nR xs) *)
 destruct p2 as [ys| ys| ].
  (*  p1 = (nR xs) & p2 = (nR ys) *)
  case (three_integers_dec_inf b c d).  
   (* `b = 0`/\`c = 0`/\`d = 0` *)
   intros (Hb, (Hc, Hd)).
   (* Intros [Hb [Hc] Hd]. *)
   case (three_integers_dec_inf f g h).   
    (* `f = 0`/\`g = 0`/\`h = 0` *)
    intros (Hf, (Hg, Hh)).
    generalize
     (Qquadratic_sign_nRdL_nRdL_1 a b c d e f g h (nR xs) 
        (nR ys) H_Qquadratic_sg_denom_nonzero).
    intros H1.
    assert
     (H_tuple_eq :
      ((-1)%Z, (na, (nb, (nc, nd)), (ne, (nf, (ng, nh))), (np1, np2))) =
      ((Z.sgn a * Z.sgn e)%Z,
      (a, (b, (c, d)), (e, (f, (g, h))), (nR xs, nR ys))));
     [ apply
        trans_eq
         with
           (Qquadratic_sign a b c d e f g h (nR xs) 
              (nR ys) H_Qquadratic_sg_denom_nonzero);
        [ apply sym_eq | apply H1; discriminate || (repeat split) ];
        assumption
     | generalize
        (Qquadratic_sign_tuple_equal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
           _ _ H_tuple_eq);
        intros
         (hl,
          ((hna, (hnb, (hnc, (hnd, (hne, (hnf, (hng, hnh))))))),
          (hp1,
           hp2)));
        do 10
         match goal with
         | id1:(?X1 = ?X2) |- ?X3 => try rewrite id1; clear id1
         end ].
    left; left; left; left; left; rewrite <- Zsgn_15 in hl.
    case (Zsgn_17 _ _ (sym_eq hl)); intros (Ha, He); [ left | right ];
     repeat split;
     repeat
      match goal with
      | id1:(?X1 = 0%Z) |- ?X2 => rewrite id1; clear id1
      end; first [ apply Z.le_refl | apply Zlt_le_weak ]; 
     assumption.
    (* ~(`f = 0`/\`g = 0`/\`h = 0`) *)
    intros H_fgh'.
    case (Z_lt_dec 2 o2).
     (*  `2 < o2` *)
     intro Ho2.
     generalize
      (Qquadratic_sign_nRdL_nRdL_2 a b c d e f g h 
         (nR xs) (nR ys) H_Qquadratic_sg_denom_nonzero).
     intros H1.
     assert
      (H_tuple_eq :
       ((-1)%Z, (na, (nb, (nc, nd)), (ne, (nf, (ng, nh))), (np1, np2))) =
       (Z.sgn a, (a, (b, (c, d)), (e, (f, (g, h))), (nR xs, nR ys))));
      [ apply
         trans_eq
          with
            (Qquadratic_sign a b c d e f g h (nR xs) 
               (nR ys) H_Qquadratic_sg_denom_nonzero);
         [ apply sym_eq | apply H1; discriminate || (repeat split) ];
         assumption
      | generalize
         (Qquadratic_sign_tuple_equal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
            _ _ H_tuple_eq);
         intros
          (hl,
           ((hna, (hnb, (hnc, (hnd, (hne, (hnf, (hng, hnh))))))),
           (hp1,
            hp2)));
         do 10
          match goal with
          | id1:(?X1 = ?X2) |- ?X3 => try rewrite id1; clear id1
          end ].
     left; left; left; left; left; right; repeat split;
      repeat
       match goal with
       | id1:(?X1 = 0%Z) |- ?X2 => rewrite id1; clear id1
       end; first
      [ apply Z.le_refl
      | match goal with
        |  |- (0 <= ?X1)%Z =>
            apply Zlt_le_weak; apply Zsgn_9; apply Z.opp_inj
        |  |- (?X1 <= 0)%Z => apply Zlt_le_weak; apply Zsgn_10
        end; apply sym_eq; assumption
      | unfold o2 in Ho2;
         match goal with
         | id1:(2 < outside_square ?X1 ?X2 ?X3 ?X4)%Z |- 
         (0 <= ?X1)%Z =>
             apply outside_square_3 with X2 X3 X4
         | id1:(2 < outside_square ?X1 ?X2 ?X3 ?X4)%Z |- 
         (0 <= ?X2)%Z =>
             apply outside_square_4 with X1 X3 X4
         | id1:(2 < outside_square ?X1 ?X2 ?X3 ?X4)%Z |- 
         (0 <= ?X3)%Z =>
             apply outside_square_5 with X1 X2 X4
         | id1:(2 < outside_square ?X1 ?X2 ?X3 ?X4)%Z |- 
         (0 <= ?X4)%Z =>
             apply outside_square_6 with X1 X2 X3
         | id1:(outside_square ?X1 ?X2 ?X3 ?X4 < -2)%Z |- 
         (?X1 <= 0)%Z =>
             apply outside_square_7 with X2 X3 X4
         | id1:(outside_square ?X1 ?X2 ?X3 ?X4 < -2)%Z |- 
         (?X2 <= 0)%Z =>
             apply outside_square_8 with X1 X3 X4
         | id1:(outside_square ?X1 ?X2 ?X3 ?X4 < -2)%Z |- 
         (?X3 <= 0)%Z =>
             apply outside_square_9 with X1 X2 X4
         | id1:(outside_square ?X1 ?X2 ?X3 ?X4 < -2)%Z |- 
         (?X4 <= 0)%Z => apply outside_square_10 with X1 X2 X3
         end; assumption ].
     
     (*  ~`2 < o2` *)
     case (Z_lt_dec o2 (-2)).     
     (* `(-2) < o2` *)
      intros Ho2' Ho2.
      generalize
       (Qquadratic_sign_nRdL_nRdL_3 a b c d e f g h 
          (nR xs) (nR ys) H_Qquadratic_sg_denom_nonzero).
      intros H1.
      assert
       (H_tuple_eq :
        ((-1)%Z, (na, (nb, (nc, nd)), (ne, (nf, (ng, nh))), (np1, np2))) =
        ((- Z.sgn a)%Z, (a, (b, (c, d)), (e, (f, (g, h))), (nR xs, nR ys))));
       [ apply
          trans_eq
           with
             (Qquadratic_sign a b c d e f g h (nR xs) 
                (nR ys) H_Qquadratic_sg_denom_nonzero);
          [ apply sym_eq | apply H1; discriminate || (repeat split) ];
          assumption
       | generalize
          (Qquadratic_sign_tuple_equal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
             _ _ _ H_tuple_eq);
          intros
           (hl,
            ((hna, (hnb, (hnc, (hnd, (hne, (hnf, (hng, hnh))))))),
            (hp1,
             hp2)));
          do 10
           match goal with
           | id1:(?X1 = ?X2) |- ?X3 => try rewrite id1; clear id1
           end ].
      left; left; left; left; left; left; repeat split;
       repeat
        match goal with
        | id1:(?X1 = 0%Z) |- ?X2 => rewrite id1; clear id1
        end; first
       [ apply Z.le_refl
       | match goal with
         |  |- (0 <= ?X1)%Z =>
             apply Zlt_le_weak; apply Zsgn_9; apply Z.opp_inj
         |  |- (?X1 <= 0)%Z => apply Zlt_le_weak; apply Zsgn_10
         end; apply sym_eq; assumption
       | unfold o2 in Ho2';
          match goal with
          | id1:(2 < outside_square ?X1 ?X2 ?X3 ?X4)%Z |- 
          (0 <= ?X1)%Z =>
              apply outside_square_3 with X2 X3 X4
          | id1:(2 < outside_square ?X1 ?X2 ?X3 ?X4)%Z |- 
          (0 <= ?X2)%Z =>
              apply outside_square_4 with X1 X3 X4
          | id1:(2 < outside_square ?X1 ?X2 ?X3 ?X4)%Z |- 
          (0 <= ?X3)%Z =>
              apply outside_square_5 with X1 X2 X4
          | id1:(2 < outside_square ?X1 ?X2 ?X3 ?X4)%Z |- 
          (0 <= ?X4)%Z =>
              apply outside_square_6 with X1 X2 X3
          | id1:(outside_square ?X1 ?X2 ?X3 ?X4 < -2)%Z |- 
          (?X1 <= 0)%Z =>
              apply outside_square_7 with X2 X3 X4
          | id1:(outside_square ?X1 ?X2 ?X3 ?X4 < -2)%Z |- 
          (?X2 <= 0)%Z =>
              apply outside_square_8 with X1 X3 X4
          | id1:(outside_square ?X1 ?X2 ?X3 ?X4 < -2)%Z |- 
          (?X3 <= 0)%Z =>
              apply outside_square_9 with X1 X2 X4
          | id1:(outside_square ?X1 ?X2 ?X3 ?X4 < -2)%Z |- 
          (?X4 <= 0)%Z => apply outside_square_10 with X1 X2 X3
          end; assumption ].
     (* ~`o1 < (-2)` /\ ~`2 < o1` *)
      intros Ho2' Ho2.
      generalize
       (Qquadratic_sign_nR_nR_4 a b c d e f g h (nR xs) xs 
          (nR ys) ys H_Qquadratic_sg_denom_nonzero
          (Qquadratic_signok_1 _ _ _ _ _ _ H_Qquadratic_sg_denom_nonzero)
          (refl_equal _) (refl_equal _)).
      intros H1.
      assert
       (H_tuple_eq :
        Qquadratic_sign a (a + b) (a + c) (a + b + c + d) e 
          (e + f) (e + g) (e + f + g + h) xs ys
          (Qquadratic_signok_1 e f g h xs ys H_Qquadratic_sg_denom_nonzero) =
        ((-1)%Z, (na, (nb, (nc, nd)), (ne, (nf, (ng, nh))), (np1, np2))));
       [ apply
          trans_eq
           with
             (Qquadratic_sign a b c d e f g h (nR xs) 
                (nR ys) H_Qquadratic_sg_denom_nonzero);
          [ apply sym_eq; apply H1; repeat split | idtac ]
       | apply
          (Qquadratic_sign_neg_2 a (a + b)%Z (a + c)%Z 
             (a + b + c + d)%Z e (e + f)%Z (e + g)%Z 
             (e + f + g + h)%Z xs ys
             (Qquadratic_signok_1 e f g h xs ys H_Qquadratic_sg_denom_nonzero)
             na nb nc nd ne nf ng nh np1 np2) ]; assumption.
   (* ~ `b = 0`/\`c = 0`/\`d = 0` *)
   intros Hbcd'.
   (* Intros [Hb [Hc] Hd]. *)
   case (three_integers_dec_inf f g h).   
    (* `f = 0`/\`g = 0`/\`h = 0` *)
    intros (Hf, (Hg, Hh)).
    case (Z_lt_dec 2 o1).
     (*  `2 < o1` *)
     intro Ho1.
     generalize
      (Qquadratic_sign_nRdL_nRdL_5 a b c d e f g h 
         (nR xs) (nR ys) H_Qquadratic_sg_denom_nonzero).
     intros H1.
     assert
      (H_tuple_eq :
       ((-1)%Z, (na, (nb, (nc, nd)), (ne, (nf, (ng, nh))), (np1, np2))) =
       (Z.sgn e, (a, (b, (c, d)), (e, (f, (g, h))), (nR xs, nR ys))));
      [ apply
         trans_eq
          with
            (Qquadratic_sign a b c d e f g h (nR xs) 
               (nR ys) H_Qquadratic_sg_denom_nonzero);
         [ apply sym_eq | apply H1; discriminate || (repeat split) ];
         assumption
      | generalize
         (Qquadratic_sign_tuple_equal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
            _ _ H_tuple_eq);
         intros
          (hl,
           ((hna, (hnb, (hnc, (hnd, (hne, (hnf, (hng, hnh))))))),
           (hp1,
            hp2)));
         do 10
          match goal with
          | id1:(?X1 = ?X2) |- ?X3 => try rewrite id1; clear id1
          end ].
     left; left; left; left; left; left; repeat split;
      repeat
       match goal with
       | id1:(?X1 = 0%Z) |- ?X2 => rewrite id1; clear id1
       end; first
      [ apply Z.le_refl
      | match goal with
        |  |- (0 <= ?X1)%Z =>
            apply Zlt_le_weak; apply Zsgn_9; apply Z.opp_inj
        |  |- (?X1 <= 0)%Z => apply Zlt_le_weak; apply Zsgn_10
        end; apply sym_eq; assumption
      | unfold o1 in Ho1;
         match goal with
         | id1:(2 < outside_square ?X1 ?X2 ?X3 ?X4)%Z |- 
         (0 <= ?X1)%Z =>
             apply outside_square_3 with X2 X3 X4
         | id1:(2 < outside_square ?X1 ?X2 ?X3 ?X4)%Z |- 
         (0 <= ?X2)%Z =>
             apply outside_square_4 with X1 X3 X4
         | id1:(2 < outside_square ?X1 ?X2 ?X3 ?X4)%Z |- 
         (0 <= ?X3)%Z =>
             apply outside_square_5 with X1 X2 X4
         | id1:(2 < outside_square ?X1 ?X2 ?X3 ?X4)%Z |- 
         (0 <= ?X4)%Z =>
             apply outside_square_6 with X1 X2 X3
         | id1:(outside_square ?X1 ?X2 ?X3 ?X4 < -2)%Z |- 
         (?X1 <= 0)%Z =>
             apply outside_square_7 with X2 X3 X4
         | id1:(outside_square ?X1 ?X2 ?X3 ?X4 < -2)%Z |- 
         (?X2 <= 0)%Z =>
             apply outside_square_8 with X1 X3 X4
         | id1:(outside_square ?X1 ?X2 ?X3 ?X4 < -2)%Z |- 
         (?X3 <= 0)%Z =>
             apply outside_square_9 with X1 X2 X4
         | id1:(outside_square ?X1 ?X2 ?X3 ?X4 < -2)%Z |- 
         (?X4 <= 0)%Z => apply outside_square_10 with X1 X2 X3
         end; assumption ].
     (*  ~`2 < o1` *)
     case (Z_lt_dec o1 (-2)).
      (* `(-2) < o1` *)
      intros Ho1' Ho1.
      generalize
       (Qquadratic_sign_nRdL_nRdL_6 a b c d e f g h 
          (nR xs) (nR ys) H_Qquadratic_sg_denom_nonzero).
      intros H1.
      assert
       (H_tuple_eq :
        ((-1)%Z, (na, (nb, (nc, nd)), (ne, (nf, (ng, nh))), (np1, np2))) =
        ((- Z.sgn e)%Z, (a, (b, (c, d)), (e, (f, (g, h))), (nR xs, nR ys))));
       [ apply
          trans_eq
           with
             (Qquadratic_sign a b c d e f g h (nR xs) 
                (nR ys) H_Qquadratic_sg_denom_nonzero);
          [ apply sym_eq | apply H1; discriminate || (repeat split) ];
          assumption
       | generalize
          (Qquadratic_sign_tuple_equal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
             _ _ _ H_tuple_eq);
          intros
           (hl,
            ((hna, (hnb, (hnc, (hnd, (hne, (hnf, (hng, hnh))))))),
            (hp1,
             hp2)));
          do 10
           match goal with
           | id1:(?X1 = ?X2) |- ?X3 => try rewrite id1; clear id1
           end ].
      left; left; left; left; left; right; repeat split;
       repeat
        match goal with
        | id1:(?X1 = 0%Z) |- ?X2 => rewrite id1; clear id1
        end; first
       [ apply Z.le_refl
       | match goal with
         |  |- (0 <= ?X1)%Z =>
             apply Zlt_le_weak; apply Zsgn_9; apply Z.opp_inj
         |  |- (?X1 <= 0)%Z => apply Zlt_le_weak; apply Zsgn_10
         end; apply sym_eq; assumption
       | unfold o1 in Ho1';
          match goal with
          | id1:(2 < outside_square ?X1 ?X2 ?X3 ?X4)%Z |- 
          (0 <= ?X1)%Z =>
              apply outside_square_3 with X2 X3 X4
          | id1:(2 < outside_square ?X1 ?X2 ?X3 ?X4)%Z |- 
          (0 <= ?X2)%Z =>
              apply outside_square_4 with X1 X3 X4
          | id1:(2 < outside_square ?X1 ?X2 ?X3 ?X4)%Z |- 
          (0 <= ?X3)%Z =>
              apply outside_square_5 with X1 X2 X4
          | id1:(2 < outside_square ?X1 ?X2 ?X3 ?X4)%Z |- 
          (0 <= ?X4)%Z =>
              apply outside_square_6 with X1 X2 X3
          | id1:(outside_square ?X1 ?X2 ?X3 ?X4 < -2)%Z |- 
          (?X1 <= 0)%Z =>
              apply outside_square_7 with X2 X3 X4
          | id1:(outside_square ?X1 ?X2 ?X3 ?X4 < -2)%Z |- 
          (?X2 <= 0)%Z =>
              apply outside_square_8 with X1 X3 X4
          | id1:(outside_square ?X1 ?X2 ?X3 ?X4 < -2)%Z |- 
          (?X3 <= 0)%Z =>
              apply outside_square_9 with X1 X2 X4
          | id1:(outside_square ?X1 ?X2 ?X3 ?X4 < -2)%Z |- 
          (?X4 <= 0)%Z => apply outside_square_10 with X1 X2 X3
          end; assumption ].

      (* ~`o1 < (-2)` /\ ~`2 < o1` *)
      intros Ho2' Ho2.
      generalize
       (Qquadratic_sign_nR_nR_7 a b c d e f g h (nR xs) xs 
          (nR ys) ys H_Qquadratic_sg_denom_nonzero
          (Qquadratic_signok_1 _ _ _ _ _ _ H_Qquadratic_sg_denom_nonzero)
          (refl_equal _) (refl_equal _)).
      intros H1.
      assert
       (H_tuple_eq :
        Qquadratic_sign a (a + b) (a + c) (a + b + c + d) e 
          (e + f) (e + g) (e + f + g + h) xs ys
          (Qquadratic_signok_1 e f g h xs ys H_Qquadratic_sg_denom_nonzero) =
        ((-1)%Z, (na, (nb, (nc, nd)), (ne, (nf, (ng, nh))), (np1, np2))));
       [ apply
          trans_eq
           with
             (Qquadratic_sign a b c d e f g h (nR xs) 
                (nR ys) H_Qquadratic_sg_denom_nonzero);
          [ apply sym_eq; apply H1; repeat split | idtac ]
       | apply
          (Qquadratic_sign_neg_2 a (a + b)%Z (a + c)%Z 
             (a + b + c + d)%Z e (e + f)%Z (e + g)%Z 
             (e + f + g + h)%Z xs ys
             (Qquadratic_signok_1 e f g h xs ys H_Qquadratic_sg_denom_nonzero)
             na nb nc nd ne nf ng nh np1 np2) ]; assumption.
    (* ~(`f = 0`/\`g = 0`/\`h = 0`) *)
    intro Hfgh'.
    case (inside_square_1_dec_inf o1 o2).    
     (* (inside_square_1 o1 o2) *)
     intro H_inside_1.
     generalize
      (Qquadratic_sign_nRdL_nRdL_8 a b c d e f g h 
         (nR xs) (nR ys) H_Qquadratic_sg_denom_nonzero).
     intros H1.
     assert
      (H_tuple_eq :
       ((-1)%Z, (na, (nb, (nc, nd)), (ne, (nf, (ng, nh))), (np1, np2))) =
       (1%Z, (a, (b, (c, d)), (e, (f, (g, h))), (nR xs, nR ys))));
      [ apply
         trans_eq
          with
            (Qquadratic_sign a b c d e f g h (nR xs) 
               (nR ys) H_Qquadratic_sg_denom_nonzero);
         [ apply sym_eq | apply H1; discriminate || (repeat split) ];
         assumption
      | generalize
         (Qquadratic_sign_tuple_equal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
            _ _ H_tuple_eq);
         intros
          (hl,
           ((hna, (hnb, (hnc, (hnd, (hne, (hnf, (hng, hnh))))))),
           (hp1,
            hp2)));
         do 10
          match goal with
          | id1:(?X1 = ?X2) |- ?X3 => try rewrite id1; clear id1
          end ].
     discriminate hl.
     (* ~(inside_square_1 o1 o2) *)    
     intro H_inside_1'.
     case (inside_square_2_dec_inf o1 o2).    
      (* (inside_square_2 o1 o2) *)
      intro H_inside_2.
      generalize
       (Qquadratic_sign_nRdL_nRdL_9 a b c d e f g h 
          (nR xs) (nR ys) H_Qquadratic_sg_denom_nonzero).
      intros H1.
      assert
       (H_tuple_eq :
        ((-1)%Z, (na, (nb, (nc, nd)), (ne, (nf, (ng, nh))), (np1, np2))) =
        ((-1)%Z, (a, (b, (c, d)), (e, (f, (g, h))), (nR xs, nR ys))));
       [ apply
          trans_eq
           with
             (Qquadratic_sign a b c d e f g h (nR xs) 
                (nR ys) H_Qquadratic_sg_denom_nonzero);
          [ apply sym_eq | apply H1; discriminate || (repeat split) ];
          assumption
       | generalize
          (Qquadratic_sign_tuple_equal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
             _ _ _ H_tuple_eq);
          intros
           (hl,
            ((hna, (hnb, (hnc, (hnd, (hne, (hnf, (hng, hnh))))))),
            (hp1,
             hp2)));
          do 10
           match goal with
           | id1:(?X1 = ?X2) |- ?X3 => try rewrite id1; clear id1
           end ].
     left; left; left; left; left; case (inside_square_2_inf _ _ H_inside_2);
      intros (Ho1, Ho2); [ left | right ]; repeat split; first
      [ apply Z.le_refl
      | match goal with
        |  |- (0 <= ?X1)%Z =>
            apply Zlt_le_weak; apply Zsgn_9; apply Z.opp_inj
        |  |- (?X1 <= 0)%Z => apply Zlt_le_weak; apply Zsgn_10
        end; apply sym_eq; assumption
      | unfold o1 in Ho1; unfold o2 in Ho2;
         match goal with
         | id1:(2 < outside_square ?X1 ?X2 ?X3 ?X4)%Z |- 
         (0 <= ?X1)%Z =>
             apply outside_square_3 with X2 X3 X4
         | id1:(2 < outside_square ?X1 ?X2 ?X3 ?X4)%Z |- 
         (0 <= ?X2)%Z =>
             apply outside_square_4 with X1 X3 X4
         | id1:(2 < outside_square ?X1 ?X2 ?X3 ?X4)%Z |- 
         (0 <= ?X3)%Z =>
             apply outside_square_5 with X1 X2 X4
         | id1:(2 < outside_square ?X1 ?X2 ?X3 ?X4)%Z |- 
         (0 <= ?X4)%Z =>
             apply outside_square_6 with X1 X2 X3
         | id1:(outside_square ?X1 ?X2 ?X3 ?X4 < -2)%Z |- 
         (?X1 <= 0)%Z =>
             apply outside_square_7 with X2 X3 X4
         | id1:(outside_square ?X1 ?X2 ?X3 ?X4 < -2)%Z |- 
         (?X2 <= 0)%Z =>
             apply outside_square_8 with X1 X3 X4
         | id1:(outside_square ?X1 ?X2 ?X3 ?X4 < -2)%Z |- 
         (?X3 <= 0)%Z =>
             apply outside_square_9 with X1 X2 X4
         | id1:(outside_square ?X1 ?X2 ?X3 ?X4 < -2)%Z |- 
         (?X4 <= 0)%Z => apply outside_square_10 with X1 X2 X3
         end; assumption ].

      (*  ~(inside_square_1 o1 o2)/\~(inside_square_2 o1 o2) *)
      intros H_inside_2'. 
      generalize
       (Qquadratic_sign_nR_nR_10 a b c d e f g h (nR xs) xs 
          (nR ys) ys H_Qquadratic_sg_denom_nonzero
          (Qquadratic_signok_1 _ _ _ _ _ _ H_Qquadratic_sg_denom_nonzero)
          (refl_equal _) (refl_equal _)).
      intros H1.
      assert
       (H_tuple_eq :
        Qquadratic_sign a (a + b) (a + c) (a + b + c + d) e 
          (e + f) (e + g) (e + f + g + h) xs ys
          (Qquadratic_signok_1 e f g h xs ys H_Qquadratic_sg_denom_nonzero) =
        ((-1)%Z, (na, (nb, (nc, nd)), (ne, (nf, (ng, nh))), (np1, np2))));
       [ apply
          trans_eq
           with
             (Qquadratic_sign a b c d e f g h (nR xs) 
                (nR ys) H_Qquadratic_sg_denom_nonzero);
          [ apply sym_eq; apply H1; repeat split | idtac ]
       | apply
          (Qquadratic_sign_neg_2 a (a + b)%Z (a + c)%Z 
             (a + b + c + d)%Z e (e + f)%Z (e + g)%Z 
             (e + f + g + h)%Z xs ys
             (Qquadratic_signok_1 e f g h xs ys H_Qquadratic_sg_denom_nonzero)
             na nb nc nd ne nf ng nh np1 np2) ]; assumption.

 (*  p1 = (nR xs) & p2 = (dL ys) *)
  case (three_integers_dec_inf b c d).  
   (* `b = 0`/\`c = 0`/\`d = 0` *)
   intros (Hb, (Hc, Hd)).
   (* Intros [Hb [Hc] Hd]. *)
   case (three_integers_dec_inf f g h).   
    (* `f = 0`/\`g = 0`/\`h = 0` *)
    intros (Hf, (Hg, Hh)).
    generalize
     (Qquadratic_sign_nRdL_nRdL_1 a b c d e f g h (nR xs) 
        (dL ys) H_Qquadratic_sg_denom_nonzero).
    intros H1.
    assert
     (H_tuple_eq :
      ((-1)%Z, (na, (nb, (nc, nd)), (ne, (nf, (ng, nh))), (np1, np2))) =
      ((Z.sgn a * Z.sgn e)%Z,
      (a, (b, (c, d)), (e, (f, (g, h))), (nR xs, dL ys))));
     [ apply
        trans_eq
         with
           (Qquadratic_sign a b c d e f g h (nR xs) 
              (dL ys) H_Qquadratic_sg_denom_nonzero);
        [ apply sym_eq | apply H1; discriminate || (repeat split) ];
        assumption
     | generalize
        (Qquadratic_sign_tuple_equal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
           _ _ H_tuple_eq);
        intros
         (hl,
          ((hna, (hnb, (hnc, (hnd, (hne, (hnf, (hng, hnh))))))),
          (hp1,
           hp2)));
        do 10
         match goal with
         | id1:(?X1 = ?X2) |- ?X3 => try rewrite id1; clear id1
         end ].
    left; left; left; left; left; rewrite <- Zsgn_15 in hl.
    case (Zsgn_17 _ _ (sym_eq hl)); intros (Ha, He); [ left | right ];
     repeat split;
     repeat
      match goal with
      | id1:(?X1 = 0%Z) |- ?X2 => rewrite id1; clear id1
      end; first [ apply Z.le_refl | apply Zlt_le_weak ]; 
     assumption.
    (* ~(`f = 0`/\`g = 0`/\`h = 0`) *)
    intros H_fgh'.
    case (Z_lt_dec 2 o2).
     (*  `2 < o2` *)
     intro Ho2.
     generalize
      (Qquadratic_sign_nRdL_nRdL_2 a b c d e f g h 
         (nR xs) (dL ys) H_Qquadratic_sg_denom_nonzero).
     intros H1.
     assert
      (H_tuple_eq :
       ((-1)%Z, (na, (nb, (nc, nd)), (ne, (nf, (ng, nh))), (np1, np2))) =
       (Z.sgn a, (a, (b, (c, d)), (e, (f, (g, h))), (nR xs, dL ys))));
      [ apply
         trans_eq
          with
            (Qquadratic_sign a b c d e f g h (nR xs) 
               (dL ys) H_Qquadratic_sg_denom_nonzero);
         [ apply sym_eq | apply H1; discriminate || (repeat split) ];
         assumption
      | generalize
         (Qquadratic_sign_tuple_equal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
            _ _ H_tuple_eq);
         intros
          (hl,
           ((hna, (hnb, (hnc, (hnd, (hne, (hnf, (hng, hnh))))))),
           (hp1,
            hp2)));
         do 10
          match goal with
          | id1:(?X1 = ?X2) |- ?X3 => try rewrite id1; clear id1
          end ].
     left; left; left; left; left; right; repeat split;
      repeat
       match goal with
       | id1:(?X1 = 0%Z) |- ?X2 => rewrite id1; clear id1
       end; first
      [ apply Z.le_refl
      | match goal with
        |  |- (0 <= ?X1)%Z =>
            apply Zlt_le_weak; apply Zsgn_9; apply Z.opp_inj
        |  |- (?X1 <= 0)%Z => apply Zlt_le_weak; apply Zsgn_10
        end; apply sym_eq; assumption
      | unfold o2 in Ho2;
         match goal with
         | id1:(2 < outside_square ?X1 ?X2 ?X3 ?X4)%Z |- 
         (0 <= ?X1)%Z =>
             apply outside_square_3 with X2 X3 X4
         | id1:(2 < outside_square ?X1 ?X2 ?X3 ?X4)%Z |- 
         (0 <= ?X2)%Z =>
             apply outside_square_4 with X1 X3 X4
         | id1:(2 < outside_square ?X1 ?X2 ?X3 ?X4)%Z |- 
         (0 <= ?X3)%Z =>
             apply outside_square_5 with X1 X2 X4
         | id1:(2 < outside_square ?X1 ?X2 ?X3 ?X4)%Z |- 
         (0 <= ?X4)%Z =>
             apply outside_square_6 with X1 X2 X3
         | id1:(outside_square ?X1 ?X2 ?X3 ?X4 < -2)%Z |- 
         (?X1 <= 0)%Z =>
             apply outside_square_7 with X2 X3 X4
         | id1:(outside_square ?X1 ?X2 ?X3 ?X4 < -2)%Z |- 
         (?X2 <= 0)%Z =>
             apply outside_square_8 with X1 X3 X4
         | id1:(outside_square ?X1 ?X2 ?X3 ?X4 < -2)%Z |- 
         (?X3 <= 0)%Z =>
             apply outside_square_9 with X1 X2 X4
         | id1:(outside_square ?X1 ?X2 ?X3 ?X4 < -2)%Z |- 
         (?X4 <= 0)%Z => apply outside_square_10 with X1 X2 X3
         end; assumption ].
     
     (*  ~`2 < o2` *)
     case (Z_lt_dec o2 (-2)).     
     (* `(-2) < o2` *)
      intros Ho2' Ho2.
      generalize
       (Qquadratic_sign_nRdL_nRdL_3 a b c d e f g h 
          (nR xs) (dL ys) H_Qquadratic_sg_denom_nonzero).
      intros H1.
      assert
       (H_tuple_eq :
        ((-1)%Z, (na, (nb, (nc, nd)), (ne, (nf, (ng, nh))), (np1, np2))) =
        ((- Z.sgn a)%Z, (a, (b, (c, d)), (e, (f, (g, h))), (nR xs, dL ys))));
       [ apply
          trans_eq
           with
             (Qquadratic_sign a b c d e f g h (nR xs) 
                (dL ys) H_Qquadratic_sg_denom_nonzero);
          [ apply sym_eq | apply H1; discriminate || (repeat split) ];
          assumption
       | generalize
          (Qquadratic_sign_tuple_equal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
             _ _ _ H_tuple_eq);
          intros
           (hl,
            ((hna, (hnb, (hnc, (hnd, (hne, (hnf, (hng, hnh))))))),
            (hp1,
             hp2)));
          do 10
           match goal with
           | id1:(?X1 = ?X2) |- ?X3 => try rewrite id1; clear id1
           end ].
      left; left; left; left; left; left; repeat split;
       repeat
        match goal with
        | id1:(?X1 = 0%Z) |- ?X2 => rewrite id1; clear id1
        end; first
       [ apply Z.le_refl
       | match goal with
         |  |- (0 <= ?X1)%Z =>
             apply Zlt_le_weak; apply Zsgn_9; apply Z.opp_inj
         |  |- (?X1 <= 0)%Z => apply Zlt_le_weak; apply Zsgn_10
         end; apply sym_eq; assumption
       | unfold o2 in Ho2';
          match goal with
          | id1:(2 < outside_square ?X1 ?X2 ?X3 ?X4)%Z |- 
          (0 <= ?X1)%Z =>
              apply outside_square_3 with X2 X3 X4
          | id1:(2 < outside_square ?X1 ?X2 ?X3 ?X4)%Z |- 
          (0 <= ?X2)%Z =>
              apply outside_square_4 with X1 X3 X4
          | id1:(2 < outside_square ?X1 ?X2 ?X3 ?X4)%Z |- 
          (0 <= ?X3)%Z =>
              apply outside_square_5 with X1 X2 X4
          | id1:(2 < outside_square ?X1 ?X2 ?X3 ?X4)%Z |- 
          (0 <= ?X4)%Z =>
              apply outside_square_6 with X1 X2 X3
          | id1:(outside_square ?X1 ?X2 ?X3 ?X4 < -2)%Z |- 
          (?X1 <= 0)%Z =>
              apply outside_square_7 with X2 X3 X4
          | id1:(outside_square ?X1 ?X2 ?X3 ?X4 < -2)%Z |- 
          (?X2 <= 0)%Z =>
              apply outside_square_8 with X1 X3 X4
          | id1:(outside_square ?X1 ?X2 ?X3 ?X4 < -2)%Z |- 
          (?X3 <= 0)%Z =>
              apply outside_square_9 with X1 X2 X4
          | id1:(outside_square ?X1 ?X2 ?X3 ?X4 < -2)%Z |- 
          (?X4 <= 0)%Z => apply outside_square_10 with X1 X2 X3
          end; assumption ].
     (* ~`o1 < (-2)` /\ ~`2 < o1` *)
      intros Ho2' Ho2.
      generalize
       (Qquadratic_sign_nR_dL_4 a b c d e f g h (nR xs) xs 
          (dL ys) ys H_Qquadratic_sg_denom_nonzero
          (Qquadratic_signok_2 _ _ _ _ _ _ H_Qquadratic_sg_denom_nonzero)
          (refl_equal _) (refl_equal _)).
      intros H1.
      assert
       (H_tuple_eq :
        Qquadratic_sign (a + b) b (a + b + c + d) (b + d) 
          (e + f) f (e + f + g + h) (f + h) xs ys
          (Qquadratic_signok_2 e f g h xs ys H_Qquadratic_sg_denom_nonzero) =
        ((-1)%Z, (na, (nb, (nc, nd)), (ne, (nf, (ng, nh))), (np1, np2))));
       [ apply
          trans_eq
           with
             (Qquadratic_sign a b c d e f g h (nR xs) 
                (dL ys) H_Qquadratic_sg_denom_nonzero);
          [ apply sym_eq; apply H1; repeat split | idtac ]
       | apply
          (Qquadratic_sign_neg_2 (a + b)%Z b (a + b + c + d)%Z 
             (b + d)%Z (e + f)%Z f (e + f + g + h)%Z 
             (f + h)%Z xs ys
             (Qquadratic_signok_2 e f g h xs ys H_Qquadratic_sg_denom_nonzero)
             na nb nc nd ne nf ng nh np1 np2) ]; assumption.
   (* ~ `b = 0`/\`c = 0`/\`d = 0` *)
   intros Hbcd'.
   (* Intros [Hb [Hc] Hd]. *)
   case (three_integers_dec_inf f g h).   
    (* `f = 0`/\`g = 0`/\`h = 0` *)
    intros (Hf, (Hg, Hh)).
    case (Z_lt_dec 2 o1).
     (*  `2 < o1` *)
     intro Ho1.
     generalize
      (Qquadratic_sign_nRdL_nRdL_5 a b c d e f g h 
         (nR xs) (dL ys) H_Qquadratic_sg_denom_nonzero).
     intros H1.
     assert
      (H_tuple_eq :
       ((-1)%Z, (na, (nb, (nc, nd)), (ne, (nf, (ng, nh))), (np1, np2))) =
       (Z.sgn e, (a, (b, (c, d)), (e, (f, (g, h))), (nR xs, dL ys))));
      [ apply
         trans_eq
          with
            (Qquadratic_sign a b c d e f g h (nR xs) 
               (dL ys) H_Qquadratic_sg_denom_nonzero);
         [ apply sym_eq | apply H1; discriminate || (repeat split) ];
         assumption
      | generalize
         (Qquadratic_sign_tuple_equal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
            _ _ H_tuple_eq);
         intros
          (hl,
           ((hna, (hnb, (hnc, (hnd, (hne, (hnf, (hng, hnh))))))),
           (hp1,
            hp2)));
         do 10
          match goal with
          | id1:(?X1 = ?X2) |- ?X3 => try rewrite id1; clear id1
          end ].
     left; left; left; left; left; left; repeat split;
      repeat
       match goal with
       | id1:(?X1 = 0%Z) |- ?X2 => rewrite id1; clear id1
       end; first
      [ apply Z.le_refl
      | match goal with
        |  |- (0 <= ?X1)%Z =>
            apply Zlt_le_weak; apply Zsgn_9; apply Z.opp_inj
        |  |- (?X1 <= 0)%Z => apply Zlt_le_weak; apply Zsgn_10
        end; apply sym_eq; assumption
      | unfold o1 in Ho1;
         match goal with
         | id1:(2 < outside_square ?X1 ?X2 ?X3 ?X4)%Z |- 
         (0 <= ?X1)%Z =>
             apply outside_square_3 with X2 X3 X4
         | id1:(2 < outside_square ?X1 ?X2 ?X3 ?X4)%Z |- 
         (0 <= ?X2)%Z =>
             apply outside_square_4 with X1 X3 X4
         | id1:(2 < outside_square ?X1 ?X2 ?X3 ?X4)%Z |- 
         (0 <= ?X3)%Z =>
             apply outside_square_5 with X1 X2 X4
         | id1:(2 < outside_square ?X1 ?X2 ?X3 ?X4)%Z |- 
         (0 <= ?X4)%Z =>
             apply outside_square_6 with X1 X2 X3
         | id1:(outside_square ?X1 ?X2 ?X3 ?X4 < -2)%Z |- 
         (?X1 <= 0)%Z =>
             apply outside_square_7 with X2 X3 X4
         | id1:(outside_square ?X1 ?X2 ?X3 ?X4 < -2)%Z |- 
         (?X2 <= 0)%Z =>
             apply outside_square_8 with X1 X3 X4
         | id1:(outside_square ?X1 ?X2 ?X3 ?X4 < -2)%Z |- 
         (?X3 <= 0)%Z =>
             apply outside_square_9 with X1 X2 X4
         | id1:(outside_square ?X1 ?X2 ?X3 ?X4 < -2)%Z |- 
         (?X4 <= 0)%Z => apply outside_square_10 with X1 X2 X3
         end; assumption ].
     (*  ~`2 < o1` *)
     case (Z_lt_dec o1 (-2)).
      (* `(-2) < o1` *)
      intros Ho1' Ho1.
      generalize
       (Qquadratic_sign_nRdL_nRdL_6 a b c d e f g h 
          (nR xs) (dL ys) H_Qquadratic_sg_denom_nonzero).
      intros H1.
      assert
       (H_tuple_eq :
        ((-1)%Z, (na, (nb, (nc, nd)), (ne, (nf, (ng, nh))), (np1, np2))) =
        ((- Z.sgn e)%Z, (a, (b, (c, d)), (e, (f, (g, h))), (nR xs, dL ys))));
       [ apply
          trans_eq
           with
             (Qquadratic_sign a b c d e f g h (nR xs) 
                (dL ys) H_Qquadratic_sg_denom_nonzero);
          [ apply sym_eq | apply H1; discriminate || (repeat split) ];
          assumption
       | generalize
          (Qquadratic_sign_tuple_equal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
             _ _ _ H_tuple_eq);
          intros
           (hl,
            ((hna, (hnb, (hnc, (hnd, (hne, (hnf, (hng, hnh))))))),
            (hp1,
             hp2)));
          do 10
           match goal with
           | id1:(?X1 = ?X2) |- ?X3 => try rewrite id1; clear id1
           end ].
      left; left; left; left; left; right; repeat split;
       repeat
        match goal with
        | id1:(?X1 = 0%Z) |- ?X2 => rewrite id1; clear id1
        end; first
       [ apply Z.le_refl
       | match goal with
         |  |- (0 <= ?X1)%Z =>
             apply Zlt_le_weak; apply Zsgn_9; apply Z.opp_inj
         |  |- (?X1 <= 0)%Z => apply Zlt_le_weak; apply Zsgn_10
         end; apply sym_eq; assumption
       | unfold o1 in Ho1';
          match goal with
          | id1:(2 < outside_square ?X1 ?X2 ?X3 ?X4)%Z |- 
          (0 <= ?X1)%Z =>
              apply outside_square_3 with X2 X3 X4
          | id1:(2 < outside_square ?X1 ?X2 ?X3 ?X4)%Z |- 
          (0 <= ?X2)%Z =>
              apply outside_square_4 with X1 X3 X4
          | id1:(2 < outside_square ?X1 ?X2 ?X3 ?X4)%Z |- 
          (0 <= ?X3)%Z =>
              apply outside_square_5 with X1 X2 X4
          | id1:(2 < outside_square ?X1 ?X2 ?X3 ?X4)%Z |- 
          (0 <= ?X4)%Z =>
              apply outside_square_6 with X1 X2 X3
          | id1:(outside_square ?X1 ?X2 ?X3 ?X4 < -2)%Z |- 
          (?X1 <= 0)%Z =>
              apply outside_square_7 with X2 X3 X4
          | id1:(outside_square ?X1 ?X2 ?X3 ?X4 < -2)%Z |- 
          (?X2 <= 0)%Z =>
              apply outside_square_8 with X1 X3 X4
          | id1:(outside_square ?X1 ?X2 ?X3 ?X4 < -2)%Z |- 
          (?X3 <= 0)%Z =>
              apply outside_square_9 with X1 X2 X4
          | id1:(outside_square ?X1 ?X2 ?X3 ?X4 < -2)%Z |- 
          (?X4 <= 0)%Z => apply outside_square_10 with X1 X2 X3
          end; assumption ].

      (* ~`o1 < (-2)` /\ ~`2 < o1` *)
      intros Ho2' Ho2.
      generalize
       (Qquadratic_sign_nR_dL_7 a b c d e f g h (nR xs) xs 
          (dL ys) ys H_Qquadratic_sg_denom_nonzero
          (Qquadratic_signok_2 _ _ _ _ _ _ H_Qquadratic_sg_denom_nonzero)
          (refl_equal _) (refl_equal _)).
      intros H1.
      assert
       (H_tuple_eq :
        Qquadratic_sign (a + b) b (a + b + c + d) (b + d) 
          (e + f) f (e + f + g + h) (f + h) xs ys
          (Qquadratic_signok_2 e f g h xs ys H_Qquadratic_sg_denom_nonzero) =
        ((-1)%Z, (na, (nb, (nc, nd)), (ne, (nf, (ng, nh))), (np1, np2))));
       [ apply
          trans_eq
           with
             (Qquadratic_sign a b c d e f g h (nR xs) 
                (dL ys) H_Qquadratic_sg_denom_nonzero);
          [ apply sym_eq; apply H1; repeat split | idtac ]
       | apply
          (Qquadratic_sign_neg_2 (a + b)%Z b (a + b + c + d)%Z 
             (b + d)%Z (e + f)%Z f (e + f + g + h)%Z 
             (f + h)%Z xs ys
             (Qquadratic_signok_2 e f g h xs ys H_Qquadratic_sg_denom_nonzero)
             na nb nc nd ne nf ng nh np1 np2) ]; assumption.
    (* ~(`f = 0`/\`g = 0`/\`h = 0`) *)
    intro Hfgh'.
    case (inside_square_1_dec_inf o1 o2).    
     (* (inside_square_1 o1 o2) *)
     intro H_inside_1.
     generalize
      (Qquadratic_sign_nRdL_nRdL_8 a b c d e f g h 
         (nR xs) (dL ys) H_Qquadratic_sg_denom_nonzero).
     intros H1.
     assert
      (H_tuple_eq :
       ((-1)%Z, (na, (nb, (nc, nd)), (ne, (nf, (ng, nh))), (np1, np2))) =
       (1%Z, (a, (b, (c, d)), (e, (f, (g, h))), (nR xs, dL ys))));
      [ apply
         trans_eq
          with
            (Qquadratic_sign a b c d e f g h (nR xs) 
               (dL ys) H_Qquadratic_sg_denom_nonzero);
         [ apply sym_eq | apply H1; discriminate || (repeat split) ];
         assumption
      | generalize
         (Qquadratic_sign_tuple_equal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
            _ _ H_tuple_eq);
         intros
          (hl,
           ((hna, (hnb, (hnc, (hnd, (hne, (hnf, (hng, hnh))))))),
           (hp1,
            hp2)));
         do 10
          match goal with
          | id1:(?X1 = ?X2) |- ?X3 => try rewrite id1; clear id1
          end ].
     discriminate hl.

      (* ~(inside_square_1 o1 o2) *)    
     intro H_inside_1'.
     case (inside_square_2_dec_inf o1 o2).    
      (* (inside_square_2 o1 o2) *)
      intro H_inside_2.
      generalize
       (Qquadratic_sign_nRdL_nRdL_9 a b c d e f g h 
          (nR xs) (dL ys) H_Qquadratic_sg_denom_nonzero).
      intros H1.
      assert
       (H_tuple_eq :
        ((-1)%Z, (na, (nb, (nc, nd)), (ne, (nf, (ng, nh))), (np1, np2))) =
        ((-1)%Z, (a, (b, (c, d)), (e, (f, (g, h))), (nR xs, dL ys))));
       [ apply
          trans_eq
           with
             (Qquadratic_sign a b c d e f g h (nR xs) 
                (dL ys) H_Qquadratic_sg_denom_nonzero);
          [ apply sym_eq | apply H1; discriminate || (repeat split) ];
          assumption
       | generalize
          (Qquadratic_sign_tuple_equal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
             _ _ _ H_tuple_eq);
          intros
           (hl,
            ((hna, (hnb, (hnc, (hnd, (hne, (hnf, (hng, hnh))))))),
            (hp1,
             hp2)));
          do 10
           match goal with
           | id1:(?X1 = ?X2) |- ?X3 => try rewrite id1; clear id1
           end ].
     left; left; left; left; left; case (inside_square_2_inf _ _ H_inside_2);
      intros (Ho1, Ho2); [ left | right ]; repeat split; first
      [ apply Z.le_refl
      | match goal with
        |  |- (0 <= ?X1)%Z =>
            apply Zlt_le_weak; apply Zsgn_9; apply Z.opp_inj
        |  |- (?X1 <= 0)%Z => apply Zlt_le_weak; apply Zsgn_10
        end; apply sym_eq; assumption
      | unfold o1 in Ho1; unfold o2 in Ho2;
         match goal with
         | id1:(2 < outside_square ?X1 ?X2 ?X3 ?X4)%Z |- 
         (0 <= ?X1)%Z =>
             apply outside_square_3 with X2 X3 X4
         | id1:(2 < outside_square ?X1 ?X2 ?X3 ?X4)%Z |- 
         (0 <= ?X2)%Z =>
             apply outside_square_4 with X1 X3 X4
         | id1:(2 < outside_square ?X1 ?X2 ?X3 ?X4)%Z |- 
         (0 <= ?X3)%Z =>
             apply outside_square_5 with X1 X2 X4
         | id1:(2 < outside_square ?X1 ?X2 ?X3 ?X4)%Z |- 
         (0 <= ?X4)%Z =>
             apply outside_square_6 with X1 X2 X3
         | id1:(outside_square ?X1 ?X2 ?X3 ?X4 < -2)%Z |- 
         (?X1 <= 0)%Z =>
             apply outside_square_7 with X2 X3 X4
         | id1:(outside_square ?X1 ?X2 ?X3 ?X4 < -2)%Z |- 
         (?X2 <= 0)%Z =>
             apply outside_square_8 with X1 X3 X4
         | id1:(outside_square ?X1 ?X2 ?X3 ?X4 < -2)%Z |- 
         (?X3 <= 0)%Z =>
             apply outside_square_9 with X1 X2 X4
         | id1:(outside_square ?X1 ?X2 ?X3 ?X4 < -2)%Z |- 
         (?X4 <= 0)%Z => apply outside_square_10 with X1 X2 X3
         end; assumption ].
      (*  ~(inside_square_1 o1 o2)/\~(inside_square_2 o1 o2) *)
      intros H_inside_2'. 
      generalize
       (Qquadratic_sign_nR_dL_10 a b c d e f g h (nR xs) xs 
          (dL ys) ys H_Qquadratic_sg_denom_nonzero
          (Qquadratic_signok_2 _ _ _ _ _ _ H_Qquadratic_sg_denom_nonzero)
          (refl_equal _) (refl_equal _)).
      intros H1.
      assert
       (H_tuple_eq :
        Qquadratic_sign (a + b) b (a + b + c + d) (b + d) 
          (e + f) f (e + f + g + h) (f + h) xs ys
          (Qquadratic_signok_2 e f g h xs ys H_Qquadratic_sg_denom_nonzero) =
        ((-1)%Z, (na, (nb, (nc, nd)), (ne, (nf, (ng, nh))), (np1, np2))));
       [ apply
          trans_eq
           with
             (Qquadratic_sign a b c d e f g h (nR xs) 
                (dL ys) H_Qquadratic_sg_denom_nonzero);
          [ apply sym_eq; apply H1; repeat split | idtac ]
       | apply
          (Qquadratic_sign_neg_2 (a + b)%Z b (a + b + c + d)%Z 
             (b + d)%Z (e + f)%Z f (e + f + g + h)%Z 
             (f + h)%Z xs ys
             (Qquadratic_signok_2 e f g h xs ys H_Qquadratic_sg_denom_nonzero)
             na nb nc nd ne nf ng nh np1 np2) ]; assumption.
 (*  p1 = (nR xs) & p2 = One *)
  generalize (Qquadratic_signok_0' _ _ _ _ _ H_Qquadratic_sg_denom_nonzero).
  intros H_Qhomographic_sg_denom_nonzero.
  set
   (L3 :=
    Qhomographic_sign (a + b) (c + d) (e + f) (g + h) 
      (nR xs) H_Qhomographic_sg_denom_nonzero) in *.
  set (l1 := fst L3) in *.
  set (l2 := fst (snd L3)) in *.
  set (l3 := snd (snd L3)) in *.
  set (na_ := fst l2) in *.
  set (nb_ := fst (snd l2)) in *.
  set (nc_ := fst (snd (snd l2))) in *.
  set (nd_ := snd (snd (snd l2))) in *.
  generalize
   (Qquadratic_sign_nRdL_One a b c d e f g h (nR xs) One
      H_Qquadratic_sg_denom_nonzero l1 na_ nb_ nc_ nd_ l3
      H_Qhomographic_sg_denom_nonzero); intros H1.
  assert
   (H_tuple_eq :
    ((-1)%Z, (na, (nb, (nc, nd)), (ne, (nf, (ng, nh))), (np1, np2))) =
    (l1, (0%Z, (na_, (0%Z, nb_)), (0%Z, (nc_, (0%Z, nd_))), (l3, One))));
   [ apply
      trans_eq
       with
         (Qquadratic_sign a b c d e f g h (nR xs) One
            H_Qquadratic_sg_denom_nonzero);
      [ apply sym_eq; assumption
      | apply H1; fold L3 in |- *; repeat (apply pair_2; try reflexivity);
         discriminate || reflexivity ]
   | generalize
      (Qquadratic_sign_tuple_equal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
         _ H_tuple_eq);
      intros
       (hl,
        ((hna, (hnb, (hnc, (hnd, (hne, (hnf, (hng, hnh))))))),
        (hp1,
         hp2)));
      do 10
       match goal with
       | id1:(?X1 = ?X2) |- ?X3 => try rewrite id1; clear id1
       end; repeat rewrite ZERO_left; repeat rewrite Zplus_0_r ].
  assert
   (H_sg_unfolded :
    Qhomographic_sign (a + b) (c + d) (e + f) (g + h) 
      (nR xs) H_Qhomographic_sg_denom_nonzero =
    ((-1)%Z, (na_, (nb_, (nc_, nd_)), l3))).
  rewrite hl; fold L3 in |- *; repeat (apply pair_2; try reflexivity);
   discriminate || reflexivity.
  generalize
   (sg_neg_2 (a + b) (c + d) (e + f) (g + h) (nR xs)
      H_Qhomographic_sg_denom_nonzero na_ nb_ nc_ nd_ l3 H_sg_unfolded).
  intros [[(H_a, (H_b, (H_c, H_d)))| (H_a, (H_b, (H_c, H_d)))]| H_l3];
   [ case l3; left;
      [ right; repeat split; assumption || discriminate
      | right; repeat split; assumption || discriminate
      | left; right; repeat split ]
   | case l3;
      [ right; repeat split; assumption || discriminate
      | right; repeat split; assumption || discriminate
      | left; left; right; repeat split ]
   | left; left; right; repeat split; assumption ].


 (* p1 = (dL xs) *)
 destruct p2 as [ys| ys| ].
  (*  p1 = (dL xs) & p2 = (nR ys) *)
  case (three_integers_dec_inf b c d).  
   (* `b = 0`/\`c = 0`/\`d = 0` *)
   intros (Hb, (Hc, Hd)).
   (* Intros [Hb [Hc] Hd]. *)
   case (three_integers_dec_inf f g h).   
    (* `f = 0`/\`g = 0`/\`h = 0` *)
    intros (Hf, (Hg, Hh)).
    generalize
     (Qquadratic_sign_nRdL_nRdL_1 a b c d e f g h (dL xs) 
        (nR ys) H_Qquadratic_sg_denom_nonzero).
    intros H1.
    assert
     (H_tuple_eq :
      ((-1)%Z, (na, (nb, (nc, nd)), (ne, (nf, (ng, nh))), (np1, np2))) =
      ((Z.sgn a * Z.sgn e)%Z,
      (a, (b, (c, d)), (e, (f, (g, h))), (dL xs, nR ys))));
     [ apply
        trans_eq
         with
           (Qquadratic_sign a b c d e f g h (dL xs) 
              (nR ys) H_Qquadratic_sg_denom_nonzero);
        [ apply sym_eq | apply H1; discriminate || (repeat split) ];
        assumption
     | generalize
        (Qquadratic_sign_tuple_equal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
           _ _ H_tuple_eq);
        intros
         (hl,
          ((hna, (hnb, (hnc, (hnd, (hne, (hnf, (hng, hnh))))))),
          (hp1,
           hp2)));
        do 10
         match goal with
         | id1:(?X1 = ?X2) |- ?X3 => try rewrite id1; clear id1
         end ].
    left; left; left; left; left; rewrite <- Zsgn_15 in hl.
    case (Zsgn_17 _ _ (sym_eq hl)); intros (Ha, He); [ left | right ];
     repeat split;
     repeat
      match goal with
      | id1:(?X1 = 0%Z) |- ?X2 => rewrite id1; clear id1
      end; first [ apply Z.le_refl | apply Zlt_le_weak ]; 
     assumption.
    (* ~(`f = 0`/\`g = 0`/\`h = 0`) *)
    intros H_fgh'.
    case (Z_lt_dec 2 o2).
     (*  `2 < o2` *)
     intro Ho2.
     generalize
      (Qquadratic_sign_nRdL_nRdL_2 a b c d e f g h 
         (dL xs) (nR ys) H_Qquadratic_sg_denom_nonzero).
     intros H1.
     assert
      (H_tuple_eq :
       ((-1)%Z, (na, (nb, (nc, nd)), (ne, (nf, (ng, nh))), (np1, np2))) =
       (Z.sgn a, (a, (b, (c, d)), (e, (f, (g, h))), (dL xs, nR ys))));
      [ apply
         trans_eq
          with
            (Qquadratic_sign a b c d e f g h (dL xs) 
               (nR ys) H_Qquadratic_sg_denom_nonzero);
         [ apply sym_eq | apply H1; discriminate || (repeat split) ];
         assumption
      | generalize
         (Qquadratic_sign_tuple_equal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
            _ _ H_tuple_eq);
         intros
          (hl,
           ((hna, (hnb, (hnc, (hnd, (hne, (hnf, (hng, hnh))))))),
           (hp1,
            hp2)));
         do 10
          match goal with
          | id1:(?X1 = ?X2) |- ?X3 => try rewrite id1; clear id1
          end ].
     left; left; left; left; left; right; repeat split;
      repeat
       match goal with
       | id1:(?X1 = 0%Z) |- ?X2 => rewrite id1; clear id1
       end; first
      [ apply Z.le_refl
      | match goal with
        |  |- (0 <= ?X1)%Z =>
            apply Zlt_le_weak; apply Zsgn_9; apply Z.opp_inj
        |  |- (?X1 <= 0)%Z => apply Zlt_le_weak; apply Zsgn_10
        end; apply sym_eq; assumption
      | unfold o2 in Ho2;
         match goal with
         | id1:(2 < outside_square ?X1 ?X2 ?X3 ?X4)%Z |- 
         (0 <= ?X1)%Z =>
             apply outside_square_3 with X2 X3 X4
         | id1:(2 < outside_square ?X1 ?X2 ?X3 ?X4)%Z |- 
         (0 <= ?X2)%Z =>
             apply outside_square_4 with X1 X3 X4
         | id1:(2 < outside_square ?X1 ?X2 ?X3 ?X4)%Z |- 
         (0 <= ?X3)%Z =>
             apply outside_square_5 with X1 X2 X4
         | id1:(2 < outside_square ?X1 ?X2 ?X3 ?X4)%Z |- 
         (0 <= ?X4)%Z =>
             apply outside_square_6 with X1 X2 X3
         | id1:(outside_square ?X1 ?X2 ?X3 ?X4 < -2)%Z |- 
         (?X1 <= 0)%Z =>
             apply outside_square_7 with X2 X3 X4
         | id1:(outside_square ?X1 ?X2 ?X3 ?X4 < -2)%Z |- 
         (?X2 <= 0)%Z =>
             apply outside_square_8 with X1 X3 X4
         | id1:(outside_square ?X1 ?X2 ?X3 ?X4 < -2)%Z |- 
         (?X3 <= 0)%Z =>
             apply outside_square_9 with X1 X2 X4
         | id1:(outside_square ?X1 ?X2 ?X3 ?X4 < -2)%Z |- 
         (?X4 <= 0)%Z => apply outside_square_10 with X1 X2 X3
         end; assumption ].
     
     (*  ~`2 < o2` *)
     case (Z_lt_dec o2 (-2)).     
     (* `(-2) < o2` *)
      intros Ho2' Ho2.
      generalize
       (Qquadratic_sign_nRdL_nRdL_3 a b c d e f g h 
          (dL xs) (nR ys) H_Qquadratic_sg_denom_nonzero).
      intros H1.
      assert
       (H_tuple_eq :
        ((-1)%Z, (na, (nb, (nc, nd)), (ne, (nf, (ng, nh))), (np1, np2))) =
        ((- Z.sgn a)%Z, (a, (b, (c, d)), (e, (f, (g, h))), (dL xs, nR ys))));
       [ apply
          trans_eq
           with
             (Qquadratic_sign a b c d e f g h (dL xs) 
                (nR ys) H_Qquadratic_sg_denom_nonzero);
          [ apply sym_eq | apply H1; discriminate || (repeat split) ];
          assumption
       | generalize
          (Qquadratic_sign_tuple_equal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
             _ _ _ H_tuple_eq);
          intros
           (hl,
            ((hna, (hnb, (hnc, (hnd, (hne, (hnf, (hng, hnh))))))),
            (hp1,
             hp2)));
          do 10
           match goal with
           | id1:(?X1 = ?X2) |- ?X3 => try rewrite id1; clear id1
           end ].
      left; left; left; left; left; left; repeat split;
       repeat
        match goal with
        | id1:(?X1 = 0%Z) |- ?X2 => rewrite id1; clear id1
        end; first
       [ apply Z.le_refl
       | match goal with
         |  |- (0 <= ?X1)%Z =>
             apply Zlt_le_weak; apply Zsgn_9; apply Z.opp_inj
         |  |- (?X1 <= 0)%Z => apply Zlt_le_weak; apply Zsgn_10
         end; apply sym_eq; assumption
       | unfold o2 in Ho2';
          match goal with
          | id1:(2 < outside_square ?X1 ?X2 ?X3 ?X4)%Z |- 
          (0 <= ?X1)%Z =>
              apply outside_square_3 with X2 X3 X4
          | id1:(2 < outside_square ?X1 ?X2 ?X3 ?X4)%Z |- 
          (0 <= ?X2)%Z =>
              apply outside_square_4 with X1 X3 X4
          | id1:(2 < outside_square ?X1 ?X2 ?X3 ?X4)%Z |- 
          (0 <= ?X3)%Z =>
              apply outside_square_5 with X1 X2 X4
          | id1:(2 < outside_square ?X1 ?X2 ?X3 ?X4)%Z |- 
          (0 <= ?X4)%Z =>
              apply outside_square_6 with X1 X2 X3
          | id1:(outside_square ?X1 ?X2 ?X3 ?X4 < -2)%Z |- 
          (?X1 <= 0)%Z =>
              apply outside_square_7 with X2 X3 X4
          | id1:(outside_square ?X1 ?X2 ?X3 ?X4 < -2)%Z |- 
          (?X2 <= 0)%Z =>
              apply outside_square_8 with X1 X3 X4
          | id1:(outside_square ?X1 ?X2 ?X3 ?X4 < -2)%Z |- 
          (?X3 <= 0)%Z =>
              apply outside_square_9 with X1 X2 X4
          | id1:(outside_square ?X1 ?X2 ?X3 ?X4 < -2)%Z |- 
          (?X4 <= 0)%Z => apply outside_square_10 with X1 X2 X3
          end; assumption ].
     (* ~`o1 < (-2)` /\ ~`2 < o1` *)
      intros Ho2' Ho2.
      generalize
       (Qquadratic_sign_dL_nR_4 a b c d e f g h (dL xs) xs 
          (nR ys) ys H_Qquadratic_sg_denom_nonzero
          (Qquadratic_signok_3 _ _ _ _ _ _ H_Qquadratic_sg_denom_nonzero)
          (refl_equal _) (refl_equal _)).
      intros H1.
      assert
       (H_tuple_eq :
        Qquadratic_sign (a + c) (a + b + c + d) c (c + d) 
          (e + g) (e + f + g + h) g (g + h) xs ys
          (Qquadratic_signok_3 e f g h xs ys H_Qquadratic_sg_denom_nonzero) =
        ((-1)%Z, (na, (nb, (nc, nd)), (ne, (nf, (ng, nh))), (np1, np2))));
       [ apply
          trans_eq
           with
             (Qquadratic_sign a b c d e f g h (dL xs) 
                (nR ys) H_Qquadratic_sg_denom_nonzero);
          [ apply sym_eq; apply H1; repeat split | idtac ]
       | apply
          (Qquadratic_sign_neg_2 (a + c)%Z (a + b + c + d)%Z c 
             (c + d)%Z (e + g)%Z (e + f + g + h)%Z g 
             (g + h)%Z xs ys
             (Qquadratic_signok_3 e f g h xs ys H_Qquadratic_sg_denom_nonzero)
             na nb nc nd ne nf ng nh np1 np2) ]; assumption.
   (* ~ `b = 0`/\`c = 0`/\`d = 0` *)
   intros Hbcd'.
   (* Intros [Hb [Hc] Hd]. *)
   case (three_integers_dec_inf f g h).   
    (* `f = 0`/\`g = 0`/\`h = 0` *)
    intros (Hf, (Hg, Hh)).
    case (Z_lt_dec 2 o1).
     (*  `2 < o1` *)
     intro Ho1.
     generalize
      (Qquadratic_sign_nRdL_nRdL_5 a b c d e f g h 
         (dL xs) (nR ys) H_Qquadratic_sg_denom_nonzero).
     intros H1.
     assert
      (H_tuple_eq :
       ((-1)%Z, (na, (nb, (nc, nd)), (ne, (nf, (ng, nh))), (np1, np2))) =
       (Z.sgn e, (a, (b, (c, d)), (e, (f, (g, h))), (dL xs, nR ys))));
      [ apply
         trans_eq
          with
            (Qquadratic_sign a b c d e f g h (dL xs) 
               (nR ys) H_Qquadratic_sg_denom_nonzero);
         [ apply sym_eq | apply H1; discriminate || (repeat split) ];
         assumption
      | generalize
         (Qquadratic_sign_tuple_equal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
            _ _ H_tuple_eq);
         intros
          (hl,
           ((hna, (hnb, (hnc, (hnd, (hne, (hnf, (hng, hnh))))))),
           (hp1,
            hp2)));
         do 10
          match goal with
          | id1:(?X1 = ?X2) |- ?X3 => try rewrite id1; clear id1
          end ].
     left; left; left; left; left; left; repeat split;
      repeat
       match goal with
       | id1:(?X1 = 0%Z) |- ?X2 => rewrite id1; clear id1
       end; first
      [ apply Z.le_refl
      | match goal with
        |  |- (0 <= ?X1)%Z =>
            apply Zlt_le_weak; apply Zsgn_9; apply Z.opp_inj
        |  |- (?X1 <= 0)%Z => apply Zlt_le_weak; apply Zsgn_10
        end; apply sym_eq; assumption
      | unfold o1 in Ho1;
         match goal with
         | id1:(2 < outside_square ?X1 ?X2 ?X3 ?X4)%Z |- 
         (0 <= ?X1)%Z =>
             apply outside_square_3 with X2 X3 X4
         | id1:(2 < outside_square ?X1 ?X2 ?X3 ?X4)%Z |- 
         (0 <= ?X2)%Z =>
             apply outside_square_4 with X1 X3 X4
         | id1:(2 < outside_square ?X1 ?X2 ?X3 ?X4)%Z |- 
         (0 <= ?X3)%Z =>
             apply outside_square_5 with X1 X2 X4
         | id1:(2 < outside_square ?X1 ?X2 ?X3 ?X4)%Z |- 
         (0 <= ?X4)%Z =>
             apply outside_square_6 with X1 X2 X3
         | id1:(outside_square ?X1 ?X2 ?X3 ?X4 < -2)%Z |- 
         (?X1 <= 0)%Z =>
             apply outside_square_7 with X2 X3 X4
         | id1:(outside_square ?X1 ?X2 ?X3 ?X4 < -2)%Z |- 
         (?X2 <= 0)%Z =>
             apply outside_square_8 with X1 X3 X4
         | id1:(outside_square ?X1 ?X2 ?X3 ?X4 < -2)%Z |- 
         (?X3 <= 0)%Z =>
             apply outside_square_9 with X1 X2 X4
         | id1:(outside_square ?X1 ?X2 ?X3 ?X4 < -2)%Z |- 
         (?X4 <= 0)%Z => apply outside_square_10 with X1 X2 X3
         end; assumption ].
     (*  ~`2 < o1` *)
     case (Z_lt_dec o1 (-2)).
      (* `(-2) < o1` *)
      intros Ho1' Ho1.
      generalize
       (Qquadratic_sign_nRdL_nRdL_6 a b c d e f g h 
          (dL xs) (nR ys) H_Qquadratic_sg_denom_nonzero).
      intros H1.
      assert
       (H_tuple_eq :
        ((-1)%Z, (na, (nb, (nc, nd)), (ne, (nf, (ng, nh))), (np1, np2))) =
        ((- Z.sgn e)%Z, (a, (b, (c, d)), (e, (f, (g, h))), (dL xs, nR ys))));
       [ apply
          trans_eq
           with
             (Qquadratic_sign a b c d e f g h (dL xs) 
                (nR ys) H_Qquadratic_sg_denom_nonzero);
          [ apply sym_eq | apply H1; discriminate || (repeat split) ];
          assumption
       | generalize
          (Qquadratic_sign_tuple_equal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
             _ _ _ H_tuple_eq);
          intros
           (hl,
            ((hna, (hnb, (hnc, (hnd, (hne, (hnf, (hng, hnh))))))),
            (hp1,
             hp2)));
          do 10
           match goal with
           | id1:(?X1 = ?X2) |- ?X3 => try rewrite id1; clear id1
           end ].
      left; left; left; left; left; right; repeat split;
       repeat
        match goal with
        | id1:(?X1 = 0%Z) |- ?X2 => rewrite id1; clear id1
        end; first
       [ apply Z.le_refl
       | match goal with
         |  |- (0 <= ?X1)%Z =>
             apply Zlt_le_weak; apply Zsgn_9; apply Z.opp_inj
         |  |- (?X1 <= 0)%Z => apply Zlt_le_weak; apply Zsgn_10
         end; apply sym_eq; assumption
       | unfold o1 in Ho1';
          match goal with
          | id1:(2 < outside_square ?X1 ?X2 ?X3 ?X4)%Z |- 
          (0 <= ?X1)%Z =>
              apply outside_square_3 with X2 X3 X4
          | id1:(2 < outside_square ?X1 ?X2 ?X3 ?X4)%Z |- 
          (0 <= ?X2)%Z =>
              apply outside_square_4 with X1 X3 X4
          | id1:(2 < outside_square ?X1 ?X2 ?X3 ?X4)%Z |- 
          (0 <= ?X3)%Z =>
              apply outside_square_5 with X1 X2 X4
          | id1:(2 < outside_square ?X1 ?X2 ?X3 ?X4)%Z |- 
          (0 <= ?X4)%Z =>
              apply outside_square_6 with X1 X2 X3
          | id1:(outside_square ?X1 ?X2 ?X3 ?X4 < -2)%Z |- 
          (?X1 <= 0)%Z =>
              apply outside_square_7 with X2 X3 X4
          | id1:(outside_square ?X1 ?X2 ?X3 ?X4 < -2)%Z |- 
          (?X2 <= 0)%Z =>
              apply outside_square_8 with X1 X3 X4
          | id1:(outside_square ?X1 ?X2 ?X3 ?X4 < -2)%Z |- 
          (?X3 <= 0)%Z =>
              apply outside_square_9 with X1 X2 X4
          | id1:(outside_square ?X1 ?X2 ?X3 ?X4 < -2)%Z |- 
          (?X4 <= 0)%Z => apply outside_square_10 with X1 X2 X3
          end; assumption ].

      (* ~`o1 < (-2)` /\ ~`2 < o1` *)
      intros Ho2' Ho2.
      generalize
       (Qquadratic_sign_dL_nR_7 a b c d e f g h (dL xs) xs 
          (nR ys) ys H_Qquadratic_sg_denom_nonzero
          (Qquadratic_signok_3 _ _ _ _ _ _ H_Qquadratic_sg_denom_nonzero)
          (refl_equal _) (refl_equal _)).
      intros H1.
      assert
       (H_tuple_eq :
        Qquadratic_sign (a + c) (a + b + c + d) c (c + d) 
          (e + g) (e + f + g + h) g (g + h) xs ys
          (Qquadratic_signok_3 e f g h xs ys H_Qquadratic_sg_denom_nonzero) =
        ((-1)%Z, (na, (nb, (nc, nd)), (ne, (nf, (ng, nh))), (np1, np2))));
       [ apply
          trans_eq
           with
             (Qquadratic_sign a b c d e f g h (dL xs) 
                (nR ys) H_Qquadratic_sg_denom_nonzero);
          [ apply sym_eq; apply H1; repeat split | idtac ]
       | apply
          (Qquadratic_sign_neg_2 (a + c)%Z (a + b + c + d)%Z c 
             (c + d)%Z (e + g)%Z (e + f + g + h)%Z g 
             (g + h)%Z xs ys
             (Qquadratic_signok_3 e f g h xs ys H_Qquadratic_sg_denom_nonzero)
             na nb nc nd ne nf ng nh np1 np2) ]; assumption.
    (* ~(`f = 0`/\`g = 0`/\`h = 0`) *)
    intro Hfgh'.
    case (inside_square_1_dec_inf o1 o2).    
     (* (inside_square_1 o1 o2) *)
     intro H_inside_1.
     generalize
      (Qquadratic_sign_nRdL_nRdL_8 a b c d e f g h 
         (dL xs) (nR ys) H_Qquadratic_sg_denom_nonzero).
     intros H1.
     assert
      (H_tuple_eq :
       ((-1)%Z, (na, (nb, (nc, nd)), (ne, (nf, (ng, nh))), (np1, np2))) =
       (1%Z, (a, (b, (c, d)), (e, (f, (g, h))), (dL xs, nR ys))));
      [ apply
         trans_eq
          with
            (Qquadratic_sign a b c d e f g h (dL xs) 
               (nR ys) H_Qquadratic_sg_denom_nonzero);
         [ apply sym_eq | apply H1; discriminate || (repeat split) ];
         assumption
      | generalize
         (Qquadratic_sign_tuple_equal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
            _ _ H_tuple_eq);
         intros
          (hl,
           ((hna, (hnb, (hnc, (hnd, (hne, (hnf, (hng, hnh))))))),
           (hp1,
            hp2)));
         do 10
          match goal with
          | id1:(?X1 = ?X2) |- ?X3 => try rewrite id1; clear id1
          end ].
     discriminate hl.
     (* ~(inside_square_1 o1 o2) *)    
     intro H_inside_1'.
     case (inside_square_2_dec_inf o1 o2).    
      (* (inside_square_2 o1 o2) *)
      intro H_inside_2.
      generalize
       (Qquadratic_sign_nRdL_nRdL_9 a b c d e f g h 
          (dL xs) (nR ys) H_Qquadratic_sg_denom_nonzero).
      intros H1.
      assert
       (H_tuple_eq :
        ((-1)%Z, (na, (nb, (nc, nd)), (ne, (nf, (ng, nh))), (np1, np2))) =
        ((-1)%Z, (a, (b, (c, d)), (e, (f, (g, h))), (dL xs, nR ys))));
       [ apply
          trans_eq
           with
             (Qquadratic_sign a b c d e f g h (dL xs) 
                (nR ys) H_Qquadratic_sg_denom_nonzero);
          [ apply sym_eq | apply H1; discriminate || (repeat split) ];
          assumption
       | generalize
          (Qquadratic_sign_tuple_equal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
             _ _ _ H_tuple_eq);
          intros
           (hl,
            ((hna, (hnb, (hnc, (hnd, (hne, (hnf, (hng, hnh))))))),
            (hp1,
             hp2)));
          do 10
           match goal with
           | id1:(?X1 = ?X2) |- ?X3 => try rewrite id1; clear id1
           end ].
     left; left; left; left; left; case (inside_square_2_inf _ _ H_inside_2);
      intros (Ho1, Ho2); [ left | right ]; repeat split; first
      [ apply Z.le_refl
      | match goal with
        |  |- (0 <= ?X1)%Z =>
            apply Zlt_le_weak; apply Zsgn_9; apply Z.opp_inj
        |  |- (?X1 <= 0)%Z => apply Zlt_le_weak; apply Zsgn_10
        end; apply sym_eq; assumption
      | unfold o1 in Ho1; unfold o2 in Ho2;
         match goal with
         | id1:(2 < outside_square ?X1 ?X2 ?X3 ?X4)%Z |- 
         (0 <= ?X1)%Z =>
             apply outside_square_3 with X2 X3 X4
         | id1:(2 < outside_square ?X1 ?X2 ?X3 ?X4)%Z |- 
         (0 <= ?X2)%Z =>
             apply outside_square_4 with X1 X3 X4
         | id1:(2 < outside_square ?X1 ?X2 ?X3 ?X4)%Z |- 
         (0 <= ?X3)%Z =>
             apply outside_square_5 with X1 X2 X4
         | id1:(2 < outside_square ?X1 ?X2 ?X3 ?X4)%Z |- 
         (0 <= ?X4)%Z =>
             apply outside_square_6 with X1 X2 X3
         | id1:(outside_square ?X1 ?X2 ?X3 ?X4 < -2)%Z |- 
         (?X1 <= 0)%Z =>
             apply outside_square_7 with X2 X3 X4
         | id1:(outside_square ?X1 ?X2 ?X3 ?X4 < -2)%Z |- 
         (?X2 <= 0)%Z =>
             apply outside_square_8 with X1 X3 X4
         | id1:(outside_square ?X1 ?X2 ?X3 ?X4 < -2)%Z |- 
         (?X3 <= 0)%Z =>
             apply outside_square_9 with X1 X2 X4
         | id1:(outside_square ?X1 ?X2 ?X3 ?X4 < -2)%Z |- 
         (?X4 <= 0)%Z => apply outside_square_10 with X1 X2 X3
         end; assumption ].

      (*  ~(inside_square_1 o1 o2)/\~(inside_square_2 o1 o2) *)
      intros H_inside_2'. 
      generalize
       (Qquadratic_sign_dL_nR_10 a b c d e f g h (dL xs) xs 
          (nR ys) ys H_Qquadratic_sg_denom_nonzero
          (Qquadratic_signok_3 _ _ _ _ _ _ H_Qquadratic_sg_denom_nonzero)
          (refl_equal _) (refl_equal _)).
      intros H1.
      assert
       (H_tuple_eq :
        Qquadratic_sign (a + c) (a + b + c + d) c (c + d) 
          (e + g) (e + f + g + h) g (g + h) xs ys
          (Qquadratic_signok_3 e f g h xs ys H_Qquadratic_sg_denom_nonzero) =
        ((-1)%Z, (na, (nb, (nc, nd)), (ne, (nf, (ng, nh))), (np1, np2))));
       [ apply
          trans_eq
           with
             (Qquadratic_sign a b c d e f g h (dL xs) 
                (nR ys) H_Qquadratic_sg_denom_nonzero);
          [ apply sym_eq; apply H1; repeat split | idtac ]
       | apply
          (Qquadratic_sign_neg_2 (a + c)%Z (a + b + c + d)%Z c 
             (c + d)%Z (e + g)%Z (e + f + g + h)%Z g 
             (g + h)%Z xs ys
             (Qquadratic_signok_3 e f g h xs ys H_Qquadratic_sg_denom_nonzero)
             na nb nc nd ne nf ng nh np1 np2) ]; assumption.

 (*  p1 = (dL xs) & p2 = (dL ys) *)
  case (three_integers_dec_inf b c d).  
   (* `b = 0`/\`c = 0`/\`d = 0` *)
   intros (Hb, (Hc, Hd)).
   (* Intros [Hb [Hc] Hd]. *)
   case (three_integers_dec_inf f g h).   
    (* `f = 0`/\`g = 0`/\`h = 0` *)
    intros (Hf, (Hg, Hh)).
    generalize
     (Qquadratic_sign_nRdL_nRdL_1 a b c d e f g h (dL xs) 
        (dL ys) H_Qquadratic_sg_denom_nonzero).
    intros H1.
    assert
     (H_tuple_eq :
      ((-1)%Z, (na, (nb, (nc, nd)), (ne, (nf, (ng, nh))), (np1, np2))) =
      ((Z.sgn a * Z.sgn e)%Z,
      (a, (b, (c, d)), (e, (f, (g, h))), (dL xs, dL ys))));
     [ apply
        trans_eq
         with
           (Qquadratic_sign a b c d e f g h (dL xs) 
              (dL ys) H_Qquadratic_sg_denom_nonzero);
        [ apply sym_eq | apply H1; discriminate || (repeat split) ];
        assumption
     | generalize
        (Qquadratic_sign_tuple_equal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
           _ _ H_tuple_eq);
        intros
         (hl,
          ((hna, (hnb, (hnc, (hnd, (hne, (hnf, (hng, hnh))))))),
          (hp1,
           hp2)));
        do 10
         match goal with
         | id1:(?X1 = ?X2) |- ?X3 => try rewrite id1; clear id1
         end ].
    left; left; left; left; left; rewrite <- Zsgn_15 in hl.
    case (Zsgn_17 _ _ (sym_eq hl)); intros (Ha, He); [ left | right ];
     repeat split;
     repeat
      match goal with
      | id1:(?X1 = 0%Z) |- ?X2 => rewrite id1; clear id1
      end; first [ apply Z.le_refl | apply Zlt_le_weak ]; 
     assumption.
    (* ~(`f = 0`/\`g = 0`/\`h = 0`) *)
    intros H_fgh'.
    case (Z_lt_dec 2 o2).
     (*  `2 < o2` *)
     intro Ho2.
     generalize
      (Qquadratic_sign_nRdL_nRdL_2 a b c d e f g h 
         (dL xs) (dL ys) H_Qquadratic_sg_denom_nonzero).
     intros H1.
     assert
      (H_tuple_eq :
       ((-1)%Z, (na, (nb, (nc, nd)), (ne, (nf, (ng, nh))), (np1, np2))) =
       (Z.sgn a, (a, (b, (c, d)), (e, (f, (g, h))), (dL xs, dL ys))));
      [ apply
         trans_eq
          with
            (Qquadratic_sign a b c d e f g h (dL xs) 
               (dL ys) H_Qquadratic_sg_denom_nonzero);
         [ apply sym_eq | apply H1; discriminate || (repeat split) ];
         assumption
      | generalize
         (Qquadratic_sign_tuple_equal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
            _ _ H_tuple_eq);
         intros
          (hl,
           ((hna, (hnb, (hnc, (hnd, (hne, (hnf, (hng, hnh))))))),
           (hp1,
            hp2)));
         do 10
          match goal with
          | id1:(?X1 = ?X2) |- ?X3 => try rewrite id1; clear id1
          end ].
     left; left; left; left; left; right; repeat split;
      repeat
       match goal with
       | id1:(?X1 = 0%Z) |- ?X2 => rewrite id1; clear id1
       end; first
      [ apply Z.le_refl
      | match goal with
        |  |- (0 <= ?X1)%Z =>
            apply Zlt_le_weak; apply Zsgn_9; apply Z.opp_inj
        |  |- (?X1 <= 0)%Z => apply Zlt_le_weak; apply Zsgn_10
        end; apply sym_eq; assumption
      | unfold o2 in Ho2;
         match goal with
         | id1:(2 < outside_square ?X1 ?X2 ?X3 ?X4)%Z |- 
         (0 <= ?X1)%Z =>
             apply outside_square_3 with X2 X3 X4
         | id1:(2 < outside_square ?X1 ?X2 ?X3 ?X4)%Z |- 
         (0 <= ?X2)%Z =>
             apply outside_square_4 with X1 X3 X4
         | id1:(2 < outside_square ?X1 ?X2 ?X3 ?X4)%Z |- 
         (0 <= ?X3)%Z =>
             apply outside_square_5 with X1 X2 X4
         | id1:(2 < outside_square ?X1 ?X2 ?X3 ?X4)%Z |- 
         (0 <= ?X4)%Z =>
             apply outside_square_6 with X1 X2 X3
         | id1:(outside_square ?X1 ?X2 ?X3 ?X4 < -2)%Z |- 
         (?X1 <= 0)%Z =>
             apply outside_square_7 with X2 X3 X4
         | id1:(outside_square ?X1 ?X2 ?X3 ?X4 < -2)%Z |- 
         (?X2 <= 0)%Z =>
             apply outside_square_8 with X1 X3 X4
         | id1:(outside_square ?X1 ?X2 ?X3 ?X4 < -2)%Z |- 
         (?X3 <= 0)%Z =>
             apply outside_square_9 with X1 X2 X4
         | id1:(outside_square ?X1 ?X2 ?X3 ?X4 < -2)%Z |- 
         (?X4 <= 0)%Z => apply outside_square_10 with X1 X2 X3
         end; assumption ].
     
     (*  ~`2 < o2` *)
     case (Z_lt_dec o2 (-2)).     
     (* `(-2) < o2` *)
      intros Ho2' Ho2.
      generalize
       (Qquadratic_sign_nRdL_nRdL_3 a b c d e f g h 
          (dL xs) (dL ys) H_Qquadratic_sg_denom_nonzero).
      intros H1.
      assert
       (H_tuple_eq :
        ((-1)%Z, (na, (nb, (nc, nd)), (ne, (nf, (ng, nh))), (np1, np2))) =
        ((- Z.sgn a)%Z, (a, (b, (c, d)), (e, (f, (g, h))), (dL xs, dL ys))));
       [ apply
          trans_eq
           with
             (Qquadratic_sign a b c d e f g h (dL xs) 
                (dL ys) H_Qquadratic_sg_denom_nonzero);
          [ apply sym_eq | apply H1; discriminate || (repeat split) ];
          assumption
       | generalize
          (Qquadratic_sign_tuple_equal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
             _ _ _ H_tuple_eq);
          intros
           (hl,
            ((hna, (hnb, (hnc, (hnd, (hne, (hnf, (hng, hnh))))))),
            (hp1,
             hp2)));
          do 10
           match goal with
           | id1:(?X1 = ?X2) |- ?X3 => try rewrite id1; clear id1
           end ].
      left; left; left; left; left; left; repeat split;
       repeat
        match goal with
        | id1:(?X1 = 0%Z) |- ?X2 => rewrite id1; clear id1
        end; first
       [ apply Z.le_refl
       | match goal with
         |  |- (0 <= ?X1)%Z =>
             apply Zlt_le_weak; apply Zsgn_9; apply Z.opp_inj
         |  |- (?X1 <= 0)%Z => apply Zlt_le_weak; apply Zsgn_10
         end; apply sym_eq; assumption
       | unfold o2 in Ho2';
          match goal with
          | id1:(2 < outside_square ?X1 ?X2 ?X3 ?X4)%Z |- 
          (0 <= ?X1)%Z =>
              apply outside_square_3 with X2 X3 X4
          | id1:(2 < outside_square ?X1 ?X2 ?X3 ?X4)%Z |- 
          (0 <= ?X2)%Z =>
              apply outside_square_4 with X1 X3 X4
          | id1:(2 < outside_square ?X1 ?X2 ?X3 ?X4)%Z |- 
          (0 <= ?X3)%Z =>
              apply outside_square_5 with X1 X2 X4
          | id1:(2 < outside_square ?X1 ?X2 ?X3 ?X4)%Z |- 
          (0 <= ?X4)%Z =>
              apply outside_square_6 with X1 X2 X3
          | id1:(outside_square ?X1 ?X2 ?X3 ?X4 < -2)%Z |- 
          (?X1 <= 0)%Z =>
              apply outside_square_7 with X2 X3 X4
          | id1:(outside_square ?X1 ?X2 ?X3 ?X4 < -2)%Z |- 
          (?X2 <= 0)%Z =>
              apply outside_square_8 with X1 X3 X4
          | id1:(outside_square ?X1 ?X2 ?X3 ?X4 < -2)%Z |- 
          (?X3 <= 0)%Z =>
              apply outside_square_9 with X1 X2 X4
          | id1:(outside_square ?X1 ?X2 ?X3 ?X4 < -2)%Z |- 
          (?X4 <= 0)%Z => apply outside_square_10 with X1 X2 X3
          end; assumption ].
     (* ~`o1 < (-2)` /\ ~`2 < o1` *)
      intros Ho2' Ho2.
      generalize
       (Qquadratic_sign_dL_dL_4 a b c d e f g h (dL xs) xs 
          (dL ys) ys H_Qquadratic_sg_denom_nonzero
          (Qquadratic_signok_4 _ _ _ _ _ _ H_Qquadratic_sg_denom_nonzero)
          (refl_equal _) (refl_equal _)).
      intros H1.
      assert
       (H_tuple_eq :
        Qquadratic_sign (a + b + c + d) (b + d) (c + d) d 
          (e + f + g + h) (f + h) (g + h) h xs ys
          (Qquadratic_signok_4 e f g h xs ys H_Qquadratic_sg_denom_nonzero) =
        ((-1)%Z, (na, (nb, (nc, nd)), (ne, (nf, (ng, nh))), (np1, np2))));
       [ apply
          trans_eq
           with
             (Qquadratic_sign a b c d e f g h (dL xs) 
                (dL ys) H_Qquadratic_sg_denom_nonzero);
          [ apply sym_eq; apply H1; repeat split | idtac ]
       | apply
          (Qquadratic_sign_neg_2 (a + b + c + d)%Z 
             (b + d)%Z (c + d)%Z d (e + f + g + h)%Z 
             (f + h)%Z (g + h)%Z h xs ys
             (Qquadratic_signok_4 e f g h xs ys H_Qquadratic_sg_denom_nonzero)
             na nb nc nd ne nf ng nh np1 np2) ]; assumption.
   (* ~ `b = 0`/\`c = 0`/\`d = 0` *)
   intros Hbcd'.
   (* Intros [Hb [Hc] Hd]. *)
   case (three_integers_dec_inf f g h).   
    (* `f = 0`/\`g = 0`/\`h = 0` *)
    intros (Hf, (Hg, Hh)).
    case (Z_lt_dec 2 o1).
     (*  `2 < o1` *)
     intro Ho1.
     generalize
      (Qquadratic_sign_nRdL_nRdL_5 a b c d e f g h 
         (dL xs) (dL ys) H_Qquadratic_sg_denom_nonzero).
     intros H1.
     assert
      (H_tuple_eq :
       ((-1)%Z, (na, (nb, (nc, nd)), (ne, (nf, (ng, nh))), (np1, np2))) =
       (Z.sgn e, (a, (b, (c, d)), (e, (f, (g, h))), (dL xs, dL ys))));
      [ apply
         trans_eq
          with
            (Qquadratic_sign a b c d e f g h (dL xs) 
               (dL ys) H_Qquadratic_sg_denom_nonzero);
         [ apply sym_eq | apply H1; discriminate || (repeat split) ];
         assumption
      | generalize
         (Qquadratic_sign_tuple_equal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
            _ _ H_tuple_eq);
         intros
          (hl,
           ((hna, (hnb, (hnc, (hnd, (hne, (hnf, (hng, hnh))))))),
           (hp1,
            hp2)));
         do 10
          match goal with
          | id1:(?X1 = ?X2) |- ?X3 => try rewrite id1; clear id1
          end ].
     left; left; left; left; left; left; repeat split;
      repeat
       match goal with
       | id1:(?X1 = 0%Z) |- ?X2 => rewrite id1; clear id1
       end; first
      [ apply Z.le_refl
      | match goal with
        |  |- (0 <= ?X1)%Z =>
            apply Zlt_le_weak; apply Zsgn_9; apply Z.opp_inj
        |  |- (?X1 <= 0)%Z => apply Zlt_le_weak; apply Zsgn_10
        end; apply sym_eq; assumption
      | unfold o1 in Ho1;
         match goal with
         | id1:(2 < outside_square ?X1 ?X2 ?X3 ?X4)%Z |- 
         (0 <= ?X1)%Z =>
             apply outside_square_3 with X2 X3 X4
         | id1:(2 < outside_square ?X1 ?X2 ?X3 ?X4)%Z |- 
         (0 <= ?X2)%Z =>
             apply outside_square_4 with X1 X3 X4
         | id1:(2 < outside_square ?X1 ?X2 ?X3 ?X4)%Z |- 
         (0 <= ?X3)%Z =>
             apply outside_square_5 with X1 X2 X4
         | id1:(2 < outside_square ?X1 ?X2 ?X3 ?X4)%Z |- 
         (0 <= ?X4)%Z =>
             apply outside_square_6 with X1 X2 X3
         | id1:(outside_square ?X1 ?X2 ?X3 ?X4 < -2)%Z |- 
         (?X1 <= 0)%Z =>
             apply outside_square_7 with X2 X3 X4
         | id1:(outside_square ?X1 ?X2 ?X3 ?X4 < -2)%Z |- 
         (?X2 <= 0)%Z =>
             apply outside_square_8 with X1 X3 X4
         | id1:(outside_square ?X1 ?X2 ?X3 ?X4 < -2)%Z |- 
         (?X3 <= 0)%Z =>
             apply outside_square_9 with X1 X2 X4
         | id1:(outside_square ?X1 ?X2 ?X3 ?X4 < -2)%Z |- 
         (?X4 <= 0)%Z => apply outside_square_10 with X1 X2 X3
         end; assumption ].
     (*  ~`2 < o1` *)
     case (Z_lt_dec o1 (-2)).
      (* `(-2) < o1` *)
      intros Ho1' Ho1.
      generalize
       (Qquadratic_sign_nRdL_nRdL_6 a b c d e f g h 
          (dL xs) (dL ys) H_Qquadratic_sg_denom_nonzero).
      intros H1.
      assert
       (H_tuple_eq :
        ((-1)%Z, (na, (nb, (nc, nd)), (ne, (nf, (ng, nh))), (np1, np2))) =
        ((- Z.sgn e)%Z, (a, (b, (c, d)), (e, (f, (g, h))), (dL xs, dL ys))));
       [ apply
          trans_eq
           with
             (Qquadratic_sign a b c d e f g h (dL xs) 
                (dL ys) H_Qquadratic_sg_denom_nonzero);
          [ apply sym_eq | apply H1; discriminate || (repeat split) ];
          assumption
       | generalize
          (Qquadratic_sign_tuple_equal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
             _ _ _ H_tuple_eq);
          intros
           (hl,
            ((hna, (hnb, (hnc, (hnd, (hne, (hnf, (hng, hnh))))))),
            (hp1,
             hp2)));
          do 10
           match goal with
           | id1:(?X1 = ?X2) |- ?X3 => try rewrite id1; clear id1
           end ].
      left; left; left; left; left; right; repeat split;
       repeat
        match goal with
        | id1:(?X1 = 0%Z) |- ?X2 => rewrite id1; clear id1
        end; first
       [ apply Z.le_refl
       | match goal with
         |  |- (0 <= ?X1)%Z =>
             apply Zlt_le_weak; apply Zsgn_9; apply Z.opp_inj
         |  |- (?X1 <= 0)%Z => apply Zlt_le_weak; apply Zsgn_10
         end; apply sym_eq; assumption
       | unfold o1 in Ho1';
          match goal with
          | id1:(2 < outside_square ?X1 ?X2 ?X3 ?X4)%Z |- 
          (0 <= ?X1)%Z =>
              apply outside_square_3 with X2 X3 X4
          | id1:(2 < outside_square ?X1 ?X2 ?X3 ?X4)%Z |- 
          (0 <= ?X2)%Z =>
              apply outside_square_4 with X1 X3 X4
          | id1:(2 < outside_square ?X1 ?X2 ?X3 ?X4)%Z |- 
          (0 <= ?X3)%Z =>
              apply outside_square_5 with X1 X2 X4
          | id1:(2 < outside_square ?X1 ?X2 ?X3 ?X4)%Z |- 
          (0 <= ?X4)%Z =>
              apply outside_square_6 with X1 X2 X3
          | id1:(outside_square ?X1 ?X2 ?X3 ?X4 < -2)%Z |- 
          (?X1 <= 0)%Z =>
              apply outside_square_7 with X2 X3 X4
          | id1:(outside_square ?X1 ?X2 ?X3 ?X4 < -2)%Z |- 
          (?X2 <= 0)%Z =>
              apply outside_square_8 with X1 X3 X4
          | id1:(outside_square ?X1 ?X2 ?X3 ?X4 < -2)%Z |- 
          (?X3 <= 0)%Z =>
              apply outside_square_9 with X1 X2 X4
          | id1:(outside_square ?X1 ?X2 ?X3 ?X4 < -2)%Z |- 
          (?X4 <= 0)%Z => apply outside_square_10 with X1 X2 X3
          end; assumption ].

      (* ~`o1 < (-2)` /\ ~`2 < o1` *)
      intros Ho2' Ho2.
      generalize
       (Qquadratic_sign_dL_dL_7 a b c d e f g h (dL xs) xs 
          (dL ys) ys H_Qquadratic_sg_denom_nonzero
          (Qquadratic_signok_4 _ _ _ _ _ _ H_Qquadratic_sg_denom_nonzero)
          (refl_equal _) (refl_equal _)).
      intros H1.
      assert
       (H_tuple_eq :
        Qquadratic_sign (a + b + c + d) (b + d) (c + d) d 
          (e + f + g + h) (f + h) (g + h) h xs ys
          (Qquadratic_signok_4 e f g h xs ys H_Qquadratic_sg_denom_nonzero) =
        ((-1)%Z, (na, (nb, (nc, nd)), (ne, (nf, (ng, nh))), (np1, np2))));
       [ apply
          trans_eq
           with
             (Qquadratic_sign a b c d e f g h (dL xs) 
                (dL ys) H_Qquadratic_sg_denom_nonzero);
          [ apply sym_eq; apply H1; repeat split | idtac ]
       | apply
          (Qquadratic_sign_neg_2 (a + b + c + d)%Z 
             (b + d)%Z (c + d)%Z d (e + f + g + h)%Z 
             (f + h)%Z (g + h)%Z h xs ys
             (Qquadratic_signok_4 e f g h xs ys H_Qquadratic_sg_denom_nonzero)
             na nb nc nd ne nf ng nh np1 np2) ]; assumption.
    (* ~(`f = 0`/\`g = 0`/\`h = 0`) *)
    intro Hfgh'.
    case (inside_square_1_dec_inf o1 o2).    
     (* (inside_square_1 o1 o2) *)
     intro H_inside_1.
     generalize
      (Qquadratic_sign_nRdL_nRdL_8 a b c d e f g h 
         (dL xs) (dL ys) H_Qquadratic_sg_denom_nonzero).
     intros H1.
     assert
      (H_tuple_eq :
       ((-1)%Z, (na, (nb, (nc, nd)), (ne, (nf, (ng, nh))), (np1, np2))) =
       (1%Z, (a, (b, (c, d)), (e, (f, (g, h))), (dL xs, dL ys))));
      [ apply
         trans_eq
          with
            (Qquadratic_sign a b c d e f g h (dL xs) 
               (dL ys) H_Qquadratic_sg_denom_nonzero);
         [ apply sym_eq | apply H1; discriminate || (repeat split) ];
         assumption
      | generalize
         (Qquadratic_sign_tuple_equal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
            _ _ H_tuple_eq);
         intros
          (hl,
           ((hna, (hnb, (hnc, (hnd, (hne, (hnf, (hng, hnh))))))),
           (hp1,
            hp2)));
         do 10
          match goal with
          | id1:(?X1 = ?X2) |- ?X3 => try rewrite id1; clear id1
          end ].
     discriminate hl.

      (* ~(inside_square_1 o1 o2) *)    
     intro H_inside_1'.
     case (inside_square_2_dec_inf o1 o2).    
      (* (inside_square_2 o1 o2) *)
      intro H_inside_2.
      generalize
       (Qquadratic_sign_nRdL_nRdL_9 a b c d e f g h 
          (dL xs) (dL ys) H_Qquadratic_sg_denom_nonzero).
      intros H1.
      assert
       (H_tuple_eq :
        ((-1)%Z, (na, (nb, (nc, nd)), (ne, (nf, (ng, nh))), (np1, np2))) =
        ((-1)%Z, (a, (b, (c, d)), (e, (f, (g, h))), (dL xs, dL ys))));
       [ apply
          trans_eq
           with
             (Qquadratic_sign a b c d e f g h (dL xs) 
                (dL ys) H_Qquadratic_sg_denom_nonzero);
          [ apply sym_eq | apply H1; discriminate || (repeat split) ];
          assumption
       | generalize
          (Qquadratic_sign_tuple_equal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
             _ _ _ H_tuple_eq);
          intros
           (hl,
            ((hna, (hnb, (hnc, (hnd, (hne, (hnf, (hng, hnh))))))),
            (hp1,
             hp2)));
          do 10
           match goal with
           | id1:(?X1 = ?X2) |- ?X3 => try rewrite id1; clear id1
           end ].
     left; left; left; left; left; case (inside_square_2_inf _ _ H_inside_2);
      intros (Ho1, Ho2); [ left | right ]; repeat split; first
      [ apply Z.le_refl
      | match goal with
        |  |- (0 <= ?X1)%Z =>
            apply Zlt_le_weak; apply Zsgn_9; apply Z.opp_inj
        |  |- (?X1 <= 0)%Z => apply Zlt_le_weak; apply Zsgn_10
        end; apply sym_eq; assumption
      | unfold o1 in Ho1; unfold o2 in Ho2;
         match goal with
         | id1:(2 < outside_square ?X1 ?X2 ?X3 ?X4)%Z |- 
         (0 <= ?X1)%Z =>
             apply outside_square_3 with X2 X3 X4
         | id1:(2 < outside_square ?X1 ?X2 ?X3 ?X4)%Z |- 
         (0 <= ?X2)%Z =>
             apply outside_square_4 with X1 X3 X4
         | id1:(2 < outside_square ?X1 ?X2 ?X3 ?X4)%Z |- 
         (0 <= ?X3)%Z =>
             apply outside_square_5 with X1 X2 X4
         | id1:(2 < outside_square ?X1 ?X2 ?X3 ?X4)%Z |- 
         (0 <= ?X4)%Z =>
             apply outside_square_6 with X1 X2 X3
         | id1:(outside_square ?X1 ?X2 ?X3 ?X4 < -2)%Z |- 
         (?X1 <= 0)%Z =>
             apply outside_square_7 with X2 X3 X4
         | id1:(outside_square ?X1 ?X2 ?X3 ?X4 < -2)%Z |- 
         (?X2 <= 0)%Z =>
             apply outside_square_8 with X1 X3 X4
         | id1:(outside_square ?X1 ?X2 ?X3 ?X4 < -2)%Z |- 
         (?X3 <= 0)%Z =>
             apply outside_square_9 with X1 X2 X4
         | id1:(outside_square ?X1 ?X2 ?X3 ?X4 < -2)%Z |- 
         (?X4 <= 0)%Z => apply outside_square_10 with X1 X2 X3
         end; assumption ].
      (*  ~(inside_square_1 o1 o2)/\~(inside_square_2 o1 o2) *)
      intros H_inside_2'. 
      generalize
       (Qquadratic_sign_dL_dL_10 a b c d e f g h (dL xs) xs 
          (dL ys) ys H_Qquadratic_sg_denom_nonzero
          (Qquadratic_signok_4 _ _ _ _ _ _ H_Qquadratic_sg_denom_nonzero)
          (refl_equal _) (refl_equal _)).
      intros H1.
      assert
       (H_tuple_eq :
        Qquadratic_sign (a + b + c + d) (b + d) (c + d) d 
          (e + f + g + h) (f + h) (g + h) h xs ys
          (Qquadratic_signok_4 e f g h xs ys H_Qquadratic_sg_denom_nonzero) =
        ((-1)%Z, (na, (nb, (nc, nd)), (ne, (nf, (ng, nh))), (np1, np2))));
       [ apply
          trans_eq
           with
             (Qquadratic_sign a b c d e f g h (dL xs) 
                (dL ys) H_Qquadratic_sg_denom_nonzero);
          [ apply sym_eq; apply H1; repeat split | idtac ]
       | apply
          (Qquadratic_sign_neg_2 (a + b + c + d)%Z 
             (b + d)%Z (c + d)%Z d (e + f + g + h)%Z 
             (f + h)%Z (g + h)%Z h xs ys
             (Qquadratic_signok_4 e f g h xs ys H_Qquadratic_sg_denom_nonzero)
             na nb nc nd ne nf ng nh np1 np2) ]; assumption.
 (*  p1 = (dL xs) & p2 = One *)
  generalize (Qquadratic_signok_0' _ _ _ _ _ H_Qquadratic_sg_denom_nonzero).
  intros H_Qhomographic_sg_denom_nonzero.
  set
   (L3 :=
    Qhomographic_sign (a + b) (c + d) (e + f) (g + h) 
      (dL xs) H_Qhomographic_sg_denom_nonzero) in *.
  set (l1 := fst L3) in *.
  set (l2 := fst (snd L3)) in *.
  set (l3 := snd (snd L3)) in *.
  set (na_ := fst l2) in *.
  set (nb_ := fst (snd l2)) in *.
  set (nc_ := fst (snd (snd l2))) in *.
  set (nd_ := snd (snd (snd l2))) in *.
  generalize
   (Qquadratic_sign_nRdL_One a b c d e f g h (dL xs) One
      H_Qquadratic_sg_denom_nonzero l1 na_ nb_ nc_ nd_ l3
      H_Qhomographic_sg_denom_nonzero); intros H1.
  assert
   (H_tuple_eq :
    ((-1)%Z, (na, (nb, (nc, nd)), (ne, (nf, (ng, nh))), (np1, np2))) =
    (l1, (0%Z, (na_, (0%Z, nb_)), (0%Z, (nc_, (0%Z, nd_))), (l3, One))));
   [ apply
      trans_eq
       with
         (Qquadratic_sign a b c d e f g h (dL xs) One
            H_Qquadratic_sg_denom_nonzero);
      [ apply sym_eq; assumption
      | apply H1; fold L3 in |- *; repeat (apply pair_2; try reflexivity);
         discriminate || reflexivity ]
   | generalize
      (Qquadratic_sign_tuple_equal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
         _ H_tuple_eq);
      intros
       (hl,
        ((hna, (hnb, (hnc, (hnd, (hne, (hnf, (hng, hnh))))))),
        (hp1,
         hp2)));
      do 10
       match goal with
       | id1:(?X1 = ?X2) |- ?X3 => try rewrite id1; clear id1
       end; repeat rewrite ZERO_left; repeat rewrite Zplus_0_r ].
  assert
   (H_sg_unfolded :
    Qhomographic_sign (a + b) (c + d) (e + f) (g + h) 
      (dL xs) H_Qhomographic_sg_denom_nonzero =
    ((-1)%Z, (na_, (nb_, (nc_, nd_)), l3))).
  rewrite hl; fold L3 in |- *; repeat (apply pair_2; try reflexivity);
   discriminate || reflexivity.
  generalize
   (sg_neg_2 (a + b) (c + d) (e + f) (g + h) (dL xs)
      H_Qhomographic_sg_denom_nonzero na_ nb_ nc_ nd_ l3 H_sg_unfolded).
  intros [[(H_a, (H_b, (H_c, H_d)))| (H_a, (H_b, (H_c, H_d)))]| H_l3];
   [ case l3; left;
      [ right; repeat split; assumption || discriminate
      | right; repeat split; assumption || discriminate
      | left; right; repeat split ]
   | case l3;
      [ right; repeat split; assumption || discriminate
      | right; repeat split; assumption || discriminate
      | left; left; right; repeat split ]
   | left; left; right; repeat split; assumption ].

 (* p1 = One *)
  generalize (Qquadratic_signok_0 _ _ _ _ _ H_Qquadratic_sg_denom_nonzero).
  intros H_Qhomographic_sg_denom_nonzero.
  set
   (L3 :=
    Qhomographic_sign (a + c) (b + d) (e + g) (f + h) p2
      H_Qhomographic_sg_denom_nonzero) in *.
  set (l1 := fst L3) in *.
  set (l2 := fst (snd L3)) in *.
  set (l3 := snd (snd L3)) in *.
  set (na_ := fst l2) in *.
  set (nb_ := fst (snd l2)) in *.
  set (nc_ := fst (snd (snd l2))) in *.
  set (nd_ := snd (snd (snd l2))) in *.
  generalize
   (Qquadratic_sign_One_y a b c d e f g h One p2
      H_Qquadratic_sg_denom_nonzero l1 na_ nb_ nc_ nd_ l3
      H_Qhomographic_sg_denom_nonzero); intros H1.
  assert
   (H_tuple_eq :
    ((-1)%Z, (na, (nb, (nc, nd)), (ne, (nf, (ng, nh))), (np1, np2))) =
    (l1, (0%Z, (0%Z, (na_, nb_)), (0%Z, (0%Z, (nc_, nd_))), (One, l3))));
   [ apply
      trans_eq
       with
         (Qquadratic_sign a b c d e f g h One p2
            H_Qquadratic_sg_denom_nonzero);
      [ apply sym_eq; assumption
      | apply H1; fold L3 in |- *; repeat (apply pair_2; try reflexivity);
         discriminate || reflexivity ]
   | generalize
      (Qquadratic_sign_tuple_equal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
         _ H_tuple_eq);
      intros
       (hl,
        ((hna, (hnb, (hnc, (hnd, (hne, (hnf, (hng, hnh))))))),
        (hp1,
         hp2)));
      do 10
       match goal with
       | id1:(?X1 = ?X2) |- ?X3 => try rewrite id1; clear id1
       end; repeat rewrite ZERO_left; repeat rewrite Zplus_0_r ].
  assert
   (H_sg_unfolded :
    Qhomographic_sign (a + c) (b + d) (e + g) (f + h) p2
      H_Qhomographic_sg_denom_nonzero =
    ((-1)%Z, (na_, (nb_, (nc_, nd_)), l3))).
  rewrite hl; fold L3 in |- *; repeat (apply pair_2; try reflexivity);
   discriminate || reflexivity.
  generalize
   (sg_neg_2 (a + c) (b + d) (e + g) (f + h) p2
      H_Qhomographic_sg_denom_nonzero na_ nb_ nc_ nd_ l3 H_sg_unfolded).
  intros [[(H_a, (H_b, (H_c, H_d)))| (H_a, (H_b, (H_c, H_d)))]| H_l3]; left;
   left; [ left; left; right | left; right | right ]; 
   repeat split; assumption.
Qed.
