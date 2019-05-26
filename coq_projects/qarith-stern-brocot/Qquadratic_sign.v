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
Require Import Qhomographic_sign.
Require Import Zaux.

Definition outside_square (a b c d : Z) :=
  (Z.sgn a + Z.sgn b + Z.sgn c + Z.sgn d)%Z.


Lemma three_integers_dec_inf :
 forall a b c : Z,
 {a = 0%Z /\ b = 0%Z /\ c = 0%Z} + {~ (a = 0%Z /\ b = 0%Z /\ c = 0%Z)}.
Proof.
 intros. 
 case (Z_zerop a).
 intro.
 case (Z_zerop b).
 intro.
 case (Z_zerop c);
  [ intro; left; repeat split; assumption
  | intro; right; intros (H, (H1, H2)); Falsum ].
 intro; right; intros (H, (H1, H2)); Falsum.
 intro; right; intros (H, (H1, H2)); Falsum.
Defined.


Definition inside_square_1 (o1 o2 : Z) :=
  (2 < o1)%Z /\ (2 < o2)%Z \/ (o1 < -2)%Z /\ (o2 < -2)%Z.

Definition inside_square_2 (o1 o2 : Z) :=
  (2 < o1)%Z /\ (o2 < -2)%Z \/ (o1 < -2)%Z /\ (2 < o2)%Z.

Lemma inside_square_1_dec_inf :
 forall o1 o2 : Z, {inside_square_1 o1 o2} + {~ inside_square_1 o1 o2}.
Proof.
 intros.
 case (Z_lt_dec 2 o1).
 intro.
 case (Z_lt_dec 2 o2).
 intros.
 left.
 left. 
 split; repeat assumption.
 intro.
 right. 
 intro.
 apply n.
 case H. 
 intros (H1, H2).
 assumption.
 intros (H1, H2).
 apply False_ind.
 apply Z.lt_irrefl with o1.
 apply Z.lt_trans with (-2)%Z.
 assumption.
 apply Z.lt_trans with 2%Z.
 constructor.
 assumption.

 intro. 
 case (Z_lt_dec o1 (-2)).
 intro. 
 case (Z_lt_dec o2 (-2)).
 intros.
 left.
 right.
 split; repeat assumption.
 intro.
 right.
 intro.
 apply n0.
 case H.
 intros (H1, H2).
 apply False_ind.
 apply Z.lt_irrefl with o1.
 apply Z.lt_trans with (-2)%Z.
 assumption.
 apply Z.lt_trans with 2%Z.
 constructor.
 assumption.
 intros (H1, H2).
 assumption.
 
 intros.  
 right.
 intro.
 apply n0.
 case H.  
 intros (H1, H2).
 apply False_ind.
 apply n.
 assumption.
 intros (H1, H2).
 assumption.
Qed.

Lemma inside_square_2_dec_inf :
 forall o1 o2 : Z, {inside_square_2 o1 o2} + {~ inside_square_2 o1 o2}.
Proof.
 intros.
 case (Z_lt_dec 2 o1).
 intro.
 case (Z_lt_dec o2 (-2)).
 intros.
 left.
 left. 
 split; repeat assumption.
 intro.
 right. 
 intro.
 apply n.
 case H. 
 intros (H1, H2).
 assumption.
 intros (H1, H2).
 apply False_ind.
 apply Z.lt_irrefl with o1.
 apply Z.lt_trans with (-2)%Z.
 assumption.
 apply Z.lt_trans with 2%Z.
 constructor.
 assumption.

 intro. 
 case (Z_lt_dec o1 (-2)).
 intro. 
 case (Z_lt_dec 2 o2).
 intros.
 left.
 right.
 split; repeat assumption.
 intro.
 right.
 intro.
 apply n0.
 case H.
 intros (H1, H2).
 apply False_ind.
 apply Z.lt_irrefl with o1.
 apply Z.lt_trans with (-2)%Z.
 assumption.
 apply Z.lt_trans with 2%Z.
 constructor.
 assumption.
 intros (H1, H2).
 assumption.
 
 intros.  
 right.
 intro.
 apply n0.
 case H.  
 intros (H1, H2).
 apply False_ind.
 apply n.
 assumption.
 intros (H1, H2).
 assumption.
Qed.


Inductive Qquadratic_sg_denom_nonzero :
Z -> Z -> Z -> Z -> Qpositive -> Qpositive -> Prop :=
  | Qquadratic_signok0 :
      forall (e f g h : Z) (p1 p2 : Qpositive),
      p2 = One ->
      Qhomographic_sg_denom_nonzero (e + f) (g + h) p1 ->
      Qquadratic_sg_denom_nonzero e f g h p1 p2
  | Qquadratic_signok0' :
      forall (e f g h : Z) (p1 p2 : Qpositive),
      p1 = One ->
      Qhomographic_sg_denom_nonzero (e + g) (f + h) p2 ->
      Qquadratic_sg_denom_nonzero e f g h p1 p2
  | Qquadratic_signok1 :
      forall (e f g h : Z) (p1 p2 : Qpositive),
      Qquadratic_sg_denom_nonzero e (e + f)%Z (e + g)%Z 
        (e + f + g + h)%Z p1 p2 ->
      Qquadratic_sg_denom_nonzero e f g h (nR p1) (nR p2)
  | Qquadratic_signok2 :
      forall (e f g h : Z) (p1 p2 : Qpositive),
      Qquadratic_sg_denom_nonzero (e + f)%Z f (e + f + g + h)%Z 
        (f + h)%Z p1 p2 ->
      Qquadratic_sg_denom_nonzero e f g h (nR p1) (dL p2)
  | Qquadratic_signok3 :
      forall (e f g h : Z) (p1 p2 : Qpositive),
      Qquadratic_sg_denom_nonzero (e + g)%Z (e + f + g + h)%Z g 
        (g + h)%Z p1 p2 ->
      Qquadratic_sg_denom_nonzero e f g h (dL p1) (nR p2)
  | Qquadratic_signok4 :
      forall (e f g h : Z) (p1 p2 : Qpositive),
      Qquadratic_sg_denom_nonzero (e + f + g + h)%Z 
        (f + h)%Z (g + h)%Z h p1 p2 ->
      Qquadratic_sg_denom_nonzero e f g h (dL p1) (dL p2).


Lemma Qquadratic_signok_0 :
 forall (e f g h : Z) (p2 : Qpositive),
 Qquadratic_sg_denom_nonzero e f g h One p2 ->
 Qhomographic_sg_denom_nonzero (e + g) (f + h) p2.
Proof.
 intros.
 inversion H.
 inversion H1.
 apply Qhomographic_signok0.
 assumption.
 replace (e + g + (f + h))%Z with (e + f + (g + h))%Z.
 assumption.
 abstract ring.
 assumption.
Defined.

Lemma Qquadratic_signok_0' :
 forall (e f g h : Z) (p1 : Qpositive),
 Qquadratic_sg_denom_nonzero e f g h p1 One ->
 Qhomographic_sg_denom_nonzero (e + f) (g + h) p1.
Proof.
 intros.
 inversion H.
 assumption.
 inversion H1.
 apply Qhomographic_signok0.
 assumption.
 replace (e + f + (g + h))%Z with (e + g + (f + h))%Z.
 assumption.
 abstract ring.
Defined.

Lemma Qquadratic_signok_1 :
 forall (e f g h : Z) (p1 p2 : Qpositive),
 Qquadratic_sg_denom_nonzero e f g h (nR p1) (nR p2) ->
 Qquadratic_sg_denom_nonzero e (e + f) (e + g) (e + f + g + h) p1 p2.
Proof.
 intros.
 inversion H.
 discriminate H0.
 discriminate H0.
 assumption.
Defined.

Lemma Qquadratic_signok_2 :
 forall (e f g h : Z) (p1 p2 : Qpositive),
 Qquadratic_sg_denom_nonzero e f g h (nR p1) (dL p2) ->
 Qquadratic_sg_denom_nonzero (e + f) f (e + f + g + h) (f + h) p1 p2.
Proof.
 intros.
 inversion H.
 discriminate H0.
 discriminate H0.
 assumption.
Defined.

Lemma Qquadratic_signok_3 :
 forall (e f g h : Z) (p1 p2 : Qpositive),
 Qquadratic_sg_denom_nonzero e f g h (dL p1) (nR p2) ->
 Qquadratic_sg_denom_nonzero (e + g) (e + f + g + h) g (g + h) p1 p2.
Proof.
 intros.
 inversion H.
 discriminate H0.
 discriminate H0.
 assumption.
Defined.

Lemma Qquadratic_signok_4 :
 forall (e f g h : Z) (p1 p2 : Qpositive),
 Qquadratic_sg_denom_nonzero e f g h (dL p1) (dL p2) ->
 Qquadratic_sg_denom_nonzero (e + f + g + h) (f + h) (g + h) h p1 p2.
Proof.
 intros.
 inversion H.
 discriminate H0.
 discriminate H0.
 assumption.
Defined.

Fixpoint Qquadratic_sign (a b c d e f g h : Z) (p1 p2 : Qpositive) {struct p1} :
  forall (H_Qquadratic_sg_denom_nonzero : Qquadratic_sg_denom_nonzero e f g h p1 p2),
  Z * (Z * (Z * (Z * Z)) * (Z * (Z * (Z * Z))) * (Qpositive * Qpositive)).
set (o1 := outside_square a b c d) in *.
set (o2 := outside_square e f g h) in *.
destruct p1 as [xs| xs| ].
 (* p1=(nR xs) *)
 destruct p2 as [ys| ys| ]; intro H_Qquadratic_sg_denom_nonzero.
  (* p2=(nR xs) *)
  case (three_integers_dec_inf b c d).  
   (* `b = 0`/\`c = 0`/\`d = 0` *)
   intro Hbcd.
   (* Intros [Hb [Hc] Hd]. *)
   case (three_integers_dec_inf f g h).  
    (* `f = 0`/\`g = 0`/\`h = 0` *)
    intro Hfgh.
    exact
     ((Z.sgn a * Z.sgn e)%Z,
     (a, (b, (c, d)), (e, (f, (g, h))), (nR xs, nR ys))).
    (* ~(`f = 0`/\`g = 0`/\`h = 0`) *)
    case (Z_lt_dec 2 o2).
     (*  `2 < o2` *)
     intros H_o2_gt_2 Hfgh'.
     exact (Z.sgn a, (a, (b, (c, d)), (e, (f, (g, h))), (nR xs, nR ys))).
     case (Z_lt_dec o2 (-2)).
      (* `o2<(-2)` *)
      intros H_o2_lt_min_2 H_o2_gt_2' Hefg'.
      exact
       ((- Z.sgn a)%Z, (a, (b, (c, d)), (e, (f, (g, h))), (nR xs, nR ys))).
      (*    ~`o2 < (-2)` /\ ~`2 < o2`/\~(`f = 0`/\`g = 0`/\`h = 0`) *) 
      intros H_o2_lt_min_2' H_o2_gt_2' Hfgh'.
      refine
       (Qquadratic_sign a (a + b)%Z (a + c)%Z (a + b + c + d)%Z e 
          (e + f)%Z (e + g)%Z (e + f + g + h)%Z xs ys _).  
      apply Qquadratic_signok_1.
      assumption. 
   (* ~(`b = 0`/\`c = 0`/\`d = 0`) *)
   intro Hbcd'.  
   case (three_integers_dec_inf f g h).  
    (* `f = 0`/\`g = 0`/\`h = 0` *)
    intro Hfgh.
    case (Z_lt_dec 2 o1).
     (*  `2 < o1` *)
     intros H_o1_gt_2.
     exact (Z.sgn e, (a, (b, (c, d)), (e, (f, (g, h))), (nR xs, nR ys))).
     case (Z_lt_dec o1 (-2)).
      (* `o1<(-2)` *)
      intros H_o1_lt_min_2 H_o1_gt_2'.
      exact
       ((- Z.sgn e)%Z, (a, (b, (c, d)), (e, (f, (g, h))), (nR xs, nR ys))).
      (*    ~`o1 < (-2)` /\ ~`2 < o1` *)
      intros H_o1_lt_min_2' H_o1_gt_2'. 
      refine
       (Qquadratic_sign a (a + b)%Z (a + c)%Z (a + b + c + d)%Z e 
          (e + f)%Z (e + g)%Z (e + f + g + h)%Z xs ys _).  
      apply Qquadratic_signok_1.
      assumption. 
    (* ~(`f = 0`/\`g = 0`/\`h = 0`) *)
    intro Hfgh'.
    case (inside_square_1_dec_inf o1 o2).    
     (* (inside_square_1 o1 o2) *)
     intro H_inside_1.
     exact (1%Z, (a, (b, (c, d)), (e, (f, (g, h))), (nR xs, nR ys))).
     (* ~(inside_square_1 o1 o2) *)
     intro H_inside_1'.
     case (inside_square_2_dec_inf o1 o2).    
      (* (inside_square_2 o1 o2) *)
      intro H_inside_2.
      exact ((-1)%Z, (a, (b, (c, d)), (e, (f, (g, h))), (nR xs, nR ys))).
      (*  ~(inside_square_1 o1 o2)/\~(inside_square_2 o1 o2) *)
      intros H_inside_2'. 
      refine
       (Qquadratic_sign a (a + b)%Z (a + c)%Z (a + b + c + d)%Z e 
          (e + f)%Z (e + g)%Z (e + f + g + h)%Z xs ys _).  
      apply Qquadratic_signok_1.
      assumption. 
  (* p2=(dL xs) *)
  case (three_integers_dec_inf b c d).  
   (* `b = 0`/\`c = 0`/\`d = 0` *)
   intro Hbcd.
   (* Intros [Hb [Hc] Hd]. *)
   case (three_integers_dec_inf f g h).  
    (* `f = 0`/\`g = 0`/\`h = 0` *)
    intro Hfgh.
    exact
     ((Z.sgn a * Z.sgn e)%Z,
     (a, (b, (c, d)), (e, (f, (g, h))), (nR xs, dL ys))).
    (* ~(`f = 0`/\`g = 0`/\`h = 0`) *)
    case (Z_lt_dec 2 o2).
     (*  `2 < o2` *)
     intros H_o2_gt_2 Hfgh'.
     exact (Z.sgn a, (a, (b, (c, d)), (e, (f, (g, h))), (nR xs, dL ys))).
     case (Z_lt_dec o2 (-2)).
      (* `o2<(-2)` *)
      intros H_o2_lt_min_2 H_o2_gt_2' Hefg'.
      exact
       ((- Z.sgn a)%Z, (a, (b, (c, d)), (e, (f, (g, h))), (nR xs, dL ys))).
      (*    ~`o2 < (-2)` /\ ~`2 < o2`/\~(`f = 0`/\`g = 0`/\`h = 0`) *) 
      intros H_o2_lt_min_2' H_o2_gt_2' Hfgh'.
      refine
       (Qquadratic_sign (a + b)%Z b (a + b + c + d)%Z 
          (b + d)%Z (e + f)%Z f (e + f + g + h)%Z (f + h)%Z xs ys _). 
      apply Qquadratic_signok_2.
      assumption. 
   (* ~(`b = 0`/\`c = 0`/\`d = 0`) *)
   intro Hbcd'.  
   case (three_integers_dec_inf f g h).  
    (* `f = 0`/\`g = 0`/\`h = 0` *)
    intro Hfgh.
    case (Z_lt_dec 2 o1).
     (*  `2 < o1` *)
     intros H_o1_gt_2.
     exact (Z.sgn e, (a, (b, (c, d)), (e, (f, (g, h))), (nR xs, dL ys))).
     case (Z_lt_dec o1 (-2)).
      (* `o1<(-2)` *)
      intros H_o1_lt_min_2 H_o1_gt_2'.
      exact
       ((- Z.sgn e)%Z, (a, (b, (c, d)), (e, (f, (g, h))), (nR xs, dL ys))).
      (*    ~`o1 < (-2)` /\ ~`2 < o1` *)
      intros H_o1_lt_min_2' H_o1_gt_2'. 
      refine
       (Qquadratic_sign (a + b)%Z b (a + b + c + d)%Z 
          (b + d)%Z (e + f)%Z f (e + f + g + h)%Z (f + h)%Z xs ys _). 
      apply Qquadratic_signok_2.
      assumption. 
    (* ~(`f = 0`/\`g = 0`/\`h = 0`) *)
    intro Hfgh'.
    case (inside_square_1_dec_inf o1 o2).    
     (* (inside_square_1 o1 o2) *)
     intro H_inside_1.
     exact (1%Z, (a, (b, (c, d)), (e, (f, (g, h))), (nR xs, dL ys))).
     (* ~(inside_square_1 o1 o2) *)
     intro H_inside_1'.
     case (inside_square_2_dec_inf o1 o2).    
      (* (inside_square_2 o1 o2) *)
      intro H_inside_2.
      exact ((-1)%Z, (a, (b, (c, d)), (e, (f, (g, h))), (nR xs, dL ys))).
      (*  ~(inside_square_1 o1 o2)/\~(inside_square_2 o1 o2) *)
      intros H_inside_2'. 
      refine
       (Qquadratic_sign (a + b)%Z b (a + b + c + d)%Z 
          (b + d)%Z (e + f)%Z f (e + f + g + h)%Z (f + h)%Z xs ys _). 
      apply Qquadratic_signok_2.
      assumption.    
  (* p2=One *)
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
  exact (l1, (0%Z, (na, (0%Z, nb)), (0%Z, (nc, (0%Z, nd))), (l3, One))).

 (* p1=(dL xs) *)
 destruct p2 as [ys| ys| ]; intro H_Qquadratic_sg_denom_nonzero.
  (* p2=(nR xs) *)
  case (three_integers_dec_inf b c d).  
   (* `b = 0`/\`c = 0`/\`d = 0` *)
   intro Hbcd.
   (* Intros [Hb [Hc] Hd]. *)
   case (three_integers_dec_inf f g h).  
    (* `f = 0`/\`g = 0`/\`h = 0` *)
    intro Hfgh.
    exact
     ((Z.sgn a * Z.sgn e)%Z,
     (a, (b, (c, d)), (e, (f, (g, h))), (dL xs, nR ys))).
    (* ~(`f = 0`/\`g = 0`/\`h = 0`) *)
    case (Z_lt_dec 2 o2).
     (*  `2 < o2` *)
     intros H_o2_gt_2 Hfgh'.
     exact (Z.sgn a, (a, (b, (c, d)), (e, (f, (g, h))), (dL xs, nR ys))).
     case (Z_lt_dec o2 (-2)).
      (* `o2<(-2)` *)
      intros H_o2_lt_min_2 H_o2_gt_2' Hefg'.
      exact
       ((- Z.sgn a)%Z, (a, (b, (c, d)), (e, (f, (g, h))), (dL xs, nR ys))).
      (*    ~`o2 < (-2)` /\ ~`2 < o2`/\~(`f = 0`/\`g = 0`/\`h = 0`) *) 
      intros H_o2_lt_min_2' H_o2_gt_2' Hfgh'.
      refine
       (Qquadratic_sign (a + c)%Z (a + b + c + d)%Z c 
          (c + d)%Z (e + g)%Z (e + f + g + h)%Z g (g + h)%Z xs ys _). 
      apply Qquadratic_signok_3.
      assumption. 
   (* ~(`b = 0`/\`c = 0`/\`d = 0`) *)
   intro Hbcd'.  
   case (three_integers_dec_inf f g h).  
    (* `f = 0`/\`g = 0`/\`h = 0` *)
    intro Hfgh.
    case (Z_lt_dec 2 o1).
     (*  `2 < o1` *)
     intros H_o1_gt_2.
     exact (Z.sgn e, (a, (b, (c, d)), (e, (f, (g, h))), (dL xs, nR ys))).
     case (Z_lt_dec o1 (-2)).
      (* `o1<(-2)` *)
      intros H_o1_lt_min_2 H_o1_gt_2'.
      exact
       ((- Z.sgn e)%Z, (a, (b, (c, d)), (e, (f, (g, h))), (dL xs, nR ys))).
      (*    ~`o1 < (-2)` /\ ~`2 < o1` *)
      intros H_o1_lt_min_2' H_o1_gt_2'. 
      refine
       (Qquadratic_sign (a + c)%Z (a + b + c + d)%Z c 
          (c + d)%Z (e + g)%Z (e + f + g + h)%Z g (g + h)%Z xs ys _). 
      apply Qquadratic_signok_3.
      assumption. 
    (* ~(`f = 0`/\`g = 0`/\`h = 0`) *)
    intro Hfgh'.
    case (inside_square_1_dec_inf o1 o2).    
     (* (inside_square_1 o1 o2) *)
     intro H_inside_1.
     exact (1%Z, (a, (b, (c, d)), (e, (f, (g, h))), (dL xs, nR ys))).
     (* ~(inside_square_1 o1 o2) *)
     intro H_inside_1'.
     case (inside_square_2_dec_inf o1 o2).    
      (* (inside_square_2 o1 o2) *)
      intro H_inside_2.
      exact ((-1)%Z, (a, (b, (c, d)), (e, (f, (g, h))), (dL xs, nR ys))).
      (*  ~(inside_square_1 o1 o2)/\~(inside_square_2 o1 o2) *)
      intros H_inside_2'.
      refine
       (Qquadratic_sign (a + c)%Z (a + b + c + d)%Z c 
          (c + d)%Z (e + g)%Z (e + f + g + h)%Z g (g + h)%Z xs ys _). 
      apply Qquadratic_signok_3.
      assumption. 
  (* p2=(dL xs) *)
  case (three_integers_dec_inf b c d).  
   (* `b = 0`/\`c = 0`/\`d = 0` *)
   intro Hbcd.
   (* Intros [Hb [Hc] Hd]. *)
   case (three_integers_dec_inf f g h).  
    (* `f = 0`/\`g = 0`/\`h = 0` *)
    intro Hfgh.
    exact
     ((Z.sgn a * Z.sgn e)%Z,
     (a, (b, (c, d)), (e, (f, (g, h))), (dL xs, dL ys))).
    (* ~(`f = 0`/\`g = 0`/\`h = 0`) *)
    case (Z_lt_dec 2 o2).
     (*  `2 < o2` *)
     intros H_o2_gt_2 Hfgh'.
     exact (Z.sgn a, (a, (b, (c, d)), (e, (f, (g, h))), (dL xs, dL ys))).
     case (Z_lt_dec o2 (-2)).
      (* `o2<(-2) ` *)
      intros H_o2_lt_min_2 H_o2_gt_2' Hefg'.
      exact
       ((- Z.sgn a)%Z, (a, (b, (c, d)), (e, (f, (g, h))), (dL xs, dL ys))).
      (*    ~`o2 < (-2)` /\ ~`2 < o2`/\~(`f = 0`/\`g = 0`/\`h = 0`) *) 
      intros H_o2_lt_min_2' H_o2_gt_2' Hfgh'.
      refine
       (Qquadratic_sign (a + b + c + d)%Z (b + d)%Z 
          (c + d)%Z d (e + f + g + h)%Z (f + h)%Z (g + h)%Z h xs ys _). 
      apply Qquadratic_signok_4.
      assumption. 
   (* ~(`b = 0`/\`c = 0`/\`d = 0`) *)
   intro Hbcd'.  
   case (three_integers_dec_inf f g h).  
    (* `f = 0`/\`g = 0`/\`h = 0` *)
    intro Hfgh.
    case (Z_lt_dec 2 o1).
     (*  `2 < o1` *)
     intros H_o1_gt_2.
     exact (Z.sgn e, (a, (b, (c, d)), (e, (f, (g, h))), (dL xs, dL ys))).
     case (Z_lt_dec o1 (-2)).
      (* `o1<(-2)` *)
      intros H_o1_lt_min_2 H_o1_gt_2'.
      exact
       ((- Z.sgn e)%Z, (a, (b, (c, d)), (e, (f, (g, h))), (dL xs, dL ys))).
      (*    ~`o1 < (-2)` /\ ~`2 < o1` *)
      intros H_o1_lt_min_2' H_o1_gt_2'. 
      refine
       (Qquadratic_sign (a + b + c + d)%Z (b + d)%Z 
          (c + d)%Z d (e + f + g + h)%Z (f + h)%Z (g + h)%Z h xs ys _). 
      apply Qquadratic_signok_4.
      assumption. 
    (* ~(`f = 0`/\`g = 0`/\`h = 0`) *)
    intro Hfgh'.
    case (inside_square_1_dec_inf o1 o2).    
     (* (inside_square_1 o1 o2) *)
     intro H_inside_1.
     exact (1%Z, (a, (b, (c, d)), (e, (f, (g, h))), (dL xs, dL ys))).
     (* ~(inside_square_1 o1 o2) *)
     intro H_inside_1'.
     case (inside_square_2_dec_inf o1 o2).    
      (* (inside_square_2 o1 o2) *)
      intro H_inside_2.
      exact ((-1)%Z, (a, (b, (c, d)), (e, (f, (g, h))), (dL xs, dL ys))).
      (*  ~(inside_square_1 o1 o2)/\~(inside_square_2 o1 o2) *)
      intros H_inside_2'. 
      refine
       (Qquadratic_sign (a + b + c + d)%Z (b + d)%Z 
          (c + d)%Z d (e + f + g + h)%Z (f + h)%Z (g + h)%Z h xs ys _). 
      apply Qquadratic_signok_4.
      assumption.    
  (* p2=One *)
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
  exact (l1, (0%Z, (na, (0%Z, nb)), (0%Z, (nc, (0%Z, nd))), (l3, One))).
 
 (* p1=One  *)
 intros H_Qquadratic_sg_denom_nonzero.
 generalize (Qquadratic_signok_0 _ _ _ _ _ H_Qquadratic_sg_denom_nonzero).
 intros H_Qhomographic_sg_denom_nonzero.
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
 exact (l1, (0%Z, (0%Z, (na, nb)), (0%Z, (0%Z, (nc, nd))), (One, l3))).
Defined.

Scheme Qquadratic_sg_denom_nonzero_inv_dep :=
  Induction for Qquadratic_sg_denom_nonzero Sort Prop.

(** We prove the Proof Irrelevace for Qquadratic_sg_denom_nonzero*)

Lemma Qquadratic_sign_equal :
 forall (a b c d e f g h : Z) (p1 p2 : Qpositive)
   (H1 H2 : Qquadratic_sg_denom_nonzero e f g h p1 p2),
 Qquadratic_sign a b c d e f g h p1 p2 H1 =
 Qquadratic_sign a b c d e f g h p1 p2 H2.
Proof.
 intros.
 generalize H2 H1 a b c d.
 intro.
 elim H0 using Qquadratic_sg_denom_nonzero_inv_dep.

 (* First big subgoal  Qquadratic_signok0 *)
  intros.
  destruct p3 as [p| p| ]; rename q into s.
  (* p3 = (nR p) *)
  discriminate e1.
  (* p3 = (dL p) *)
  discriminate e1.
  (* p3 = One *)
  destruct p0 as [p| p| ].
  (* p0 = (nR p) *)
  unfold Qquadratic_sign in |- *.
  assert
   (Qhomographic_sign (a0 + b0) (c0 + d0) (e0 + f0) 
      (g0 + h0) (nR p) (Qquadratic_signok_0' e0 f0 g0 h0 (nR p) H3) =
    Qhomographic_sign (a0 + b0) (c0 + d0) (e0 + f0) 
      (g0 + h0) (nR p)
      (Qquadratic_signok_0' e0 f0 g0 h0 (nR p)
         (Qquadratic_signok0 e0 f0 g0 h0 (nR p) One e1 s))).
  apply Qhomographic_sign_equal.
  rewrite H.
  reflexivity.
  (* p0 = (dL p) *)
  unfold Qquadratic_sign in |- *.
  assert
   (Qhomographic_sign (a0 + b0) (c0 + d0) (e0 + f0) 
      (g0 + h0) (dL p) (Qquadratic_signok_0' e0 f0 g0 h0 (dL p) H3) =
    Qhomographic_sign (a0 + b0) (c0 + d0) (e0 + f0) 
      (g0 + h0) (dL p)
      (Qquadratic_signok_0' e0 f0 g0 h0 (dL p)
         (Qquadratic_signok0 e0 f0 g0 h0 (dL p) One e1 s))).
  apply Qhomographic_sign_equal.
  rewrite H.
  reflexivity.
  (* p3 = One *)
  reflexivity.

 (* Second big subgoal Qquadratic_signok0' *)
  intros.
  destruct p0 as [p| p| ]; rename q into s.
  (* p0 = (nR p) *)
  discriminate e1.
  (* p0 = (dL p) *)
  discriminate e1.
  (* p0 = One *)
  simpl in |- *.
  assert
   (Qhomographic_sign (a0 + c0) (b0 + d0) (e0 + g0) 
      (f0 + h0) p3 (Qquadratic_signok_0 e0 f0 g0 h0 p3 H3) =
    Qhomographic_sign (a0 + c0) (b0 + d0) (e0 + g0) (f0 + h0) p3 s).
  apply Qhomographic_sign_equal.
  rewrite H.
  reflexivity.

  (* Third big subgoal Qquadratic_signok1 *)
  intros.
  simpl in |- *.
  rewrite H.
  reflexivity.
  (* Fourth big subgoal Qquadratic_signok2 *)
  intros.
  simpl in |- *.
  rewrite H.
  reflexivity.
  (* Fifth big subgoal Qquadratic_signok3 *)
  intros.
  simpl in |- *.
  rewrite H.
  reflexivity.
  (* Sixth  big subgoal Qquadratic_signok4 *)
  intros.
  simpl in |- *.
  rewrite H.
  reflexivity.
Qed.

Lemma Qquadratic_sign_equal_strong :
 forall (a1 a2 b1 b2 c1 c2 d1 d2 e1 e2 f1 f2 g1 g2 h1 h2 : Z)
   (x1 x2 y1 y2 : Qpositive)
   (H_ok_1 : Qquadratic_sg_denom_nonzero e1 f1 g1 h1 x1 y1)
   (H_ok_2 : Qquadratic_sg_denom_nonzero e2 f2 g2 h2 x2 y2),
 a1 = a2 ->
 b1 = b2 ->
 c1 = c2 ->
 d1 = d2 ->
 e1 = e2 ->
 f1 = f2 ->
 g1 = g2 ->
 h1 = h2 ->
 x1 = x2 ->
 y1 = y2 ->
 Qquadratic_sign a1 b1 c1 d1 e1 f1 g1 h1 x1 y1 H_ok_1 =
 Qquadratic_sign a2 b2 c2 d2 e2 f2 g2 h2 x2 y2 H_ok_2.
Proof.
 intros; generalize H_ok_2;
  repeat
   match goal with
   | id1:(?X1 = ?X2) |- ?X3 => rewrite <- id1; clear id1
   end; intro; apply Qquadratic_sign_equal.
Qed.


Lemma Qquadratic_sign_One_y :
 forall (a b c d e f g h : Z) (p1 p2 : Qpositive)
   (H_Qquadratic_sg_denom_nonzero : Qquadratic_sg_denom_nonzero e f g h p1 p2)
   (l1 na nb nc nd : Z) (l3 : Qpositive)
   (H_Qhomographic_sg_denom_nonzero : Qhomographic_sg_denom_nonzero 
                                        (e + g) (f + h) p2),
 (l1, (na, (nb, (nc, nd)), l3)) =
 Qhomographic_sign (a + c) (b + d) (e + g) (f + h) p2
   H_Qhomographic_sg_denom_nonzero ->
 p1 = One ->
 Qquadratic_sign a b c d e f g h p1 p2 H_Qquadratic_sg_denom_nonzero =
 (l1, (0%Z, (0%Z, (na, nb)), (0%Z, (0%Z, (nc, nd))), (One, l3))).
Proof.
 intros.
 destruct p1 as [q| q| ]; repeat (apply False_ind; discriminate H0).
 simpl in |- *.
 rewrite
  Qhomographic_sign_equal
                          with
                          (H1 := 
                            Qquadratic_signok_0 e f g h p2
                              H_Qquadratic_sg_denom_nonzero)
                         (H2 := H_Qhomographic_sg_denom_nonzero).
 rewrite <- H.
 reflexivity.
Qed.


Lemma Qquadratic_sign_nRdL_One :
 forall (a b c d e f g h : Z) (p1 p2 : Qpositive)
   (H_Qquadratic_sg_denom_nonzero : Qquadratic_sg_denom_nonzero e f g h p1 p2)
   (l1 na nb nc nd : Z) (l3 : Qpositive)
   (H_Qhomographic_sg_denom_nonzero : Qhomographic_sg_denom_nonzero 
                                        (e + f) (g + h) p1),
 (l1, (na, (nb, (nc, nd)), l3)) =
 Qhomographic_sign (a + b) (c + d) (e + f) (g + h) p1
   H_Qhomographic_sg_denom_nonzero ->
 p1 <> One ->
 p2 = One ->
 Qquadratic_sign a b c d e f g h p1 p2 H_Qquadratic_sg_denom_nonzero =
 (l1, (0%Z, (na, (0%Z, nb)), (0%Z, (nc, (0%Z, nd))), (l3, One))).
Proof.
 intros.
 destruct p2 as [q| q| ]; repeat (apply False_ind; discriminate H1).
 destruct p1 as [p| p| ].
 unfold Qquadratic_sign in |- *.
 rewrite
  Qhomographic_sign_equal
                          with
                          (H1 := 
                            Qquadratic_signok_0' e f g h 
                              (nR p) H_Qquadratic_sg_denom_nonzero)
                         (H2 := H_Qhomographic_sg_denom_nonzero).
 rewrite <- H.
 reflexivity.

 unfold Qquadratic_sign in |- *. 
 rewrite
  Qhomographic_sign_equal
                          with
                          (H1 := 
                            Qquadratic_signok_0' e f g h 
                              (dL p) H_Qquadratic_sg_denom_nonzero)
                         (H2 := H_Qhomographic_sg_denom_nonzero).
 rewrite <- H.
 reflexivity.
 Falsum.
Qed.  

Lemma Qquadratic_sign_nR_One_1 :
 forall (a b c d e f g h : Z) (p1 xs p2 : Qpositive)
   (H_Qquadratic_sg_denom_nonzero : Qquadratic_sg_denom_nonzero e f g h p1 p2)
   (l1 na nb nc nd : Z) (l3 : Qpositive)
   (H_Qhomographic_sg_denom_nonzero : Qhomographic_sg_denom_nonzero 
                                        (e + f) (g + h) p1),
 (l1, (na, (nb, (nc, nd)), l3)) =
 Qhomographic_sign (a + b) (c + d) (e + f) (g + h) p1
   H_Qhomographic_sg_denom_nonzero ->
 p1 = nR xs ->
 p2 = One ->
 Qquadratic_sign a b c d e f g h p1 p2 H_Qquadratic_sg_denom_nonzero =
 (l1, (0%Z, (na, (0%Z, nb)), (0%Z, (nc, (0%Z, nd))), (l3, One))).
Proof.
 intros.
 generalize H_Qquadratic_sg_denom_nonzero H_Qhomographic_sg_denom_nonzero H.
 rewrite H0.
 intros.
 destruct p2 as [q| q| ]; repeat (apply False_ind; discriminate H1).

 unfold Qquadratic_sign in |- *.
 rewrite
  Qhomographic_sign_equal
                          with
                          (H1 := 
                            Qquadratic_signok_0' e f g h 
                              (nR xs) H_Qquadratic_sg_denom_nonzero0)
                         (H2 := H_Qhomographic_sg_denom_nonzero0).
 rewrite <- H2.
 reflexivity.
Qed.  

Lemma Qquadratic_sign_nR_One_2 :
 forall (a b c d e f g h : Z) (p1 p2 : Qpositive)
   (H_Qquadratic_sg_denom_nonzero : Qquadratic_sg_denom_nonzero e f g h
                                      (nR p1) p2) (l1 na nb nc nd : Z)
   (l3 : Qpositive)
   (H_Qhomographic_sg_denom_nonzero : Qhomographic_sg_denom_nonzero 
                                        (e + f) (g + h) 
                                        (nR p1)),
 (l1, (na, (nb, (nc, nd)), l3)) =
 Qhomographic_sign (a + b) (c + d) (e + f) (g + h) 
   (nR p1) H_Qhomographic_sg_denom_nonzero ->
 p2 = One ->
 Qquadratic_sign a b c d e f g h (nR p1) p2 H_Qquadratic_sg_denom_nonzero =
 (l1, (0%Z, (na, (0%Z, nb)), (0%Z, (nc, (0%Z, nd))), (l3, One))).
Proof.
 intros.
 destruct p2 as [q| q| ]; repeat (apply False_ind; discriminate H0).

 unfold Qquadratic_sign in |- *.
 rewrite
  Qhomographic_sign_equal
                          with
                          (H1 := 
                            Qquadratic_signok_0' e f g h 
                              (nR p1) H_Qquadratic_sg_denom_nonzero)
                         (H2 := H_Qhomographic_sg_denom_nonzero).
 rewrite <- H.
 reflexivity.
Qed.  

Lemma Qquadratic_sign_dL_One_1 :
 forall (a b c d e f g h : Z) (p1 xs p2 : Qpositive)
   (H_Qquadratic_sg_denom_nonzero : Qquadratic_sg_denom_nonzero e f g h p1 p2)
   (l1 na nb nc nd : Z) (l3 : Qpositive)
   (H_Qhomographic_sg_denom_nonzero : Qhomographic_sg_denom_nonzero 
                                        (e + f) (g + h) p1),
 (l1, (na, (nb, (nc, nd)), l3)) =
 Qhomographic_sign (a + b) (c + d) (e + f) (g + h) p1
   H_Qhomographic_sg_denom_nonzero ->
 p1 = dL xs ->
 p2 = One ->
 Qquadratic_sign a b c d e f g h p1 p2 H_Qquadratic_sg_denom_nonzero =
 (l1, (0%Z, (na, (0%Z, nb)), (0%Z, (nc, (0%Z, nd))), (l3, One))).
Proof.
 intros.
 generalize H_Qquadratic_sg_denom_nonzero H_Qhomographic_sg_denom_nonzero H.
 rewrite H0.
 intros.
 destruct p2 as [q| q| ]; repeat (apply False_ind; discriminate H1).

 unfold Qquadratic_sign in |- *.
 rewrite
  Qhomographic_sign_equal
                          with
                          (H1 := 
                            Qquadratic_signok_0' e f g h 
                              (dL xs) H_Qquadratic_sg_denom_nonzero0)
                         (H2 := H_Qhomographic_sg_denom_nonzero0).
 rewrite <- H2.
 reflexivity.
Qed.  

Lemma Qquadratic_sign_dL_One_2 :
 forall (a b c d e f g h : Z) (p1 p2 : Qpositive)
   (H_Qquadratic_sg_denom_nonzero : Qquadratic_sg_denom_nonzero e f g h
                                      (dL p1) p2) (l1 na nb nc nd : Z)
   (l3 : Qpositive)
   (H_Qhomographic_sg_denom_nonzero : Qhomographic_sg_denom_nonzero 
                                        (e + f) (g + h) 
                                        (dL p1)),
 (l1, (na, (nb, (nc, nd)), l3)) =
 Qhomographic_sign (a + b) (c + d) (e + f) (g + h) 
   (dL p1) H_Qhomographic_sg_denom_nonzero ->
 p2 = One ->
 Qquadratic_sign a b c d e f g h (dL p1) p2 H_Qquadratic_sg_denom_nonzero =
 (l1, (0%Z, (na, (0%Z, nb)), (0%Z, (nc, (0%Z, nd))), (l3, One))).
Proof.
 intros.
 destruct p2 as [q| q| ]; repeat (apply False_ind; discriminate H0).

 unfold Qquadratic_sign in |- *.
 rewrite
  Qhomographic_sign_equal
                          with
                          (H1 := 
                            Qquadratic_signok_0' e f g h 
                              (dL p1) H_Qquadratic_sg_denom_nonzero)
                         (H2 := H_Qhomographic_sg_denom_nonzero).
 rewrite <- H.
 reflexivity.
Qed.  

Lemma Qquadratic_sign_nRdL_nRdL_1 :
 forall (a b c d e f g h : Z) (p1 p2 : Qpositive)
   (H_Qquadratic_sg_denom_nonzero : Qquadratic_sg_denom_nonzero e f g h p1 p2),
 p1 <> One ->
 p2 <> One ->
 b = 0%Z /\ c = 0%Z /\ d = 0%Z ->
 f = 0%Z /\ g = 0%Z /\ h = 0%Z ->
 Qquadratic_sign a b c d e f g h p1 p2 H_Qquadratic_sg_denom_nonzero =
 ((Z.sgn a * Z.sgn e)%Z, (a, (b, (c, d)), (e, (f, (g, h))), (p1, p2))).
Proof.
 intros.
 destruct p1 as [q| q| ];
  solve [ Falsum ] ||
    let T_local :=
     (simpl in |- *; case (three_integers_dec_inf b c d);
       [ intro; case (three_integers_dec_inf f g h);
          [ intro; reflexivity | intro H3; Falsum ]
       | intro H3; Falsum ]) in
    (destruct p2 as [q0| q0| ]; [ T_local | T_local | Falsum ]).
Qed. 

Lemma Qquadratic_sign_nRdL_nRdL_2 :
 forall (a b c d e f g h : Z) (p1 p2 : Qpositive)
   (H_Qquadratic_sg_denom_nonzero : Qquadratic_sg_denom_nonzero e f g h p1 p2),
 p1 <> One ->
 p2 <> One ->
 b = 0%Z /\ c = 0%Z /\ d = 0%Z ->
 ~ (f = 0%Z /\ g = 0%Z /\ h = 0%Z) ->
 (2 < outside_square e f g h)%Z ->
 Qquadratic_sign a b c d e f g h p1 p2 H_Qquadratic_sg_denom_nonzero =
 (Z.sgn a, (a, (b, (c, d)), (e, (f, (g, h))), (p1, p2))).             
Proof.
 intros.
 destruct p1 as [q| q| ];
  solve [ Falsum ] ||
    let T_local :=
     (simpl in |- *; case (three_integers_dec_inf b c d);
       [ intro; case (three_integers_dec_inf f g h);
          [ intro H4; Falsum
          | case (Z_lt_dec 2 (outside_square e f g h));
             [ intro; reflexivity | intro H4; Falsum ] ]
       | intro H4; Falsum ]) in
    (destruct p2 as [q0| q0| ]; [ T_local | T_local | Falsum ]).
Qed.


Lemma Qquadratic_sign_nRdL_nRdL_3 :
 forall (a b c d e f g h : Z) (p1 p2 : Qpositive)
   (H_Qquadratic_sg_denom_nonzero : Qquadratic_sg_denom_nonzero e f g h p1 p2),
 p1 <> One ->
 p2 <> One ->
 b = 0%Z /\ c = 0%Z /\ d = 0%Z ->
 ~ (f = 0%Z /\ g = 0%Z /\ h = 0%Z) ->
 ~ (2 < outside_square e f g h)%Z ->
 (outside_square e f g h < -2)%Z ->
 Qquadratic_sign a b c d e f g h p1 p2 H_Qquadratic_sg_denom_nonzero =
 ((- Z.sgn a)%Z, (a, (b, (c, d)), (e, (f, (g, h))), (p1, p2))).             
Proof.
 intros.
 destruct p1 as [q| q| ];
  solve [ Falsum ] ||
    let T_local :=
     (simpl in |- *; case (three_integers_dec_inf b c d);
       [ intro; case (three_integers_dec_inf f g h);
          [ intro H5; Falsum
          | intro n; case (Z_lt_dec 2 (outside_square e f g h));
             [ intro H5; Falsum
             | intro n0; case (Z_lt_dec (outside_square e f g h) (-2));
                [ intro; reflexivity | intro H5; Falsum ] ] ]
       | intro H5; Falsum ]) in
    (destruct p2 as [q0| q0| ]; [ T_local | T_local | Falsum ]).
Qed.


Lemma Qquadratic_sign_nR_nR_4 :
 forall (a b c d e f g h : Z) (p1 xs p2 ys : Qpositive)
   (H_Qquadratic_sg_denom_nonzero : Qquadratic_sg_denom_nonzero e f g h p1 p2)
   (H_Qquadratic_sg_denom_nonzero_II : Qquadratic_sg_denom_nonzero e 
                                         (e + f) (e + g) 
                                         (e + f + g + h) xs ys),
 p1 = nR xs ->
 p2 = nR ys ->
 b = 0%Z /\ c = 0%Z /\ d = 0%Z ->
 ~ (f = 0%Z /\ g = 0%Z /\ h = 0%Z) ->
 ~ (2 < outside_square e f g h)%Z ->
 ~ (outside_square e f g h < -2)%Z ->
 Qquadratic_sign a b c d e f g h p1 p2 H_Qquadratic_sg_denom_nonzero =
 Qquadratic_sign a (a + b) (a + c) (a + b + c + d) e 
   (e + f) (e + g) (e + f + g + h) xs ys H_Qquadratic_sg_denom_nonzero_II.
Proof.
 intros.
 generalize H_Qquadratic_sg_denom_nonzero H_Qquadratic_sg_denom_nonzero_II.
 rewrite H.
 rewrite H0.
 intros.

 simpl in |- *.
 case (three_integers_dec_inf b c d).
  intro.
  case (three_integers_dec_inf f g h).
   intro H5.
   Falsum.
   intro n.
   case (Z_lt_dec 2 (outside_square e f g h)).
    intro H5.
    Falsum.
    intro n0.
    case (Z_lt_dec (outside_square e f g h) (-2)).
       intro H5.
       Falsum.
       intro n1.
       apply Qquadratic_sign_equal.
  intro H5.
  Falsum.
Qed.

Lemma Qquadratic_sign_nR_dL_4 :
 forall (a b c d e f g h : Z) (p1 xs p2 ys : Qpositive)
   (H_Qquadratic_sg_denom_nonzero : Qquadratic_sg_denom_nonzero e f g h p1 p2)
   (H_Qquadratic_sg_denom_nonzero_IO : Qquadratic_sg_denom_nonzero 
                                         (e + f) f 
                                         (e + f + g + h) 
                                         (f + h) xs ys),
 p1 = nR xs ->
 p2 = dL ys ->
 b = 0%Z /\ c = 0%Z /\ d = 0%Z ->
 ~ (f = 0%Z /\ g = 0%Z /\ h = 0%Z) ->
 ~ (2 < outside_square e f g h)%Z ->
 ~ (outside_square e f g h < -2)%Z ->
 Qquadratic_sign a b c d e f g h p1 p2 H_Qquadratic_sg_denom_nonzero =
 Qquadratic_sign (a + b) b (a + b + c + d) (b + d) 
   (e + f) f (e + f + g + h) (f + h) xs ys H_Qquadratic_sg_denom_nonzero_IO.
Proof.
 intros.
 generalize H_Qquadratic_sg_denom_nonzero H_Qquadratic_sg_denom_nonzero_IO.
 rewrite H.
 rewrite H0.
 intros.

 simpl in |- *.
 case (three_integers_dec_inf b c d).
  intro.
  case (three_integers_dec_inf f g h).
   intro H5.
   Falsum.
   intro n.
   case (Z_lt_dec 2 (outside_square e f g h)).
    intro H5.
    Falsum.
    intro n0.
    case (Z_lt_dec (outside_square e f g h) (-2)).
       intro H5.
       Falsum.
       intro n1.
       apply Qquadratic_sign_equal.
  intro H5.
  Falsum.
Qed.


Lemma Qquadratic_sign_dL_nR_4 :
 forall (a b c d e f g h : Z) (p1 xs p2 ys : Qpositive)
   (H_Qquadratic_sg_denom_nonzero : Qquadratic_sg_denom_nonzero e f g h p1 p2)
   (H_Qquadratic_sg_denom_nonzero_OI : Qquadratic_sg_denom_nonzero 
                                         (e + g) (e + f + g + h) g 
                                         (g + h) xs ys),
 p1 = dL xs ->
 p2 = nR ys ->
 b = 0%Z /\ c = 0%Z /\ d = 0%Z ->
 ~ (f = 0%Z /\ g = 0%Z /\ h = 0%Z) ->
 ~ (2 < outside_square e f g h)%Z ->
 ~ (outside_square e f g h < -2)%Z ->
 Qquadratic_sign a b c d e f g h p1 p2 H_Qquadratic_sg_denom_nonzero =
 Qquadratic_sign (a + c) (a + b + c + d) c (c + d) 
   (e + g) (e + f + g + h) g (g + h) xs ys H_Qquadratic_sg_denom_nonzero_OI.
Proof.
 intros.
 generalize H_Qquadratic_sg_denom_nonzero H_Qquadratic_sg_denom_nonzero_OI.
 rewrite H.
 rewrite H0.
 intros.

 simpl in |- *.
 case (three_integers_dec_inf b c d).
  intro.
  case (three_integers_dec_inf f g h).
   intro H5.
   Falsum.
   intro n.
   case (Z_lt_dec 2 (outside_square e f g h)).
    intro H5.
    Falsum.
    intro n0.
    case (Z_lt_dec (outside_square e f g h) (-2)).
       intro H5.
       Falsum.
       intro n1.
       apply Qquadratic_sign_equal.
  intro H5.
  Falsum.
Qed.

Lemma Qquadratic_sign_dL_dL_4 :
 forall (a b c d e f g h : Z) (p1 xs p2 ys : Qpositive)
   (H_Qquadratic_sg_denom_nonzero : Qquadratic_sg_denom_nonzero e f g h p1 p2)
   (H_Qquadratic_sg_denom_nonzero_OO : Qquadratic_sg_denom_nonzero
                                         (e + f + g + h) 
                                         (f + h) (g + h) h xs ys),
 p1 = dL xs ->
 p2 = dL ys ->
 b = 0%Z /\ c = 0%Z /\ d = 0%Z ->
 ~ (f = 0%Z /\ g = 0%Z /\ h = 0%Z) ->
 ~ (2 < outside_square e f g h)%Z ->
 ~ (outside_square e f g h < -2)%Z ->
 Qquadratic_sign a b c d e f g h p1 p2 H_Qquadratic_sg_denom_nonzero =
 Qquadratic_sign (a + b + c + d) (b + d) (c + d) d 
   (e + f + g + h) (f + h) (g + h) h xs ys H_Qquadratic_sg_denom_nonzero_OO.
Proof.
 intros.
 generalize H_Qquadratic_sg_denom_nonzero H_Qquadratic_sg_denom_nonzero_OO.
 rewrite H.
 rewrite H0.
 intros.

 simpl in |- *.
 case (three_integers_dec_inf b c d).
  intro.
  case (three_integers_dec_inf f g h).
   intro H5.
   Falsum.
   intro n.
   case (Z_lt_dec 2 (outside_square e f g h)).
    intro H5.
    Falsum.
    intro n0.
    case (Z_lt_dec (outside_square e f g h) (-2)).
       intro H5.
       Falsum.
       intro n1.
       apply Qquadratic_sign_equal.
  intro H5.
  Falsum.
Qed.

Lemma Qquadratic_sign_nRdL_nRdL_5 :
 forall (a b c d e f g h : Z) (p1 p2 : Qpositive)
   (H_Qquadratic_sg_denom_nonzero : Qquadratic_sg_denom_nonzero e f g h p1 p2),
 p1 <> One ->
 p2 <> One ->
 ~ (b = 0%Z /\ c = 0%Z /\ d = 0%Z) ->
 f = 0%Z /\ g = 0%Z /\ h = 0%Z ->
 (2 < outside_square a b c d)%Z ->
 Qquadratic_sign a b c d e f g h p1 p2 H_Qquadratic_sg_denom_nonzero =
 (Z.sgn e, (a, (b, (c, d)), (e, (f, (g, h))), (p1, p2))).
Proof.
 intros.
 destruct p1 as [q| q| ];
  solve [ Falsum ] ||
    let T_local :=
     (simpl in |- *; case (three_integers_dec_inf b c d); intro Hbcd;
       [ Falsum
       | case (three_integers_dec_inf f g h); intro Hfgh;
          [ case (Z_lt_dec 2 (outside_square a b c d)); intro Ho1;
             [ reflexivity | Falsum ]
          | Falsum ] ]) in
    (destruct p2 as [q0| q0| ]; [ T_local | T_local | Falsum ]).
Qed.

Lemma Qquadratic_sign_nRdL_nRdL_6 :
 forall (a b c d e f g h : Z) (p1 p2 : Qpositive)
   (H_Qquadratic_sg_denom_nonzero : Qquadratic_sg_denom_nonzero e f g h p1 p2),
 p1 <> One ->
 p2 <> One ->
 ~ (b = 0%Z /\ c = 0%Z /\ d = 0%Z) ->
 f = 0%Z /\ g = 0%Z /\ h = 0%Z ->
 ~ (2 < outside_square a b c d)%Z ->
 (outside_square a b c d < -2)%Z ->
 Qquadratic_sign a b c d e f g h p1 p2 H_Qquadratic_sg_denom_nonzero =
 ((- Z.sgn e)%Z, (a, (b, (c, d)), (e, (f, (g, h))), (p1, p2))).
Proof.
 intros.
 destruct p1 as [q| q| ];
  solve [ Falsum ] ||
    let T_local :=
     (simpl in |- *; case (three_integers_dec_inf b c d); intro Hbcd;
       [ Falsum
       | case (three_integers_dec_inf f g h); intro Hfgh;
          [ case (Z_lt_dec 2 (outside_square a b c d)); intro Ho1;
             [ Falsum
             | case (Z_lt_dec (outside_square a b c d) (-2)); intro Ho1';
                [ reflexivity | Falsum ] ]
          | Falsum ] ]) in
    (destruct p2 as [q0| q0| ]; [ T_local | T_local | Falsum ]).
Qed.


Lemma Qquadratic_sign_nR_nR_7 :
 forall (a b c d e f g h : Z) (p1 xs p2 ys : Qpositive)
   (H_Qquadratic_sg_denom_nonzero : Qquadratic_sg_denom_nonzero e f g h p1 p2)
   (H_Qquadratic_sg_denom_nonzero_II : Qquadratic_sg_denom_nonzero e 
                                         (e + f) (e + g) 
                                         (e + f + g + h) xs ys),
 p1 = nR xs ->
 p2 = nR ys ->
 ~ (b = 0%Z /\ c = 0%Z /\ d = 0%Z) ->
 f = 0%Z /\ g = 0%Z /\ h = 0%Z ->
 ~ (2 < outside_square a b c d)%Z ->
 ~ (outside_square a b c d < -2)%Z ->
 Qquadratic_sign a b c d e f g h p1 p2 H_Qquadratic_sg_denom_nonzero =
 Qquadratic_sign a (a + b) (a + c) (a + b + c + d) e 
   (e + f) (e + g) (e + f + g + h) xs ys H_Qquadratic_sg_denom_nonzero_II.
Proof.
 intros;
  generalize H_Qquadratic_sg_denom_nonzero H_Qquadratic_sg_denom_nonzero_II;
  rewrite H; rewrite H0; intros; simpl in |- *;
  case (three_integers_dec_inf b c d); intro Hbcd;
  [ Falsum
  | case (three_integers_dec_inf f g h); intro Hfgh;
     [ case (Z_lt_dec 2 (outside_square a b c d)); intro Ho1;
        [ Falsum
        | case (Z_lt_dec (outside_square a b c d) (-2)); intro Ho1';
           [ Falsum | apply Qquadratic_sign_equal ] ]
     | Falsum ] ].
Qed.

Lemma Qquadratic_sign_nR_dL_7 :
 forall (a b c d e f g h : Z) (p1 xs p2 ys : Qpositive)
   (H_Qquadratic_sg_denom_nonzero : Qquadratic_sg_denom_nonzero e f g h p1 p2)
   (H_Qquadratic_sg_denom_nonzero_IO : Qquadratic_sg_denom_nonzero 
                                         (e + f) f 
                                         (e + f + g + h) 
                                         (f + h) xs ys),
 p1 = nR xs ->
 p2 = dL ys ->
 ~ (b = 0%Z /\ c = 0%Z /\ d = 0%Z) ->
 f = 0%Z /\ g = 0%Z /\ h = 0%Z ->
 ~ (2 < outside_square a b c d)%Z ->
 ~ (outside_square a b c d < -2)%Z ->
 Qquadratic_sign a b c d e f g h p1 p2 H_Qquadratic_sg_denom_nonzero =
 Qquadratic_sign (a + b) b (a + b + c + d) (b + d) 
   (e + f) f (e + f + g + h) (f + h) xs ys H_Qquadratic_sg_denom_nonzero_IO.
Proof.
 intros;
  generalize H_Qquadratic_sg_denom_nonzero H_Qquadratic_sg_denom_nonzero_IO;
  rewrite H; rewrite H0; intros; simpl in |- *;
  case (three_integers_dec_inf b c d); intro Hbcd;
  [ Falsum
  | case (three_integers_dec_inf f g h); intro Hfgh;
     [ case (Z_lt_dec 2 (outside_square a b c d)); intro Ho1;
        [ Falsum
        | case (Z_lt_dec (outside_square a b c d) (-2)); intro Ho1';
           [ Falsum | apply Qquadratic_sign_equal ] ]
     | Falsum ] ].
Qed.

Lemma Qquadratic_sign_dL_nR_7 :
 forall (a b c d e f g h : Z) (p1 xs p2 ys : Qpositive)
   (H_Qquadratic_sg_denom_nonzero : Qquadratic_sg_denom_nonzero e f g h p1 p2)
   (H_Qquadratic_sg_denom_nonzero_OI : Qquadratic_sg_denom_nonzero 
                                         (e + g) (e + f + g + h) g 
                                         (g + h) xs ys),
 p1 = dL xs ->
 p2 = nR ys ->
 ~ (b = 0%Z /\ c = 0%Z /\ d = 0%Z) ->
 f = 0%Z /\ g = 0%Z /\ h = 0%Z ->
 ~ (2 < outside_square a b c d)%Z ->
 ~ (outside_square a b c d < -2)%Z ->
 Qquadratic_sign a b c d e f g h p1 p2 H_Qquadratic_sg_denom_nonzero =
 Qquadratic_sign (a + c) (a + b + c + d) c (c + d) 
   (e + g) (e + f + g + h) g (g + h) xs ys H_Qquadratic_sg_denom_nonzero_OI.
Proof.
 intros;
  generalize H_Qquadratic_sg_denom_nonzero H_Qquadratic_sg_denom_nonzero_OI;
  rewrite H; rewrite H0; intros; simpl in |- *;
  case (three_integers_dec_inf b c d); intro Hbcd;
  [ Falsum
  | case (three_integers_dec_inf f g h); intro Hfgh;
     [ case (Z_lt_dec 2 (outside_square a b c d)); intro Ho1;
        [ Falsum
        | case (Z_lt_dec (outside_square a b c d) (-2)); intro Ho1';
           [ Falsum | apply Qquadratic_sign_equal ] ]
     | Falsum ] ].
Qed.

Lemma Qquadratic_sign_dL_dL_7 :
 forall (a b c d e f g h : Z) (p1 xs p2 ys : Qpositive)
   (H_Qquadratic_sg_denom_nonzero : Qquadratic_sg_denom_nonzero e f g h p1 p2)
   (H_Qquadratic_sg_denom_nonzero_OO : Qquadratic_sg_denom_nonzero
                                         (e + f + g + h) 
                                         (f + h) (g + h) h xs ys),
 p1 = dL xs ->
 p2 = dL ys ->
 ~ (b = 0%Z /\ c = 0%Z /\ d = 0%Z) ->
 f = 0%Z /\ g = 0%Z /\ h = 0%Z ->
 ~ (2 < outside_square a b c d)%Z ->
 ~ (outside_square a b c d < -2)%Z ->
 Qquadratic_sign a b c d e f g h p1 p2 H_Qquadratic_sg_denom_nonzero =
 Qquadratic_sign (a + b + c + d) (b + d) (c + d) d 
   (e + f + g + h) (f + h) (g + h) h xs ys H_Qquadratic_sg_denom_nonzero_OO.
Proof. 
 intros;
  generalize H_Qquadratic_sg_denom_nonzero H_Qquadratic_sg_denom_nonzero_OO;
  rewrite H; rewrite H0; intros; simpl in |- *;
  case (three_integers_dec_inf b c d); intro Hbcd;
  [ Falsum
  | case (three_integers_dec_inf f g h); intro Hfgh;
     [ case (Z_lt_dec 2 (outside_square a b c d)); intro Ho1;
        [ Falsum
        | case (Z_lt_dec (outside_square a b c d) (-2)); intro Ho1';
           [ Falsum | apply Qquadratic_sign_equal ] ]
     | Falsum ] ].
Qed.

Lemma Qquadratic_sign_nRdL_nRdL_8 :
 forall (a b c d e f g h : Z) (p1 p2 : Qpositive)
   (H_Qquadratic_sg_denom_nonzero : Qquadratic_sg_denom_nonzero e f g h p1 p2),
 p1 <> One ->
 p2 <> One ->
 ~ (b = 0%Z /\ c = 0%Z /\ d = 0%Z) ->
 ~ (f = 0%Z /\ g = 0%Z /\ h = 0%Z) ->
 inside_square_1 (outside_square a b c d) (outside_square e f g h) ->
 Qquadratic_sign a b c d e f g h p1 p2 H_Qquadratic_sg_denom_nonzero =
 (1%Z, (a, (b, (c, d)), (e, (f, (g, h))), (p1, p2))).
Proof.
 intros.
 destruct p1 as [q| q| ];
  solve [ Falsum ] ||
    let T_local :=
     (simpl in |- *; case (three_integers_dec_inf b c d); intro Hbcd;
       [ Falsum
       | case (three_integers_dec_inf f g h); intro Hfgh;
          [ Falsum
          | case
             (inside_square_1_dec_inf (outside_square a b c d)
                (outside_square e f g h)); intro H_inside_1;
             [ reflexivity | Falsum ] ] ]) in
    (destruct p2 as [q0| q0| ]; [ T_local | T_local | Falsum ]).
Qed.



Lemma Qquadratic_sign_nRdL_nRdL_9 :
 forall (a b c d e f g h : Z) (p1 p2 : Qpositive)
   (H_Qquadratic_sg_denom_nonzero : Qquadratic_sg_denom_nonzero e f g h p1 p2),
 p1 <> One ->
 p2 <> One ->
 ~ (b = 0%Z /\ c = 0%Z /\ d = 0%Z) ->
 ~ (f = 0%Z /\ g = 0%Z /\ h = 0%Z) ->
 ~ inside_square_1 (outside_square a b c d) (outside_square e f g h) ->
 inside_square_2 (outside_square a b c d) (outside_square e f g h) ->
 Qquadratic_sign a b c d e f g h p1 p2 H_Qquadratic_sg_denom_nonzero =
 ((-1)%Z, (a, (b, (c, d)), (e, (f, (g, h))), (p1, p2))).
Proof.
 intros.
 destruct p1 as [q| q| ];
  solve [ Falsum ] ||
    let T_local :=
     (simpl in |- *; case (three_integers_dec_inf b c d); intro Hbcd;
       [ Falsum
       | case (three_integers_dec_inf f g h); intro Hfgh;
          [ Falsum
          | case
             (inside_square_1_dec_inf (outside_square a b c d)
                (outside_square e f g h)); intro H_inside_1;
             [ Falsum
             | case
                (inside_square_2_dec_inf (outside_square a b c d)
                   (outside_square e f g h)); intro H_inside_2;
                [ reflexivity | Falsum ] ] ] ]) in
    (destruct p2 as [q0| q0| ]; [ T_local | T_local | Falsum ]).
Qed.

Lemma Qquadratic_sign_nR_nR_10 :
 forall (a b c d e f g h : Z) (p1 xs p2 ys : Qpositive)
   (H_Qquadratic_sg_denom_nonzero : Qquadratic_sg_denom_nonzero e f g h p1 p2)
   (H_Qquadratic_sg_denom_nonzero_II : Qquadratic_sg_denom_nonzero e 
                                         (e + f) (e + g) 
                                         (e + f + g + h) xs ys),
 p1 = nR xs ->
 p2 = nR ys ->
 ~ (b = 0%Z /\ c = 0%Z /\ d = 0%Z) ->
 ~ (f = 0%Z /\ g = 0%Z /\ h = 0%Z) ->
 ~ inside_square_1 (outside_square a b c d) (outside_square e f g h) ->
 ~ inside_square_2 (outside_square a b c d) (outside_square e f g h) ->
 Qquadratic_sign a b c d e f g h p1 p2 H_Qquadratic_sg_denom_nonzero =
 Qquadratic_sign a (a + b) (a + c) (a + b + c + d) e 
   (e + f) (e + g) (e + f + g + h) xs ys H_Qquadratic_sg_denom_nonzero_II.
Proof.
 intros;
  generalize H_Qquadratic_sg_denom_nonzero H_Qquadratic_sg_denom_nonzero_II;
  rewrite H; rewrite H0; intros; simpl in |- *;
  case (three_integers_dec_inf b c d); intro Hbcd;
  [ Falsum
  | case (three_integers_dec_inf f g h); intro Hfgh;
     [ Falsum
     | case
        (inside_square_1_dec_inf (outside_square a b c d)
           (outside_square e f g h)); intro H_inside_1;
        [ Falsum
        | case
           (inside_square_2_dec_inf (outside_square a b c d)
              (outside_square e f g h)); intro H_inside_2;
           [ Falsum | apply Qquadratic_sign_equal ] ] ] ].
Qed.

Lemma Qquadratic_sign_nR_dL_10 :
 forall (a b c d e f g h : Z) (p1 xs p2 ys : Qpositive)
   (H_Qquadratic_sg_denom_nonzero : Qquadratic_sg_denom_nonzero e f g h p1 p2)
   (H_Qquadratic_sg_denom_nonzero_IO : Qquadratic_sg_denom_nonzero 
                                         (e + f) f 
                                         (e + f + g + h) 
                                         (f + h) xs ys),
 p1 = nR xs ->
 p2 = dL ys ->
 ~ (b = 0%Z /\ c = 0%Z /\ d = 0%Z) ->
 ~ (f = 0%Z /\ g = 0%Z /\ h = 0%Z) ->
 ~ inside_square_1 (outside_square a b c d) (outside_square e f g h) ->
 ~ inside_square_2 (outside_square a b c d) (outside_square e f g h) ->
 Qquadratic_sign a b c d e f g h p1 p2 H_Qquadratic_sg_denom_nonzero =
 Qquadratic_sign (a + b) b (a + b + c + d) (b + d) 
   (e + f) f (e + f + g + h) (f + h) xs ys H_Qquadratic_sg_denom_nonzero_IO.
Proof.
 intros;
  generalize H_Qquadratic_sg_denom_nonzero H_Qquadratic_sg_denom_nonzero_IO;
  rewrite H; rewrite H0; intros; simpl in |- *;
  case (three_integers_dec_inf b c d); intro Hbcd;
  [ Falsum
  | case (three_integers_dec_inf f g h); intro Hfgh;
     [ Falsum
     | case
        (inside_square_1_dec_inf (outside_square a b c d)
           (outside_square e f g h)); intro H_inside_1;
        [ Falsum
        | case
           (inside_square_2_dec_inf (outside_square a b c d)
              (outside_square e f g h)); intro H_inside_2;
           [ Falsum | apply Qquadratic_sign_equal ] ] ] ].
Qed.

Lemma Qquadratic_sign_dL_nR_10 :
 forall (a b c d e f g h : Z) (p1 xs p2 ys : Qpositive)
   (H_Qquadratic_sg_denom_nonzero : Qquadratic_sg_denom_nonzero e f g h p1 p2)
   (H_Qquadratic_sg_denom_nonzero_OI : Qquadratic_sg_denom_nonzero 
                                         (e + g) (e + f + g + h) g 
                                         (g + h) xs ys),
 p1 = dL xs ->
 p2 = nR ys ->
 ~ (b = 0%Z /\ c = 0%Z /\ d = 0%Z) ->
 ~ (f = 0%Z /\ g = 0%Z /\ h = 0%Z) ->
 ~ inside_square_1 (outside_square a b c d) (outside_square e f g h) ->
 ~ inside_square_2 (outside_square a b c d) (outside_square e f g h) ->
 Qquadratic_sign a b c d e f g h p1 p2 H_Qquadratic_sg_denom_nonzero =
 Qquadratic_sign (a + c) (a + b + c + d) c (c + d) 
   (e + g) (e + f + g + h) g (g + h) xs ys H_Qquadratic_sg_denom_nonzero_OI.
Proof.
 intros;
  generalize H_Qquadratic_sg_denom_nonzero H_Qquadratic_sg_denom_nonzero_OI;
  rewrite H; rewrite H0; intros; simpl in |- *;
  case (three_integers_dec_inf b c d); intro Hbcd;
  [ Falsum
  | case (three_integers_dec_inf f g h); intro Hfgh;
     [ Falsum
     | case
        (inside_square_1_dec_inf (outside_square a b c d)
           (outside_square e f g h)); intro H_inside_1;
        [ Falsum
        | case
           (inside_square_2_dec_inf (outside_square a b c d)
              (outside_square e f g h)); intro H_inside_2;
           [ Falsum | apply Qquadratic_sign_equal ] ] ] ].
Qed.

Lemma Qquadratic_sign_dL_dL_10 :
 forall (a b c d e f g h : Z) (p1 xs p2 ys : Qpositive)
   (H_Qquadratic_sg_denom_nonzero : Qquadratic_sg_denom_nonzero e f g h p1 p2)
   (H_Qquadratic_sg_denom_nonzero_OO : Qquadratic_sg_denom_nonzero
                                         (e + f + g + h) 
                                         (f + h) (g + h) h xs ys),
 p1 = dL xs ->
 p2 = dL ys ->
 ~ (b = 0%Z /\ c = 0%Z /\ d = 0%Z) ->
 ~ (f = 0%Z /\ g = 0%Z /\ h = 0%Z) ->
 ~ inside_square_1 (outside_square a b c d) (outside_square e f g h) ->
 ~ inside_square_2 (outside_square a b c d) (outside_square e f g h) ->
 Qquadratic_sign a b c d e f g h p1 p2 H_Qquadratic_sg_denom_nonzero =
 Qquadratic_sign (a + b + c + d) (b + d) (c + d) d 
   (e + f + g + h) (f + h) (g + h) h xs ys H_Qquadratic_sg_denom_nonzero_OO.
Proof.
 intros;
  generalize H_Qquadratic_sg_denom_nonzero H_Qquadratic_sg_denom_nonzero_OO;
  rewrite H; rewrite H0; intros; simpl in |- *;
  case (three_integers_dec_inf b c d); intro Hbcd;
  [ Falsum
  | case (three_integers_dec_inf f g h); intro Hfgh;
     [ Falsum
     | case
        (inside_square_1_dec_inf (outside_square a b c d)
           (outside_square e f g h)); intro H_inside_1;
        [ Falsum
        | case
           (inside_square_2_dec_inf (outside_square a b c d)
              (outside_square e f g h)); intro H_inside_2;
           [ Falsum | apply Qquadratic_sign_equal ] ] ] ].
Qed.

Lemma Qquadratic_sign_sign :
 forall (a b c d e f g h : Z) (p1 p2 : Qpositive)
   (H_Qquadratic_sg_denom_nonzero : Qquadratic_sg_denom_nonzero e f g h p1 p2),
 let (l1, L2) :=
     Qquadratic_sign a b c d e f g h p1 p2 H_Qquadratic_sg_denom_nonzero in
 {l1 = 0%Z} + {l1 = 1%Z} + {l1 = (-1)%Z}.
Proof.
 fix Qquadratic_sign_sign 9.
 intros.
 
  destruct p1 as [p| p| ].
   destruct p2 as [p0| p0| ].
    (* p1 = (nR p) p2 = (nR p0) *) 
    case (three_integers_dec_inf b c d); intro Hbcd;
     case (three_integers_dec_inf f g h); intro Hfgh;
     [ rewrite Qquadratic_sign_nRdL_nRdL_1;
        try solve [ discriminate | assumption ]; rewrite <- Zsgn_15;
        apply Zsgn_1
     | case (Z_lt_dec 2 (outside_square e f g h)); intro Ho2;
        [ rewrite Qquadratic_sign_nRdL_nRdL_2;
           try solve [ discriminate | assumption ]; 
           apply Zsgn_1
        | case (Z_lt_dec (outside_square e f g h) (-2)); intro Ho2';
           [ rewrite Qquadratic_sign_nRdL_nRdL_3;
              try solve [ discriminate | assumption ]; 
              rewrite <- Zsgn_25; apply Zsgn_1
           | match goal with
             | id1:(?X1 ?X2 ?X3 ?X4 ?X5 (nR ?X6) (nR ?X7)) |- ?X8 =>
                 rewrite
                  (Qquadratic_sign_nR_nR_4 a b c d e f g h 
                     (nR p) p (nR p0) p0 H_Qquadratic_sg_denom_nonzero
                     (Qquadratic_signok_1 e f g h p p0
                        H_Qquadratic_sg_denom_nonzero) 
                     (refl_equal _) (refl_equal _) Hbcd Hfgh Ho2 Ho2')
                  
             | id1:(?X1 ?X2 ?X3 ?X4 ?X5 (nR ?X6) (dL ?X7)) |- ?X8 =>
                 rewrite
                  (Qquadratic_sign_nR_dL_4 a b c d e f g h 
                     (nR p) p (dL p0) p0 H_Qquadratic_sg_denom_nonzero
                     (Qquadratic_signok_2 e f g h p p0
                        H_Qquadratic_sg_denom_nonzero) 
                     (refl_equal _) (refl_equal _) Hbcd Hfgh Ho2 Ho2')
                  
             | id1:(?X1 ?X2 ?X3 ?X4 ?X5 (dL ?X6) (nR ?X7)) |- ?X8 =>
                 rewrite
                  (Qquadratic_sign_dL_nR_4 a b c d e f g h 
                     (dL p) p (nR p0) p0 H_Qquadratic_sg_denom_nonzero
                     (Qquadratic_signok_3 e f g h p p0
                        H_Qquadratic_sg_denom_nonzero) 
                     (refl_equal _) (refl_equal _) Hbcd Hfgh Ho2 Ho2')
                  
             | id1:(?X1 ?X2 ?X3 ?X4 ?X5 (dL ?X6) (dL ?X7)) |- ?X8 =>
                 rewrite
                  (Qquadratic_sign_dL_dL_4 a b c d e f g h 
                     (dL p) p (dL p0) p0 H_Qquadratic_sg_denom_nonzero
                     (Qquadratic_signok_4 e f g h p p0
                        H_Qquadratic_sg_denom_nonzero) 
                     (refl_equal _) (refl_equal _) Hbcd Hfgh Ho2 Ho2')
                  
             end; apply Qquadratic_sign_sign ] ]
     | case (Z_lt_dec 2 (outside_square a b c d)); intro Ho1;
        [ rewrite Qquadratic_sign_nRdL_nRdL_5;
           try solve [ discriminate | assumption ]; 
           apply Zsgn_1
        | case (Z_lt_dec (outside_square a b c d) (-2)); intro Ho1';
           [ rewrite Qquadratic_sign_nRdL_nRdL_6;
              try solve [ discriminate | assumption ]; 
              rewrite <- Zsgn_25; apply Zsgn_1
           | match goal with
             | id1:(?X1 ?X2 ?X3 ?X4 ?X5 (nR ?X6) (nR ?X7)) |- ?X8 =>
                 rewrite
                  (Qquadratic_sign_nR_nR_7 a b c d e f g h 
                     (nR p) p (nR p0) p0 H_Qquadratic_sg_denom_nonzero
                     (Qquadratic_signok_1 e f g h p p0
                        H_Qquadratic_sg_denom_nonzero) 
                     (refl_equal _) (refl_equal _) Hbcd Hfgh Ho1 Ho1')
                  
             | id1:(?X1 ?X2 ?X3 ?X4 ?X5 (nR ?X6) (dL ?X7)) |- ?X8 =>
                 rewrite
                  (Qquadratic_sign_nR_dL_7 a b c d e f g h 
                     (nR p) p (dL p0) p0 H_Qquadratic_sg_denom_nonzero
                     (Qquadratic_signok_2 e f g h p p0
                        H_Qquadratic_sg_denom_nonzero) 
                     (refl_equal _) (refl_equal _) Hbcd Hfgh Ho1 Ho1')
                  
             | id1:(?X1 ?X2 ?X3 ?X4 ?X5 (dL ?X6) (nR ?X7)) |- ?X8 =>
                 rewrite
                  (Qquadratic_sign_dL_nR_7 a b c d e f g h 
                     (dL p) p (nR p0) p0 H_Qquadratic_sg_denom_nonzero
                     (Qquadratic_signok_3 e f g h p p0
                        H_Qquadratic_sg_denom_nonzero) 
                     (refl_equal _) (refl_equal _) Hbcd Hfgh Ho1 Ho1')
                  
             | id1:(?X1 ?X2 ?X3 ?X4 ?X5 (dL ?X6) (dL ?X7)) |- ?X8 =>
                 rewrite
                  (Qquadratic_sign_dL_dL_7 a b c d e f g h 
                     (dL p) p (dL p0) p0 H_Qquadratic_sg_denom_nonzero
                     (Qquadratic_signok_4 e f g h p p0
                        H_Qquadratic_sg_denom_nonzero) 
                     (refl_equal _) (refl_equal _) Hbcd Hfgh Ho1 Ho1')
                  
             end; apply Qquadratic_sign_sign ] ]
     | case
        (inside_square_1_dec_inf (outside_square a b c d)
           (outside_square e f g h)); intro H_inside_1;
        [ rewrite Qquadratic_sign_nRdL_nRdL_8;
           try solve [ discriminate | assumption ]; 
           left; right; reflexivity
        | case
           (inside_square_2_dec_inf (outside_square a b c d)
              (outside_square e f g h)); intro H_inside_2;
           [ rewrite Qquadratic_sign_nRdL_nRdL_9;
              try solve [ discriminate | assumption ]; 
              right; reflexivity
           | match goal with
             | id1:(?X1 ?X2 ?X3 ?X4 ?X5 (nR ?X6) (nR ?X7)) |- ?X8 =>
                 rewrite
                  (Qquadratic_sign_nR_nR_10 a b c d e f g h 
                     (nR p) p (nR p0) p0 H_Qquadratic_sg_denom_nonzero
                     (Qquadratic_signok_1 e f g h p p0
                        H_Qquadratic_sg_denom_nonzero) 
                     (refl_equal _) (refl_equal _) Hbcd Hfgh H_inside_1
                     H_inside_2)
             | id1:(?X1 ?X2 ?X3 ?X4 ?X5 (nR ?X6) (dL ?X7)) |- ?X8 =>
                 rewrite
                  (Qquadratic_sign_nR_dL_10 a b c d e f g h 
                     (nR p) p (dL p0) p0 H_Qquadratic_sg_denom_nonzero
                     (Qquadratic_signok_2 e f g h p p0
                        H_Qquadratic_sg_denom_nonzero) 
                     (refl_equal _) (refl_equal _) Hbcd Hfgh H_inside_1
                     H_inside_2)
             | id1:(?X1 ?X2 ?X3 ?X4 ?X5 (dL ?X6) (nR ?X7)) |- ?X8 =>
                 rewrite
                  (Qquadratic_sign_dL_nR_10 a b c d e f g h 
                     (dL p) p (nR p0) p0 H_Qquadratic_sg_denom_nonzero
                     (Qquadratic_signok_3 e f g h p p0
                        H_Qquadratic_sg_denom_nonzero) 
                     (refl_equal _) (refl_equal _) Hbcd Hfgh H_inside_1
                     H_inside_2)
             | id1:(?X1 ?X2 ?X3 ?X4 ?X5 (dL ?X6) (dL ?X7)) |- ?X8 =>
                 rewrite
                  (Qquadratic_sign_dL_dL_10 a b c d e f g h 
                     (dL p) p (dL p0) p0 H_Qquadratic_sg_denom_nonzero
                     (Qquadratic_signok_4 e f g h p p0
                        H_Qquadratic_sg_denom_nonzero) 
                     (refl_equal _) (refl_equal _) Hbcd Hfgh H_inside_1
                     H_inside_2)
             end; apply Qquadratic_sign_sign ] ] ].
  
    (* p1 = (nR p) p2 = (dL p0) *) 
    case (three_integers_dec_inf b c d); intro Hbcd;
     case (three_integers_dec_inf f g h); intro Hfgh;
     [ rewrite Qquadratic_sign_nRdL_nRdL_1;
        try solve [ discriminate | assumption ]; rewrite <- Zsgn_15;
        apply Zsgn_1
     | case (Z_lt_dec 2 (outside_square e f g h)); intro Ho2;
        [ rewrite Qquadratic_sign_nRdL_nRdL_2;
           try solve [ discriminate | assumption ]; 
           apply Zsgn_1
        | case (Z_lt_dec (outside_square e f g h) (-2)); intro Ho2';
           [ rewrite Qquadratic_sign_nRdL_nRdL_3;
              try solve [ discriminate | assumption ]; 
              rewrite <- Zsgn_25; apply Zsgn_1
           | match goal with
             | id1:(?X1 ?X2 ?X3 ?X4 ?X5 (nR ?X6) (nR ?X7)) |- ?X8 =>
                 rewrite
                  (Qquadratic_sign_nR_nR_4 a b c d e f g h 
                     (nR p) p (nR p0) p0 H_Qquadratic_sg_denom_nonzero
                     (Qquadratic_signok_1 e f g h p p0
                        H_Qquadratic_sg_denom_nonzero) 
                     (refl_equal _) (refl_equal _) Hbcd Hfgh Ho2 Ho2')
                  
             | id1:(?X1 ?X2 ?X3 ?X4 ?X5 (nR ?X6) (dL ?X7)) |- ?X8 =>
                 rewrite
                  (Qquadratic_sign_nR_dL_4 a b c d e f g h 
                     (nR p) p (dL p0) p0 H_Qquadratic_sg_denom_nonzero
                     (Qquadratic_signok_2 e f g h p p0
                        H_Qquadratic_sg_denom_nonzero) 
                     (refl_equal _) (refl_equal _) Hbcd Hfgh Ho2 Ho2')
                  
             | id1:(?X1 ?X2 ?X3 ?X4 ?X5 (dL ?X6) (nR ?X7)) |- ?X8 =>
                 rewrite
                  (Qquadratic_sign_dL_nR_4 a b c d e f g h 
                     (dL p) p (nR p0) p0 H_Qquadratic_sg_denom_nonzero
                     (Qquadratic_signok_3 e f g h p p0
                        H_Qquadratic_sg_denom_nonzero) 
                     (refl_equal _) (refl_equal _) Hbcd Hfgh Ho2 Ho2')
                  
             | id1:(?X1 ?X2 ?X3 ?X4 ?X5 (dL ?X6) (dL ?X7)) |- ?X8 =>
                 rewrite
                  (Qquadratic_sign_dL_dL_4 a b c d e f g h 
                     (dL p) p (dL p0) p0 H_Qquadratic_sg_denom_nonzero
                     (Qquadratic_signok_4 e f g h p p0
                        H_Qquadratic_sg_denom_nonzero) 
                     (refl_equal _) (refl_equal _) Hbcd Hfgh Ho2 Ho2')
                  
             end; apply Qquadratic_sign_sign ] ]
     | case (Z_lt_dec 2 (outside_square a b c d)); intro Ho1;
        [ rewrite Qquadratic_sign_nRdL_nRdL_5;
           try solve [ discriminate | assumption ]; 
           apply Zsgn_1
        | case (Z_lt_dec (outside_square a b c d) (-2)); intro Ho1';
           [ rewrite Qquadratic_sign_nRdL_nRdL_6;
              try solve [ discriminate | assumption ]; 
              rewrite <- Zsgn_25; apply Zsgn_1
           | match goal with
             | id1:(?X1 ?X2 ?X3 ?X4 ?X5 (nR ?X6) (nR ?X7)) |- ?X8 =>
                 rewrite
                  (Qquadratic_sign_nR_nR_7 a b c d e f g h 
                     (nR p) p (nR p0) p0 H_Qquadratic_sg_denom_nonzero
                     (Qquadratic_signok_1 e f g h p p0
                        H_Qquadratic_sg_denom_nonzero) 
                     (refl_equal _) (refl_equal _) Hbcd Hfgh Ho1 Ho1')
                  
             | id1:(?X1 ?X2 ?X3 ?X4 ?X5 (nR ?X6) (dL ?X7)) |- ?X8 =>
                 rewrite
                  (Qquadratic_sign_nR_dL_7 a b c d e f g h 
                     (nR p) p (dL p0) p0 H_Qquadratic_sg_denom_nonzero
                     (Qquadratic_signok_2 e f g h p p0
                        H_Qquadratic_sg_denom_nonzero) 
                     (refl_equal _) (refl_equal _) Hbcd Hfgh Ho1 Ho1')
                  
             | id1:(?X1 ?X2 ?X3 ?X4 ?X5 (dL ?X6) (nR ?X7)) |- ?X8 =>
                 rewrite
                  (Qquadratic_sign_dL_nR_7 a b c d e f g h 
                     (dL p) p (nR p0) p0 H_Qquadratic_sg_denom_nonzero
                     (Qquadratic_signok_3 e f g h p p0
                        H_Qquadratic_sg_denom_nonzero) 
                     (refl_equal _) (refl_equal _) Hbcd Hfgh Ho1 Ho1')
                  
             | id1:(?X1 ?X2 ?X3 ?X4 ?X5 (dL ?X6) (dL ?X7)) |- ?X8 =>
                 rewrite
                  (Qquadratic_sign_dL_dL_7 a b c d e f g h 
                     (dL p) p (dL p0) p0 H_Qquadratic_sg_denom_nonzero
                     (Qquadratic_signok_4 e f g h p p0
                        H_Qquadratic_sg_denom_nonzero) 
                     (refl_equal _) (refl_equal _) Hbcd Hfgh Ho1 Ho1')
                  
             end; apply Qquadratic_sign_sign ] ]
     | case
        (inside_square_1_dec_inf (outside_square a b c d)
           (outside_square e f g h)); intro H_inside_1;
        [ rewrite Qquadratic_sign_nRdL_nRdL_8;
           try solve [ discriminate | assumption ]; 
           left; right; reflexivity
        | case
           (inside_square_2_dec_inf (outside_square a b c d)
              (outside_square e f g h)); intro H_inside_2;
           [ rewrite Qquadratic_sign_nRdL_nRdL_9;
              try solve [ discriminate | assumption ]; 
              right; reflexivity
           | match goal with
             | id1:(?X1 ?X2 ?X3 ?X4 ?X5 (nR ?X6) (nR ?X7)) |- ?X8 =>
                 rewrite
                  (Qquadratic_sign_nR_nR_10 a b c d e f g h 
                     (nR p) p (nR p0) p0 H_Qquadratic_sg_denom_nonzero
                     (Qquadratic_signok_1 e f g h p p0
                        H_Qquadratic_sg_denom_nonzero) 
                     (refl_equal _) (refl_equal _) Hbcd Hfgh H_inside_1
                     H_inside_2)
             | id1:(?X1 ?X2 ?X3 ?X4 ?X5 (nR ?X6) (dL ?X7)) |- ?X8 =>
                 rewrite
                  (Qquadratic_sign_nR_dL_10 a b c d e f g h 
                     (nR p) p (dL p0) p0 H_Qquadratic_sg_denom_nonzero
                     (Qquadratic_signok_2 e f g h p p0
                        H_Qquadratic_sg_denom_nonzero) 
                     (refl_equal _) (refl_equal _) Hbcd Hfgh H_inside_1
                     H_inside_2)
             | id1:(?X1 ?X2 ?X3 ?X4 ?X5 (dL ?X6) (nR ?X7)) |- ?X8 =>
                 rewrite
                  (Qquadratic_sign_dL_nR_10 a b c d e f g h 
                     (dL p) p (nR p0) p0 H_Qquadratic_sg_denom_nonzero
                     (Qquadratic_signok_3 e f g h p p0
                        H_Qquadratic_sg_denom_nonzero) 
                     (refl_equal _) (refl_equal _) Hbcd Hfgh H_inside_1
                     H_inside_2)
             | id1:(?X1 ?X2 ?X3 ?X4 ?X5 (dL ?X6) (dL ?X7)) |- ?X8 =>
                 rewrite
                  (Qquadratic_sign_dL_dL_10 a b c d e f g h 
                     (dL p) p (dL p0) p0 H_Qquadratic_sg_denom_nonzero
                     (Qquadratic_signok_4 e f g h p p0
                        H_Qquadratic_sg_denom_nonzero) 
                     (refl_equal _) (refl_equal _) Hbcd Hfgh H_inside_1
                     H_inside_2)
             end; apply Qquadratic_sign_sign ] ] ].
  (* p1 = (nR p) p2 = One *)  
  generalize (Qquadratic_signok_0' _ _ _ _ _ H_Qquadratic_sg_denom_nonzero);
   intro H_Qhomographic_sg_denom_nonzero;
   set
    (L3 :=
     Qhomographic_sign (a + b) (c + d) (e + f) (g + h) 
       (nR p) H_Qhomographic_sg_denom_nonzero) in *; 
   set (l1' := fst L3) in *; set (l2 := fst (snd L3)) in *;
   set (l3 := snd (snd L3)) in *; set (na := fst l2) in *;
   set (nb := fst (snd l2)) in *; set (nc := fst (snd (snd l2))) in *;
   set (nd := snd (snd (snd l2))) in *;
   rewrite
    (Qquadratic_sign_nRdL_One a b c d e f g h (nR p) One
       H_Qquadratic_sg_denom_nonzero l1' na nb nc nd l3
       H_Qhomographic_sg_denom_nonzero);
   [ replace l1' with
      (h_sign (a + b) (c + d) (e + f) (g + h) (nR p)
         H_Qhomographic_sg_denom_nonzero);
      [ apply sg_sign_dec | reflexivity ]
   | fold L3 in |- *; repeat (apply pair_2; try reflexivity);
      discriminate || reflexivity
   | discriminate
   | reflexivity ].

  destruct p2 as [p0| p0| ].
    (* p1 = (dL p) p2 = (nR p0) *) (* CLONE of the above *) 
    case (three_integers_dec_inf b c d); intro Hbcd;
     case (three_integers_dec_inf f g h); intro Hfgh;
     [ rewrite Qquadratic_sign_nRdL_nRdL_1;
        try solve [ discriminate | assumption ]; rewrite <- Zsgn_15;
        apply Zsgn_1
     | case (Z_lt_dec 2 (outside_square e f g h)); intro Ho2;
        [ rewrite Qquadratic_sign_nRdL_nRdL_2;
           try solve [ discriminate | assumption ]; 
           apply Zsgn_1
        | case (Z_lt_dec (outside_square e f g h) (-2)); intro Ho2';
           [ rewrite Qquadratic_sign_nRdL_nRdL_3;
              try solve [ discriminate | assumption ]; 
              rewrite <- Zsgn_25; apply Zsgn_1
           | match goal with
             | id1:(?X1 ?X2 ?X3 ?X4 ?X5 (nR ?X6) (nR ?X7)) |- ?X8 =>
                 rewrite
                  (Qquadratic_sign_nR_nR_4 a b c d e f g h 
                     (nR p) p (nR p0) p0 H_Qquadratic_sg_denom_nonzero
                     (Qquadratic_signok_1 e f g h p p0
                        H_Qquadratic_sg_denom_nonzero) 
                     (refl_equal _) (refl_equal _) Hbcd Hfgh Ho2 Ho2')
                  
             | id1:(?X1 ?X2 ?X3 ?X4 ?X5 (nR ?X6) (dL ?X7)) |- ?X8 =>
                 rewrite
                  (Qquadratic_sign_nR_dL_4 a b c d e f g h 
                     (nR p) p (dL p0) p0 H_Qquadratic_sg_denom_nonzero
                     (Qquadratic_signok_2 e f g h p p0
                        H_Qquadratic_sg_denom_nonzero) 
                     (refl_equal _) (refl_equal _) Hbcd Hfgh Ho2 Ho2')
                  
             | id1:(?X1 ?X2 ?X3 ?X4 ?X5 (dL ?X6) (nR ?X7)) |- ?X8 =>
                 rewrite
                  (Qquadratic_sign_dL_nR_4 a b c d e f g h 
                     (dL p) p (nR p0) p0 H_Qquadratic_sg_denom_nonzero
                     (Qquadratic_signok_3 e f g h p p0
                        H_Qquadratic_sg_denom_nonzero) 
                     (refl_equal _) (refl_equal _) Hbcd Hfgh Ho2 Ho2')
                  
             | id1:(?X1 ?X2 ?X3 ?X4 ?X5 (dL ?X6) (dL ?X7)) |- ?X8 =>
                 rewrite
                  (Qquadratic_sign_dL_dL_4 a b c d e f g h 
                     (dL p) p (dL p0) p0 H_Qquadratic_sg_denom_nonzero
                     (Qquadratic_signok_4 e f g h p p0
                        H_Qquadratic_sg_denom_nonzero) 
                     (refl_equal _) (refl_equal _) Hbcd Hfgh Ho2 Ho2')
                  
             end; apply Qquadratic_sign_sign ] ]
     | case (Z_lt_dec 2 (outside_square a b c d)); intro Ho1;
        [ rewrite Qquadratic_sign_nRdL_nRdL_5;
           try solve [ discriminate | assumption ]; 
           apply Zsgn_1
        | case (Z_lt_dec (outside_square a b c d) (-2)); intro Ho1';
           [ rewrite Qquadratic_sign_nRdL_nRdL_6;
              try solve [ discriminate | assumption ]; 
              rewrite <- Zsgn_25; apply Zsgn_1
           | match goal with
             | id1:(?X1 ?X2 ?X3 ?X4 ?X5 (nR ?X6) (nR ?X7)) |- ?X8 =>
                 rewrite
                  (Qquadratic_sign_nR_nR_7 a b c d e f g h 
                     (nR p) p (nR p0) p0 H_Qquadratic_sg_denom_nonzero
                     (Qquadratic_signok_1 e f g h p p0
                        H_Qquadratic_sg_denom_nonzero) 
                     (refl_equal _) (refl_equal _) Hbcd Hfgh Ho1 Ho1')
                  
             | id1:(?X1 ?X2 ?X3 ?X4 ?X5 (nR ?X6) (dL ?X7)) |- ?X8 =>
                 rewrite
                  (Qquadratic_sign_nR_dL_7 a b c d e f g h 
                     (nR p) p (dL p0) p0 H_Qquadratic_sg_denom_nonzero
                     (Qquadratic_signok_2 e f g h p p0
                        H_Qquadratic_sg_denom_nonzero) 
                     (refl_equal _) (refl_equal _) Hbcd Hfgh Ho1 Ho1')
                  
             | id1:(?X1 ?X2 ?X3 ?X4 ?X5 (dL ?X6) (nR ?X7)) |- ?X8 =>
                 rewrite
                  (Qquadratic_sign_dL_nR_7 a b c d e f g h 
                     (dL p) p (nR p0) p0 H_Qquadratic_sg_denom_nonzero
                     (Qquadratic_signok_3 e f g h p p0
                        H_Qquadratic_sg_denom_nonzero) 
                     (refl_equal _) (refl_equal _) Hbcd Hfgh Ho1 Ho1')
                  
             | id1:(?X1 ?X2 ?X3 ?X4 ?X5 (dL ?X6) (dL ?X7)) |- ?X8 =>
                 rewrite
                  (Qquadratic_sign_dL_dL_7 a b c d e f g h 
                     (dL p) p (dL p0) p0 H_Qquadratic_sg_denom_nonzero
                     (Qquadratic_signok_4 e f g h p p0
                        H_Qquadratic_sg_denom_nonzero) 
                     (refl_equal _) (refl_equal _) Hbcd Hfgh Ho1 Ho1')
                  
             end; apply Qquadratic_sign_sign ] ]
     | case
        (inside_square_1_dec_inf (outside_square a b c d)
           (outside_square e f g h)); intro H_inside_1;
        [ rewrite Qquadratic_sign_nRdL_nRdL_8;
           try solve [ discriminate | assumption ]; 
           left; right; reflexivity
        | case
           (inside_square_2_dec_inf (outside_square a b c d)
              (outside_square e f g h)); intro H_inside_2;
           [ rewrite Qquadratic_sign_nRdL_nRdL_9;
              try solve [ discriminate | assumption ]; 
              right; reflexivity
           | match goal with
             | id1:(?X1 ?X2 ?X3 ?X4 ?X5 (nR ?X6) (nR ?X7)) |- ?X8 =>
                 rewrite
                  (Qquadratic_sign_nR_nR_10 a b c d e f g h 
                     (nR p) p (nR p0) p0 H_Qquadratic_sg_denom_nonzero
                     (Qquadratic_signok_1 e f g h p p0
                        H_Qquadratic_sg_denom_nonzero) 
                     (refl_equal _) (refl_equal _) Hbcd Hfgh H_inside_1
                     H_inside_2)
             | id1:(?X1 ?X2 ?X3 ?X4 ?X5 (nR ?X6) (dL ?X7)) |- ?X8 =>
                 rewrite
                  (Qquadratic_sign_nR_dL_10 a b c d e f g h 
                     (nR p) p (dL p0) p0 H_Qquadratic_sg_denom_nonzero
                     (Qquadratic_signok_2 e f g h p p0
                        H_Qquadratic_sg_denom_nonzero) 
                     (refl_equal _) (refl_equal _) Hbcd Hfgh H_inside_1
                     H_inside_2)
             | id1:(?X1 ?X2 ?X3 ?X4 ?X5 (dL ?X6) (nR ?X7)) |- ?X8 =>
                 rewrite
                  (Qquadratic_sign_dL_nR_10 a b c d e f g h 
                     (dL p) p (nR p0) p0 H_Qquadratic_sg_denom_nonzero
                     (Qquadratic_signok_3 e f g h p p0
                        H_Qquadratic_sg_denom_nonzero) 
                     (refl_equal _) (refl_equal _) Hbcd Hfgh H_inside_1
                     H_inside_2)
             | id1:(?X1 ?X2 ?X3 ?X4 ?X5 (dL ?X6) (dL ?X7)) |- ?X8 =>
                 rewrite
                  (Qquadratic_sign_dL_dL_10 a b c d e f g h 
                     (dL p) p (dL p0) p0 H_Qquadratic_sg_denom_nonzero
                     (Qquadratic_signok_4 e f g h p p0
                        H_Qquadratic_sg_denom_nonzero) 
                     (refl_equal _) (refl_equal _) Hbcd Hfgh H_inside_1
                     H_inside_2)
             end; apply Qquadratic_sign_sign ] ] ].
  
    (* p1 = (dL p) p2 = (dL p0) *)  (* CLONE of the above *) 
    case (three_integers_dec_inf b c d); intro Hbcd;
     case (three_integers_dec_inf f g h); intro Hfgh;
     [ rewrite Qquadratic_sign_nRdL_nRdL_1;
        try solve [ discriminate | assumption ]; rewrite <- Zsgn_15;
        apply Zsgn_1
     | case (Z_lt_dec 2 (outside_square e f g h)); intro Ho2;
        [ rewrite Qquadratic_sign_nRdL_nRdL_2;
           try solve [ discriminate | assumption ]; 
           apply Zsgn_1
        | case (Z_lt_dec (outside_square e f g h) (-2)); intro Ho2';
           [ rewrite Qquadratic_sign_nRdL_nRdL_3;
              try solve [ discriminate | assumption ]; 
              rewrite <- Zsgn_25; apply Zsgn_1
           | match goal with
             | id1:(?X1 ?X2 ?X3 ?X4 ?X5 (nR ?X6) (nR ?X7)) |- ?X8 =>
                 rewrite
                  (Qquadratic_sign_nR_nR_4 a b c d e f g h 
                     (nR p) p (nR p0) p0 H_Qquadratic_sg_denom_nonzero
                     (Qquadratic_signok_1 e f g h p p0
                        H_Qquadratic_sg_denom_nonzero) 
                     (refl_equal _) (refl_equal _) Hbcd Hfgh Ho2 Ho2')
                  
             | id1:(?X1 ?X2 ?X3 ?X4 ?X5 (nR ?X6) (dL ?X7)) |- ?X8 =>
                 rewrite
                  (Qquadratic_sign_nR_dL_4 a b c d e f g h 
                     (nR p) p (dL p0) p0 H_Qquadratic_sg_denom_nonzero
                     (Qquadratic_signok_2 e f g h p p0
                        H_Qquadratic_sg_denom_nonzero) 
                     (refl_equal _) (refl_equal _) Hbcd Hfgh Ho2 Ho2')
                  
             | id1:(?X1 ?X2 ?X3 ?X4 ?X5 (dL ?X6) (nR ?X7)) |- ?X8 =>
                 rewrite
                  (Qquadratic_sign_dL_nR_4 a b c d e f g h 
                     (dL p) p (nR p0) p0 H_Qquadratic_sg_denom_nonzero
                     (Qquadratic_signok_3 e f g h p p0
                        H_Qquadratic_sg_denom_nonzero) 
                     (refl_equal _) (refl_equal _) Hbcd Hfgh Ho2 Ho2')
                  
             | id1:(?X1 ?X2 ?X3 ?X4 ?X5 (dL ?X6) (dL ?X7)) |- ?X8 =>
                 rewrite
                  (Qquadratic_sign_dL_dL_4 a b c d e f g h 
                     (dL p) p (dL p0) p0 H_Qquadratic_sg_denom_nonzero
                     (Qquadratic_signok_4 e f g h p p0
                        H_Qquadratic_sg_denom_nonzero) 
                     (refl_equal _) (refl_equal _) Hbcd Hfgh Ho2 Ho2')
                  
             end; apply Qquadratic_sign_sign ] ]
     | case (Z_lt_dec 2 (outside_square a b c d)); intro Ho1;
        [ rewrite Qquadratic_sign_nRdL_nRdL_5;
           try solve [ discriminate | assumption ]; 
           apply Zsgn_1
        | case (Z_lt_dec (outside_square a b c d) (-2)); intro Ho1';
           [ rewrite Qquadratic_sign_nRdL_nRdL_6;
              try solve [ discriminate | assumption ]; 
              rewrite <- Zsgn_25; apply Zsgn_1
           | match goal with
             | id1:(?X1 ?X2 ?X3 ?X4 ?X5 (nR ?X6) (nR ?X7)) |- ?X8 =>
                 rewrite
                  (Qquadratic_sign_nR_nR_7 a b c d e f g h 
                     (nR p) p (nR p0) p0 H_Qquadratic_sg_denom_nonzero
                     (Qquadratic_signok_1 e f g h p p0
                        H_Qquadratic_sg_denom_nonzero) 
                     (refl_equal _) (refl_equal _) Hbcd Hfgh Ho1 Ho1')
                  
             | id1:(?X1 ?X2 ?X3 ?X4 ?X5 (nR ?X6) (dL ?X7)) |- ?X8 =>
                 rewrite
                  (Qquadratic_sign_nR_dL_7 a b c d e f g h 
                     (nR p) p (dL p0) p0 H_Qquadratic_sg_denom_nonzero
                     (Qquadratic_signok_2 e f g h p p0
                        H_Qquadratic_sg_denom_nonzero) 
                     (refl_equal _) (refl_equal _) Hbcd Hfgh Ho1 Ho1')
                  
             | id1:(?X1 ?X2 ?X3 ?X4 ?X5 (dL ?X6) (nR ?X7)) |- ?X8 =>
                 rewrite
                  (Qquadratic_sign_dL_nR_7 a b c d e f g h 
                     (dL p) p (nR p0) p0 H_Qquadratic_sg_denom_nonzero
                     (Qquadratic_signok_3 e f g h p p0
                        H_Qquadratic_sg_denom_nonzero) 
                     (refl_equal _) (refl_equal _) Hbcd Hfgh Ho1 Ho1')
                  
             | id1:(?X1 ?X2 ?X3 ?X4 ?X5 (dL ?X6) (dL ?X7)) |- ?X8 =>
                 rewrite
                  (Qquadratic_sign_dL_dL_7 a b c d e f g h 
                     (dL p) p (dL p0) p0 H_Qquadratic_sg_denom_nonzero
                     (Qquadratic_signok_4 e f g h p p0
                        H_Qquadratic_sg_denom_nonzero) 
                     (refl_equal _) (refl_equal _) Hbcd Hfgh Ho1 Ho1')
                  
             end; apply Qquadratic_sign_sign ] ]
     | case
        (inside_square_1_dec_inf (outside_square a b c d)
           (outside_square e f g h)); intro H_inside_1;
        [ rewrite Qquadratic_sign_nRdL_nRdL_8;
           try solve [ discriminate | assumption ]; 
           left; right; reflexivity
        | case
           (inside_square_2_dec_inf (outside_square a b c d)
              (outside_square e f g h)); intro H_inside_2;
           [ rewrite Qquadratic_sign_nRdL_nRdL_9;
              try solve [ discriminate | assumption ]; 
              right; reflexivity
           | match goal with
             | id1:(?X1 ?X2 ?X3 ?X4 ?X5 (nR ?X6) (nR ?X7)) |- ?X8 =>
                 rewrite
                  (Qquadratic_sign_nR_nR_10 a b c d e f g h 
                     (nR p) p (nR p0) p0 H_Qquadratic_sg_denom_nonzero
                     (Qquadratic_signok_1 e f g h p p0
                        H_Qquadratic_sg_denom_nonzero) 
                     (refl_equal _) (refl_equal _) Hbcd Hfgh H_inside_1
                     H_inside_2)
             | id1:(?X1 ?X2 ?X3 ?X4 ?X5 (nR ?X6) (dL ?X7)) |- ?X8 =>
                 rewrite
                  (Qquadratic_sign_nR_dL_10 a b c d e f g h 
                     (nR p) p (dL p0) p0 H_Qquadratic_sg_denom_nonzero
                     (Qquadratic_signok_2 e f g h p p0
                        H_Qquadratic_sg_denom_nonzero) 
                     (refl_equal _) (refl_equal _) Hbcd Hfgh H_inside_1
                     H_inside_2)
             | id1:(?X1 ?X2 ?X3 ?X4 ?X5 (dL ?X6) (nR ?X7)) |- ?X8 =>
                 rewrite
                  (Qquadratic_sign_dL_nR_10 a b c d e f g h 
                     (dL p) p (nR p0) p0 H_Qquadratic_sg_denom_nonzero
                     (Qquadratic_signok_3 e f g h p p0
                        H_Qquadratic_sg_denom_nonzero) 
                     (refl_equal _) (refl_equal _) Hbcd Hfgh H_inside_1
                     H_inside_2)
             | id1:(?X1 ?X2 ?X3 ?X4 ?X5 (dL ?X6) (dL ?X7)) |- ?X8 =>
                 rewrite
                  (Qquadratic_sign_dL_dL_10 a b c d e f g h 
                     (dL p) p (dL p0) p0 H_Qquadratic_sg_denom_nonzero
                     (Qquadratic_signok_4 e f g h p p0
                        H_Qquadratic_sg_denom_nonzero) 
                     (refl_equal _) (refl_equal _) Hbcd Hfgh H_inside_1
                     H_inside_2)
             end; apply Qquadratic_sign_sign ] ] ].
   (* p1 = (nR p) p2 = One *) (* not a CLONE *) 
   generalize (Qquadratic_signok_0' _ _ _ _ _ H_Qquadratic_sg_denom_nonzero);
    intro H_Qhomographic_sg_denom_nonzero;
    set
     (L3 :=
      Qhomographic_sign (a + b) (c + d) (e + f) (g + h) 
        (dL p) H_Qhomographic_sg_denom_nonzero) in *;
    set (l1' := fst L3) in *; set (l2 := fst (snd L3)) in *;
    set (l3 := snd (snd L3)) in *; set (na := fst l2) in *;
    set (nb := fst (snd l2)) in *; set (nc := fst (snd (snd l2))) in *;
    set (nd := snd (snd (snd l2))) in *;
    rewrite
     (Qquadratic_sign_nRdL_One a b c d e f g h (dL p) One
        H_Qquadratic_sg_denom_nonzero l1' na nb nc nd l3
        H_Qhomographic_sg_denom_nonzero);
    [ replace l1' with
       (h_sign (a + b) (c + d) (e + f) (g + h) (dL p)
          H_Qhomographic_sg_denom_nonzero);
       [ apply sg_sign_dec | reflexivity ]
    | fold L3 in |- *; repeat (apply pair_2; try reflexivity);
       discriminate || reflexivity
    | discriminate
    | reflexivity ].

 (* p1 = One *)
  generalize (Qquadratic_signok_0 _ _ _ _ _ H_Qquadratic_sg_denom_nonzero);
   intro H_Qhomographic_sg_denom_nonzero;
   set
    (L3 :=
     Qhomographic_sign (a + c) (b + d) (e + g) (f + h) p2
       H_Qhomographic_sg_denom_nonzero) in *; set (l1' := fst L3) in *;
   set (l2 := fst (snd L3)) in *; set (l3 := snd (snd L3)) in *;
   set (na := fst l2) in *; set (nb := fst (snd l2)) in *;
   set (nc := fst (snd (snd l2))) in *; set (nd := snd (snd (snd l2))) in *;
   rewrite
    (Qquadratic_sign_One_y a b c d e f g h One p2
       H_Qquadratic_sg_denom_nonzero l1' na nb nc nd l3
       H_Qhomographic_sg_denom_nonzero);
   [ replace l1' with
      (h_sign (a + c) (b + d) (e + g) (f + h) p2
         H_Qhomographic_sg_denom_nonzero);
      [ apply sg_sign_dec | reflexivity ]
   | fold L3 in |- *; repeat (apply pair_2; try reflexivity);
      discriminate || reflexivity
   | reflexivity ].
Qed.

Definition q_sign (a b c d e f g h : Z) (p1 p2 : Qpositive)
  (H_Qquadratic_sg_denom_nonzero : Qquadratic_sg_denom_nonzero e f g h p1 p2) :=
  let (l1, L2) :=
      Qquadratic_sign a b c d e f g h p1 p2 H_Qquadratic_sg_denom_nonzero in
  l1.

Lemma Qquadratic_sign_sign_dec :
 forall (a b c d e f g h : Z) (p1 p2 : Qpositive)
   (H_Qquadratic_sg_denom_nonzero : Qquadratic_sg_denom_nonzero e f g h p1 p2),
 {q_sign a b c d e f g h p1 p2 H_Qquadratic_sg_denom_nonzero = 0%Z} +
 {q_sign a b c d e f g h p1 p2 H_Qquadratic_sg_denom_nonzero = 1%Z} +
 {q_sign a b c d e f g h p1 p2 H_Qquadratic_sg_denom_nonzero = (-1)%Z}.
Proof.
 intros.
 unfold q_sign in |- *.
 generalize
  (Qquadratic_sign_sign a b c d e f g h p1 p2 H_Qquadratic_sg_denom_nonzero).
 case (Qquadratic_sign a b c d e f g h p1 p2 H_Qquadratic_sg_denom_nonzero).
 intros l1 L2.
 trivial.
Qed.
