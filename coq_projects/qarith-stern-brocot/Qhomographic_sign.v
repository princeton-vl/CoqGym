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



Require Export positive_fraction_encoding.
Require Import ZArithRing.

Definition outside_interval (a b : Z) := (Z.sgn a + Z.sgn b)%Z.

Definition inside_interval_1 (o1 o2 : Z) :=
  (0 < o1)%Z /\ (0 < o2)%Z \/ (o1 < 0)%Z /\ (o2 < 0)%Z.

Definition inside_interval_2 (o1 o2 : Z) :=
  (0 < o1)%Z /\ (o2 < 0)%Z \/ (o1 < 0)%Z /\ (0 < o2)%Z.

Lemma inside_interval_1_dec_inf :
 forall o1 o2 : Z, {inside_interval_1 o1 o2} + {~ inside_interval_1 o1 o2}.
Proof.
 intros.
 abstract (case (Z_lt_dec 0 o1); intro Ho1;
            [ case (Z_lt_dec 0 o2); intro Ho2;
               [ left; left; split
               | right; intro H;
                  match goal with
                  | id1:(~ ?X1) |- ?X2 =>
                      apply id1; case H; intros (H1, H2);
                       [ idtac
                       | apply False_ind; apply Z.lt_irrefl with o1;
                          apply Z.lt_trans with 0%Z ]
                  end ]
            | case (Z_lt_dec o1 0); intro Ho1';
               [ case (Z_lt_dec o2 0); intro Ho2;
                  [ left; right; split
                  | right; intro H; case H; intros (H1, H2);
                     [ apply Ho1 | apply Ho2 ] ]
               | right; intro H; apply Ho1; case H; intros (H1, H2);
                  [ idtac | apply False_ind; apply Ho1' ] ] ]; 
            try assumption).
Defined. 

Lemma inside_interval_2_dec_inf :
 forall o1 o2 : Z, {inside_interval_2 o1 o2} + {~ inside_interval_2 o1 o2}.
Proof.
 intros.
 abstract (case (Z_lt_dec 0 o1); intro Ho1;
            [ case (Z_lt_dec o2 0); intro Ho2;
               [ left; left; split
               | right; intro H;
                  match goal with
                  | id1:(~ ?X1) |- ?X2 =>
                      apply id1; case H; intros (H1, H2);
                       [ idtac
                       | apply False_ind; apply Z.lt_irrefl with o1;
                          apply Z.lt_trans with 0%Z ]
                  end ]
            | case (Z_lt_dec o1 0); intro Ho1';
               [ case (Z_lt_dec 0 o2); intro Ho2;
                  [ left; right; split
                  | right; intro H; case H; intros (H1, H2);
                     [ apply Ho1 | apply Ho2 ] ]
               | right; intro H; apply Ho1; case H; intros (H1, H2);
                  [ idtac | apply False_ind; apply Ho1' ] ] ]; 
            try assumption).
Defined. 


Inductive Qhomographic_sg_denom_nonzero : Z -> Z -> Qpositive -> Prop :=
  | Qhomographic_signok0 :
      forall (c d : Z) (p : Qpositive),
      p = One -> (c + d)%Z <> 0%Z -> Qhomographic_sg_denom_nonzero c d p
  | Qhomographic_signok1 :
      forall (c d : Z) (xs : Qpositive),
      Qhomographic_sg_denom_nonzero c (c + d)%Z xs ->
      Qhomographic_sg_denom_nonzero c d (nR xs)
  | Qhomographic_signok2 :
      forall (c d : Z) (xs : Qpositive),
      Qhomographic_sg_denom_nonzero (c + d)%Z d xs ->
      Qhomographic_sg_denom_nonzero c d (dL xs).

Lemma Qhomographic_signok_1 :
 forall c d : Z, Qhomographic_sg_denom_nonzero c d One -> (c + d)%Z <> 0%Z.
Proof.
 intros.
 inversion H.
 assumption.
Defined.

Lemma Qhomographic_signok_2 :
 forall (c d : Z) (xs : Qpositive),
 Qhomographic_sg_denom_nonzero c d (nR xs) ->
 Qhomographic_sg_denom_nonzero c (c + d) xs.
Proof.
 intros.
 inversion H.
 discriminate H0.
 assumption.
Defined.

Lemma Qhomographic_signok_3 :
 forall (c d : Z) (xs : Qpositive),
 Qhomographic_sg_denom_nonzero c d (dL xs) ->
 Qhomographic_sg_denom_nonzero (c + d) d xs.
Proof.
 intros.
 inversion H.
 discriminate H0.
 assumption.
Defined.



Fixpoint Qhomographic_sign (a b c d : Z) (p : Qpositive) {struct p} :
  forall (H_Qhomographic_sg_denom_nonzero : Qhomographic_sg_denom_nonzero c d p),
  Z * (Z * (Z * (Z * Z)) * Qpositive).
set (o1 := outside_interval a b) in *.
set (o2 := outside_interval c d) in *.
destruct p as [q| q| ]; intros H_Qhomographic_sg_denom_nonzero.
 (* p=(nR xs) *)
  case (Z_zerop b).
   (* b=0 *)
   intro Hb.
   case (Z_zerop d).
    (* d=0 *)
    intro Hd.
    exact ((Z.sgn a * Z.sgn c)%Z, (a, (b, (c, d)), nR q)).
    (* d<>0 *) 
    intro Hd'. 
    case (Z_lt_dec 0 o2).
     (*  `0 < o2` *)
     intro Ho2.
     exact (Z.sgn a, (a, (b, (c, d)), nR q)).
     (* ~( 0<o2 ) *)
     intro Ho2'.
     case (Z_lt_dec o2 0).
      (* o2 < 0  *)
      intro Ho2.
      exact ((- Z.sgn a)%Z, (a, (b, (c, d)), nR q)).
      (* ~`0 < o2` /\ ~ `0 < o2` /\ d<>0  *)
      intro Ho2''.
      exact
       (Qhomographic_sign a (a + b)%Z c (c + d)%Z q
          (Qhomographic_signok_2 c d q H_Qhomographic_sg_denom_nonzero)).
   (* b<>0 *)
   intro Hb.
   case (Z_zerop d).
    (* d=0 *)
    intro Hd. 
    case (Z_lt_dec 0 o1).
     (*  `0 < o1` *)
     intro Ho1.
     exact (Z.sgn c, (a, (b, (c, d)), nR q)).
     (* ~( 0<o1 ) *)
     intro Ho1'.
     case (Z_lt_dec o1 0).
      (* o1 < 0  *)
      intro Ho1.
      exact ((- Z.sgn c)%Z, (a, (b, (c, d)), nR q)).
      (* ~`0 < o1` /\ ~ `0 < o1` /\ b<>0  *)
      intro Ho1''.
      exact
       (Qhomographic_sign a (a + b)%Z c (c + d)%Z q
          (Qhomographic_signok_2 c d q H_Qhomographic_sg_denom_nonzero)).
    (* d<>0 *)
    intro Hd'.
    case (inside_interval_1_dec_inf o1 o2).    
     (* (inside_interval_1 o1 o2) *)
     intro H_inside_1.
     exact (1%Z, (a, (b, (c, d)), nR q)).
     (* ~(inside_interval_1 o1 o2) *)
     intro H_inside_1'.
     case (inside_interval_2_dec_inf o1 o2).    
      (* (inside_interval_2 o1 o2) *)
      intro H_inside_2.
      exact ((-1)%Z, (a, (b, (c, d)), nR q)).
      (*  ~(inside_interval_1 o1 o2)/\~(inside_interval_2 o1 o2) *)
      intros H_inside_2'. 
      exact
       (Qhomographic_sign a (a + b)%Z c (c + d)%Z q
          (Qhomographic_signok_2 c d q H_Qhomographic_sg_denom_nonzero)).
  (* p=(dL xs) *)
  case (Z_zerop b).
   (* b=0 *)
   intro Hb.
   case (Z_zerop d).
    (* d=0 *)
    intro Hd.
    exact ((Z.sgn a * Z.sgn c)%Z, (a, (b, (c, d)), dL q)).
    (* d<>0 *) 
    intro Hd'. 
    case (Z_lt_dec 0 o2).
     (*  `0 < o2` *)
     intro Ho2.
     exact (Z.sgn a, (a, (b, (c, d)), dL q)).
     (* ~( 0<o2 ) *)
     intro Ho2'.
     case (Z_lt_dec o2 0).
      (* o2 < 0  *)
      intro Ho2.
      exact ((- Z.sgn a)%Z, (a, (b, (c, d)), dL q)).
      (* ~`0 < o2` /\ ~ `0 < o2` /\ d<>0  *)
      intro Ho2''.
      exact
       (Qhomographic_sign (a + b)%Z b (c + d)%Z d q
          (Qhomographic_signok_3 c d q H_Qhomographic_sg_denom_nonzero)).
   (* b<>0 *)
   intro Hb.
   case (Z_zerop d).
    (* d=0 *)
    intro Hd. 
    case (Z_lt_dec 0 o1).
     (*  `0 < o1` *)
     intro Ho1.
     exact (Z.sgn c, (a, (b, (c, d)), dL q)).
     (* ~( 0<o1 ) *)
     intro Ho1'.
     case (Z_lt_dec o1 0).
      (* o1 < 0  *)
      intro Ho1.
      exact ((- Z.sgn c)%Z, (a, (b, (c, d)), dL q)).
      (* ~`0 < o1` /\ ~ `0 < o1` /\ b<>0  *)
      intro Ho1''.
      exact
       (Qhomographic_sign (a + b)%Z b (c + d)%Z d q
          (Qhomographic_signok_3 c d q H_Qhomographic_sg_denom_nonzero)).
    (* d<>0 *)
    intro Hd'.
    case (inside_interval_1_dec_inf o1 o2).    
     (* (inside_interval_1 o1 o2) *)
     intro H_inside_1.
     exact (1%Z, (a, (b, (c, d)), dL q)).
     (* ~(inside_interval_1 o1 o2) *)
     intro H_inside_1'.
     case (inside_interval_2_dec_inf o1 o2).    
      (* (inside_interval_2 o1 o2) *)
      intro H_inside_2.
      exact ((-1)%Z, (a, (b, (c, d)), dL q)).
      (*  ~(inside_interval_1 o1 o2)/\~(inside_interval_2 o1 o2) *)
      intros H_inside_2'. 
      exact
       (Qhomographic_sign (a + b)%Z b (c + d)%Z d q
          (Qhomographic_signok_3 c d q H_Qhomographic_sg_denom_nonzero)).

 (* p = One *)
  set (soorat := Z.sgn (a + b)) in *.
  set (makhraj := Z.sgn (c + d)) in *.

  case (Z.eq_dec soorat 0).   
   (*  `soorat = 0` *)
   intro eq_numerator0.
   exact (0%Z, (a, (b, (c, d)), One)).
   (*  `soorat <> 0` *)   
   intro.
   case (Z.eq_dec soorat makhraj).
    (* soorat = makhraj *)
    intro.
    exact (1%Z, (a, (b, (c, d)), One)).
    (* soorat <> makhraj *)
    intro.
    exact ((-1)%Z, (a, (b, (c, d)), One)).
Defined.

Functional Scheme Qhomographic_sign_ind :=
  Induction for Qhomographic_sign Sort Prop.

Scheme Qhomographic_sg_denom_nonzero_inv_dep :=
  Induction for Qhomographic_sg_denom_nonzero Sort Prop.


Lemma Qhomographic_sign_equal :
 forall (a b c d : Z) (p : Qpositive)
   (H1 H2 : Qhomographic_sg_denom_nonzero c d p),
 Qhomographic_sign a b c d p H1 = Qhomographic_sign a b c d p H2.
Proof.
 intros.
 generalize H2 H1 a b.
 intro.
 abstract let T_local := (intros; simpl in |- *; rewrite H; reflexivity) in
          (elim H0 using Qhomographic_sg_denom_nonzero_inv_dep; intros;
            [ destruct p0 as [q| q| ];
               [ discriminate e
               | discriminate e
               | simpl in |- *; case (Z.eq_dec (Z.sgn (a0 + b0)) 0);
                  case (Z.eq_dec (Z.sgn (a0 + b0)) (Z.sgn (c0 + d0))); 
                  intros; reflexivity ]
            | T_local
            | T_local ]).
Defined. 

Lemma Qhomographic_sign_equal_strong :
 forall (a1 a2 b1 b2 c1 c2 d1 d2 : Z) (p1 p2 : Qpositive)
   (H_ok_1 : Qhomographic_sg_denom_nonzero c1 d1 p1)
   (H_ok_2 : Qhomographic_sg_denom_nonzero c2 d2 p2),
 a1 = a2 ->
 b1 = b2 ->
 c1 = c2 ->
 d1 = d2 ->
 p1 = p2 ->
 Qhomographic_sign a1 b1 c1 d1 p1 H_ok_1 =
 Qhomographic_sign a2 b2 c2 d2 p2 H_ok_2.
Proof.
 abstract (intros; generalize H_ok_2;
            repeat
             match goal with
             | id1:(?X1 = ?X2) |- ?X3 => rewrite <- id1; clear id1
             end; intro; apply Qhomographic_sign_equal). 
Defined.


Lemma sg_One_2 :
 forall (a b c d : Z) (p : Qpositive)
   (H_Qhomographic_sg_denom_nonzero : Qhomographic_sg_denom_nonzero c d p),
 p = One ->
 Z.sgn (a + b) = 0%Z ->
 Qhomographic_sign a b c d p H_Qhomographic_sg_denom_nonzero =
 (0%Z, (a, (b, (c, d)), One)).
Proof.
 intros.
 destruct p as [q| q| ]; repeat (apply False_ind; discriminate H).
 simpl in |- *.
 case (Z.eq_dec (Z.sgn (a + b)) 0).
 intro.
 reflexivity.
 intro.
 Falsum.
Defined.

Lemma sg_One_3 :
 forall (a b c d : Z) (p : Qpositive)
   (H_Qhomographic_sg_denom_nonzero : Qhomographic_sg_denom_nonzero c d p),
 p = One ->
 Z.sgn (a + b) <> 0%Z ->
 Z.sgn (a + b) = Z.sgn (c + d) ->
 Qhomographic_sign a b c d p H_Qhomographic_sg_denom_nonzero =
 (1%Z, (a, (b, (c, d)), One)).
Proof.
 intros.
 destruct p as [q| q| ]; repeat (apply False_ind; discriminate H).
 simpl in |- *.
 case (Z.eq_dec (Z.sgn (a + b)) 0).
 Falsum.
 intro.
 case (Z.eq_dec (Z.sgn (a + b)) (Z.sgn (c + d))).
 intro.
 reflexivity.
 intro.
 Falsum.
Defined.


Lemma sg_One_4 :
 forall (a b c d : Z) (p : Qpositive)
   (H_Qhomographic_sg_denom_nonzero : Qhomographic_sg_denom_nonzero c d p),
 p = One ->
 Z.sgn (a + b) <> 0%Z ->
 Z.sgn (a + b) <> Z.sgn (c + d) ->
 Qhomographic_sign a b c d p H_Qhomographic_sg_denom_nonzero =
 ((-1)%Z, (a, (b, (c, d)), One)).
Proof.
 intros.
 destruct p as [q| q| ]; repeat (apply False_ind; discriminate H).
 simpl in |- *.
 case (Z.eq_dec (Z.sgn (a + b)) 0).
 Falsum.
 case (Z.eq_dec (Z.sgn (a + b)) (Z.sgn (c + d))).
 Falsum.
 reflexivity.
Defined.

Lemma Qhomographic_sign_nR_1 :
 forall (a b c d : Z) (p xs : Qpositive)
   (H_Qhomographic_sg_denom_nonzero : Qhomographic_sg_denom_nonzero c d p),
 p = nR xs ->
 b = 0%Z ->
 d = 0%Z ->
 Qhomographic_sign a b c d p H_Qhomographic_sg_denom_nonzero =
 ((Z.sgn a * Z.sgn c)%Z, (a, (b, (c, d)), p)).
Proof.
 intros; generalize H_Qhomographic_sg_denom_nonzero;
  clear H_Qhomographic_sg_denom_nonzero; rewrite H;
  intros H_Qhomographic_sg_denom_nonzero; simpl in |- *; 
  case (Z_zerop b); intro Hb;
  [ case (Z_zerop d); intro Hd; [ reflexivity | Falsum ] | Falsum ].
Defined.


Lemma Qhomographic_sign_nR_2 :
 forall (a b c d : Z) (p xs : Qpositive)
   (H_Qhomographic_sg_denom_nonzero : Qhomographic_sg_denom_nonzero c d p),
 p = nR xs ->
 b = 0%Z ->
 d <> 0%Z ->
 (0 < outside_interval c d)%Z ->
 Qhomographic_sign a b c d p H_Qhomographic_sg_denom_nonzero =
 (Z.sgn a, (a, (b, (c, d)), p)).
Proof.
 intros; generalize H_Qhomographic_sg_denom_nonzero;
  clear H_Qhomographic_sg_denom_nonzero; rewrite H;
  intros H_Qhomographic_sg_denom_nonzero; simpl in |- *; 
  case (Z_zerop b); intro Hb;
  [ case (Z_zerop d); intro Hd;
     [ Falsum
     | case (Z_lt_dec 0 (outside_interval c d)); intro Ho2;
        [ reflexivity | Falsum ] ]
  | Falsum ].
Defined.


Lemma Qhomographic_sign_nR_3 :
 forall (a b c d : Z) (p xs : Qpositive)
   (H_Qhomographic_sg_denom_nonzero : Qhomographic_sg_denom_nonzero c d p),
 p = nR xs ->
 b = 0%Z ->
 d <> 0%Z ->
 ~ (0 < outside_interval c d)%Z ->
 (outside_interval c d < 0)%Z ->
 Qhomographic_sign a b c d p H_Qhomographic_sg_denom_nonzero =
 ((- Z.sgn a)%Z, (a, (b, (c, d)), p)).
Proof.
 intros; generalize H_Qhomographic_sg_denom_nonzero;
  clear H_Qhomographic_sg_denom_nonzero; rewrite H;
  intros H_Qhomographic_sg_denom_nonzero; simpl in |- *; 
  case (Z_zerop b); intro Hb;
  [ case (Z_zerop d); intro Hd;
     [ Falsum
     | case (Z_lt_dec 0 (outside_interval c d)); intro Ho2;
        [ Falsum
        | case (Z_lt_dec (outside_interval c d) 0); intro Ho2';
           [ reflexivity | Falsum ] ] ]
  | Falsum ].
Defined.

Lemma Qhomographic_sign_nR_4 :
 forall (a b c d : Z) (p xs : Qpositive)
   (H_Qhomographic_sg_denom_nonzero : Qhomographic_sg_denom_nonzero c 
                                        (c + d) xs)
   (H_Qhomographic_sg_denom_nonzero_nR : Qhomographic_sg_denom_nonzero c d
                                           (nR xs)),
 b = 0%Z ->
 d <> 0%Z ->
 ~ (0 < outside_interval c d)%Z ->
 ~ (outside_interval c d < 0)%Z ->
 Qhomographic_sign a b c d (nR xs) H_Qhomographic_sg_denom_nonzero_nR =
 Qhomographic_sign a (a + b) c (c + d) xs H_Qhomographic_sg_denom_nonzero.
Proof.
 intros; simpl in |- *; case (Z_zerop b); intro Hb;
  [ case (Z_zerop d); intro Hd;
     [ Falsum
     | case (Z_lt_dec 0 (outside_interval c d)); intro Ho2;
        [ Falsum
        | case (Z_lt_dec (outside_interval c d) 0); intro Ho2';
           [ Falsum | apply Qhomographic_sign_equal ] ] ]
  | Falsum ].
Defined.

Lemma Qhomographic_sign_nR_5 :
 forall (a b c d : Z) (p xs : Qpositive)
   (H_Qhomographic_sg_denom_nonzero : Qhomographic_sg_denom_nonzero c d p),
 p = nR xs ->
 b <> 0%Z ->
 d = 0%Z ->
 (0 < outside_interval a b)%Z ->
 Qhomographic_sign a b c d p H_Qhomographic_sg_denom_nonzero =
 (Z.sgn c, (a, (b, (c, d)), p)).
Proof.
 intros; generalize H_Qhomographic_sg_denom_nonzero;
  clear H_Qhomographic_sg_denom_nonzero; rewrite H;
  intros H_Qhomographic_sg_denom_nonzero; simpl in |- *; 
  case (Z_zerop b); intro Hb;
  [ Falsum
  | case (Z_zerop d); intro Hd;
     [ case (Z_lt_dec 0 (outside_interval a b)); intro Ho2;
        [ reflexivity | Falsum ]
     | Falsum ] ].
Defined.

Lemma Qhomographic_sign_nR_6 :
 forall (a b c d : Z) (p xs : Qpositive)
   (H_Qhomographic_sg_denom_nonzero : Qhomographic_sg_denom_nonzero c d p),
 p = nR xs ->
 b <> 0%Z ->
 d = 0%Z ->
 ~ (0 < outside_interval a b)%Z ->
 (outside_interval a b < 0)%Z ->
 Qhomographic_sign a b c d p H_Qhomographic_sg_denom_nonzero =
 ((- Z.sgn c)%Z, (a, (b, (c, d)), p)).
Proof.
 intros; generalize H_Qhomographic_sg_denom_nonzero;
  clear H_Qhomographic_sg_denom_nonzero; rewrite H;
  intros H_Qhomographic_sg_denom_nonzero; simpl in |- *; 
  case (Z_zerop b); intro Hb;
  [ Falsum
  | case (Z_zerop d); intro Hd;
     [ case (Z_lt_dec 0 (outside_interval a b)); intro Ho2;
        [ Falsum
        | case (Z_lt_dec (outside_interval a b) 0); intro Ho2';
           [ reflexivity | Falsum ] ]
     | Falsum ] ].
Defined.

Lemma Qhomographic_sign_nR_7 :
 forall (a b c d : Z) (p xs : Qpositive)
   (H_Qhomographic_sg_denom_nonzero : Qhomographic_sg_denom_nonzero c 
                                        (c + d) xs)
   (H_Qhomographic_sg_denom_nonzero_nR : Qhomographic_sg_denom_nonzero c d
                                           (nR xs)),
 b <> 0%Z ->
 d = 0%Z ->
 ~ (0 < outside_interval a b)%Z ->
 ~ (outside_interval a b < 0)%Z ->
 Qhomographic_sign a b c d (nR xs) H_Qhomographic_sg_denom_nonzero_nR =
 Qhomographic_sign a (a + b) c (c + d) xs H_Qhomographic_sg_denom_nonzero.
Proof.
 intros; simpl in |- *; case (Z_zerop b); intro Hb;
  [ Falsum
  | case (Z_zerop d); intro Hd;
     [ case (Z_lt_dec 0 (outside_interval a b)); intro Ho2;
        [ Falsum
        | case (Z_lt_dec (outside_interval a b) 0); intro Ho2';
           [ Falsum | apply Qhomographic_sign_equal ] ]
     | Falsum ] ].
Defined.


Lemma Qhomographic_sign_nR_8 :
 forall (a b c d : Z) (p xs : Qpositive)
   (H_Qhomographic_sg_denom_nonzero : Qhomographic_sg_denom_nonzero c d p),
 p = nR xs ->
 b <> 0%Z ->
 d <> 0%Z ->
 inside_interval_1 (outside_interval a b) (outside_interval c d) ->
 Qhomographic_sign a b c d p H_Qhomographic_sg_denom_nonzero =
 (1%Z, (a, (b, (c, d)), p)).
Proof.
 intros; generalize H_Qhomographic_sg_denom_nonzero;
  clear H_Qhomographic_sg_denom_nonzero; rewrite H;
  intros H_Qhomographic_sg_denom_nonzero; simpl in |- *; 
  case (Z_zerop b); intro Hb;
  [ Falsum
  | case (Z_zerop d); intro Hd;
     [ Falsum
     | case
        (inside_interval_1_dec_inf (outside_interval a b)
           (outside_interval c d)); intro H_inside_1;
        [ reflexivity | Falsum ] ] ].
Defined.


Lemma Qhomographic_sign_nR_9 :
 forall (a b c d : Z) (p xs : Qpositive)
   (H_Qhomographic_sg_denom_nonzero : Qhomographic_sg_denom_nonzero c d p),
 p = nR xs ->
 b <> 0%Z ->
 d <> 0%Z ->
 ~ inside_interval_1 (outside_interval a b) (outside_interval c d) ->
 inside_interval_2 (outside_interval a b) (outside_interval c d) ->
 Qhomographic_sign a b c d p H_Qhomographic_sg_denom_nonzero =
 ((-1)%Z, (a, (b, (c, d)), p)).
Proof.
 intros; generalize H_Qhomographic_sg_denom_nonzero;
  clear H_Qhomographic_sg_denom_nonzero; rewrite H;
  intros H_Qhomographic_sg_denom_nonzero; simpl in |- *; 
  case (Z_zerop b); intro Hb;
  [ Falsum
  | case (Z_zerop d); intro Hd;
     [ Falsum
     | case
        (inside_interval_1_dec_inf (outside_interval a b)
           (outside_interval c d)); intro H_inside_1;
        [ Falsum
        | case
           (inside_interval_2_dec_inf (outside_interval a b)
              (outside_interval c d)); intro H_inside_2;
           [ reflexivity | Falsum ] ] ] ].
Defined.


Lemma Qhomographic_sign_nR_10 :
 forall (a b c d : Z) (p xs : Qpositive)
   (H_Qhomographic_sg_denom_nonzero : Qhomographic_sg_denom_nonzero c 
                                        (c + d) xs)
   (H_Qhomographic_sg_denom_nonzero_nR : Qhomographic_sg_denom_nonzero c d
                                           (nR xs)),
 b <> 0%Z ->
 d <> 0%Z ->
 ~ inside_interval_1 (outside_interval a b) (outside_interval c d) ->
 ~ inside_interval_2 (outside_interval a b) (outside_interval c d) ->
 Qhomographic_sign a b c d (nR xs) H_Qhomographic_sg_denom_nonzero_nR =
 Qhomographic_sign a (a + b) c (c + d) xs H_Qhomographic_sg_denom_nonzero.
Proof.
 intros; simpl in |- *; case (Z_zerop b); intro Hb;
  [ Falsum
  | case (Z_zerop d); intro Hd;
     [ Falsum
     | case
        (inside_interval_1_dec_inf (outside_interval a b)
           (outside_interval c d)); intro H_inside_1;
        [ Falsum
        | case
           (inside_interval_2_dec_inf (outside_interval a b)
              (outside_interval c d)); intro H_inside_2;
           [ Falsum | apply Qhomographic_sign_equal ] ] ] ].
Defined.

(* the next 10 proofs are just clone of the above 10 proofs *)

Lemma Qhomographic_sign_dL_1 :
 forall (a b c d : Z) (p xs : Qpositive)
   (H_Qhomographic_sg_denom_nonzero : Qhomographic_sg_denom_nonzero c d p),
 p = dL xs ->
 b = 0%Z ->
 d = 0%Z ->
 Qhomographic_sign a b c d p H_Qhomographic_sg_denom_nonzero =
 ((Z.sgn a * Z.sgn c)%Z, (a, (b, (c, d)), p)).
Proof.
 intros; generalize H_Qhomographic_sg_denom_nonzero;
  clear H_Qhomographic_sg_denom_nonzero; rewrite H;
  intros H_Qhomographic_sg_denom_nonzero; simpl in |- *; 
  case (Z_zerop b); intro Hb;
  [ case (Z_zerop d); intro Hd; [ reflexivity | Falsum ] | Falsum ].
Defined.

Lemma Qhomographic_sign_dL_2 :
 forall (a b c d : Z) (p xs : Qpositive)
   (H_Qhomographic_sg_denom_nonzero : Qhomographic_sg_denom_nonzero c d p),
 p = dL xs ->
 b = 0%Z ->
 d <> 0%Z ->
 (0 < outside_interval c d)%Z ->
 Qhomographic_sign a b c d p H_Qhomographic_sg_denom_nonzero =
 (Z.sgn a, (a, (b, (c, d)), p)).
Proof.
 intros; generalize H_Qhomographic_sg_denom_nonzero;
  clear H_Qhomographic_sg_denom_nonzero; rewrite H;
  intros H_Qhomographic_sg_denom_nonzero; simpl in |- *; 
  case (Z_zerop b); intro Hb;
  [ case (Z_zerop d); intro Hd;
     [ Falsum
     | case (Z_lt_dec 0 (outside_interval c d)); intro Ho2;
        [ reflexivity | Falsum ] ]
  | Falsum ].
Defined.

Lemma Qhomographic_sign_dL_3 :
 forall (a b c d : Z) (p xs : Qpositive)
   (H_Qhomographic_sg_denom_nonzero : Qhomographic_sg_denom_nonzero c d p),
 p = dL xs ->
 b = 0%Z ->
 d <> 0%Z ->
 ~ (0 < outside_interval c d)%Z ->
 (outside_interval c d < 0)%Z ->
 Qhomographic_sign a b c d p H_Qhomographic_sg_denom_nonzero =
 ((- Z.sgn a)%Z, (a, (b, (c, d)), p)).
Proof.
 intros; generalize H_Qhomographic_sg_denom_nonzero;
  clear H_Qhomographic_sg_denom_nonzero; rewrite H;
  intros H_Qhomographic_sg_denom_nonzero; simpl in |- *; 
  case (Z_zerop b); intro Hb;
  [ case (Z_zerop d); intro Hd;
     [ Falsum
     | case (Z_lt_dec 0 (outside_interval c d)); intro Ho2;
        [ Falsum
        | case (Z_lt_dec (outside_interval c d) 0); intro Ho2';
           [ reflexivity | Falsum ] ] ]
  | Falsum ].
Defined.


Lemma Qhomographic_sign_dL_4 :
 forall (a b c d : Z) (p xs : Qpositive)
   (H_Qhomographic_sg_denom_nonzero : Qhomographic_sg_denom_nonzero 
                                        (c + d) d xs)
   (H_Qhomographic_sg_denom_nonzero_dL : Qhomographic_sg_denom_nonzero c d
                                           (dL xs)),
 b = 0%Z ->
 d <> 0%Z ->
 ~ (0 < outside_interval c d)%Z ->
 ~ (outside_interval c d < 0)%Z ->
 Qhomographic_sign a b c d (dL xs) H_Qhomographic_sg_denom_nonzero_dL =
 Qhomographic_sign (a + b) b (c + d) d xs H_Qhomographic_sg_denom_nonzero.
Proof.
 intros; simpl in |- *; case (Z_zerop b); intro Hb;
  [ case (Z_zerop d); intro Hd;
     [ Falsum
     | case (Z_lt_dec 0 (outside_interval c d)); intro Ho2;
        [ Falsum
        | case (Z_lt_dec (outside_interval c d) 0); intro Ho2';
           [ Falsum | apply Qhomographic_sign_equal ] ] ]
  | Falsum ].
Defined.

Lemma Qhomographic_sign_dL_5 :
 forall (a b c d : Z) (p xs : Qpositive)
   (H_Qhomographic_sg_denom_nonzero : Qhomographic_sg_denom_nonzero c d p),
 p = dL xs ->
 b <> 0%Z ->
 d = 0%Z ->
 (0 < outside_interval a b)%Z ->
 Qhomographic_sign a b c d p H_Qhomographic_sg_denom_nonzero =
 (Z.sgn c, (a, (b, (c, d)), p)).
Proof.
 intros; generalize H_Qhomographic_sg_denom_nonzero;
  clear H_Qhomographic_sg_denom_nonzero; rewrite H;
  intros H_Qhomographic_sg_denom_nonzero; simpl in |- *; 
  case (Z_zerop b); intro Hb;
  [ Falsum
  | case (Z_zerop d); intro Hd;
     [ case (Z_lt_dec 0 (outside_interval a b)); intro Ho2;
        [ reflexivity | Falsum ]
     | Falsum ] ].
Defined.

Lemma Qhomographic_sign_dL_6 :
 forall (a b c d : Z) (p xs : Qpositive)
   (H_Qhomographic_sg_denom_nonzero : Qhomographic_sg_denom_nonzero c d p),
 p = dL xs ->
 b <> 0%Z ->
 d = 0%Z ->
 ~ (0 < outside_interval a b)%Z ->
 (outside_interval a b < 0)%Z ->
 Qhomographic_sign a b c d p H_Qhomographic_sg_denom_nonzero =
 ((- Z.sgn c)%Z, (a, (b, (c, d)), p)).
Proof.
 intros; generalize H_Qhomographic_sg_denom_nonzero;
  clear H_Qhomographic_sg_denom_nonzero; rewrite H;
  intros H_Qhomographic_sg_denom_nonzero; simpl in |- *; 
  case (Z_zerop b); intro Hb;
  [ Falsum
  | case (Z_zerop d); intro Hd;
     [ case (Z_lt_dec 0 (outside_interval a b)); intro Ho2;
        [ Falsum
        | case (Z_lt_dec (outside_interval a b) 0); intro Ho2';
           [ reflexivity | Falsum ] ]
     | Falsum ] ].
Defined.

Lemma Qhomographic_sign_dL_7 :
 forall (a b c d : Z) (p xs : Qpositive)
   (H_Qhomographic_sg_denom_nonzero : Qhomographic_sg_denom_nonzero 
                                        (c + d) d xs)
   (H_Qhomographic_sg_denom_nonzero_dL : Qhomographic_sg_denom_nonzero c d
                                           (dL xs)),
 b <> 0%Z ->
 d = 0%Z ->
 ~ (0 < outside_interval a b)%Z ->
 ~ (outside_interval a b < 0)%Z ->
 Qhomographic_sign a b c d (dL xs) H_Qhomographic_sg_denom_nonzero_dL =
 Qhomographic_sign (a + b) b (c + d) d xs H_Qhomographic_sg_denom_nonzero.
Proof.
 intros; simpl in |- *; case (Z_zerop b); intro Hb;
  [ Falsum
  | case (Z_zerop d); intro Hd;
     [ case (Z_lt_dec 0 (outside_interval a b)); intro Ho2;
        [ Falsum
        | case (Z_lt_dec (outside_interval a b) 0); intro Ho2';
           [ Falsum | apply Qhomographic_sign_equal ] ]
     | Falsum ] ].
Defined.


Lemma Qhomographic_sign_dL_8 :
 forall (a b c d : Z) (p xs : Qpositive)
   (H_Qhomographic_sg_denom_nonzero : Qhomographic_sg_denom_nonzero c d p),
 p = dL xs ->
 b <> 0%Z ->
 d <> 0%Z ->
 inside_interval_1 (outside_interval a b) (outside_interval c d) ->
 Qhomographic_sign a b c d p H_Qhomographic_sg_denom_nonzero =
 (1%Z, (a, (b, (c, d)), p)).
Proof.
 intros; generalize H_Qhomographic_sg_denom_nonzero;
  clear H_Qhomographic_sg_denom_nonzero; rewrite H;
  intros H_Qhomographic_sg_denom_nonzero; simpl in |- *; 
  case (Z_zerop b); intro Hb;
  [ Falsum
  | case (Z_zerop d); intro Hd;
     [ Falsum
     | case
        (inside_interval_1_dec_inf (outside_interval a b)
           (outside_interval c d)); intro H_inside_1;
        [ reflexivity | Falsum ] ] ].
Defined.

Lemma Qhomographic_sign_dL_9 :
 forall (a b c d : Z) (p xs : Qpositive)
   (H_Qhomographic_sg_denom_nonzero : Qhomographic_sg_denom_nonzero c d p),
 p = dL xs ->
 b <> 0%Z ->
 d <> 0%Z ->
 ~ inside_interval_1 (outside_interval a b) (outside_interval c d) ->
 inside_interval_2 (outside_interval a b) (outside_interval c d) ->
 Qhomographic_sign a b c d p H_Qhomographic_sg_denom_nonzero =
 ((-1)%Z, (a, (b, (c, d)), p)).
Proof.
 intros; generalize H_Qhomographic_sg_denom_nonzero;
  clear H_Qhomographic_sg_denom_nonzero; rewrite H;
  intros H_Qhomographic_sg_denom_nonzero; simpl in |- *; 
  case (Z_zerop b); intro Hb;
  [ Falsum
  | case (Z_zerop d); intro Hd;
     [ Falsum
     | case
        (inside_interval_1_dec_inf (outside_interval a b)
           (outside_interval c d)); intro H_inside_1;
        [ Falsum
        | case
           (inside_interval_2_dec_inf (outside_interval a b)
              (outside_interval c d)); intro H_inside_2;
           [ reflexivity | Falsum ] ] ] ].
Defined.

Lemma Qhomographic_sign_dL_10 :
 forall (a b c d : Z) (p xs : Qpositive)
   (H_Qhomographic_sg_denom_nonzero : Qhomographic_sg_denom_nonzero 
                                        (c + d) d xs)
   (H_Qhomographic_sg_denom_nonzero_dL : Qhomographic_sg_denom_nonzero c d
                                           (dL xs)),
 b <> 0%Z ->
 d <> 0%Z ->
 ~ inside_interval_1 (outside_interval a b) (outside_interval c d) ->
 ~ inside_interval_2 (outside_interval a b) (outside_interval c d) ->
 Qhomographic_sign a b c d (dL xs) H_Qhomographic_sg_denom_nonzero_dL =
 Qhomographic_sign (a + b) b (c + d) d xs H_Qhomographic_sg_denom_nonzero.
Proof.
 intros; simpl in |- *; case (Z_zerop b); intro Hb;
  [ Falsum
  | case (Z_zerop d); intro Hd;
     [ Falsum
     | case
        (inside_interval_1_dec_inf (outside_interval a b)
           (outside_interval c d)); intro H_inside_1;
        [ Falsum
        | case
           (inside_interval_2_dec_inf (outside_interval a b)
              (outside_interval c d)); intro H_inside_2;
           [ Falsum | apply Qhomographic_sign_equal ] ] ] ].
Defined.


Lemma sg_sign :
 forall (a b c d : Z) (qp : Qpositive)
   (H_Qhomographic_sg_denom_nonzero : Qhomographic_sg_denom_nonzero c d qp),
 let (l1, L2) :=
     Qhomographic_sign a b c d qp H_Qhomographic_sg_denom_nonzero in
 {l1 = 0%Z} + {l1 = 1%Z} + {l1 = (-1)%Z}.
Proof.
 fix sg_sign 5.
 intros.
 (* (nR p) *)

 let T_local :=
  (case (Z_zerop b); intro Hb;
    [ case (Z_zerop d); intro Hd;
       [ match goal with
         | id1:(?X1 ?X2 ?X3 (nR ?X4)) |- ?X5 =>
             rewrite
              (Qhomographic_sign_nR_1 a b c d (nR q) q
                 H_Qhomographic_sg_denom_nonzero (refl_equal (nR q)) Hb Hd)
              
         | id1:(?X1 ?X2 ?X3 (dL ?X4)) |- ?X5 =>
             rewrite
              (Qhomographic_sign_dL_1 a b c d (dL q) q
                 H_Qhomographic_sg_denom_nonzero (refl_equal (dL q)) Hb Hd)
              
         end; generalize a c;
          intros [|pa|pa] [| pc| pc]; 
          simpl in |- *; first
          [ right; reflexivity
          | left; left; reflexivity
          | left; right; reflexivity ]
       | case (Z_lt_dec 0 (outside_interval c d)); intros Ho2;
          [ match goal with
            | id1:(?X1 ?X2 ?X3 (nR ?X4)) |- ?X5 =>
                rewrite
                 (Qhomographic_sign_nR_2 a b c d (nR q) q
                    H_Qhomographic_sg_denom_nonzero 
                    (refl_equal (nR q)) Hb Hd Ho2)
            | id1:(?X1 ?X2 ?X3 (dL ?X4)) |- ?X5 =>
                rewrite
                 (Qhomographic_sign_dL_2 a b c d (dL q) q
                    H_Qhomographic_sg_denom_nonzero 
                    (refl_equal (dL q)) Hb Hd Ho2)
            end; generalize a; intros [| pa| pa]; simpl in |- *; first
             [ right; reflexivity
             | left; left; reflexivity
             | left; right; reflexivity ]
          | case (Z_lt_dec (outside_interval c d) 0); intros Ho2';
             [ match goal with
               | id1:(?X1 ?X2 ?X3 (nR ?X4)) |- ?X5 =>
                   rewrite
                    (Qhomographic_sign_nR_3 a b c d 
                       (nR q) q H_Qhomographic_sg_denom_nonzero
                       (refl_equal (nR q)) Hb Hd Ho2 Ho2')
                    
               | id1:(?X1 ?X2 ?X3 (dL ?X4)) |- ?X5 =>
                   rewrite
                    (Qhomographic_sign_dL_3 a b c d 
                       (dL q) q H_Qhomographic_sg_denom_nonzero
                       (refl_equal (dL q)) Hb Hd Ho2 Ho2')
                    
               end; generalize a; intros [| pa| pa]; 
                simpl in |- *; first
                [ right; reflexivity
                | left; left; reflexivity
                | left; right; reflexivity ]
             | match goal with
               | id1:(?X1 ?X2 ?X3 (nR ?X4)) |- ?X5 =>
                   rewrite
                    (Qhomographic_sign_nR_4 a b c d 
                       (nR q) q
                       (Qhomographic_signok_2 c d q
                          H_Qhomographic_sg_denom_nonzero)
                       H_Qhomographic_sg_denom_nonzero Hb Hd Ho2 Ho2')
                    
               | id1:(?X1 ?X2 ?X3 (dL ?X4)) |- ?X5 =>
                   rewrite
                    (Qhomographic_sign_dL_4 a b c d 
                       (dL q) q
                       (Qhomographic_signok_3 c d q
                          H_Qhomographic_sg_denom_nonzero)
                       H_Qhomographic_sg_denom_nonzero Hb Hd Ho2 Ho2')
                    
               end; apply sg_sign ] ] ]
    | case (Z_zerop d); intro Hd;
       [ case (Z_lt_dec 0 (outside_interval a b)); intros Ho1;
          [ match goal with
            | id1:(?X1 ?X2 ?X3 (nR ?X4)) |- ?X5 =>
                rewrite
                 (Qhomographic_sign_nR_5 a b c d (nR q) q
                    H_Qhomographic_sg_denom_nonzero 
                    (refl_equal (nR q)) Hb Hd Ho1)
            | id1:(?X1 ?X2 ?X3 (dL ?X4)) |- ?X5 =>
                rewrite
                 (Qhomographic_sign_dL_5 a b c d (dL q) q
                    H_Qhomographic_sg_denom_nonzero 
                    (refl_equal (dL q)) Hb Hd Ho1)
            end; generalize c; intros [| pc| pc]; simpl in |- *; first
             [ right; reflexivity
             | left; left; reflexivity
             | left; right; reflexivity ]
          | case (Z_lt_dec (outside_interval a b) 0); intros Ho1';
             [ match goal with
               | id1:(?X1 ?X2 ?X3 (nR ?X4)) |- ?X5 =>
                   rewrite
                    (Qhomographic_sign_nR_6 a b c d 
                       (nR q) q H_Qhomographic_sg_denom_nonzero
                       (refl_equal (nR q)) Hb Hd Ho1 Ho1')
                    
               | id1:(?X1 ?X2 ?X3 (dL ?X4)) |- ?X5 =>
                   rewrite
                    (Qhomographic_sign_dL_6 a b c d 
                       (dL q) q H_Qhomographic_sg_denom_nonzero
                       (refl_equal (dL q)) Hb Hd Ho1 Ho1')
                    
               end; generalize c; intros [| pc| pc]; 
                simpl in |- *; first
                [ right; reflexivity
                | left; left; reflexivity
                | left; right; reflexivity ]
             | match goal with
               | id1:(?X1 ?X2 ?X3 (nR ?X4)) |- ?X5 =>
                   rewrite
                    (Qhomographic_sign_nR_7 a b c d 
                       (nR q) q
                       (Qhomographic_signok_2 c d q
                          H_Qhomographic_sg_denom_nonzero)
                       H_Qhomographic_sg_denom_nonzero Hb Hd Ho1 Ho1')
                    
               | id1:(?X1 ?X2 ?X3 (dL ?X4)) |- ?X5 =>
                   rewrite
                    (Qhomographic_sign_dL_7 a b c d 
                       (dL q) q
                       (Qhomographic_signok_3 c d q
                          H_Qhomographic_sg_denom_nonzero)
                       H_Qhomographic_sg_denom_nonzero Hb Hd Ho1 Ho1')
                    
               end; apply sg_sign ] ]
       | case
          (inside_interval_1_dec_inf (outside_interval a b)
             (outside_interval c d)); intros H_inside_1;
          [ match goal with
            | id1:(?X1 ?X2 ?X3 (nR ?X4)) |- ?X5 =>
                rewrite
                 (Qhomographic_sign_nR_8 a b c d (nR q) q
                    H_Qhomographic_sg_denom_nonzero 
                    (refl_equal (nR q)) Hb Hd H_inside_1)
                 
            | id1:(?X1 ?X2 ?X3 (dL ?X4)) |- ?X5 =>
                rewrite
                 (Qhomographic_sign_dL_8 a b c d (dL q) q
                    H_Qhomographic_sg_denom_nonzero 
                    (refl_equal (dL q)) Hb Hd H_inside_1)
                 
            end; first
             [ right; reflexivity
             | left; left; reflexivity
             | left; right; reflexivity ]
          | case
             (inside_interval_2_dec_inf (outside_interval a b)
                (outside_interval c d)); intros H_inside_2;
             [ match goal with
               | id1:(?X1 ?X2 ?X3 (nR ?X4)) |- ?X5 =>
                   rewrite
                    (Qhomographic_sign_nR_9 a b c d 
                       (nR q) q H_Qhomographic_sg_denom_nonzero
                       (refl_equal (nR q)) Hb Hd H_inside_1 H_inside_2)
                    
               | id1:(?X1 ?X2 ?X3 (dL ?X4)) |- ?X5 =>
                   rewrite
                    (Qhomographic_sign_dL_9 a b c d 
                       (dL q) q H_Qhomographic_sg_denom_nonzero
                       (refl_equal (dL q)) Hb Hd H_inside_1 H_inside_2)
                    
               end; first
                [ right; reflexivity
                | left; left; reflexivity
                | left; right; reflexivity ]
             | match goal with
               | id1:(?X1 ?X2 ?X3 (nR ?X4)) |- ?X5 =>
                   rewrite
                    (Qhomographic_sign_nR_10 a b c d 
                       (nR q) q
                       (Qhomographic_signok_2 c d q
                          H_Qhomographic_sg_denom_nonzero)
                       H_Qhomographic_sg_denom_nonzero Hb Hd H_inside_1
                       H_inside_2)
               | id1:(?X1 ?X2 ?X3 (dL ?X4)) |- ?X5 =>
                   rewrite
                    (Qhomographic_sign_dL_10 a b c d 
                       (dL q) q
                       (Qhomographic_signok_3 c d q
                          H_Qhomographic_sg_denom_nonzero)
                       H_Qhomographic_sg_denom_nonzero Hb Hd H_inside_1
                       H_inside_2)
               end; apply sg_sign ] ] ] ]) in
 (destruct qp as [q| q| ];
   [ T_local
   | T_local
   | case (Z.eq_dec (Z.sgn (a + b)) 0); intro H_ab;
      [ rewrite
         (sg_One_2 a b c d One H_Qhomographic_sg_denom_nonzero
            (refl_equal One) H_ab)
      | case (Z.eq_dec (Z.sgn (a + b)) (Z.sgn (c + d))); intro H_ab_cd;
         [ rewrite
            (sg_One_3 a b c d One H_Qhomographic_sg_denom_nonzero
               (refl_equal One) H_ab H_ab_cd)
         | rewrite
            (sg_One_4 a b c d One H_Qhomographic_sg_denom_nonzero
               (refl_equal One) H_ab H_ab_cd) ] ]; first
      [ right; reflexivity
      | left; left; reflexivity
      | left; right; reflexivity ] ]).
Defined.


Definition h_sign (a b c d : Z) (p : Qpositive)
  (H_Qhomographic_sg_denom_nonzero : Qhomographic_sg_denom_nonzero c d p) :=
  let (l1, L2) :=
      Qhomographic_sign a b c d p H_Qhomographic_sg_denom_nonzero in
  l1.


Lemma sg_sign_dec :
 forall (a b c d : Z) (p : Qpositive)
   (H_Qhomographic_sg_denom_nonzero : Qhomographic_sg_denom_nonzero c d p),
 {h_sign a b c d p H_Qhomographic_sg_denom_nonzero = 0%Z} +
 {h_sign a b c d p H_Qhomographic_sg_denom_nonzero = 1%Z} +
 {h_sign a b c d p H_Qhomographic_sg_denom_nonzero = (-1)%Z}.
Proof.
 intros.
 unfold h_sign in |- *.
 generalize (sg_sign a b c d p H_Qhomographic_sg_denom_nonzero).
 case (Qhomographic_sign a b c d p H_Qhomographic_sg_denom_nonzero).
 intros l1 L2.
 trivial.
Defined.


