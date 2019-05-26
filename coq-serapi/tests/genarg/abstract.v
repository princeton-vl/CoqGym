Require Import ZArith.

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

Inductive Qpositive : Set :=
  | nR : Qpositive -> Qpositive
  | dL : Qpositive -> Qpositive
  | One : Qpositive.

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
