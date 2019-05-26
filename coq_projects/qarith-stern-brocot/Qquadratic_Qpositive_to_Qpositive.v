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



Require Import Merge_Order.
Require Export Qhomographic_Qpositive_to_Qpositive.

Definition quadratic_top_more (a b c d e f g h : Z) :=
  (e <= a)%Z /\ (f <= b)%Z /\ (g <= c)%Z /\ (h < d)%Z \/
  (e <= a)%Z /\ (f <= b)%Z /\ (g < c)%Z /\ (h <= d)%Z \/
  (e <= a)%Z /\ (f < b)%Z /\ (g <= c)%Z /\ (h <= d)%Z \/
  (e < a)%Z /\ (f <= b)%Z /\ (g <= c)%Z /\ (h <= d)%Z.

Lemma octet_leq_inf :
 forall a b c d e f g h : Z,
 {(e <= a)%Z /\ (f <= b)%Z /\ (g <= c)%Z /\ (h <= d)%Z} +
 {~ ((e <= a)%Z /\ (f <= b)%Z /\ (g <= c)%Z /\ (h <= d)%Z)}.
Proof.
 intros.
 case (Z_le_dec e a); intros;
  [ case (Z_le_dec f b); intros;
     [ case (Z_le_dec g c); intros;
        [ case (Z_le_dec h d);
           [ intros; left; repeat (split; try assumption) | intros; right ]
        | intros; right ]
     | intros; right ]
  | intros; right ]; (intros (H0, (H1, (H2, H3))); Falsum). 
Defined.


Lemma quadratic_top_more_informative :
 forall a b c d e f g h : Z,
 {quadratic_top_more a b c d e f g h} +
 {~ quadratic_top_more a b c d e f g h}.
Proof.
 intros.
 unfold quadratic_top_more in |- *.
 case (octet_leq_inf a b c d e f g h);
  [ idtac
  | right; red in |- *;
     intros
      [(H, (H1, (H2, H3)))|
       [(H, (H1, (H2, H3)))| [(H, (H1, (H2, H3)))| (H, (H1, (H2, H3)))]]];
     apply n; repeat split; assumption || (apply Zlt_le_weak; assumption) ].

 intros (H, (H1, (H2, H3))).
 case (Z_le_lt_eq_dec e a H);
  [ intro; left; repeat right; repeat split; assumption
  | intro; case (Z_le_lt_eq_dec f b H1);
     [ intro; left; do 2 right; left; repeat split; assumption
     | intro; case (Z_le_lt_eq_dec g c H2);
        [ intro; left; right; left; repeat split; assumption
        | intro; case (Z_le_lt_eq_dec h d H3);
           [ intro; repeat left; repeat split; assumption
           | intro; clear H H1 H2 H3; right; red in |- *;
              intros
               [(H, (H1, (H2, H3)))|
                [(H, (H1, (H2, H3)))|
                 [(H, (H1, (H2, H3)))| (H, (H1, (H2, H3)))]]];
              [ rewrite e3 in H3; apply Z.lt_irrefl with d; assumption
              | rewrite e2 in H2; apply Z.lt_irrefl with c; assumption
              | rewrite e1 in H1; apply Z.lt_irrefl with b; assumption
              | rewrite e0 in H; apply Z.lt_irrefl with a; assumption ] ] ] ] ].
Defined.

Lemma quadratic_top_more_1 :
 forall a b c d e f g h : Z,
 quadratic_top_more a b c d e f g h ->
 (0 < a - e + (b - f) + (c - g) + (d - h))%Z.
Proof.
 intros.
 case H;
  [ intros (Hea, (Hfb, (Hgc, Hhd)))
  | intros
     [(Hea, (Hfb, (Hgc, Hhd)))|
      [(Hea, (Hfb, (Hgc, Hhd)))| (Hea, (Hfb, (Hgc, Hhd)))]] ];
  replace 0%Z with (0 + 0 + 0 + 0)%Z;
  [ apply Zplus_le_lt_compat; [ repeat simple apply Zplus_le_0_compat | idtac ]
  | constructor
  | apply Zplus_lt_le_compat;
     [ apply Zplus_le_lt_compat; try apply Zplus_le_0_compat | idtac ]
  | constructor
  | apply Zplus_lt_le_compat;
     [ apply Zplus_lt_le_compat; [ apply Zplus_le_lt_compat | idtac ]
     | idtac ]
  | constructor
  | repeat apply Zplus_lt_le_compat
  | constructor ]; apply Zle_minus || apply Zaux.Zlt_minus; 
  assumption.
Qed.

Lemma quadratic_top_more_2 :
 forall a b c d e f g h : Z,
 quadratic_top_more a b c d e f g h -> (e + f + g + h < a + b + c + d)%Z.
Proof.
intros.
 case H;
  [ intros (Hea, (Hfb, (Hgc, Hhd)))
  | intros
     [(Hea, (Hfb, (Hgc, Hhd)))|
      [(Hea, (Hfb, (Hgc, Hhd)))| (Hea, (Hfb, (Hgc, Hhd)))]] ];
  [ apply Zplus_le_lt_compat; [ repeat apply Zplus_le_compat | idtac ]
  | apply Zplus_lt_le_compat;
     [ apply Zplus_le_lt_compat; try apply Zplus_le_compat | idtac ]
  | apply Zplus_lt_le_compat;
     [ apply Zplus_lt_le_compat; [ apply Zplus_le_lt_compat | idtac ]
     | idtac ]
  | repeat apply Zplus_lt_le_compat ]; assumption.
Qed.

Lemma quadratic_top_more_3 :
 forall a b c d e f g h : Z,
 (0 < e + f + g + h)%Z ->
 (a - e + (b - f) + (c - g) + (d - h) < a + b + c + d)%Z.
Proof.
 intros.
 apply Zplus_lt_reg_l with (e + f + g + h)%Z.
 apply Zplus_lt_reg_l with (- a - b - c - d)%Z.
 replace
  (- a - b - c - d + (e + f + g + h + (a - e + (b - f) + (c - g) + (d - h))))%Z
  with 0%Z.
 replace (- a - b - c - d + (e + f + g + h + (a + b + c + d)))%Z with
  (e + f + g + h)%Z.
 assumption.
 abstract ring.
 abstract ring.
Qed.

Lemma quadratic_top_more_4_1 :
 forall a b c d e f g h : Z, quadratic_top_more a b c d e f g h -> (e <= a)%Z.
Proof.
 intros.
 case H;
  [ intros (Hea, (Hfb, (Hgc, Hhd)))
  | intros
     [(Hea, (Hfb, (Hgc, Hhd)))|
      [(Hea, (Hfb, (Hgc, Hhd)))| (Hea, (Hfb, (Hgc, Hhd)))]] ];
  assumption || (apply Zlt_le_weak; assumption).
Qed.

Lemma quadratic_top_more_4_2 :
 forall a b c d e f g h : Z, quadratic_top_more a b c d e f g h -> (f <= b)%Z.
Proof.
 intros.
 case H;
  [ intros (Hea, (Hfb, (Hgc, Hhd)))
  | intros
     [(Hea, (Hfb, (Hgc, Hhd)))|
      [(Hea, (Hfb, (Hgc, Hhd)))| (Hea, (Hfb, (Hgc, Hhd)))]] ];
  assumption || (apply Zlt_le_weak; assumption).
Qed.

Lemma quadratic_top_more_4_3 :
 forall a b c d e f g h : Z, quadratic_top_more a b c d e f g h -> (g <= c)%Z.
Proof.
 intros.
 case H;
  [ intros (Hea, (Hfb, (Hgc, Hhd)))
  | intros
     [(Hea, (Hfb, (Hgc, Hhd)))|
      [(Hea, (Hfb, (Hgc, Hhd)))| (Hea, (Hfb, (Hgc, Hhd)))]] ];
  assumption || (apply Zlt_le_weak; assumption).
Qed.

Lemma quadratic_top_more_4_4 :
 forall a b c d e f g h : Z, quadratic_top_more a b c d e f g h -> (h <= d)%Z.
Proof.
 intros.
 case H;
  [ intros (Hea, (Hfb, (Hgc, Hhd)))
  | intros
     [(Hea, (Hfb, (Hgc, Hhd)))|
      [(Hea, (Hfb, (Hgc, Hhd)))| (Hea, (Hfb, (Hgc, Hhd)))]] ];
  assumption || (apply Zlt_le_weak; assumption).
Qed.

Lemma quadratic_top_more_5 :
 forall a b c d e f g h : Z,
 (0 < e + f + g + h)%Z ->
 (a - e + (b - f) + (c - g) + (d - h) + e + f + g + h <
  a + b + c + d + e + f + g + h)%Z.
Proof.
 intros. 
 assert
  ((a - e + (b - f) + (c - g) + (d - h) + e + f + g + h)%Z =
   (a + b + c + d + 0)%Z).
 abstract ring.
 rewrite H0.
 repeat rewrite Zplus_assoc_reverse with (n := (a + b + c + d)%Z).
 apply Zplus_le_lt_compat.  
 apply Z.le_refl.
 assumption.
Qed.

Lemma quadratic_top_more_5' :
 forall a b c d e f g h : Z,
 (0 < a + b + c + d)%Z ->
 (a + b + c + d + (e - a) + (f - b) + (g - c) + (h - d) <
  a + b + c + d + e + f + g + h)%Z.
 intros. 
 assert
  ((a + b + c + d + (e - a) + (f - b) + (g - c) + (h - d))%Z =
   (0 + e + f + g + h)%Z).
 abstract ring.
 rewrite H0.
 repeat rewrite Zplus_assoc_reverse with (n := (a + b + c + d)%Z).
 repeat rewrite Zplus_assoc_reverse with (n := 0%Z).
 apply Zplus_lt_le_compat.  
 assumption.
 apply Z.le_refl.
Qed.


Inductive quadraticAcc :
Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Qpositive -> Qpositive -> Prop :=
  | quadraticacc0 :
      forall (a b c d e f g h : Z) (p1 p2 : Qpositive),
      p1 = One ->
      homographicAcc (a + c) (b + d) (e + g) (f + h) p2 ->
      quadraticAcc a b c d e f g h p1 p2
  | quadraticacc0' :
      forall (a b c d e f g h : Z) (p1 p2 : Qpositive),
      p1 <> One ->
      p2 = One ->
      homographicAcc (a + b) (c + d) (e + f) (g + h) p1 ->
      quadraticAcc a b c d e f g h p1 p2
  | quadraticacc1 :
      forall (a b c d e f g h : Z) (p1 p2 : Qpositive),
      p1 <> One ->
      p2 <> One ->
      quadratic_top_more a b c d e f g h ->
      quadraticAcc (a - e)%Z (b - f)%Z (c - g)%Z (d - h)%Z e f g h p1 p2 ->
      quadraticAcc a b c d e f g h p1 p2
  | quadraticacc2 :
      forall (a b c d e f g h : Z) (p1 p2 : Qpositive),
      p1 <> One ->
      p2 <> One ->
      ~ quadratic_top_more a b c d e f g h ->
      quadratic_top_more e f g h a b c d ->
      quadraticAcc a b c d (e - a)%Z (f - b)%Z (g - c)%Z (h - d)%Z p1 p2 ->
      quadraticAcc a b c d e f g h p1 p2
  | quadraticacc3_II :
      forall (a b c d e f g h : Z) (xs ys : Qpositive),
      ~ quadratic_top_more a b c d e f g h ->
      ~ quadratic_top_more e f g h a b c d ->
      quadraticAcc a (a + b)%Z (a + c)%Z (a + b + c + d)%Z e 
        (e + f)%Z (e + g)%Z (e + f + g + h)%Z xs ys ->
      quadraticAcc a b c d e f g h (nR xs) (nR ys)
  | quadraticacc3_IO :
      forall (a b c d e f g h : Z) (xs ys : Qpositive),
      ~ quadratic_top_more a b c d e f g h ->
      ~ quadratic_top_more e f g h a b c d ->
      quadraticAcc (a + b)%Z b (a + b + c + d)%Z (b + d)%Z 
        (e + f)%Z f (e + f + g + h)%Z (f + h)%Z xs ys ->
      quadraticAcc a b c d e f g h (nR xs) (dL ys)
  | quadraticacc3_OI :
      forall (a b c d e f g h : Z) (xs ys : Qpositive),
      ~ quadratic_top_more a b c d e f g h ->
      ~ quadratic_top_more e f g h a b c d ->
      quadraticAcc (a + c)%Z (a + b + c + d)%Z c (c + d)%Z 
        (e + g)%Z (e + f + g + h)%Z g (g + h)%Z xs ys ->
      quadraticAcc a b c d e f g h (dL xs) (nR ys)
  | quadraticacc3_OO :
      forall (a b c d e f g h : Z) (xs ys : Qpositive),
      ~ quadratic_top_more a b c d e f g h ->
      ~ quadratic_top_more e f g h a b c d ->
      quadraticAcc (a + b + c + d)%Z (b + d)%Z (c + d)%Z d 
        (e + f + g + h)%Z (f + h)%Z (g + h)%Z h xs ys ->
      quadraticAcc a b c d e f g h (dL xs) (dL ys).

Lemma quadraticacc_0 :
 forall (a b c d e f g h : Z) (p1 p2 : Qpositive),
 quadraticAcc a b c d e f g h p1 p2 ->
 p1 = One -> homographicAcc (a + c) (b + d) (e + g) (f + h) p2.
Proof.
 intros; inversion H; trivial; try solve [ Falsum ]; rewrite H0 in H12;
  discriminate H12.
Defined.

Lemma quadraticacc_0' :
 forall (a b c d e f g h : Z) (p1 p2 : Qpositive),
 quadraticAcc a b c d e f g h p1 p2 ->
 p1 <> One -> p2 = One -> homographicAcc (a + b) (c + d) (e + f) (g + h) p1.
Proof.
 intros; inversion H; trivial; try solve [ Falsum ]; rewrite H1 in H14;
  discriminate H14.
Defined.

Lemma quadraticacc_1 :
 forall (a b c d e f g h : Z) (p1 p2 : Qpositive),
 quadraticAcc a b c d e f g h p1 p2 ->
 p1 <> One ->
 p2 <> One ->
 quadratic_top_more a b c d e f g h ->
 quadraticAcc (a - e) (b - f) (c - g) (d - h) e f g h p1 p2.
Proof.
 simple destruct 1; intros; trivial; try solve [ Falsum ].
Defined.

Lemma quadraticacc_2 :
 forall (a b c d e f g h : Z) (p1 p2 : Qpositive),
 quadraticAcc a b c d e f g h p1 p2 ->
 p1 <> One ->
 p2 <> One ->
 ~ quadratic_top_more a b c d e f g h ->
 quadratic_top_more e f g h a b c d ->
 quadraticAcc a b c d (e - a) (f - b) (g - c) (h - d) p1 p2.
Proof.
 simple destruct 1; intros; trivial; try solve [ Falsum ].
Defined.

Lemma quadraticacc_3_II :
 forall (a b c d e f g h : Z) (p1 p2 : Qpositive),
 quadraticAcc a b c d e f g h p1 p2 ->
 forall xs ys : Qpositive,
 p1 = nR xs ->
 p2 = nR ys ->
 ~ quadratic_top_more a b c d e f g h ->
 ~ quadratic_top_more e f g h a b c d ->
 quadraticAcc a (a + b) (a + c) (a + b + c + d) e (e + f) 
   (e + g) (e + f + g + h) xs ys.
Proof.
 simple destruct 1; intros; try solve [ Falsum ];
  match goal with
  | id1:(dL _ = nR _) |- _ => discriminate id1
  | id1:(nR _ = dL _) |- _ => discriminate id1
  | id1:_ |- _ => idtac
  end;
  (rewrite H0 in H2; discriminate H2) ||
    (rewrite H1 in H4; discriminate H4) ||
      (try
        let T_local1 := eval compute in (f_equal Qpositive_tail H3) in
        let T_local2 := eval compute in (f_equal Qpositive_tail H4) in
        (rewrite <- T_local1; rewrite <- T_local2; assumption)).
Defined.

Lemma quadraticacc_3_IO :
 forall (a b c d e f g h : Z) (p1 p2 : Qpositive),
 quadraticAcc a b c d e f g h p1 p2 ->
 forall xs ys : Qpositive,
 p1 = nR xs ->
 p2 = dL ys ->
 ~ quadratic_top_more a b c d e f g h ->
 ~ quadratic_top_more e f g h a b c d ->
 quadraticAcc (a + b) b (a + b + c + d) (b + d) (e + f) f 
   (e + f + g + h) (f + h) xs ys.
Proof.
 simple destruct 1; intros; try solve [ Falsum ];
  match goal with
  | id1:(dL _ = nR _) |- _ => discriminate id1
  | id1:(nR _ = dL _) |- _ => discriminate id1
  | id1:_ |- _ => idtac
  end;
  (rewrite H0 in H2; discriminate H2) ||
    (rewrite H1 in H4; discriminate H4) ||
      (try
        let T_local1 := eval compute in (f_equal Qpositive_tail H3) in
        let T_local2 := eval compute in (f_equal Qpositive_tail H4) in
        (rewrite <- T_local1; rewrite <- T_local2; assumption)).
Defined.

Lemma quadraticacc_3_OI :
 forall (a b c d e f g h : Z) (p1 p2 : Qpositive),
 quadraticAcc a b c d e f g h p1 p2 ->
 forall xs ys : Qpositive,
 p1 = dL xs ->
 p2 = nR ys ->
 ~ quadratic_top_more a b c d e f g h ->
 ~ quadratic_top_more e f g h a b c d ->
 quadraticAcc (a + c) (a + b + c + d) c (c + d) (e + g) 
   (e + f + g + h) g (g + h) xs ys.
Proof.
 simple destruct 1; intros; try solve [ Falsum ];
  match goal with
  | id1:(dL _ = nR _) |- _ => discriminate id1
  | id1:(nR _ = dL _) |- _ => discriminate id1
  | id1:_ |- _ => idtac
  end;
  (rewrite H0 in H2; discriminate H2) ||
    (rewrite H1 in H4; discriminate H4) ||
      (try
        let T_local1 := eval compute in (f_equal Qpositive_tail H3) in
        let T_local2 := eval compute in (f_equal Qpositive_tail H4) in
        (rewrite <- T_local1; rewrite <- T_local2; assumption)).
Defined.

Lemma quadraticacc_3_OO :
 forall (a b c d e f g h : Z) (p1 p2 : Qpositive),
 quadraticAcc a b c d e f g h p1 p2 ->
 forall xs ys : Qpositive,
 p1 = dL xs ->
 p2 = dL ys ->
 ~ quadratic_top_more a b c d e f g h ->
 ~ quadratic_top_more e f g h a b c d ->
 quadraticAcc (a + b + c + d) (b + d) (c + d) d (e + f + g + h) 
   (f + h) (g + h) h xs ys.
Proof.
 simple destruct 1; intros; try solve [ Falsum ];
  match goal with
  | id1:(dL _ = nR _) |- _ => discriminate id1
  | id1:(nR _ = dL _) |- _ => discriminate id1
  | id1:_ |- _ => idtac
  end;
  (rewrite H0 in H2; discriminate H2) ||
    (rewrite H1 in H4; discriminate H4) ||
      (try
        let T_local1 := eval compute in (f_equal Qpositive_tail H3) in
        let T_local2 := eval compute in (f_equal Qpositive_tail H4) in
        (rewrite <- T_local1; rewrite <- T_local2; assumption)).
Defined.


Fixpoint Qquadratic_Qpositive_to_Qpositive (a b c d e f g h : Z)
 (p1 p2 : Qpositive) (hyp : quadraticAcc a b c d e f g h p1 p2) {struct hyp} 
   : Qpositive :=
  match Qpositive_dec_One p1 with
  | left Hp1 =>
      Qhomographic_Qpositive_to_Qpositive (a + c) (b + d) 
        (e + g) (f + h) p2 (quadraticacc_0 a b c d e f g h p1 p2 hyp Hp1)
  | right Hp1 =>
      match Qpositive_dec_One p2 with
      | left Hp2 =>
          Qhomographic_Qpositive_to_Qpositive (a + b) 
            (c + d) (e + f) (g + h) p1
            (quadraticacc_0' a b c d e f g h p1 p2 hyp Hp1 Hp2)
      | right Hp2 =>
          match quadratic_top_more_informative a b c d e f g h with
          | left Habcdefgh =>
              nR
                (Qquadratic_Qpositive_to_Qpositive 
                   (a - e)%Z (b - f)%Z (c - g)%Z (d - h)%Z e f g h p1 p2
                   (quadraticacc_1 a b c d e f g h p1 p2 hyp Hp1 Hp2
                      Habcdefgh))
          | right Habcdefgh =>
              match quadratic_top_more_informative e f g h a b c d with
              | left Hefghabcd =>
                  dL
                    (Qquadratic_Qpositive_to_Qpositive a b c d 
                       (e - a)%Z (f - b)%Z (g - c)%Z 
                       (h - d)%Z p1 p2
                       (quadraticacc_2 a b c d e f g h p1 p2 hyp Hp1 Hp2
                          Habcdefgh Hefghabcd))
              | right Hefghabcd =>
                  match p1 as q return (p1 = q -> Qpositive) with
                  | nR x =>
                      match
                        p2 as q
                        return
                          (p2 = q ->
                           forall q0 : Qpositive, p1 = nR q0 -> Qpositive)
                      with
                      | nR ys =>
                          fun (Hys : p2 = nR ys) (xs : Qpositive)
                            (Hxs : p1 = nR xs) =>
                          Qquadratic_Qpositive_to_Qpositive a 
                            (a + b)%Z (a + c)%Z (a + b + c + d)%Z e 
                            (e + f)%Z (e + g)%Z (e + f + g + h)%Z xs ys
                            (quadraticacc_3_II a b c d e f g h p1 p2 hyp xs
                               ys Hxs Hys Habcdefgh Hefghabcd)
                      | dL ys =>
                          fun (Hys : p2 = dL ys) (xs : Qpositive)
                            (Hxs : p1 = nR xs) =>
                          Qquadratic_Qpositive_to_Qpositive 
                            (a + b)%Z b (a + b + c + d)%Z 
                            (b + d)%Z (e + f)%Z f (e + f + g + h)%Z 
                            (f + h)%Z xs ys
                            (quadraticacc_3_IO a b c d e f g h p1 p2 hyp xs
                               ys Hxs Hys Habcdefgh Hefghabcd)
                      | One =>
                          fun Hp2_ : p2 = One =>
                          False_rec
                            (forall q : Qpositive, p1 = nR q -> Qpositive)
                            (False_ind False (Hp2 Hp2_))
                      end (refl_equal p2) x
                  | dL x =>
                      match
                        p2 as q
                        return
                          (p2 = q ->
                           forall q0 : Qpositive, p1 = dL q0 -> Qpositive)
                      with
                      | nR ys =>
                          fun (Hys : p2 = nR ys) (xs : Qpositive)
                            (Hxs : p1 = dL xs) =>
                          Qquadratic_Qpositive_to_Qpositive 
                            (a + c)%Z (a + b + c + d)%Z c 
                            (c + d)%Z (e + g)%Z (e + f + g + h)%Z g 
                            (g + h)%Z xs ys
                            (quadraticacc_3_OI a b c d e f g h p1 p2 hyp xs
                               ys Hxs Hys Habcdefgh Hefghabcd)
                      | dL ys =>
                          fun (Hys : p2 = dL ys) (xs : Qpositive)
                            (Hxs : p1 = dL xs) =>
                          Qquadratic_Qpositive_to_Qpositive 
                            (a + b + c + d)%Z (b + d)%Z 
                            (c + d)%Z d (e + f + g + h)%Z 
                            (f + h)%Z (g + h)%Z h xs ys
                            (quadraticacc_3_OO a b c d e f g h p1 p2 hyp xs
                               ys Hxs Hys Habcdefgh Hefghabcd)
                      | One =>
                          fun Hp2_ : p2 = One =>
                          False_rec
                            (forall q : Qpositive, p1 = dL q -> Qpositive)
                            (False_ind False (Hp2 Hp2_))
                      end (refl_equal p2) x
                  | One =>
                      fun Hp1_ : p1 = One =>
                      False_rec Qpositive (False_ind False (Hp1 Hp1_))
                  end (refl_equal p1)
              end
          end
      end
  end.


(** The interactive version of the above definition :
Definition Qquadratic_Qpositive_to_Qpositive [a,b,c,d,e,f,g,h:Z; p1,p2:Qpositive; hyp:(quadraticAcc a b c d e f g h p1 p2)]:Qpositive.
Refine (Fix Qquadratic_Qpositive_to_Qpositive { Qquadratic_Qpositive_to_Qpositive[a,b,c,d,e,f,g,h:Z; p1,p2:Qpositive; hyp:(quadraticAcc a b c d e f g h p1 p2)]:Qpositive:=?}). 
Case (Qpositive_dec_One p1);
Intro Hp1.
 Exact (Qhomographic_Qpositive_to_Qpositive `a+c` `b+d` `e+g` `f+h` p2 (quadraticacc_0 ?????????? hyp Hp1)). 
 Case (Qpositive_dec_One p2);
 Intro Hp2.
  Exact (Qhomographic_Qpositive_to_Qpositive `a+b` `c+d` `e+f` `g+h` p1 (quadraticacc_0' ?????????? hyp Hp1 Hp2)). 
  Case (quadratic_top_more_informative a b c d e f g h);
  Intro Habcdefgh. 
   Exact (nR (Qquadratic_Qpositive_to_Qpositive `a-e` `b-f` `c-g` `d-h` e f g h p1 p2 (quadraticacc_1 ?????????? hyp Hp1 Hp2 Habcdefgh))).
   Case (quadratic_top_more_informative e f g h a b c d);
   Intro Hefghabcd.
    Exact (dL (Qquadratic_Qpositive_to_Qpositive a b c d `e-a` `f-b` `g-c` `h-d` p1 p2 (quadraticacc_2 ?????????? hyp Hp1 Hp2 Habcdefgh Hefghabcd))).
    CaseEq p1; [ Idtac | Idtac| Intro Hp1_; Apply False_rec; Falsum]; 
    CaseEq p2.
      Intros ys Hys xs Hxs.
      Refine (Qquadratic_Qpositive_to_Qpositive a `a+b` `a+c` `a+b+c+d` e `e+f` `e+g` `e+f+g+h` xs ys ?).
      Apply (quadraticacc_3_II ?????????? hyp ?? Hxs Hys Habcdefgh Hefghabcd).
      Intros ys Hys xs Hxs.
      Refine (Qquadratic_Qpositive_to_Qpositive `a+b` b `a+b+c+d` `b+d` `e+f` f `e+f+g+h` `f+h` xs ys ?).
      Apply (quadraticacc_3_IO ?????????? hyp ?? Hxs Hys Habcdefgh Hefghabcd).
      Intro Hp2_; Apply False_rec; Falsum.

      Intros ys Hys xs Hxs.
      Refine (Qquadratic_Qpositive_to_Qpositive `a+c` `a+b+c+d` c `c+d` `e+g` `e+f+g+h` g `g+h` xs ys ?).
      Apply (quadraticacc_3_OI ?????????? hyp ?? Hxs Hys Habcdefgh Hefghabcd).
      Intros ys Hys xs Hxs.
      Refine (Qquadratic_Qpositive_to_Qpositive `a+b+c+d` `b+d` `c+d` d `e+f+g+h` `f+h` `g+h` h xs ys ?).
      Apply (quadraticacc_3_OO ?????????? hyp ?? Hxs Hys Habcdefgh Hefghabcd).
      Intro Hp2_; Apply False_rec; Falsum.
Qed.
*)




Definition octet_lt (a b c d e f g h : Z) (p1 p2 : Qpositive)
  (a' b' c' d' e' f' g' h' : Z) (p1' p2' : Qpositive) : Prop :=
  bin_lt p1 p1' \/
  p1 = p1' /\
  (a + b + c + d + e + f + g + h < a' + b' + c' + d' + e' + f' + g' + h')%Z. 



Definition octointegral_lt (a b c d e f g h a' b' c' d' e' f' g' h' : Z) :=
  (a + b + c + d + e + f + g + h < a' + b' + c' + d' + e' + f' + g' + h')%Z.

Definition octointegral_eq (a b c d e f g h a' b' c' d' e' f' g' h' : Z) :=
  a = a' /\
  b = b' /\ c = c' /\ d = d' /\ e = e' /\ f = f' /\ g = g' /\ h = h'.




Record Z8 : Set := 
  {z8crr :> Z * Z * (Z * Z) * (Z * Z * (Z * Z));
   z8prf :
    (0 <= fst (fst (fst z8crr)))%Z /\
    (0 <= snd (fst (fst z8crr)))%Z /\
    (0 <= fst (snd (fst z8crr)))%Z /\
    (0 <= snd (snd (fst z8crr)))%Z /\
    (0 <= fst (fst (snd z8crr)))%Z /\
    (0 <= snd (fst (snd z8crr)))%Z /\
    (0 <= fst (snd (snd z8crr)))%Z /\ (0 <= snd (snd (snd z8crr)))%Z}.


Definition Z8_lt : Z8 -> Z8 -> Prop.
intros x y.
case (z8crr x).
intros W1 W2.
case (z8crr y).
intros W3 W4.
case W1.
intros V1 V2.
case W2.
intros V3 V4.
case W3.
intros U1 U2.
case W4.
intros U3 U4.
case V1.
intros a b.
case V2.
intros c d.
case V3.
intros e f.
case V4.
intros g h.
case U1.
intros a' b'.
case U2.
intros c' d'.
case U3.
intros e' f'.
case U4.
intros g' h'.
exact (octointegral_lt a b c d e f g h a' b' c' d' e' f' g' h').
Defined.



Definition Z8_eq : Z8 -> Z8 -> Prop.
intros x y.
case (z8crr x).
intros W1 W2.
case (z8crr y).
intros W3 W4.
case W1.
intros V1 V2.
case W2.
intros V3 V4.
case W3.
intros U1 U2.
case W4.
intros U3 U4.
case V1.
intros a b.
case V2.
intros c d.
case V3.
intros e f.
case V4.
intros g h.
case U1.
intros a' b'.
case U2.
intros c' d'.
case U3.
intros e' f'.
case U4.
intros g' h'.
exact (octointegral_eq a b c d e f g h a' b' c' d' e' f' g' h').
Defined.


Lemma Z8_lt_is_irreflexive : forall x : Z8, ~ Z8_lt x x.
Proof.
 intros ((((a, b), (c, d)), ((e, f), (g, h))), z8prf0).
 unfold Z8_lt in |- *. 
 unfold octointegral_lt in |- *.
 simpl in |- *.
 apply Z.lt_irrefl. 
Qed.


Lemma Z8_lt_is_transitive :
 forall x y z : Z8, Z8_lt x y -> Z8_lt y z -> Z8_lt x z.
Proof.
 intros ((((a, b), (c, d)), ((e, f), (g, h))), z8prf0)
  ((((a', b'), (c', d')), ((e', f'), (g', h'))), z8prf1)
  ((((a2, b2), (c2, d2)), ((e2, f2), (g2, h2))), z8prf2).
 unfold Z8_lt in |- *. 
 unfold octointegral_lt in |- *.
 simpl in |- *.
 intros.
 apply Z.lt_trans with (a' + b' + c' + d' + e' + f' + g' + h')%Z; assumption.
Qed.



Lemma Z8_lt_is_order : is_order Z8 Z8_lt.
Proof.
 split.
 apply Z8_lt_is_irreflexive.
 apply Z8_lt_is_transitive.
Qed.


Lemma Z8_eq_is_reflexive : forall x : Z8, Z8_eq x x.
Proof.
 intros ((((a, b), (c, d)), ((e, f), (g, h))), z8prf0).
 unfold Z8_eq in |- *.
 unfold octointegral_eq in |- *; repeat split.
Qed.

Lemma Z8_eq_is_symmetric : forall x y : Z8, Z8_eq x y -> Z8_eq y x.
Proof.
 intros ((((a, b), (c, d)), ((e, f), (g, h))), z8prf0)
  ((((a', b'), (c', d')), ((e', f'), (g', h'))), z8prf1).
 unfold Z8_eq in |- *.
 unfold octointegral_eq in |- *.
 intros (H1, (H2, (H3, (H4, (H5, (H6, (H7, H8))))))); repeat split;
  symmetry  in |- *; assumption.
Qed.

Lemma Z8_eq_is_transitive :
 forall x y z : Z8, Z8_eq x y -> Z8_eq y z -> Z8_eq x z.
Proof.
 intros ((((a, b), (c, d)), ((e, f), (g, h))), z8prf0)
  ((((a', b'), (c', d')), ((e', f'), (g', h'))), z8prf1)
  ((((a2, b2), (c2, d2)), ((e2, f2), (g2, h2))), z8prf2).
 unfold Z8_eq in |- *. 
 unfold octointegral_eq in |- *.
 simpl in |- *.
 clear z8prf0 z8prf1 z8prf2.
 intros (H1, (H2, (H3, (H4, (H5, (H6, (H7, H8)))))))
  (H9, (H10, (H11, (H12, (H13, (H14, (H15, H16))))))); 
  repeat split;
  match goal with
  | id12:(?X1 = ?X2),id23:(?X2 = ?X3) |- (?X1 = ?X3) =>
      try apply (trans_eq id12 id23)
  end.
Qed.

 
Lemma Z8_eq_is_equality : is_equality Z8 Z8_eq.
Proof.
 split.
 apply Z8_eq_is_reflexive.
 split.
 apply Z8_eq_is_symmetric.
 apply Z8_eq_is_transitive.
Qed.


Lemma Z8_lt_is_wf : wf_ind Z8 Z8_lt.
Proof.
 red in |- *.
 intros P H ((((a, b), (c, d)), ((e, f), (g, h))), p); revert p. 
 simpl in |- *.
 intros (Ha, (Hb, (Hc, (Hd, (He, (Hf, (Hg, Hh))))))).
 assert (H_a_b_c_d_e_f_g_h : (0 <= a + b + c + d + e + f + g + h)%Z);
  repeat apply Zplus_le_0_compat; try assumption.
 set
  (P8 :=
   fun k : Z_pos =>
   forall (a b c d e f g h : Z)
     (Habcdefgh : (0 <= a)%Z /\
                  (0 <= b)%Z /\
                  (0 <= c)%Z /\
                  (0 <= d)%Z /\
                  (0 <= e)%Z /\ (0 <= f)%Z /\ (0 <= g)%Z /\ (0 <= h)%Z)
     (Hk : zposcrr k = (a + b + c + d + e + f + g + h)%Z),
   P (Build_Z8 (a, b, (c, d), (e, f, (g, h))) Habcdefgh)) 
  in *.

 assert (P8 (Build_Z_pos (a + b + c + d + e + f + g + h) H_a_b_c_d_e_f_g_h)).

 apply Z_pos_lt_is_wf.
 intros q_pos.
 red in |- *.
 intros.
 apply H.
 intros ((((r_a, r_b), (r_c, r_d)), ((r_e, r_f), (r_g, r_h))), p); revert p. 
 simpl in |- *.
 intros (H_r_a, (H_r_b, (H_r_c, (H_r_d, (H_r_e, (H_r_f, (H_r_g, H_r_h))))))). 
 intro Hr. 

 assert
  (H_r_a_b_c_d_e_f_g_h :
   (0 <= r_a + r_b + r_c + r_d + r_e + r_f + r_g + r_h)%Z);
  repeat apply Zplus_le_0_compat; try assumption.

 assert
  (P8
     (Build_Z_pos (r_a + r_b + r_c + r_d + r_e + r_f + r_g + r_h)
        H_r_a_b_c_d_e_f_g_h)).

 apply H0.
 rewrite Hk.
 simpl in |- *.
 assumption.

 apply H1.
 reflexivity.
 apply H0.
 reflexivity.
Qed.

Lemma Z8_lt_is_well_def_rht : is_well_def_rht Z8 Z8_lt Z8_eq.
Proof.
 red in |- *.
 intros ((((a, b), (c, d)), ((e, f), (g, h))), z8prf0)
  ((((a', b'), (c', d')), ((e', f'), (g', h'))), z8prf1).
 intro H.
 intros ((((a2, b2), (c2, d2)), ((e2, f2), (g2, h2))), z8prf2).
 generalize H.
 unfold Z8_lt in |- *.
 unfold Z8_eq in |- *. 
 unfold octointegral_lt in |- *.
 unfold octointegral_eq in |- *.
 simpl in |- *.
 clear H z8prf0 z8prf1 z8prf2.
 intros H0 (H1, (H2, (H3, (H4, (H5, (H6, (H7, H8))))))).
 repeat
  match goal with
  | id:(?X1 = ?X2) |- _ => try rewrite id in H0; clear id
  end.
 assumption.
Qed.


Definition Z8_as_well_ordering :=
  Build_well_ordering Z8 Z8_lt Z8_eq Z8_lt_is_order Z8_eq_is_equality
    Z8_lt_is_wf Z8_lt_is_well_def_rht.

Definition Qpositive2 := (Qpositive * Qpositive)%type.

Definition bin2_lt (x y : Qpositive2) :=
  let (p1, p2) := x in let (p1', p2) := y in bin_lt p1 p1'.

Definition bin2_eq (x y : Qpositive2) :=
  let (p1, p2) := x in let (p1', p2) := y in p1 = p1'.

Lemma bin2_lt_is_irreflexive : forall x : Qpositive2, ~ bin2_lt x x.
Proof.
 intros (p1, p2).
 unfold bin2_lt in |- *.
 apply bin_lt_is_irreflexive.
Qed.

Lemma bin2_lt_is_transitive :
 forall x y z : Qpositive2, bin2_lt x y -> bin2_lt y z -> bin2_lt x z.
Proof.
 intros (p1_x, p2_x) (p1_y, p2_y) (p1_z, p2_z).
 unfold bin2_lt in |- *. 
 apply bin_lt_is_transitive.
Qed.

Lemma bin2_lt_is_order : is_order Qpositive2 bin2_lt.
Proof.
 split.
 apply bin2_lt_is_irreflexive.
 apply bin2_lt_is_transitive.
Qed.

Lemma bin2_eq_is_reflexive : forall x : Qpositive2, bin2_eq x x.
Proof.
 intros (p1, p2).
 unfold bin2_eq in |- *.
 reflexivity.
Qed.

Lemma bin2_eq_is_symmetric :
 forall x y : Qpositive2, bin2_eq x y -> bin2_eq y x.
Proof.
 intros (p1_x, p2_x) (p1_y, p2_y).
 unfold bin2_eq in |- *.
 apply sym_eq.
Qed.

Lemma bin2_eq_is_transitive :
 forall x y z : Qpositive2, bin2_eq x y -> bin2_eq y z -> bin2_eq x z.
Proof.
 intros (p1_x, p2_x) (p1_y, p2_y) (p1_z, p2_z).
 unfold bin2_eq in |- *.
 apply trans_eq.
Qed.

Lemma bin2_eq_is_equality : is_equality Qpositive2 bin2_eq.
Proof.
 split.
 apply bin2_eq_is_reflexive.
 split.
 apply bin2_eq_is_symmetric.
 apply bin2_eq_is_transitive.
Qed.

Lemma bin2_lt_is_wf : wf_ind Qpositive2 bin2_lt.
Proof.
 red in |- *.
 intros P H (q1, q2).
 set (P2 := fun p1 : Qpositive => forall p2 : Qpositive, P (p1, p2)) in *.
 generalize q2.
 change (P2 q1) in |- *.
 apply bin_lt_is_wf.
 intros.
 unfold P2 in |- *.
 intro.
 apply H.
 intros (r1, r2). 
 intro.
 generalize r2.
 change (P2 r1) in |- *.
 apply H0.
 unfold bin2_lt in H1.
 assumption.
Qed.

Lemma bin2_lt_is_well_def_rht : is_well_def_rht Qpositive2 bin2_lt bin2_eq.
Proof.
 red in |- *.
 intros (p1_x, p2_x) (p1_y, p2_y).
 intros H (p1_z, p2_z) H0.
 red in H0.
 rewrite <- H0.
 assumption.
Qed.

Definition Qpositive2_as_well_ordering :=
  Build_well_ordering Qpositive2 bin2_lt bin2_eq bin2_lt_is_order
    bin2_eq_is_equality bin2_lt_is_wf bin2_lt_is_well_def_rht.


Lemma octet_lt_wf_rec_without_zeros_and_One :
 forall
   P : Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Qpositive -> Qpositive -> Prop,
 (forall (a b c d e f g h : Z_pos) (q1 q2 : Qpositive),
  (forall (k l r s t u v w : Z_pos) (p1 p2 : Qpositive),
   octet_lt k l r s t u v w p1 p2 a b c d e f g h q1 q2 ->
   P k l r s t u v w p1 p2) -> P a b c d e f g h q1 q2) ->
 forall (a b c d e f g h : Z_pos) (q1 q2 : Qpositive),
 P a b c d e f g h q1 q2.
Proof.
 intros P H (a, Ha) (b, Hb) (c, Hc) (d, Hd) (e, He) (
  f, Hf) (g, Hg) (h, Hh) q1 q2.
 set
  (P2 :=
   fun (p_i : Qpositive2) (x : Z8) =>
   P (fst (fst (fst x))) (snd (fst (fst x))) (fst (snd (fst x)))
     (snd (snd (fst x))) (fst (fst (snd x))) (snd (fst (snd x)))
     (fst (snd (snd x))) (snd (snd (snd x))) (fst p_i) 
     (snd p_i)) in *.
 simpl in |- *.

 assert
  (z8prf_Z8 :
   (0 <= a)%Z /\
   (0 <= b)%Z /\
   (0 <= c)%Z /\
   (0 <= d)%Z /\ (0 <= e)%Z /\ (0 <= f)%Z /\ (0 <= g)%Z /\ (0 <= h)%Z);
  repeat split; try assumption.
 
 assert (P2 (q1, q2) (Build_Z8 (a, b, (c, d), (e, f, (g, h))) z8prf_Z8)).
 
 apply (merge_lt_wf Qpositive2_as_well_ordering Z8_as_well_ordering).
 intros (p1_i, p2_i).
 intros ((((a_i, b_i), (c_i, d_i)), ((e_i, f_i), (g_i, h_i))), p); revert p.
 unfold P2 in |- *.
 simpl in |- *.
 intros (Ha_i, (Hb_i, (Hc_i, (Hd_i, (He_i, (Hf_i, (Hg_i, Hh_i))))))).
 intros.
 change
   (P (Build_Z_pos a_i Ha_i) (Build_Z_pos b_i Hb_i) 
      (Build_Z_pos c_i Hc_i) (Build_Z_pos d_i Hd_i) 
      (Build_Z_pos e_i He_i) (Build_Z_pos f_i Hf_i) 
      (Build_Z_pos g_i Hg_i) (Build_Z_pos h_i Hh_i) p1_i p2_i) 
  in |- *.
 apply H.
 intros (k_, k_p) (l_, l_p) (r_, r_p) (s_, s_p) (t_, t_p) (
  u_, u_p) (v_, v_p) (w_, w_p) p1 p2.
 simpl in |- *.
 intro H1.
 assert
  (z8prf2_Z8 :
   (0 <= k_)%Z /\
   (0 <= l_)%Z /\
   (0 <= r_)%Z /\
   (0 <= s_)%Z /\ (0 <= t_)%Z /\ (0 <= u_)%Z /\ (0 <= v_)%Z /\ (0 <= w_)%Z);
  repeat split; try assumption.
 apply
  (H0 (p1, p2) (Build_Z8 (k_, l_, (r_, s_), (t_, u_, (v_, w_))) z8prf2_Z8)).
 case H1.
 intro.
 left.
 assumption.
 intros (H2, H3).
 right.
 split; assumption.
 assumption.
Qed.

Lemma quadraticAcc_wf :
 forall (a b c d e f g h : Z) (p1 p2 : Qpositive),
 (0 < a + b + c + d)%Z ->
 (0 < e + f + g + h)%Z ->
 (0 <= a)%Z ->
 (0 <= b)%Z ->
 (0 <= c)%Z ->
 (0 <= d)%Z ->
 (0 <= e)%Z ->
 (0 <= f)%Z -> (0 <= g)%Z -> (0 <= h)%Z -> quadraticAcc a b c d e f g h p1 p2.
Proof.
 intros a b c d e f g h p1 p2 Habcd Hefgh Ha Hb Hc Hd He Hf Hg Hh.
 set (pos_a := Build_Z_pos a Ha) in *.
 set (pos_b := Build_Z_pos b Hb) in *.
 set (pos_c := Build_Z_pos c Hc) in *.
 set (pos_d := Build_Z_pos d Hd) in *.
 set (pos_e := Build_Z_pos e He) in *.
 set (pos_f := Build_Z_pos f Hf) in *.
 set (pos_g := Build_Z_pos g Hg) in *.
 set (pos_h := Build_Z_pos h Hh) in *.
 generalize Habcd Hefgh Ha Hb Hc Hd He Hf Hg Hh.
 change
   ((0 < pos_a + pos_b + pos_c + pos_d)%Z ->
    (0 < pos_e + pos_f + pos_g + pos_h)%Z ->
    (0 <= pos_a)%Z ->
    (0 <= pos_b)%Z ->
    (0 <= pos_c)%Z ->
    (0 <= pos_d)%Z ->
    (0 <= pos_e)%Z ->
    (0 <= pos_f)%Z ->
    (0 <= pos_g)%Z ->
    (0 <= pos_h)%Z ->
    quadraticAcc pos_a pos_b pos_c pos_d pos_e pos_f pos_g pos_h p1 p2)
  in |- *.
 

  apply
   octet_lt_wf_rec_without_zeros_and_One
    with
      (P := fun (k l r s t u v w : Z) (p1 p2 : Qpositive) =>
            (0 < k + l + r + s)%Z ->
            (0 < t + u + v + w)%Z ->
            (0 <= k)%Z ->
            (0 <= l)%Z ->
            (0 <= r)%Z ->
            (0 <= s)%Z ->
            (0 <= t)%Z ->
            (0 <= u)%Z ->
            (0 <= v)%Z -> (0 <= w)%Z -> quadraticAcc k l r s t u v w p1 p2).
  
  intros a0 b0 c0 d0 e0 f0 g0 h0 q1 q2 hyp1_aux.

(* modifying hyp1_aux *)
 assert
  (hyp1 :
   forall (k l r s t u v w : Z) (p1 p2 : Qpositive),
   octet_lt k l r s t u v w p1 p2 a0 b0 c0 d0 e0 f0 g0 h0 q1 q2 ->
   (0 < k + l + r + s)%Z ->
   (0 < t + u + v + w)%Z ->
   (0 <= k)%Z ->
   (0 <= l)%Z ->
   (0 <= r)%Z ->
   (0 <= s)%Z ->
   (0 <= t)%Z ->
   (0 <= u)%Z ->
   (0 <= v)%Z -> (0 <= w)%Z -> quadraticAcc k l r s t u v w p1 p2).      
 intros k l r s t u v w p3 p4.
 intros.
 change
   (quadraticAcc (Build_Z_pos k H2) (Build_Z_pos l H3) 
      (Build_Z_pos r H4) (Build_Z_pos s H5) (Build_Z_pos t H6)
      (Build_Z_pos u H7) (Build_Z_pos v H8) (Build_Z_pos w H9) p3 p4) 
  in |- *.
 apply hyp1_aux; repeat assumption.
(* end modifying hyp1 *)

 destruct q1 as [q| q| ].
  (** q1 = (nR xs) *)
  destruct q2 as [q0| q0| ].  
   (** q2 = (nR xs) *)
   case (quadratic_top_more_informative a0 b0 c0 d0 e0 f0 g0 h0).
    (** (quadratic_top_more a0 b0 c0 d0 e0 f0 g0 h0) *)
    intro t.
    intros.
    apply quadraticacc1; try discriminate.
    assumption.
    apply hyp1;
     [ right; split; [ reflexivity | apply quadratic_top_more_5; assumption ]
     | apply quadratic_top_more_1; assumption
     | assumption
     | idtac
     | idtac
     | idtac
     | idtac
     | assumption
     | assumption
     | assumption
     | assumption ]; apply Zle_minus;
     apply (quadratic_top_more_4_1 _ _ _ _ _ _ _ _ t) ||
       apply (quadratic_top_more_4_2 _ _ _ _ _ _ _ _ t) ||
         apply (quadratic_top_more_4_3 _ _ _ _ _ _ _ _ t) ||
           apply (quadratic_top_more_4_4 _ _ _ _ _ _ _ _ t).
    (** ~(quadratic_top_more a0 b0 c0 d0 e0 f0 g0 h0) *)
    intro n.
    case (quadratic_top_more_informative e0 f0 g0 h0 a0 b0 c0 d0).   
     (** (quadratic_top_more e0 f0 g0 h0 a0 b0 c0 d0) *)       
     intro t.
     intros.
     apply quadraticacc2; try discriminate; try assumption.
     apply hyp1;
      [ right; split;
         [ reflexivity | apply quadratic_top_more_5'; assumption ]
      | assumption
      | apply quadratic_top_more_1; assumption
      | assumption
      | assumption
      | assumption
      | assumption
      | idtac
      | idtac
      | idtac
      | idtac ]; apply Zle_minus;
      apply (quadratic_top_more_4_1 _ _ _ _ _ _ _ _ t) ||
        apply (quadratic_top_more_4_2 _ _ _ _ _ _ _ _ t) ||
          apply (quadratic_top_more_4_3 _ _ _ _ _ _ _ _ t) ||
            apply (quadratic_top_more_4_4 _ _ _ _ _ _ _ _ t).
     (** ~ (quadratic_top_more e0 f0 g0 h0 a0 b0 c0 d0) *)       
     intro t.
     intros.
     apply quadraticacc3_II; try assumption.
     apply hyp1;
      [ left; unfold bin_lt in |- *; apply compare_nR
      | idtac
      | idtac
      | assumption
      | idtac
      | idtac
      | apply Zlt_le_weak; assumption
      | assumption
      | idtac
      | idtac
      | apply Zlt_le_weak; assumption ];
      (replace 0%Z with (0 + 0)%Z; [ apply Zplus_le_lt_compat | constructor ];
        [ repeat apply Zplus_le_0_compat | assumption ]; 
        assumption) || (repeat apply Zplus_le_0_compat); 
      assumption.
          
   (** q2 = (dL xs) *)
   case (quadratic_top_more_informative a0 b0 c0 d0 e0 f0 g0 h0).
    (** (quadratic_top_more a0 b0 c0 d0 e0 f0 g0 h0) *)
    intro t.
    intros.
    apply quadraticacc1; try discriminate.
    assumption.
    apply hyp1;
     [ right; split; [ reflexivity | apply quadratic_top_more_5; assumption ]
     | apply quadratic_top_more_1; assumption
     | assumption
     | idtac
     | idtac
     | idtac
     | idtac
     | assumption
     | assumption
     | assumption
     | assumption ]; apply Zle_minus;
     apply (quadratic_top_more_4_1 _ _ _ _ _ _ _ _ t) ||
       apply (quadratic_top_more_4_2 _ _ _ _ _ _ _ _ t) ||
         apply (quadratic_top_more_4_3 _ _ _ _ _ _ _ _ t) ||
           apply (quadratic_top_more_4_4 _ _ _ _ _ _ _ _ t).
    (** ~(quadratic_top_more a0 b0 c0 d0 e0 f0 g0 h0) *)
    intro n.
    case (quadratic_top_more_informative e0 f0 g0 h0 a0 b0 c0 d0).   
     (** (quadratic_top_more e0 f0 g0 h0 a0 b0 c0 d0) *)       
     intro t.
     intros.
     apply quadraticacc2; try discriminate; try assumption.
     apply hyp1;
      [ right; split;
         [ reflexivity | apply quadratic_top_more_5'; assumption ]
      | assumption
      | apply quadratic_top_more_1; assumption
      | assumption
      | assumption
      | assumption
      | assumption
      | idtac
      | idtac
      | idtac
      | idtac ]; apply Zle_minus;
      apply (quadratic_top_more_4_1 _ _ _ _ _ _ _ _ t) ||
        apply (quadratic_top_more_4_2 _ _ _ _ _ _ _ _ t) ||
          apply (quadratic_top_more_4_3 _ _ _ _ _ _ _ _ t) ||
            apply (quadratic_top_more_4_4 _ _ _ _ _ _ _ _ t).
     (** ~ (quadratic_top_more e0 f0 g0 h0 a0 b0 c0 d0) *)       
     intro t.
     intros.
     apply quadraticacc3_IO; try assumption.
     apply hyp1;
      [ left; unfold bin_lt in |- *; apply compare_nR
      | idtac
      | idtac
      | idtac
      | assumption
      | apply Zlt_le_weak; assumption
      | idtac
      | idtac
      | assumption
      | apply Zlt_le_weak; assumption
      | idtac ];
      (replace 0%Z with (0 + 0 + 0)%Z;
        [ apply Zplus_lt_le_compat;
           [ apply Zplus_le_lt_compat; try assumption | idtac ]
        | constructor ]; repeat apply Zplus_le_0_compat; 
        assumption) || (repeat apply Zplus_le_0_compat); 
      assumption. 
    
   (** q2 = One *)
   intros.
   apply quadraticacc0'.
   discriminate.
   constructor.
   apply homographicAcc_wf;
    (rewrite Zplus_assoc; assumption) ||
      (repeat apply Zplus_le_0_compat; try assumption).
   
  (** q1 = (dL xs) *)
  destruct q2 as [q0| q0| ].  
   (** q2 = (nR xs) *)
   case (quadratic_top_more_informative a0 b0 c0 d0 e0 f0 g0 h0).
    (** (quadratic_top_more a0 b0 c0 d0 e0 f0 g0 h0) *)
    intro t.
    intros.
    apply quadraticacc1; try discriminate.
    assumption.
    apply hyp1;
     [ right; split; [ reflexivity | apply quadratic_top_more_5; assumption ]
     | apply quadratic_top_more_1; assumption
     | assumption
     | idtac
     | idtac
     | idtac
     | idtac
     | assumption
     | assumption
     | assumption
     | assumption ]; apply Zle_minus;
     apply (quadratic_top_more_4_1 _ _ _ _ _ _ _ _ t) ||
       apply (quadratic_top_more_4_2 _ _ _ _ _ _ _ _ t) ||
         apply (quadratic_top_more_4_3 _ _ _ _ _ _ _ _ t) ||
           apply (quadratic_top_more_4_4 _ _ _ _ _ _ _ _ t).
    (** ~(quadratic_top_more a0 b0 c0 d0 e0 f0 g0 h0) *)
    intro n.
    case (quadratic_top_more_informative e0 f0 g0 h0 a0 b0 c0 d0).   
     (** (quadratic_top_more e0 f0 g0 h0 a0 b0 c0 d0) *)       
     intro t.
     intros.
     apply quadraticacc2; try discriminate; try assumption.
     apply hyp1;
      [ right; split;
         [ reflexivity | apply quadratic_top_more_5'; assumption ]
      | assumption
      | apply quadratic_top_more_1; assumption
      | assumption
      | assumption
      | assumption
      | assumption
      | idtac
      | idtac
      | idtac
      | idtac ]; apply Zle_minus;
      apply (quadratic_top_more_4_1 _ _ _ _ _ _ _ _ t) ||
        apply (quadratic_top_more_4_2 _ _ _ _ _ _ _ _ t) ||
          apply (quadratic_top_more_4_3 _ _ _ _ _ _ _ _ t) ||
            apply (quadratic_top_more_4_4 _ _ _ _ _ _ _ _ t).
     (** ~ (quadratic_top_more e0 f0 g0 h0 a0 b0 c0 d0) *)       
     intro t.
     intros.
     apply quadraticacc3_OI; try assumption.
     apply hyp1;
      [ left; unfold bin_lt in |- *; apply compare_dL
      | idtac
      | idtac
      | idtac
      | apply Zlt_le_weak; assumption
      | assumption
      | idtac
      | idtac
      | apply Zlt_le_weak; assumption
      | assumption
      | idtac ];
      (replace 0%Z with (0 + 0 + 0 + 0)%Z;
        [ apply Zplus_lt_le_compat;
           [ apply Zplus_lt_le_compat; [ apply Zplus_le_lt_compat | idtac ]
           | idtac ]
        | constructor ]; try apply Zplus_le_0_compat; 
        assumption) || (repeat apply Zplus_le_0_compat); 
      assumption.
          
   (** q2 = (dL xs) *)
   case (quadratic_top_more_informative a0 b0 c0 d0 e0 f0 g0 h0).
    (** (quadratic_top_more a0 b0 c0 d0 e0 f0 g0 h0) *)
    intro t.
    intros.
    apply quadraticacc1; try discriminate.
    assumption.
    apply hyp1;
     [ right; split; [ reflexivity | apply quadratic_top_more_5; assumption ]
     | apply quadratic_top_more_1; assumption
     | assumption
     | idtac
     | idtac
     | idtac
     | idtac
     | assumption
     | assumption
     | assumption
     | assumption ]; apply Zle_minus;
     apply (quadratic_top_more_4_1 _ _ _ _ _ _ _ _ t) ||
       apply (quadratic_top_more_4_2 _ _ _ _ _ _ _ _ t) ||
         apply (quadratic_top_more_4_3 _ _ _ _ _ _ _ _ t) ||
           apply (quadratic_top_more_4_4 _ _ _ _ _ _ _ _ t).
    (** ~(quadratic_top_more a0 b0 c0 d0 e0 f0 g0 h0) *)
    intro n.
    case (quadratic_top_more_informative e0 f0 g0 h0 a0 b0 c0 d0).   
     (** (quadratic_top_more e0 f0 g0 h0 a0 b0 c0 d0) *)       
     intro t.
     intros.
     apply quadraticacc2; try discriminate; try assumption.
     apply hyp1;
      [ right; split;
         [ reflexivity | apply quadratic_top_more_5'; assumption ]
      | assumption
      | apply quadratic_top_more_1; assumption
      | assumption
      | assumption
      | assumption
      | assumption
      | idtac
      | idtac
      | idtac
      | idtac ]; apply Zle_minus;
      apply (quadratic_top_more_4_1 _ _ _ _ _ _ _ _ t) ||
        apply (quadratic_top_more_4_2 _ _ _ _ _ _ _ _ t) ||
          apply (quadratic_top_more_4_3 _ _ _ _ _ _ _ _ t) ||
            apply (quadratic_top_more_4_4 _ _ _ _ _ _ _ _ t).
     (** ~ (quadratic_top_more e0 f0 g0 h0 a0 b0 c0 d0) *)       
     intro t.
     intros.
     apply quadraticacc3_OO; try assumption.
     apply hyp1;
      [ left; unfold bin_lt in |- *; apply compare_dL
      | idtac
      | idtac
      | apply Zlt_le_weak; assumption
      | idtac
      | idtac
      | assumption
      | apply Zlt_le_weak; assumption
      | idtac
      | idtac
      | assumption ];
      (replace 0%Z with (0 + 0 + 0 + 0)%Z;
        [ repeat apply Zplus_lt_le_compat | constructor ];
        try apply Zplus_le_0_compat; assumption) ||
        (repeat apply Zplus_le_0_compat); assumption.
    
   (** q2 = One *)
   intros.
   apply quadraticacc0'.
   discriminate.
   constructor.
   apply homographicAcc_wf;
    (rewrite Zplus_assoc; assumption) ||
      (repeat apply Zplus_le_0_compat; try assumption).
   
  (** q1 = One *)
  intros.
  apply quadraticacc0.
  reflexivity.
  apply homographicAcc_wf;
   (apply Zplus_le_0_compat; assumption) ||
     (rewrite Zplus_assoc;
       (rewrite Zplus_assoc_reverse with (m := c0:Z);
         rewrite Zplus_comm with (n := c0:Z)) ||
         (rewrite Zplus_assoc_reverse with (m := g0:Z);
           rewrite Zplus_comm with (n := g0:Z)); rewrite Zplus_assoc);
   assumption.
Qed.

(** Proof independence of Qquadratic_Qpositive_to_Qpositive: *)

Scheme quadraticAcc_ind_dep := Induction for quadraticAcc Sort Prop.


Lemma Qquadratic_Qpositive_to_Qpositive_equal :
 forall (a b c d e f g h : Z) (p1 p2 : Qpositive)
   (hyp1 hyp2 : quadraticAcc a b c d e f g h p1 p2),
 Qquadratic_Qpositive_to_Qpositive a b c d e f g h p1 p2 hyp1 =
 Qquadratic_Qpositive_to_Qpositive a b c d e f g h p1 p2 hyp2.
Proof.
 intros a b c d e f g h p1 p2 hyp1.
 pattern a, b, c, d, e, f, g, h, p1, p2, hyp1 in |- *.
 elim hyp1 using quadraticAcc_ind_dep; clear a b c d e f g h p1 p2 hyp1.


 (* 1st big subgoal *)
   intros a b c d e f g h p1 p2 Hp1 hAcc hyp2; generalize Hp1 hAcc;
    clear Hp1 hAcc.
   pattern a, b, c, d, e, f, g, h, p1, p2, hyp2 in |- *.
   elim hyp2 using quadraticAcc_ind_dep; clear a b c d e f g h p1 p2 hyp2;
    intros.
   
   (* 1.1 *)
   unfold Qquadratic_Qpositive_to_Qpositive;fold Qquadratic_Qpositive_to_Qpositive;
    case (Qpositive_dec_One p1); intros Hp; [ idtac | Falsum ];
     apply Qhomographic_Qpositive_to_Qpositive_equal.
    (* 1.2 *)
    Falsum.
    (* 1.3 *)
    Falsum. 
    (* 1.4 *)
    Falsum.
    (* 1.5 *)
    discriminate Hp1.
    (* 1.6 *)
    discriminate Hp1.
    (* 1.7 *)
    discriminate Hp1.
    (* 1.8 *)
    discriminate Hp1.


 (* 2nd big subgoal *)
   intros a b c d e f g h p1 p2 Hp1 Hp2 hAcc hyp2; generalize Hp1 Hp2 hAcc;
    clear Hp1 Hp2 hAcc.
   pattern a, b, c, d, e, f, g, h, p1, p2, hyp2 in |- *.
   elim hyp2 using quadraticAcc_ind_dep; clear a b c d e f g h p1 p2 hyp2;
    intros.
   
    (* 2.1 *)
    Falsum.
    (* 2.2 *)
   unfold Qquadratic_Qpositive_to_Qpositive;fold Qquadratic_Qpositive_to_Qpositive;
    case (Qpositive_dec_One p1); intros Hp1_; [ Falsum | idtac ];
     case (Qpositive_dec_One p2); intros Hp2_; [ idtac | Falsum ];
     apply Qhomographic_Qpositive_to_Qpositive_equal.
    (* 2.3 *)
    Falsum.
    (* 2.4 *)
    Falsum. 
    (* 2.5 *)
    discriminate Hp2.
    (* 2.6 *)
    discriminate Hp2.
    (* 2.7 *)
    discriminate Hp2.
    (* 2.8 *)
    discriminate Hp2.


 (* 3rd big subgoal *)
   intros a b c d e f g h p1 p2 Hp1 Hp2 Habcdefgh qAcc H_ind hyp2.
   generalize Hp1 Hp2 Habcdefgh qAcc H_ind;
    clear Hp1 Hp2 Habcdefgh qAcc H_ind.
   pattern a, b, c, d, e, f, g, h, p1, p2, hyp2 in |- *.
   elim hyp2 using quadraticAcc_ind_dep; clear a b c d e f g h p1 p2 hyp2;
    intros.
   
    (* 3.1 *)
    Falsum.
    (* 3.2 *)
    Falsum.
    (* 3.3 *)
   unfold Qquadratic_Qpositive_to_Qpositive;fold Qquadratic_Qpositive_to_Qpositive;
    case (Qpositive_dec_One p1); intros Hp1_; [ Falsum | idtac ];
     case (Qpositive_dec_One p2); intros Hp2_; [ Falsum | idtac ];
     case (quadratic_top_more_informative a b c d e f g h); 
     intros Habcdefgh_; [ idtac | Falsum ]; apply f_equal with Qpositive;
     apply H_ind.
    (* 3.4 *)
    Falsum. 
    (* 3.5 *)
    Falsum.
    (* 3.6 *)
    Falsum.
    (* 3.7 *)
    Falsum.
    (* 3.8 *)
    Falsum.

 (* 4th big subgoal *)
   intros a b c d e f g h p1 p2 Hp1 Hp2 Habcdefgh Hefghabcd qAcc H_ind hyp2.
   generalize Hp1 Hp2 Habcdefgh Hefghabcd qAcc H_ind;
    clear Hp1 Hp2 Habcdefgh Hefghabcd qAcc H_ind.
   pattern a, b, c, d, e, f, g, h, p1, p2, hyp2 in |- *.
   elim hyp2 using quadraticAcc_ind_dep; clear a b c d e f g h p1 p2 hyp2;
    intros; try solve [ Falsum ].

    (* 4.4 *)
   unfold Qquadratic_Qpositive_to_Qpositive;fold Qquadratic_Qpositive_to_Qpositive;
    case (Qpositive_dec_One p1); intros Hp1_; [ Falsum | idtac ];
     case (Qpositive_dec_One p2); intros Hp2_; [ Falsum | idtac ];
     case (quadratic_top_more_informative a b c d e f g h); 
     intros Habcdefgh_; [ Falsum | idtac ];
     case (quadratic_top_more_informative e f g h a b c d); 
     intros Hefghabcd_; [ idtac | Falsum ]; apply f_equal with Qpositive;
     apply H_ind.


 (* 5th big subgoal *)
   intros a b c d e f g h xs ys Habcdefgh Hefghabcd qAcc H_ind hyp2.
   set (P1 := nR xs) in *; assert (HP1 : P1 = nR xs); trivial; generalize HP1.
   set (P2 := nR ys) in *; assert (HP2 : P2 = nR ys); trivial; generalize HP2.
   generalize Habcdefgh Hefghabcd qAcc H_ind;
    clear Habcdefgh Hefghabcd qAcc H_ind.
   (* we copy the goal and change the second occurence of P1 and P2 to (nR xs) and (nR ys) *)
   elim hyp2 using
    quadraticAcc_ind_dep
     with
       (P := fun (a b c d e f g h : Z) (P1 P2 : Qpositive)
               (hyp2 : quadraticAcc a b c d e f g h P1 P2) =>
             forall (Habcdefgh : ~ quadratic_top_more a b c d e f g h)
               (Hefghabcd : ~ quadratic_top_more e f g h a b c d)
               (qAcc : quadraticAcc a (a + b) (a + c) 
                         (a + b + c + d) e (e + f) 
                         (e + g) (e + f + g + h) xs ys),
             (forall
                hyp2 : quadraticAcc a (a + b) (a + c) 
                         (a + b + c + d) e (e + f) 
                         (e + g) (e + f + g + h) xs ys,
              Qquadratic_Qpositive_to_Qpositive a (a + b) 
                (a + c) (a + b + c + d) e (e + f) (e + g) 
                (e + f + g + h) xs ys qAcc =
              Qquadratic_Qpositive_to_Qpositive a (a + b) 
                (a + c) (a + b + c + d) e (e + f) (e + g) 
                (e + f + g + h) xs ys hyp2) ->
             P2 = nR ys ->
             P1 = nR xs ->
             Qquadratic_Qpositive_to_Qpositive a b c d e f g h 
               (nR xs) (nR ys)
               (quadraticacc3_II a b c d e f g h xs ys Habcdefgh Hefghabcd
                  qAcc) =
             Qquadratic_Qpositive_to_Qpositive a b c d e f g h P1 P2 hyp2);
    clear a b c d e f g h hyp2; intros.   
    (* 5.1 *)
    Falsum; rewrite H1 in e0; discriminate e0.
    (* 5.2 *)
    Falsum; rewrite H0 in e0; discriminate e0.
    (* 5.3 *)
    Falsum.
    (* 5.4 *)
    Falsum. 
    (* 5.5 *)
   unfold Qquadratic_Qpositive_to_Qpositive;fold Qquadratic_Qpositive_to_Qpositive;
    case (quadratic_top_more_informative a b c d e f g h); intros Habcdefgh_;
     [ Falsum | idtac ];
     case (quadratic_top_more_informative e f g h a b c d); 
     intros Hefghabcd_; [ Falsum | idtac ]; generalize q;
     let T_local1 := eval compute in (f_equal Qpositive_tail H1) in
     let T_local2 := eval compute in (f_equal Qpositive_tail H2) in
     (rewrite T_local1; rewrite T_local2; apply H0).
    (* 5.6 *)
    discriminate H1.
    (* 5.7 *)
    discriminate H2.
    (* 5.8 *)
    discriminate H1.


 (* 6th big subgoal *)
   intros a b c d e f g h xs ys Habcdefgh Hefghabcd qAcc H_ind hyp2.
   set (P1 := nR xs) in *; assert (HP1 : P1 = nR xs); trivial; generalize HP1.
   set (P2 := dL ys) in *; assert (HP2 : P2 = dL ys); trivial; generalize HP2.
   generalize Habcdefgh Hefghabcd qAcc H_ind;
    clear Habcdefgh Hefghabcd qAcc H_ind.
   elim hyp2 using
    quadraticAcc_ind_dep
     with
       (P := fun (a b c d e f g h : Z) (P1 P2 : Qpositive)
               (hyp2 : quadraticAcc a b c d e f g h P1 P2) =>
             forall (Habcdefgh : ~ quadratic_top_more a b c d e f g h)
               (Hefghabcd : ~ quadratic_top_more e f g h a b c d)
               (qAcc : quadraticAcc (a + b) b (a + b + c + d) 
                         (b + d) (e + f) f (e + f + g + h) 
                         (f + h) xs ys),
             (forall
                hyp2 : quadraticAcc (a + b) b (a + b + c + d) 
                         (b + d) (e + f) f (e + f + g + h) 
                         (f + h) xs ys,
              Qquadratic_Qpositive_to_Qpositive (a + b) b 
                (a + b + c + d) (b + d) (e + f) f (e + f + g + h) 
                (f + h) xs ys qAcc =
              Qquadratic_Qpositive_to_Qpositive (a + b) b 
                (a + b + c + d) (b + d) (e + f) f (e + f + g + h) 
                (f + h) xs ys hyp2) ->
             P2 = dL ys ->
             P1 = nR xs ->
             Qquadratic_Qpositive_to_Qpositive a b c d e f g h 
               (nR xs) (dL ys)
               (quadraticacc3_IO a b c d e f g h xs ys Habcdefgh Hefghabcd
                  qAcc) =
             Qquadratic_Qpositive_to_Qpositive a b c d e f g h P1 P2 hyp2);
    clear a b c d e f g h hyp2; intros.   
    (* 6.1 *)
    Falsum; rewrite H1 in e0; discriminate e0.
    (* 6.2 *)
    Falsum; rewrite H0 in e0; discriminate e0.
    (* 6.3 *)
    Falsum.
    (* 6.4 *)
    Falsum. 
    (* 6.5 *)
    discriminate H1.
    (* 6.6 *)
    unfold Qquadratic_Qpositive_to_Qpositive;fold Qquadratic_Qpositive_to_Qpositive;
    case (quadratic_top_more_informative a b c d e f g h); intros Habcdefgh_;
     [ Falsum | idtac ];
     case (quadratic_top_more_informative e f g h a b c d); 
     intros Hefghabcd_; [ Falsum | idtac ]; generalize q;
     let T_local1 := eval compute in (f_equal Qpositive_tail H1) in
     let T_local2 := eval compute in (f_equal Qpositive_tail H2) in
     (rewrite T_local1; rewrite T_local2; apply H0).
    (* 6.7 *)
    discriminate H2.
    (* 6.8 *)
    discriminate H2.


 (* 7th big subgoal *)
   intros a b c d e f g h xs ys Habcdefgh Hefghabcd qAcc H_ind hyp2.
   set (P1 := dL xs) in *; assert (HP1 : P1 = dL xs); trivial; generalize HP1.
   set (P2 := nR ys) in *; assert (HP2 : P2 = nR ys); trivial; generalize HP2.
   generalize Habcdefgh Hefghabcd qAcc H_ind;
    clear Habcdefgh Hefghabcd qAcc H_ind.
   elim hyp2 using
    quadraticAcc_ind_dep
     with
       (P := fun (a b c d e f g h : Z) (P1 P2 : Qpositive)
               (hyp2 : quadraticAcc a b c d e f g h P1 P2) =>
             forall (Habcdefgh : ~ quadratic_top_more a b c d e f g h)
               (Hefghabcd : ~ quadratic_top_more e f g h a b c d)
               (qAcc : quadraticAcc (a + c) (a + b + c + d) c 
                         (c + d) (e + g) (e + f + g + h) g 
                         (g + h) xs ys),
             (forall
                hyp2 : quadraticAcc (a + c) (a + b + c + d) c 
                         (c + d) (e + g) (e + f + g + h) g 
                         (g + h) xs ys,
              Qquadratic_Qpositive_to_Qpositive (a + c) 
                (a + b + c + d) c (c + d) (e + g) (e + f + g + h) g 
                (g + h) xs ys qAcc =
              Qquadratic_Qpositive_to_Qpositive (a + c) 
                (a + b + c + d) c (c + d) (e + g) (e + f + g + h) g 
                (g + h) xs ys hyp2) ->
             P2 = nR ys ->
             P1 = dL xs ->
             Qquadratic_Qpositive_to_Qpositive a b c d e f g h 
               (dL xs) (nR ys)
               (quadraticacc3_OI a b c d e f g h xs ys Habcdefgh Hefghabcd
                  qAcc) =
             Qquadratic_Qpositive_to_Qpositive a b c d e f g h P1 P2 hyp2);
    clear a b c d e f g h hyp2; intros.   
    (* 7.1 *)
    Falsum; rewrite H1 in e0; discriminate e0.
    (* 7.2 *)
    Falsum; rewrite H0 in e0; discriminate e0.
    (* 7.3 *)
    Falsum.
    (* 7.4 *)
    Falsum. 
    (* 7.5 *)
    discriminate H2.
    (* 7.6 *)
    discriminate H1.
    (* 7.7 *)
    unfold Qquadratic_Qpositive_to_Qpositive;fold Qquadratic_Qpositive_to_Qpositive;
    case (quadratic_top_more_informative a b c d e f g h); intros Habcdefgh_;
     [ Falsum | idtac ];
     case (quadratic_top_more_informative e f g h a b c d); 
     intros Hefghabcd_; [ Falsum | idtac ]; generalize q;
     let T_local1 := eval compute in (f_equal Qpositive_tail H1) in
     let T_local2 := eval compute in (f_equal Qpositive_tail H2) in
     (rewrite T_local1; rewrite T_local2; apply H0).
    (* 7.8 *)
    discriminate H1.

 (* 8th big subgoal *)
   intros a b c d e f g h xs ys Habcdefgh Hefghabcd qAcc H_ind hyp2.
   set (P1 := dL xs) in *; assert (HP1 : P1 = dL xs); trivial; generalize HP1.
   set (P2 := dL ys) in *; assert (HP2 : P2 = dL ys); trivial; generalize HP2.
   generalize Habcdefgh Hefghabcd qAcc H_ind;
    clear Habcdefgh Hefghabcd qAcc H_ind.
   elim hyp2 using
    quadraticAcc_ind_dep
     with
       (P := fun (a b c d e f g h : Z) (P1 P2 : Qpositive)
               (hyp2 : quadraticAcc a b c d e f g h P1 P2) =>
             forall (Habcdefgh : ~ quadratic_top_more a b c d e f g h)
               (Hefghabcd : ~ quadratic_top_more e f g h a b c d)
               (qAcc : quadraticAcc (a + b + c + d) 
                         (b + d) (c + d) d (e + f + g + h) 
                         (f + h) (g + h) h xs ys),
             (forall
                hyp2 : quadraticAcc (a + b + c + d) 
                         (b + d) (c + d) d (e + f + g + h) 
                         (f + h) (g + h) h xs ys,
              Qquadratic_Qpositive_to_Qpositive (a + b + c + d) 
                (b + d) (c + d) d (e + f + g + h) (f + h) 
                (g + h) h xs ys qAcc =
              Qquadratic_Qpositive_to_Qpositive (a + b + c + d) 
                (b + d) (c + d) d (e + f + g + h) (f + h) 
                (g + h) h xs ys hyp2) ->
             P2 = dL ys ->
             P1 = dL xs ->
             Qquadratic_Qpositive_to_Qpositive a b c d e f g h 
               (dL xs) (dL ys)
               (quadraticacc3_OO a b c d e f g h xs ys Habcdefgh Hefghabcd
                  qAcc) =
             Qquadratic_Qpositive_to_Qpositive a b c d e f g h P1 P2 hyp2);
    clear a b c d e f g h hyp2; intros.   
    (* 8.1 *)
    Falsum; rewrite H1 in e0; discriminate e0.
    (* 8.2 *)
    Falsum; rewrite H0 in e0; discriminate e0.
    (* 8.3 *)
    Falsum.
    (* 8.4 *)
    Falsum. 
    (* 8.5 *)
    discriminate H2.
    (* 8.6 *)
    discriminate H2.
    (* 8.7 *)
    discriminate H1.
    (* 8.8 *)
    unfold Qquadratic_Qpositive_to_Qpositive;fold Qquadratic_Qpositive_to_Qpositive;
    case (quadratic_top_more_informative a b c d e f g h); intros Habcdefgh_;
     [ Falsum | idtac ];
     case (quadratic_top_more_informative e f g h a b c d); 
     intros Hefghabcd_; [ Falsum | idtac ]; generalize q;
     let T_local1 := eval compute in (f_equal Qpositive_tail H1) in
     let T_local2 := eval compute in (f_equal Qpositive_tail H2) in
     (rewrite T_local1; rewrite T_local2; apply H0).
Qed.


Lemma Qquadratic_Qpositive_to_Qpositive_equal_strong :
 forall (a1 a2 b1 b2 c1 c2 d1 d2 e1 e2 f1 f2 g1 g2 h1 h2 : Z)
   (x1 x2 y1 y2 : Qpositive)
   (hyp1 : quadraticAcc a1 b1 c1 d1 e1 f1 g1 h1 x1 y1)
   (hyp2 : quadraticAcc a2 b2 c2 d2 e2 f2 g2 h2 x2 y2),
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
 Qquadratic_Qpositive_to_Qpositive a1 b1 c1 d1 e1 f1 g1 h1 x1 y1 hyp1 =
 Qquadratic_Qpositive_to_Qpositive a2 b2 c2 d2 e2 f2 g2 h2 x2 y2 hyp2.
Proof.
 intros; subst; apply Qquadratic_Qpositive_to_Qpositive_equal.
Qed.

(** Here we expand the fixpoint equations of "Qquadratic_Qpositive_to_Qpositive" function *)

Lemma Qquadratic_Qpositive_to_Qpositive_0 :
 forall (a b c d e f g h : Z) (p1 p2 : Qpositive)
   (hyp : quadraticAcc a b c d e f g h p1 p2),
 p1 = One ->
 forall hyp_ni : homographicAcc (a + c) (b + d) (e + g) (f + h) p2,
 Qquadratic_Qpositive_to_Qpositive a b c d e f g h p1 p2 hyp =
 Qhomographic_Qpositive_to_Qpositive (a + c) (b + d) 
   (e + g) (f + h) p2 hyp_ni.
Proof.
 intros.
 apply
  trans_eq
   with
     (Qquadratic_Qpositive_to_Qpositive a b c d e f g h One p2
        (quadraticacc0 a b c d e f g h One p2 (refl_equal One) hyp_ni)).
 apply Qquadratic_Qpositive_to_Qpositive_equal_strong;
  reflexivity || assumption.
 reflexivity.
Qed.

Lemma Qquadratic_Qpositive_to_Qpositive_0' :
 forall (a b c d e f g h : Z) (p1 p2 : Qpositive)
   (hyp : quadraticAcc a b c d e f g h p1 p2),
 p1 <> One ->
 p2 = One ->
 forall hyp_ni : homographicAcc (a + b) (c + d) (e + f) (g + h) p1,
 Qquadratic_Qpositive_to_Qpositive a b c d e f g h p1 p2 hyp =
 Qhomographic_Qpositive_to_Qpositive (a + b) (c + d) 
   (e + f) (g + h) p1 hyp_ni.
Proof.
 intros.
 apply
  trans_eq
   with
     (Qquadratic_Qpositive_to_Qpositive a b c d e f g h p1 One
        (quadraticacc0' a b c d e f g h p1 One H (refl_equal One) hyp_ni)).
 apply Qquadratic_Qpositive_to_Qpositive_equal_strong;
  reflexivity || assumption.
    unfold Qquadratic_Qpositive_to_Qpositive;fold Qquadratic_Qpositive_to_Qpositive;
  case (Qpositive_dec_One p1); intros Hp1; [ Falsum | idtac ]; reflexivity.
Qed.

Lemma Qquadratic_Qpositive_to_Qpositive_1 :
 forall (a b c d e f g h : Z) (p1 p2 : Qpositive)
   (hyp : quadraticAcc a b c d e f g h p1 p2),
 p1 <> One ->
 p2 <> One ->
 quadratic_top_more a b c d e f g h ->
 forall hyp_rec : quadraticAcc (a - e) (b - f) (c - g) (d - h) e f g h p1 p2,
 Qquadratic_Qpositive_to_Qpositive a b c d e f g h p1 p2 hyp =
 nR
   (Qquadratic_Qpositive_to_Qpositive (a - e) (b - f) 
      (c - g) (d - h) e f g h p1 p2 hyp_rec).
Proof.
 intros.
 apply
  trans_eq
   with
     (Qquadratic_Qpositive_to_Qpositive a b c d e f g h p1 p2
        (quadraticacc1 a b c d e f g h p1 p2 H H0 H1 hyp_rec)).
 apply Qquadratic_Qpositive_to_Qpositive_equal. 
 unfold Qquadratic_Qpositive_to_Qpositive;fold Qquadratic_Qpositive_to_Qpositive;
  case (Qpositive_dec_One p1); intros Hp1; [ Falsum | idtac ];
   case (Qpositive_dec_One p2); intros Hp2; [ Falsum | idtac ];
   case (quadratic_top_more_informative a b c d e f g h); 
   intros Habcdefgh; [ idtac | Falsum ]; apply f_equal with Qpositive;
   reflexivity.
Qed.

Lemma Qquadratic_Qpositive_to_Qpositive_2 :
 forall (a b c d e f g h : Z) (p1 p2 : Qpositive)
   (hyp : quadraticAcc a b c d e f g h p1 p2),
 p1 <> One ->
 p2 <> One ->
 ~ quadratic_top_more a b c d e f g h ->
 quadratic_top_more e f g h a b c d ->
 forall hyp_rec : quadraticAcc a b c d (e - a) (f - b) (g - c) (h - d) p1 p2,
 Qquadratic_Qpositive_to_Qpositive a b c d e f g h p1 p2 hyp =
 dL
   (Qquadratic_Qpositive_to_Qpositive a b c d (e - a) 
      (f - b) (g - c) (h - d) p1 p2 hyp_rec).
Proof.
 intros.
 apply
  trans_eq
   with
     (Qquadratic_Qpositive_to_Qpositive a b c d e f g h p1 p2
        (quadraticacc2 a b c d e f g h p1 p2 H H0 H1 H2 hyp_rec)).
 apply Qquadratic_Qpositive_to_Qpositive_equal. 
 unfold Qquadratic_Qpositive_to_Qpositive;fold Qquadratic_Qpositive_to_Qpositive;
  case (Qpositive_dec_One p1); intros Hp1; [ Falsum | idtac ];
   case (Qpositive_dec_One p2); intros Hp2; [ Falsum | idtac ];
   case (quadratic_top_more_informative a b c d e f g h); 
   intros Habcdefgh; [ Falsum | idtac ];
   case (quadratic_top_more_informative e f g h a b c d); 
   intros Hefghabcd; [ idtac | Falsum ]; apply f_equal with Qpositive;
   reflexivity.
Qed.

Lemma Qquadratic_Qpositive_to_Qpositive_3_II :
 forall (a b c d e f g h : Z) (p1 p2 : Qpositive)
   (hyp : quadraticAcc a b c d e f g h p1 p2),
 ~ quadratic_top_more a b c d e f g h ->
 ~ quadratic_top_more e f g h a b c d ->
 forall xs : Qpositive,
 p1 = nR xs ->
 forall ys : Qpositive,
 p2 = nR ys ->
 forall
   hyp_rec : quadraticAcc a (a + b) (a + c) (a + b + c + d) e 
               (e + f) (e + g) (e + f + g + h) xs ys,
 Qquadratic_Qpositive_to_Qpositive a b c d e f g h p1 p2 hyp =
 Qquadratic_Qpositive_to_Qpositive a (a + b) (a + c) 
   (a + b + c + d) e (e + f) (e + g) (e + f + g + h) xs ys hyp_rec.
Proof.
 intros.
 apply
  trans_eq
   with
     (Qquadratic_Qpositive_to_Qpositive a b c d e f g h 
        (nR xs) (nR ys) (quadraticacc3_II a b c d e f g h xs ys H H0 hyp_rec)).
 apply Qquadratic_Qpositive_to_Qpositive_equal_strong;
  reflexivity || assumption.
 unfold Qquadratic_Qpositive_to_Qpositive;fold Qquadratic_Qpositive_to_Qpositive;
   case (quadratic_top_more_informative a b c d e f g h);
   intros Habcdefgh; [ Falsum | idtac ];
   case (quadratic_top_more_informative e f g h a b c d); 
   intros Hefghabcd; [ Falsum | idtac ]; reflexivity.
Qed.

Lemma Qquadratic_Qpositive_to_Qpositive_3_IO :
 forall (a b c d e f g h : Z) (p1 p2 : Qpositive)
   (hyp : quadraticAcc a b c d e f g h p1 p2),
 ~ quadratic_top_more a b c d e f g h ->
 ~ quadratic_top_more e f g h a b c d ->
 forall xs : Qpositive,
 p1 = nR xs ->
 forall ys : Qpositive,
 p2 = dL ys ->
 forall
   hyp_rec : quadraticAcc (a + b) b (a + b + c + d) 
               (b + d) (e + f) f (e + f + g + h) (f + h) xs ys,
 Qquadratic_Qpositive_to_Qpositive a b c d e f g h p1 p2 hyp =
 Qquadratic_Qpositive_to_Qpositive (a + b) b (a + b + c + d) 
   (b + d) (e + f) f (e + f + g + h) (f + h) xs ys hyp_rec.
Proof.
 intros.
 apply
  trans_eq
   with
     (Qquadratic_Qpositive_to_Qpositive a b c d e f g h 
        (nR xs) (dL ys) (quadraticacc3_IO a b c d e f g h xs ys H H0 hyp_rec)).
 apply Qquadratic_Qpositive_to_Qpositive_equal_strong;
  reflexivity || assumption.
    unfold Qquadratic_Qpositive_to_Qpositive;fold Qquadratic_Qpositive_to_Qpositive;
      case (quadratic_top_more_informative a b c d e f g h);
   intros Habcdefgh; [ Falsum | idtac ];
   case (quadratic_top_more_informative e f g h a b c d); 
   intros Hefghabcd; [ Falsum | idtac ]; reflexivity.
Qed.

Lemma Qquadratic_Qpositive_to_Qpositive_3_OI :
 forall (a b c d e f g h : Z) (p1 p2 : Qpositive)
   (hyp : quadraticAcc a b c d e f g h p1 p2),
 ~ quadratic_top_more a b c d e f g h ->
 ~ quadratic_top_more e f g h a b c d ->
 forall xs : Qpositive,
 p1 = dL xs ->
 forall ys : Qpositive,
 p2 = nR ys ->
 forall
   hyp_rec : quadraticAcc (a + c) (a + b + c + d) c 
               (c + d) (e + g) (e + f + g + h) g (g + h) xs ys,
 Qquadratic_Qpositive_to_Qpositive a b c d e f g h p1 p2 hyp =
 Qquadratic_Qpositive_to_Qpositive (a + c) (a + b + c + d) c 
   (c + d) (e + g) (e + f + g + h) g (g + h) xs ys hyp_rec.
Proof.
 intros.
 apply
  trans_eq
   with
     (Qquadratic_Qpositive_to_Qpositive a b c d e f g h 
        (dL xs) (nR ys) (quadraticacc3_OI a b c d e f g h xs ys H H0 hyp_rec)).
 apply Qquadratic_Qpositive_to_Qpositive_equal_strong;
  reflexivity || assumption.
 unfold Qquadratic_Qpositive_to_Qpositive;fold Qquadratic_Qpositive_to_Qpositive;
   case (quadratic_top_more_informative a b c d e f g h);
   intros Habcdefgh; [ Falsum | idtac ];
   case (quadratic_top_more_informative e f g h a b c d); 
   intros Hefghabcd; [ Falsum | idtac ]; reflexivity.
Qed.


Lemma Qquadratic_Qpositive_to_Qpositive_3_OO :
 forall (a b c d e f g h : Z) (p1 p2 : Qpositive)
   (hyp : quadraticAcc a b c d e f g h p1 p2),
 ~ quadratic_top_more a b c d e f g h ->
 ~ quadratic_top_more e f g h a b c d ->
 forall xs : Qpositive,
 p1 = dL xs ->
 forall ys : Qpositive,
 p2 = dL ys ->
 forall
   hyp_rec : quadraticAcc (a + b + c + d) (b + d) (c + d) d 
               (e + f + g + h) (f + h) (g + h) h xs ys,
 Qquadratic_Qpositive_to_Qpositive a b c d e f g h p1 p2 hyp =
 Qquadratic_Qpositive_to_Qpositive (a + b + c + d) 
   (b + d) (c + d) d (e + f + g + h) (f + h) (g + h) h xs ys hyp_rec.
Proof.
 intros.
 apply
  trans_eq
   with
     (Qquadratic_Qpositive_to_Qpositive a b c d e f g h 
        (dL xs) (dL ys) (quadraticacc3_OO a b c d e f g h xs ys H H0 hyp_rec)).
 apply Qquadratic_Qpositive_to_Qpositive_equal_strong;
  reflexivity || assumption.
 unfold Qquadratic_Qpositive_to_Qpositive;fold Qquadratic_Qpositive_to_Qpositive;
   case (quadratic_top_more_informative a b c d e f g h);
   intros Habcdefgh; [ Falsum | idtac ];
   case (quadratic_top_more_informative e f g h a b c d); 
   intros Hefghabcd; [ Falsum | idtac ]; reflexivity.
Qed.
