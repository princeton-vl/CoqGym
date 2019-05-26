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



Require Export general_Q.
Require Export positive_fraction_encoding.
Require Import Merge_Order.
Require Import Wf_nat.

Definition top_more (a b c d : Z) :=
  (c <= a)%Z /\ (d < b)%Z \/ (c < a)%Z /\ (d <= b)%Z.

Lemma top_more_informative :
 forall a b c d : Z, {top_more a b c d} + {~ top_more a b c d}.
Proof.
 intros.
 case (quadro_leq_inf a b c d). 
 intro.
 elim a0.
 intros. 
 case (Z_le_lt_eq_dec c a H).
 intro. 
 left.
 right.
 split.
 assumption.
 assumption.
 intro. 
 case (Z_le_lt_eq_dec d b H0).
 intro.
 left.
 left.
 split.
 assumption.
 assumption.
 intro.
 right.  
 intro.
 case H1.
 intro.
 elim H2.
 intros.
 rewrite e0 in H4.
 apply (Zgt_irrefl b).
 Flip.
 intro.
 elim H2.
 intros.
 rewrite e in H3.
 apply (Zgt_irrefl a).
 Flip.

 unfold top_more in |- *. 
 intro.
 right.
 intro.
 case H.
 intro. 
 apply n.
 elim H0. 
 intros.
 split.
 assumption.
 apply Zlt_le_weak. 
 assumption.
 intro.
 apply n.
 elim H0. 
 intros.
 split.
 apply Zlt_le_weak.
 assumption.
 assumption. 
Defined.

Lemma top_more_1 :
 forall a b c d : Z, top_more a b c d -> (0 < a - c + (b - d))%Z.
Proof.
 intros.
 case H.
 intros.
 elim H0.
 intros.
 replace 0%Z with (0 + 0)%Z.
 apply Zplus_le_lt_compat.
 unfold Zminus in |- *.
 apply Zle_left.
 assumption.
 apply Zlt_minus.
 assumption.    
 constructor.
 intro.
 elim H0.   
 intros.
 replace 0%Z with (0 + 0)%Z.
 apply Zplus_lt_le_compat.
 apply Zlt_minus.
 assumption.
 unfold Zminus in |- *.
 apply Zle_left.
 assumption.
 constructor.
Defined.

Lemma top_more_2 : forall a b c d : Z, top_more a b c d -> (c + d < a + b)%Z.
Proof. 
 intros.
 case H.
 intros.
 elim H0.
 intros.
 apply Zplus_le_lt_compat. 
 assumption.
 assumption.
 intros.
 elim H0.
 intros.
 apply Zplus_lt_le_compat. 
 assumption.
 assumption.
Defined.


Lemma top_more_3 :
 forall a b c d : Z, (0 < c + d)%Z -> (a - c + (b - d) < a + b)%Z.
Proof.
 intros.
 apply Zplus_lt_reg_l with (c + d)%Z.
 apply Zplus_lt_reg_l with (- a - b)%Z.
 replace (- a - b + (c + d + (a - c + (b - d))))%Z with 0%Z.
 replace (- a - b + (c + d + (a + b)))%Z with (c + d)%Z.
 assumption.
 ring.
 ring.
Defined.

Lemma top_more_4 : forall a b c d : Z, top_more a b c d -> (c <= a)%Z.
Proof. 
 intros.
 case H.
 intros.
 elim H0.
 intros.
 assumption.
 intros.
 elim H0.
 intros.
 apply Zlt_le_weak.
 assumption.
Defined.

Lemma top_more_4' : forall a b c d : Z, top_more a b c d -> (d <= b)%Z.
Proof. 
 intros.
 case H.
 intros.
 elim H0.
 intros.
 apply Zlt_le_weak.
 assumption.
 intros.
 elim H0.
 intros.
 assumption.
Defined.

Lemma top_more_5 :
 forall a b c d : Z,
 (0 < c + d)%Z -> (a - c + (b - d) + c + d < a + b + c + d)%Z.
Proof.
 intros.
 assert ((a - c + (b - d) + c + d)%Z = (a + b + 0)%Z).
 ring.
 rewrite H0.
 rewrite Zplus_assoc_reverse with (n := (a + b)%Z).
 apply Zplus_le_lt_compat.  
 apply Z.le_refl.
 assumption.
Defined.

Lemma top_more_5' :
 forall a b c d : Z,
 (0 < a + b)%Z -> (a + b + (c - a) + (d - b) < a + b + c + d)%Z.
Proof.
 intros.
 assert ((a + b + (c - a) + (d - b))%Z = (0 + (c + d))%Z).
 ring.
 rewrite H0.
 rewrite Zplus_assoc_reverse with (n := (a + b)%Z).
 apply Zplus_lt_le_compat.  
 assumption.
 apply Z.le_refl.
Defined.



Inductive homographicAcc : Z -> Z -> Z -> Z -> Qpositive -> Prop :=
  | homographicacc0 :
      forall (a b c d : Z) (p : Qpositive),
      p = One -> (0 < a + b)%Z -> (0 < c + d)%Z -> homographicAcc a b c d p
  | homographicacc1 :
      forall (a b c d : Z) (p : Qpositive),
      p <> One ->
      top_more a b c d ->
      homographicAcc (a - c)%Z (b - d)%Z c d p -> homographicAcc a b c d p
  | homographicacc2 :
      forall (a b c d : Z) (p : Qpositive),
      p <> One ->
      ~ top_more a b c d ->
      top_more c d a b ->
      homographicAcc a b (c - a)%Z (d - b)%Z p -> homographicAcc a b c d p
  | homographicacc3 :
      forall (a b c d : Z) (xs : Qpositive),
      ~ top_more a b c d ->
      ~ top_more c d a b ->
      homographicAcc a (a + b)%Z c (c + d)%Z xs ->
      homographicAcc a b c d (nR xs)
  | homographicacc3' :
      forall (a b c d : Z) (xs : Qpositive),
      ~ top_more a b c d ->
      ~ top_more c d a b ->
      homographicAcc (a + b)%Z b (c + d)%Z d xs ->
      homographicAcc a b c d (dL xs).

Lemma homographicacc_0_num :
 forall a b c d : Z, homographicAcc a b c d One -> (0 < a + b)%Z.
Proof.
 intros.
 abstract (inversion H; trivial; Irreflex; discriminate H0).
Defined.

Lemma homographicacc_0_denom :
 forall a b c d : Z, homographicAcc a b c d One -> (0 < c + d)%Z.
Proof.
 intros.
 abstract (inversion H; trivial; Irreflex; discriminate H0).
Defined.


Lemma homographicacc_1 :
 forall (a b c d : Z) (p : Qpositive),
 homographicAcc a b c d p ->
 p <> One -> top_more a b c d -> homographicAcc (a - c) (b - d) c d p.
Proof.
 simple destruct 1; intros; trivial; Falsum.
Defined.  

Lemma homographicacc_2 :
 forall (a b c d : Z) (p : Qpositive),
 homographicAcc a b c d p ->
 p <> One ->
 ~ top_more a b c d ->
 top_more c d a b -> homographicAcc a b (c - a) (d - b) p.
Proof.
 simple destruct 1; intros; trivial; Falsum.
Defined.  

Lemma homographicacc_3 :
 forall (a b c d : Z) (p : Qpositive),
 homographicAcc a b c d p ->
 forall xs : Qpositive,
 p = nR xs ->
 ~ top_more a b c d ->
 ~ top_more c d a b -> homographicAcc a (a + b) c (c + d) xs.
Proof.
 intros a b c d p HAcc; case HAcc; intros; try solve [ Falsum ];
  [ rewrite H2 in H; clear H2; discriminate H
  | let T_local := eval compute in (f_equal Qpositive_tail H2) in
    (rewrite <- T_local; assumption)
  | discriminate H2 ].
Defined.  

Lemma homographicacc_3' :
 forall (a b c d : Z) (p : Qpositive),
 homographicAcc a b c d p ->
 forall xs : Qpositive,
 p = dL xs ->
 ~ top_more a b c d ->
 ~ top_more c d a b -> homographicAcc (a + b) b (c + d) d xs.
Proof.
 intros a b c d p HAcc xs.
 case HAcc; intros; try solve [ Falsum ];
  [ rewrite H2 in H; clear H2; discriminate H
  | discriminate H2
  | let T_local := eval compute in (f_equal Qpositive_tail H2) in
    (rewrite <- T_local; assumption) ].
Defined.  


Fixpoint Qhomographic_Qpositive_to_Qpositive (a b c d : Z) 
 (p : Qpositive) (hyp : homographicAcc a b c d p) {struct hyp} : Qpositive :=
  match Qpositive_dec_One p with
  | left H_p_is_One =>
      let H :=
        eq_ind p (fun p : Qpositive => homographicAcc a b c d p) hyp One
          H_p_is_One in
      (fun hyp0 : homographicAcc a b c d One =>
       (fun (Hab : (0 < a + b)%Z) (Hcd : (0 < c + d)%Z) =>
        positive_fraction_encoding (a + b) (c + d) Hab Hcd)
         (homographicacc_0_num a b c d hyp0)
         (homographicacc_0_denom a b c d hyp0)) H
  | right H_p_not_One =>
      match top_more_informative a b c d with
      | left H_abcd =>
          nR
            (Qhomographic_Qpositive_to_Qpositive (a - c)%Z 
               (b - d)%Z c d p
               (homographicacc_1 a b c d p hyp H_p_not_One H_abcd))
      | right H_abcd =>
          match top_more_informative c d a b with
          | left H_cdab =>
              dL
                (Qhomographic_Qpositive_to_Qpositive a b 
                   (c - a)%Z (d - b)%Z p
                   (homographicacc_2 a b c d p hyp H_p_not_One H_abcd H_cdab))
          | right H_cdab =>
              match p as q return (p = q -> Qpositive) with
              | nR q =>
                  fun H : p = nR q =>
                  Qhomographic_Qpositive_to_Qpositive a 
                    (a + b)%Z c (c + d)%Z q
                    (homographicacc_3 a b c d p hyp q H H_abcd H_cdab)
              | dL q =>
                  fun H : p = dL q =>
                  Qhomographic_Qpositive_to_Qpositive 
                    (a + b)%Z b (c + d)%Z d q
                    (homographicacc_3' a b c d p hyp q H H_abcd H_cdab)
              | One =>
                  fun q : p = One =>
                  False_rec Qpositive (False_ind False (H_p_not_One q))
              end (refl_equal p)
          end
      end
  end.

(** some sort of lexicographical order on binary lists *)

Fixpoint Qpositive_length (qp : Qpositive) : nat :=
  match qp with
  | One => 0
  | dL qp1 => S (Qpositive_length qp1)
  | nR qp1 => S (Qpositive_length qp1)
  end.


Definition bin_lt (qp1 qp2 : Qpositive) : Prop :=
  Qpositive_length qp1 < Qpositive_length qp2.


Definition bin_eq (x y : Qpositive) := x = y.

(* We mention the following form only for the proof of the well-foundedness  *)
Lemma bin_lt_compat_via_length :
 forall x y : Qpositive,
 bin_lt x y -> Qpositive_length x < Qpositive_length y.
Proof.
 trivial.
Defined.

Lemma compare_dL : forall x : Qpositive, bin_lt x (dL x). 
Proof.
 unfold bin_lt in |- *.
 simpl in |- *.
 auto with arith.
Defined.

Lemma compare_nR : forall x : Qpositive, bin_lt x (nR x). 
Proof.
 unfold bin_lt in |- *.
 simpl in |- *.
 auto with arith.
Defined.


(** Definition of order for quadroples and a binary sequnce *)


Record Z_pos : Set :=  {zposcrr :> Z; z4prf_Z_pos : (0 <= zposcrr)%Z}.


Definition qlt (a b c d : Z) (p : Qpositive) (a' b' c' d' : Z)
  (p' : Qpositive) : Prop :=
  bin_lt p p' \/ p = p' /\ (a + b + c + d < a' + b' + c' + d')%Z. 

Definition qle (a b c d : Z) (p : Qpositive) (a' b' c' d' : Z)
  (p' : Qpositive) : Prop :=
  qlt a b c d p a' b' c' d' p' \/
  a = a' /\ b = b' /\ c = c' /\ d = d' /\ p = p'. 

Definition quadrointegral_lt (a b c d a' b' c' d' : Z) :=
  (a + b + c + d < a' + b' + c' + d')%Z.

Definition quadrointegral_eq (a b c d a' b' c' d' : Z) :=
  a = a' /\ b = b' /\ c = c' /\ d = d'.


Record Z4 : Set := 
  {z4crr :> Z * Z * (Z * Z);
   z4prf :
    (0 <= fst (fst z4crr))%Z /\
    (0 <= snd (fst z4crr))%Z /\
    (0 <= fst (snd z4crr))%Z /\ (0 <= snd (snd z4crr))%Z}.


Definition Z4_lt (x y : Z4) :=
  let (V1, V2) := z4crr x in
  let (V3, V4) := z4crr y in
  let (a, b) := V1 in
  let (c, d) := V2 in
  let (a', b') := V3 in
  let (c', d') := V4 in quadrointegral_lt a b c d a' b' c' d'.


Definition Z4_eq (x y : Z4) :=
  let (V1, V2) := z4crr x in
  let (V3, V4) := z4crr y in
  let (a, b) := V1 in
  let (c, d) := V2 in
  let (a', b') := V3 in
  let (c', d') := V4 in quadrointegral_eq a b c d a' b' c' d'.


Lemma Z4_lt_is_irreflexive : forall x : Z4, ~ Z4_lt x x.
Proof.
 intros (((a, b), (c, d)), z4prf0).
 unfold Z4_lt in |- *. 
 unfold quadrointegral_lt in |- *.
 simpl in |- *.
 apply Z.lt_irrefl. 
Defined.


Lemma Z4_lt_is_transitive :
 forall x y z : Z4, Z4_lt x y -> Z4_lt y z -> Z4_lt x z.
Proof.
 intros (((a, b), (c, d)), z4prf0) (((a', b'), (c', d')), z4prf1)
  (((a2, b2), (c2, d2)), z4prf2).
 unfold Z4_lt in |- *.
 unfold quadrointegral_lt in |- *.
 simpl in |- *.
 intros.
 apply Z.lt_trans with (a' + b' + c' + d')%Z; assumption.
Defined.


Lemma Z4_lt_is_order : is_order Z4 Z4_lt.
Proof.
 split.
 apply Z4_lt_is_irreflexive.
 apply Z4_lt_is_transitive.
Defined.



Lemma Z4_eq_is_reflexive : forall x : Z4, Z4_eq x x.
Proof.
 intros (((a, b), (c, d)), z4prf0).
 unfold Z4_eq in |- *. 
 unfold quadrointegral_eq in |- *; repeat split. 
Defined.  


Lemma Z4_eq_is_symmetric : forall x y : Z4, Z4_eq x y -> Z4_eq y x.
Proof.
 intros (((a, b), (c, d)), z4prf0) (((a', b'), (c', d')), z4prf1).
 unfold Z4_eq in |- *.
 unfold quadrointegral_eq in |- *.
 intros (HH1, (HH2, (HH3, HH4))); repeat split; symmetry  in |- *; assumption.
Defined.

Lemma Z4_eq_is_transitive :
 forall x y z : Z4, Z4_eq x y -> Z4_eq y z -> Z4_eq x z.
Proof.
 intros (((a, b), (c, d)), z4prf0) (((a', b'), (c', d')), z4prf1)
  (((a2, b2), (c2, d2)), z4prf2).
 unfold Z4_eq in |- *.
 unfold quadrointegral_eq in |- *.
 simpl in |- *.
 intros (HH2, (HH4, (HH6, HH7))) (HH9, (HH11, (HH13, HH14))); repeat split;
  match goal with
  | id12:(?X1 = ?X2),id23:(?X2 = ?X3) |- (?X1 = ?X3) =>
      try apply (trans_eq id12 id23)
  end.
Defined.


Lemma Z4_eq_is_equality : is_equality Z4 Z4_eq.
Proof.
 split.
 apply Z4_eq_is_reflexive.
 split.
 apply Z4_eq_is_symmetric.
 apply Z4_eq_is_transitive.
Defined.


Lemma Z_pos_lt_is_wf :
 forall P : Z_pos -> Prop,
 (forall q : Z_pos, (forall r : Z_pos, (r < q)%Z -> P r) -> P q) ->
 forall q : Z_pos, P q.
Proof.
 intros.
 destruct q.
 rename zposcrr0 into q.
 set (P2 := fun p : Z => forall Hp : (0 <= p)%Z, P (Build_Z_pos p Hp)) in *. 
 assert (P2 q).
 apply Zind_wf with (p := 0%Z).
 intros.
 unfold P2 in |- *. 
 intro.
 apply H.
 intros.
 destruct r.
 rename zposcrr0 into r.
 assert (P2 r).
 apply H0.
 split.
 assumption.
 assumption.
 apply (H2 z4prf_Z_pos1).
 assumption.
 apply (H0 z4prf_Z_pos0).
Defined. 


Lemma Z4_lt_is_wf : wf_ind Z4 Z4_lt.
Proof.
 red in |- *.
 intros P H (((a, b), (c, d)), p); revert p;
 simpl in |- *.
 intros (Ha, (Hb, (Hc, Hd))).
 assert (H_a_b_c_d : (0 <= a + b + c + d)%Z); repeat apply Zplus_le_0_compat;
  try assumption.
 (* Here Omega tactic would have worked as opposed to the similar situation below *)
 set
  (P4 :=
   fun k : Z_pos =>
   forall (a b c d : Z)
     (Habcd : (0 <= a)%Z /\ (0 <= b)%Z /\ (0 <= c)%Z /\ (0 <= d)%Z)
     (Hk : zposcrr k = (a + b + c + d)%Z), P (Build_Z4 (a, b, (c, d)) Habcd))
  in *.
 assert (P4 (Build_Z_pos (a + b + c + d) H_a_b_c_d)).

 apply Z_pos_lt_is_wf.
 intros q_pos.
 red in |- *.
 intros.
 apply H.
 intros (((r_a, r_b), (r_c, r_d)), p); revert p.
 simpl in |- *.
 intros (H_r_a, (H_r_b, (H_r_c, H_r_d))).
 intro Hq.

 assert (H_r_a_b_c_d : (0 <= r_a + r_b + r_c + r_d)%Z);
  repeat apply Zplus_le_0_compat; try assumption.
 (* Here Omega tactic does not work, as if we say "Clear z4prf1" and gives an error! *)
 assert (P4 (Build_Z_pos (r_a + r_b + r_c + r_d) H_r_a_b_c_d)).

 apply H0.
 rewrite Hk.
 simpl in |- *.
 assumption.

 apply H1.
 reflexivity.
 apply H0.
 reflexivity.
Defined.


Lemma Z4_lt_is_well_def_rht : is_well_def_rht Z4 Z4_lt Z4_eq.
Proof.
 red in |- *.
 intros (((a, b), (c, d)), z4prf0) (((a', b'), (c', d')), z4prf1).
 intro H.
 intros (((a2, b2), (c2, d2)), z4prf2).
 generalize H.
 unfold Z4_lt in |- *.
 unfold Z4_eq in |- *. 
 unfold quadrointegral_lt in |- *.
 unfold quadrointegral_eq in |- *.
 simpl in |- *.
 clear H z4prf0 z4prf1 z4prf2.
 intros H0 (H1, (H2, (H3, H4))).
 repeat
  match goal with
  | id:(?X1 = ?X2) |- _ => try rewrite id in H0; clear id
  end.
 assumption.
Defined.


Definition Z4_as_well_ordering :=
  Build_well_ordering Z4 Z4_lt Z4_eq Z4_lt_is_order Z4_eq_is_equality
    Z4_lt_is_wf Z4_lt_is_well_def_rht.


Lemma bin_lt_is_irreflexive : forall x : Qpositive, ~ bin_lt x x.
Proof.
 intros x.
 unfold bin_lt in |- *.
 apply lt_irrefl.
Defined.


Lemma bin_lt_is_transitive :
 forall x y z : Qpositive, bin_lt x y -> bin_lt y z -> bin_lt x z.
Proof.
 intros x y z; unfold bin_lt in |- *.
 apply lt_trans.
Defined.

Lemma bin_lt_is_order : is_order Qpositive bin_lt.
Proof.
 split.
 apply bin_lt_is_irreflexive.
 apply bin_lt_is_transitive.
Defined.


Lemma bin_eq_is_reflexive : forall x : Qpositive, bin_eq x x.
Proof.
 intros.
 unfold bin_eq in |- *.
 reflexivity.
Defined.  


Lemma bin_eq_is_symmetric : forall x y : Qpositive, bin_eq x y -> bin_eq y x.
Proof.
 intros x y.
 unfold bin_eq in |- *.
 apply sym_eq.
Defined.

Lemma bin_eq_is_transitive :
 forall x y z : Qpositive, bin_eq x y -> bin_eq y z -> bin_eq x z.
Proof.
 intros x y z.
 unfold bin_eq in |- *.
 apply trans_eq.
Defined.



Lemma bin_eq_is_equality : is_equality Qpositive bin_eq.
Proof.
 split.
 apply bin_eq_is_reflexive.
 split.
 apply bin_eq_is_symmetric.
 apply bin_eq_is_transitive.
Defined.


Lemma bin_lt_is_wf : wf_ind Qpositive bin_lt.
Proof.
 generalize
  (well_founded_lt_compat Qpositive Qpositive_length bin_lt
     bin_lt_compat_via_length).
 intro H.
 exact (well_founded_ind H).
Defined.

Lemma bin_lt_is_well_def_rht : is_well_def_rht Qpositive bin_lt bin_eq.
Proof.
 red in |- *.
 intros.
 red in H0.
 rewrite <- H0.
 assumption.
Defined.

Definition Qpositive_as_well_ordering :=
  Build_well_ordering Qpositive bin_lt bin_eq bin_lt_is_order
    bin_eq_is_equality bin_lt_is_wf bin_lt_is_well_def_rht.


Lemma qlt_wf_rec_without_zeros_and_One :
 forall P : Z -> Z -> Z -> Z -> Qpositive -> Prop,
 (forall (a b c d : Z_pos) (p : Qpositive),
  (forall (r s t u : Z_pos) (p1 : Qpositive),
   qlt r s t u p1 a b c d p -> P r s t u p1) -> P a b c d p) ->
 forall (a b c d : Z_pos) (p : Qpositive), P a b c d p.
Proof.
 intros P H (a, Ha) (b, Hb) (c, Hc) (d, Hd) p.
 set
  (P2 :=
   fun (p_i : Qpositive) (x : Z4) =>
   P (fst (fst x)) (snd (fst x)) (fst (snd x)) (snd (snd x)) p_i) 
  in *.
 simpl in |- *.

 assert (z4prf_Z4 : (0 <= a)%Z /\ (0 <= b)%Z /\ (0 <= c)%Z /\ (0 <= d)%Z);
  repeat split; try assumption.

 assert (P2 p (Build_Z4 (a, b, (c, d)) z4prf_Z4)).
 
 apply (merge_lt_wf Qpositive_as_well_ordering Z4_as_well_ordering).
 intro p_i.
 intros (((a_i, b_i), (c_i, d_i)), q); revert q.
 unfold P2 in |- *.
 simpl in |- *.
 intros (Ha_i, (Hb_i, (Hc_i, Hd_i))).
 intros.
 change
   (P (Build_Z_pos a_i Ha_i) (Build_Z_pos b_i Hb_i) 
      (Build_Z_pos c_i Hc_i) (Build_Z_pos d_i Hd_i) p_i) 
  in |- *.
 apply H.
 intros (r_, r_p) (s_, s_p) (t_, t_p) (u_, u_p) p1.
 simpl in |- *.
 intro H1.
 assert
  (z4prf2_Z4 : (0 <= r_)%Z /\ (0 <= s_)%Z /\ (0 <= t_)%Z /\ (0 <= u_)%Z);
  repeat split; try assumption.
 apply (H0 p1 (Build_Z4 (r_, s_, (t_, u_)) z4prf2_Z4)).
 case H1.
 intro.
 left.
 assumption.
 intros (H2, H3).
 right.
 split; assumption.
 assumption.
Defined.


Lemma homographicAcc_wf :
 forall (a b c d : Z) (p : Qpositive),
 (0 < a + b)%Z ->
 (0 < c + d)%Z ->
 (0 <= a)%Z ->
 (0 <= b)%Z -> (0 <= c)%Z -> (0 <= d)%Z -> homographicAcc a b c d p.
Proof.
 intros a b c d p Hab Hcd Ha Hb Hc Hd.
 set (ha := Build_Z_pos a Ha) in *.
 set (hb := Build_Z_pos b Hb) in *.
 set (hc := Build_Z_pos c Hc) in *.
 set (hd := Build_Z_pos d Hd) in *.
 generalize Hab Hcd Ha Hb Hc Hd.
 change
   ((0 < ha + hb)%Z ->
    (0 < hc + hd)%Z ->
    (0 <= ha)%Z ->
    (0 <= hb)%Z -> (0 <= hc)%Z -> (0 <= hd)%Z -> homographicAcc ha hb hc hd p)
  in |- *.


 apply
  qlt_wf_rec_without_zeros_and_One
   with
     (P := fun (r s t u : Z) (p1 : Qpositive) =>
           (0 < r + s)%Z ->
           (0 < t + u)%Z ->
           (0 <= r)%Z ->
           (0 <= s)%Z ->
           (0 <= t)%Z -> (0 <= u)%Z -> homographicAcc r s t u p1).
                       
 intros a0 b0 c0 d0 p0 hyp1_aux.

 
(* modifying hyp1_aux *)
 assert
  (hyp1 :
   forall (r s t u : Z) (p1 : Qpositive),
   qlt r s t u p1 a0 b0 c0 d0 p0 ->
   (0 < r + s)%Z ->
   (0 < t + u)%Z ->
   (0 <= r)%Z ->
   (0 <= s)%Z -> (0 <= t)%Z -> (0 <= u)%Z -> homographicAcc r s t u p1).
 intros.
 change
   (homographicAcc (Build_Z_pos r H2) (Build_Z_pos s H3) 
      (Build_Z_pos t H4) (Build_Z_pos u H5) p1) in |- *.
 apply hyp1_aux; repeat assumption.
(* end modifying hyp1 *)



 destruct p0 as [q| q| ].

 (** p0 = (nR p0) *)
  case (top_more_informative a0 b0 c0 d0).
  (** (top_more a0 b0 c0 d0) *)
   intros.
   apply homographicacc1.
   discriminate.
   assumption.
   apply hyp1.
   right.
   split.
   reflexivity.
   apply top_more_5.
   assumption.
   apply top_more_1.
   assumption.
   assumption.
   apply Zle_minus.
   apply (top_more_4 _ _ _ _ t).
   apply Zle_minus.
   apply (top_more_4' _ _ _ _ t).
   assumption.
   assumption.
  (** ~(top_more a0 b0 c0 d0) *)
   intro.
   case (top_more_informative c0 d0 a0 b0).
   (** (top_more c0 d0 a0 b0) *)
    intros.
    apply homographicacc2.
    discriminate.
    assumption.
    assumption.
    apply hyp1.
    right.
    split.
    reflexivity.
    apply top_more_5'.
    assumption.
    assumption.    
    apply top_more_1.
    assumption.
    assumption.
    assumption.   
    apply Zle_minus.
    apply (top_more_4 _ _ _ _ t).
    apply Zle_minus.
    apply (top_more_4' _ _ _ _ t).
   (** ~(top_more c0 d0 a0 b0) *)
    intros.
    apply homographicacc3.
    (* Discriminate. *)(**)
    assumption.
    assumption.
    apply hyp1.

    left.
    unfold bin_lt in |- *.
    apply compare_nR.    

    replace 0%Z with (0 + 0)%Z.
    apply Zplus_le_lt_compat.
    assumption.
    assumption.
    constructor.
    replace 0%Z with (0 + 0)%Z.
    apply Zplus_le_lt_compat.
    assumption.
    assumption.
    constructor.
    assumption.
    apply Zlt_le_weak.
    assumption.
    assumption.
    apply Zlt_le_weak.
    assumption.
 (** p0 = (dL p0) *)
  case (top_more_informative a0 b0 c0 d0).
  (** (top_more a0 b0 c0 d0) *)
   intros.
   apply homographicacc1.
   discriminate.
   assumption.
   apply hyp1.
   right.

   split.
   reflexivity.


   apply top_more_5.
   assumption.

   apply top_more_1.
   assumption.
   assumption.
   apply Zle_minus.
   apply (top_more_4 _ _ _ _ t).
   apply Zle_minus.
   apply (top_more_4' _ _ _ _ t).
   assumption.
   assumption.
  (** ~(top_more a0 b0 c0 d0) *)
   intro.
   case (top_more_informative c0 d0 a0 b0).
   (** (top_more c0 d0 a0 b0) *)
    intros.
    apply homographicacc2.
    discriminate.
    assumption.
    assumption.
    apply hyp1.
    right.

    split.
    reflexivity.

    apply top_more_5'.
    assumption.

    assumption.    
    apply top_more_1.
    assumption.
    assumption.
    assumption.   
    apply Zle_minus.
    apply (top_more_4 _ _ _ _ t).
    apply Zle_minus.
    apply (top_more_4' _ _ _ _ t).
   (** ~(top_more c0 d0 a0 b0) *)
    intros.
    apply homographicacc3'.

    assumption.
    assumption.
    apply hyp1.
    left.

    unfold bin_lt in |- *.
    apply compare_dL.  
    replace 0%Z with (0 + 0)%Z.
    apply Zplus_lt_le_compat.
    assumption.
    assumption.
    constructor.
    replace 0%Z with (0 + 0)%Z.
    apply Zplus_lt_le_compat.
    assumption.
    assumption.
    constructor.
    apply Zlt_le_weak.
    assumption.
    assumption.
    apply Zlt_le_weak.
    assumption.
    assumption.
 (** p = One *)
  intros.
  apply homographicacc0.
  reflexivity.
  assumption.
  assumption.
Defined.


(* TEST part *)
(* This part is an attempt to test the computational power of "Qhomographic_Qpositive_to_Qpositive" function. We try to calculate h(x)=2x+3/(x+4) for x:=1 *) 
(* TEST 1 : 01_08_02 RAM:386MB Coq:7.3 OS:Redhat7.3   RESULT:insufficient memory *) 

Remark one_non_negative : (0 <= 1)%Z.
Proof. 
 apply Zorder.Zle_0_pos. 
Defined.


Remark two_non_negative : (0 <= 2)%Z.
Proof. 
 apply Zorder.Zle_0_pos. 
Defined.

Remark three_non_negative : (0 <= 3)%Z.
Proof.
 apply Zorder.Zle_0_pos.
Defined.


Remark four_non_negative : (0 <= 4)%Z.
Proof.
 apply Zorder.Zle_0_pos.
Defined.

Remark five_non_negative : (0 <= 5)%Z.
Proof.
 apply Zorder.Zle_0_pos.
Defined.


Remark six_non_negative : (0 <= 6)%Z.
Proof.
 apply Zorder.Zle_0_pos.
Defined.

Remark seven_non_negative : (0 <= 7)%Z.
Proof.
 apply Zorder.Zle_0_pos.
Defined.


Remark two_plus_three_positive : (0 < 2 + 3)%Z.
Proof. 
 simpl in |- *.
 apply ZERO_lt_POS. 
Defined.

Remark one_plus_four_positive : (0 < 1 + 4)%Z.
Proof.
 simpl in |- *.
 apply ZERO_lt_POS.
Defined.



Definition homographicacc_wf_for_five_over_five :=
  homographicAcc_wf 2 3 1 4 One two_plus_three_positive
    one_plus_four_positive two_non_negative three_non_negative
    one_non_negative four_non_negative.

(* TEST: Eval Compute in (Qhomographic_Qpositive_to_Qpositive `2` `3` `1` `4` (One) homographicacc_wf_for_five_over_five). *)

(* End of the TEST part *)


(** Proof independence of Qhomographic_Qpositive_to_Qpositive: *)

Scheme homographicAcc_ind_dep := Induction for homographicAcc Sort Prop.


Lemma Qhomographic_Qpositive_to_Qpositive_equal :
 forall (a b c d : Z) (p : Qpositive) (hyp1 hyp2 : homographicAcc a b c d p),
 Qhomographic_Qpositive_to_Qpositive a b c d p hyp1 =
 Qhomographic_Qpositive_to_Qpositive a b c d p hyp2.
Proof.
 intros a b c d p hyp1 hyp2.
 generalize hyp2.
 clear hyp2.
 pattern a, b, c, d, p, hyp1 in |- *.
 elim hyp1 using homographicAcc_ind_dep; clear a b c d p hyp1.


 (* 1st big subgoal *)
   intros a b c d p Hp Hab Hcd hyp2; generalize Hp Hab Hcd; clear Hp Hab Hcd.
   pattern a, b, c, d, p, hyp2 in |- *.
   elim hyp2 using homographicAcc_ind_dep; clear a b c d p hyp2; intros.

    
    (* 1.1 *)
    simpl in |- *.
    case (Qpositive_dec_One p); intro Hp_; [ idtac | Falsum ].
    apply positive_fraction_encoding_equal. 
    (* 1.2 *)
    Falsum.
    (* 1.3 *)
    Falsum.
    (* 1.4 *)
    discriminate Hp.
    (* 1.5 *)
    discriminate Hp.


 (* 2nd big subgoal *)
   intros a b c d p Hp Habcd hyp1 H_ind hyp2; generalize Hp Habcd hyp1 H_ind;
    clear Hp Habcd H_ind hyp1.
   pattern a, b, c, d, p, hyp2 in |- *.
   elim hyp2 using homographicAcc_ind_dep; clear a b c d p hyp2; intros.

    
    (* 2.1 *)
    Falsum.
    (* 2.2 *)
    simpl in |- *; case (Qpositive_dec_One p); intro Hp_; [ Falsum | idtac ];
     case (top_more_informative a b c d); intro Habcd_; 
     [ idtac | Falsum ]; apply f_equal with Qpositive; 
     apply H_ind.
    (* 2.3 *)
    Falsum.
    (* 2.4 *)
    Falsum.
    (* 2.5 *)
    Falsum.

 (* 3rd big subgoal *)
   intros a b c d p Hp Habcd Hcdab hyp1 H_ind hyp2;
    generalize Hp Habcd Hcdab hyp1 H_ind; clear Hp Habcd Hcdab H_ind hyp1.
   pattern a, b, c, d, p, hyp2 in |- *.
   elim hyp2 using homographicAcc_ind_dep; clear a b c d p hyp2; intros.

    
    (* 3.1 *)
    Falsum.
    (* 3.2 *)
    Falsum.
    (* 3.3 *)
    simpl in |- *; case (Qpositive_dec_One p); intro Hp_; [ Falsum | idtac ];
     case (top_more_informative a b c d); intro Habcd_; 
     [ Falsum | idtac ]; case (top_more_informative c d a b); 
     intro Hcdab_; [ idtac | Falsum ]; apply f_equal with Qpositive;
     apply H_ind.
    (* 3.4 *)
    Falsum.
    (* 3.5 *)
    Falsum.

 (* 4th big subgoal *)
   intros a b c d xs Habcd Hcdab hyp1 H_ind hyp2.
   set (P := nR xs) in *; assert (HP : P = nR xs); trivial; generalize HP.
   generalize Habcd Hcdab hyp1 H_ind.
   clear Habcd Hcdab H_ind hyp1.
   (* here we copy-paste the current goal but change the 2nd occurnece of P to (dL xs) *)
   elim hyp2 using
    homographicAcc_ind_dep
     with
       (P := fun (a b c d : Z) (P : Qpositive)
               (hyp2 : homographicAcc a b c d P) =>
             forall (Habcd : ~ top_more a b c d) (Hcdab : ~ top_more c d a b)
               (hyp1 : homographicAcc a (a + b) c (c + d) xs),
             (forall hyp2 : homographicAcc a (a + b) c (c + d) xs,
              Qhomographic_Qpositive_to_Qpositive a (a + b) c (c + d) xs hyp1 =
              Qhomographic_Qpositive_to_Qpositive a (a + b) c (c + d) xs hyp2) ->
             P = nR xs ->
             Qhomographic_Qpositive_to_Qpositive a b c d 
               (nR xs) (homographicacc3 a b c d xs Habcd Hcdab hyp1) =
             Qhomographic_Qpositive_to_Qpositive a b c d P hyp2);
    clear a b c d hyp2; intros.
    
    (* 4.1 *)
    Falsum; rewrite H0 in e; discriminate e.
    (* 4.2 *)
    Falsum.
    (* 4.3 *)
    Falsum.
    (* 4.4 *)
    simpl in |- *.
    case (top_more_informative a b c d); intro Habcd_; [ Falsum | idtac ];
     case (top_more_informative c d a b); intro Hcdab_; 
     [ Falsum | idtac ].
    generalize h;
     let T_local := eval compute in (f_equal Qpositive_tail H1) in
     rewrite T_local.
    intro; apply H0.
    (* 4.5 *)
    discriminate H1.

 (* 5th big subgoal *)
   intros a b c d xs Habcd Hcdab hyp1 H_ind hyp2.
   set (P := dL xs) in *; assert (HP : P = dL xs); trivial; generalize HP.
   generalize Habcd Hcdab hyp1 H_ind.
   clear Habcd Hcdab H_ind hyp1.
   elim hyp2 using
    homographicAcc_ind_dep
     with
       (P := fun (a b c d : Z) (P : Qpositive)
               (hyp2 : homographicAcc a b c d P) =>
             forall (Habcd : ~ top_more a b c d) (Hcdab : ~ top_more c d a b)
               (hyp1 : homographicAcc (a + b) b (c + d) d xs),
             (forall hyp2 : homographicAcc (a + b) b (c + d) d xs,
              Qhomographic_Qpositive_to_Qpositive (a + b) b (c + d) d xs hyp1 =
              Qhomographic_Qpositive_to_Qpositive (a + b) b (c + d) d xs hyp2) ->
             P = dL xs ->
             Qhomographic_Qpositive_to_Qpositive a b c d 
               (dL xs) (homographicacc3' a b c d xs Habcd Hcdab hyp1) =
             Qhomographic_Qpositive_to_Qpositive a b c d P hyp2);
    clear a b c d hyp2; intros.
    
    (* 5.1 *)
    Falsum; rewrite H0 in e; discriminate e.
    (* 5.2 *)
    Falsum.
    (* 5.3 *)
    Falsum.
    (* 5.4 *)
    discriminate H1.
    (* 5.5 *)
    simpl in |- *.
    case (top_more_informative a b c d); intro Habcd_; [ Falsum | idtac ];
     case (top_more_informative c d a b); intro Hcdab_; 
     [ Falsum | idtac ].
    generalize h;
     let T_local := eval compute in (f_equal Qpositive_tail H1) in
     rewrite T_local.
    intro; apply H0.
Defined. 


Lemma Qhomographic_Qpositive_to_Qpositive_equal_strong :
 forall (a1 a2 b1 b2 c1 c2 d1 d2 : Z) (p1 p2 : Qpositive)
   (hyp1 : homographicAcc a1 b1 c1 d1 p1)
   (hyp2 : homographicAcc a2 b2 c2 d2 p2),
 a1 = a2 ->
 b1 = b2 ->
 c1 = c2 ->
 d1 = d2 ->
 p1 = p2 ->
 Qhomographic_Qpositive_to_Qpositive a1 b1 c1 d1 p1 hyp1 =
 Qhomographic_Qpositive_to_Qpositive a2 b2 c2 d2 p2 hyp2.
Proof.
 intros.
 subst.
 apply Qhomographic_Qpositive_to_Qpositive_equal. 
Defined.


(** Here we expand the fixpoint equations of "Qhomographic_Qpositive_to_Qpositive" function *)

Lemma Qhomographic_Qpositive_to_Qpositive_0 :
 forall (a b c d : Z) (p : Qpositive) (hyp : homographicAcc a b c d p),
 p = One ->
 forall (H1 : (0 < a + b)%Z) (H2 : (0 < c + d)%Z),
 Qhomographic_Qpositive_to_Qpositive a b c d p hyp =
 positive_fraction_encoding (a + b) (c + d) H1 H2. 
Proof. 
 intros. 
 apply
  trans_eq
   with
     (Qhomographic_Qpositive_to_Qpositive a b c d One
        (homographicacc0 a b c d One (refl_equal One) H1 H2)).
 apply Qhomographic_Qpositive_to_Qpositive_equal_strong; repeat reflexivity.
 assumption.
  simpl in |- *.
  apply positive_fraction_encoding_equal.
Defined.


Lemma Qhomographic_Qpositive_to_Qpositive_1 :
 forall (a b c d : Z) (p : Qpositive) (hyp : homographicAcc a b c d p),
 p <> One ->
 top_more a b c d ->
 forall h : homographicAcc (a - c) (b - d) c d p,
 Qhomographic_Qpositive_to_Qpositive a b c d p hyp =
 nR (Qhomographic_Qpositive_to_Qpositive (a - c) (b - d) c d p h).
Proof.
 intros.
 apply
  trans_eq
   with
     (Qhomographic_Qpositive_to_Qpositive a b c d p
        (homographicacc1 a b c d p H H0 h)).
 apply Qhomographic_Qpositive_to_Qpositive_equal.
  simpl in |- *.
  case (Qpositive_dec_One p); intros Hp; [ Falsum | idtac ].
  case (top_more_informative a b c d); intros Habcd; [ idtac | Falsum ].
  apply f_equal with Qpositive; reflexivity.
Defined.

Lemma Qhomographic_Qpositive_to_Qpositive_2 :
 forall (a b c d : Z) (p : Qpositive) (hyp : homographicAcc a b c d p),
 p <> One ->
 ~ top_more a b c d ->
 top_more c d a b ->
 forall h : homographicAcc a b (c - a) (d - b) p,
 Qhomographic_Qpositive_to_Qpositive a b c d p hyp =
 dL (Qhomographic_Qpositive_to_Qpositive a b (c - a) (d - b) p h).
Proof.
 intros.
 apply
  trans_eq
   with
     (Qhomographic_Qpositive_to_Qpositive a b c d p
        (homographicacc2 a b c d p H H0 H1 h)).
 apply Qhomographic_Qpositive_to_Qpositive_equal.
  simpl in |- *.
  case (Qpositive_dec_One p); intros Hp; [ Falsum | idtac ].
  case (top_more_informative a b c d); intros Habcd; [ Falsum | idtac ].
  case (top_more_informative c d a b); intros Hcdab; [ idtac | Falsum ].
  apply f_equal with Qpositive; reflexivity.
Defined.


Lemma Qhomographic_Qpositive_to_Qpositive_3 :
 forall (a b c d : Z) (p : Qpositive) (hyp : homographicAcc a b c d p),
 ~ top_more a b c d ->
 ~ top_more c d a b ->
 forall xs : Qpositive,
 p = nR xs ->
 forall h : homographicAcc a (a + b) c (c + d) xs,
 Qhomographic_Qpositive_to_Qpositive a b c d p hyp =
 Qhomographic_Qpositive_to_Qpositive a (a + b) c (c + d) xs h.
Proof.
 intros.
 apply
  trans_eq
   with
     (Qhomographic_Qpositive_to_Qpositive a b c d (nR xs)
        (homographicacc3 a b c d xs H H0 h)).
 apply Qhomographic_Qpositive_to_Qpositive_equal_strong; trivial.
  simpl in |- *.
  case (top_more_informative a b c d); intros Habcd; [ Falsum | idtac ].
  case (top_more_informative c d a b); intros Hcdab; [ Falsum | idtac ].
  reflexivity.
Defined.

Lemma Qhomographic_Qpositive_to_Qpositive_3' :
 forall (a b c d : Z) (p : Qpositive) (hyp : homographicAcc a b c d p),
 ~ top_more a b c d ->
 ~ top_more c d a b ->
 forall xs : Qpositive,
 p = dL xs ->
 forall h : homographicAcc (a + b) b (c + d) d xs,
 Qhomographic_Qpositive_to_Qpositive a b c d p hyp =
 Qhomographic_Qpositive_to_Qpositive (a + b) b (c + d) d xs h.
Proof.
 intros.
 apply
  trans_eq
   with
     (Qhomographic_Qpositive_to_Qpositive a b c d (dL xs)
        (homographicacc3' a b c d xs H H0 h)).
 apply Qhomographic_Qpositive_to_Qpositive_equal_strong; trivial.
  simpl in |- *.
  case (top_more_informative a b c d); intros Habcd; [ Falsum | idtac ].
  case (top_more_informative c d a b); intros Hcdab; [ Falsum | idtac ].
  reflexivity.
Defined.
