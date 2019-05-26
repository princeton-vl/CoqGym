(************************************************************************)
(* Copyright 2007 Milad Niqui                                           *)
(* This file is distributed under the terms of the                      *)
(* GNU Lesser General Public License Version 2.1                        *)
(* A copy of the license can be found at                                *)
(*                  <http://www.gnu.org/licenses/lgpl.txt>              *)
(************************************************************************)

Require Import utf_AMM11262.
Import NatSet GeneralProperties.

Section example_five_inhabitants.
(** Now we find the witness, in a town with 5 inhabitants; ie, n=2 *)

Definition town_2:= {1}∪({2}∪({3}∪({4}∪({5}∪∅)))).

Remark population₂ : |town_2| = 2×2 +1.
Proof.
 reflexivity.
Qed.


(* (1,2),(1,3),(1,4),(1,5),
   (2,5),
   (3,4),(3,5)
*)

Definition familiarity₂ (m n:elt):Prop := 
  match m,n with
  | 1,2=> True
  | 1,3 => True
  | 1,4 => True
  | 1,5 => True
  | 2,1 => True
  | 2,5 => True
  | 3,1 => True
  | 3,4 => True
  | 3,5 => True
  | 4,1 => True
  | 4,3 => True
  | 5,1 => True
  | 5,2 => True
  | 5,3 => True
  | _,_ => False
  end.
Infix "ℛ₂" := familiarity₂ (at level 70, no associativity).

Remark familiarity₂_sym:∀ m n, m ℛ₂ n ⇒ n ℛ₂ m.
Proof.
 intros [|[|[|[|[|[|m']]]]]] [|[|[|[|[|[|n']]]]]]; trivial.
Qed. 

Remark familiarity₂_extensional:∀ m n p, n≡p ⇒ m ℛ₂ n ⇒ m ℛ₂ p.
Proof.
 intros m n p H1 H2; compute in H1; rewrite <- H1; assumption. 
Qed.


Remark subsets_2: ∀ B, B⊆town_2 ⇒ |B| = 2 ⇒ 
  (((((((((B ≐ {1}∪({2}∪∅)\/ B≐{1}∪({3}∪∅)) ∨ B≐{1}∪({4}∪∅)) ∨ B ≐ {1}∪({5}∪∅)) ∨ B≐{2}∪({3}∪∅)) ∨ 
   B≐{2}∪({4}∪∅)) ∨ B≐{2}∪({5}∪∅)) ∨ B≐{3}∪({4}∪∅)) ∨ B ≐ {3}∪({5}∪∅)) ∨ B≐{4}∪({5}∪∅)).
Proof.
 intros B H_sub H_card.
 destruct (In_dec 1 B) as [H1|H1].
  (* 1∈B *)
  do 6 left. 
  assert (H_card_rem:|B\{1}|=1);
  [ rewrite <- (remove_cardinal_1 H1) in H_card; apply eq_add_S; assumption|].
  destruct (In_dec 2 (B\{1})) as [H12|H12].
   (* B={1,2} *)
   do 3 left.
   rewrite <- (add_remove H1).
   rewrite <- (add_remove H12).
   generalize (remove_cardinal_1 H12).
   rewrite H_card_rem; intro H_eq2.
   rewrite (empty_is_empty_1 (cardinal_inv_1 (eq_add_S _ _ H_eq2))); reflexivity...
   (* ¬ 2∈B *)
   destruct (In_dec 3 (B\{1})) as [H13|H13].
    (* B={1,3} *)
    do 2 left; right.
    rewrite <- (add_remove H1).
    rewrite <- (add_remove H13).
    generalize (remove_cardinal_1 H13).
    rewrite H_card_rem; intro H_eq2.
    rewrite (empty_is_empty_1 (cardinal_inv_1 (eq_add_S _ _ H_eq2))); reflexivity...
    (* ¬ 3∈B *)
    destruct (In_dec 4 (B\{1})) as [H14|H14].
     (* B={1,4} *)
     left; right.
     rewrite <- (add_remove H1).
     rewrite <- (add_remove H14).
     generalize (remove_cardinal_1 H14).
     rewrite H_card_rem; intro H_eq2.
     rewrite (empty_is_empty_1 (cardinal_inv_1 (eq_add_S _ _ H_eq2))); reflexivity...
     (* ¬ 4∈B *)
     destruct (In_dec 5 (B\{1})) as [H15|H15].
      (* B={1,5} *)
      right.
      rewrite <- (add_remove H1).
      rewrite <- (add_remove H15).
      generalize (remove_cardinal_1 H15).
      rewrite H_card_rem; intro H_eq2.
      rewrite (empty_is_empty_1 (cardinal_inv_1 (eq_add_S _ _ H_eq2))); reflexivity...
      (* ¬ 5∈B *)
      apply False_rec.
      assert (H11:=(@remove_1 B _ _ (refl_equal 1))).
      destruct (cardinal_inv_2 H_card_rem) as [b Hb].
       destruct (NatSet.E.eq_dec b 1) as [Hb1|Hb1].
        apply H11; rewrite Hb1 in Hb; assumption.
        destruct (NatSet.E.eq_dec b 2) as [Hb2|Hb2].
         apply H12; rewrite <- Hb2; assumption.
         destruct (NatSet.E.eq_dec b 3) as [Hb3|Hb3].
          apply H13; rewrite <- Hb3; assumption.
          destruct (NatSet.E.eq_dec b 4) as [Hb4|Hb4].
           apply H14; rewrite <- Hb4; assumption.
           destruct (NatSet.E.eq_dec b 5) as [Hb5|Hb5].
            apply H15; rewrite <- Hb5; assumption.

            assert (H_sub':=@subset_remove_3 _ _ 1 H_sub).
            assert (Hb_town:=H_sub' _ Hb).
            unfold town_2 in Hb_town.
            destruct (proj1 (FM.add_iff _ _ b) Hb_town) as [Hb1_town|Hb1_town].
             apply Hb1; rewrite Hb1_town; reflexivity.
             destruct (proj1 (FM.add_iff _ _ b) Hb1_town) as [Hb2_town|Hb2_town].
              apply Hb2; rewrite Hb2_town; reflexivity.
               destruct (proj1 (FM.add_iff _ _ b) Hb2_town) as [Hb3_town|Hb3_town].
                apply Hb3; rewrite Hb3_town; reflexivity.
                destruct (proj1 (FM.add_iff _ _ b) Hb3_town) as [Hb4_town|Hb4_town].
                 apply Hb4; rewrite Hb4_town; reflexivity.
                 destruct (proj1 (FM.add_iff _ _ b) Hb4_town) as [Hb5_town|Hb5_town].
                  apply Hb5; rewrite Hb5_town; reflexivity.
                  apply (proj1 (FM.empty_iff b) Hb5_town)...
  (* ¬ 1∈B *)
  destruct (In_dec 2 B) as [H2|H2].
   (* 2∈B *)
   assert (H_card_rem:|B\{2}|=1);
   [ rewrite <- (remove_cardinal_1 H2) in H_card; apply eq_add_S; assumption|].
   assert (H21:=fun HH : 1∈(B\{2}) => H1 (remove_3 HH)).  
   destruct (In_dec 3 (B\{2})) as [H23|H23].
    (* B={2,3} *)
    do 5 left; right.
    rewrite <- (add_remove H2).
    rewrite <- (add_remove H23).
    generalize (remove_cardinal_1 H23).
    rewrite H_card_rem; intro H_eq2.
    rewrite (empty_is_empty_1 (cardinal_inv_1 (eq_add_S _ _ H_eq2))); reflexivity...
    (* ¬ 3∈B *)
    destruct (In_dec 4 (B\{2})) as [H24|H24].
     (* B={2,4} *)
     do 4 left; right.
     rewrite <- (add_remove H2).
     rewrite <- (add_remove H24).
     generalize (remove_cardinal_1 H24).
     rewrite H_card_rem; intro H_eq2.
     rewrite (empty_is_empty_1 (cardinal_inv_1 (eq_add_S _ _ H_eq2))); reflexivity...
     (* ¬ 4∈B *)
     destruct (In_dec 5 (B\{2})) as [H25|H25].
      (* B={2,5} *)
      do 3 left; right.
      rewrite <- (add_remove H2).
      rewrite <- (add_remove H25).
      generalize (remove_cardinal_1 H25).
      rewrite H_card_rem; intro H_eq2.
      rewrite (empty_is_empty_1 (cardinal_inv_1 (eq_add_S _ _ H_eq2))); reflexivity...
      (* ¬ 5∈B *)
      apply False_rec.
      assert (H22:=(@remove_1 B _ _ (refl_equal 2))).
      destruct (cardinal_inv_2 H_card_rem) as [b Hb].
       destruct (NatSet.E.eq_dec b 1) as [Hb1|Hb1].
        apply H21; rewrite Hb1 in Hb; assumption.
        destruct (NatSet.E.eq_dec b 2) as [Hb2|Hb2].
         apply H22; rewrite Hb2 in Hb; assumption.
         destruct (NatSet.E.eq_dec b 3) as [Hb3|Hb3].
          apply H23; rewrite <- Hb3; assumption.
          destruct (NatSet.E.eq_dec b 4) as [Hb4|Hb4].
           apply H24; rewrite <- Hb4; assumption.
           destruct (NatSet.E.eq_dec b 5) as [Hb5|Hb5].
            apply H25; rewrite <- Hb5; assumption.

            assert (H_sub':=@subset_remove_3 _ _ 2 H_sub).
            assert (Hb_town:=H_sub' _ Hb).
            unfold town_2 in Hb_town.
            destruct (proj1 (FM.add_iff _ _ b) Hb_town) as [Hb1_town|Hb1_town].
             apply Hb1; rewrite Hb1_town; reflexivity.
             destruct (proj1 (FM.add_iff _ _ b) Hb1_town) as [Hb2_town|Hb2_town].
              apply Hb2; rewrite Hb2_town; reflexivity.
               destruct (proj1 (FM.add_iff _ _ b) Hb2_town) as [Hb3_town|Hb3_town].
                apply Hb3; rewrite Hb3_town; reflexivity.
                destruct (proj1 (FM.add_iff _ _ b) Hb3_town) as [Hb4_town|Hb4_town].
                 apply Hb4; rewrite Hb4_town; reflexivity.
                 destruct (proj1 (FM.add_iff _ _ b) Hb4_town) as [Hb5_town|Hb5_town].
                  apply Hb5; rewrite Hb5_town; reflexivity.
                  apply (proj1 (FM.empty_iff b) Hb5_town)...
   (* ¬ 2∈B *)
   destruct (In_dec 3 B) as [H3|H3].
    (* 3∈B *)
    assert (H_card_rem:|B\{3}|=1);
    [ rewrite <- (remove_cardinal_1 H3) in H_card; apply eq_add_S; assumption|].
    assert (H31:=fun HH : 1∈(B\{3}) => H1 (remove_3 HH)).
    assert (H32:=fun HH : 2∈(B\{3}) => H2 (remove_3 HH)).  
    destruct (In_dec 4 (B\{3})) as [H34|H34].
     (* B={3,4} *)
     do 2 left; right.
     rewrite <- (add_remove H3).
     rewrite <- (add_remove H34).
     generalize (remove_cardinal_1 H34).
     rewrite H_card_rem; intro H_eq2.
     rewrite (empty_is_empty_1 (cardinal_inv_1 (eq_add_S _ _ H_eq2))); reflexivity...
     (* ¬ 4∈B *)
     destruct (In_dec 5 (B\{3})) as [H35|H35].
      (* B={3,5} *)
      left; right.
      rewrite <- (add_remove H3).
      rewrite <- (add_remove H35).
      generalize (remove_cardinal_1 H35).
      rewrite H_card_rem; intro H_eq2.
      rewrite (empty_is_empty_1 (cardinal_inv_1 (eq_add_S _ _ H_eq2))); reflexivity...
      (* ¬ 5∈B *)
      apply False_rec.
      assert (H33:=(@remove_1 B _ _ (refl_equal 3))).
      destruct (cardinal_inv_2 H_card_rem) as [b Hb].
       destruct (NatSet.E.eq_dec b 1) as [Hb1|Hb1].
        apply H31; rewrite Hb1 in Hb; assumption.
        destruct (NatSet.E.eq_dec b 2) as [Hb2|Hb2].
         apply H32; rewrite Hb2 in Hb; assumption.
         destruct (NatSet.E.eq_dec b 3) as [Hb3|Hb3].
          apply H33; rewrite Hb3 in Hb; assumption.
          destruct (NatSet.E.eq_dec b 4) as [Hb4|Hb4].
           apply H34; rewrite <- Hb4; assumption.
           destruct (NatSet.E.eq_dec b 5) as [Hb5|Hb5].
            apply H35; rewrite <- Hb5; assumption.

            assert (H_sub':=@subset_remove_3 _ _ 3 H_sub).
            assert (Hb_town:=H_sub' _ Hb).
            unfold town_2 in Hb_town.
            destruct (proj1 (FM.add_iff _ _ b) Hb_town) as [Hb1_town|Hb1_town].
             apply Hb1; rewrite Hb1_town; reflexivity.
             destruct (proj1 (FM.add_iff _ _ b) Hb1_town) as [Hb2_town|Hb2_town].
              apply Hb2; rewrite Hb2_town; reflexivity.
               destruct (proj1 (FM.add_iff _ _ b) Hb2_town) as [Hb3_town|Hb3_town].
                apply Hb3; rewrite Hb3_town; reflexivity.
                destruct (proj1 (FM.add_iff _ _ b) Hb3_town) as [Hb4_town|Hb4_town].
                 apply Hb4; rewrite Hb4_town; reflexivity.
                 destruct (proj1 (FM.add_iff _ _ b) Hb4_town) as [Hb5_town|Hb5_town].
                  apply Hb5; rewrite Hb5_town; reflexivity.
                  apply (proj1 (FM.empty_iff b) Hb5_town)...
    (* ¬ 3∈B *)
    destruct (In_dec 4 B) as [H4|H4].
     (* 4∈B *)
     assert (H_card_rem:|B\{4}|=1);
     [ rewrite <- (remove_cardinal_1 H4) in H_card; apply eq_add_S; assumption|].
     assert (H41:=fun HH : 1∈(B\{4}) => H1 (remove_3 HH)).
     assert (H42:=fun HH : 2∈(B\{4}) => H2 (remove_3 HH)).
     assert (H43:=fun HH : 3∈(B\{4}) => H3 (remove_3 HH)).  
     destruct (In_dec 5 (B\{4})) as [H45|H45].
      (* B={4,5} *)
      right.
      rewrite <- (add_remove H4).
      rewrite <- (add_remove H45).
      generalize (remove_cardinal_1 H45).
      rewrite H_card_rem; intro H_eq2.
      rewrite (empty_is_empty_1 (cardinal_inv_1 (eq_add_S _ _ H_eq2))); reflexivity...
      (* ¬ 5∈B *)
      apply False_rec.
      assert (H44:=(@remove_1 B _ _ (refl_equal 4))).
      destruct (cardinal_inv_2 H_card_rem) as [b Hb].
       destruct (NatSet.E.eq_dec b 1) as [Hb1|Hb1].
        apply H41; rewrite Hb1 in Hb; assumption.
        destruct (NatSet.E.eq_dec b 2) as [Hb2|Hb2].
         apply H42; rewrite Hb2 in Hb; assumption.
         destruct (NatSet.E.eq_dec b 3) as [Hb3|Hb3].
          apply H43; rewrite Hb3 in Hb; assumption.
          destruct (NatSet.E.eq_dec b 4) as [Hb4|Hb4].
           apply H44; rewrite Hb4 in Hb; assumption.
           destruct (NatSet.E.eq_dec b 5) as [Hb5|Hb5].
            apply H45; rewrite <- Hb5; assumption.

            assert (H_sub':=@subset_remove_3 _ _ 4 H_sub).
            assert (Hb_town:=H_sub' _ Hb).
            unfold town_2 in Hb_town.
            destruct (proj1 (FM.add_iff _ _ b) Hb_town) as [Hb1_town|Hb1_town].
             apply Hb1; rewrite Hb1_town; reflexivity.
             destruct (proj1 (FM.add_iff _ _ b) Hb1_town) as [Hb2_town|Hb2_town].
              apply Hb2; rewrite Hb2_town; reflexivity.
               destruct (proj1 (FM.add_iff _ _ b) Hb2_town) as [Hb3_town|Hb3_town].
                apply Hb3; rewrite Hb3_town; reflexivity.
                destruct (proj1 (FM.add_iff _ _ b) Hb3_town) as [Hb4_town|Hb4_town].
                 apply Hb4; rewrite Hb4_town; reflexivity.
                 destruct (proj1 (FM.add_iff _ _ b) Hb4_town) as [Hb5_town|Hb5_town].
                  apply Hb5; rewrite Hb5_town; reflexivity.
                  apply (proj1 (FM.empty_iff b) Hb5_town)...
     (* ¬ 4∈B *)
     apply False_rec.
     destruct (In_dec 5 B) as [H5|H5].
      (* 5∈ B *)
      assert (H_card_rem:|B\{5}|=1);
      [ rewrite <- (remove_cardinal_1 H5) in H_card; apply eq_add_S; assumption|].
      assert (H51:=fun HH : 1∈(B\{5}) => H1 (remove_3 HH)).
      assert (H52:=fun HH : 2∈(B\{5}) => H2 (remove_3 HH)).
      assert (H53:=fun HH : 3∈(B\{5}) => H3 (remove_3 HH)).
      assert (H54:=fun HH : 4∈(B\{5}) => H4 (remove_3 HH)).
      assert (H55:=(@remove_1 B _ _ (refl_equal 5))).
      destruct (cardinal_inv_2 H_card_rem) as [b Hb].
      assert (H_sub':=@subset_remove_3 _ _ 5 H_sub).
      assert (Hb_town:=H_sub' _ Hb).
      unfold town_2 in Hb_town.
      destruct (proj1 (FM.add_iff _ _ b) Hb_town) as [Hb1_town|Hb1_town].
       apply H51; rewrite <- Hb1_town in Hb; assumption. 
       destruct (proj1 (FM.add_iff _ _ b) Hb1_town) as [Hb2_town|Hb2_town].
        apply H52; rewrite <- Hb2_town in Hb; assumption. 
         destruct (proj1 (FM.add_iff _ _ b) Hb2_town) as [Hb3_town|Hb3_town].
          apply H53; rewrite <- Hb3_town in Hb; assumption.
          destruct (proj1 (FM.add_iff _ _ b) Hb3_town) as [Hb4_town|Hb4_town].
           apply H54; rewrite <- Hb4_town in Hb; assumption.
           destruct (proj1 (FM.add_iff _ _ b) Hb4_town) as [Hb5_town|Hb5_town].
            apply H55; rewrite <- Hb5_town in Hb; assumption.
            apply (proj1 (FM.empty_iff b) Hb5_town)...
      (* 1,2,3,4,5 ∈ B *)
      destruct (cardinal_inv_2 H_card) as [b Hb].
       destruct (NatSet.E.eq_dec b 1) as [Hb1|Hb1].
        apply H1; rewrite Hb1 in Hb; assumption.
        destruct (NatSet.E.eq_dec b 2) as [Hb2|Hb2].
         apply H2; rewrite Hb2 in Hb; assumption.
         destruct (NatSet.E.eq_dec b 3) as [Hb3|Hb3].
          apply H3; rewrite Hb3 in Hb; assumption.
          destruct (NatSet.E.eq_dec b 4) as [Hb4|Hb4].
           apply H4; rewrite Hb4 in Hb; assumption.
           destruct (NatSet.E.eq_dec b 5) as [Hb5|Hb5].
            apply H5; rewrite <- Hb5; assumption.

            assert (Hb_town:=H_sub _ Hb).
            unfold town_2 in Hb_town.
            destruct (proj1 (FM.add_iff _ _ b) Hb_town) as [Hb1_town|Hb1_town].
             apply Hb1; rewrite Hb1_town; reflexivity.
             destruct (proj1 (FM.add_iff _ _ b) Hb1_town) as [Hb2_town|Hb2_town].
              apply Hb2; rewrite Hb2_town; reflexivity.
               destruct (proj1 (FM.add_iff _ _ b) Hb2_town) as [Hb3_town|Hb3_town].
                apply Hb3; rewrite Hb3_town; reflexivity.
                destruct (proj1 (FM.add_iff _ _ b) Hb3_town) as [Hb4_town|Hb4_town].
                 apply Hb4; rewrite Hb4_town; reflexivity.
                 destruct (proj1 (FM.add_iff _ _ b) Hb4_town) as [Hb5_town|Hb5_town].
                  apply Hb5; rewrite Hb5_town; reflexivity.
                  apply (proj1 (FM.empty_iff b) Hb5_town)...
Qed.
      

Remark acquintance_2: ∀ B, B⊆town_2 ⇒ |B| = 2 ⇒ 
          ∃d, d∈(town_2\B) ∧ (∀ b, b∈B ⇒ d ℛ₂ b).
Proof.
 intros B H_sub H_card.
 destruct (subsets_2 B H_sub H_card) as [[[[[[[[[HB12|HB13]|HB14]|HB15]|HB23]|HB24]|HB25]|HB34]|HB35]|HB45].
  (* B={1,2} *)
  exists 5; split.
   rewrite HB12; apply mem_2; trivial.
   intro b; rewrite HB12; intro Hb.
   destruct (proj1 (FM.add_iff _ _ b) Hb) as [H|H].
    compute in H; rewrite <- H; simpl; trivial.
    destruct (proj1 (FM.add_iff _ _ b) H) as [H'|H'].
     compute in H'; rewrite <- H'; simpl; trivial.
     apply False_ind; apply (proj1 (FM.empty_iff b) H').
  (* B={1,3} *)
  exists 4; split.
   rewrite HB13; apply mem_2; trivial.
   intro b; rewrite HB13; intro Hb.
   destruct (proj1 (FM.add_iff _ _ b) Hb) as [H|H].
    compute in H; rewrite <- H; simpl; trivial.
    destruct (proj1 (FM.add_iff _ _ b) H) as [H'|H'].
     compute in H'; rewrite <- H'; simpl; trivial.
     apply False_ind; apply (proj1 (FM.empty_iff b) H').
  (* B={1,4} *)
  exists 3; split.
   rewrite HB14; apply mem_2; trivial.
   intro b; rewrite HB14; intro Hb.
   destruct (proj1 (FM.add_iff _ _ b) Hb) as [H|H].
    compute in H; rewrite <- H; simpl; trivial.
    destruct (proj1 (FM.add_iff _ _ b) H) as [H'|H'].
     compute in H'; rewrite <- H'; simpl; trivial.
     apply False_ind; apply (proj1 (FM.empty_iff b) H').
  (* B={1,5} *)
  exists 2; split.
   rewrite HB15; apply mem_2; trivial.
   intro b; rewrite HB15; intro Hb.
   destruct (proj1 (FM.add_iff _ _ b) Hb) as [H|H].
    compute in H; rewrite <- H; simpl; trivial.
    destruct (proj1 (FM.add_iff _ _ b) H) as [H'|H'].
     compute in H'; rewrite <- H'; simpl; trivial.
     apply False_ind; apply (proj1 (FM.empty_iff b) H').
  (* B={2,3} *)
  exists 5; split.
   rewrite HB23; apply mem_2; trivial.
   intro b; rewrite HB23; intro Hb.
   destruct (proj1 (FM.add_iff _ _ b) Hb) as [H|H].
    compute in H; rewrite <- H; simpl; trivial.
    destruct (proj1 (FM.add_iff _ _ b) H) as [H'|H'].
     compute in H'; rewrite <- H'; simpl; trivial.
     apply False_ind; apply (proj1 (FM.empty_iff b) H').
  (* B={2,4} *)
  exists 1; split.
   rewrite HB24; apply mem_2; trivial.
   intro b; rewrite HB24; intro Hb.
   destruct (proj1 (FM.add_iff _ _ b) Hb) as [H|H].
    compute in H; rewrite <- H; simpl; trivial.
    destruct (proj1 (FM.add_iff _ _ b) H) as [H'|H'].
     compute in H'; rewrite <- H'; simpl; trivial.
     apply False_ind; apply (proj1 (FM.empty_iff b) H').
  (* B={2,5} *)
  exists 1; split.
   rewrite HB25; apply mem_2; trivial.
   intro b; rewrite HB25; intro Hb.
   destruct (proj1 (FM.add_iff _ _ b) Hb) as [H|H].
    compute in H; rewrite <- H; simpl; trivial.
    destruct (proj1 (FM.add_iff _ _ b) H) as [H'|H'].
     compute in H'; rewrite <- H'; simpl; trivial.
     apply False_ind; apply (proj1 (FM.empty_iff b) H').
  (* B={3,4} *)
  exists 1; split.
   rewrite HB34; apply mem_2; trivial.
   intro b; rewrite HB34; intro Hb.
   destruct (proj1 (FM.add_iff _ _ b) Hb) as [H|H].
    compute in H; rewrite <- H; simpl; trivial.
    destruct (proj1 (FM.add_iff _ _ b) H) as [H'|H'].
     compute in H'; rewrite <- H'; simpl; trivial.
     apply False_ind; apply (proj1 (FM.empty_iff b) H').
  (* B={3,5} *)
  exists 1; split.
   rewrite HB35; apply mem_2; trivial.
   intro b; rewrite HB35; intro Hb.
   destruct (proj1 (FM.add_iff _ _ b) Hb) as [H|H].
    compute in H; rewrite <- H; simpl; trivial.
    destruct (proj1 (FM.add_iff _ _ b) H) as [H'|H'].
     compute in H'; rewrite <- H'; simpl; trivial.
     apply False_ind; apply (proj1 (FM.empty_iff b) H').
  (* B={4,5} *)
  exists 3; split.
   rewrite HB45; apply mem_2; trivial.
   intro b; rewrite HB45; intro Hb.
   destruct (proj1 (FM.add_iff _ _ b) Hb) as [H|H].
    compute in H; rewrite <- H; simpl; trivial.
    destruct (proj1 (FM.add_iff _ _ b) H) as [H'|H'].
     compute in H'; rewrite <- H'; simpl; trivial.
     apply False_ind; apply (proj1 (FM.empty_iff b) H').
Defined.

Check (AMM11262 town_2 2 population₂ familiarity₂ familiarity₂_sym familiarity₂_extensional acquintance_2).

Definition social_citizen_2:=AMM11262 town_2 2 population₂ familiarity₂ 
                                      familiarity₂_sym familiarity₂_extensional acquintance_2.

End example_five_inhabitants.


Extraction "social2" social_citizen_2.
