(************************************************************************)
(* Copyright 2007 Milad Niqui                                           *)
(* This file is distributed under the terms of the                      *)
(* GNU Lesser General Public License Version 2.1                        *)
(* A copy of the license can be found at                                *)
(*                  <http://www.gnu.org/licenses/lgpl.txt>              *)
(************************************************************************)

Require Import utf_AMM11262.
Import NatSet GeneralProperties.

Section example_three_inhabitants.
(** Now we find the witness, in a town with three inhabitants; ie, n=1 *)

Definition town_1:= {1}∪({2}∪({3}∪∅)).

Remark population₁ : |town_1| = 2×1 +1.
Proof.
 reflexivity.
Qed.

Definition familiarity₁ (m n:elt):Prop := 
  match m,n with
  | 1,2 => True
  | 2,1 => True
  | 2,3 => True
  | 3,2 => True
  | _,_ => False
  end.
Infix "ℛ₁" := familiarity₁ (at level 70, no associativity).

Remark familiarity₁_sym:∀ m n, m ℛ₁ n ⇒ n ℛ₁ m.
Proof.
 intros [|[|[|[|m']]]] [|[|[|[|n']]]]; trivial.
Qed. 

Remark familiarity₁_extensional:∀ m n p, n≡p ⇒ m ℛ₁ n ⇒ m ℛ₁ p.
Proof.
 intros m n p H1 H2; compute in H1; rewrite <- H1; assumption. 
Qed.


Remark subsets_1: ∀ B, B⊆town_1 ⇒ |B| = 1 ⇒ (B ≐ {1}∪∅ \/ B ≐ {2}∪∅ ) ∨ B ≐ {3}∪∅.
Proof.
 intros B H_sub H_card.
 destruct (In_dec 1 B) as [H1|H1].
  (* 1∈B *)
  left; left;
  rewrite <- (add_remove H1); generalize (remove_cardinal_1 H1); rewrite H_card; intro H_eq;
  rewrite (empty_is_empty_1 (cardinal_inv_1 (eq_add_S _ _ H_eq))); reflexivity...
  (* ¬ 1∈B *)
  destruct (In_dec 2 B) as [H2|H2].
   (* 2∈B *)
   left; right;
   rewrite <- (add_remove H2); generalize (remove_cardinal_1 H2); rewrite H_card; intro H_eq;
   rewrite (empty_is_empty_1 (cardinal_inv_1 (eq_add_S _ _ H_eq))); reflexivity...
   (* ¬ 2∈B *)
   destruct (In_dec 3 B) as [H3|H3].
    (* 3∈B *)
    right;
    rewrite <- (add_remove H3); generalize (remove_cardinal_1 H3); rewrite H_card; intro H_eq;
    rewrite (empty_is_empty_1 (cardinal_inv_1 (eq_add_S _ _ H_eq))); reflexivity...
    (* ¬ 3∈B *)
    apply False_rec.
    destruct (cardinal_inv_2 H_card) as [b Hb].
    destruct (NatSet.E.eq_dec b 1) as [Hb1|Hb1].
     apply H1; rewrite <- Hb1; assumption.
     destruct (NatSet.E.eq_dec b 2) as [Hb2|Hb2].
     apply H2; rewrite <- Hb2; assumption.
     destruct (NatSet.E.eq_dec b 3) as [Hb3|Hb3].
      apply H3; rewrite <- Hb3; assumption.

      assert (Hb_town:=H_sub _ Hb).
      unfold town_1 in Hb_town.
      destruct (proj1 (FM.add_iff _ _ b) Hb_town) as [Hb1_town|Hb1_town].
       apply Hb1; rewrite Hb1_town; reflexivity.
       destruct (proj1 (FM.add_iff _ _ b) Hb1_town) as [Hb2_town|Hb2_town].
        apply Hb2; rewrite Hb2_town; reflexivity.
        destruct (proj1 (FM.add_iff _ _ b) Hb2_town) as [Hb3_town|Hb3_town].
         apply Hb3; rewrite Hb3_town; reflexivity.
         apply (proj1 (FM.empty_iff b) Hb3_town).
Qed.
      

Remark acquintance_1: ∀ B, B⊆town_1 ⇒ |B| = 1 ⇒ 
          ∃d, d∈(town_1\B) ∧ (∀ b, b∈B ⇒ d ℛ₁ b).
Proof.
 intros B H_sub H_card.
 destruct (subsets_1 B H_sub H_card) as [[HB1|HB2]|HB3].
  (* B={1} *)
  exists 2; split.
   rewrite HB1; apply mem_2; trivial.
   intro b; rewrite HB1; intro Hb.
   destruct (proj1 (FM.add_iff _ _ b) Hb) as [H|H].
    compute in H; rewrite <- H; simpl; trivial.
    apply False_ind; apply (proj1 (FM.empty_iff b) H).
  (* B={2} *)
  exists 1; split.
   rewrite HB2; apply mem_2; trivial.
   intro b; rewrite HB2; intro Hb.
   destruct (proj1 (FM.add_iff _ _ b) Hb) as [H|H].
    compute in H; rewrite <- H; simpl; trivial.
    apply False_ind; apply (proj1 (FM.empty_iff b) H).
  (* B={3} *)
  exists 2; split.
   rewrite HB3; apply mem_2; trivial.
   intro b; rewrite HB3; intro Hb.
   destruct (proj1 (FM.add_iff _ _ b) Hb) as [H|H].
    compute in H; rewrite <- H; simpl; trivial.
    apply False_ind; apply (proj1 (FM.empty_iff b) H).
Defined.

Check (AMM11262 town_1 1 population₁ familiarity₁ familiarity₁_sym familiarity₁_extensional acquintance_1).

Definition social_citizen_1:=AMM11262 town_1 1 population₁ familiarity₁ 
                                      familiarity₁_sym familiarity₁_extensional acquintance_1.


End example_three_inhabitants.

Extraction "social1" social_citizen_1.
