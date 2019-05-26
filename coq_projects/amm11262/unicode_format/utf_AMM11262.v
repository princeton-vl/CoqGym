(************************************************************************)
(* Copyright 2007 Milad Niqui                                           *)
(* This file is distributed under the terms of the                      *)
(* GNU Lesser General Public License Version 2.1                        *)
(* A copy of the license can be found at                                *)
(*                  <http://www.gnu.org/licenses/lgpl.txt>              *)
(************************************************************************)

Require Import Arith Omega.

Require OrderedTypeEx.
Require FSetList.
Require Extraction.
Module NatSet := FSetList.Make(OrderedTypeEx.Nat_as_OT).
Import NatSet.

Notation " A ⇒ B " := (A -> B) (at level 90, right associativity) : type_scope.
Notation " ∀ x , B  " := (forall x:_, B ) (at level 200, x at level 0, no associativity) : type_scope.
Notation " ∀ x y , B  " := (forall (x:_) (y:_), B ) (at level 200, x at level 0, y at level 0, no associativity) : type_scope.
Notation " ∀ x y z , B  " := (forall (x:_) (y:_) (z:_), B ) (at level 200, x at level 0, y at level 0, z at level 0, no associativity) : type_scope.
Notation " ¬ x " := (not  x) (at level 75, right associativity) : type_scope.
Notation " A ∧ B " := (A /\ B) (at level 80, right associativity) : type_scope.
Notation " A ∨ B " := (sumor A B) (at level 85, right associativity) : type_scope.
Notation " A \/ B " := (sumbool A B) (at level 85, right associativity) : type_scope.
Notation " ∃ x , B  " := (sig (fun x:_=>B) ) (at level 0, x at level 99, no associativity) : type_scope.
Notation " A × B " := (A * B) (at level 40, left associativity) : type_scope.
Notation " 'ℕ' " := nat : type_scope.
Infix " ≤ " := le (at level 70, right associativity): nat_scope.
Notation "s ≐ t" := (Equal s t) (at level 70, no associativity).
Infix "∈" := In (at level 30, no associativity).
Infix "⊆" := Subset (at level 70, right associativity).
Infix "\" := diff (at level 40, left associativity).
Notation "| A |" := (cardinal A) (at level 10, no associativity).
Infix "≡" := E.eq (at level 70, no associativity).
Infix "∩" := inter (at level 40, left associativity).
Infix "∪" := union (at level 50, left associativity).
Notation " { x } ∪ X " := (add x X) (at level 50, left associativity).
Notation " X \ { x } " := (remove x X) (at level 40, left associativity).
Notation "∅" := empty.

Require FSetFacts FSetProperties.

Module GeneralProperties := FSetProperties.Properties NatSet.
Import GeneralProperties.

Section problem_knows_not_refl.

Variable town: t.
Variable n:ℕ.
Variable cardinality: | town | = 2×n+1.

Variable knows: elt ⇒ elt ⇒ Prop. 
Infix "ℛ" := knows (at level 70, no associativity).

Variable knows_sym: ∀m n, m ℛ n ⇒ n ℛ m.
Variable knows_extensional:∀m n p, n≡p ⇒ m ℛ n⇒ m ℛ p.

Variable property: ∀B, B ⊆ town ⇒ |B| = n ⇒ 
           ∃d, d∈(town\B) /\ (∀b, b∈B ⇒ d ℛ b).

Lemma extendible_by_one:∀ B', |B'| ≤ |town| -1 ⇒ ∃d, d∈town ∧ ¬(d∈B').
Proof.
 clear knows knows_sym knows_extensional property.
 intros B' H_cardinal_town.
 assert (H_town:1≤ |town|); [omega|].
 rewrite <- (diff_inter_cardinal town B') in H_cardinal_town.
 rewrite <- (diff_inter_cardinal town B') in H_town.
 assert (H_inter:|town∩B'| ≤ |B'|);
  [apply (subset_cardinal);apply (inter_subset_2)|].
 generalize (le_trans _ _ _ H_inter H_cardinal_town); intro H1.
 assert (H2:1≤|town\B'|); [omega|].
 assert (H3:=(S_pred _ _ H2)).
 destruct (cardinal_inv_2 H3) as [d Hd].
 exists d; split.
  apply diff_1 with B'; assumption.
  apply diff_2 with town; assumption.
Qed.  

Lemma extendible_to_n:∀ B', B'⊆town ⇒ |B'| ≤ n ⇒ ∃B, |B| = n ∧  B'⊆B ∧ B⊆town.  
Proof.
 intros B' H_sub H_B'_cardinal.
 assert (H_cardinal_aux_3:2×n≤ |town| -1);[apply le_trans with (2×n); omega|].
 clear property.
 induction n in H_B'_cardinal, H_cardinal_aux_3 |- *.
 (* n = 0 *)
 generalize (sym_eq (le_n_O_eq _ H_B'_cardinal)); intro H_eq.
 generalize (empty_is_empty_1 (cardinal_inv_1 H_eq)).
 intro H_B'.
 exists ∅; repeat split. 
  rewrite H_B'; apply subset_empty.
  apply subset_empty.
 (* n = S n0 *)
 destruct (le_lt_eq_dec _ _ H_B'_cardinal) as [H_lt|H_le].
  generalize (lt_n_Sm_le _ _ H_lt); clear H_lt; intro H_le.
  assert (H_cardinal_town_2:2 * n0 ≤ |town| - 1);[omega|].
  destruct (IHn0 H_le H_cardinal_town_2) as [C [HC1 [HC2 HC3]]].
  assert (HC5:|C| ≤ |town| - 1).
   rewrite HC1; apply le_trans with (2×(S n0));[omega| assumption].
  destruct (extendible_by_one C HC5) as [d [Hd1 Hd2]].
  exists ({d} ∪ C).
  repeat split.
   rewrite (add_cardinal_2 Hd2); rewrite HC1; reflexivity.
   apply subset_add_2; assumption.
   apply subset_add_3; assumption.
  
  exists B'.
  repeat split; trivial; apply subset_refl.
Qed.


(** The following property, proven by induction, is the heart of the
solution, and is due to Tonny Hurkens. *)
Lemma inductive_invariant:∀ m, m≤ n ⇒
                ∃B', B'⊆town ∧ |B'| = m ∧ ∀ b'₀ b'₁, b'₀∈B' ⇒ b'₁∈B' ⇒ ¬(b'₀≡b'₁) ⇒ b'₀ ℛ b'₁.
Proof.
 intros m.
 induction m; intros H_le.
  (* 0 *)
  exists ∅.
  repeat split.
   apply subset_empty.
   intros b'₀ b'₁ H0 H1; apply False_ind. 
   elim (FM.empty_iff b'₀); intros H2 _; apply H2; assumption.
  (* S n *)
  assert (H_le0:=le_Sn_le _ _ H_le).
  destruct (IHm H_le0) as [B' [H3' [H1 H2]]].
  rewrite <- H1 in H_le0.
  destruct (extendible_to_n B' H3' H_le0) as [B [HB1 [HB2 HB3]]].
  destruct (property B HB3 HB1) as [d [Hd1 Hd2]].
  exists ({d}∪ B'); repeat split.
   (* subset of town *)
   apply subset_add_3.
   apply diff_1 with B; assumption.
   apply subset_trans with B; assumption.
   (* cardinality *)
   rewrite <- H1.
   apply add_cardinal_2.
   intro Hd4.
   generalize (in_subset Hd4 HB2).
   apply diff_2 with town; assumption.
(* second big goal *)
   intros b'₀ b'₁ H_b'₀ H_b'₁ H_neq.
   destruct ((proj1 (FM.add_iff B' d b'₀)) H_b'₀) as [H3|H3].
    apply knows_sym; apply knows_extensional with d; trivial.
    destruct ((proj1 (FM.add_iff B' d b'₁)) H_b'₁) as [H4|H4].
     apply False_ind; apply H_neq; rewrite <- H3; assumption.
     apply knows_sym. 
     apply Hd2; apply in_subset with B'; trivial.
    destruct ((proj1 (FM.add_iff B' d b'₁)) H_b'₁) as [H4|H4].
     apply knows_extensional with d; trivial.
     apply knows_sym.
     apply Hd2; apply in_subset with B'; trivial.
     apply H2; assumption.
Qed.

Theorem AMM11262: ∃e,e∈town ∧ ∀ u, u∈town ∧ ¬(u≡e)⇒ e ℛ u.
Proof.
 destruct (inductive_invariant n (le_refl n)) as [B [HB1 [HB2 HB3]]].
 destruct (property B HB1 HB2) as [d [Hd1 Hd2]].
 set (C:=(town\({d}∪B))).
 (* C subset town *)
 assert (H_susbset_C:C⊆town);
 [ subst C; apply subset_diff; apply subset_refl
 | ].
 (* inter town *) 
 assert (H_inter_town: (town∩ ({d}∪B)) ≐ {d} ∪ B).
  rewrite inter_sym; apply inter_subset_equal;
  apply subset_add_3; trivial; apply diff_1 with B; assumption.
 (* ¬ d∈B *)
 assert (H_d_nin_B:¬d∈B); [apply diff_2 with town; assumption|].
 (* |C| = n *)
 assert (H_cardinal_C:|C| =n).
  assert (H_aux:|town∩({d}∪B)|=S n).
   rewrite (@Equal_cardinal (town∩({d}∪B)) ({d}∪B) H_inter_town);
   rewrite (add_cardinal_2 H_d_nin_B); rewrite HB2; reflexivity.
  generalize (diff_inter_cardinal town ({d}∪B));
  fold C; rewrite H_aux; rewrite cardinality; omega.
 
 destruct (property C H_susbset_C H_cardinal_C) as [e [He1 He2]].
 exists e.
 (* ({d}∪B)⊆town *)
 assert (H_dB_town:({d}∪B)⊆town).
  intros a Ha0; destruct ((proj1 (FM.add_iff B d a)) Ha0) as [Had|HaB].  
   rewrite <- Had; apply diff_1 with B; assumption.
   apply HB1; assumption.
 (* town\C = {d}∪B *)
 assert (H_diff: town\C ≐ {d}∪B ).
  unfold C; split; intro H_mem.
   (* ≥ *)
   assert (H_a0:=diff_1 H_mem);
   assert (H_a1:=diff_2 H_mem);
   destruct (In_dec a ({d}∪B)) as [H_a2|H_a2]; trivial;
   apply False_ind; apply H_a1; exact (diff_3 H_a0 H_a2).
   (* ≤ *)
   destruct (In_dec a (town\({d}∪B))) as [H_a2|H_a2].
    apply False_ind; exact (diff_2 H_a2 H_mem). 
    apply diff_3; trivial; apply H_dB_town; assumption.
 (* e∈({d}∪B) *)
 assert (H_e_dB:e∈({d}∪B)); [rewrite <- H_diff; assumption|].

 split.
  apply diff_1 with C; assumption...
  intros u [Hu Hu'].
  assert (H_town_part:town ≐ (C∪({d}∪B))).
   rewrite <- (diff_inter_all town ({d}∪B)); rewrite H_inter_town; apply equal_refl.
   rewrite H_town_part in Hu.
   destruct (union_1 Hu) as [HuC|HudB].
    (* u∈C *)
    apply He2; assumption. 
    (* u∈({d}∪B) *)
    destruct ((proj1 (FM.add_iff B d u)) HudB) as [Hud|HuB].
     (* d=u *)
     apply knows_extensional with d; trivial.
     apply knows_sym.
     destruct ((proj1 (FM.add_iff B d e)) H_e_dB) as [Hed|HeB].
      (* d=e *)
      apply False_ind; apply Hu'; rewrite <- Hud; assumption.
      (* e∈B *)
      apply Hd2; assumption.
     (* u∈B *)
     destruct ((proj1 (FM.add_iff B d e)) H_e_dB) as [Hed|HeB].
      (* d=e *) 
      apply knows_sym; apply knows_extensional with d; trivial;
      apply knows_sym; apply Hd2; assumption.
      (* e∈B *)
      apply HB3; assumption || contradict Hu'; auto with *.
Qed.

End problem_knows_not_refl.

Extraction "amm11262" AMM11262.
