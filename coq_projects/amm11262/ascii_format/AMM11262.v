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
Module NatSet := FSetList.Make(OrderedTypeEx.Nat_as_OT).
Import NatSet.

Infix "++" := add (at level 60, right associativity).
Notation "s [=] t" := (Equal s t) (at level 70, no associativity).

Require FSetFacts FSetProperties.
Require Extraction.

Module GeneralProperties := FSetProperties.Properties NatSet.
Import GeneralProperties.

Section problem_knows_not_refl.

Variable town: t.
Variable n:nat.
Variable cardinality: cardinal town = 2*n+1.

Variable knows: elt -> elt -> Prop. 

Variable knows_sym: forall m n, knows m n ->  knows n m.
Variable knows_extensional:forall m n p, E.eq n p -> knows m n-> knows m p.

Variable property: forall B, Subset B town -> cardinal B = n -> 
           {d:elt | In d (diff town B)/\(forall b, In b B -> knows d b)}.

Lemma extendible_by_one:forall B', cardinal B' <= (cardinal town)-1 -> {d:elt| In d town /\ ~(In d B')}.
Proof.
 clear knows knows_sym knows_extensional property.
 intros B' H_cardinal_town.
 assert (H_town:1<=(cardinal town)); [omega|].
 rewrite <- (diff_inter_cardinal town B') in H_cardinal_town.
 rewrite <- (diff_inter_cardinal town B') in H_town.
 assert (H_inter:cardinal (inter town B') <= cardinal B');
  [apply (subset_cardinal);apply (inter_subset_2)|].
 generalize (le_trans _ _ _ H_inter H_cardinal_town); intro H1.
 assert (H2:1<=cardinal (diff town B')); [omega|].
 assert (H3:=(S_pred _ _ H2)).
 destruct (cardinal_inv_2 H3) as [d Hd].
 exists d; split.
  apply diff_1 with B'; assumption.
  apply diff_2 with town; assumption.
Qed.  

Lemma extendible_to_n:forall B', Subset B' town -> cardinal B' <= n -> 
     {B:t| cardinal B = n /\  Subset B' B /\ Subset B town}.  
Proof.
 intros B' H_sub H_B'_cardinal.
 assert (H_cardinal_aux_3:2*n<=(cardinal town)-1);[apply le_trans with (2*n); omega|].
 clear property.
 induction n in H_B'_cardinal, H_cardinal_aux_3 |- *.
 (* n = 0 *)
 generalize (sym_eq (le_n_O_eq _ H_B'_cardinal)); intro H_eq.
 generalize (empty_is_empty_1 (cardinal_inv_1 H_eq)).
 intro H_B'.
 exists empty; repeat split. 
  rewrite H_B'; apply subset_empty.
  apply subset_empty.
 (* n = S n0 *)
 destruct (le_lt_eq_dec _ _ H_B'_cardinal) as [H_lt|H_le].
  generalize (lt_n_Sm_le _ _ H_lt); clear H_lt; intro H_le.
  assert (H_cardinal_town_2:2 * n0 <= cardinal town - 1);[omega|].
  destruct (IHn0 H_le H_cardinal_town_2) as [C [HC1 [HC2 HC3]]].
  assert (HC5:cardinal C <= cardinal town - 1).
   rewrite HC1; apply le_trans with (2*(S n0));[omega| assumption].
  destruct (extendible_by_one C HC5) as [d [Hd1 Hd2]].
  exists (d ++ C).
  repeat split.
   rewrite (add_cardinal_2 Hd2); rewrite HC1; reflexivity.
   apply subset_add_2; assumption.
   apply subset_add_3; assumption.
  
  exists B'.
  repeat split; trivial; apply subset_refl.
Qed.


(** The following property, proven by induction, is the heart of the
solution, and is due to Tonny Hurkens. *)
Lemma inductive_invariant:forall m, m<= n ->
   {B':t| Subset B' town /\ cardinal B' = m /\ forall b'0 b'1, In b'0 B' -> In b'1 B' -> ~(E.eq b'0 b'1) -> knows b'0 b'1}.
Proof.
 intros m.
 induction m; intros H_le.
  (* 0 *)
  exists empty.
  repeat split.
   apply subset_empty.
   intros b'0 b'1 H0 H1; apply False_ind. 
   elim (FM.empty_iff b'0); intros H2 _; apply H2; assumption.
  (* S n *)
  assert (H_le0:=le_Sn_le _ _ H_le).
  destruct (IHm H_le0) as [B' [H3' [H1 H2]]].
  rewrite <- H1 in H_le0.
  destruct (extendible_to_n B' H3' H_le0) as [B [HB1 [HB2 HB3]]].
  destruct (property B HB3 HB1) as [d [Hd1 Hd2]].
  exists (add d B'); repeat split.
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
   intros b'0 b'1 H_b'0 H_b'1 H_neq.
   destruct ((proj1 (FM.add_iff B' d b'0)) H_b'0) as [H3|H3].
    apply knows_sym; apply knows_extensional with d; trivial.
    destruct ((proj1 (FM.add_iff B' d b'1)) H_b'1) as [H4|H4].
     apply False_ind; apply H_neq; rewrite <- H3; assumption.
     apply knows_sym. 
     apply Hd2; apply in_subset with B'; trivial.
    destruct ((proj1 (FM.add_iff B' d b'1)) H_b'1) as [H4|H4].
     apply knows_extensional with d; trivial.
     apply knows_sym.
     apply Hd2; apply in_subset with B'; trivial.
     apply H2; assumption.
Qed.

Theorem AMM11262: {e:elt | In e town /\ forall u, In u town /\ ~(E.eq u e)-> knows e u}.
Proof.
 destruct (inductive_invariant n (le_refl n)) as [B [HB1 [HB2 HB3]]].
 destruct (property B HB1 HB2) as [d [Hd1 Hd2]].
 set (C:=(diff town (d ++ B))).
 (* C subset town *)
 assert (H_susbset_C:Subset C town);
 [ subst C; apply subset_diff; apply subset_refl
 | ].
 (* inter town *) 
 assert (H_inter_town: inter town (d ++ B)[=]d ++ B).
  rewrite inter_sym; apply inter_subset_equal;
  apply subset_add_3; trivial; apply diff_1 with B; assumption.
 (* ~ In d B *)
 assert (H_d_nin_B:~In d B); [apply diff_2 with town; assumption|].
 (* cardinal C = n *)
 assert (H_cardinal_C:cardinal C=n).
  assert (H_aux:cardinal (inter town (d ++ B))=S n).
   rewrite (@Equal_cardinal (inter town (d ++ B)) (d++B) H_inter_town);
   rewrite (add_cardinal_2 H_d_nin_B); rewrite HB2; reflexivity.
  generalize (diff_inter_cardinal town (d++B));
  fold C; rewrite H_aux; rewrite cardinality; omega.
 
 destruct (property C H_susbset_C H_cardinal_C) as [e [He1 He2]].
 exists e.
 (* Subset (d++B) town *)
 assert (H_dB_town:Subset (d++B) town).
  intros a Ha0; destruct ((proj1 (FM.add_iff B d a)) Ha0) as [Had|HaB].  
   rewrite <- Had; apply diff_1 with B; assumption.
   apply HB1; assumption.
 (* diff town C = d++B *)
 assert (H_diff:diff town C [=] d++B ).
  unfold C; split; intro H_mem.
   (* => *)
   assert (H_a0:=diff_1 H_mem);
   assert (H_a1:=diff_2 H_mem);
   destruct (In_dec a (d++B)) as [H_a2|H_a2]; trivial;
   apply False_ind; apply H_a1; exact (diff_3 H_a0 H_a2).
   (* <= *)
   destruct (In_dec a (diff town (d++B))) as [H_a2|H_a2].
    apply False_ind; exact (diff_2 H_a2 H_mem). 
    apply diff_3; trivial; apply H_dB_town; assumption.
 (* In e (d++B) *)
 assert (H_e_dB:In e (d++B)); [rewrite <- H_diff; assumption|].

 split.
  apply diff_1 with C; assumption...
  intros u [Hu Hu'].
  assert (H_town_part:town [=] (union C (d++B))).
   rewrite <- (diff_inter_all town (d++B)); rewrite H_inter_town; apply equal_refl.
   rewrite H_town_part in Hu.
   destruct (union_1 Hu) as [HuC|HudB].
    (* In u C *)
    apply He2; assumption. 
    (* In u (d++B) *)
    destruct ((proj1 (FM.add_iff B d u)) HudB) as [Hud|HuB].
     (* d=u *)
     apply knows_extensional with d; trivial.
     apply knows_sym.
     destruct ((proj1 (FM.add_iff B d e)) H_e_dB) as [Hed|HeB].
      (* d=e *)
      apply False_ind; apply Hu'; rewrite <- Hud; assumption.
      (* In e B *)
      apply Hd2; assumption.
     (* In u B *)
     destruct ((proj1 (FM.add_iff B d e)) H_e_dB) as [Hed|HeB].
      (* d=e *) 
      apply knows_sym; apply knows_extensional with d; trivial;
      apply knows_sym; apply Hd2; assumption.
      (* In e B *)
      apply HB3; assumption || contradict Hu'; auto with *.
Qed.

End problem_knows_not_refl.

Extraction "amm11262" AMM11262.
