(************************************************************************)
(* Copyright 2006 Milad Niqui                                           *)
(* This file is distributed under the terms of the                      *)
(* GNU Lesser General Public License Version 2.1                        *)
(* A copy of the license can be found at                                *)
(*                  <http://www.gnu.org/licenses/lgpl-2.1.html>         *)
(************************************************************************)


Require Export Qsyntax.
Require Export Field_Theory_Q.
Require Export Q_ordered_field_properties.


Lemma Qpositive_in_Q_Archimedean_inf:forall qp:Qpositive, {z:Z | (Qpos qp)<=z /\ (z-(Qpos qp))<= Qone}.
Proof.
 induction qp as [qp [z [Hz1 Hz2]]|qp [z [Hz1 Hz2]]|]; simpl.
  exists (z+1)%Z; split;rewrite Qpos_nR; rewrite Z_to_Qplus; qZ_numerals.
   apply Qle_plus_plus; trivial.
   stepl (z-Qpos qp); [assumption|ring].

  exists (1)%Z; split; rewrite Qpos_dL; fold (Qdiv (Qpos qp) (Qpos qp + Qone)); qZ_numerals.
   apply Qmult_pos_Qdiv_Qle; auto; stepr (Qpos qp+Qone); [|ring]; apply Qle_Zero_Qminus; stepr Qone; [auto|ring].
   stepl (Qone/(Qpos qp + Qone)); [|field; auto];
    apply Qmult_pos_Qdiv_Qle; auto;  stepr (Qpos qp+Qone); [|ring]; apply Qle_Zero_Qminus;  stepr (Qpos qp); [auto|ring].
   
 exists (1)%Z; split; auto.
Qed.


Theorem Q_Archimedean_inf:forall q:Q, {z:Z | q<=z /\ (z-q)<= Qone}.
Proof.
 intros [|qp|qp].  
 (* 0 *)
 exists (0)%Z; split; auto.
 (* Qpos *)
 destruct (Qpositive_in_Q_Archimedean_inf qp) as [z Hz]; exists z; assumption.
 (* Qneg *)  
 destruct (Qpositive_in_Q_Archimedean_inf qp) as [z [Hz1 Hz2]]; exists (-(z-1))%Z; rewrite Z_to_Qopp;
           rewrite (Z_to_Qminus); qZ_numerals; split; apply Qle_opp; apply Qle_Zero_Qminus; rewrite Qopp_Qpos.
  stepr (Qone-(z - Qpos qp)); [|ring]; apply Qle_Qminus_Zero; assumption.
  stepr (z-(Qpos qp));[|ring]; apply Qle_Qminus_Zero; assumption.
Qed.

Definition up_Q q:= proj1_sig (Q_Archimedean_inf q).

Definition up_Q_property q := proj2_sig (Q_Archimedean_inf q):  q <= (up_Q q) /\ (up_Q q) - q <= Qone.

Lemma Q_Archimedean_nat_inf:forall q:Q, {n:nat | q<=n }.
Proof.
 intro q.
 destruct (Q_le_lt_dec q Zero).
  exists O; qnat_zero.
  exists (Z.abs_nat (up_Q q)).
  destruct (up_Q_property q) as [H1 H2].  
  stepr (up_Q q); trivial.
   assert (H3:(0<=(up_Q q))%Z).
    assert (H4:Zero<Z_to_Q (up_Q q));[apply Qlt_le_trans with q; auto|];
    generalize (Q_to_Z_monotone _ _ H4); simpl; rewrite Q_to_Z_to_Q; trivial.
   rewrite (Z_of_nat_Zabs_nat_pos _ H3); reflexivity.
Qed.
