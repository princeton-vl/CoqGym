(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import List Permutation Arith Omega.

Require Import utils pos vec. 
Require Import subcode sss mm_defs.
Require Import ill eill.

Set Implicit Arguments.

Local Infix "~p" := (@Permutation _) (at level 70).

(** ** MM reduces to eILL *)

Section Minsky.

  (* We consider Minsky machines with n registers *)

  Variable (n : nat).

  (** register p (0<=p<n) is encoded by p
      its dual            is encoded by n+p

     positions in the program (PC) are encoded from 2*n until (potential) infinity

   **)
   
  Let q (i : nat) : ll_vars := 2*n+i. 
  Let rx (p : pos n) := pos2nat p.
  Let ry (p : pos n) := n+pos2nat p. 

  Let H_rx : forall p q, rx p = rx q -> p = q.
  Proof.
    intros p1 p2; unfold rx; intros.
    apply pos2nat_inj; omega.
  Qed.

  (* This encodes a list of instructions starting at PC=i 

     i:INC x    ~~~>  ((rx x) -o q(1+i)) -o (q i)
     i:DEC x p  ~~~>  (ry x & q p) -o q i and (rx x) -o q(1+i) -o (q i) 

   *)
  
  Local Fixpoint mm_linstr_enc i l :=
    match l with
      | nil          => nil
      | INC x   :: l => LL_INC  (rx x) (q (1+i)) (q i)                                  :: mm_linstr_enc (1+i) l
      | DEC x p :: l => LL_FORK (ry x) (q p)     (q i) :: LL_DEC (rx x) (q (1+i)) (q i) :: mm_linstr_enc (1+i) l
    end.
    
  Local Fact mm_linstr_enc_app i l m : mm_linstr_enc i (l++m) = mm_linstr_enc i l ++ mm_linstr_enc (length l+i) m.
  Proof.
    revert i; induction l as [ | [ x | x p ] l IHl ]; intros i; simpl; f_equal; auto.
    rewrite IHl; do 2 f_equal; omega.
    f_equal; rewrite IHl; do 2 f_equal; omega.
  Qed.
    
  Local Fact subcode_mm_linstr_enc i x j l : (i,INC x::nil) <sc (j,l) -> In (LL_INC  (rx x) (q (1+i)) (q i)) (mm_linstr_enc j l).
  Proof.
    intros (l1 & l2 & H1 & H2); subst.
    rewrite mm_linstr_enc_app.
    apply in_or_app; right; left; do 2 f_equal; omega.
  Qed.
  
  Local Fact subcode_mm_linstr_dec i x p j l : (i,DEC x p::nil) <sc (j,l) -> incl (LL_FORK (ry x) (q p) (q i) :: LL_DEC (rx x) (q (1+i)) (q i) :: nil) (mm_linstr_enc j l).
  Proof.
    intros (l1 & l2 & H1 & H2); subst.
    rewrite mm_linstr_enc_app.
    intros A HA; apply in_or_app; right.
    destruct HA as [ HA | [ HA | [] ] ]; subst.
    left; do 2 f_equal; omega.
    right; left; do 2 f_equal; omega.
  Qed.
    
  Local Fact mm_linstr_enc_spec i ll A : In A (mm_linstr_enc i ll) -> (exists j x,   (j,INC x::nil)   <sc (i,ll)  /\   A = LL_INC  (rx x) (q (1+j)) (q j))
                                                                   \/ (exists j x p, (j,DEC x p::nil) <sc (i,ll)  /\ ( A = LL_FORK (ry x) (q p)     (q j)
                                                                                                                  \/ A = LL_DEC  (rx x) (q (1+j)) (q j) ) ). 
  Proof.
    revert i A; induction ll as [ | [ x | x p ] ll IHll ]; intros i A HA.
    destruct HA.
    destruct HA as [ HA | HA ].
    left; exists i, x; split; auto.
    apply IHll in HA.
    destruct HA as [ (j & x' & H1 & H2) | (j & x' & p & H1 & H2) ].
    left; exists j, x'; split; auto.
    apply subcode_trans with (1 := H1); subcode_tac; solve list eq.
    right; exists j, x', p; split; auto.
    apply subcode_trans with (1 := H1); subcode_tac; solve list eq.
    destruct HA as [ HA | HA ].
    right; exists i, x, p; split; auto.
    destruct HA as [ HA | HA ].
    right; exists i, x, p; split; auto.
    apply IHll in HA.
    destruct HA as [ (j & x' & H1 & H2) | (j & x' & p' & H1 & H2) ].
    left; exists j, x'; split; auto.
    apply subcode_trans with (1 := H1); subcode_tac; solve list eq.
    right; exists j, x', p'; split; auto.
    apply subcode_trans with (1 := H1); subcode_tac; solve list eq.
  Qed.

  (* k is a position outside the program were execution has to stop *)
   
  Variable (P : nat*(list (mm_instr n))) (k : nat) (Hk : out_code k P).

  (* This encodes P into EILL commands 
  
     (q k)  terminates on an zero vector
     (ry j) terminates on a vector vec there is no (rx j)
     
  *)
                  
  Definition Sig0 := LL_INC (q k) (q k) (q k)
                  :: map (fun c => LL_DEC (rx (fst c)) (ry (snd c)) (ry (snd c))) (pos_not_diag n)
                  ++ map (fun j => LL_INC (ry j) (ry j) (ry j)) (pos_list n).

  Definition SigI := match P with (i,l) => mm_linstr_enc i l end.

  Definition Sig := Sig0 ++ SigI.

  Notation "P // s -[ k ]-> t" := (sss_steps (@mm_sss _) P k s t).
  Notation "P // s ->> t" := (sss_compute (@mm_sss _) P s t).

  (* We define the semantics as in the paper ToCL 2013 (DLW & Galmiche) *)

  Local Definition s (x : ll_vars) (v : vec nat n) : Prop.
  Proof.
    refine (match le_lt_dec n x with
                 | left H1  => match le_lt_dec (2*n) x with
                     | left _   => P // (x-2*n,v) ->> (k,vec_zero)
                     | right H2 => vec_pos v (@nat2pos n (x-n) _) = 0
                   end
                 | right H1 => v = vec_one (@nat2pos n x H1)
               end); omega.
  Defined.

  (* We check the required properties *)

  Let H_s_q : forall i v, s (q i) v <-> P // (i,v) ->> (k,vec_zero).
  Proof.
    intros i v; unfold q, s.
    destruct (le_lt_dec n (2*n+i)); [ | omega ].
    destruct (le_lt_dec (2*n) (2*n+i)); [ | omega ].
    replace (2*n+i-2*n) with i by omega; tauto.
  Qed.

  Let H_s_rx : forall p v, s (rx p) v <-> v = vec_one p.
  Proof.
    intros p v; unfold s, rx.
    destruct (le_lt_dec n (pos2nat p)).
    generalize (pos2nat_prop p); omega.
    rewrite nat2pos_pos2nat; tauto.
  Qed.
 
  Let H_s_ry : forall p v, s (ry p) v <-> vec_pos v p = 0.
  Proof.
    intros p v; unfold s, ry.
    destruct (le_lt_dec n (n+pos2nat p)); [ | omega ].
    destruct (le_lt_dec (2*n) (n+pos2nat p)).
    generalize (pos2nat_prop p); omega.
    match goal with |- vec_pos _ (nat2pos ?H) = _ <-> _ => cutrewrite (nat2pos H = p) end.
    tauto.
    apply pos2nat_inj; rewrite pos2nat_nat2pos; omega.
  Qed.

  (* No need of the code of s anymore *)

  Opaque s.

  (* This is a notation for the trivial phase semantics *)
 
  Notation "'[[' A ']]'" := (ll_tps s A) (at level 65).

  (* i -o (_j_ -o _j_) *)
  
  Let sem_x_y_y i j : i <> j -> [[ [i LL_DEC (rx i) (ry j) (ry j) ] ]] vec_zero.
  Proof.
    intros Hij.
    simpl; unfold ll_tps_imp.
    intros v Hv.
    rewrite H_s_rx in Hv.
    intros w Hw.
    rewrite H_s_ry in Hw.
    rewrite H_s_ry.
    rewrite (vec_plus_comm v), vec_zero_plus.
    unfold vec_plus; rewrite vec_pos_set.
    subst; rewrite Hw, vec_one_spec_neq; auto.
  Qed.
  
  Let sem_y_y_y j : [[ [i LL_INC (ry j) (ry j) (ry j) ] ]] vec_zero.
  Proof.
    simpl; unfold ll_tps_imp.
    intros x Hx; rew vec.
    generalize (Hx vec_zero); rew vec.
    intros H; apply H, H_s_ry; rew vec.
  Qed.
 
  (* We need out_code k P here *)
  
  Let sem_k v : [[£ (q k)]] v <-> v = vec_zero.
  Proof.
    simpl; rewrite H_s_q.
    split.
    2: intros; subst; exists 0; constructor. 
    intros H.
    apply sss_compute_stop in H; auto.
    inversion H; auto.
  Qed.
  
  Let sem_k_k_k : [[ [i LL_INC (q k) (q k) (q k) ] ]] vec_zero.
  Proof.
    simpl; unfold ll_tps_imp.
    intros x Hx; rew vec.
    generalize (Hx vec_zero); rew vec.
    intros H; apply H, sem_k; auto.
  Qed.

  Let Sig0_zero A : In A Sig0 -> [[ [iA] ]] vec_zero.
  Proof.
    unfold Sig0.
    intros [ H | H ]; subst. 
    
    apply sem_k_k_k.
    
    apply in_app_or in H.
    destruct H as [ H | H ]; 
    apply in_map_iff in H.
    
    destruct H as ((i & j) & H1 & H2); subst.
    apply sem_x_y_y; simpl.
    apply pos_not_diag_spec in H2; auto.
    
    destruct H as (y & H1 & _); subst.
    apply sem_y_y_y.
  Qed.
  
  Let SigI_zero A : In A SigI -> [[ [iA] ]] vec_zero.
  Proof.
    unfold SigI.
    destruct P as (i & lP).
    intros H.
    apply mm_linstr_enc_spec in H.
    destruct H as [ (j & x & H1 & H2) | (j & x & p & H1 & [ H2 | H2 ]) ]; subst A.
    
    simpl; unfold ll_tps_imp.
    intros v Hv.
    rewrite vec_plus_comm, vec_zero_plus.
    apply H_s_q.
    apply mm_compute_INC with (1 := H1).
    specialize (Hv (vec_one x)).
    replace (vec_change v x (S (vec_pos v x))) with (vec_plus (vec_one x) v).
    apply H_s_q.
    apply Hv.
    apply H_s_rx; split.
    apply vec_pos_ext.
    intros p; rewrite vec_pos_plus.
    destruct (pos_eq_dec x p).
    subst; rewrite vec_one_spec_eq, vec_change_eq; auto.
    rewrite vec_one_spec_neq, vec_change_neq; auto.
    
    simpl; unfold ll_tps_imp.
    intros v (Hv1 & Hv2).
    rewrite vec_plus_comm, vec_zero_plus.
    apply H_s_q.
    rewrite H_s_ry in Hv1.
    apply mm_compute_DEC_0 with (1 := H1); auto.
    apply H_s_q; auto.
    
    simpl; unfold ll_tps_imp.
    intros v Hv w Hw.
    rewrite (vec_plus_comm v), vec_zero_plus.
    apply H_s_q.
    apply H_s_rx in Hv.
    rewrite vec_plus_comm.
    assert (exists u, vec_pos (vec_plus v w) x = S u) as Hu.
      exists (vec_pos w x).
      rewrite vec_pos_plus; subst.
      rewrite vec_one_spec_eq; auto.
    destruct Hu as (u & Hu).
    apply mm_compute_DEC_S with (1 := H1) (u := vec_pos w x); auto.
    rewrite vec_pos_plus; subst.
    rewrite vec_one_spec_eq; auto.
    apply H_s_q.
    eq goal Hw; f_equal.
    apply vec_pos_ext.
    intros r.
    destruct (pos_eq_dec x r).
    subst; rewrite vec_change_eq; auto.
    rewrite vec_change_neq, vec_pos_plus; auto.
    subst; rewrite vec_one_spec_neq; auto.
  Qed.
 
  Lemma Sig_zero A : In A Sig -> [[ [i A] ]] vec_zero.
  Proof.
    intros H; apply in_app_or in H; destruct H.
    apply Sig0_zero; auto.
    apply SigI_zero; auto.
  Qed.
  
  Corollary ll_tps_Sig_zero : ll_tps_list s (map (fun c => ❗[i c]) Sig) vec_zero.
  Proof.
    generalize Sig Sig_zero; intros S.
    induction S as [ | A S IHS ]; intros HS.
    simpl; auto.
    simpl; exists vec_zero, vec_zero; repeat split; auto.
    rew vec.
    apply HS; left; auto.
    apply IHS; intros; apply HS; right; auto.
  Qed.
 
  Theorem lemma_5_5 v i : Sig; vec_map_list v rx ⊦ q i -> P // (i,v) ->> (k,vec_zero).
  Proof.
    intros H.
    apply G_eill_sound in H.
    apply ll_tps_sound with (s := s) in H.
    red in H.
    specialize (H v).
    rewrite vec_plus_comm, vec_zero_plus in H.
    apply H_s_q; auto.
    apply H.
    rewrite ll_tps_app.
    exists vec_zero, v; repeat split.
    rew vec.
    apply ll_tps_Sig_zero.
    apply ll_tps_vec_map_list; auto.
  Qed.
  
  Let prop_5_2_rec (p : pos n) v Ga : 
         vec_pos v p = 0 
      -> Sig0;                      Ga ⊦ ry p 
      -> Sig0; vec_map_list v rx ++ Ga ⊦ ry p.
  Proof.
    revert Ga.
    induction v as [ | r | v w Hv Hw ] using (@vec_nat_induction _); intros Ga.

    intros _.
    rewrite vec_map_list_zero.
    auto.
    
    destruct (pos_eq_dec r p) as [ H | H ]; rew vec.
    omega.
    intros _ H1.
    rewrite vec_map_list_one.
    apply in_eill_dec with (rx r) (ry p); auto.
    right; apply in_or_app; left.
    apply in_map_iff.
    exists (r,p); simpl; split; auto.
    apply pos_not_diag_spec; auto.
    apply in_eill_ax.
    
    intros H1 H2.
    rewrite vec_pos_plus in H1.
    apply in_eill_perm with (vec_map_list v rx ++ vec_map_list w rx ++ Ga).
    rewrite vec_map_list_plus, app_ass; auto.
    apply Hv.
    omega.
    apply Hw; auto; omega.
  Qed.
  
  Lemma prop_5_2 p v : 
           vec_pos v p = 0 
        -> Sig; vec_map_list v rx ⊦ ry p.
  Proof.
    rewrite (app_nil_end (_ _ rx)).
    intros H.
    apply g_eill_mono_Si with Sig0.
    unfold Sig; intros ? ?; apply in_or_app; left; auto.
    apply prop_5_2_rec; auto.
    apply in_eill_inc with (ry p) (ry p).
    right; apply in_or_app; right.
    apply in_map_iff.
    exists p; split; auto.
    apply pos_list_prop.
    apply in_eill_ax.
  Qed.
  
  Lemma lemma_5_3 i v : P // (i,v) ->> (k,vec_zero) -> Sig; vec_map_list v rx ⊦ q i.
  Proof.
    intros (r & Hr); revert i v Hr.
    induction r as [ | r IHr ]; intros i v Hr.
    
    apply sss_steps_0_inv in Hr.
    inversion Hr; subst i v; clear Hr.
    rewrite vec_map_list_zero.
    apply in_eill_inc with (q k) (q k).
    left; auto.
    apply in_eill_ax.
    
    apply sss_steps_S_inv' in Hr.
    destruct Hr as ((j,w) & H1 & H2).
    apply IHr in H2.
    generalize (sss_step_in_code H1); simpl fst; intros H3.
    apply in_code_subcode in H3.
    destruct H3 as (ii & Hii).
    apply sss_step_subcode_inv with (1 := Hii) in H1.
    destruct ii as [ p | p l ].
    
    apply mm_sss_INC_inv in H1.
    destruct H1; subst.
    apply in_eill_inc with (rx p) (q (1+i)).
    apply in_or_app; right.
    unfold SigI; destruct P as (ip,lP).
    apply subcode_mm_linstr_enc; auto.
    revert H2; apply in_eill_perm.
    rewrite vec_change_succ, vec_map_list_plus, vec_map_list_one; auto.
    
    case_eq (vec_pos v p).
    
    intros Hv.
    apply mm_sss_DEC0_inv in H1; auto.
    destruct H1; subst l w.
    apply in_eill_fork with (ry p) (q j); auto.
    apply in_or_app; right.
    unfold SigI; destruct P as (ip,lP).
    apply subcode_mm_linstr_dec with (1 := Hii); auto.
    left; auto.
    apply prop_5_2; auto.
    
    intros u Hu.
    apply mm_sss_DEC1_inv with (u := u) in H1; auto.
    destruct H1; subst j w.
    rewrite vec_change_pred with (1 := Hu).
    apply in_eill_perm with (1 := Permutation_sym (vec_map_list_plus _ _ _)).
    rewrite vec_map_list_one.
    apply in_eill_dec with (rx p) (q (1+i)); auto.
    apply in_or_app; right.
    unfold SigI; destruct P as (ip,lP).
    apply subcode_mm_linstr_dec with (1 := Hii); auto.
    right; left; auto.
    apply in_eill_ax.
  Qed.
   
  Theorem G_eill_mm i v : P // (i,v) ->> (k,vec_zero) 
                      <-> Sig; vec_map_list v rx ⊦ q i.
  Proof.
    split.
    apply lemma_5_3.
    apply lemma_5_5; auto.
  Qed.
  
End Minsky.

