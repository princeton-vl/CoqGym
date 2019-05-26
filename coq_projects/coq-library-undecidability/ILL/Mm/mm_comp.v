(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import List Arith Omega.

Require Import utils pos vec.
Require Import subcode sss compiler_correction.
Require Import list_bool.
Require Import bsm_defs.
Require Import mm_defs mm_utils.

Set Implicit Arguments.

(** ** BSM recues to MM *)

Tactic Notation "rew" "length" := autorewrite with length_db.

Local Notation "e #> x" := (vec_pos e x).
Local Notation "e [ v / x ]" := (vec_change e x v).

Local Notation "I '/BSM/' s -1> t" := (bsm_sss I s t) (at level 70, no associativity).
Local Notation "P '/BSM/' s -+> t" := (sss_progress (@bsm_sss _) P s t) (at level 70, no associativity).
Local Notation "P '/BSM/' s ->> t" := (sss_compute (@bsm_sss _) P s t) (at level 70, no associativity).
Local Notation "P '/BSM/' s ~~> t" := (sss_output (@bsm_sss _) P s t) (at level 70, no associativity).
Local Notation "P '/BSM/' s ↓" := (sss_terminates (@bsm_sss _) P s)(at level 70, no associativity).

Local Notation "P '/MM/' s -+> t" := (sss_progress (@mm_sss _) P s t) (at level 70, no associativity).
Local Notation "P '/MM/' s ->> t" := (sss_compute (@mm_sss _) P s t) (at level 70, no associativity).
Local Notation "P '/MM/' s '~~>' t" := (sss_output (@mm_sss _) P s t) (at level 70, no associativity).
Local Notation "P '/MM/' s ↓" := (sss_terminates (@mm_sss _) P s)(at level 70, no associativity).

Section simulator.

  Ltac dest x y := destruct (pos_eq_dec x y) as [ | ]; [ subst x | ]; rew vec.

  Variables (m : nat).
  
  (** each stack of the BSM corresponds to a (unique) register in the MM 
      and there are extra registers: tmp1, tmp2 which must have value 0 at start 
      they might change value during a simulated BSM instruction but when
      the instruction is finished, their values are back to 0 

      This is expressed in the below bsm_state_enc invariant
  *)
  
  Let n := 2+m.
  Let tmp1 : pos n := pos0.
  Let tmp2 : pos n := pos1.
  Let reg p: pos n := pos_nxt (pos_nxt p).
   
  Let Hv12 : tmp1 <> tmp2.             Proof. discriminate. Qed.
  Let Hvr1 : forall p, reg p <> tmp1.  Proof. discriminate. Qed.
  Let Hvr2 : forall p, reg p <> tmp2.  Proof. discriminate. Qed.
  
  Let Hreg : forall p q, reg p = reg q -> p = q.
  Proof. intros; do 2 apply pos_nxt_inj; apply H. Qed. 

  Definition bsm_state_enc (v : vec (list bool) m) w := 
            w#>tmp1 = 0
         /\ w#>tmp2 = 0
         /\ forall p, w#>(reg p) = stack_enc (v#>p).

  (* i is the position in the source code *)

  Definition bsm_instr_compile lnk i ii :=
    match ii with
      | PUSH s Zero => mm_push_Zero (reg s) tmp1 tmp2 (lnk i)
      | PUSH s One  => mm_push_One  (reg s) tmp1 tmp2 (lnk i)
      | POP  s j k  => mm_pop (reg s) tmp1 tmp2 (lnk i) (lnk j) (lnk (1+i)) (lnk k)
    end.

  Definition bsm_instr_compile_length (ii : bsm_instr m) :=
    match ii with 
      | PUSH _ Zero => 7
      | PUSH _ One  => 8
      | POP  _ _ _  => 16
    end.

  Fact bsm_instr_compile_length_eq lnk i ii : length (bsm_instr_compile lnk i ii) = bsm_instr_compile_length ii.
  Proof. destruct ii as [ | ? [] ]; simpl; auto. Qed.
    
  Fact bsm_instr_compile_length_geq ii : 1 <= bsm_instr_compile_length ii.
  Proof. destruct ii as [ | ? [] ]; simpl; auto; omega. Qed.

  Hint Resolve bsm_instr_compile_length_eq bsm_instr_compile_length_geq.

  (* This main soundness lemma per simulated instruction *)

  Lemma bsm_instr_compile_sound : instruction_compiler_sound bsm_instr_compile (@bsm_sss _) (@mm_sss _) bsm_state_enc.
  Proof.
    intros lnk I i1 v1 i2 v2 w1 H; revert H w1.
    change v1 with (snd (i1,v1)) at 2.
    change i1 with (fst (i1,v1)) at 2 3 4 6 7 8.
    change v2 with (snd (i2,v2)) at 2.
    change i2 with (fst (i2,v2)) at 2.
    generalize (i1,v1) (i2,v2); clear i1 v1 i2 v2.
    induction 1 as    [ i p j k v Hv
                      | i p j k v ll Hll 
                      | i p j k v ll Hll
                      | i p [] v
                      ]; simpl; intros w1 H0 H; generalize H; intros (H1 & H2 & H3).

    + exists w1; split; auto.
      apply mm_pop_void_progress; auto.
      rewrite H3, Hv; auto.

    + exists (w1[(stack_enc ll)/reg p]); repeat split; auto; rew vec.
      * apply mm_pop_Zero_progress; auto.
        rewrite H3, Hll; auto.
      * intros q; dest p q.
        assert (reg p <> reg q); rew vec.
    
    + exists (w1[(stack_enc ll)/reg p]); repeat split; auto; rew vec.
      * apply mm_pop_One_progress; auto.
        rewrite H3, Hll; auto.
      * intros q; dest p q.
        assert (reg p <> reg q); rew vec.
   
    + exists (w1[(stack_enc (One::v#>p))/reg p]); repeat split; auto; rew vec.
      rewrite H0; apply mm_push_One_progress; auto.
      intros q; dest p q.
      assert (reg p <> reg q); rew vec.

    + exists (w1[(stack_enc (Zero::v#>p))/reg p]); repeat split; auto; rew vec.
      rewrite H0; apply mm_push_Zero_progress; auto.
      intros q; dest p q.
      assert (reg p <> reg q); rew vec.
  Qed.

  Hint Resolve bsm_instr_compile_sound.

  Section bsm_sim.

    Variable (iP : nat) (cP : list (bsm_instr m)).

    Let lnk_Q_pair := @gen_compiler_correction _ _ _ _ bsm_instr_compile_length_eq _ _ _ _  (@bsm_sss_total' _)
                     (@mm_sss_fun _) _ bsm_instr_compile_sound (iP,cP) 1. 

    Let lnk := projT1 lnk_Q_pair.
    Let Q := proj1_sig (projT2 lnk_Q_pair).

    Let Hlnk : fst Q = 1 /\ lnk iP = 1 /\ forall i, out_code i (iP,cP) -> lnk i = code_end Q.
    Proof.
      repeat split; apply (proj2_sig (projT2 lnk_Q_pair)).
    Qed.

    Infix "⋈" := bsm_state_enc (at level 70, no associativity).

    Let HQ1 : forall i1 v1 w1 i2 v2, v1 ⋈ w1 /\ (iP,cP) /BSM/ (i1,v1) ~~> (i2,v2)     
                    -> exists w2,    v2 ⋈ w2 /\ Q /MM/ (lnk i1,w1) ~~> (lnk i2,w2).
    Proof. apply (proj2_sig (projT2 lnk_Q_pair)). Qed.

    Let HQ2 : forall i1 v1 w1 j2 w2, v1 ⋈ w1 /\ Q /MM/ (lnk i1,w1) ~~> (j2,w2) 
                    -> exists i2 v2, v2 ⋈ w2 /\ (iP,cP) /BSM/ (i1,v1) ~~> (i2,v2) /\ j2 = lnk i2.
    Proof. apply (proj2_sig (projT2 lnk_Q_pair)). Qed.

    Variable v : vec (list bool) m. 

    Let w := 0##0##vec_map stack_enc v.

    Let w_prop : bsm_state_enc v w.
    Proof.
      red; unfold w, tmp1, tmp2; repeat split; rew vec.
      intros p; unfold reg; simpl. 
      rewrite vec_pos_map; trivial.
    Qed. 

    (** (iQ,cQ) simulates termination of (iP,cP) while ensuring tmp1 and tmp2 stay void when it terminates *)

    Let Q_spec1 : (iP,cP) /BSM/ (iP,v) ↓ -> exists w', Q /MM/ (1,w) ~~> (code_end Q, w') /\ w'#>tmp1 = 0 /\ w'#>tmp2 = 0.
    Proof.
      intros ((i1,v1) & H1).
      destruct HQ1 with (1 := conj w_prop H1) as (w' & H2 & H3).
      rewrite <- (proj2 (proj2 Hlnk) i1), <- (proj1 (proj2 Hlnk)).
      * exists w'; split; auto; red in H2; tauto.
      * apply H1.
    Qed.

    Let Q_spec2 : Q /MM/ (1,w) ↓ -> (iP,cP) /BSM/ (iP,v) ↓.
    Proof.
      intros ((j,w2) & H1).
      rewrite <- (proj1 (proj2 Hlnk)) in H1.
      destruct HQ2 with (1 := conj w_prop H1) as (i2 & v2 & H2 & H3 & _).
      exists (i2,v2); auto.
    Qed.

    Definition bsm_mm_sim := snd Q.

    Theorem bsm_mm_sim_spec : (iP,cP) /BSM/ (iP,v) ↓ <-> (1,bsm_mm_sim) /MM/ (1,w) ↓.
    Proof.
      rewrite <- (proj1 Hlnk) at 1.
      rewrite <- surjective_pairing.
      split; auto.
      intros H.
      destruct (Q_spec1 H) as (w' & H1 & _).
      exists (code_end Q, w'); auto.
    Qed.

    Let iE := code_end Q.

    (** We complete (iQ,cQ) with some code nullifying all variables except tmp1 & tmp2 *)

    Let cN := mm_nullify tmp1 iE (map (fun p => pos_nxt (pos_nxt p)) (pos_list m)).
    Let cE := cN ++ DEC tmp1 0 :: nil.
  
    Let E_spec w' : w'#>tmp1 = 0 -> w'#>tmp2 = 0 -> (iE,cE) /MM/ (iE,w') -+> (0,vec_zero).
    Proof.
      intros H1 H2.
      unfold cE.
      apply sss_compute_progress_trans with (length cN+iE,vec_zero).
      + apply subcode_sss_compute with (P := (iE,cN)); auto.
        apply mm_nullify_compute; auto.
        * intros p Hp.
          apply in_map_iff in Hp.
          destruct Hp as (x & H3 & H4); subst; discriminate.
        * intros p Hp.
          apply in_map_iff in Hp.
          destruct Hp as (x & H3 & H4); subst; apply vec_zero_spec.
        * intros p Hp.
          unfold n, tmp1, tmp2 in *; simpl in p.
          pos_inv p; auto.
          pos_inv p; auto.
          destruct Hp; apply in_map_iff; exists p; split; auto.
          apply pos_list_prop.
      + apply subcode_sss_progress with (P := (length cN+iE,DEC tmp1 0::nil)); auto.
        mm sss DEC 0 with tmp1 0.
        apply subcode_refl.
        mm sss stop.
    Qed.
  
    Definition bsm_mm := snd Q ++ cE.
  
    Let cQ_sim : Q <sc (1,bsm_mm).
    Proof.
      unfold bsm_mm; destruct Q as (iQ,cQ); simpl in Hlnk.
      simpl snd; rewrite (proj1 Hlnk); auto.
    Qed.
  
    Let cE_sim : (iE,cE) <sc (1,bsm_mm).
    Proof.
      unfold iE, bsm_mm; subcode_tac; solve list eq.
      rewrite (proj1 Hlnk); auto.
    Qed.

    (** (1,bsm_sim) is a simulator for (iP,cP) *)
  
    Theorem bsm_mm_spec : (iP,cP) /BSM/ (iP,v) ↓ <-> (1,bsm_mm) /MM/ (1,w) ~~> (0,vec_zero).
    Proof.
      split.
      * intros H1.
        apply Q_spec1 in H1.
        destruct H1 as (w' & (H1 & H0) & H2 & H3).
        split.
        2: simpl; omega.
        apply sss_compute_trans with (st2 := (iE,w')).
        revert H1; apply subcode_sss_compute; auto.
        apply sss_progress_compute.
        generalize (E_spec _ H2 H3); apply subcode_sss_progress; auto.
      * intros H1.
        apply Q_spec2.
        apply subcode_sss_terminates with (1 := cQ_sim).
        exists (0,vec_zero); auto.
    Qed.

  End bsm_sim.

End simulator.

Theorem bsm_mm_compiler_1 n i (P : list (bsm_instr n)) :
  { Q : list (mm_instr (2+n)) | forall v, (i,P) /BSM/ (i,v) ↓ <-> (1,Q) /MM/ (1,0##0##vec_map stack_enc v) ↓ }.
Proof. exists (bsm_mm_sim i P); apply bsm_mm_sim_spec. Qed.

Theorem bsm_mm_compiler_2 n i (P : list (bsm_instr n)) :
  { Q : list (mm_instr (2+n)) | forall v, (i,P) /BSM/ (i,v) ↓ <-> (1,Q) /MM/ (1,0##0##vec_map stack_enc v) ~~> (0,vec_zero) }.
Proof. exists (bsm_mm i P); apply bsm_mm_spec. Qed.
