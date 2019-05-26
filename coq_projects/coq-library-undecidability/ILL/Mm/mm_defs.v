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
Require Import subcode sss.

Set Implicit Arguments.

Tactic Notation "rew" "length" := autorewrite with length_db.

Local Notation "e #> x" := (vec_pos e x).
Local Notation "e [ v / x ]" := (vec_change e x v).

(** * Minsky Machines

    A Minsky machine has n registers and there are just two instructions
 
    1/ INC x   : increment register x by 1
    2/ DEC x k : decrement register x by 1 if x > 0
                 or jump to k if x = 0

  *)

Inductive mm_instr n : Set :=
  | mm_inc : pos n -> mm_instr n
  | mm_dec : pos n -> nat -> mm_instr n
  .

Notation INC := mm_inc.
Notation DEC := mm_dec.

(** ** Semantics for MM *)

Section Minsky_Machine.

  Variable (n : nat).

  Definition mm_state := (nat*vec nat n)%type.

  (* Minsky machine small step semantics *)

  Inductive mm_sss : mm_instr n -> mm_state -> mm_state -> Prop :=
    | in_mm_sss_inc   : forall i x v,                   INC x   // (i,v) -1> (1+i,v[(S (v#>x))/x])
    | in_mm_sss_dec_0 : forall i x k v,   v#>x = O   -> DEC x k // (i,v) -1> (k,v)
    | in_mm_sss_dec_1 : forall i x k v u, v#>x = S u -> DEC x k // (i,v) -1> (1+i,v[u/x])
  where "i // s -1> t" := (mm_sss i s t).

  Fact mm_sss_fun i s t1 t2 : i // s -1> t1 -> i // s -1> t2 -> t1 = t2.
  Proof.
    intros []; subst.
    inversion 1; subst; auto.
    inversion 1; subst; auto.
    rewrite H in H6; discriminate.
    inversion 1; subst; auto.
    rewrite H in H6; discriminate.
    rewrite H in H6; inversion H6; subst; auto.
  Qed.
  
  Fact mm_sss_total ii s : { t | ii // s -1> t }.
  Proof.
    destruct s as (i,v).
    destruct ii as [ x | x j ]; [ | case_eq (v#>x); [ | intros k ]; intros E ].
    * exists (1+i,v[(S (v#>x))/x]); constructor.
    * exists (j,v); constructor; auto.
    * exists (1+i,v[k/x]); constructor; auto.
  Qed.
  
  Fact mm_sss_INC_inv x i v j w : INC x // (i,v) -1> (j,w) -> j=1+i /\ w = v[(S (v#>x))/x].
  Proof. inversion 1; subst; auto. Qed.
  
  Fact mm_sss_DEC0_inv x k i v j w : v#>x = O -> DEC x k // (i,v) -1> (j,w) -> j = k /\ w = v.
  Proof. 
    intros H; inversion 1; subst; auto; rewrite H in H2; try discriminate.
  Qed.
  
  Fact mm_sss_DEC1_inv x k u i v j w : v#>x = S u -> DEC x k // (i,v) -1> (j,w) -> j=1+i /\ w = v[u/x].
  Proof. 
    intros H; inversion 1; subst; auto; rewrite H in H2; try discriminate.
    inversion H2; subst; auto.
  Qed.

(*
  Definition mm_step_stall := sss_step_stall mm_sss.
  Definition mm_program := (nat*list (mm_instr n))%type.
  Definition mm_steps := sss_steps mm_sss.
  Definition mm_compute := sss_compute mm_sss.
*)

  Notation "P // s -[ k ]-> t" := (sss_steps mm_sss P k s t).
  Notation "P // s -+> t" := (sss_progress mm_sss P s t).
  Notation "P // s ->> t" := (sss_compute mm_sss P s t).
  
  Fact mm_progress_INC P i x v st :
         (i,INC x::nil) <sc P
      -> P // (1+i,v[(S (v#>x))/x]) ->> st
      -> P // (i,v) -+> st.
  Proof.
    intros H1 H2.
    apply sss_progress_compute_trans with (2 := H2).
    apply subcode_sss_progress with (1 := H1).
    exists 1; split; auto; apply sss_steps_1.
    apply in_sss_step with (l := nil).
    simpl; omega.
    constructor; auto.
  Qed.
  
  Corollary mm_compute_INC P i x v st : (i,INC x::nil) <sc P -> P // (1+i,v[(S (v#>x))/x]) ->> st -> P // (i,v) ->> st.
  Proof. intros; apply sss_progress_compute; eapply mm_progress_INC; eauto. Qed.
  
  Fact mm_progress_DEC_0 P i x k v st :
         (i,DEC x k::nil) <sc P
      -> v#>x = O 
      -> P // (k,v) ->> st
      -> P // (i,v) -+> st.
  Proof.
    intros H1 H2 H3.
    apply sss_progress_compute_trans with (2 := H3).
    apply subcode_sss_progress with (1 := H1).
    exists 1; split; auto; apply sss_steps_1.
    apply in_sss_step with (l := nil).
    simpl; omega.
    constructor; auto.
  Qed.
  
  Corollary mm_compute_DEC_0 P i x k v st : (i,DEC x k::nil) <sc P -> v#>x = O -> P // (k,v) ->> st -> P // (i,v) ->> st.
  Proof. intros; apply sss_progress_compute; eapply mm_progress_DEC_0; eauto. Qed.
  
  Fact mm_progress_DEC_S P i x k v u st :
         (i,DEC x k::nil) <sc P
      -> v#>x = S u 
      -> P // (1+i,v[u/x]) ->> st
      -> P // (i,v) -+> st.
  Proof.
    intros H1 H2 H3.
    apply sss_progress_compute_trans with (2 := H3).
    apply subcode_sss_progress with (1 := H1).
    exists 1; split; auto; apply sss_steps_1.
    apply in_sss_step with (l := nil).
    simpl; omega.
    constructor; auto.
  Qed.
  
  Corollary mm_compute_DEC_S P i x k v u st : (i,DEC x k::nil) <sc P -> v#>x = S u -> P // (1+i,v[u/x]) ->> st -> P // (i,v) ->> st.
  Proof. intros; apply sss_progress_compute; eapply mm_progress_DEC_S; eauto. Qed.
  
  Fact mm_steps_INC_inv k P i x v st :
         (i,INC x::nil) <sc P
      -> k <> 0
      -> P // (i,v) -[k]-> st
      -> exists k', k' < k /\ P // (1+i,v[(S (v#>x))/x]) -[k']-> st.
  Proof.
    intros H1 H2 H4.
    apply sss_steps_inv in H4.
    destruct H4 as [ (? & ?) | (k' & st2 & ? & H4 & H5) ]; subst; auto.
    destruct H2; auto.
    apply sss_step_subcode_inv with (1 := H1) in H4.
    exists k'; split.
    omega.
    inversion H4; subst; auto.
  Qed.
  
  Fact mm_steps_DEC_0_inv k P i x p v st :
         (i,DEC x p::nil) <sc P
      -> k <> 0
      -> v#>x = 0
      -> P // (i,v) -[k]-> st
      -> exists k', k' < k /\ P // (p,v) -[k']-> st.
  Proof.
    intros H1 H2 H3 H4.
    apply sss_steps_inv in H4.
    destruct H4 as [ (? & ?) | (k' & st2 & ? & H4 & H5) ]; subst; auto.
    destruct H2; auto.
    apply sss_step_subcode_inv with (1 := H1) in H4.
    exists k'; split.
    omega.
    inversion H4; subst; auto.
    rewrite H3 in H9; discriminate.
  Qed.
  
  Fact mm_steps_DEC_1_inv k P i x p v u st :
         (i,DEC x p::nil) <sc P
      -> k <> 0
      -> v#>x = S u
      -> P // (i,v) -[k]-> st
      -> exists k', k' < k /\ P // (1+i,v[u/x]) -[k']-> st.
  Proof.
    intros H1 H2 H3 H4.
    apply sss_steps_inv in H4.
    destruct H4 as [ (? & ?) | (k' & st2 & ? & H4 & H5) ]; subst; auto.
    destruct H2; auto.
    apply sss_step_subcode_inv with (1 := H1) in H4.
    exists k'; split.
    omega.
    inversion H4; subst; auto; rewrite H3 in H9.
    discriminate.
    inversion H9; subst; auto.
  Qed.
  
End Minsky_Machine.

Local Notation "P // s -[ k ]-> t" := (sss_steps (@mm_sss _) P k s t).
Local Notation "P // s -+> t" := (sss_progress (@mm_sss _) P s t).
Local Notation "P // s ->> t" := (sss_compute (@mm_sss _) P s t).

Tactic Notation "mm" "sss" "INC" "with" uconstr(a) := 
  match goal with
    | |- _ // _ -+> _ => apply mm_progress_INC with (x := a)
    | |- _ // _ ->> _ => apply mm_compute_INC with (x := a)
  end; auto.

Tactic Notation "mm" "sss" "DEC" "0" "with" uconstr(a) uconstr(b) := 
  match goal with
    | |- _ // _ -+> _ => apply mm_progress_DEC_0 with (x := a) (k := b)
    | |- _ // _ ->> _ => apply mm_compute_DEC_0 with (x := a) (k := b)
  end; auto.

Tactic Notation "mm" "sss" "DEC" "S" "with" uconstr(a) uconstr(b) uconstr(c) := 
  match goal with
    | |- _ // _ -+> _ => apply mm_progress_DEC_S with (x := a) (k := b) (u := c)
    | |- _ // _ ->> _ => apply mm_compute_DEC_S with (x := a) (k := b) (u := c)
  end; auto.
    
Tactic Notation "mm" "sss" "stop" := exists 0; apply sss_steps_0; auto.

(* The Halting problem for MM, for linear logic encoding, we restrict
   to a very specific halting problem. Starting from (1,v), does the
   MM halt at state (0,vec_zero) *)

Definition MM_PROBLEM := { n : nat & { P : list (mm_instr n) & vec nat n } }.

Local Notation "i // s -1> t" := (@mm_sss _ i s t).
Local Notation "P // s ~~> t" := (sss_output (@mm_sss _) P s t).
Local Notation "P // s ↓" := (sss_terminates (@mm_sss _) P s). 

Definition MM_HALTS_ON_ZERO (P : MM_PROBLEM) := 
  match P with existT _ n (existT _ P v) => (1,P) // (1,v) ~~> (0,vec_zero) end.

Definition MM_HALTING (P : MM_PROBLEM) :=
  match P with existT _ n (existT _ P v) => (1, P) // (1, v) ↓ end.

Section mm_special_ind.

  Variables (n : nat) (P : nat*list (mm_instr n)) (se : nat * vec nat n)
            (Q : nat * vec nat n -> Prop).

  Hypothesis (HQ0 : Q se)
             (HQ1 : forall i ρ v j w,   (i,ρ::nil) <sc P
                                     -> ρ // (i,v) -1> (j,w)
                                     -> P // (j,w) ->> se
                                     -> Q (j,w)
                                     -> Q (i,v)).

  Theorem mm_special_ind s : P // s ->> se -> Q s.
  Proof.
    intros (q & H1); revert s H1.
    induction q as [ | q IHq ]; intros s Hs.
    + apply sss_steps_0_inv in Hs; subst; apply HQ0.
    + apply sss_steps_S_inv' in Hs.
      destruct Hs as ((j,w) & (j' & l & ρ & r & u & G1 & G2 & G3) & Hs2); subst s P.
      apply HQ1 with (i := j'+length l) (2 := G3); auto.
      exists q; auto.
  Qed.

End mm_special_ind.

Section mm_term_ind.

  Variables (n : nat) (P : nat*list (mm_instr n)) (se : nat * vec nat n)
            (Q : nat * vec nat n -> Prop).

  Hypothesis (HQ0 : out_code (fst se) P -> Q se)
             (HQ1 : forall i ρ v j w,    (i,ρ::nil) <sc P
                                     -> ρ // (i,v) -1> (j,w)
                                     -> P // (j,w) ~~> se
                                     -> Q (j,w)
                                     -> Q (i,v)).

  Theorem mm_term_ind s : P // s ~~> se -> Q s.
  Proof.
    intros (H1 & H2).
    revert s H1; apply mm_special_ind; auto.
    intros i rho v j w' H1 H3 H4.
    apply HQ1 with (1 := H1); auto.
    split; auto.
  Qed.

End mm_term_ind.




