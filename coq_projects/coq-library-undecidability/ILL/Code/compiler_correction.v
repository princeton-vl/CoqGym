(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

(* Trying an abstract compiler with labels instead of nats as source code addressing *)

Require Import List Arith Omega.

Require Import utils subcode sss bsm_defs compiler.


(** ** Semantic Correctness of Compiled Code *)

Set Implicit Arguments.

Section comp.

  (** This is an abstract proof of compiler soundness & completeness 

      The principle of this compiler is to map every source individual
      instruction into a list of target instructions that simulate the
      source instruction. We describe our assumptions later on ...

    *)

  Variable (X Y : Set)                                  (* X is a small type of source instructions and 
                                                           Y of destination instructions *) 
           (icomp : (nat -> nat) -> nat -> X -> list Y) (* instruction compiler w.r.t. a given linker & a position 
                                                           icomp lnk i x compiles instruction x at position i 
                                                           using linker lnk into a list of target instructions
                                                         *)
           (ilen  : X -> nat)                           (* compiled code length does not depend on linker or position,
                                                           it only depends on the original instruction
                                                           whether this assumption is strong or not is debatable
                                                           but we only encountered cases which satisfy this assuption
                                                         *)
           (Hilen : forall lnk n x, length (icomp lnk n x) = ilen x)
           (*Hilen2  : forall x, 1 <= ilen x*).           (* compiled code should not be empty, even if the source
                                                           instruction is something like NO-OP, to ensure progress
                                                           in the simulation as source code executes 
                                                           also not a strong requirement

                                                           This can be removed because it can be deduced (where it
                                                           is used) from Hilen1 & step_X_tot & Hicomp 
                                                         *)

  (* Semantics for X and Y instructions *)

  Variables (state_X state_Y : Type)
            (step_X : X -> (nat*state_X) -> (nat*state_X) -> Prop)
            (step_Y : Y -> (nat*state_Y) -> (nat*state_Y) -> Prop).

  Notation "i '/X/' s -1> t" := (step_X i s t) (at level 70, no associativity).
  Notation "P '/X/' s '-[' k ']->' t" := (sss_steps step_X P k s t) (at level 70, no associativity).
  Notation "P '/X/' s '-+>' t" := (sss_progress step_X P s t) (at level 70, no associativity).
  Notation "P '/X/' s ->> t" := (sss_compute step_X P s t) (at level 70, no associativity).
  Notation "P '/X/' s '~~>' t" := (sss_output step_X P s t) (at level 70, no associativity).
  Notation "P '/X/' s ↓" := (sss_terminates step_X P s)(at level 70, no associativity).

  Notation "i '/Y/' s -1> t" := (step_Y i s t) (at level 70, no associativity).
  Notation "P '/Y/' s '-[' k ']->' t" := (sss_steps step_Y P k s t) (at level 70, no associativity).
  Notation "P '/Y/' s '-+>' t" := (sss_progress step_Y P s t) (at level 70, no associativity).
  Notation "P '/Y/' s ->> t" := (sss_compute step_Y P s t) (at level 70, no associativity).
  Notation "P '/Y/' s '~~>' t" := (sss_output step_Y P s t) (at level 70, no associativity).
  Notation "P '/Y/' s ↓" := (sss_terminates step_Y P s)(at level 70, no associativity).

  (** We assume totality of X semantics, i.e. no instruction can block the computation
      and functionality of Y semantics 

      Totality is not necessary achieved ... think of a HALT instruction 
      what should we do in that case ? It should not be too difficult to
      embed a partial model of computation into a total one by transforming
      blocking cases into jumps at a PC value outside of the code.
    *)

  Hypothesis (step_X_tot : forall I st1, exists st2, I /X/ st1 -1> st2)
             (step_Y_fun : forall I st st1 st2, I /Y/ st -1> st1 -> I /Y/ st -1> st2 -> st1 = st2).

 (** simul is an invariant: simul st_X st_Y means that st_X is simulated by st_Y *)

  Variable (simul : state_X -> state_Y -> Prop).

  Infix "⋈" := simul (at level 70, no associativity).

  (** Simulation is preserved by compiled instructions 
      this of course ensures the *semantic correctness of
      the compilation of individual instructions*

      Notice the important hypothesis of preservation of the +1
      relative address by the linker otherwise it might not be
      possible to establish the below predicate.

      If the source language involves other relative addresses like
      +2 or +d or -d, the present compiler might have to be substantially
      updated.

      +1 is very likely to be used even implicitly because every instruction
      that does not branch (like INC or PUSH) implicitly jumps at +1 ...
    *) 

  Definition instruction_compiler_sound := forall lnk I i1 v1 i2 v2 w1, 
                     I /X/ (i1,v1) -1> (i2,v2)
                  -> lnk (1+i1) = length (icomp lnk i1 I) + lnk i1
                  -> v1 ⋈ w1
       -> exists w2, (lnk i1,icomp lnk i1 I) /Y/ (lnk i1,w1) -+> (lnk i2,w2)
                  /\ v2 ⋈ w2.

  Hypothesis Hicomp : instruction_compiler_sound.

  Section correctness. 

    (** We assume each instruction in P is compiled in Q according to the individual 
        instruction compiler combined with what the linker says for branching. 
        This is a *syntactic correctness criterion* for the whole compiled program Q
      *)

    Variables (linker : nat -> nat) (P : nat * list X) (Q : nat * list Y)
              (HPQ : forall i I, (i,I::nil) <sc P -> (linker i, icomp linker i I) <sc Q
                                                   /\ linker (1+i) = ilen I + linker i).

    (** From semantic correctness of individually compiled instructions and
        syntactic correctness of the whole compiled program, we derive
        soundness and completeness of the compiled program Q wrt the
        source program P *)

    Theorem compiler_sound i1 v1 i2 v2 w1 :
                      v1 ⋈ w1 /\ P /X/ (i1,v1) ->> (i2,v2)
        -> exists w2, v2 ⋈ w2 /\ Q /Y/ (linker i1,w1) ->> (linker i2,w2).
    Proof.
      change i1 with (fst (i1,v1)) at 2; change v1 with (snd (i1,v1)) at 1.
      change i2 with (fst (i2,v2)) at 2; change v2 with (snd (i2,v2)) at 2.
      generalize (i1,v1) (i2,v2); clear i1 v1 i2 v2.
      intros st1 st2 (H1 & q & H2); revert H2 w1 H1.
      induction 1 as [ (i1,v1) | q (i1,v1) (i2,v2) st3 H1 H2 IH2]; simpl; intros w1 H0.
      + exists w1; split; auto; exists 0; constructor.
      + destruct H1 as (k & l & I & r & v' & G1 & G2 & G3).
        inversion G2; subst v' i1; clear G2.
        destruct (Hicomp linker) with (1 := G3) (3 := H0)
          as (w2 & G4 & G5).
        * rewrite Hilen; apply HPQ; subst; exists l, r; auto.
        * destruct (IH2 _ G5) as (w3 & G6 & G7).
          exists w3; split; auto.
          apply sss_compute_trans with (2 := G7); simpl.
          apply sss_progress_compute.
          revert G4; apply subcode_sss_progress.
          apply HPQ; subst; exists l, r; auto.
    Qed.

    (* When still inside of P, the computation in Q simulates
       a computation in P *)

    Local Lemma compiler_complete_step p st1 w1 w3 :
           snd st1 ⋈ snd w1
        -> linker (fst st1) = fst w1
        -> in_code (fst st1) P
        -> out_code (fst w3) Q
        -> Q /Y/ w1 -[p]-> w3
        -> exists q st2 w2, snd st2 ⋈ snd w2
                        /\ linker (fst st2) = fst w2
                        /\ P /X/ st1 ->> st2
                        /\ Q /Y/ w2 -[q]-> w3
                        /\ q < p.
    Proof.
      revert st1 w1 w3; intros (i1,v1) (j1,w1) (j3,w3); simpl fst; simpl snd.
      intros H1 H2 H3 H4 H5.
      destruct (in_code_subcode H3) as (I & HI).
      destruct HPQ with (1 := HI) as (H6 & H7).
      assert (out_code j3 (linker i1, icomp linker i1 I)) as G2.
      { revert H4; apply subcode_out_code; auto. }
      assert (H8 : ilen I <> 0).
      { intros H.
        destruct (step_X_tot I (i1,v1)) as ((i2,v2) & Hst).
        apply (Hicomp linker) with (3 := H1) in Hst; auto.
        2: rewrite Hilen; auto.
        destruct Hst as (w2 & (q & Hq1 & Hq2) & _).
        rewrite <- (Hilen linker i1) in H.
        destruct (icomp linker i1 I); try discriminate.
        apply sss_steps_stall, proj1 in Hq2; simpl; omega. }
      assert (in_code (linker i1) (linker i1, icomp linker i1 I)) as G3.
      { simpl; rewrite (Hilen linker i1 I); omega. }
      rewrite <- H2 in H5.
      destruct (step_X_tot I (i1,v1)) as ((i2,v2) & G4).
      destruct (Hicomp linker) with (1 := G4) (3 := H1) as (w2 & G5 & G6).
      * rewrite H7, Hilen; auto.
      * apply subcode_sss_progress_inv with (3 := H6) (4 := G5) in H5; auto.
        destruct H5 as (q & H5 & G7).
        exists q, (i2,v2), (linker i2, w2); simpl; repeat (split; auto).
        apply subcode_sss_compute with (1 := HI).
        exists 1; apply sss_steps_1.
        exists i1, nil, I, nil, v1; repeat (split; auto).
        f_equal; simpl; omega.
    Qed.

    (* Termination in Q simulates termination in P *)

    Theorem compiler_complete i1 v1 w1 : 
          v1 ⋈ w1 -> Q /Y/ (linker i1,w1) ↓ -> P /X/ (i1,v1) ↓.
    Proof.
      intros H1 (st & (q & H2) & H3). 
      revert i1 v1 w1 H1 H2 H3.
      induction q as [ q IHq ] using (well_founded_induction lt_wf).
      intros i1 v1 w1 H1 H2 H3.
      destruct (in_out_code_dec i1 P) as [ H4 | H4 ].
      + destruct compiler_complete_step with (5 := H2) (st1 := (i1,v1))
          as (p & (i2,v2) & (j2,w2) & G1 & G2 & G3 & G4 & G5); auto; simpl in *; subst j2.
        destruct IHq with (1 := G5) (2 := G1) (3 := G4)
          as ((i3 & v3) & F3 & F4); auto.
        exists (i3,v3); repeat (split; auto).
        apply sss_compute_trans with (1 := G3); auto.
      + exists (i1,v1); repeat (split; auto).
        exists 0; constructor.
    Qed.

    Corollary compiler_complete' i1 v1 w1 st : 
                            v1 ⋈ w1 /\ Q /Y/ (linker i1,w1) ~~> st
        -> exists i2 v2 w2, v2 ⋈ w2 /\ P /X/ (i1,v1) ~~> (i2,v2)
                                    /\ Q /Y/ (linker i2,w2) ~~> st.
    Proof.
      intros (H1 & H2).
      destruct compiler_complete with (1 := H1) (2 := ex_intro (fun x => Q /Y/ (linker i1, w1) ~~> x) _ H2)
        as ((i2,v2) & H3 & H4).
      exists i2, v2.
      destruct (compiler_sound (conj H1 H3)) as (w2 & H5 & H6).
      exists w2; do 2 (split; auto).
      split; auto.
      destruct H2 as (H2 & H0); split; auto.
      apply sss_compute_inv with (3 := H6); auto.
    Qed.

  End correctness.

  (** ** A Syntactically Correct Compiler *)

  (** Now we build a correct linker & compiled program pair *)

  Variable (P : nat * list X) (iQ : nat).

  Let iP := fst P.
  Let cP := snd P.

  Let err := iQ+length_compiler ilen cP.

  Definition gen_linker := linker ilen (iP,cP) iQ err.
  Definition gen_compiler := compiler icomp ilen (iP,cP) iQ err.

  Notation cQ := gen_compiler.
  Notation lnk := gen_linker.

  Let P_eq : P = (iP,cP).
  Proof. unfold iP, cP; destruct P; auto. Qed.

  Fact gen_linker_out i : out_code i (iP,cP) -> lnk i = iQ+length cQ.
  Proof.
    intros H.
    unfold lnk.
    rewrite linker_out_err; unfold err; simpl; auto.
    * unfold cQ; rewrite compiler_length; auto.
    * omega.
  Qed.

  Theorem gen_compiler_sound i1 v1 i2 v2 w1 : 
                    v1 ⋈ w1 /\ (iP,cP) /X/ (i1,v1) ~~> (i2,v2)
      -> exists w2, v2 ⋈ w2 /\ (iQ,cQ) /Y/ (lnk i1,w1) ~~> (lnk i2,w2).
  Proof.
    intros (H1 & H2 & H3).
    destruct compiler_sound with (2 := conj H1 H2) (linker := gen_linker) (Q := (iQ,cQ))
      as (w2 & G1 & G2).
    + apply compiler_subcode; auto.
    + simpl fst in H3.
      exists w2; split; auto.
      split; auto; simpl.
      rewrite <- gen_linker_out with i2; auto.
  Qed.

  Theorem gen_compiler_complete i1 v1 w1 :
            v1 ⋈ w1 -> (iQ,gen_compiler) /Y/ (gen_linker i1,w1) ↓ -> (iP,cP) /X/ (i1,v1) ↓.
  Proof.
    apply compiler_complete, compiler_subcode; auto.
  Qed.

  Corollary gen_compiler_output v w i' v' : 
        v ⋈ w -> (iP,cP) /X/ (iP,v) ~~> (i',v') -> exists w', (iQ,gen_compiler) /Y/ (iQ,w) ~~> (code_end (iQ,cQ),w') /\ v' ⋈ w'.
  Proof.
    intros H H1.
    destruct gen_compiler_sound with (1 := conj H H1) as (w1 & H2 & H3).
    exists w1.
    simpl; rewrite <- gen_linker_out with i'.
    + rewrite <- (linker_code_start ilen (iP,cP) iQ err) at 2; auto.
    + apply H1.
  Qed.

  Corollary gen_compiler_terminates v w : 
          v ⋈ w -> (iQ,gen_compiler) /Y/ (iQ,w) ↓ -> (iP,cP) /X/ (iP,v) ↓.
  Proof.
    intros H (w' & H').
    apply gen_compiler_complete with (1 := H).
    unfold gen_linker; rewrite linker_code_start; auto; firstorder.
  Qed.

  Theorem gen_compiler_correction : 
           { lnk : nat -> nat 
           & { Q | fst Q = iQ 
                /\ lnk iP = iQ
                /\ (forall i, out_code i P -> lnk i = code_end Q)
                /\ (forall i1 v1 w1 i2 v2, v1 ⋈ w1 /\ P /X/ (i1,v1) ~~> (i2,v2)     -> exists w2,    v2 ⋈ w2 /\ Q /Y/ (lnk i1,w1) ~~> (lnk i2,w2)) 
                /\ (forall i1 v1 w1 j2 w2, v1 ⋈ w1 /\ Q /Y/ (lnk i1,w1) ~~> (j2,w2) -> exists i2 v2, v2 ⋈ w2 /\ P /X/ (i1,v1) ~~> (i2,v2) /\ j2 = lnk i2) 
           } }.
  Proof.
    exists lnk, (iQ,cQ); split; auto; split; [ | split ].
    + rewrite <- (linker_code_start ilen (iP,cP) iQ err); auto.
    + rewrite P_eq; apply gen_linker_out.
    + rewrite P_eq.
      split.
      * intros i1 v1 w1 i2 v2 H.
        destruct gen_compiler_sound with (1 := H) as (w2 & H3 & H4).
        exists w2; split; auto.
      * intros i1 v1 w1 j2 w2 (H1 & H2).
        destruct gen_compiler_complete with (1 := H1) (i1 := i1) 
          as ((i3,v3) & H3).
        - exists (j2,w2); auto.
        - destruct gen_compiler_sound with (1 := conj H1 H3) as (w3 & H4 & H5).
          generalize (sss_output_fun step_Y_fun H2 H5); inversion 1.
          exists i3, v3; auto.
  Qed.

End comp.
