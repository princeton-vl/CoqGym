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
Require Import subcode sss compiler.
Require Import list_bool.
Require Import bsm_defs.
Require Import mm_defs mm_utils.

Set Implicit Arguments.

Tactic Notation "rew" "length" := autorewrite with length_db.

Local Notation "e #> x" := (vec_pos e x).
Local Notation "e [ v / x ]" := (vec_change e x v).

Local Notation "P '/BSM/' s ->> t" := (sss_compute (@bsm_sss _) P s t) (at level 70, no associativity).

Local Notation "P // s -[ k ]-> t" := (sss_steps (@mm_sss _) P k s t).
Local Notation "P // s -+> t" := (sss_progress (@mm_sss _) P s t).
Local Notation "P // s ->> t" := (sss_compute (@mm_sss _) P s t).
Local Notation "P // s -]] t" := (sss_compute_max (@mm_sss _) P s t).

Section compiler.

  Ltac dest x y := destruct (pos_eq_dec x y) as [ | ]; [ subst x | ]; rew vec.

  Variables (m : nat) (P : nat*list (bsm_instr m)).
  
  (** each stack of the BSM corresponds to a (unique) register in the MM 
        and there are extra registers: tmp1, tmp2 which must have value 0 at start 
        they might change value during a simulated BSM instruction but when
        the instruction is finished, their values are back to 0 
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
  
  Let err := length_compiler bsm_instr_compile_length (snd P)+1.
  
  Definition bsm_linker := linker bsm_instr_compile_length P 1 err.
  Definition bsm_compiler := compiler bsm_instr_compile bsm_instr_compile_length P 1 err.
     
  Notation Q := (1,bsm_compiler).

  Notation lnk := bsm_linker.
  Notation comp := (bsm_instr_compile lnk).
  Notation lng := bsm_instr_compile_length.
  
  Fact bsm_compiler_length : length bsm_compiler = length_compiler bsm_instr_compile_length (snd P).
  Proof. apply compiler_length, bsm_instr_compile_length_eq. Qed.
             
  (** Coherence hypothesis = syntactic correction criterion 
     
        Every instruction at position i in P is compiled in Q 
        between positions lnk i and lnk (1+i)
    
     *)

  Fact bsm_coherence i ibsm :     (i,ibsm::nil) <sc P 
                               -> (lnk i, comp i ibsm) <sc Q
                                /\ lnk (1+i) = lng ibsm + lnk i.
  Proof. apply compiler_subcode, bsm_instr_compile_length_eq. Qed.
  
  Fact bsm_linker_start : lnk (fst P) = 1.
  Proof. apply linker_code_start. Qed.
  
  Fact bsm_linker_out_code i : out_code i P -> out_code (lnk i) Q.
  Proof. 
    apply linker_out_code.
    apply bsm_instr_compile_length_eq.
    unfold err; omega.
  Qed.
  
  Fact bsm_linker_out_err i : out_code i P -> lnk i = err.
  Proof.
    unfold err.
    destruct (eq_nat_dec i (code_end P)) as [ E | D ].
    rewrite E; intros _; apply linker_code_end.
    intros; apply linker_err_code.
    simpl in D, H; omega.
  Qed.

  Notation Hc := bsm_coherence.

  Let Hc1 i : in_code i P -> in_code (lnk i) Q.
  Proof. 
    apply linker_in_code.
    apply bsm_instr_compile_length_eq.
    apply bsm_instr_compile_length_geq.
  Qed.

  Definition bsm_state_enc (v : vec (list bool) m) w := 
            w#>tmp1 = 0
         /\ w#>tmp2 = 0
         /\ forall p, w#>(reg p) = stack_enc (v#>p).
         
  (*** Soundness results *)

  Fact bic_PUSH_Zero i x w s : 
            (i,PUSH x Zero::nil) <sc P
         -> w#>(reg x) = stack_enc s
         -> w#>tmp1 = 0
         -> w#>tmp2 = 0
         -> (lnk i, comp i (PUSH x Zero)) // (lnk i,w) -+> (lnk (1+i), w[(stack_enc (Zero::s))/reg x]).
  Proof.
    intros H1 H2 H3 H4.
    replace (lnk (1+i)) with (7+lnk i).
    apply mm_push_Zero_progress; auto.
    apply Hc, proj2 in H1.
    rewrite H1; auto.
  Qed.

  Fact bic_PUSH_One i x w s : 
            (i,PUSH x One::nil) <sc P
         -> w#>(reg x) = stack_enc s
         -> w#>tmp1 = 0
         -> w#>tmp2 = 0
         -> (lnk i, comp i (PUSH x One)) // (lnk i,w) -+> (lnk (1+i), w[(stack_enc (One::s))/reg x]).
  Proof.
    intros H1 H2 H3 H4.
    replace (lnk (1+i)) with (8+lnk i).
    apply mm_push_One_progress; auto.
    apply Hc, proj2 in H1.
    rewrite H1; auto.
  Qed.

  Fact bic_POP_void i x j k w : 
           (i,POP x j k::nil) <sc P
        -> w#>(reg x) = stack_enc nil
        -> w#>tmp1 = 0
        -> w#>tmp2 = 0
        -> (lnk i, comp i (POP x j k)) // (lnk i,w) -+> (lnk k, w).
  Proof. intros; apply mm_pop_void_progress; auto. Qed.

  Fact bic_POP_Zero i x j k w s : 
            (i,POP x j k::nil) <sc P
         -> w#>(reg x) = stack_enc (Zero::s)
         -> w#>tmp1 = 0
         -> w#>tmp2 = 0
          -> (lnk i, comp i (POP x j k)) // (lnk i,w) -+> (lnk j, w[(stack_enc s)/reg x]).
  Proof. intros; apply mm_pop_Zero_progress; auto. Qed.

  Fact bic_POP_One i x j k w s : 
            (i,POP x j k::nil) <sc P
         -> w#>(reg x) = stack_enc (One::s)
         -> w#>tmp1 = 0
         -> w#>tmp2 = 0
         -> (lnk i, comp i (POP x j k)) // (lnk i,w) -+> (lnk (1+i), w[(stack_enc s)/reg x]).
  Proof. intros; apply mm_pop_One_progress; auto. Qed.
  
  Lemma bsm_instr_compiler_sound ii st1 st2 w1 :
           bsm_state_enc (snd st1) w1
        -> bsm_sss ii st1 st2
        -> (fst st1,ii::nil) <sc P
        -> exists w2, bsm_state_enc (snd st2) w2
                   /\ Q // (lnk (fst st1),w1) ->> (lnk (fst st2),w2).
  Proof.
    intros H1 H2 H3.
    induction H2 as   [ i p j k v Hv
                      | i p j k v ll Hll 
                      | i p j k v ll Hll
                      | i p [] v
                      ]; simpl in H1; destruct H1 as (H11 & H12 & H13);
                         generalize (@Hvr1 p) (@Hvr2 p); intros G1 G2.

    (* POP Empty *)

    * exists w1; split.
      red; rew vec; repeat split; auto.
      generalize (Hc _ _ H3); intros (G4 & _).
      apply subcode_sss_compute with (1 := G4).
      unfold fst, snd.
      apply sss_progress_compute, bic_POP_void; auto.
      rewrite H13, Hv; auto.
      
    (* POP Zero *)

    * exists (w1[(stack_enc ll)/reg p]); simpl; split.
      red; rew vec; repeat split; auto.
      intros q.
      dest p q.
      assert (reg p <> reg q).
        intros E; apply Hreg in E; subst; tauto.
      rew vec.
      generalize (Hc _ _ H3); intros (G4 & _).
      apply subcode_sss_compute with (1 := G4).
      unfold fst, snd.
      apply sss_progress_compute, bic_POP_Zero; auto.
      rewrite H13, Hll; auto.

    (* POP One *)

    * exists (w1[(stack_enc ll)/reg p]); simpl; split.
      red; rew vec; repeat split; auto.
      intros q.
      dest p q.
      assert (reg p <> reg q).
        intros E; apply Hreg in E; subst; tauto.
      rew vec.
      generalize (Hc _ _ H3); intros (G4 & _).
      apply subcode_sss_compute with (1 := G4).
      unfold fst, snd.
      apply sss_progress_compute, bic_POP_One; auto.
      rewrite H13, Hll; auto.

    (* PUSH One *)

    * exists (w1[(stack_enc (One::v#>p))/reg p]); simpl; split.
      red; rew vec; repeat split; auto.
      intros q.
      dest p q.
      assert (reg p <> reg q).
        intros E; apply Hreg in E; subst; tauto.
      rew vec.
      generalize (Hc _ _ H3); intros (G4 & _).
      apply subcode_sss_compute with (1 := G4).
      unfold fst, snd.
      apply sss_progress_compute, bic_PUSH_One; auto.

    (* PUSH Zero *)

    * exists (w1[(stack_enc (Zero::v#>p))/reg p]); simpl; split.
      red; rew vec; repeat split; auto.
      intros q.
      dest p q.
      assert (reg p <> reg q).
        intros E; apply Hreg in E; subst; tauto.
      rew vec.
      generalize (Hc _ _ H3); intros (G4 & _).
      apply subcode_sss_compute with (1 := G4).
      unfold fst, snd.
      apply sss_progress_compute, bic_PUSH_Zero; auto.
  Qed.

  Theorem bsm_compiler_sound st1 st2 w1 :
           bsm_state_enc (snd st1) w1
        -> P /BSM/ st1 ->> st2
        -> exists w2, 
           bsm_state_enc (snd st2) w2
        /\ Q // (lnk (fst st1),w1) ->> (lnk (fst st2),w2).
  Proof.
    intros H1 (q & H2); revert H2 w1 H1.
    induction 1 as [ (i,v1) | q st1 st2 st3 H1 H2 IH2 ];
        intros w1 H3.
    * exists w1.
      simpl in H3 |- *.
      repeat (split; auto).
      exists 0; constructor.
    * destruct H1 as (j & l & ii & r & st0 & HP & Hst1 & H1).
      destruct (bsm_instr_compiler_sound H3 H1) as (v2 & H4 & H5).
      rewrite HP, Hst1; subcode_tac.
      destruct (IH2 _ H4) as (v3 & H7 & H8).
      exists v3; repeat (split; auto).
      apply sss_compute_trans with (1 := H5); auto.
  Qed.
  
  (*** Completeness results *)

  Fact bic_PUSH_Zero_inv p i x w s st : 
            (i,PUSH x Zero::nil) <sc P
         -> w#>(reg x) = stack_enc s
         -> w#>tmp1 = 0
         -> w#>tmp2 = 0
         -> out_code (fst st) Q
         -> Q // (lnk i,w) -[p]-> st
         -> exists q, q < p /\ Q // (lnk (1+i), w[(stack_enc (Zero::s))/reg x]) -[q]-> st.
  Proof.
    intros H1 H2 H3 H4 H5 H6.
    apply subcode_sss_progress_inv with (4 := bic_PUSH_Zero _ _ _ _ H1 H2 H3 H4); auto.
    apply mm_sss_fun.
    revert H5; apply subcode_out_code; auto.
    apply Hc; auto.
    apply Hc; auto.
  Qed.
    
  Fact bic_PUSH_One_inv p i x w s st : 
            (i,PUSH x One::nil) <sc P
         -> w#>(reg x) = stack_enc s
         -> w#>tmp1 = 0
         -> w#>tmp2 = 0
         -> out_code (fst st) Q
         -> Q // (lnk i,w) -[p]-> st
         -> exists q, q < p /\ Q // (lnk (1+i), w[(stack_enc (One::s))/reg x]) -[q]-> st.
  Proof.
    intros H1 H2 H3 H4 H5 H6.
    apply subcode_sss_progress_inv with (4 := bic_PUSH_One _ _ _ _ H1 H2 H3 H4); auto.
    apply mm_sss_fun.
    revert H5; apply subcode_out_code; auto.
    apply Hc; auto.
    apply Hc; auto.
  Qed.
    
  Fact bic_POP_void_inv p i x j k w st : 
           (i,POP x j k::nil) <sc P
        -> w#>(reg x) = stack_enc nil
        -> w#>tmp1 = 0
        -> w#>tmp2 = 0
        -> out_code (fst st) Q
        -> Q // (lnk i,w) -[p]-> st
        -> exists q, q < p /\ Q // (lnk k,w) -[q]-> st.
  Proof.
    intros H1 H2 H3 H4 H5 H6.
    apply subcode_sss_progress_inv with (4 := bic_POP_void _ _ _ _ _ H1 H2 H3 H4); auto.
    apply mm_sss_fun.
    revert H5; apply subcode_out_code; auto.
    apply Hc; auto.
    apply Hc; auto.
  Qed.
    
  Fact bic_POP_One_inv p i x j k w s st : 
           (i,POP x j k::nil) <sc P
        -> w#>(reg x) = stack_enc (One::s)
        -> w#>tmp1 = 0
        -> w#>tmp2 = 0
        -> out_code (fst st) Q
        -> Q // (lnk i,w) -[p]-> st
        -> exists q, q < p /\ Q // (lnk (1+i), w[(stack_enc s)/reg x]) -[q]-> st.
  Proof.
    intros H1 H2 H3 H4 H5 H6.
    apply subcode_sss_progress_inv with (4 := bic_POP_One _ _ _ _ _ H1 H2 H3 H4); auto.
    apply mm_sss_fun.
    revert H5; apply subcode_out_code; auto.
    apply Hc; auto.
    apply Hc; auto.
  Qed.
    
  Fact bic_POP_Zero_inv p i x j k w s st : 
           (i,POP x j k::nil) <sc P
        -> w#>(reg x) = stack_enc (Zero::s)
        -> w#>tmp1 = 0
        -> w#>tmp2 = 0
        -> out_code (fst st) Q
        -> Q // (lnk i,w) -[p]-> st
        -> exists q, q < p /\ Q // (lnk j, w[(stack_enc s)/reg x]) -[q]-> st.
  Proof.
    intros H1 H2 H3 H4 H5 H6.
    apply subcode_sss_progress_inv with (4 := bic_POP_Zero _ _ _ _ _ _ H1 H2 H3 H4); auto.
    apply mm_sss_fun.
    revert H5; apply subcode_out_code; auto.
    apply Hc; auto.
    apply Hc; auto.
  Qed.
  
  Lemma bsm_instr_compiler_complete p st1 w1 w3 :
           bsm_state_enc (snd st1) (snd w1)
        -> lnk (fst st1) = fst w1
        -> in_code (fst st1) P
        -> out_code (fst w3) Q
        -> Q // w1 -[p]-> w3
        -> exists q st2 w2, bsm_state_enc (snd st2) (snd w2)
                        /\ lnk (fst st2) = fst w2
                        /\ P /BSM/ st1 ->> st2
                        /\ Q // w2 -[q]-> w3
                        /\ q < p.
  Proof.
    revert st1 w1 w3.
    intros (i1,v1) (j1,w1) w3; unfold fst, snd; intros H1 H2 H3 H4 H5.
    destruct (in_code_subcode H3) as (ii & Hii).
    destruct (Hc _ _ Hii) as (H6 & H7).
    assert (out_code (fst w3) (lnk i1, comp i1 ii)) as G2.
    { revert H4; apply subcode_out_code; auto. }
    assert (in_code (lnk i1) (lnk i1, comp i1 ii)) as G3.
    { simpl; generalize (bsm_instr_compile_length_geq ii);
      rewrite bsm_instr_compile_length_eq; omega. }
    rewrite <- H2 in H5.
    destruct H1 as (F1 & F2 & F4).
    destruct ii as [ x j k | x [] ]; 
      generalize (@Hvr1 x) (@Hvr2 x); intros Hvx1 Hvx2;
      generalize (F4 x); intros F4';
      [ case_eq (v1#>x); [| intros [] lx ];  intros Hv1 | | ].
  
    (* POP void *)
      
    * apply bic_POP_void_inv with (1 := Hii) in H5; auto.
      2: rewrite F4'; f_equal; auto.
      destruct H5 as (q & Hq & H5).
      exists q, (k,v1), (lnk k, w1); repeat split; auto.
      bsm sss POP empty with x j k.
      bsm sss stop.

    (* POP One *)

    * apply bic_POP_One_inv with (s := lx) (1 := Hii) in H5; auto.
      2: rewrite F4'; f_equal; auto.
      destruct H5 as (q & Hq & H5).
      exists q, (1+i1,v1[lx/x]), (lnk (1+i1), w1[(stack_enc lx)/reg x]); repeat split; auto; rew vec.
      intros y.
      dest x y.
      assert (reg x <> reg y).
      { intros E; apply Hreg in E; subst; tauto. }
      rew vec.
      bsm sss POP 1 with x j k lx.
      bsm sss stop.
         
    (* POP Zero *)
         
    * apply bic_POP_Zero_inv with (s := lx) (1 := Hii) in H5; auto.
      2: rewrite F4'; f_equal; auto.
      destruct H5 as (q & Hq & H5).
      exists q, (j,v1[lx/x]), (lnk j, w1[(stack_enc lx)/reg x]); repeat split; auto; rew vec.
      intros y.
      dest x y.
      assert (reg x <> reg y).
      { intros E; apply Hreg in E; subst; tauto. }
      rew vec.
      bsm sss POP 0 with x j k lx.
      bsm sss stop.
         
    (* PUSH One *)
       
    * apply bic_PUSH_One_inv with (s := v1#>x) (1 := Hii) in H5; auto.
      destruct H5 as (q & Hq & H5).
      exists q, (1+i1,v1[(One::v1#>x)/x]), (lnk (1+i1),w1[(stack_enc (One::v1#>x))/reg x]);
        repeat split; auto; rew vec.
      intros y.
      dest x y.
      assert (reg x <> reg y); [ | rew vec ];
        intros E; apply Hreg in E; subst; tauto.
      bsm sss PUSH with x One.
      bsm sss stop.
       
    (* PUSH Zero *)
       
    * apply bic_PUSH_Zero_inv with (s := v1#>x) (1 := Hii) in H5; auto.
      destruct H5 as (q & Hq & H5).
      exists q, (1+i1,v1[(Zero::v1#>x)/x]), (lnk (1+i1),w1[(stack_enc (Zero::v1#>x))/reg x]);
        repeat split; auto; rew vec.
      intros y.
      dest x y.
      assert (reg x <> reg y); [ | rew vec ];
        intros E; apply Hreg in E; subst; tauto.
      bsm sss PUSH with x Zero.
      bsm sss stop.
  Qed.

  Theorem bsm_compiler_complete : forall st1 iv1 iv3,
           bsm_state_enc (snd st1) (snd iv1)
        -> lnk (fst st1) = fst iv1
        -> out_code (fst iv3) Q
        -> Q // iv1 ->> iv3
        -> exists st2 iv2, 
           bsm_state_enc (snd st2) (snd iv2)
        /\ lnk (fst st2) = fst iv2
        /\ out_code (fst st2) P
        /\ P /BSM/ st1 ->> st2
        /\ Q // iv2 ->> iv3.
  Proof.
    intros st1 iv1 iv3 H1 H2 H3 (p & H5).
    revert st1 iv1 iv3 H1 H2 H3 H5.
    induction p as [ p IHp ] using (well_founded_induction lt_wf).
    intros st1 iv1 iv3 H1 H2 H3' H5.
    destruct (in_out_code_dec (fst st1) P) as [ H3 | H3 ].
    * destruct (bsm_instr_compiler_complete _ H1 H2 H3 H3' H5)
        as (q & st2 & iv2 & G1 & G2 & G3 & G4 & G5).
      apply IHp with (1 := G5) (2 := G1) in G4; auto.
      destruct G4 as (st4 & iv4 & G4 & G7 & G8 & G9 & G10).
      exists st4, iv4; repeat (split; auto).
      apply sss_compute_trans with (1 := G3); auto.
    * exists st1, iv1.
      repeat (split; auto).
      bsm sss stop.
      revert H5; apply sss_steps_compute.
  Qed.
  
  Let bsm_enc_0 v : bsm_state_enc v (0 ## 0 ## vec_map stack_enc v).
  Proof. repeat split; auto; intros; unfold reg; simpl; rewrite vec_pos_map; auto. Qed.
  
  Theorem bsm_compiler_correct1 v : 
            (exists q w, P /BSM/ (fst P,v) ->> (q,w) /\ out_code q P) 
         -> exists w, Q // (1,0##0##vec_map stack_enc v) ->> (err,w) 
                   /\ w#>tmp1 = 0 /\ w#>tmp2 = 0.
  Proof.
    intros (q & w & H1 & H2).
    apply bsm_compiler_sound with (w1 :=0##0##vec_map stack_enc v) in H1; auto.
    destruct H1 as (w1 & H1 & H3); simpl in H3.
    rewrite bsm_linker_start, bsm_linker_out_err in H3; auto.
    exists w1; split; auto.
    split; apply H1.
  Qed.
  
  Theorem bsm_compiler_correct2 v j w1 :
            out_code j Q 
         -> Q // (1,0##0##vec_map stack_enc v) ->> (j,w1)
         -> (exists q w, P /BSM/ (fst P,v) ->> (q,w) /\ out_code q P).
  Proof. 
    intros H1 H2.
    apply bsm_compiler_complete with (st1 := (fst P,v)) in H2; auto.
    - destruct H2 as ((q & w) & iv2 & H0 & H2 & H3 & H4 & H5); auto.
      exists q, w; split; auto.
    - simpl; auto.
    - simpl; apply bsm_linker_start.
  Qed.
  
  Let bsm_end := mm_nullify tmp1 err (map (fun p => pos_nxt (pos_nxt p)) (pos_list m)) ++ DEC tmp1 0 :: nil.
  
  Let length_nullify : length (mm_nullify tmp1 err (map (fun p => pos_nxt (pos_nxt p)) (pos_list m))) = 2*m.
  Proof.
    rewrite mm_nullify_length; rew length.
    rewrite pos_list_length; auto.
  Qed.

  Let bsm_end_spec w : w#>tmp1 = 0 -> w#>tmp2 = 0 -> (err,bsm_end) // (err,w) -+> (0,vec_zero).
  Proof.
    intros H1 H2.
    unfold bsm_end.
    
    apply sss_compute_progress_trans with (2*m+err,vec_zero).
    apply subcode_sss_compute with (P := (err,mm_nullify tmp1 err (map (fun p => pos_nxt (pos_nxt p)) (pos_list m)))); auto.
    rewrite <- length_nullify; apply mm_nullify_compute; auto.
    intros p Hp.
    apply in_map_iff in Hp.
    destruct Hp as (x & H3 & H4); subst; discriminate.
    intros p Hp.
    apply in_map_iff in Hp.
    destruct Hp as (x & H3 & H4); subst; apply vec_zero_spec.
    intros p Hp.
    unfold n, tmp1, tmp2 in *; simpl in p.
    pos_inv p; auto.
    pos_inv p; auto.
    destruct Hp; apply in_map_iff; exists p; split; auto.
    apply pos_list_prop.
    
    apply subcode_sss_progress with (P := (2*m+err,DEC tmp1 0::nil)); auto.
    rewrite <- length_nullify, mm_nullify_length.
    mm sss DEC 0 with tmp1 0.
    apply subcode_refl.
    mm sss stop.
  Qed.
  
  Definition bsm_simulator := bsm_compiler ++ bsm_end.
  
  Let bsm_comp_sim : Q <sc (1,bsm_simulator).
  Proof.
    unfold bsm_simulator; auto.
  Qed.
  
  Let bsm_end_sim : (err,bsm_end) <sc (1,bsm_simulator).
  Proof.
    unfold err, bsm_simulator; subcode_tac; solve list eq.
    rewrite bsm_compiler_length.
    unfold snd; omega.
  Qed.
  
  Theorem bsm_simulator_correct v : (exists q w, P /BSM/ (fst P,v) ->> (q,w) /\ out_code q P) 
                                <-> (1,bsm_simulator) // (1,0##0##vec_map stack_enc v) ->> (0,vec_zero).
  Proof.
    split.
    * intros H1.
      apply bsm_compiler_correct1 in H1.
      destruct H1 as (w & H1 & H2 & H3).
      apply sss_compute_trans with (st2 := (err,w)).
      revert H1; apply subcode_sss_compute; auto.
      apply sss_progress_compute.
      generalize (bsm_end_spec _ H2 H3); apply subcode_sss_progress; auto.
    * intros H1.
      apply subcode_sss_compute_inv with (1 := bsm_comp_sim) in H1.
      2: (simpl; auto; rewrite bsm_compiler_length).
      destruct H1 as ((j,w) & H1 & H2 & H3).
      apply bsm_compiler_correct2 in H1; auto.
  Qed.
  
End compiler.
