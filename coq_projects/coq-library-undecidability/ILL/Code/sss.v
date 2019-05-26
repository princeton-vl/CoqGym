(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import List Arith Omega.

Require Import utils subcode.

Set Implicit Arguments.

Reserved Notation "i '//' r '-1>' s" (at level 70, no associativity).
Reserved Notation "P '//' r ':1>' s" (at level 70, no associativity).
Reserved Notation "P '//' r '-[' n ']->' s" (at level 70, no associativity).
Reserved Notation "P '//' r '-+>' s" (at level 70, no associativity).
Reserved Notation "P '//' r '->>' s" (at level 70, no associativity).
Reserved Notation "P '//' r '-]]' s" (at level 70, no associativity).
Reserved Notation "P '//' r '~~>' s" (at level 70, no associativity).
Reserved Notation "P '//' r ↓" (at level 70, no associativity).

Section Small_Step_Semantics.

  (** * Code
      A generic library to implement Small Step Semantics on programs described
      by lists of instructions that modify a state and a Program Counter (PC) 
     
      An important part of the library is devoted to show locality lemmas
      that related computation inside sub-programs to outer programs
      
      This is ESSENTIAL to be able to show properties compositionally,
      ie to derive properties of program from properties of sub-programs
   *)

  (** ** Syntax *)


  Variable (instr : Set) (data : Type).

  (* A state contain the PC (current instruction) and data *)
  
  Notation state := (nat * data)%type.
  
  Variable one_step : instr -> state -> state -> Prop.
  
  Notation "i // s -1> t" := (one_step i s t) (at level 70, no associativity).
  Notation "s ⟬ i ⦒  t" := (one_step i s t) (at level 70, no associativity).
 
  Hypothesis (sss_fun : forall i s t1 t2, i // s -1> t1 -> i // s -1> t2 -> t1 = t2).
  Hypothesis (sss_dec : forall i st1 st2, { i // st1 -1> st2 } + { ~ i // st1 -1> st2 }).
  
  (* A code is a contiguous list of instructions starting at some position *)
  
  Notation code := (nat * list instr)%type.
  
  (** ** Semantics *)
  
  (* This a one step computation *) 

  Definition sss_step P st1 st2 := exists k l i r d, P = (k,l++i::r)
                                                  /\ st1 = (k+length l,d)
                                                  /\ i // st1 -1> st2.
                                                        
  Notation "P // r :1> s" := (sss_step P r s)  (at level 70, no associativity).
  
  (* Functionality of one step computations *)

  Fact sss_step_fun P s t1 t2 : P // s :1> t1 -> P // s :1> t2 -> t1 = t2.
  Proof.
    intros (k1 & l1 & i1 & r1 & d1 & ? & ? & H1)
           (k2 & l2 & i2 & r2 & d2 & ? & ? & H2).
    subst.
    inversion H3.
    inversion H4.
    subst k2.
    apply list_app_inj in H5; try omega.
    destruct H5 as (? & H5); inversion H5.
    subst.
    revert H1 H2; apply sss_fun.
  Qed.
 
  (* A "more general/usable" constructor *)
  
  Fact in_sss_step k l i r st1 st2 : fst st1 = k+length l        
                               ->       i     // st1  -1>  st2 
                               -> (k,l++i::r) // st1  :1>  st2.
  Proof. destruct st1 as (j,d); simpl; intro; subst; exists k,l,i,r,d; auto. Qed.

  (* A destructor *)

  Fact sss_step_subcode_inv P ii st st' : 
        (fst st, ii::nil) <sc P -> P // st :1> st' -> ii // st -1> st'.
  Proof.
    intros H1 (k & l2 & jj & r2 & d1 & H3 & H4 & H5); subst P st.
    destruct H1 as (l1 & r1 & H1 & H2).
    simpl in H1, H2.
    apply list_app_inj in H1; try omega.
    destruct H1 as (? & H1); subst l2.
    inversion H1; subst jj r2; auto.
  Qed.

  Fact sss_step_supcode P Q st st' :
       P <sc Q -> in_code (fst st) P -> Q // st :1> st' -> P // st :1> st'.
  Proof.
    intros H1 H2 (k & l & ii & r & d & ? & ? & H3); subst.
    destruct P as (iP,cP). 
    destruct H1 as (ll & rr & H1 & H4).
    simpl in H2.
    symmetry in H1.
    apply list_app_cons_eq_inv in H1.
    destruct H1 as [ (m & G1 & G2) | (m & G1 & G2) ].
    2: apply f_equal with (f := @length _) in G1;
       exfalso; revert G1; rew length; intro; omega.
    apply list_app_cons_eq_inv in G2.
    destruct G2 as [ (p & G3 & G4) | (p & G3 & G4) ].
    subst; exfalso; revert H2; rew length; intro; omega.
    subst.
    apply in_sss_step; auto.
    revert H2; rew length; simpl; intro; omega.
  Qed.
  
  (* sss_step is decidable *)
  
  Fact sss_step_dec P st1 st2 : { P // st1 :1> st2 } + { ~ P // st1 :1> st2 }.
  Proof.
    destruct st1 as (j,d).
    destruct P as (k,ll).
    destruct (le_lt_dec k j) as [ H1 | H1 ].
    destruct (le_lt_dec (S j) (k+length ll)) as [ H2 | H2 ].
    destruct (@list_pick _ ll (j-k)) as (i & l & r & ? & ?).
    omega.
    assert (j = k+length l) by omega; subst.
    destruct (sss_dec i (k+length l,d) st2) as [ | C ].
    left; apply in_sss_step; auto.
    right; contradict C.
    destruct C as (k1 & l1 & i1 & r1 & d1 & ? & ? & ?).
    inversion H3; subst.
    inversion H; subst.
    apply list_app_inj in H8; try omega.
    destruct H8 as (? & H8); inversion H8; subst; auto.
    
    right; intros (k1 & l1 & i1 & r1 & d1 & ? & ? & ?).
    inversion H; subst.
    inversion H0; subst.
    rewrite app_length in H2; simpl in H2; omega.
    
    right; intros (k1 & l1 & i1 & r1 & d1 & ? & ? & ?).
    inversion H; subst.
    inversion H0; subst.
    omega.
  Qed.

  (* This is a n steps computation *)
  
  Inductive sss_steps (P : code) : nat -> state -> state -> Prop :=
    | in_sss_steps_0 : forall st,                  P // st   -[0]->    st
    | in_sss_steps_S : forall n st1 st2 st3,       P // st1   :1>      st2
                                              ->   P // st2  -[n]->    st3
                                              ->   P // st1  -[S n]->  st3
  where "P // r -[ n ]-> s" := (sss_steps P n r s).
  
  (* More usable constructors *)
  
  Fact sss_steps_0 P st1 st2 : st1 = st2 -> P // st1 -[0]-> st2.
  Proof. intros []; constructor. Qed.

  Fact sss_steps_1 P st1 st2 : P // st1 :1> st2 -> P // st1 -[1]-> st2.
  Proof.
    constructor 2 with st2; auto.
    constructor 1.
  Qed.
  
  Fact sss_steps_trans P n m st1 st2 st3 :
         P // st1 -[n]-> st2 -> P // st2 -[m]-> st3 -> P // st1 -[n+m]-> st3 .
  Proof.
    intros H; revert H st3.
    induction 1 as [ | ? ? st2 ]; simpl; intros; auto.
    constructor 2 with st2; auto.
  Qed.
  
  (* Inversion lemma *)
 
  Fact sss_steps_0_inv P st1 st2 : P // st1 -[0]-> st2 -> st1 = st2.
  Proof. inversion 1; auto. Qed.
  
  Fact sss_steps_S_inv P st1 st3 k : 
                        st1 <> st3 
      ->                P // st1 -[k]-> st3 
      -> exists k' st2, k = S k' 
                     /\ P // st1 :1> st2
                     /\ P // st2 -[k']-> st3.
  Proof.
    intros H.
    inversion 1; subst.
    destruct H; auto.
    exists n, st2; auto.
  Qed.

  Fact sss_steps_inv P k st1 st3 : 
          P // st1 -[k]-> st3 
       -> (k = 0 /\ st1 = st3)
        + { k' | exists st2, k = S k' 
                       /\ P // st1 :1> st2
                       /\ P // st2 -[k']-> st3 }%type.
  Proof.
    intros H.
    destruct k as [ | k ]; [ left | right ].
    apply sss_steps_0_inv in H; auto.
    exists k.
    inversion H; subst.
    exists st2; auto.
  Qed.
  
  Fact sss_steps_S_inv' P st1 st3 k :  
                        P // st1 -[S k]-> st3 
      -> exists st2,    P // st1 :1> st2
                     /\ P // st2 -[k]-> st3.
  Proof.
    intros H.
    inversion H; subst.
    exists st2; auto.
  Qed.
 
  Fact sss_steps_fun P k s t1 t2 :
         P // s -[k]-> t1 
      -> P // s -[k]-> t2 
      -> t1 = t2.
  Proof.
    intros H; revert H t2; induction 1 as [ | ? ? st2 ? H1 H2 IH2 ]; simpl; intros t2 Ht2; auto.
    inversion Ht2; auto.
    inversion Ht2; subst.
    generalize (sss_step_fun H1 H0); intro; subst.
    apply IH2 in H3; auto.
  Qed.
   
  Fact sss_steps_plus_inv P n m st1 st3 : 
         P // st1 -[n+m]-> st3 
      -> exists st2, P // st1 -[n]-> st2 
                  /\ P // st2 -[m]-> st3.
  Proof.
    revert st1 st3; induction n as [ | n IHn ]; intros s t.
    exists s; split; auto; constructor.
    inversion 1; subst.
    apply IHn in H2; destruct H2 as (st & ? & ?).
    exists st; split; auto.
    constructor 2 with st2; auto.
  Qed.
  
  Definition sss_progress P st1 st2 := exists k, 0 < k /\ P // st1 -[k]-> st2.
  Definition sss_compute  P st1 st2 := exists k, P // st1 -[k]-> st2.
  
  Notation "P // r -+> s" := (sss_progress P r s).
  Notation "P // r ->> s" := (sss_compute P r s).
  
  Fact sss_progress_compute P st1 st2 : P // st1 -+> st2 -> P // st1 ->> st2.
  Proof. intros (k & _ & ?); exists k; auto. Qed. 
  
  Fact sss_compute_trans P st1 st2 st3 : P // st1 ->> st2 -> P // st2 ->> st3 -> P // st1 ->> st3.
  Proof. intros (i & H1) (j & H2); exists (i+j); revert H1 H2; apply sss_steps_trans. Qed.
  
  Fact sss_progress_compute_trans P st1 st2 st3 : P // st1 -+> st2 -> P // st2 ->> st3 -> P // st1 -+> st3.
  Proof. intros (i & ? & H1) (j & H2); exists (i+j); split; try omega; revert H1 H2; apply sss_steps_trans. Qed.
  
  Fact sss_compute_progress_trans P st1 st2 st3 : P // st1 ->> st2 -> P // st2 -+> st3 -> P // st1 -+> st3.
  Proof. intros (i & H1) (j & ? & H2); exists (i+j); split; try omega; revert H1 H2; apply sss_steps_trans. Qed.
  
  Fact sss_progress_trans P st1 st2 st3 : P // st1 -+> st2 -> P // st2 -+> st3 -> P // st1 -+> st3.
  Proof. intro; apply sss_compute_progress_trans, sss_progress_compute; trivial. Qed.

  (* Computations must start inside code *) 
  
  Fact sss_step_in_code P st1 st2 : P // st1 :1> st2 -> in_code (fst st1) P.
  Proof.
    revert P st1 st2; intros (n,c) (i,d) st2 (q & l & ii & r & d1 & H1 & H2 & _).
    inversion H1; subst.
    inversion H2; subst.
    simpl; rew length; omega.
  Qed.

  Fact sss_steps_compute P n st1 st2 : P // st1 -[n]-> st2 -> P // st1 ->> st2.
  Proof. exists n; trivial. Qed.
  
  (** We propose a library of locality lemmas that link computations
      in subcode to computations in the code *)

  (** ** Compisitional Reasoning over Subcode *)

  (* First inclusions lemmas *)

  Fact subcode_sss_step P Q st1 st2: P <sc Q -> P // st1 :1> st2 -> Q // st1 :1> st2.
  Proof.
    destruct P as (n1,c1).
    destruct Q as (n2,c2).
    simpl.
    intros (l & r & H1 & H2) H3.
    destruct H3 as (q & ll & i & rr & d1 & H3 & H4 & H5).
    inversion H3; subst.
    exists n2, (l++ll), i, (rr++r), d1; repeat split; auto.
    f_equal; solve list eq.
    f_equal; rew length; omega.
  Qed.

  Fact subcode_sss_steps P Q k st1 st2: P <sc Q -> P // st1 -[k]-> st2 -> Q // st1 -[k]-> st2.
  Proof.
    induction 2 as [ | k st1 st2 st3 H3 H4 IH4 ].
    constructor.
    constructor 2 with st2; auto.
    revert H3; apply subcode_sss_step; auto.
  Qed.
  
  Fact subcode_sss_progress P Q st1 st2: P <sc Q -> P // st1 -+> st2 -> Q // st1 -+> st2.
  Proof.
    intros ? (k & ? & Hk); exists k; split; auto; revert Hk; apply subcode_sss_steps; auto.
  Qed.

  Fact subcode_sss_compute P Q st1 st2: P <sc Q -> P // st1 ->> st2 -> Q // st1 ->> st2.
  Proof.
    intros ? (k & Hk); exists k; revert Hk; apply subcode_sss_steps; auto.
  Qed.

  Fact subcode_sss_compute_trans P Q st1 st2 st3 :
       P <sc Q -> P // st1 ->> st2 -> Q // st2 ->> st3 -> Q // st1 ->> st3.
  Proof.
    intros ? H.
    apply sss_compute_trans.
    revert H; apply subcode_sss_compute; auto.
  Qed.
  
  Fact subcode_sss_compute_linstr k li P st1 st2 st :
            (fst st1,li) // st1 -[k]-> st2
         -> (fst st1,li) <sc P
         -> P // st2 ->> st
         -> P // st1 ->> st.
  Proof.
    intros H1 H2.
    apply subcode_sss_compute_trans with (1 := H2).
    exists k; auto.
  Qed.
  
  Fact subcode_sss_compute_instr P i st1 st2 st3 : 
            i // st1 -1> st2
        ->  (fst st1,i::nil) <sc P
        ->  P // st2 ->> st3
        ->  P // st1 ->> st3.
  Proof.
    intro H; apply subcode_sss_compute_linstr with (k := 1).
    apply sss_steps_1, in_sss_step with (l := nil); auto.
  Qed.
  
  (* Then are reverse inclusion lemmas *)

  Fact subcode_sss_step_inv P Q st1 st2 : 
         P <sc Q 
      -> in_code (fst st1) P
      -> Q // st1 :1> st2
      -> P // st1 :1> st2.
  Proof.
    revert P Q st1 st2; intros (nP,cP) (nQ,cQ) (i,d) st; simpl.
    intros (l & r & H1 & H2) H3 (q & ll & ii & rr & d1 & H4 & H5 & H6).
    inversion H4; subst.
    inversion H5; subst.
    clear H4 H5.
    apply list_app_cons_eq_inv in H7. 
    destruct H7 as [ (m & Hm1 & Hm2) | (m & Hm1 & Hm2) ].
    apply list_app_cons_eq_inv in Hm2.
    destruct Hm2 as [ (p & Hp1 & Hp2) | (p & Hp1 & Hp2) ].

    apply f_equal with (f := @length _) in Hm1.
    apply f_equal with (f := @length _) in Hp1.
    revert Hm1 Hp1; rew length; intros; omega.

    subst cP; apply in_sss_step; auto.
    simpl; subst; rew length; omega.
    
    apply f_equal with (f := @length _) in Hm1.
    apply f_equal with (f := @length _) in Hm2.
    revert Hm1 Hm2; rew length; intros; omega.
  Qed.

  Definition sss_output P st st' := P // st ->> st' /\ out_code (fst st') P.

  Notation "P // x ~~> y" := (sss_output P x y).

  Definition sss_terminates P st := exists st', P // st ~~> st'.

  Notation "P // x ↓" := (sss_terminates P x).

  Fact subcode_sss_terminates_instr P i st1 st2 : 
            i // st1 -1> st2
        ->  (fst st1,i::nil) <sc P
        ->  P // st2 ↓
        ->  P // st1 ↓.
  Proof.
    intros H1 H2 (st3 & H3 & H4).
    exists st3; split; auto.
    revert H1 H2 H3; apply subcode_sss_compute_instr.
  Qed.

  (* No computation is possible *)
  
  Definition sss_stall ii st := forall st', ~ ii // st -1> st'.
  Definition sss_step_stall P st := forall st', ~ P // st :1> st'.

  Fact sss_steps_stall_inv P p s1 s2 : sss_step_stall P s1 -> P // s1 -[p]-> s2 -> p = 0 /\ s1 = s2.
  Proof.
    intros H; induction 1 as [ | p st1 st2 st3 H1 ]; auto.
    apply H in H1; destruct H1.
  Qed.

  Fact sss_steps_stall_fun P p q s1 s2 :
         sss_step_stall P s2
      -> P // s1 -[p]-> s2 
      -> P // s1 -[q]-> s2
      -> p = q.
  Proof.
    intros H1 H2; revert H2 q.
    induction 1 as [ s1 | p s1 s2 s3 H2 H3 IH3 ];
      intros q H5.
    apply sss_steps_stall_inv, proj1 in H5; auto.
    destruct q.
    apply sss_steps_0_inv in H5; subst.
    apply H1 in H2; destruct H2.
    specialize (IH3 H1).
    apply sss_steps_S_inv' in H5.
    destruct H5 as (st2' & H5 & H6).
    generalize (sss_step_fun H2 H5).
    intros; subst st2'.
    apply IH3 in H6; subst; auto.
  Qed. 

  Definition sss_compute_max P s1 s2 := (P // s1 ->> s2 /\ sss_step_stall P s2).

  Notation " P // s1 -]] s2 " := (sss_compute_max P s1 s2).
  
  (* No computation outside the code *)

  Fact sss_out_step_stall P st : out_code (fst st) P -> sss_step_stall P st.
  Proof.
    revert P st; intros (n,code) (i,st).
    intros H1 st' (k & l & ii & r & d1 & H2 & H3 & H4).
    inversion H2; inversion H3; subst.
    simpl in H1.
    revert H1; rew length; intros []; omega.
  Qed.

  Fact sss_stall_step_stall ii P st :
          (fst st,ii::nil) <sc P
       -> sss_stall ii st
       -> sss_step_stall P st.
  Proof.
    intros H1 H2 st' H.
    apply sss_step_subcode_inv  with (1 := H1) in H.
    revert H; apply H2.
  Qed.
  
  Fact sss_stall_step_0 ii P q st st' :
          (fst st,ii::nil) <sc P
       -> sss_stall ii st
       -> P // st -[q]-> st' -> q = 0 /\ st = st'.
  Proof.
    intros H1 H2.
    generalize (sss_stall_step_stall H1 H2).
    intros H3 H4.
    apply sss_steps_inv in H4.
    destruct H4 as [ | (k & st2 & _ & H5 & _) ]; auto.
    contradict H5; apply H3.
  Qed.

  Fact sss_step_stall_inv P st :
          sss_step_stall P st
       -> { ii | (fst st,ii::nil) <sc P /\ sss_stall ii st }
        + { out_code (fst st) P }.
  Proof.
    intros H.
    destruct (in_out_code_dec (fst st) P) as [ H1 | H1 ].
    2: tauto.
    destruct P as (iP,cP).
    destruct st as (j,d).
    simpl in H1.
    destruct (@list_pick _ cP (j-iP)) as (ii & l & r & H2 & H3).
    omega.
    left; exists ii; simpl; split.
    exists l, r; split; auto; omega.
    intros st' H4.
    apply (H st'). 
    subst; apply in_sss_step; auto.
    simpl; omega.
  Qed.

  Fact sss_steps_stall k P st st' : 
         out_code (fst st) P
      -> P // st -[k]-> st' 
      -> k = 0 /\ st = st'.
  Proof.
    destruct P; simpl.
    intros H1 H2.
    apply sss_steps_inv in H2.
    destruct H2 as [ (? & ?) | (m & st2 & ? & H2 & _) ]; auto.
    apply sss_out_step_stall in H2; try red; tauto.
  Qed.
  
  (** This is a critical lemma about the locality of computations
  
      If P is subcode of Q and a computation in Q starts in P and ends outside of P,
      then it is decomposed in a first computation in P ending outside of P
      and a second computation in Q 
      
    *)
  
  Lemma subcode_sss_steps_inv P Q k st1 st3 :
       P <sc Q
    -> in_code  (fst st1) P
    -> out_code (fst st3) P
    -> Q // st1 -[k]-> st3
    -> exists k1 k2 st2, 
          P // st1 -[k1]-> st2
       /\ Q // st2 -[k2]-> st3
       /\ k = k1+k2 
       /\ out_code (fst st2) P.
  Proof.
    intros H1 H2 H3 H4; revert H4 H2 H3.
    induction 1 as [ st1 | k st1 st2 st3 H4 H5 IH5 ]; intros H2 H3.
    
    exists 0, 0, st1; repeat split; auto; constructor.
    
    apply subcode_sss_step_inv with (1 := H1) in H4; auto.
    destruct (in_out_code_dec (fst st2) P) as [ H6 | H6 ].
    
    destruct (IH5 H6 H3) as (k1 & k2 & st & ? & ? & ? & ?).
    exists (S k1), k2, st; repeat split; auto.
    constructor 2 with (1 := H4); auto.
    omega.
    
    exists 1, k, st2; repeat split; auto.
    apply sss_steps_1; auto.
  Qed.

  Lemma subcode_sss_compute_inv P Q st1 st3 :
       P <sc Q
    -> out_code (fst st3) P
    -> Q // st1 ->> st3
    -> exists st2, 
          P // st1 ->> st2
       /\ Q // st2 ->> st3
       /\ out_code (fst st2) P.
  Proof.
    intros H1 H3 (k & Hk).
    destruct (in_out_code_dec (fst st1) P) as [ H2 | H2 ].
    + apply subcode_sss_steps_inv with (1 := H1) in Hk; auto.
      destruct Hk as (k1 & k2 & st2 & H4 & H5 & H6 & H7).
      exists st2; repeat split; auto; red; firstorder.
    + exists st1; repeat split; auto.
      * exists 0; constructor.
      * red; firstorder.
  Qed.

  (* Inversion lemma *)

  Fact subcode_sss_step_inv_1 P i st1 st2 : (fst st1,i::nil) <sc P -> P // st1 :1> st2 -> i // st1 -1> st2.
  Proof.
    revert P st1; intros (j,cj) (n,d) H1 H2.
    apply subcode_sss_step_inv with (1 := H1) in H2.
    2: simpl; omega.
    destruct H2 as (q & l & ii & r & d1 & H2 & H3 & H4).
    inversion H3; subst n d1; auto.
    eq goal H4; f_equal.
    inversion H2.
    destruct l as [ | ? [ | ] ]; try discriminate.
    inversion H5; subst; auto.
  Qed.

  (* Starting a computation in subcode ending outside of it
     can be cut in half *)

  Fact subcode_sss_subcode_inv P Q p k st1 st2 st3 :
           out_code (fst st3) P 
        -> P <sc Q
        -> P // st1 -[p]-> st2
        -> Q // st1 -[k]-> st3
        -> exists q, k = p+q /\ Q // st2 -[q]-> st3.
  Proof.
    revert P Q st3; intros P (j,cj) (n,d) H1 H2 H3.
    simpl in H1.
    revert k.
    induction H3 as [ st | p st1 st2 st3 H4 H5 IH5 ];
      intros k Hk.
    exists k; auto.
    apply sss_steps_inv in Hk.
    destruct Hk as [ (? & Hk) | (m & st4 & ? & Hk & H3) ].
    1: subst st1; apply sss_step_in_code in H4; simpl in H4; omega.
    apply subcode_sss_step with (1 := H2) in H4.
    rewrite (sss_step_fun Hk H4) in H3.
    apply IH5 in H3; auto.
    destruct H3 as (q & ? & H3).
    exists q; split; auto; omega.
  Qed.

  Fact subcode_sss_terminates_inv P Q st st1 :
           Q // st ↓
        -> P <sc Q
        -> P // st ~~> st1
        -> Q // st1 ↓.
  Proof.
    intros (st3 & (k & H1) & H2) H3 ((p & H4) & H5).
    destruct subcode_sss_subcode_inv with (2 := H3) (3 := H4) (4 := H1)
      as (q & _ & H6).
    1: revert H2; apply subcode_out_code; auto.
    exists st3; split; auto; exists q; auto.
  Qed.

  Fact subcode_sss_progress_inv P Q p st1 st2 st3 :
           out_code (fst st3) P 
        -> P <sc Q
        -> P // st1 -+> st2
        -> Q // st1 -[p]-> st3
        -> exists q, q < p /\ Q // st2 -[q]-> st3.
  Proof.
    intros H1 H2 (k & ? & H3) H4.
    apply subcode_sss_subcode_inv with (3 := H3) in H4; auto.
    destruct H4 as (q & ? & ?); exists q; split; auto; omega.
  Qed.

  Section sss_terminates_ind.

    Variable (P : code) (R : state -> Prop).

    Hypothesis (HR0 : forall st, out_code (fst st) P -> R st)
               (HR1 : forall st1, (forall Q st2, Q <sc P -> Q // st1 -+> st2 -> P // st2 ↓ -> R st2) -> R st1).

    Theorem sss_terminates_ind st : P // st ↓ -> R st.
    Proof.
      intros (st2 & (k & H1) & H2); revert st st2 H1 H2.
      induction k as [ k IH ] using (well_founded_induction_type lt_wf).
      intros st1 st2 H1 H2.
      destruct k as [ | k ].
      + apply sss_steps_0_inv in H1.
        subst; apply HR0; auto.
      + apply HR1.
        intros Q st2' HQ H5 (st3 & H6 & H7).
        apply subcode_sss_progress_inv with (3 := H5) in H1; auto.
        destruct H1 as (q & G1 & G2).
        apply IH with (2 := G2); auto.
        revert H2; apply subcode_out_code; auto.
    Qed.

  End sss_terminates_ind. 
 
  Section sss_compute_max_ind.

    Variable (P : code) (R : state -> state -> Prop).

    Hypothesis (HQ0 : forall st, sss_step_stall P st -> R st st)
               (HQ1 : forall st1 st3, (forall Q st2, Q <sc P -> Q // st1 -+> st2 -> P // st2 -]] st3 -> R st2 st3) -> R st1 st3).

    Theorem sss_compute_max_ind st1 st3 : P // st1 -]] st3 -> R st1 st3.
    Proof.
      intros ((k & H1) & H2); revert st1 H1.
      induction k as [ k IH ] using (well_founded_induction_type lt_wf).
      intros st1 H1.
      destruct k as [ | k ].
      apply sss_steps_0_inv in H1.
      subst; apply HQ0; auto.
      apply HQ1.
      intros Q st2' HQ H5 ((q & H6) & _).
      apply subcode_sss_progress with (1 := HQ) in H5.
      destruct H5 as (l & Hl & H5).
      generalize (sss_steps_trans H5 H6); intro H7.
      generalize (sss_steps_stall_fun H2 H1 H7); intros H8.
      apply IH with q; auto; omega.
    Qed.

  End sss_compute_max_ind. 
 
  Fact sss_compute_inv P st1 st2 st3 :
             out_code (fst st3) P
          -> P // st1 ->> st2
          -> P // st1 ->> st3
          -> P // st2 ->> st3.
  Proof.
    intros H2 (p & H3) (k & H4).
    apply subcode_sss_subcode_inv with (3 := H3) in H4; auto.
    destruct H4 as (q & _ & ?); exists q; auto.
    apply subcode_refl.
  Qed.

  Fact sss_compute_step_out_inv P k st1 st2 st3 :
           st1 <> st2
        -> out_code (fst st3) P
        -> P // st1 ->> st2
        -> P // st1 -[k]-> st3
        -> exists q, q < k /\ P // st2 -[q]-> st3.
  Proof.
    intros H1 H2 (p & H3) H4.
    apply subcode_sss_subcode_inv with (3 := H3) in H4; auto.
    destruct H4 as (q & H4 & H5).
    exists q; split; auto.
    destruct p.   
    apply sss_steps_0_inv in H3.
    destruct H1; auto.
    omega.
    apply subcode_refl.
  Qed.
  
  Fact subcode_sss_subcode_compute_inv P Q k st1 st2 st3 :
           in_code (fst st1) P
        -> out_code (fst st2) P
        -> out_code (fst st3) P 
        -> P <sc Q
        -> P // st1 ->> st2
        -> Q // st1 -[k]-> st3
        -> exists q, q < k /\ Q // st2 -[q]-> st3.
  Proof.
    intros H H0 H1 H2 (p & H3) H4.
    apply subcode_sss_subcode_inv with (2 := H2) (3 := H3) in H4; auto.
    destruct H4 as (q & Hq & H4).
    exists q; split; auto.
    destruct p; try omega.
    apply sss_steps_0_inv in H3; subst st2.
    red in H, H0; omega.
  Qed.

  Fact subcode_sss_steps_inv_1 P i k st1 st2 st3 :
        st1 <> st3
     -> i // st1 -1> st2
     -> (fst st1,i::nil) <sc P
     -> P // st1 -[k]-> st3
     -> exists k', k = S k' /\ P // st2 -[k']-> st3.
  Proof.
    intros H1 H2 H3 H4.
    apply sss_steps_inv in H4.
    destruct H4 as [ (_ & H4) | (k' & st & ? & H4 & ?) ].
    contradict H1; auto.
    exists k'; split; auto.
    apply subcode_sss_step_inv_1 with (1 := H3) in H4.
    rewrite (sss_fun H2 H4); auto.
  Qed.
  
  Fact subcode_sss_steps_stop P i k st1 st2 : 
            (forall st, ~ i // st1 -1> st)
        ->  (fst st1,i::nil) <sc P
        ->  P // st1 -[k]-> st2 -> k = 0 /\ st1 = st2.
  Proof.
    intros H1 H2 H3.
    apply sss_steps_inv in H3.
    destruct H3 as [ | (k' & st & ? & H3 & H4) ]; auto; exfalso.
    apply (H1 st), subcode_sss_step_inv_1 with (1 := H2); auto.
  Qed.
  
  Fact sss_steps_stop P k st1 st2 :
             out_code (fst st1) P
          -> P // st1 -[k]-> st2
          -> st1 = st2.
  Proof.
    intros H1 H2.
    apply sss_steps_inv in H2.
    destruct H2 as [ [ _ ? ] | (k' & st3 & H2 & H3 & H4) ]; auto.
    destruct (sss_out_step_stall H1 H3).
  Qed.

  Fact sss_compute_stop P st1 st2 :
             out_code (fst st1) P
          -> P // st1 ->> st2
          -> st1 = st2.
  Proof.
    intros H1 (k & H2); revert H2; apply sss_steps_stop; auto.
  Qed.
  
  Fact sss_compute_fun P st1 st2 st3 :
             out_code (fst st2) P
          -> out_code (fst st3) P 
          -> P // st1 ->> st2
          -> P // st1 ->> st3 
          -> st2 = st3.
  Proof.
    intros H1 H2 H3 H4.
    destruct (in_out_code_dec (fst st1) P) as [ H5 | H5 ].
    destruct H4 as (k & H4).
    apply subcode_sss_subcode_compute_inv with (5 := H3) in H4; auto.
    destruct H4 as (q & _ & H4).
    apply sss_steps_stop in H4; auto.
    apply subcode_refl.
    apply sss_compute_stop in H3; auto.
    apply sss_compute_stop in H4; auto.
    subst; auto.
  Qed.

  Fact sss_output_fun P st st1 st2 : P // st ~~> st1 -> P // st ~~> st2 -> st1 = st2.
  Proof.
    intros (H1 & H2) (H3 & H4); revert H2 H4 H1 H3; apply sss_compute_fun.
  Qed.

  Fact subcode_sss_terminates P Q st : P <sc Q -> Q // st ↓ -> P // st ↓.
  Proof.
    intros H (st' & H1 & H2).
    apply subcode_sss_compute_inv with (1 := H) in H1; auto.
    + destruct H1 as (st2 & H1 & H3 & H4).
      exists st2; split; auto.
    + revert H2; apply subcode_out_code; auto.
  Qed.

  Section sss_loop.

    (* P contains a loop that modifies the data (in a way computable by f)
       when condition C1 is satisfied and otherwise stops somewhere outside
       of P when condition C2 is satisfied.

       Then P stops iff exists n, C2 (iter f x n) *)

    Variable (P : code) (pre : data -> Prop) (spec : data -> data -> Prop)
             (f : data -> data) (Hf : forall x, x <> f x)
             (C1 C2 : data -> Prop) (HC : forall x, pre x -> { C1 x } + { C2 x }) 
             (i : nat) (p : nat) (Hp : out_code p P)
             (HP1 : forall x, pre x -> C1 x -> P // (i,x) ->> (i,f x) /\ pre (f x))
             (HP2 : forall x, pre x -> C2 x -> exists y, P // (i,x) ->> (p,y) /\ spec x y).

    Theorem sss_loop_sound x : pre x 
                            -> (exists n, C2 (iter f x n)) 
                            -> exists n y, P // (i,x) ->> (p,y) /\ spec (iter f x n) y.
    Proof.
      intros H (n & Hn); revert x H Hn.
      induction n as [ | n IHn ]; intros x Hx Hn.
      simpl; exists 0; apply HP2; auto.
      destruct (HC Hx) as [ H | H ]. 
      apply IHn in Hn.
      destruct Hn as (m & y & H1 & H2).
      exists (S m), y; split; auto.
      generalize H1; apply sss_compute_trans.
      apply HP1; auto.
      apply HP1; auto.
      destruct (HP2 Hx) as (y & H1 & H2); auto.
      exists 0, y; auto.
    Qed.

    Theorem sss_loop_complete x y q : pre x 
                                   -> out_code q P 
                                   -> P // (i,x) ->> (q,y) 
                                   -> p = q /\ exists n, C2 (iter f x n) /\ spec (iter f x n) y.
    Proof.
      intros Hx Hq (k & Hk); revert x Hx y q Hq Hk.
      induction k as [ k IHk ] using (well_founded_induction lt_wf); intros x Hx y q Hq Hk.
      destruct (HC Hx) as [ H | H ].
      * apply HP1 in H; auto; destruct H as [ H1 H2 ].
        destruct (@sss_compute_step_out_inv P k (i,x) (i,f x) (q,y))
          as (k' & H3 & H4); auto.
        { inversion 1 as [ H3 ]; revert H3; apply Hf. } 
        destruct IHk with (2 := H2) (4 := H4) as (E & n & Hn); auto.
        split; auto; exists (S n); auto.
      * destruct HP2 with (2 := H) as (z & Hz & Hy); auto.
        apply ex_intro with (x := k) in Hk.
        generalize (@sss_compute_fun _ _ (p,z) (q,y) Hp Hq Hz Hk).
        inversion 1; subst; auto.
        split; auto.
        exists 0; simpl; auto.
    Qed.

  End sss_loop.

End Small_Step_Semantics.

(*
Notation " P '//' r ':1>' s " := (sss_step _ P r s)  (at level 70, no associativity).
Notation " P '//' r '-[' n ']->' s " := (sss_steps _ P n r s) (at level 70, no associativity).
Notation " P '//' r '->>' s " := (sss_compute _ P r s) (at level 70, no associativity).
*)


