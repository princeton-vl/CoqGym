(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

(** * Minsky machines to FRACTRAN programs *)
(** ** Removal of self-loops in MMs *)

Require Import List Arith Omega.

Require Import utils pos vec. 
Require Import subcode sss mm_defs.

Set Implicit Arguments.

Tactic Notation "rew" "length" := autorewrite with length_db.

Local Notation "e #> x" := (vec_pos e x).
Local Notation "e [ v / x ]" := (vec_change e x v).

Local Notation "I // s -1> t" := (mm_sss I s t).
Local Notation "P // s -[ k ]-> t" := (sss_steps (@mm_sss _) P k s t).
Local Notation "P // s -+> t" := (sss_progress (@mm_sss _) P s t).
Local Notation "P // s ->> t" := (sss_compute (@mm_sss _) P s t).
Local Notation "P // s '~~>' t" := (sss_output (@mm_sss _) P s t).
Local Notation "P // s ↓" := (sss_terminates (@mm_sss _) P s). 

Section self_loops.

  Variables (n : nat) (P : list (mm_instr n)).

  Lemma mm_self_loop_no_term_1 i x s v : 
              (i,DEC x i::nil) <sc (1,P) 
           -> s = (i,v)
           -> v#>x = 0  
           -> ~ (1,P) // s ↓.
  Proof.
    intros H1 H2 H3 (s0 & H4).
    revert i x v H1 H2 H3.
    pattern s; revert H4; apply mm_term_ind.
    + intros Hs0 i x v H1 H2 H3.
      subst s0.
      revert Hs0; apply in_out_code.
      apply subcode_in_code with (1 := H1).
      simpl; omega.
    + intros i ρ v j w H1 H2 H3 IH3 k x p G1 G2 G3.
      inversion G2; subst p k.
      generalize (subcode_cons_inj _ _ _ _ H1 G1); intros; subst.
      apply mm_sss_DEC0_inv in H2; auto.
      destruct H2; subst j w.
      apply (IH3 _ _ _ G1 eq_refl); auto.
  Qed.

  Lemma mm_self_loop_no_term_2 i x s v : 
              (i,DEC x (1+i)::DEC x i::nil) <sc (1,P) 
           -> s = (i,v) \/ s = (1+i,v)
           -> v#>x = 0  
           -> ~ (1,P) // s ↓.
  Proof.
    intros H1 H2 H3 (s0 & H4).
    revert v H2 H3.
    pattern s; revert H4; apply mm_term_ind.
    + intros Hs0 v H2 H3.
      destruct H2; subst s0; revert Hs0; apply in_out_code;
        apply subcode_in_code with (1 := H1); simpl; omega.
    + apply subcode_cons_invert_left in H1.
      destruct H1 as [ G0 G1 ].
      intros l ρ v j w H1 H2 H3 IH3 r G2 G3.
      destruct G2 as [ G2 | G2 ]; inversion G2; subst l v.
      * generalize (subcode_cons_inj _ _ _ _ H1 G0); intros; subst.
        apply mm_sss_DEC0_inv in H2; auto.
        destruct H2; subst j w.
        revert G3; apply IH3; auto.
      * generalize (subcode_cons_inj _ _ _ _ H1 G1); intros; subst.
        apply mm_sss_DEC0_inv in H2; auto.
        destruct H2; subst j w.
        revert G3; apply IH3; auto.
  Qed.

End self_loops.

Section no_self_loops.

  Variables (n : nat).

  Definition mm_no_self_loops (Q : nat * list (mm_instr n)) := forall i x, ~ (i,DEC x i::nil) <sc Q.

  Implicit Types (P Q : list (mm_instr n)).

  Fact mm_no_self_loops_app i P Q : mm_no_self_loops (i,P) 
                                 -> mm_no_self_loops (length P +i,Q)
                                 -> mm_no_self_loops (i,P++Q).
  Proof.
    intros H1 H2 j x H.
    apply subcode_app_invert_right in H.
    destruct H as [ H | H ]; revert H.
    + apply H1.
    + apply H2.
  Qed.

End no_self_loops.

Section remove_self_loops.

  (** To safely remove self loops from (1,P) 
        1/ we map them to 2+lP 
        2/ we map outside jumps to 0
        3/ we append to P to 3 following instructions
             1+lP: DEC nv 0; DEC nv 3+lP; DEC nv 2+lP 

           where nv is a new and unused variable
    *)

  Variables (n : nat).

  Implicit Types (P Q : list (mm_instr n)).

  Let f k i (ρ : mm_instr n) := 
    match ρ with
      | INC x   => INC (pos_nxt x)
      | DEC x j => DEC (pos_nxt x) (if eq_nat_dec i j     then 1+k 
                                    else if le_lt_dec k j then 0
                                                          else j)
    end.

  Let Fixpoint g k i P := 
    match P with
      | nil  => nil
      | ρ::P => f k i ρ :: g k (S i) P
    end.

  Let g_app k i P Q : g k i (P++Q) = g k i P ++ g k (length P + i) Q.
  Proof.
    revert i; induction P as [ | ? P IHP ]; intros i; simpl; f_equal; auto.
    rewrite IHP; do 2 f_equal; omega.
  Qed.

  Let g_app_inv k i P l r : g k i P = l ++ r -> exists L R, P = L++R /\ l = g k i L /\ r = g k (length l+i) R.
  Proof.
    revert i l r.
    induction P as [ | ρ P IHP ]; intros i l r; simpl.
    + intros H; symmetry in H; exists nil, nil; simpl.
      apply app_eq_nil in H; tauto.
    + destruct l as [ | y l ]; simpl.
      * exists nil, (ρ::P); simpl in *; auto.
      * intros H; injection H; clear H; intros H1 H2.
        destruct IHP with (1 := H1) as (L & R & G1 & G2 & G3); subst.
        exists (ρ::L), R; simpl; repeat (split; auto).
        f_equal; omega.
  Qed.
 
  Let length_g l i P : length (g l i P) = length P.
  Proof. revert i; induction P; simpl; auto. Qed. 

  Let g_subcode k i P j ρ : (j,ρ::nil) <sc (i,P) -> (j, f k j ρ::nil) <sc (i,g k i P).
  Proof.
    intros (l & r & H1 & H2); subst P.
    rewrite g_app; simpl.
    exists (g k i l), (g k (S (length l+i)) r); split.
    + do 3 f_equal; omega.
    + rewrite length_g; auto.
  Qed.

  Let subcode_g k i P j ρ : (j,ρ::nil) <sc (i,g k i P) -> exists ρ', (j,ρ'::nil) <sc (i,P) /\ ρ = f k j ρ'.
  Proof.
    intros (l & r & H1 & H2).
    apply g_app_inv in H1.
    destruct H1 as (L & [ | ρ' R ] & H1 & H3 & H4); try discriminate.
    simpl in H4; inversion H4.
    exists ρ'; split; auto.
    + exists L, R; simpl; split; auto.
      rewrite H3, length_g in H2; auto.
    + f_equal; omega.
  Qed.

  Let g_loops k i P : 1 <= i -> i+length P <= k -> mm_no_self_loops (i,g k i P).
  Proof.
    intros H0 H1 j x H2.
    apply subcode_g in H2.
    destruct H2 as ([ y | y q ] & H2 & H3); simpl in H3; try discriminate.
    inversion H3; subst; simpl in H1.
    apply subcode_in_code with (i:= j) in H2; simpl in H2 |- *; try omega.
    destruct (eq_nat_dec j q); try omega.
    destruct (le_lt_dec k q); omega.
  Qed.

  Variable P : list (mm_instr n).

  Notation lP := (length P).

  Let R : list (mm_instr (S n)) := DEC pos0 0 
                                :: DEC pos0 (3+lP)
                                :: DEC pos0 (2+lP)
                                :: nil.

  Let sc_R_1 : (1+lP, DEC pos0 0 :: nil) <sc (1+lP, R).
  Proof. unfold R; auto. Qed.

  Let sc_R_2 : (2+lP, DEC pos0 (1+(2+lP)) :: DEC pos0 (2+lP) :: nil) <sc (1+lP, R).
  Proof. 
    unfold R; rewrite plus_assoc; simpl plus.
    exists (DEC pos0 0 :: nil), nil; simpl; split; auto; omega.
  Qed.

  Let R_sc i rho : (i,rho::nil) <sc (1+lP,R) -> i = 1+lP /\ rho = DEC pos0 0
                                             \/ i = 2+lP /\ rho = DEC pos0 (3+lP)
                                             \/ i = 3+lP /\ rho = DEC pos0 (2+lP).
  Proof.
    unfold R; intros ([ | u [ | v [ | w l ] ] ] & r & H1 & H2); inversion H1; subst i; simpl.
    + do 0 right; left; split; auto; omega.
    + do 1 right; left; split; auto; omega.
    + do 2 right; split; auto; omega.
    + destruct l; discriminate.
  Qed.

  Let R_no_self_loops : mm_no_self_loops (1+lP,R).
  Proof.
    intros i rho H.
    apply R_sc in H.
    destruct H as [ (H1 & H2) | H ].
    { inversion H2; omega. }
    destruct H as [ (H1 & H2) | H ].
    { inversion H2; omega. }
    destruct H as (H1 & H2).
    { inversion H2; omega. }
  Qed.
 
  Let Q := g (1+lP) 1 P ++ R.

  Let Q_no_self_loops : mm_no_self_loops (1,Q).
  Proof.
    apply mm_no_self_loops_app.
    + apply g_loops; simpl; omega. 
    + rewrite length_g, plus_comm; auto.
  Qed.

  Let sc_Q_1 j ρ : (j,ρ::nil) <sc (1,P) -> (j, f (1+lP) j ρ::nil) <sc (1,Q).
  Proof. intro; apply subcode_app_end, g_subcode; auto. Qed.

  Let sc_Q_2 : (1+lP, DEC pos0 0 :: DEC pos0 (3+lP) :: DEC pos0 (2+lP) :: nil) <sc (1,Q).
  Proof. apply subcode_right; rewrite length_g; auto. Qed.

  Let sc_Q_3 : (2+lP, DEC pos0 (3+lP) :: DEC pos0 (2+lP) :: nil) <sc (1,Q).
  Proof. apply subcode_trans with (2 := sc_Q_2); auto. Qed.
 
  Let Q_sc j ρ : (j,ρ::nil) <sc (1,Q) 
              -> (exists ρ', (j,ρ'::nil) <sc (1,P) /\ ρ = f (1+lP) j ρ')
              \/ j = 1+lP /\ ρ = DEC pos0 0
              \/ j = 2+lP /\ ρ = DEC pos0 (3+lP)
              \/ j = 3+lP /\ ρ = DEC pos0 (2+lP).
  Proof.
    intros H.
    apply subcode_app_invert_right in H.
    destruct H as [ H | H ].
    + apply subcode_g in H; auto.
    + rewrite length_g, plus_comm in H. 
      apply R_sc in H; auto.
  Qed. 

  Let Q_length : length Q = length P + 3.
  Proof. 
    unfold Q; rewrite app_length, length_g.
    unfold R; auto.
  Qed.

  Let Q_bound i x j : (i,DEC x j::nil) <sc (1,Q) -> j < 1+length Q.
  Proof.
    rewrite Q_length; intros H.
    apply Q_sc in H.
    destruct H as [ (rho & H1 & H2) | H ].
    { destruct rho as [ | y p ]; try discriminate.
      unfold f in H2.
      destruct (eq_nat_dec i p).
      { inversion H2; omega. }
      destruct (le_lt_dec (1+lP) p); inversion H2; omega. }
    destruct H as [ (H1 & H2) | H ].
    { inversion H2; omega. }
    destruct H as [ (H1 & H2) | H ].
    { inversion H2; omega. }
    destruct H as (H1 & H2).
    { inversion H2; omega. }
  Qed.

  Let P_imp_Q s s0 : in_code (fst s) (1,P) -> (1,P) // s ~~> s0 -> (1,Q) // (fst s, 0##snd s) ↓.
  Proof.
    intros H1 H; revert H1.
    pattern s; revert s H; apply mm_term_ind.
    + simpl; intros; omega.
    + intros i [ x | x p ] v j w H1 H2 H3 H5 H4; unfold fst, snd in *. 
      * apply mm_sss_INC_inv in H2.
        destruct H2 as (G1 & G2).
        destruct (eq_nat_dec i lP) as [ Hi | Hi ].
        - exists (0,0##w); split; try (simpl; omega).
          apply sc_Q_1 in H1; simpl f in H1.
          mm sss INC with (pos_nxt x).
          subst i; clear H1; mm sss DEC 0 with pos0 0.
          mm sss stop; f_equal; simpl; subst; auto. 
        - spec in H5. { subst j; simpl in H4 |- *; omega. }
          apply sc_Q_1 in H1; simpl f in H1.
          apply subcode_sss_terminates_instr with (2 := H1) (3 := H5).
          subst; constructor.
      * generalize H1; intros H6.
        apply sc_Q_1 in H6; unfold f in H6.
        case_eq (v#>x).
        ++ intros Hx.
           destruct (eq_nat_dec i p) as [ Hip | Hip ].
           -- subst p.
              destruct mm_self_loop_no_term_1 with (s := (i,v)) (v := v) (1 := H1); auto.
              exists s0.
              destruct H3 as [ H3 H7 ]; split; auto.
              apply subcode_sss_compute_instr with (1 := H2) (3 := H3); auto.
           -- destruct (le_lt_dec (1+lP) p) as [ Hp1 | Hp1 ];
                [ | destruct (eq_nat_dec p 0) as [ Hp2 | Hp2 ] ].
              ** exists (0,0##v); split; try (simpl; omega).
                 mm sss DEC 0 with (pos_nxt x) 0.
                 mm sss stop.
              ** subst p; exists (0,0##v); split; try (simpl; omega).
                 mm sss DEC 0 with (pos_nxt x) 0.
                 mm sss stop.
              ** apply mm_sss_DEC0_inv with (1 := Hx) in H2.
                 destruct H2; subst j w.
                 spec in H5. { simpl; omega. }
                 apply subcode_sss_terminates_instr with (2 := H6) (3 := H5).
                 constructor; simpl; auto.
        ++ intros u Hx.
           apply mm_sss_DEC1_inv with (1 := Hx) in H2.
           destruct H2 as [ ? H2 ]; subst j.
           destruct (eq_nat_dec i lP) as [ Hi | Hi ].
           -- exists (0,0##w); split; simpl; auto.
              apply subcode_sss_compute_instr with (2 := H6) (st2 := (1+i,0##w)); auto.
              ** replace (0##w) with ((0##v)[u/pos_nxt x]); subst; auto; constructor; auto.
              ** subst i; mm sss DEC 0 with pos0 0; mm sss stop.
           -- spec in H5. { simpl in H4 |- *; omega. }
              apply subcode_sss_terminates_instr with (2 := H6) (3 := H5); auto.
              replace (0##w) with ((0##v)[u/pos_nxt x]); subst; auto; constructor; auto.
  Qed.

  Let Q_imp_P s s0 : in_code (fst s) (1,P) -> (snd s)#>pos0 = 0 -> (1,Q) // s ~~> s0 -> (1,P) // (fst s, vec_tail (snd s)) ↓.
  Proof.
    intros H1 H2 H3; revert H1 H2.
    pattern s; revert s H3; apply mm_term_ind.
    + simpl; intros; omega.
    + intros i ρ v j w H1 H2 H3 H4 H5 H6; unfold fst, snd in *.
      rewrite (vec_head_tail v) in H2, H6.
      revert H2 H6.
      generalize (vec_head v) (vec_tail v); clear v; intros x v; simpl; intros H2 H6; subst x.
      destruct Q_sc with (1 := H1) as [ ([ x | x p ] & G1 & G2) | G1 ]; try subst ρ.
      * unfold f in H2.
        apply mm_sss_INC_inv in H2.
        destruct H2 as (? & H2); subst j w.
        revert H4; rew vec; simpl; intros H4.
        destruct (eq_nat_dec i lP) as [ Hi | Hi ].
        - exists (S i, v[(S (v#>x))/x]); split; try (simpl; omega).
          mm sss INC with x; mm sss stop.
        - spec in H4. simpl in H5; omega. spec in H4; auto.
          apply subcode_sss_terminates_instr with (2 := G1) (3 := H4); auto; constructor.
      * unfold f in H2; case_eq (v#>x).
        - intros Hx.
          apply mm_sss_DEC0_inv in H2; auto.
          destruct H2; subst j w.
          destruct (eq_nat_dec i p) as [ Hip | Hip ].
          ** subst p; exfalso.
             generalize (ex_intro _ s0 H3); simpl.
             change (~ (1,Q) // (2+lP,0##v) ↓).
             apply mm_self_loop_no_term_2 with (v := 0##v) (1 := sc_Q_3); auto.
          ** destruct (le_lt_dec (1+lP) p) as [ Hp | Hp ];
               [ | destruct (eq_nat_dec p 0) as [ Hp2 | Hp2 ] ].
             ++ exists (p,v); split; try (simpl; omega).
                mm sss DEC 0 with x p; mm sss stop.
             ++ exists (p,v); split; try (simpl; omega).
                mm sss DEC 0 with x p; mm sss stop.
             ++ spec in H4. simpl in H5 |- *; omega.
                spec in H4; auto.
                apply subcode_sss_terminates_instr with (2 := G1) (3 := H4); auto; constructor.
                simpl; auto.
        - intros u Hx.
          apply mm_sss_DEC1_inv with (u := u) in H2; auto.
          destruct H2; subst j w.
          simpl in H4.
          destruct (eq_nat_dec i lP) as [ Hi | Hi ].
          ** exists (S i, v[u/x]); split; try (simpl; omega).
             mm sss DEC S with x p u; mm sss stop.
          ** spec in H4. simpl in H5; omega.
             spec in H4; auto.
             apply subcode_sss_terminates_instr with (2 := G1) (3 := H4); auto.
             constructor; auto.
      * destruct G1 as [ (? & _) | [ (? & _) | (? & _) ] ]; simpl in H5; omega.
  Qed.

  Theorem mm_remove_self_loops : { Q |  mm_no_self_loops (1,Q)
                                     /\ (forall i x j, (i,DEC x j::nil) <sc (1,Q) -> j < 1+length Q)
                                     /\ forall v, (1,P) // (1,v) ↓ <-> (1,Q) // (1,0##v) ↓ }.
  Proof.
    destruct (eq_nat_dec lP 0) as [ HlP | HlP ].
    +  exists nil.
       split; [ | split ].
       - intros i rho ([ | ] & ? & ? & ?); discriminate.
       - intros i x j ([ | ] & ? & ? & ?); discriminate.
       - destruct P; try discriminate.
         split.
         * exists (1,0##v); split; simpl; try omega; mm sss stop.
         * exists (1,v); split; simpl; try omega; mm sss stop.
    + exists Q; split; auto; split; auto; intros v; split.
      * intros (s0 & H); revert H; apply P_imp_Q; simpl; omega.
      * intros (s0 & H); revert H; apply Q_imp_P; simpl; omega.
  Qed.

End remove_self_loops.

  
