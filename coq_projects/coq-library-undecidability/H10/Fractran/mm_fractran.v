(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*             Yannick Forster            [+]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(*                             [+] Affiliation Saarland Univ. *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

(** ** Compiler from MM to FRACTRAN *)

Require Import List Arith Omega Permutation.

Import ListNotations.

Require Import utils_tac utils_list utils_nat gcd prime rel_iter pos vec.
Require Import sss subcode mm_defs mm_no_self.
Require Import fractran_defs prime_seq.

Set Implicit Arguments.

Tactic Notation "rew" "length" := autorewrite with length_db. 

Local Notation "e #> x" := (vec_pos e x).
Local Notation "e [ v / x ]" := (vec_change e x v).

Local Notation "I // s -1> t" := (mm_sss I s t).
Local Notation "P /MM/ s → t" := (sss_step (@mm_sss _) P s t) (at level 70, no associativity). 
Local Notation "P /MM/ s -[ k ]-> t" := (sss_steps (@mm_sss _) P k s t) (at level 70, no associativity).
Local Notation "P /MM/ s ↓" := (sss_terminates (@mm_sss _) P s) (at level 70, no associativity).

Local Notation "l /F/ x → y" := (fractran_step l x y) (at level 70, no associativity).
Local Notation "l /F/ x -[ k ]-> y" := (fractran_steps l k x y) (at level 70, no associativity).

Set Implicit Arguments.

(* Fractran simulates MM *)

(*       let a MM program 1: INC ... k: DEC ... n: _ *)
(*       with variables x1...xm *)

(*    we use p1...pn,q1...qm distinct primes and  *)
(*    encode the state (i,v1,...,vm) *)
(*    as p1^0*...*pi^1*...*pn^0*q1^v1*...*qm^vm *)

(*    i: INC xu   ---> (qu*p(i+1) / pi) *)
(*    i: DEC xu j ---> (p(i+1) / pi*qu) and (pj / pi) (the second constraint should appear AFTER in the list) *)

Definition encode_state {n} (c : nat * vec nat n) := ps (fst c) * @exp n 0 (snd c).

Definition encode_inc n  i (u : pos n) := (ps (i + 1) * qs u, ps i).
Definition encode_dec n  i (u : pos n) (_ : nat) := (ps (i + 1), ps i * qs u).
Definition encode_dec2 n i (u : pos n) j := (ps j, ps i).

Definition encode_one_instr m i (rho : mm_instr m) :=
  match rho with
    | INC u   => encode_inc i u :: nil
    | DEC u j => encode_dec i u j :: encode_dec2 i u j :: nil
  end.

Fixpoint encode_mm_instr m i (l : list (mm_instr m)) : list (nat * nat) :=
  match l with
    | nil          => nil
    | rho :: l => encode_one_instr i rho ++ encode_mm_instr (S i) l
  end.

Fact encode_mm_instr_app m i l r : @encode_mm_instr m i (l++r) = encode_mm_instr i l++encode_mm_instr (length l+i) r.
Proof.
  revert i; induction l as [ | rho l IHl ]; intros i; simpl; auto; rewrite IHl, app_ass.
  do 3 f_equal; omega.
Qed.

Fact encode_mm_instr_regular n i l : Forall (fun c => fst c <> 0 /\ snd c <> 0) (@encode_mm_instr n i l).
Proof.
  revert i; induction l as [ | [ u | u j ] l IHl ]; intros i; simpl.
  + constructor.
  + constructor; auto; unfold encode_inc; simpl; split;
      [ apply Nat.neq_mul_0; split | ]; apply prime_neq_0; apply nthprime_prime.
  + constructor; [ | constructor ]; auto; split; unfold encode_dec, encode_dec2; simpl.
    2: apply Nat.neq_mul_0; split.
    all: apply prime_neq_0; apply nthprime_prime.
Qed.

Fact encode_mm_instr_regular' n i l : fractran_regular (@encode_mm_instr n i l).
Proof.
  generalize (@encode_mm_instr_regular n i l); apply Forall_impl; tauto.
Qed.

Fact encode_mm_instr_in_inv n i P el c er : 
          @encode_mm_instr n i P = el++c::er
       -> exists l rho r, P = l++rho::r /\ In c (encode_one_instr (length l+i) rho).
Proof.
  revert i el c er; induction P as [ | rho P IHP ]; simpl; intros i el c er H.
  + destruct el; discriminate.
  + destruct list_app_cons_eq_inv with (1 := H)
      as [ (m & H1 & H2) | (m & H1 & H2) ].
    * destruct IHP with (1 := H2) as (l & rho' & r & G1 & G2).
      exists (rho::l), rho', r; subst; split; auto.
      eq goal G2; do 2 f_equal; simpl; omega.
    * exists nil, rho, P; split; simpl; auto.
      rewrite <- H1; apply in_or_app; simpl; auto.
Qed.

Local Notation divides_mult_inv := prime_div_mult.

Local Ltac inv H := inversion H; subst; clear H.

Opaque ps qs.

Lemma divides_encode_state i k n v : divides (ps i) (@encode_state n (k,v)) -> i = k.
Proof.
  unfold encode_state. intros. induction v.
  - cbn in H. replace (ps k * 1) with (ps k) in H by omega.
    now eapply primestream_divides in H.
  - cbn in H. eapply divides_mult_inv in H as [ | [ | ] % divides_mult_inv ]; eauto.
    + now eapply primestream_divides in H.
    + eapply divides_pow in H; eauto.
      now eapply ps_qs_div in H.
    + now eapply ps_exp in H.
Qed.

Lemma skip_steps m k l r k' (v v' : vec _ m) :
      @mm_no_self_loops m (k, l ++ r) 
   -> encode_mm_instr (k + length l) r /F/ encode_state (k + length l,v) → encode_state (k',v') 
   -> encode_mm_instr k (l ++ r)       /F/ encode_state (k + length l,v) → encode_state (k',v').
Proof with eauto; try omega.
  revert k. induction l; cbn - [subcode] in *; intros.
  - revert H0. ring_simplify (k + 0). eauto.
  - revert H0. ring_simplify (k + S (length l)). intros H1. destruct a.
    + econstructor 2. intros [[|] % divides_mult_inv | ] % divides_mult_inv; eauto.
      * eapply primestream_divides in H0; omega.
      * now eapply ps_qs_div in H0. 
      * eapply divides_encode_state in H0; omega.
      * specialize IHl with (k := S k). revert IHl.
        cbn - [subcode]. ring_simplify (S (k + length l)).
        intros IHl. eapply IHl. 2:exact H1.
        intros ? ? ?. eapply H. eapply subcode_cons. eassumption.
    + repeat econstructor 2. 2:unfold encode_dec2.
      2,3: cbn- [subcode]. 1: intros [] % divides_mult_inv_l.
      2: intros [ | ] % divides_mult_inv...
      * eapply divides_mult_inv in H0 as [? | ?]...
        eapply primestream_divides in H0...
        eapply divides_encode_state in H0... 
      * eapply primestream_divides in H0... subst.
        eapply (H n p). eauto.
      * eapply divides_encode_state in H0...
      * specialize (IHl (S k)). revert IHl.
        cbn - [subcode]. ring_simplify (S (k + length l)).
        intros IHl. eapply IHl. 2:exact H1.
        intros ? ? ?. eapply H. eapply subcode_cons. eassumption.
Qed.

Lemma qs_exp i n u (v : vec nat n) :
  divides (qs u) (encode_state (i,v)) <-> divides (qs u) (exp 0 v).
Proof.
  split.
  - intros [ | ] % divides_mult_inv; eauto.
    now eapply qs_ps_div in H.
  - intros. unfold encode_state. now eapply divides_mult.
Qed.

Lemma qs_encode_state i n (u : pos n) (v : vec nat n) :
  divides (qs u) (encode_state (i,v)) <-> v #> u > 0.
Proof.
  rewrite qs_exp.
  enough (forall i, divides (qs (i + u)) (exp i v) <-> v #> u > 0). eapply H. intros j.
  induction v.
  - inversion u.
  - revert u. eapply pos.pos_S_invert.
    + cbn; rewrite pos2nat_fst, Nat.add_0_r. 
      split.
      * intros [ | ] % divides_mult_inv; eauto.
        -- destruct x; try omega. cbn in H. 
           apply divides_1_inv in H.
           generalize (str_prime qs j); rewrite H.
           intros [ [] _ ]; auto.
        -- eapply qs_exp_div in H; now eauto.
      * intros. destruct x. inv H.
        exists (qs j ^ x * exp (S j) v). cbn. ring.
    + cbn. intros. rewrite <- IHv, pos2nat_nxt.
      rewrite qs_shift with (m := 1).
      simpl.
      replace (j+S (pos2nat p)) with (S (j+p)); try tauto.
      2: rewrite (plus_comm _ (S _)); simpl; rewrite plus_comm; auto.
      split; intros H.
      * eapply divides_mult_inv in H as [ | ]; eauto.
        eapply divides_pow in H; auto. 
        eapply primestream_divides in H.
        omega.
      * eapply divides_mult. 
        revert H; cbn; rewrite plus_n_Sm; eauto.
Qed.

Lemma one_step_forward m i P i1 v1 i2 v2 :
     @mm_no_self_loops m (i,P) 
  -> (i, P)              /MM/ (i1, v1)           → (i2,v2) 
  -> encode_mm_instr i P /F/  encode_state (i1,v1) → encode_state (i2,v2).
Proof with eauto; try omega.
  intros HP (k & l & [ u | u j ] & r & v & ? & ? & ?); inversion H; subst; clear H.
  - inversion H0; inversion H1; subst; clear H0 H1. 
    eapply skip_steps...
    econstructor. cbn. ring_simplify.
    replace (1 + (k + length l)) with (k + length l + 1) by omega. unfold encode_state, fst, snd. 
    rewrite vec_prod_mult.
    rewrite Nat.add_0_r; ring.
  - inversion H0; inversion H1; subst; clear H0 H1.
    all:eapply skip_steps...
    + cbn. econstructor 2.
      intros [] % divides_mult_inv_l...
      eapply divides_mult_inv in H0 as [ | ]...
      * now eapply qs_ps_div in H0.          
      * eapply qs_encode_state in H0. omega.
      * unfold encode_dec2. econstructor. unfold encode_state, fst, snd. ring.
    + econstructor. cbn. unfold encode_state, fst, snd. ring_simplify.
      replace (1 + (k + length l)) with (k + length l + 1) by omega.
      erewrite <- (vec_prod_div _ _ _ H4).
      rewrite Nat.add_0_r; ring.
Qed.

Lemma steps_forward m i P i1 v1 i2 v2 k :
    @mm_no_self_loops m (i, P) 
 -> (i, P) /MM/ (i1, v1) -[k]-> (i2,v2)
 -> encode_mm_instr i P /F/ encode_state (i1,v1) -[k]-> encode_state (i2,v2).
Proof.
  intros HP H. revert v1 i1 i2 H. induction k; intros v1 i1 i2 H; inversion H; subst; clear H; cbn.
  - reflexivity.
  - destruct st2. eapply one_step_forward in H1; eauto.
Qed.

(** The divisibility results are no so complicated when
    we do not need to show that encode_state is injective ... *)

Local Fact divides_from_eq x y t : x*y = t -> divides x t.
Proof. exists y; subst; ring. Qed.

Local Fact prime_div_mult3 p x y z : prime p -> divides p (x*y*z) -> divides p x \/ divides p y \/ divides p z.
Proof.
  intros H1 H2.
  apply prime_div_mult in H2; auto.
  destruct H2 as [ H2 | ]; auto.
  apply prime_div_mult in H2; tauto.
Qed.

Local Fact prime_div_mult4 p w x y z : prime p -> divides p (w*x*y*z) -> divides p w \/ divides p x \/ divides p y \/ divides p z.
Proof.
  intros H1 H2.
  apply prime_div_mult3 in H2; auto.
  destruct H2 as [ H2 | H2 ]; try tauto.
  apply prime_div_mult in H2; tauto.
Qed.

Local Hint Resolve encode_mm_instr_regular'.

Lemma one_step_backward m i P i1 v1 st :
     @mm_no_self_loops m (i, P)
  -> encode_mm_instr i P /F/ @encode_state m (i1,v1) → st 
  -> exists i2 v2, st = @encode_state m (i2,v2)
                /\ (i, P) /MM/ (i1, v1) → (i2,v2).
Proof.
  intros H1 H2.
  destruct fractran_step_inv with (1 := H2)
    as (el & p & q & er & H3 & H4 & H5).
  unfold encode_state in H5; simpl in H5.
  destruct encode_mm_instr_in_inv with (1 := H3)
    as (l & rho & r & -> & G2).
  assert (i1 = length l+i) as E.
  { unfold encode_one_instr in G2.
    destruct rho as [ u | u j ]; unfold encode_inc, encode_dec, encode_dec2 in G2;
      [ destruct G2 as [ G2 | [] ] | destruct G2 as [ G2 | [ G2 | [] ] ] ]; 
      inversion G2; subst p q; clear G2;
      repeat rewrite mult_assoc in H5.
    * apply divides_from_eq, prime_div_mult4 in H5; auto.
      destruct H5 as [ H5 | [ H5 | [ H5 | H5 ] ] ].
      + apply primestream_divides in H5; omega.
      + apply ps_qs_div in H5; tauto.
      + apply primestream_divides in H5; omega.
      + apply ps_exp in H5; tauto.
    * rewrite <- mult_assoc in H5.
      apply divides_from_eq, prime_div_mult3 in H5; auto.
      destruct H5 as [ H5 | [ H5 | H5 ] ].
      + apply primestream_divides in H5; omega.
      + apply primestream_divides in H5; omega.
      + apply ps_exp in H5; tauto.
    * apply divides_from_eq, prime_div_mult3 in H5; auto.
      destruct H5 as [ H5 | [ H5 | H5 ] ].
      + apply primestream_divides in H5.
        exfalso; apply (H1 j u); auto.
      + apply primestream_divides in H5; omega.
      + apply ps_exp in H5; tauto. }
  destruct mm_sss_total with (ii := rho) (s := (i1,v1))
    as ((i2 & v2) & H7).
  exists i2, v2.
  assert ((i, l++rho::r) /MM/ (i1,v1) → (i2,v2)) as H8.
  { apply in_sss_step; auto; simpl; omega. }
  split; auto.
  apply one_step_forward in H8; auto.
  revert H2 H8; apply fractran_step_fun; auto.
Qed.

Lemma steps_backward m i P i1 v1 k st :
     @mm_no_self_loops m (i, P)
  ->               encode_mm_instr i P /F/ encode_state (i1,v1) -[k]-> st 
  -> exists i2 v2, (i, P) /MM/ (i1, v1) -[k]-> (i2,v2)
                /\ st = encode_state (i2,v2). 
Proof.
  intros H1.
  revert i1 v1 st; induction k as [ | k IHk ]; intros i1 v1 st H; simpl in H.
  - subst; exists i1, v1; split; auto; constructor.
  - destruct H as (st1 & H2 & H3).
    destruct one_step_backward with (2 := H2)
      as (i2 & v2 & -> & H5); auto.
    destruct IHk with (1 := H3) as (i3 & v3 & ? & ->).
    exists i3, v3; split; auto.
    constructor 2 with (i2,v2); auto.
Qed.

Theorem mm_fractran_simulation n P v :
     @mm_no_self_loops n (1, P) 
  -> (1,P) /MM/ (1,v) ↓ <-> encode_mm_instr 1 P /F/ ps 1 * exp 0 v ↓.
Proof.
  intros HP.
  change (ps 1* exp 0 v) with (encode_state (1,v)).
  split.
  + intros ((j,w) & (k & H1) & H2); simpl fst in *.
    exists (encode_state (j,w)); split.
    * exists k; apply steps_forward in H1; auto.
    * intros x Hx.
      destruct one_step_backward with (2 := Hx)
        as (i2 & v2 & -> & ?); auto.
      revert H; apply sss_out_step_stall; auto.
  + intros (st & (k & H1) & H2).
    destruct steps_backward with (2 := H1)
      as (i2 & v2 & H3 & ->); auto.
    exists (i2,v2); split.
    * exists k; auto.
    * simpl fst.
      destruct (in_out_code_dec i2 (1,P)) as [ H4 | H4 ]; auto; exfalso.
      destruct in_code_subcode with (1 := H4) as (rho & l & r & G1 & G2).
      destruct (mm_sss_total rho (i2,v2)) as ((i3,v3) & G3).
      apply H2 with (encode_state (i3,v3)).
      apply one_step_forward; auto.
      subst P; apply in_sss_step; auto.
Qed.

Theorem mm_fractran_n n (P : list (mm_instr n)) : 
        { l |  Forall (fun c => snd c <> 0) l
            /\ forall v, (1,P) /MM/ (1,v) ↓ <-> l /F/ ps 1 * exp 1 v ↓ }.
Proof.
   destruct mm_remove_self_loops with (P := P) as (Q & H1 & _ & H2).
   exists (encode_mm_instr 1 Q); split. 
   + generalize (encode_mm_instr_regular 1 Q); apply Forall_impl; intros; tauto.
   + intros x.
     rewrite H2, mm_fractran_simulation; auto.
     simpl exp; rewrite Nat.add_0_r; tauto.
Qed.

Theorem mm_fractran n (P : list (mm_instr (S n))) : 
     { l | forall x, (1,P) /MM/ (1,x##vec_zero) ↓ <-> l /F/ ps 1 * qs 1^x ↓ }.
Proof.
   destruct mm_fractran_n with (P := P) as (l & _ & Hl).
   exists l; intros x; rewrite Hl; simpl.
   rewrite exp_zero, Nat.mul_1_r; tauto.
Qed.
