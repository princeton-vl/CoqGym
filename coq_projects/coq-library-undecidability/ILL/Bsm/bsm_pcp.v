(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import List Arith Max Omega Wellfounded Bool.

Require Import utils pos vec. 
Require Import subcode sss. 
Require Import list_bool tiles_solvable bsm_defs bsm_utils.

Set Implicit Arguments.

(** ** iBPCP reduces to BSM *)

Tactic Notation "rew" "length" := autorewrite with length_db.

Local Notation "e #> x" := (vec_pos e x).
Local Notation "e [ v / x ]" := (vec_change e x v).

Local Notation "P // s -[ k ]-> t" := (sss_steps (@bsm_sss _) P k s t).
Local Notation "P // s ->> t" := (sss_compute (@bsm_sss _) P s t).
Local Notation "P // s ~~> t" := (sss_output (@bsm_sss _) P s t).

Section Simulator.

  Hint Rewrite main_loop_length main_init_length : length_db.

  Variable (lt : list ((list bool) *(list bool))).

  Let n := 4.
  Let s : pos 4 := pos0.
  Let h : pos 4 := pos1.
  Let l : pos 4 := pos2.
  Let a : pos 4 := pos3.
  
  Let Hsa : s <> a. Proof. discriminate. Qed.
  Let Hsh : s <> h. Proof. discriminate. Qed.
  Let Hsl : s <> l. Proof. discriminate. Qed.
  Let Hah : a <> h. Proof. discriminate. Qed.
  Let Hal : a <> l. Proof. discriminate. Qed.
  Let Hhl : h <> l. Proof. discriminate. Qed.

  Let lML := length_main_loop lt.
      
  (* The complete simulator for the PCP *) 
 
  Definition pcp_bsm := 
        (*      1 *) main_init s a h l 1 ++
        (*     14 *) main_loop s a h l lt 14 (14+lML) ++
        (* 14+lML *) main_init s a h l (14+lML) ++
        (* 27+lML *) POP  s 0 0 :: 
                     nil.
                     
  Notation simulator := pcp_bsm.

  Fact simulator_length : length simulator = 27+lML.
  Proof. unfold simulator; rew length; unfold lML; omega. Qed.

  Fact pcp_bsm_size : length simulator = 86+3*length lt+size_cards lt.
  Proof.
    rewrite simulator_length; unfold lML.
    rewrite main_loop_size; omega.
  Qed.
  
  Let HS1 : (1,main_init s a h l 1) <sc (1, simulator).
  Proof. unfold simulator; auto. Qed.

  Let HS2 : (14,main_loop s a h l lt 14 (14+lML)) <sc (1, simulator).
  Proof. unfold simulator; auto. Qed.

  Let HS3 : (14+lML,main_init s a h l (14+lML)) <sc (1, simulator).
  Proof. unfold simulator; auto. Qed.

  Ltac dest x y := destruct (pos_eq_dec x y) as [ | ]; [ subst x | ]; rew vec.

  Theorem pcp_bsm_sound v : 
             tiles_solvable lt 
          -> (1,simulator) // (1,v) ->> (0,v[nil/s][nil/a][nil/h][nil/l]).
  Proof.
    intros H1; unfold simulator.
    apply subcode_sss_compute_trans with (2 := main_init_spec Hsa Hsh Hsl Hah Hal 1 v); auto.
    destruct (main_loop_sound Hsa Hsh Hsl Hah Hal Hhl)
       with (lt := lt) (i := 14) (p := 14+lML)
               (v := v[(Zero::nil)/s][nil/a][nil/h][nil/l])
       as (w & Hw1 & Hw2); rew vec.
    apply subcode_sss_compute_trans with (2 := Hw1); auto.
    apply subcode_sss_compute_trans with (2 := main_init_spec Hsa Hsh Hsl Hah Hal (14+lML) _); auto.
    bsm sss POP 0 with s 0 0 nil; rew vec.
    bsm sss stop; f_equal.
    apply vec_pos_ext; intros x.
    dest x a; dest x l; dest x h; dest x s.
    rewrite <- Hw2; rew vec.
  Qed.
  
  Theorem pcp_bsm_complete v w p : 
              (1,simulator) // (1,v) ~~> (p,w)
           -> tiles_solvable lt /\ p = 0 /\ w = v[nil/s][nil/a][nil/h][nil/l].
  Proof.
    intros ((k2 & Hk2) & H1).

    destruct (main_init_spec Hsa Hsh Hsl Hah Hal 1 v) as (k1 & Hk1).
    apply subcode_sss_subcode_inv with (4 := Hk1) in Hk2; auto.
    2: apply bsm_sss_fun.
    2: revert H1; apply subcode_out_code; auto.
    destruct Hk2 as (k & ? & Hk2); subst.
    
    apply subcode_sss_steps_inv with (1 := HS2) in Hk2; auto.
    2: simpl; omega.
    2: revert H1; apply subcode_out_code; auto.
    destruct Hk2 as (k2 & k3 & (q,v') & H2 & H3 & H4 & H5).
    simpl fst in H5.
    apply ex_intro with (x := k2) in H2.
    
    apply main_loop_complete in H2; rew vec.
    2: unfold out_code, code_end, snd, fst, lML; rew length; omega.
    destruct H2 as (? & H2 & H6); subst.
    split; auto.

    destruct (main_init_spec Hsa Hsh Hsl Hah Hal (14+lML) v') as (k4 & Hk4).
    apply subcode_sss_subcode_inv with (4 := Hk4) in H3; auto.
    2: apply bsm_sss_fun.
    2: revert H1; apply subcode_out_code; auto.
    destruct H3 as (k5 & ? & H7); subst.
    
    unfold simulator in H7.
    bsm inv POP 0 with H7 s 0 0 (@nil bool); rew vec.
    destruct H7 as (k6 & H7 & H8).
    
    apply sss_steps_stall in H8.
    2: simpl; omega.
    apply proj2 in H8.
    inversion H8.
    split; auto.
    apply vec_pos_ext; intros x.
    dest x s; dest x l; dest x h; dest x a.
    rewrite <- H2; rew vec.
        
    intros E.
    apply f_equal with (f := fst) in E.
    unfold fst in E.
    subst p.
    revert H1.
    unfold out_code, code_start, code_end, fst, snd.
    rewrite simulator_length.
    intro; omega.
  Qed.
  
End Simulator.
