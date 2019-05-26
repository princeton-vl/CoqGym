From Undecidability.L Require Export L Encodings Interpreter Choose.

(** * Results obtained with self-interpreters *)

(** ** Step-indexed self-interpreter *)

(** *** Encoding of options *)

Definition none : term := .\"s", "n"; "n".
Definition some : term := .\"t", "s", "n"; "s" "t".

Hint Unfold some none : cbv.

Definition oenc t :=
  match t with
  | Some t => lambda(lambda (1 (tenc t)))
  | None => none
  end.

Lemma oenc_cls s: closed (oenc s).
Proof.
  destruct s; simpl; value.
Qed.

Lemma oenc_lambda s: lam (oenc s).
Proof.
  destruct s; simpl; value.
Qed.

Hint Resolve oenc_cls oenc_lambda: cbv.  
 
Lemma some_correct s : some (tenc s) ≡ oenc (Some s).
Proof.
  solveeq.
Qed.

Lemma some_correct_r s t t' : proc t -> proc t' -> oenc (Some s) t t' ≡ t (tenc s).
Proof.
  intros. solveeq.
Qed.

Lemma none_correct s t : proc s -> proc t  -> none s t ≡ t.
Proof.
  intros. solveeq.
Qed.

Lemma oenc_correct_some s v : lam v -> oenc (Some s) ≡ some v -> v ≡ tenc s.
Proof. 
  intros lam_v H.
  symmetry in H. eapply eqTrans with (s := lambda(lambda(1 v))) in H. eapply unique_normal_forms in H; value. inv H. reflexivity.
  symmetry; clear H; solvered.
Qed.


Lemma oenc_inj o1 o2 : oenc o1 ≡ oenc o2 -> o1 = o2.
Proof.
  intros H; eapply unique_normal_forms in H; value.
  destruct o1, o2; try congruence; cbn in H; repeat inv H.
  eapply tenc_injective in H1. now subst.
Qed.

Lemma none_equiv_some v : ~ oenc None ≡ some v.
Proof.
  intros H. assert (eva v) as (w & [Hw Hl] % evaluates_equiv) by (eapply app_eva; eexists (oenc None); eapply evaluates_equiv; split; value; eauto using equiv).
  rewrite Hw in H. symmetry in H. eapply eqTrans with (s := (lambda (lambda (1 w)))) in H.
  eapply unique_normal_forms in H; value. inv H. symmetry. unfold some. clear H. solvered.
Qed.  

(** *** Equality of encoded natural numbers *)
Definition EqN := rho (.\"EqN", "n", "m"; "n" ("m" !T !(lambda F)) (.\"n"; "m" !F (.\"m"; "EqN" "n" "m"))).

Hint Unfold EqN: cbv.

Lemma EqN_correct m n : EqN (enc m) (enc n) ≡ benc (Nat.eqb m n).
Proof with eauto.
  revert n; induction m; intros.
  - destruct n. repeat redL. repeat redL.
  - destruct n.
    + repeat redL.
    + transitivity (EqN (enc m) (enc n)). repeat redL. now rewrite IHm. 
Qed.

(** *** Substitution *)

Definition Subst := rho (.\ "Subst", "s", "k", "u"; "s" (.\"n"; !EqN "n" "k" "u" (!Var "n"))
                                                     (.\"s1", "s2"; !App ("Subst" "s1" "k" "u") ("Subst" "s2" "k" "u"))
                                                     (.\"s1"; !Lam ("Subst" "s1" (!Succ "k") "u")) ).

Hint Unfold Subst : cbv.

Lemma Subst_correct s k u :
  Subst (tenc s) (enc k) (tenc u) ≡ tenc (subst s k u).
Proof.
  revert k; induction s; intros k.
  - transitivity (EqN (enc n) (enc k) (tenc u) (Var (enc n))). solveeq.
    rewrite EqN_correct.
    destruct (Nat.eqb_spec n k); cbn; decide (n = k); try congruence; solveeq.
  - specialize (IHs1 k). specialize (IHs2 k). solveeq.
  - transitivity (Lam (((Subst (tenc s)) (Succ (enc k))) (tenc u))). solveeq.
    rewrite Succ_correct, IHs;value. solveeq.
Qed.

(** *** Step-indexed self-interpreter *)

Definition E := Eval cbv in
                 rho (.\ "Eval","n","u";"u"
                   (.\"";!none)
                   (.\"s","t"; "n" !none 
                                   (.\"n"; "Eval" "n" "s" 
                                           (.\"s"; "Eval" "n" "t" 
                                                 (.\"t"; "s"
                                                           (.\""; !none)
                                                           (.\"",""; !none)
                                                           (.\"s"; "Eval" "n" (!Subst "s" !Zero "t")))
                                                 !none)
                                           !none))
                   (.\"s"; !some (!Lam "s"))).

Definition cLam s := lambda(lambda(lambda(0 s))).
Hint Unfold cLam : cbv. 

Lemma E_rec_app_Sn_1 s t n s1 t1 : 
   proc s1 ->
   proc t1 ->
   E (enc n) (tenc s) ≡ some (cLam s1) -> 
   E (enc n) (tenc t) ≡ some (cLam t1) ->
   E (enc (S n)) (tenc (app s t)) ≡ E (enc n) (Subst s1 Zero (cLam t1)).
Proof.
  intros. solveeq. 
Qed.

Lemma E_rec_app_Sn_2 s t n : E (enc n) (tenc s) ≡ none -> E (enc (S n)) (tenc (s t)) ≡ none.
Proof.
  intros H. solveeq.
Qed.

Lemma E_rec_app_Sn_3 s t n t1 : proc t1
                                   -> E (enc n) (tenc s) ≡ some (cLam t1)
                                   -> E (enc n) (tenc t) ≡ none
                                   -> E (enc (S n)) (tenc (s t)) ≡ none.
Proof.
  intros [clsT1 lamT1] Hs Ht. solveeq.
Qed.
                                              
Lemma E_correct k s : E (enc k) (tenc s) ≡ oenc (eval k s).
Proof with value.
  revert s; induction k; intros s.
  - destruct s; solveeq.
  - destruct s.
    + solveeq.
    + destruct (eval k s1) eqn:Hs1.
      * destruct (eval_lambda Hs1); subst t. {
        destruct (eval k s2) eqn:Hs2.
        - destruct (eval_lambda Hs2); subst t.        
          eapply eqTrans. 
          eapply E_rec_app_Sn_1 with (s1 := tenc x) (t1 := tenc ( x0));
            eauto with cbv...
          rewrite IHk, Hs1. symmetry. solveeq.
          rewrite IHk, Hs2. symmetry. solveeq.
          assert (Subst (tenc x) Zero (tenc (lambda x0)) ≡ tenc (subst x 0 (lambda x0))).
          change Zero with (enc 0). eapply Subst_correct.
          rewrite H, IHk. simpl. now rewrite Hs1, Hs2. 
       -  rewrite E_rec_app_Sn_3 with (t1 := tenc x); eauto with cbv...
          simpl. rewrite Hs1, Hs2. reflexivity.
          rewrite IHk. rewrite Hs1. symmetry. solveeq.
          rewrite IHk. rewrite Hs2. symmetry. solveeq. 
        }
      * simpl. rewrite Hs1. eapply E_rec_app_Sn_2. 
        change none with (oenc (None)). rewrite <- Hs1. eapply IHk.
    + solveeq. 
Qed.

Lemma E_S n s t : E (enc n) (tenc s) ▷ oenc (Some t) -> E (enc (S n)) (tenc s) ▷ oenc (Some t).
Proof.
  rewrite !E_correct. intros [? % oenc_inj ?] % evaluates_equiv; value.
  erewrite eval_S; eauto using evaluates.
Qed.

Lemma E_sound n s : E (enc n) (tenc s) ▷ oenc (None) \/ exists t, E (enc n) (tenc s) ▷ oenc (Some t) /\ s ▷ t.
Proof.
  destruct (eval n s) eqn:Eq.
  - right. exists t. rewrite E_correct, Eq. eauto using evaluates, eval_evaluates.
  - left. rewrite E_correct, Eq. econstructor.
Qed.

Lemma E_complete s t : s ▷ t -> exists n, E (enc n) (tenc s) ▷ oenc (Some t).
Proof.
  intros [n H] % evaluates_eval. exists n. rewrite E_correct, H. econstructor.
Qed.

(** ** Class of total procedures is unrecognisable *)

Require Import DecidableRecognisable Rice.

Lemma totality : ~ recognisable (fun s => proc s /\ forall t, eva(s (tenc t))).
Proof.
  pose (f := fun s : term => lambda (0 (lambda (E 0 (tenc (s (tenc s))) D I)) F I)).
  pose (v := lambda (Lam (App (App (App (tenc 0) (Lam (App (App (App (App (tenc E) (tenc 0)) (Q (App 0 (Q 0)))) (tenc D)) (tenc I)))) (tenc F)) (tenc I)))).

  eapply (@Reduction _ f v).
  - value.
  - intros. 
    assert (forall t, f s (tenc t) ≡ (tenc t) (lambda (E 0 (tenc (s (tenc s))) D I)) F I) by (intros; solveeq).
    intuition.
    + eapply eva_Omega.
      destruct H2 as [s' [n H2] % evaluates_eval].
      specialize (H4 n).
      rewrite H0 in H4.
      eapply eva_proper; try eassumption. symmetry.
      transitivity (E (enc n) (tenc (s (tenc s))) D I). solveeq.
      rewrite E_correct, H2. solveeq.
    + value.
    + destruct t.
      * destruct (eval n (s (tenc s))) eqn:Hs.
        -- destruct H1. exists t. firstorder using eval_evaluates.
        -- rewrite H0. eapply eva_proper.
           transitivity (E (enc n) (tenc (s (tenc s))) D I). solveeq.
           rewrite E_correct, Hs. transitivity I. solveeq. reflexivity.
           exists I; repeat econstructor.
      * exists (tenc t2). solveeq.
      * exists (tenc t). solveeq.
  - intros s.
    transitivity (Lam (App (App (App (tenc 0) (Lam (App (App (App (App (tenc E) (tenc 0)) (Q (App (tenc s) (Q (tenc s))))) (tenc D)) (tenc I)))) (tenc F)) (tenc I))). solveeq.
    now rewrite Q_correct, !App_correct, Q_correct, !App_correct, Lam_correct, !App_correct, Lam_correct.
Qed.

Theorem totality_hard : ~ recognisable (fun s => forall t, pi s t) /\ ~ recognisable (fun s => ~ forall t, pi s t).
Proof.
  split.
  - intros H. eapply totality.
    eapply recognisable_intersection; eauto. eapply dec_recognisable, decidable_proc.
  - eapply rec_total.
Qed.

(** ** Self-interpreter *)

Definition H s : term := Eval cbv in (.\ "y"; !E "y" !s !(lambda T) !F).
Definition U : term := Eval cbv in .\ "x"; !E !(C (H 1)) "x" !I !I.

Lemma U_rec s : U (tenc s) ≡ E (C (H (tenc s))) (tenc s) I I.
Proof.
  solvered.
Qed.

Lemma H_test s : test (H (tenc s)).
Proof.
  intros n.
  assert ((lambda (E 0 (tenc s) (lambda T) F)) (enc n) ≡ E (enc n) (tenc s) (lambda T) F) by solveeq.
  destruct (eval n s) eqn:Eq; [ left | right]; rewrite H0, E_correct, Eq; solveeq.
Qed.

Lemma H_inv n s : satis ( H (tenc s) ) n -> eval n s <> None.
Proof.
  intros. destruct (eval n s) eqn:Eq.
  - congruence.
  - exfalso.
    assert (H (tenc s) (enc n) ≡ E (enc n) (tenc s) (lambda T) F) by solvered. unfold satis in H0.
    rewrite H1, E_correct, Eq, none_correct in H0; value. inv H0.
Qed.

Lemma H_proc s : proc (H (tenc s)).
Proof.
  value.
Qed.

Lemma U_complete s t : s ▷ t -> U (tenc s) ▷ tenc t.
Proof.
  intros [n H0] % evaluates_eval. 
  rewrite U_rec. edestruct (C_complete (n := n) (H_proc s) (H_test s)) as [? []].
  - eapply evaluates_equiv; split; value.
    transitivity ( E (enc n) (tenc s) (lambda T) F). cbn. solveeq.  
    rewrite E_correct, H0. solveeq.
  - assert ((lambda (E 0 (tenc s) (lambda T) F)) (enc x) ≡ E (enc x) (tenc s) (lambda T) F) by solveeq. 
    unfold satis in H2. eapply H_inv in H2.
    destruct (eval x s) eqn:Eq.
    + enough (t = t0). subst. rewrite H1, E_correct, Eq. solveeq.
      eapply eval_evaluates, evaluates_equiv in H0.  eapply eval_evaluates, evaluates_equiv in Eq.
      eapply unique_normal_forms; firstorder. now rewrite <- H0, <- H4.
    + congruence.
Qed.

Lemma U_sound s : eva (U (tenc s)) -> eva s.
Proof with eauto.
  rewrite U_rec. intros H0.
  assert (eva (C (H (tenc s)))) by
      now eapply app_eva in H0 as [[[H % app_eva ?] %app_eva ?] %app_eva ?].
  eapply C_sound in H1 as [n H1 % H_inv].
  destruct (eval n s) eqn:Eq; try congruence. eapply eval_evaluates in Eq. firstorder. value.
  eapply H_test.
Qed.

Lemma U_eva s : eva s <-> eva (U (tenc s)).
Proof.
  split.
  - intros [v Hv % U_complete]. eauto.
  - eauto using U_sound.
Qed.

Lemma recognisable_eva : recognisable eva.
Proof.
  exists U. split; value. intros. now rewrite U_eva.
Qed.
