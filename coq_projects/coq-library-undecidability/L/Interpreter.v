From Undecidability.L Require Export L.

(** * Step-indexed interpreter and modesty *)

(** ** Step-indexed interpreter *)

Fixpoint eval (n : nat) (u : term) :=
  match u with
  | var n => None
  | lambda s => Some (lambda s)
  | app s t => match n with 
           | 0   => None
           | S n => match eval n s, eval n t with
                    | Some (lambda s), Some t => eval n (subst s 0 t)
                    |   _ , _ => None
                    end
            end
  end.

Lemma eval_S n s t : eval n s = Some t -> eval (S n) s = Some t.
Proof.
  revert s t; induction n; intros; cbn in H;
    repeat (destruct _ eqn:_; subst; try congruence; eauto).
    remember (S n) as n'; cbn; subst.
    now rewrite (IHn _ _ E), (IHn _ _ E0), (IHn _ _ H).
Qed.

Lemma eval_step s s' t n : s ≻ s' -> eval n s' = Some t -> eval (S n) s = Some t.
Proof.
  revert s s' t; induction n; intros.
  - cbn in H0. destruct _; inv H0.
    cbn. destruct _; inv H. now rewrite H3.
  - cbn in H0. inv H; repeat (destruct _ eqn:_; subst; try congruence).
    + cbn; now rewrite E, E0, E1.
    + cbn; now rewrite E.
    + remember (S n); cbn; subst.
      erewrite eval_S, IHn; eauto. now eapply eval_S.
    + remember (S n). cbn. subst.
      erewrite IHn, eval_S; eauto. now eapply eval_S.
Qed.

Lemma evaluates_eval s t : evaluates s t -> exists n, eval n s = Some t.
Proof.
  intros [A B] % evaluates_equiv. eapply equiv_star_lam in A; eauto. induction A.
  - destruct B. subst; now exists 0.    
  - destruct (IHA B) as [k C]. eauto using eval_step.
Qed.

Lemma eval_evaluates n s t : eval n s = Some t -> evaluates s t.
Proof.
  revert s t; induction n; intros.
  - inv H. destruct _; try congruence. inv H1. firstorder.
  - inv H. repeat (destruct _ eqn:_; subst; try congruence).
    eapply IHn in E. eapply IHn in E0. eapply IHn in H1. eauto. inv H1. eauto.
Qed.

Lemma equiv_eval s t : lam t -> s ≡ t -> exists n, eval n s = Some t.
Proof.
  intros. eapply evaluates_eval. firstorder using evaluates_equiv.
Qed.

Lemma eval_equiv s s' n : eval n s = Some s' -> s ≡ s'.
Proof.
  intros ? % eval_evaluates. firstorder using evaluates_equiv.
Qed.

Lemma eval_lambda n s t : eval n s = Some t -> lam t.
Proof.
  intros ? % eval_evaluates. firstorder using evaluates_equiv.
Qed.

(** ** Modesty *)

Require Import DecidableRecognisable Encodings Coq.Logic.ConstructiveEpsilon.

Definition cChoice := constructive_indefinite_ground_description_nat_Acc.
Lemma computable_eva s : eva s -> { v | s ▷ v }.
Proof.
  intros.
  assert (exists n v, eval n s = Some v) by (destruct H as (? & ? % evaluates_eval); firstorder).
  eapply cChoice in H0 as []. destruct (eval x s) eqn:E.
  - exists t. eauto using eval_evaluates.
  - exfalso. firstorder congruence.
  - intros. destruct (eval n s). eauto.
    right. intros []. congruence.
Defined.

Lemma dec_pdec p : decidable p -> forall x, p x \/ ~ p x.
Proof.
  firstorder.
Qed.

Lemma decidable_dec p : decidable p -> exists f, forall s, f s = true <-> p s.
Proof with try tauto; try (eexists; reflexivity).
  intros (u & proc_u & Hu).
  assert (forall s, {v | u (tenc s) ▷ v}). {
    intros. eapply computable_eva. destruct (Hu s). exists T. tauto.
    exists F; tauto.
  }

  exists (fun s =>  let (v, _) := H s in if decision (v = T) then true else false).

  intros. destruct _. decide (x = T).
  - subst. firstorder. eapply decidable_spec; eauto.
  - firstorder. congruence. exfalso. eapply decidable_spec; eauto.
    destruct (Hu s) as [ [? [H4 ?] %evaluates_equiv] | []].
    destruct T_equiv_F.
    assert (x ≡ T) by now rewrite <- e, <- H4. eapply unique_normal_forms in H6. subst. congruence.
    eapply evaluates_abst; eauto. value. firstorder using evaluates_equiv.
Qed.

Fixpoint unenc s :=
match s with
| lambda (lambda 1) => Some 0
| lambda (lambda (app 0 s)) => match unenc s with Some n => Some (S n) | x=>x end
| _ => None
end.

Lemma unenc_correct m : (unenc (enc m)) = Some m.
Proof.
  induction m; simpl; now try rewrite IHm.
Qed.

Lemma unenc_correct2 t n : unenc t = Some n -> enc n = t.
Proof.
  revert n. eapply (size_induction (f := size) (p := (fun t => forall n, unenc t = Some n -> enc n = t))). clear t. intros t IHt n H.
  destruct t; try now inv H.
  destruct t; try now inv H.
  destruct t; try now inv H.
  destruct n0; try now inv H. destruct n0; try now inv H.
  destruct t1; try now inv H. destruct n0; try now inv H.
  simpl in H. destruct (unenc t2) eqn:A.
  specialize (IHt t2).
  assert (B : size t2 < size (lambda (lambda 0 t2))). simpl. omega.
  eapply IHt in B.
  destruct n. inv H. inversion H. subst n0.
    simpl. repeat f_equal. eassumption. eassumption. inv H.
Qed.

Fixpoint decode (s : term) :=
  match s with
  | lambda (lambda (lambda (app (var 2) t))) => match unenc t with Some n => Some (var n) | None => None end
  | lambda (lambda (lambda (app (app (var 1) s) t))) => match decode s, decode t with
                        | Some s, Some t => Some (s t)
                        | _, _ => None
                        end
  | lambda (lambda (lambda (app (var 0) s))) => match decode s with
                      | Some s => Some (lambda s)
                      | None => None
                                end
  | _ => None
  end.

Lemma decode_correct t : (decode (tenc t)) = Some t.
Proof.
  induction t; simpl.
  - now rewrite unenc_correct.
  - now rewrite IHt1, IHt2.
  - now rewrite IHt.
Qed.

Lemma decode_correct2 s t :
  decode s = Some t -> tenc t = s.
Proof.
  revert t. eapply (size_induction (f := size) (p := (fun s => forall t, decode s = Some t -> tenc t = s))).
  clear s. intros s IHs t H.
  destruct s; try now inv H.
  destruct s; try now inv H.
  destruct s; try now inv H.
  destruct s; try now inv H.
  destruct s1; try now inv H.
  destruct n as [ | [ | [] ] ]; try now inv H.
  - cbn in *. destruct (decode s2) eqn:E; inv H.
    eapply IHs in E; try omega. cbn. now rewrite E.
  - cbn in *. destruct (unenc s2) eqn:E; inv H.
    eapply unenc_correct2 in E. now rewrite <- E.
  - destruct s1_1; try now inv H. destruct n as [ | [] ]; try now inv H.
    cbn in *. destruct _ eqn:E1; inv H. destruct _ eqn:E2; inv H1. eapply IHs in E1; try omega.
    eapply IHs in E2; try omega. cbn. now rewrite <- E1, <- E2.
Qed.

Lemma L_computable_computable u :
  (forall s, exists t, u (tenc s) ▷ tenc t) -> { f | forall s, u (tenc s) ▷ tenc (f s)}.
Proof.
  intros H.
  assert (forall s, eva (u (tenc s))). intros. destruct (H s) as [t H1]. eauto.
  exists (fun s => match decode (proj1_sig (computable_eva (H0 s))) with Some t => t | None => 0 end).

  intros s.
  destruct (H s) as [t Ht].
  destruct computable_eva. cbn.
  enough (x = tenc t).
  - subst. now erewrite decode_correct.
  - eapply unique_normal_forms. now eapply evaluates_abst in e. value.
    now rewrite <- Ht, <- e.
Defined.
