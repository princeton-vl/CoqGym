From Undecidability.L Require Export L.

(** * Automation for equivalences and reductions *)
(** ** Tactics for closedness and abstractions *)

Lemma proc_closed p : proc p -> closed p.
Proof.
  firstorder intuition.
Qed.

Lemma proc_lam p : proc p -> lam p.
Proof.
  firstorder intuition.
Qed.

Hint Resolve proc_closed proc_lam : cbv.

Ltac value_context := try now
  match goal with
  | |- bound _ ?t = true =>
    eapply bound_ge with (k := 0); [ change (closed t); auto 3 with cbv | omega ]
  end.

Ltac dvalue' :=
  match goal with
  (* | |- rClosed ?phi _ => now (apply rClosed_decb_correct;[assumption|vm_compute;reflexivity]) *)
    | |- closed _ => cbn; unfold closed
    | |- bound _ (if ?c then _ else _) = true => destruct c
    | |- bound _ (L.var _) = true => now constructor;omega
    | |- bound _ (L.app _ _) = true => constructor
    | |- bound _ (L.lambda _) = true => constructor
    | |- bound ?s _ = true => value_context || (unfold s;simpl)
    | |- context [ andb _ _ ] => rewrite Bool.andb_true_r; dvalue'
    | |-  andb _ _ = _ => eapply Bool.andb_true_iff; split; dvalue'
  end.
Ltac dvalue := (try (progress unfold convert;cbv -[bound]; cbn)); repeat dvalue'; try (cbn; repeat dvalue').



Ltac value' :=
  match goal with
    | [ |- proc _ ] => (try eassumption; auto 3 with cbv; split; value')
    | [ |- lam _ ] => (try eassumption; auto 3 with cbv; eexists; reflexivity)
    | [ |- lam (if ?c then _ else _) ] => destruct c;(try eassumption; auto 3 with cbv; eexists; reflexivity)

    | [ |- closed _ ] => (try eassumption; auto 3 with cbv; value_context); dvalue
    | [ |-  _ ] => idtac
  end (*|| value*).

Tactic Notation "value" := value'.

Lemma beta s t u : lam u -> subst s 0 u = t -> (lambda s) u ≻ t.
Proof.
  intros.  destruct H. subst. econstructor.
Qed.

Tactic Notation "rewrite_cls" open_constr(t) :=
      let H := fresh "H" in
      enough (H : closed t); [rewrite (closed_subst _ _ H) | value]; clear H.

Ltac rewrite_closed := repeat   match goal with
  | [ |- context [subst ?s _ _] ] => rewrite_cls s
  end.

(** ** Tactics to solve equivalences and reductions *)

Lemma rho_correct s t : proc s -> proc t -> rho s t ≻* s (rho s) t.
Proof.
  intros. econstructor. eapply beta. value. cbn. rewrite_closed. reflexivity.
  repeat (do 3  econstructor ; eapply beta;  value; try now reflexivity).
Qed.

Hint Resolve rho_lam rho_closed : cbv.

Ltac recStep id :=
  unfold id; rewrite rho_correct;[fold id;simpl|(split;[vm_compute;reflexivity|value])|now value].

Lemma equiv_R_trans s s' t : s ≻ s' -> s' ≡ t -> s ≡ t.
Proof. intros H1 H2. etransitivity. econstructor; eassumption. eassumption. Qed.

Ltac dobeta := match goal with
               | [ |- _ ≡ _ ] => eapply equiv_R_trans; [ eapply beta; value;  cbn; now rewrite_closed | ]
               | [ |- _ ≻* _ ] => eapply star_step; [ eapply beta; value;  cbn; now rewrite_closed | ]
               | [ |- _ ≻ _ ] => eapply beta; value; cbn; now rewrite_closed
               end.


Lemma star_trans_l s s' t : s ≻* s' -> s t ≻* s' t.
Proof. intros H. now rewrite H. Qed.


Lemma star_trans_r (s t t' : term) : t ≻* t' -> s t ≻* s t'.
Proof. intros H. now rewrite H. Qed.


Lemma equiv_trans_l s s' t : s ≡ s' -> s t ≡ s' t.
Proof. intros H. now rewrite H. Qed.


Lemma equiv_trans_r (s t t' : term) : t ≡ t' -> s t ≡ s t'.
Proof. intros H. now rewrite H. Qed.


Ltac doleft := match goal with
               | [ |- _ ≡ _ ] => etransitivity; [ (eapply equiv_trans_l) |]
               | [ |- _ ≻* _ ] => etransitivity; [ (eapply star_trans_l) | ]
               | [ |- _ ≻ _ ] => eapply stepAppL
               end.

Ltac doright := match goal with
               | [ |- _ ≡ _ ] => etransitivity; [ (eapply equiv_trans_r) |]
               | [ |- _ ≻* _ ] => etransitivity; [ (eapply star_trans_r) | ]
               | [ |- _ ≻ _ ] => eapply stepAppR
                end.

Ltac redL := let H := fresh "H" in unfold closed;
             match goal with
             | _ => etransitivity; [ eassumption | ]
             | [ |- ?G] => tryif has_evar G then fail else reflexivity
             | [ |- _ (app ?s ?t) _ ] => tryif (assert (H : lam s) by value; clear H) then (tryif (assert (H : lam t) by value; clear H) then
                                                                                            dobeta
                                                                                          else
                                                                                            doright)
               else doleft      (* TODO: Check wether the _ as first match parameter is slow *)
             | _ => reflexivity
             end.

Ltac simplify_goal := try repeat match goal with
                           | [ |- _ ▷ _ ] => eapply evaluates_equiv; split; value
                           | [ H : _ ▷ _ |- _ ] => eapply evaluates_equiv in H as []
               end.
Ltac solveeq := simplify_goal; now repeat redL.
Ltac solvered := solveeq.


Definition Y : term := Eval cbn in .\ "f"; (.\ "x"; "f" ("x" "x")) (.\ "x"; "f" ("x" "x")).

Lemma Y_spec u : proc u -> Y u ≡ u (Y u).
Proof.
  intros.
  assert (Y u ≡ (lambda (u (O 0))) (lambda (u (O 0)))) as -> by solveeq.
  solvered.
Qed.
