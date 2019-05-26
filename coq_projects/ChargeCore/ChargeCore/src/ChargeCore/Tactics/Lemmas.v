(* This file contains lemmas used by other pieces of the automation,
 * e.g. ChargeCore.Tactics.Tauto. It is a separate file so that
 * it does not pollute the global namespace when those modules are imported.
 *)
Require Export ChargeCore.Logics.ILogic.

Section logic.
  Context {L : Type}.
  Context {ILO : ILogicOps L}.
  Context {IL : ILogic L}.

  Theorem lcut : forall P Q R : L,
      P |-- R ->
      P |-- R -->> Q ->
      P |-- Q.
  Proof.
    intros.
    eapply landAdj in H0.
    etransitivity; [ | eassumption ].
    eapply landR. reflexivity. assumption.
  Qed.

  Theorem limplAdj_true : forall P Q,
      P |-- Q ->
      ltrue |-- P -->> Q.
  Proof.
    intros. apply limplAdj. apply landL2. assumption.
  Qed.

  Theorem landAdj_true : forall P Q,
      ltrue |-- P -->> Q ->
      P |-- Q.
  Proof.
    intros. apply landAdj in H. rewrite <- H.
    apply landR. apply ltrueR. reflexivity.
  Qed.

  Lemma lapply : forall P Q R,
      P |-- Q -->> R ->
      P |-- Q ->
      P |-- R.
  Proof. intros; eapply lcut; eauto. Qed.

  Lemma lapply2 : forall P Q R S,
      P |-- Q -->> R -->> S ->
      P |-- Q ->
      P |-- R ->
      P |-- S.
  Proof. intros; eapply lcut; eauto using lapply. Qed.

  Lemma lapply3 : forall P Q R S T,
      P |-- Q -->> R -->> S -->> T ->
      P |-- Q ->
      P |-- R ->
      P |-- S ->
      P |-- T.
  Proof. intros; eapply lcut; eauto using lapply2. Qed.

  Lemma lapply4 : forall P Q R S T U,
      P |-- Q -->> R -->> S -->> T -->> U ->
      P |-- Q ->
      P |-- R ->
      P |-- S ->
      P |-- T ->
      P |-- U.
  Proof. intros; eapply lcut; eauto using lapply3. Qed.

  Lemma lapply5 : forall P Q R S T U V,
      P |-- Q -->> R -->> S -->> T -->> U -->> V ->
      P |-- Q ->
      P |-- R ->
      P |-- S ->
      P |-- T ->
      P |-- U ->
      P |-- V.
  Proof. intros; eapply lcut; eauto using lapply4. Qed.

  Lemma land_lor_distr_L : forall P Q R,
      P //\\ (Q \\// R) -|- (P //\\ Q) \\// (P //\\ R).
  Proof.
    intros. split.
    { rewrite landC. apply landAdj.
      apply lorL; apply limplAdj.
      { apply lorR1. rewrite landC. reflexivity. }
      { apply lorR2. rewrite landC. reflexivity. } }
    { apply lorL; apply landR; try solve [ apply landL1 ; reflexivity ].
      { apply lorR1. apply landL2. reflexivity. }
      { apply lorR2. apply landL2. reflexivity. } }
  Qed.

  Lemma land_lor_distr_R : forall P Q R,
      (Q \\// R) //\\ P -|- (P //\\ Q) \\// (P //\\ R).
  Proof.
    intros. split.
    { apply landAdj.
      apply lorL; apply limplAdj.
      { apply lorR1. rewrite landC. reflexivity. }
      { apply lorR2. rewrite landC. reflexivity. } }
    { apply lorL; apply landR; try solve [ apply landL1 ; reflexivity ].
      { apply lorR1. apply landL2. reflexivity. }
      { apply lorR2. apply landL2. reflexivity. } }
  Qed.

End logic.

(* Local definitions, for proving subsequent lemmas. *)
Local Ltac charge_split := apply landR.

Local Ltac charge_search_prems found :=
  match goal with
  | |- ?X |-- ?Y =>
    solve [ found
          | apply landL1 ; charge_search_prems found
          | apply landL2 ; charge_search_prems found ]
  end.

Local Ltac charge_assumption :=
  charge_search_prems reflexivity.

Local Ltac charge_intro :=
  first [ apply lforallR; intro
        | apply limplAdj_true
        | apply limplAdj ].

Local Ltac charge_intros :=
  repeat match goal with
         | |- _ |-- _ -->> _ =>
           charge_intro
         | |- _ |-- @lforall _ _ _ _ =>
           charge_intro
         end.

Local Ltac charge_trivial := apply ltrueR.

Local Ltac charge_use :=
  first [ eapply lapply; [ charge_assumption | ]
        | eapply lapply2; [ charge_assumption | | ]
        | eapply lapply3; [ charge_assumption | | | ]
        | eapply lapply4; [ charge_assumption | | | | ]
        | eapply lapply5; [ charge_assumption | | | | | ] ].

Local Ltac ends_with H ABC C :=
  let rec go k ABC :=
      match ABC with
      | C => k
      | _ -->> ?BC =>
        let k' := (k; first [ apply landAdj_true in H | apply landAdj in H ]) in
        go k' BC
      end
  in
  go ltac:(idtac) ABC.

Local Ltac charge_apply H :=
  match type of H with
  | _ |-- ?X =>
    match goal with
    | |- _ |-- ?Y =>
      ends_with H X Y ; etransitivity ; [ | eapply H ]
    end
  end.

Local Ltac charge_tauto :=
  repeat charge_split ;
  solve [ charge_assumption
        | charge_trivial
        | charge_intro; repeat charge_intro; charge_tauto
        | charge_split; solve [ charge_tauto ]
        | match goal with
          | H : _ |-- _ |- _ =>
            charge_apply H ; charge_tauto
          end
        | charge_use ; charge_tauto ].

Section logic2.
  Context {L : Type}.
  Context {ILO : ILogicOps L}.
  Context {IL : ILogic L}.

  Definition liff (A B : L) : L :=
    (A -->> B) //\\ (B -->> A).

  Local Notation "x <<-->> y" := (liff x y) (at level 78).

  Lemma ltrue_liff : forall A B,
      |-- A <<-->> B <-> A -|- B.
  Proof.
    unfold liff. split.
    { intros. split.
      { apply landAdj_true.
        rewrite H. apply landL1. reflexivity. }
      { apply landAdj_true.
        rewrite H. apply landL2. reflexivity. } }
    { intro. rewrite H.
      apply landR; apply limplAdj_true; reflexivity. }
  Qed.

  Lemma land_cancel : forall A B C,
      A |-- B <<-->> C ->
      A //\\ B -|- A //\\ C.
  Proof.
    intros. split.
    { charge_split; try charge_tauto.
      rewrite H. charge_tauto. }
    { charge_split; try charge_tauto.
      rewrite H. charge_tauto. }
  Qed.

  Lemma uncurry : forall P Q R,
      (P //\\ Q -->> R) -|- (P -->> Q -->> R).
  Proof.
    intros. split.
    { charge_tauto. }
    { charge_intro.
      eapply lapply. eapply lapply. charge_assumption.
      charge_tauto. charge_tauto. }
  Qed.

  Lemma forget_prem : forall P Q,
      |-- P -> Q |-- P.
  Proof. intros; charge_tauto. Qed.

  Lemma lrevert : forall P Q,
      |-- P -->> Q ->
      P |-- Q.
  Proof. intros; charge_tauto. Qed.

  Lemma charge_and_use : forall P Q C,
      C |-- P ->
      C //\\ P |-- Q ->
      C |-- P //\\ Q.
  Proof.
    intros. charge_tauto.
  Qed.

  Lemma land_limpl_specialize_ap : forall P Q L R G,
      L //\\ R |-- P ->
      L //\\ Q //\\ R |-- G ->
      L //\\ (P -->> Q) //\\ R |-- G.
  Proof.
    intros. charge_tauto.
  Qed.

  Lemma land_limpl_specializeR_ap : forall P Q R G,
      R |-- P ->
      Q //\\ R |-- G ->
      (P -->> Q) //\\ R |-- G.
  Proof.
    intros; charge_tauto.
  Qed.

  Lemma land_limpl_specializeL_ap : forall P Q R G,
      R |-- P ->
      Q //\\ R |-- G ->
      R //\\ (P -->> Q) |-- G.
  Proof.
    intros; charge_tauto.
  Qed.

  Lemma landA_ap : forall P Q R G,
      (P //\\ Q) //\\ R |-- G ->
      P //\\ Q //\\ R |-- G.
  Proof.
    intros. charge_tauto.
  Qed.

  Lemma land_lexists_ap : forall T (P : T -> L) Q R S,
      (forall x, S //\\ P x //\\ Q |-- R) ->
      S //\\ (lexists P) //\\ Q |-- R.
  Proof.
    intros. rewrite landC. rewrite landA.
    eapply landAdj.
    apply lexistsL.
    intro. specialize (H x).
    charge_tauto.
  Qed.

  Lemma land_lexistsL_ap : forall T (P : T -> L) R S,
      (forall x, S //\\ P x |-- R) ->
      S //\\ (lexists P) |-- R.
  Proof.
    intros. rewrite landC.
    eapply landAdj.
    apply lexistsL.
    intro. specialize (H x).
    charge_tauto.
  Qed.

  Lemma land_lexistsR_ap : forall T (P : T -> L) R S,
      (forall x, P x //\\ S |-- R) ->
      lexists P //\\ S |-- R.
  Proof.
    intros.
    eapply landAdj.
    apply lexistsL.
    intro. specialize (H x).
    charge_tauto.
  Qed.

End logic2.

Notation "x <<-->> y" := (liff x y) (at level 78).
