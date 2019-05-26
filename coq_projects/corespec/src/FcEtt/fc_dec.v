Require Import FcEtt.sigs.

Require Import FcEtt.fc_dec_fuel.
Require Import FcEtt.fc_dec_fun.
Require Import FcEtt.fc_dec_aux.

Require Import FcEtt.imports.
(* Require Export FcEtt.ett_inf_cs. *)
Require Import FcEtt.ett_ind.
Require Export FcEtt.fc_invert.

Require Import Coq.Init.Specif.
Require Import Coq.micromega.Lia.

Module fc_dec (wf : fc_wf_sig) (weak : fc_weak_sig) (subst : fc_subst_sig) (unique: fc_unique_sig).

Module invert := fc_invert wf weak subst.
Module fuel := fc_dec_fuel wf weak subst unique.
Module tc_fun := fc_dec_fun wf weak subst unique.
Module aux := fc_dec_aux wf weak subst unique.

Import tc_fun fuel aux unique wf subst invert.



Definition fuel_at n : Type :=
    (∀ a, size_tm a <= n ->  fuel_tpg a) *
    (∀ phi, size_constraint phi <= n -> fuel_pwf phi) *
    (∀ gamma, size_co gamma <= n -> fuel_iso gamma) *
    (∀ gamma, size_co gamma <= n -> fuel_deq gamma).





Ltac wfind :=
  match goal with
    | [ Hind: ∀ z : nat, z < ?x → fuel_at z |- fuel_tpg ?a ] => eapply (Hind (size_tm a))
    | [ Hind: ∀ z : nat, z < ?x → fuel_at z |- fuel_deq ?g ] => eapply (Hind (size_co g))
    | [ Hind: ∀ z : nat, z < ?x → fuel_at z |- fuel_iso ?g ] => eapply (Hind (size_co g))
    | [ Hind: ∀ z : nat, z < ?x → fuel_at z |- fuel_pwf ?g ] => eapply (Hind (size_constraint g))
  end.



Lemma fuel_all : ∀ n, fuel_at n.
Proof.
  intro n. eapply (well_founded_induction_type lt_wf). clear n. intros.
  repeat split.
  + intros a sz.
    destruct a; auto; unfold size_tm in sz; fold size_tm in sz; fold size_co in sz; fold size_constraint in sz.

    all: try econstructor; intros.
    all: try wfind.
    all: try rewrite size_tm_open_tm_wrt_tm_var; try rewrite size_tm_open_tm_wrt_co_var.
    all: try lia.

  + intros phi sz.
    destruct phi; auto; unfold size_constraint in sz; fold size_tm in sz; fold size_co in sz; fold size_constraint in sz.
    econstructor; intros.
    all: wfind.
    all: try lia.

  + intros g sz.
    destruct g; auto; unfold size_co in sz; unfold size_tm in sz; fold size_tm in sz; fold size_co in sz; fold size_constraint in sz.
(*
    Focus 5.
    apply FD_Left.
*)

    all: try econstructor; intros.
    all: try wfind.
    all: try rewrite size_tm_open_tm_wrt_tm_var; try rewrite size_tm_open_tm_wrt_co_var.
    all: try lia.



  + intros g sz.
    destruct g; auto; unfold size_co in sz; unfold size_tm in sz; fold size_tm in sz; fold size_co in sz; fold size_constraint in sz.
    all: econstructor; intros.
    all: try wfind.
    all: try
      solve [ lia
            | rewrite size_co_open_co_wrt_co_var; lia
            | rewrite size_tm_open_tm_wrt_co_var; lia
            | rewrite size_co_open_co_wrt_tm_var; lia
            | rewrite size_tm_open_tm_wrt_tm_var; lia].
Qed.


Definition gaspump : ∀ t : tm, fuel_tpg t.
Proof.
  move => t.
  move: (fuel_all (size_tm t)) => f.
  do 3 move: f => [f _].
  apply f.
  done.
Qed.

(* TODO: as added bonus, make the function that generates context fuel and write the general function (the one accepting an arbitrary context) *)
Definition FC_typechecker : ∀ t : tm, {T : tm | AnnTyping nil t T } + {(forall T, ¬ AnnTyping nil t T)} :=
  fun t => AnnTyping_dec nil t (gaspump t) An_Empty.

Theorem FC_typechecking_decidable : ∀ t : tm, (exists T : tm, AnnTyping nil t T) \/ (∀ T, ¬ AnnTyping nil t T).
Proof.
  intros t.
  case: (FC_typechecker t).
  - intros [T p]. left. exists T. exact p.
  - intros n. right. intros T. apply n.
Qed.

End fc_dec.
