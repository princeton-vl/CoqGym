Require Import FcEtt.imports.


(* FIXME; instead of importing inf, import only the right metalib module *)
Require Import FcEtt.ett_inf.


(* Tactics for the project *)

(* TODO
   - automated f_equal (etc)
   - split forall ands
   - pick fresh and specialize all atom -> P hyps
   - the organization (in different tactics, etc) is probably perfectible
*)

(* Dynamic type, useful for some tactics *)
Inductive Dyn : Type := dyn : forall {T : Type}, T -> Dyn.

Ltac unwrap_dyn d :=
  match d with
    | dyn ?v => v
  end.


(* TODO: This is subsumed by pcess_hyps down there. Make sure we never need to use *specifically* this tactic, then remove it *)
Ltac split_hyp :=
  repeat (
      match goal with
        | [ H : _ /\ _ |- _ ] => destruct H
      end).



Ltac rewrite_and_clear eq :=
  first [rewrite -> eq | rewrite <- eq]; clear eq.

Ltac try_rewrite_and_clear eq :=
  first [rewrite -> ! eq | rewrite <- ! eq | idtac]; clear eq.

(* Only forward (i.e., ->) *)
Ltac try_rewrite_and_clear_f eq :=
  first [rewrite ! eq | idtac]; clear eq.

(* Integrate these in the big match below? *)
(* Find an generalized equality, rewrite it, and clear it *)
(* TODO: need much more parameters *)
Ltac find_eq_rew_clear :=
  match goal with
    | [ eq : forall t1,                _ = _ |- _ ] => rewrite_and_clear eq
    | [ eq : forall t1 t2,             _ = _ |- _ ] => rewrite_and_clear eq
    | [ eq : forall t1 t2 t3,          _ = _ |- _ ] => rewrite_and_clear eq
    | [ eq : forall t1 t2 t3 t4,       _ = _ |- _ ] => rewrite_and_clear eq
    | [ eq : forall t1 t2 t3 t4 t5,    _ = _ |- _ ] => rewrite_and_clear eq
    | [ eq : forall t1 t2 t3 t4 t5 t6, _ = _ |- _ ] => rewrite_and_clear eq
  end.


(* Tactic equivalent to subst, but which also tries to rewrite universally quantified equalities *)
(* FIXME: good name *)
Ltac subst_forall :=
  repeat find_eq_rew_clear.


(**** Solvers ****)

(* The <solve> versions are strict: they solve the goal or do nothing. The <nosolve> versions do whatever they can *)

Tactic Notation "basic_nosolve_n"     int_or_var(n) :=
  intuition (subst; eauto n).
Tactic Notation "basic_nosolve_n'"    int_or_var(n) :=
  intuition (subst; simpl in *; subst; eauto n; try done).
Tactic Notation "basic_nosolve_fo_n"  int_or_var(n) :=
  firstorder (subst; eauto n).
Tactic Notation "basic_nosolve_fo_n'" int_or_var(n) :=
  firstorder (subst_forall; simpl in *; subst_forall; eauto n; try done).

Tactic Notation "basic_solve_n"     int_or_var(n) := try solve [basic_nosolve_n     n].
Tactic Notation "basic_solve_n'"    int_or_var(n) := try solve [basic_nosolve_n'    n].
Tactic Notation "basic_solve_fo_n"  int_or_var(n) := try solve [basic_nosolve_fo_n  n].
Tactic Notation "basic_solve_fo_n'" int_or_var(n) := try solve [basic_nosolve_fo_n' n].

(* `eauto` and the like default to `5` *)
Ltac basic_nosolve     := basic_nosolve_n     5.
Ltac basic_nosolve'    := basic_nosolve_n'    5.
Ltac basic_nosolve_fo  := basic_nosolve_fo_n  5.
Ltac basic_nosolve_fo' := basic_nosolve_fo_n' 5.

Ltac basic_solve     := try solve [basic_nosolve].
Ltac basic_solve'    := try solve [basic_nosolve'].
Ltac basic_solve_fo  := try solve [basic_nosolve_fo].
Ltac basic_solve_fo' := try solve [basic_nosolve_fo'].

Ltac solve_by_inv_hyp_about A :=
  multimatch goal with
    | [ H : context [?A] |- _ ] => solve [inversion H; basic_solve]
  end.

Ltac revert_all :=
  repeat match goal with
      | [ H : _ |- _ ] => revert H
    end.

Ltac revert_all_with t :=
  repeat match goal with
      | [ H : _ |- _ ] => try t H; revert dependent H
    end.

(* TODO: use match instead to respect names *)
Ltac intro_all_with t :=
  repeat
    (let x := fresh in intro x; try (t x)).


Ltac disjunction_assumption :=
  match goal with
    | [H : ?P |- ?P]     => exact H
    | [H : ?P |- ?P ∨ _] => left; exact H
    | [       |- _  ∨ _] => right; disjunction_assumption
  end.


(* This version does NOT check if the inversion produces only one goal *)
Ltac invert_and_clear H := inversion H; clear H.


(* Technical, tactic-internal *)
Definition wrap : forall P : Prop, P -> P * True := fun _ p => (p, I).
Ltac wrap_hyp H := apply wrap in H.


(* FIXME: copying this here, temporarily *)
Lemma AnnCtx_uniq G : AnnCtx G -> uniq G.
Proof. by elim=> * //=; apply uniq_cons. Qed.

Ltac prove_this stmt name :=
(*
  let name := fresh in
*)
  match stmt with
    | uniq ?G =>
      match goal with
      | [ HG : AnnCtx G |- _ ] =>
        (* let name := fresh in *)
        move: (AnnCtx_uniq HG) => name (* ; name *)
      end
    end.


(* This tactic finds "invertible" hyps (that is, the one that, once inverted, add information without generating multiple subgoals) and invert them. They are wrapped up afterwards to
   avoid inverting them again. *)
Ltac find_invertible_hyps :=
  repeat (
  match goal with
    (* TODO: should we keep this hyp around? -> wrap *)
    | [ H : AnnIso _ _ (g_EqCong _ _ _) _ _ |- _ ] => invert_and_clear H
    (* FIXME: actually, we may just want to do the general case - check if this indeed working well, and if so delete previous line *)
    | [ H : AnnIso _ _ (_ _) _ _ |- _ ] => inversion H; wrap_hyp H

    (* Key step: invert typing hyps *)
    (* TODO: do we want to keep the original hyp - wrap - or clear it? *)
    | [ H : AnnTyping _ (_ _) _ |- _ ] => inversion H; wrap_hyp H

  (* TODO: rhochecks as well *)
  (* TODO *)
  end).


(* TODO: if we still apply the thm here, find another name *)
Ltac pair_coupled_hyps :=
  repeat match goal with
    | [ H1 : binds ?T _ ?G, H2 : binds ?T _ ?G |- _ ] =>
      let unG := fresh "uniq" G in
      prove_this (uniq G) unG;
      move: (binds_unique _ _ _ _ _ H1 H2 unG) => ?; wrap_hyp H2

  end.


(* Put hyps in a more exploitable shape *)
(* TODO: should that be called forward reasoning instead? *)
Ltac pcess_hyps :=
  find_invertible_hyps;

  pair_coupled_hyps;

  repeat (
    match goal with
      | [ H : _ /\ _       |- _ ] => destruct H

      | [ H : exists x, _  |- _ ] => destruct H

      (* For some tricks, we put hyps in this isomorphic form - pcess_hyps gets back the original hyp *)
      | [ H : _ * True  |- _      ] => destruct H as [H _]

      (* In some automation, it is hard not to generate trivial (or already obtained) facts. We make sure here to remove such useless hyps *)
      | [ H :                   ?A = ?A |- _ ] => clear H
      | [ H : forall _,         ?A = ?A |- _ ] => clear H
      | [ H : forall _ _,       ?A = ?A |- _ ] => clear H
      | [ H : forall _ _ _,     ?A = ?A |- _ ] => clear H
      | [ H : forall _ _ _ _,   ?A = ?A |- _ ] => clear H
      | [ H : forall _ _ _ _ _, ?A = ?A |- _ ] => clear H
      (* Removing redundant hyps *)
      | [ H : ?P |- _ ] => clear H; let x := fresh in assert (x : P) by solve [assumption | trivial]; clear x

      (* Basic injection code. We rely on the redundant hyps removal *)
      | [ H : ?C _                         = ?C _                         |- _ ] => injection H; clear H; intros; try subst
      | [ H : ?C _ _                       = ?C _ _                       |- _ ] => injection H; clear H; intros; try subst
      | [ H : ?C _ _ _                     = ?C _ _ _                     |- _ ] => injection H; clear H; intros; try subst
      | [ H : ?C _ _ _ _                   = ?C _ _ _ _                   |- _ ] => injection H; clear H; intros; try subst
      | [ H : ?C _ _ _ _ _                 = ?C _ _ _ _ _                 |- _ ] => injection H; clear H; intros; try subst
      | [ H : ?C _ _ _ _ _ _               = ?C _ _ _ _ _ _               |- _ ] => injection H; clear H; intros; try subst
      | [ H : ?C _ _ _ _ _ _ _             = ?C _ _ _ _ _ _ _             |- _ ] => injection H; clear H; intros; try subst
      | [ H : ?C _ _ _ _ _ _ _ _           = ?C _ _ _ _ _ _ _ _           |- _ ] => injection H; clear H; intros; try subst
      | [ H : ?C _ _ _ _ _ _ _ _ _         = ?C _ _ _ _ _ _ _ _ _         |- _ ] => injection H; clear H; intros; try subst
      | [ H : ?C _ _ _ _ _ _ _ _ _ _       = ?C _ _ _ _ _ _ _ _ _ _       |- _ ] => injection H; clear H; intros; try subst
      | [ H : ?C _ _ _ _ _ _ _ _ _ _ _     = ?C _ _ _ _ _ _ _ _ _ _ _     |- _ ] => injection H; clear H; intros; try subst
      | [ H : ?C _ _ _ _ _ _ _ _ _ _ _ _   = ?C _ _ _ _ _ _ _ _ _ _ _ _   |- _ ] => injection H; clear H; intros; try subst
      | [ H : ?C _ _ _ _ _ _ _ _ _ _ _ _ _ = ?C _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ ] => injection H; clear H; intros; try subst


    end).

Ltac pre :=
  repeat (intros; try split);
  (*split_hyp;*)
  unfold "~" in *.

Ltac pre' :=
  repeat (intros; try split);
  pcess_hyps;
  unfold "~" in *.


Ltac prove_eq_same_head :=
  solve [subst; reflexivity | f_equal; basic_solve].


(* Ad-hoc version of fsetdec, hopefully faster *)
(* TODO: handle the subset-union cases (see fc_dec.v) *)
Ltac break_union :=
  repeat match goal with
  (* TODO: see if there are other common cases we could solve here *)
    | [ H : ~ ?x `in` union _ _ |- _ ] =>
        move: (notin_union_1 _ _ _ H) (notin_union_2 _ _ _ H) => ??; clear H
  end.

Ltac fsetdec_fast := solve [break_union; basic_solve_n 3].

Ltac autofresh_fixed x :=
   repeat match goal with
     | [ H : ∀ x' : atom, x' `notin` ?L -> _ |- _] =>
       let xL := fresh x L in
       (have xL : x `notin` L by first [fsetdec_fast | fsetdec]);
       specialize (H x xL);
       clear xL (* Clear specialized freshness assumptions *)
   end.

 (* General version that picks up a fresh variable instead *)
 Ltac autofresh :=
   let x := fresh "x" in
   pick fresh x;
   autofresh_fixed x.



(* General purpose automation tactic, tailored for this development *)
Ltac autotype :=
  pcess_hyps;

(* TODO: can use exactly once for inversions *)
(* TODO: integrate the relevant ad-hoc tactics declared in different files *)
  repeat match goal with
    | [ |- _ /\ _ ] => split

    | [ |- _ `in` _   ] => try fsetdec_fast; first [fsetdec | fail 2] (* We force failure if fsetdec can not solve this goal (there shouldn't be cases where other tactics can solve it) *)
    | [ |- ¬ _ `in` _ ] => try fsetdec_fast; first [fsetdec | fail 2]


    | [ |- _ [=] _  ] => first [fsetdec | fail 2]
    | [ |- _ [<=] _ ] => first [fsetdec | fail 2]


    | [ |- ?C _                         = ?C _                         ] => prove_eq_same_head
    | [ |- ?C _ _                       = ?C _ _                       ] => prove_eq_same_head
    | [ |- ?C _ _ _                     = ?C _ _ _                     ] => prove_eq_same_head
    | [ |- ?C _ _ _ _                   = ?C _ _ _ _                   ] => prove_eq_same_head
    | [ |- ?C _ _ _ _ _                 = ?C _ _ _ _ _                 ] => prove_eq_same_head
    | [ |- ?C _ _ _ _ _ _               = ?C _ _ _ _ _ _               ] => prove_eq_same_head
    | [ |- ?C _ _ _ _ _ _ _             = ?C _ _ _ _ _ _ _             ] => prove_eq_same_head
    | [ |- ?C _ _ _ _ _ _ _ _           = ?C _ _ _ _ _ _ _ _           ] => prove_eq_same_head
    | [ |- ?C _ _ _ _ _ _ _ _ _         = ?C _ _ _ _ _ _ _ _ _         ] => prove_eq_same_head
    | [ |- ?C _ _ _ _ _ _ _ _ _ _       = ?C _ _ _ _ _ _ _ _ _ _       ] => prove_eq_same_head
    | [ |- ?C _ _ _ _ _ _ _ _ _ _ _     = ?C _ _ _ _ _ _ _ _ _ _ _     ] => prove_eq_same_head
    | [ |- ?C _ _ _ _ _ _ _ _ _ _ _ _   = ?C _ _ _ _ _ _ _ _ _ _ _ _   ] => prove_eq_same_head
    | [ |- ?C _ _ _ _ _ _ _ _ _ _ _ _ _ = ?C _ _ _ _ _ _ _ _ _ _ _ _ _ ] => prove_eq_same_head


    | _ => try done; basic_solve; fail 0


    | [ |- ex _ ] => eexists


    (* FIXME: need to backtrack if that doesn't work *)
    (* FIXME: have a "pre" or so *)
    | [ |- AnnTyping _   (_ _) _   ] => econstructor; pcess_hyps
    | [ |- AnnDefEq  _ _ (_ _) _ _ ] => econstructor; pcess_hyps
    | [ |- AnnIso    _ _ (_ _) _ _ ] => econstructor; pcess_hyps
  end.

(**** Alias for manual proofs ****)
Ltac ok := autotype.
Ltac depind x := dependent induction x.
