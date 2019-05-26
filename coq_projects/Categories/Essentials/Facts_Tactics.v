From Categories Require Import Essentials.Notations.
From Categories Require Import Essentials.Types.

Require Export Coq.Program.Tactics.
Require Export Coq.Program.Equality.
Require Export Coq.Logic.FunctionalExtensionality.
Require Export Coq.Logic.ProofIrrelevance.

Definition equal_f : ∀ {A B : Type} {f g : A → B}, f = g → ∀ x : A, f x = g x.
Proof.
  intros A B f g H x.
  destruct H; reflexivity.
Defined.

Definition f_equal : ∀ (A B : Type) (f : A → B) (x y : A), x = y → f x = f y.
Proof.
  intros A B f x y H.
  destruct H; reflexivity.
Defined.

Arguments f_equal [_ _] _ [_ _] _.

Ltac basic_simpl :=
  let simpl_prod _ :=
      match goal with
        [H : prod _ _ |- _] =>
        let H1 := fresh H "1" in
        let H2 := fresh H "2" in
        destruct H as [H1 H2]
      end
  in
  let simpl_sig _ :=
      match goal with
        [H : @sig _ _ |- _] =>
        let H1 := fresh H "1" in
        let H2 := fresh H "2" in
        destruct H as [H1 H2]
      end
  in
  let basic_simpl_helper _ :=
      cbn in *; intros;
        repeat simpl_prod tt;
        repeat simpl_sig tt
  in
  repeat basic_simpl_helper tt
.

Global Obligation Tactic := basic_simpl; auto.

(** A tactic to apply proof irrelevance on all proofs of the same type in the
 context. *)
Ltac PIR :=
  let pir_helper _ :=
      match goal with
      |[H : ?A, H' : ?A|- _] =>
       match type of A with
       | Prop =>
         destruct (proof_irrelevance _ H H')
       end
      end
  in
  repeat pir_helper tt
.

(** A tactic to eliminate equalities in the context. *)
Ltac ElimEq := repeat match goal with [H : _ = _|- _] => destruct H end.

Hint Extern 1 => progress ElimEq.

(** A tactic to simplify terms before rewriting them. *)

Ltac cbn_rewrite W :=
  let H := fresh "H" in
  set (H := W); cbn in H; rewrite H; clear H
.

Ltac cbn_rewrite_in W V :=
  let H := fresh "H" in
  set (H := W); cbn in H; rewrite H in V; clear H
.

Ltac cbn_rewrite_back W :=
  let H := fresh "H" in
  set (H := W); cbn in H; rewrite <- H; clear H
.

Ltac cbn_rewrite_back_in W V :=
  let H := fresh "H" in
  set (H := W); cbn in H; rewrite <- H in V; clear H
.

Tactic Notation "cbn_rewrite" constr(W) := cbn_rewrite W.
Tactic Notation "cbn_rewrite" constr(W) "in" hyp_list(V) := cbn_rewrite_in W V.
Tactic Notation "cbn_rewrite" "<-" constr(W) := cbn_rewrite_back W.
Tactic Notation "cbn_rewrite" "<-" constr(W) "in" hyp_list(V) := cbn_rewrite_back_in W V.

(** Equality on sigma type under proof irrelevance *)

Lemma sig_proof_irrelevance {A : Type} (P : A → Prop) (X Y : sig P) : proj1_sig X = proj1_sig Y → X = Y.
Proof.
  basic_simpl.
  ElimEq.
  PIR.
  trivial.
Qed.

Hint Extern 2 (exist ?A _ _ = exist ?A _ _) => apply sig_proof_irrelevance.

(* Automating use of functional_extensionality *)
Ltac FunExt :=
progress (
    repeat (
        match goal with
          [|- _ = _] =>
          let x := fresh "x" in
          extensionality x
        end
      )
  )
.

Hint Extern 1 => FunExt.

Lemma pair_eq (A B : Type) (a b : A * B) : fst a = fst b → snd a = snd b → a = b.
Proof.
  intros H1 H2.
  destruct a; destruct b.
  cbn in *.
  repeat match goal with [H : _ = _|-_] => destruct H end.
  trivial.
Qed.

Hint Resolve pair_eq.

(** Tactics to apply a tactic to all hypothesis in an efficient way.
This is due to Jonathan's (jonikelee@gmail.com) message on coq-club *)

Ltac revert_clearbody_all :=
 repeat lazymatch goal with H:_ |- _ => try clearbody H; revert H end.

Ltac hyp_stack :=
 constr:(ltac:(revert_clearbody_all;constructor) : True).

Ltac next_hyp hs step last :=
 lazymatch hs with (?hs' ?H) => step H hs' | _ => last end.

Tactic Notation "dohyps" tactic3(tac) :=
 let hs := hyp_stack in
 let rec step H hs := tac H; next_hyp hs step idtac in
 next_hyp hs step idtac.

Tactic Notation "dohyps" "reverse" tactic3(tac) :=
 let hs := hyp_stack in
 let rec step H hs := next_hyp hs step idtac; tac H in
 next_hyp hs step idtac.

Tactic Notation "do1hyp" tactic3(tac) :=
 let hs := hyp_stack in
 let rec step H hs := tac H + next_hyp hs step fail in
 next_hyp hs step fail.

Tactic Notation "do1hyp" "reverse" tactic3(tac) :=
 let hs := hyp_stack in
 let rec step H hs := next_hyp hs step fail + tac H in
 next_hyp hs step fail.

(** End of tactics for applying a tactic to all hypothesis. *)
