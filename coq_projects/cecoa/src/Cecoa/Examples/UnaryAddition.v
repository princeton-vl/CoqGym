Require Import List Omega.
Import List.ListNotations.

Require Import Cecoa.Interface.
Require Import Cecoa.Lib.

Inductive variable := x | y.
Inductive function := plus | main | errF.
Inductive constructor := zero | succ | errC.

Scheme Equality for variable.
Scheme Equality for function.
Scheme Equality for constructor.

Module PlusSyntax <: Interface.SYNTAX.
  Definition variable := variable.
  Definition function := function.
  Definition constructor := constructor.

  Definition function_default := errF.
  Definition constructor_default := errC.

  Definition variable_eq_dec := variable_eq_dec.
  Definition function_eq_dec := function_eq_dec.
  Definition constructor_eq_dec := constructor_eq_dec.
End PlusSyntax.

Module Import Syn := Interface.MkSyn(PlusSyntax).
Import Syn.ProgramNotations.

Definition var_coercion : variable -> term := var_coercion_gen.
Coercion var_coercion : variable >-> term.

Notation " 'Z' " := (capply zero []).
Notation " x '.+1' " := (capply succ [x:term]) (at level 60).

Definition plus_prog : list rule :=
  [
    main (: x, y :)    --> plus (: plus (: x, y :), plus (: x, y :) :) ;

    plus (: Z, y :)    --> y ;
    plus (: x.+1, y :) --> (plus (: x, y :)) .+1
  ].

Module PlusProg <: Syn.PROGRAM.
  Definition prog := plus_prog.
End PlusProg.

Module Import Prog := Syn.MkProg (PlusProg).
Import Prog.QI Prog.Evaluator.
Definition rank : function -> nat := ltac:(autorank function_beq ranklist).

Fixpoint quote_value (n : nat) : value :=
  match n with
  | 0    => c_capply zero []
  | S n' => c_capply succ [quote_value n']
  end.

(* It's a program *)
Proposition UnaryAdd_is_wf: wf_prog.
Proof.
  cbv; repeat split; tauto.
Qed.

(* PPO *)
Proposition UnaryAdd_is_ppo : PPO_prog rank.
Proof.
  cbv.
  intros r H.
  decompose sum H; subst; ppo.
Qed.

(* QI *)
Definition cs (c : constructor) := 1. (* same for all *)
Lemma qic_nonzero : constructor_non_zero cs.
Proof. cbv; auto. Qed.

Definition mcs := 1.
Lemma qic_bounded : mcs_is_max_constructor_size mcs cs.
Proof. cbv; auto. Qed.

Definition qic (c : constructor) args := suml args + cs c.
Lemma qic_additivity : additive qic cs.
Proof. cbv; auto. Qed.

Definition qif (f : function) args := match f with
  | main => 2*(suml args)
  | plus => suml args
  | errF => suml args
  end.

Lemma qif_subterm : subterm qif.
Proof.
  intros f l x H.
  destruct f; unfold qif.
  - apply in_le_suml; trivial.
  - apply le_trans with (m:= suml l).
    + apply in_le_suml; trivial.
    + omega.
  - apply in_le_suml; trivial.
Qed.

Lemma qif_monotonic : monotonicity_qif qif.
Proof.
  intros f xs ys Hfor.
  destruct f; unfold qif; try apply Mult.mult_le_compat_l; apply forall2_le_suml; trivial.
Qed.

Lemma qi_is_compatible : compatible_QI qic qif.
Proof.
  intros f lp t s; cbn.
  intros [ H | [ H | [ H | H ]]];
    try tauto;
    injection H; clear H; intros; subst; trivial; cbn;
    omega.
Qed.

Proposition qi_is_valid : valid_QI mcs qic qif cs.
Proof.
  repeat split.
  apply qic_bounded.
  apply qic_nonzero.
  apply qif_subterm.
  apply qif_monotonic.
  apply qi_is_compatible.
Qed.

(* P-criterion *)
Theorem plus_polytime: forall i s p c f lv d v,
  let t := fapply f lv in
  let pi := cbv_update i s p c t d v in
  cbv_wf pi -> cache_bounded qic qif c ->
  cbv_size pi <= global_bound mcs qif f lv c.
Proof.
  intros.
  apply P_criterion with (rank:=rank) (cs:=cs) (qic:=qic);auto.
  - split; [ apply UnaryAdd_is_wf | trivial ].
  - intro g; destruct g; auto; simpl; apply le_0_n.
  - apply UnaryAdd_is_ppo.
  - apply qi_is_valid.
Qed.

Definition value_default := quote_value 0.

Theorem plus_correct n m : 
  evaluates (fapply plus [term_from_value(quote_value n); term_from_value(quote_value m)]) (quote_value(n+m)).
Proof.
  revert m.
  induction n as [| n IH]; cbn; intro m.
  - reduce.
  - reduce. cbn. apply IH.
Qed.
