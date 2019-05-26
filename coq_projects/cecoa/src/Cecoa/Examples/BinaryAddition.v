Require Import List Omega Numbers.BinNums.
Import List.ListNotations.

Require Import Cecoa.Interface.
Require Import Cecoa.Lib.

Inductive variable := x | y.
Inductive function := succ | addf | addt | mult | main | errF.
Inductive constructor := zero | suc0 | suc1 | errC. (* binary numbers, LSB first *)

Scheme Equality for variable.
Scheme Equality for function.
Scheme Equality for constructor.

Module BASyntax <: Interface.SYNTAX.
  Definition variable := variable.
  Definition function := function.
  Definition constructor := constructor.

  Definition function_default := errF.
  Definition constructor_default := errC.

  Definition variable_eq_dec := variable_eq_dec.
  Definition function_eq_dec := function_eq_dec.
  Definition constructor_eq_dec := constructor_eq_dec.
End BASyntax.

Module Import Syn := Interface.MkSyn(BASyntax).
Import Syn.ProgramNotations.

Definition var_coercion : variable -> term := var_coercion_gen.
Coercion var_coercion : variable >-> term.

Notation " 'Z' " := (capply zero []).
Notation "x '!0'" := (capply suc0 (@cons term x nil)) (at level 60).
Notation "x '!1'" := (capply suc1 (@cons term x nil)) (at level 60).

Definition ba_prog : list rule := [
  (* successor *)
  succ (: Z :)   --> Z!1;  (* succ(0) -> S1(0) = "01" *)
  succ (: x!0 :) --> x!1;    (* succ(S0(x)) -> S1(x)  "x0" + 1 = "x1" *)
  succ (: x!1 :) --> (succ (: x :))!0; (* succ(S1(x)) -> S0(succ(x))    "x1" + 1 = "(x+1)0" *)
  (* addition, no carry *)
  addf (: Z, y :)     --> y; (* 0 + y + 0 = y *)
  addf (: x, Z :)     --> x; (* x + 0 + 0 = x *)
  addf (: x!0, y!0 :) --> (addf (: x, y :))!0; (* "x0" + "y0" + 0 = "(x+y+0)0" *)
  addf (: x!0, y!1 :) --> (addf (: x, y :))!1; (* "x0" + "y1" + 0 = "(x+y+0)1" *)
  addf (: x!1, y!0 :) --> (addf (: x, y :))!1; (* "x1" + "y0" + 0 = "(x+y+0)1" *)
  addf (: x!1, y!1 :) --> (addt (: x, y :))!0; (* "x1" + "y1" + 0 = "(x+y+1)0" *)
  (* addition, with carry *)
  addt (: Z, y :)     --> succ (: y :); (* 0 + y + 1 = y+1 *)
  addt (: x, Z :)     --> succ (: x :); (* x + 0 + 1 = x+1 *)
  addt (: x!0, y!0 :) --> (addf (: x, y :))!1; (* "x0" + "y0" + 1 = "(x+y+0)1" *)
  addt (: x!0, y!1 :) --> (addt (: x, y :))!0; (* "x0" + "y1" + 1 = "(x+y+1)0" *)
  addt (: x!1, y!0 :) --> (addt (: x, y :))!0; (* "x1" + "y0" + 1 = "(x+y+1)0" *)
  addt (: x!1, y!1 :) --> (addt (: x, y :))!1; (* "x1" + "y1" + 1 = "(x+y+1)1" *)
  (* multiplication *)
  mult (: Z, y :)   --> Z;
  mult (: x!0, y :) --> (mult (: x, y :))!0;
  mult (: x!1, y :) --> addf (: y, (mult (: x, y :))!0 :) ;
  (* main computation *)
  main (: x :) --> addf (: addf (: mult (: x, mult (: x, x :) :), (* X³ *)
                                   mult (: Z!1!0!1, x :) :), (* + 5X *)
                                   Z!1 :)                    (* + 1 *)
].

Module BAProg <: Syn.PROGRAM.
  Definition prog := ba_prog.
End BAProg.

Module Import Prog := Syn.MkProg (BAProg).
Import Prog.QI Prog.Evaluator.
Definition rank : function -> nat := ltac:(autorank function_beq ranklist).

(* It's a program *)
Proposition BinaryOp_is_wf: wf_prog.
Proof. cbv; repeat split; tauto. Qed.

(* PPO *)
Proposition BinaryOp_is_ppo : PPO_prog rank.
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
  | main => Nat.max (Nat.max (5*(suml args)) (8+(suml args)) + 1) 2 + 1 (* max(max(5X,X+8) + 1, 2) + 1 *)
            (* args here has only one element, X, so suml args = X *)
  | mult => suml args + (hd 0 args)  (* 2X+Y *)
            (* args here has only two elements, X and Y, so suml args = X+Y *)
  | addf => maxl args + 1
  | addt => maxl args + 1
  | succ => suml args + 1
  | errF => suml args
  end.

Lemma qif_subterm : subterm qif.
Proof.
intros f l x Hin.
destruct f;unfold qif.
- apply le_trans with (m := suml l).
  + apply in_le_suml;trivial.
  + omega.
- apply le_trans with (m := maxl l).
  + apply maxl_is_max;trivial.
  + omega.
- apply le_trans with (m := maxl l).
  + apply maxl_is_max;trivial.
  + omega.
- apply le_trans with (m := suml l).
  + apply in_le_suml;trivial.
  + omega.
- apply le_trans with (m := max (max (5 * suml l) (8 + suml l) + 1) 2).
  apply le_trans with (m := max (5 * suml l) (8 + suml l) + 1).
  apply le_trans with (m := max (5 * suml l) (8 + suml l)).
  apply le_trans with (m := 8 + suml l).
  apply le_trans with (m := suml l).
  + apply in_le_suml;trivial.
  + omega.
  + apply Nat.le_max_r.
  + omega.
  + apply Nat.le_max_l.
  + omega.
- apply in_le_suml; trivial.
Qed.

Ltac qif_monotonic_tac :=
  repeat (apply forall2_le_suml || apply forall2_le_maxl ||
          apply Plus.plus_le_compat_r || apply Plus.plus_le_compat_l || apply Plus.plus_le_compat ||
          apply Nat.max_le_compat_r || apply Nat.max_le_compat_l || apply Nat.max_le_compat ||
          apply Mult.mult_le_compat_l || apply Mult.mult_le_compat_r
         ); trivial.

Lemma qif_monotonic : monotonicity_qif qif.
Proof.
  intros f xs ys Hfor.
  destruct f; unfold qif; qif_monotonic_tac.
  destruct Hfor; unfold hd; trivial.
Qed.

Lemma qi_is_compatible : compatible_QI qic qif.
Proof.
  intros f lp t s; cbn.
  intros H; repeat destruct H as [ H | H ]; try tauto;
  injection H; clear H; intros; subst; cbn; try (unfold qic, cs; omega);
  fold term_assignment; fold term_from_value;
  set (QIx := term_assignment qic qif (term_from_value (s x)));
  set (QIy := term_assignment qic qif (term_from_value (s y)));
  unfold cs;
  repeat rewrite Nat.add_0_r; repeat rewrite Nat.max_0_r; repeat rewrite Nat.add_max_distr_r;
  try trivial.
  - destruct QIy; omega.
  - rewrite Nat.add_1_r; apply le_S, Nat.le_max_l.
  - destruct QIy; omega.
  - repeat rewrite Nat.add_1_r.
    apply le_n_S, Nat.le_max_l.
  - rewrite Nat.max_r; omega.
  - repeat rewrite Nat.add_1_r; apply le_n_S.
    apply Nat.max_le_compat_r, le_n_S, Nat.max_le_compat; omega.
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
Theorem polytime: forall i s p c f lv d v,
  let t := fapply f lv in
  let pi := cbv_update i s p c t d v in
  cbv_wf pi -> cache_bounded qic qif c ->
  cbv_size pi <= global_bound mcs qif f lv c.
Proof.
intros.
apply P_criterion with (rank:=rank) (cs:=cs) (qic:=qic); auto.
- split; [ apply BinaryOp_is_wf | trivial ].
- cbv; omega.
- intros f0; destruct f0; cbv; omega.
- apply BinaryOp_is_ppo.
- apply qi_is_valid.
Qed.

Fixpoint quote_positive (p: positive) : value :=
  match p with
    | xI p' => c_capply suc1 [quote_positive p']
    | xO p' => c_capply suc0 [quote_positive p']
    | xH    => c_capply suc1 [c_capply zero []]
  end.

Definition quote_value (n: N) : value :=
  match n with
    | N0     => c_capply zero []
    | Npos p => quote_positive p
  end.

Lemma quote_positive_value p : quote_positive p = quote_value (Npos p).
Proof. trivial. Qed.

Definition value_default := quote_value (0%N).

Notation evaluates := (Evaluates.evaluates variable_eq_dec function_eq_dec constructor_eq_dec value_default ba_prog).

Lemma succ_correct : forall n, evaluates (fapply succ [term_from_value (quote_value n)]) (quote_value (N.succ n)).
Proof.
intro n.
destruct n as [ | n]; simpl.
- reduce.
- induction n as [ p | p | ]; simpl; repeat reduce.
Qed.

Hint Resolve succ_correct : eval.

Lemma add_correct m n:
  evaluates (fapply addf [term_from_value (quote_value m); term_from_value (quote_value n)]) (quote_value (m + n)) /\
  evaluates (fapply addt [term_from_value (quote_value m); term_from_value (quote_value n)]) (quote_value (N.succ( m + n))).
Proof.
destruct m as [ | p].
simpl; split; reduce; apply succ_correct.
revert n; induction p; intro n; split.
- destruct n as [ | p'].
  + repeat reduce.
  + destruct (IHp (N.div2 (Npos p'))).
    destruct p' as [p' | p' |]; reduce.
    auto with eval.
    now rewrite Pos.add_carry_spec.
- destruct n as [ | p'].
  + repeat reduce.
     do 2 rewrite quote_positive_value.
    apply succ_correct.
  + destruct (IHp (N.div2 (Npos p'))).
    destruct p' as [p' | p' |]; reduce.
    now rewrite Pos.add_carry_spec.
- destruct n as [ | p'].
  + repeat reduce.
  + destruct (IHp (N.div2 (Npos p'))).
    destruct p' as [p' | p' |]; reduce.
- destruct n as [ | p'].
  + repeat reduce.
  + destruct (IHp (N.div2 (Npos p'))).
    destruct p' as [p' | p' |]; reduce.
- destruct n as [ | p'].
  + repeat reduce.
  + destruct p' as [p' | p' |]; repeat reduce.
    do 2 rewrite quote_positive_value.
    apply succ_correct.
- destruct n as [ | p'].
  + repeat reduce.
  + destruct p' as [p' | p' |]; repeat reduce;
    do 2 rewrite quote_positive_value;
    apply succ_correct.
Qed.

Hint Resolve add_correct : eval.