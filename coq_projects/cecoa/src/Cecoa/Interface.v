Require Import List.
Require Cecoa.Syntax Cecoa.Program Cecoa.CBV_cache Cecoa.Ordering Cecoa.QI Cecoa.Final Cecoa.Evaluates.

Module Type SYNTAX.
  Parameters variable function constructor : Type.

  (* Default values, for error cases *)
  Parameter function_default : function.
  Parameter constructor_default : constructor.

  Parameter variable_eq_dec : forall (x1 x2 : variable), {x1=x2}+{x1<>x2}.
  Parameter function_eq_dec : forall (x1 x2 : function), {x1=x2}+{x1<>x2}.
  Parameter constructor_eq_dec : forall (x1 x2 : constructor), {x1=x2}+{x1<>x2}.
End SYNTAX.

Module MkSyn (S: SYNTAX).
  Definition value := Syntax.value S.constructor.
  Definition term := Syntax.term S.variable S.function S.constructor.
  Definition pattern := Syntax.pattern S.variable S.constructor.
  Definition rule := Syntax.rule S.variable S.function S.constructor.

  Definition var : S.variable -> term := @Syntax.var _ _ _.
  Definition capply : S.constructor -> list term -> term := @Syntax.capply _ _ _.
  Definition fapply : S.function -> list term -> term := @Syntax.fapply _ _ _.

  Definition c_capply : S.constructor -> list value -> value := @Syntax.c_capply _.

  Definition value_default : value := c_capply S.constructor_default nil.
  Definition rule_default : rule :=
    Syntax.rule_intro S.function_default nil (capply S.constructor_default nil).

  Definition term_from_value : value -> term :=
    @Syntax.term_from_value S.variable S.function S.constructor.
  Definition term_from_pattern : pattern -> term :=
    @Syntax.term_from_pattern S.variable S.function S.constructor.

  Definition cbv : Type := CBV_cache.cbv S.variable S.function S.constructor.
  Definition cache : Type := list (term * value).
  Definition cbv_constr : list cbv -> cache -> term -> cache -> value -> cbv :=
    @CBV_cache.cbv_constr S.variable S.function S.constructor.
  Definition cbv_split : list cbv -> cbv -> cache -> term -> cache -> value -> cbv :=
    @CBV_cache.cbv_split S.variable S.function S.constructor.
  Definition cbv_update : nat -> (S.variable -> value) -> cbv -> cache -> term -> cache -> value -> cbv :=
    @CBV_cache.cbv_update S.variable S.function S.constructor.
  Definition cbv_read : cache -> term -> value -> cbv :=
    @CBV_cache.cbv_read S.variable S.function S.constructor.

  Definition cbv_size : cbv -> nat := @CBV_cache.size S.variable S.function S.constructor.

  Definition proj_left : cbv -> term :=
    @CBV_cache.proj_left S.variable S.function S.constructor.
  Definition proj_right : cbv -> value :=
    @CBV_cache.proj_right S.variable S.function S.constructor.

  Module Type PROGRAM.
    Parameter prog : list rule.
  End PROGRAM.

  Module MkProg (P: PROGRAM).
    Definition ranklist := Program.ranklist S.variable S.function S.constructor S.function_eq_dec P.prog.
    Definition max_rank : nat := Program.max_rank S.variable S.function S.constructor S.function_eq_dec P.prog.
    Ltac autorank := TopologicalSort.autorank.

    Definition max_arity : nat := Program.max_arity_prog S.variable S.function S.constructor P.prog.
    Definition wf_prog : Prop := Program.wf_prog S.variable S.function S.constructor P.prog.

    Definition cbv_wf : cbv -> Prop :=
      CBV_cache.wf
        S.variable_eq_dec S.function_eq_dec S.constructor_eq_dec
        rule_default P.prog max_arity.

    Definition PPO_prog (rank: S.function -> nat) : Prop := Ordering.PPO_prog P.prog rank.
    Ltac ppo := Ordering.ppo S.variable_eq_dec S.function_eq_dec S.constructor_eq_dec.

    (* QI *)
    Module QI.
      Definition constructor_non_zero := @QI.constructor_non_zero S.constructor.
      Definition mcs_is_max_constructor_size := @QI.mcs_is_max_constructor_size S.constructor.
      Definition additive := @QI.additive S.constructor.
      Definition subterm := @QI.subterm S.function.
      Definition monotonicity_qic := @QI.monotonicity_qic S.constructor.
      Definition monotonicity_qif := @QI.monotonicity_qif S.function.
      Definition cache_bounded :=
        @QI.cache_bounded S.variable S.function S.constructor.
      Definition compatible_QI :=
        @QI.compatible_QI S.variable S.function S.constructor P.prog.
      Definition term_assignment :=
        @QI.term_assignment S.variable S.function S.constructor.
      Definition valid_QI :=
        @QI.valid_QI S.variable S.function S.constructor P.prog.
      Definition global_bound :=
        Final.global_bound S.variable S.function S.constructor P.prog max_arity max_rank.
      Definition P_criterion wf_prog rank :=
        Final.P_criterion S.variable S.function S.constructor P.prog max_arity rule_default wf_prog
                          S.variable_eq_dec S.function_eq_dec S.constructor_eq_dec rank max_rank.
    End QI.

    Module Evaluator.
      Definition first_rule := Evaluates.first_rule S.variable_eq_dec S.function_eq_dec S.constructor_eq_dec value_default P.prog.
      Definition evaluates := Evaluates.evaluates S.variable_eq_dec S.function_eq_dec S.constructor_eq_dec value_default P.prog.
      Ltac reduce := Evaluates.reduce.
      Ltac auto_for_auto lemma :=
        let t' := type of lemma in
        let t := eval unfold evaluates in t' in
            exact t.
      Hint Unfold evaluates : eval.
    End Evaluator.
  End MkProg.


  (* Notations for program definitions *)

  Module ProgramNotations.
    Fixpoint patternify (t: term) : pattern :=
      match t with
      | Syntax.var v         => Syntax.p_var v
      | Syntax.capply cst ys => Syntax.p_capply cst (map patternify ys)
      | _                    => Syntax.p_capply S.constructor_default nil
      end.

    Definition rulify (t e: term) : rule :=
      match t with
        | Syntax.fapply f ys => Syntax.rule_intro f (map patternify ys) e
        | _                  => Syntax.rule_intro S.function_default nil (Syntax.capply S.constructor_default nil)
      end.

    Notation " f '(:' ':)' " := (Syntax.fapply f (@nil term)) (at level 65).
    Notation " f '(:' x ':)' " := (Syntax.fapply f (@cons term x nil)) (at level 65).
    Notation " f '(:' x ',' .. ',' z ':)' " := (Syntax.fapply f (@cons term x .. (@cons term z nil) .. )) (at level 65).
    Notation "fl '-->' e" := (rulify fl e) (at level 70).

    Definition var_coercion_gen : S.variable -> term := @Syntax.var _ _ _.
  End ProgramNotations.
End MkSyn.
