Require Import List.
Require Import Cecoa.TopologicalSort Cecoa.Lib Cecoa.Syntax.

Section Program.

Variables variable function constructor : Type.
Variable variable_eq_dec : forall (x1 x2 : variable), {x1=x2}+{x1<>x2}.
Variable function_eq_dec : forall (x1 x2 : function), {x1=x2}+{x1<>x2}.
Variable constructor_eq_dec : forall (x1 x2 : constructor), {x1=x2}+{x1<>x2}.

Notation value := (Syntax.value constructor).
Notation term := (Syntax.term variable function constructor).
Notation pattern := (Syntax.pattern variable constructor).
Notation rule := (Syntax.rule variable function constructor).

Variable prog : list rule.

Definition function_of_rule (r : rule) :=
  match r with rule_intro f _ _ => f end.

Definition functions_of_prog : list function :=
  map function_of_rule prog.

Definition max_arity_prog := maxl (map (@max_arity_rule _ _ _) prog).

Definition wf_prog : Prop :=
  andl (map (@rule_vars_defined _ _ _) prog).

Definition prog_graph : Graph function :=
  map (fun f => (f, filter (fun g => negb (function_beq function_eq_dec f g))
                          (concat (map (fun r => functions_of_term (rhs_of_rule r)) 
                                       (filter (fun r => function_beq function_eq_dec f (function_of_rule r)) prog)))))
      (uniquify function_eq_dec functions_of_prog).

Definition ranklist := topologicalRankList function (function_beq function_eq_dec) prog_graph.

Definition max_rank : nat := maxl (map snd ranklist).

End Program.