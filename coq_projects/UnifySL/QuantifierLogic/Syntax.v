(*
(* Require Import Logic.lib.SublistT.*)
Require Import Logic.GeneralLogic.Base.
Require Import Logic.MinimunLogic.Syntax.
Require Import Logic.PropositionalLogic.Syntax.

Local Open Scope logic_base.
Local Open Scope syntax.
Import PropositionalLanguageNotation.


Class SimpleTypedLambdaCalculus (TC: TermCalculus) : Type := {
  arrow_type: type -> type -> type;
  term_abs: forall a t_var t_term, term (args_cons t_var a) t_term -> term a (arrow_type t_var t_term);
  term_app: forall a t_var t_term, term a (arrow_type t_var t_term) -> term a t_var -> term a t_term;
  beta_red: forall a t_var t_term (func: term (args_cons t_var a) t_term) arg, term_app _ _ _ (term_abs _ _ _ func) arg = term_ins _ _ _ func arg
}.

Class BinderLanguage: Type := {
(* parameter *)
  type: Type;
  args: Type;
  args_cons: type -> args -> args;
  binded_L :> list type -> Language;
  binded_expr := fun ts => @expr (binded_L ts)
}.

Arguments binded_expr {_} _.
Arguments ins_expr {_} {_} {_} _ _.
Arguments lift_expr {_} {_} {_} _ _.

Class QuantifierLanguage (BL: BinderLanguage): Type := {
  allp: forall t ts, binded_expr (t :: ts) -> binded_expr ts;
  exp: forall t ts, binded_expr (t :: ts) -> binded_expr ts;
  lift_allp: forall t ts1 ts2 (g: sublistT ts1 ts2) (x: binded_expr (t :: ts1)), lift_expr g (allp t ts1 x) = allp t ts2 (lift_expr (sublistT_cons_cons t g) x);
  lift_exp: forall t ts1 ts2 (g: sublistT ts1 ts2) (x: binded_expr (t :: ts1)), lift_expr g (exp t ts1 x) = exp t ts2 (lift_expr (sublistT_cons_cons t g) x)
}.

Arguments allp {_} {_} {_} {_} _.
Arguments exp {_} {_} {_} {_} _.

Class NormalBinderLanguage (BL: BinderLanguage): Type := {
  binded_nL:> forall ts, NormalLanguage (binded_L ts);
  lift_impp:
    forall ts1 ts2 (g: sublistT ts1 ts2) (x y: binded_expr ts1),
      lift_expr g (x --> y) = lift_expr g x --> lift_expr g y
}.

Class PropositionalBinderLanguage (BL: BinderLanguage) {nBL: NormalBinderLanguage BL}: Type := {
  binded_pL:> forall ts, PropositionalLanguage (binded_L ts);
  lift_andp:
    forall ts1 ts2 (g: sublistT ts1 ts2) (x y: binded_expr ts1),
      lift_expr g (x && y) = lift_expr g x && lift_expr g y;
  lift_orp:
    forall ts1 ts2 (g: sublistT ts1 ts2) (x y: binded_expr ts1),
      lift_expr g (x || y) = lift_expr g x || lift_expr g y
}.
*)