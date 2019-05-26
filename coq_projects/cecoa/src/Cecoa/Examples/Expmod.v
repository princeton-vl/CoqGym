Require Import List Omega Numbers.BinNums Psatz.
Import List.ListNotations.

Require Import Cecoa.Lib Cecoa.Interface.

Inductive variable := x | y | p | q | x0 | m | c | n' | m' | r | r'.
Inductive function := pred_doubleF | succ_double_maskF | double_maskF | double_pred_maskF | sub_maskF | sub_mask_carryF | compare_contEqF | compare_contGtF | compare_contLtF | compareF | succ_doubleF | doubleF | subF | compare0F | lebF | moduloF | errF | sub_auxF | leb_auxF | pos_moduloOF | pos_moduloIF | pos_moduloF | condF | succF | addF | add_carryF | add0F | mul_modF | mul_mod_auxF | exp_modF | exp_mod_auxF | mod_auxF | modF | boundF.
Inductive constructor := TrueC | FalseC | PairC | EqC | LtC | GtC | XIC | XOC | XHC | N0C | NposC | IsNulC | IsPosC | IsNegC | errC.

Scheme Equality for variable.
Scheme Equality for constructor.
Scheme Equality for function.

Module EMSyntax <: Interface.SYNTAX.
  Definition variable := variable.
  Definition function := function.
  Definition constructor := constructor.

  Definition function_default := errF.
  Definition constructor_default := errC.

  Definition variable_eq_dec := variable_eq_dec.
  Definition function_eq_dec := function_eq_dec.
  Definition constructor_eq_dec := constructor_eq_dec.
End EMSyntax.

Module Import Syn := Interface.MkSyn(EMSyntax).
Import Syn.ProgramNotations.

Definition var_coercion : variable -> term := var_coercion_gen.
Coercion var_coercion : variable >-> term.
Notation " x '#' l " := (capply x (map var_coercion l)) (at level 50).

(* Some notations for the constructors *)
Notation "'XO' a" := (capply XOC [var_coercion a]) (at level 60).
Notation "'XI' a" := (capply XIC [var_coercion a]) (at level 60).
Notation "'Ispos' a" := (capply IsPosC [var_coercion a]) (at level 60).
Notation "'NPos' a" := (capply NposC [var_coercion a]) (at level 60).
Notation "'XH'" := (capply XHC []) (at level 60).
Notation "'Isnul'" := (capply IsNulC []) (at level 60).
Notation "'Isneg'" := (capply IsNegC []) (at level 60).
Notation "'GT'" := (capply GtC []) (at level 60).
Notation "'LT'" := (capply LtC []) (at level 60).
Notation "'EQ'" := (capply EqC []) (at level 60).
Notation "'N0'" := (capply N0C []) (at level 60).
Notation "'TRUE'" := (capply TrueC []) (at level 60).
Notation "'FALSE'" := (capply FalseC []) (at level 60).

(* Mostly generated using:
Extraction Language Haskell.
Recursive Extraction N.modulo.*)

Definition em_prog : list rule := [
pred_doubleF (: XI p :) --> capply XIC [XO p];
pred_doubleF (: XO p :) --> capply XIC [pred_doubleF (: p :)];
pred_doubleF (: XH :) --> XH;

succ_double_maskF (: Isnul :) --> capply IsPosC [XH];
succ_double_maskF (: Ispos p :)  --> capply IsPosC [XI p];
succ_double_maskF (: Isneg :) --> Isneg;

double_maskF (: Ispos p :) --> capply IsPosC [XO p];
double_maskF (: x0 :) --> x0;

double_pred_maskF (: XI p :) --> 
  capply IsPosC [capply XOC [XO p]];
double_pred_maskF (: XO p :) --> 
  capply IsPosC [capply XOC [pred_doubleF (: p :)]];
double_pred_maskF (: XH :) --> Isnul;

sub_maskF (: XI p, XI q :) --> double_maskF (: sub_maskF (: p, q :) :);
sub_maskF (: XI p, XO q :) --> succ_double_maskF (: sub_maskF (: p, q :) :);
sub_maskF (: XI p, XH :) --> capply IsPosC [XO p];

sub_maskF (: XO p, XI q :) --> 
  succ_double_maskF (: sub_mask_carryF (: p, q :) :);
sub_maskF (: XO p, XO q :) --> double_maskF (: sub_maskF (: p, q :) :);
sub_maskF (: XO p, XH :) --> capply IsPosC [pred_doubleF (: p :)];
sub_maskF (: XH, XH :) --> Isnul;
sub_maskF (: XH, q :) --> Isneg;

sub_mask_carryF (: XI p, XI q :) --> 
  succ_double_maskF (: sub_mask_carryF (: p, q :) :);
sub_mask_carryF (: XI p, XO q :) --> 
  double_maskF (: sub_maskF (: p, q :) :);
sub_mask_carryF (: XI p, XH :) --> capply IsPosC [pred_doubleF (: p :)];
sub_mask_carryF (: XO p, XI q :) --> 
  double_maskF (: sub_mask_carryF (: p, q :) :);
sub_mask_carryF (: XO p, XO q :) --> 
  succ_double_maskF (: sub_mask_carryF (: p, q :) :);
sub_mask_carryF (: XO p, XH :) --> double_pred_maskF (: p :);
sub_mask_carryF (: XH, q :) --> Isneg;

(* compare_cont with r specified, to have ppo *)
compare_contEqF (: XI p, XI q :) --> compare_contEqF (: p, q :);
compare_contEqF (: XI p, XO q :) --> compare_contGtF (: p, q :);
compare_contEqF (: XI p, XH :) --> GT;
compare_contEqF (: XO p, XI q :) --> compare_contLtF (: p, q :);
compare_contEqF (: XO p, XO q :) --> compare_contEqF (: p, q :);
compare_contEqF (: XO p, XH :) --> GT;
compare_contEqF (: XH, XH :) --> EQ;
compare_contEqF (: XH, q :) --> LT;

compare_contLtF (: XI p, XI q :) --> compare_contLtF (: p, q :);
compare_contLtF (: XI p, XO q :) --> compare_contGtF (: p, q :);
compare_contLtF (: XI p, XH :) --> GT;
compare_contLtF (: XO p, XI q :) --> compare_contLtF (: p, q :);
compare_contLtF (: XO p, XO q :) --> compare_contLtF (: p, q :);
compare_contLtF (: XO p, XH :) --> GT;
compare_contLtF (: XH, XH :) --> LT;
compare_contLtF (: XH, q :) --> LT;

compare_contGtF (: XI p, XI q :) --> compare_contGtF (: p, q :);
compare_contGtF (: XI p, XO q :) --> compare_contGtF (: p, q :);
compare_contGtF (: XI p, XH :) --> GT;
compare_contGtF (: XO p, XI q :) --> compare_contLtF (: p, q :);
compare_contGtF (: XO p, XO q :) --> compare_contGtF (: p, q :);
compare_contGtF (: XO p, XH :) --> GT;
compare_contGtF (: XH, XH :) --> GT;
compare_contGtF (: XH, q :) --> LT;

compareF (: p, q :) -->  compare_contEqF (: p, q :);

succ_doubleF (: N0 :) --> capply NposC [XH];
succ_doubleF (: NPos p :) --> capply NposC [XI p];

doubleF (: N0 :) --> N0;
doubleF (: NPos p :) --> capply NposC [XO p];

(* added for case *)
sub_auxF (: Ispos p :) --> NPos p;
sub_auxF (: p :) --> N0;

subF (: N0, m :) --> N0;
subF (: NPos p, N0 :) --> NPos p;
subF (: NPos p, NPos q :) --> sub_auxF (: sub_maskF (: p, q :) :);

compare0F (: N0, N0 :) --> EQ;
compare0F (: N0, NPos q :) --> LT;
compare0F (: NPos n', N0 :) --> GT;
compare0F (: NPos n', NPos m' :) --> compareF (: n', m' :);

leb_auxF (: GT :) --> FALSE;
leb_auxF (: q :) --> TRUE;

lebF (:x, y :) --> leb_auxF (: compare0F (: x, y :) :);

condF (: TRUE, x, y :) --> x;
condF (: FALSE, x, y :) --> y;

mod_auxF (: XH, capply NposC [XH] :) --> N0 ;
mod_auxF (: XH, m :) --> capply NposC [XH] ;
mod_auxF (: XO x, m :) --> 
  condF (: lebF (: m, doubleF (: mod_auxF (: x, m :) :) :), 
           subF (: doubleF (: mod_auxF (: x, m :) :), m :),
           doubleF (: mod_auxF (: x, m :) :) :) ;
mod_auxF (: XI x, m :) --> 
  condF (: lebF (: m, succ_doubleF (: mod_auxF (: x, m :) :) :), 
           subF (: succ_doubleF (: mod_auxF (: x, m :):), m :),
           succ_doubleF (: mod_auxF (: x, m :) :) :) ;

modF (: N0, m :) --> N0;
modF (: NPos x, m :) --> mod_auxF (: x, m :);

(* back to extracted code *)

succF (: XI p :) --> capply XOC [succF (: p :)];
succF (: XO p :) --> XI p;
succF (: XH :) --> capply XOC [XH];

addF (: XI p, XI q :) --> capply XOC [add_carryF (: p, q :)];
addF (: XI p, XO q :) --> capply XIC [addF (: p, q :)];
addF (: XI p, XH :) --> capply XOC [succF (: p :)];
addF (: XO p, XI q :) --> capply XIC [addF (: p, q :)];
addF (: XO p, XO q :) --> capply XOC [addF (: p, q :)];
addF (: XO p, XH :) --> XI p;
addF (: XH, XI q :) --> capply XOC [succF (: q :)];
addF (: XH, XO q :) --> XI q;
addF (: XH, XH :) --> capply XOC [XH];

add_carryF (: XI p, XI q :) --> capply XIC [add_carryF (: p, q :)];
add_carryF (: XI p, XO q :) --> capply XOC [add_carryF (: p, q :)];
add_carryF (: XI p, XH :) --> capply XIC [succF (: p :)];
add_carryF (: XO p, XI q :) --> capply XOC [add_carryF (: p, q :)];
add_carryF (: XO p, XO q :) --> capply XIC [addF (: p, q :)];
add_carryF (: XO p, XH :) --> capply XOC [succF (: p :)];
add_carryF (: XH, XI q :) --> capply XIC [succF (: q :)];
add_carryF (: XH, XO q :) --> capply XOC [succF (: q :)];
add_carryF (: XH, XH :) --> capply XIC [XH];

add0F (: N0, m :) --> m;
add0F (: NPos p, N0 :) --> NPos p;
add0F (: NPos p, NPos q :)--> capply NposC [addF (: p, q :)];

mul_mod_auxF (: XI p, y, m, XO x :) --> 
  modF (: add0F (: y, doubleF (: mul_mod_auxF (: p, y, m, x :) :):), m :);
mul_mod_auxF (: XO p, y, m, XO x :) --> 
  modF (: doubleF (: mul_mod_auxF (: p, y, m, x :) :), m :);
mul_mod_auxF (: XH, y, m, x :) --> modF (: y, m :);

mul_modF (: N0, y, m, p :) --> N0;
mul_modF (: NPos x , y, m, p :) --> mul_mod_auxF (: x, y, m, p :);

exp_mod_auxF (: x, XH, m, p :) --> modF (: x, m :);
exp_mod_auxF (: x, XO y, m, p :) -->
  mul_modF (: exp_mod_auxF (: x, y, m, p :), exp_mod_auxF (: x, y, m, p :), m, p :) ;
exp_mod_auxF (: x, XI y, m, p :) -->
  mul_modF (: modF (: x, m :), mul_modF (: exp_mod_auxF (: x, y, m, p :), exp_mod_auxF (: x, y, m, p :), m, p :), m, p :);

boundF (: N0 :) --> XH;
boundF (: NPos p :) --> boundF (: p :);
boundF (: XH :) --> capply XOC [XH];
boundF (: XI x :) --> capply XOC [boundF (: x :)];
boundF (: XO x :) --> capply XOC [boundF (: x :)];

exp_modF (: x, N0 , m :) --> modF(: capply NposC [XH], m :) ;
exp_modF (: x, NPos y, m :) --> exp_mod_auxF (: x, y, m, boundF (: m :) :)
].

Module EMProg <: Syn.PROGRAM.
  Definition prog := em_prog.
End EMProg.

Module Import Prog := Syn.MkProg (EMProg).
Import Prog.QI Prog.Evaluator.

Definition rank : function -> nat := ltac:(autorank function_beq ranklist).

(* It's a program *)
Proposition Expmod_is_wf: wf_prog.
Proof. cbv; repeat split; try tauto; auto. Qed.

Proposition expmod_is_ppo : PPO_prog rank.
Proof.
  cbv.
  intros r H.
  decompose sum H; subst; ppo.
Qed.

(* QI *)
Definition cs (c : constructor) := 1%nat. (* same for all *)

Lemma qic_nonzero : constructor_non_zero cs.
Proof. cbv; auto. Qed.

Definition mcs := 1.
Lemma qic_bounded : mcs_is_max_constructor_size mcs cs.
Proof. cbv; auto. Qed.

Definition qic (c : constructor) args := suml args + cs c.

Lemma qic_additivity : additive qic cs.
Proof. cbv; auto. Qed.

Lemma cons_app {A : Type}  (h: A) t: h::t = [h] ++t.
Proof. trivial. Qed.


(* big tactic hopefully proving inequalities *)
Ltac try_prove_ineq := 
unfold qic, cs;
try tauto; intros; subst; cbn; try omega;
repeat rewrite Nat.add_0_r; repeat rewrite Nat.max_0_r; 
repeat rewrite Nat.add_max_distr_r; repeat rewrite Nat.add_1_r;
repeat rewrite Nat.max_id, Max.max_r;
try (solve [simpl; auto with *]);
try (nia); repeat (case QI.value_assignment); auto with *.

(* tactic proving 1 inequality *)
Ltac prove_rule H :=
  rewrite cons_app; apply QI.p_smc_QI_app;
  [ intros f lp t s; cbn; intro H;
    repeat (destruct H as [ H | H ];
      [inversion H; subst; unfold map; simpl; 
       repeat rewrite QI.value_as_p_term_assignment;
        eexists; eexists; repeat split; repeat try_prove_ineq| ]); inversion H
  |].

Definition spec_QI (f : function) (qf : list nat -> nat) :=
 fun g => if function_beq g f then Some qf else None.

Ltac inst f qi := idtac "instantiating" f; apply QI.p_smc_split with (h := spec_QI f qi).

(* get next function name and instantiate it *)
Ltac inst_next qi :=
match goal with 
| |- context[rulify (Syntax.fapply ?ff _) _ ::_] => 
    (idtac "instantiating" ff;
    apply QI.p_smc_split with (h := spec_QI ff qi))
end.

Ltac qif_monotonic_tac :=
  repeat (apply forall2_le_suml || apply forall2_le_maxl ||
          apply Plus.plus_le_compat_r || apply Plus.plus_le_compat_l || apply Plus.plus_le_compat ||
          apply Nat.max_le_compat_r || apply Nat.max_le_compat_l || apply Nat.max_le_compat ||
          apply Mult.mult_le_compat_l || apply Mult.mult_le_compat_r || apply Mult.mult_le_compat
         ); trivial.

Definition qif_proofs : {qif | subterm qif /\ monotonicity_qif qif /\ compatible_QI qic qif}.
Proof.
(* let's define the qi via a partial function, starting with an 
   everywhere undefined function *)
apply QI.p_smc_smc.
unfold EMProg.prog, em_prog.

inst_next (fun x => maxl x + 1). do 3 (prove_rule H).

inst_next (fun x => maxl x + 1).
inst double_maskF (fun x => maxl x + 1).
do 5 (prove_rule H).

inst_next (fun x => maxl x + 2).
inst sub_maskF (fun x => maxl x + 1).
inst sub_mask_carryF (fun x => maxl x + 1).
do 18 (prove_rule H).

inst_next maxl.
inst compare_contLtF maxl.
inst compare_contGtF maxl.
inst compareF maxl.
do 25 (prove_rule H).

inst_next (fun l => maxl l + 1).
inst doubleF (fun l => maxl l + 1).
do 4 (prove_rule H).

inst_next (fun l => maxl l). prove_rule H.
(* second rule relies on constructor_non_zero *)
rewrite cons_app. apply QI.p_smc_QI_app.
{ intros f lp t s. cbn. intro H.
  destruct H; try tauto. inversion H.
  subst. unfold map. simpl.
  rewrite QI.value_as_p_term_assignment. simpl.
  eexists. eexists. repeat split; auto.
  rewrite Nat.max_0_r.
  unfold qic at 1. simpl. unfold cs.
  apply le_trans with (m:=Syntax.value_size (s p)).
  - rewrite <- Syntax.compatible_sizes with (variable:=variable) (function:=function).
    set (v:=Syntax.term_from_value variable function (s p)).
    generalize (Syntax.gt_term_size_O v). intro. omega.
  - apply QI.value_size_le_QI with (cs:=cs).
    + apply qic_additivity.
    + apply qic_nonzero.
}
inst_next (fun l => maxl l).
do 3 (prove_rule H).

inst_next maxl. do 4 (prove_rule H).

inst_next (fun l => maxl l). prove_rule H.
(* second rule relies on constructor_non_zero *)
rewrite cons_app. apply QI.p_smc_QI_app.
{ intros f lp t s. cbn. intro H.
  destruct H; try tauto. inversion H.
  subst. unfold map. simpl.
  rewrite QI.value_as_p_term_assignment. simpl.
  eexists. eexists. repeat split; auto.
  rewrite Nat.max_0_r.
  unfold qic at 1. simpl. unfold cs.
  apply le_trans with (m:=Syntax.value_size (s q)).
  - rewrite <- Syntax.compatible_sizes with (variable:=variable) (function:=function).
    set (v:=Syntax.term_from_value variable function (s q)).
    generalize (Syntax.gt_term_size_O v). intro. omega.
  - apply QI.value_size_le_QI with (cs:=cs).
    + apply qic_additivity.
    + apply qic_nonzero.
}

inst_next maxl. prove_rule H.

inst_next maxl. do 2 (prove_rule H).

(* modF *)
inst_next (fun l => suml l + 1). do 4 (prove_rule H).
inst_next (fun l => suml l + 1). do 2 (prove_rule H).

inst_next (fun l => maxl l + 1); do 3 (prove_rule H).
inst add_carryF (fun l => maxl l + 1).
inst_next (fun l => maxl l + 1). do 18 (prove_rule H).

inst_next (fun l => maxl l + 1); do 3 (prove_rule H).

inst_next (fun l => match l with [p1;y1;m1;c1] => (m1+3) * (c1+1) + max p1 y1 | _ => maxl l end).
do 3 (prove_rule H).

inst_next (fun l => match l with [p1;y1;m1;c1] => (m1+3) * (c1+1) + max p1 y1 | _ => maxl l end).
do 2 (prove_rule H).

inst_next (fun l => match l with [x1;y1;m1;c1] => 
  x1 + (y1 + 1) * 2 * (m1+3) * (c1+1) | _ => maxl l end).
do 3 (prove_rule H).

(* bound *)
inst_next (fun l => maxl l +1).
do 5 (prove_rule H).

(* expmod *)
(* (y1+1) because of subterm *)
inst_next (fun l => match l with [x1;y1;m1] => 
  x1 + (y1+1) * 2 * (m1+3) * (m1+2) | _ => maxl l end).
do 2 (prove_rule H).

eexists (fun x => None).
unfold QI.p_smc, QI.p_compatible_QI, QI.p_subterm, QI.p_monotonicity.
repeat split.
(* subterm *)
- intros f l x Hin; assert(H' := maxl_is_max _ _ Hin); 
    assert (H'' := maxl_le_suml l); destruct f; simpl; trivial;
  try omega;
  (repeat (destruct l; trivial);
   repeat(destruct Hin as [ H | Hin]; [subst; simpl; try_prove_ineq |]);
   try inversion Hin).
   simpl; nia.
(* monotonic *)
- intros f xs ys Hfor.
  destruct f; qif_monotonic_tac;
  repeat (destruct Hfor; simpl; try qif_monotonic_tac).
- simpl; tauto.
Defined.

Definition qif := proj1_sig qif_proofs.

Proposition qi_is_valid : valid_QI mcs qic qif cs.
Proof.
unfold qif.
destruct qif_proofs as (qif & Hs & Hm & Hc).
repeat split; trivial.
apply qic_bounded.
apply qic_nonzero.
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
- split; [ apply Expmod_is_wf | trivial ].
- cbv; omega.
- intros f0; destruct f0; cbv; omega.
- apply expmod_is_ppo.
- apply qi_is_valid.
Qed.

(* Specifications *)


(* Conversion functions from/to term values/Coq types. *)
Fixpoint Pos_of_value (v : value) : positive := match v with
| Syntax.c_capply XHC [] => xH
| Syntax.c_capply XOC [v] => xO (Pos_of_value v)
| Syntax.c_capply XIC [v] => xI (Pos_of_value v)
| _ => xH
end.

Fixpoint N_of_value (v : value) : N := match v with
| Syntax.c_capply N0C [] => 0
| Syntax.c_capply NPosC [v] => N.pos (Pos_of_value v)
| _ => 0
end.

Fixpoint value_of_pos (n : positive) : value := match n with
| xH => c_capply XHC []
| xO a => c_capply XOC [value_of_pos a]
| xI a => c_capply XIC [value_of_pos a]
end.

Fixpoint pos_of_value p := match p with
| Syntax.c_capply XHC [] => xH
| Syntax.c_capply XOC [a] => xO (pos_of_value a)
| Syntax.c_capply XIC [a] => xI (pos_of_value a)
| _ => xH
end.

Definition value_of_N (n : N) : Syntax.value EMSyntax.constructor (* value *) :=
  match n with
  | 0%N => c_capply N0C []
  | Npos a => c_capply NposC [value_of_pos a]
  end.

Definition value_of_mask (m : Pos.mask) := match m with
| IsPos a => c_capply IsPosC [value_of_pos a]
| IsNeg => c_capply IsNegC []
| IsNul => c_capply IsNulC []
end.

Definition mask_of_value m := match m with
| Syntax.c_capply IsPosC [a] => IsPos (pos_of_value a)
| Syntax.c_capply IsNegC [] => IsNeg
| Syntax.c_capply IsNulC [] => IsNul
| _ => IsNul
end.

Definition value_of_comp c := match c with
| Eq => c_capply EqC []
| Lt => c_capply LtC []
| Gt => c_capply GtC []
end.

Definition comp_of_value v := match v with
| Syntax.c_capply EqC [] => Eq
| Syntax.c_capply LtC [] => Lt
| Syntax.c_capply GtC [] => Gt
| _ => Eq
end.

Definition value_of_bool b := match b with
| true => c_capply TrueC []
| false => c_capply FalseC []
end.

Definition bool_of_value v := match v with
| Syntax.c_capply TrueC [] => true
| Syntax.c_capply FalseC [] => false
| _ => false
end.

Definition pairN : Type := (N * N).

Definition value_of_pair (x : pairN) := c_capply PairC [value_of_N (fst x); value_of_N (snd x)].

Coercion value_of_N : N >-> Syntax.value.

Coercion value_of_pair : pairN >-> value.


Open Scope N_scope.

Lemma pred_double_correct p : forall t,
evaluates t (value_of_pos p) ->
  evaluates (pred_doubleF (: t :)) (value_of_pos (Pos.pred_double p)).
Proof. induction p; intros; reduce; apply IHp; auto with *. Qed.

Definition pred_double_correct' : ltac:(auto_for_auto pred_double_correct) := pred_double_correct.
Hint Resolve pred_double_correct' : eval.

Lemma succ_double_mask_correct m : forall t,
evaluates t (value_of_mask m) ->
evaluates (succ_double_maskF (: t :)) 
          (value_of_mask (Pos.succ_double_mask m)).
Proof. induction m; reduce. Qed.

Definition succ_double_mask_correct' : ltac:(auto_for_auto succ_double_mask_correct) := succ_double_mask_correct.
Hint Resolve succ_double_mask_correct' : eval.

Lemma double_mask_correct m : forall t,
evaluates t (value_of_mask m) ->
evaluates (double_maskF (: t :)) (value_of_mask (Pos.double_mask m)).
Proof. induction m; reduce. Qed.

Definition double_mask_correct' : ltac:(auto_for_auto double_mask_correct) := double_mask_correct.
Hint Resolve double_mask_correct' : eval.

Lemma double_pred_mask_correct p : forall t,
evaluates t (value_of_pos p) ->
evaluates (double_pred_maskF (: t :)) (value_of_mask (Pos.double_pred_mask p)).
Proof. induction p; reduce. Qed.

Definition double_pred_mask_correct' : ltac:(auto_for_auto double_pred_mask_correct) := double_pred_mask_correct.
Hint Resolve double_pred_mask_correct' : eval.

Lemma sub_mask_correct q : forall p tp tq,
evaluates tp (value_of_pos p) ->
evaluates tq (value_of_pos q) ->
evaluates (sub_maskF (: tp, tq :)) 
          (value_of_mask (Pos.sub_mask p q)) /\
evaluates (sub_mask_carryF (: tp, tq :)) 
          (value_of_mask (Pos.sub_mask_carry p q)).
Proof.
induction q;
intros p tp tq Hp Hq;
destruct p; split; reduce; simpl; fold value_of_pos;
case_eq (Pos.sub_mask p0 q0); 
case_eq (Pos.sub_mask_carry p0 q0); intros;
  (econstructor;
  [ reduce; apply IHq; auto with *
  | try rewrite H; try rewrite H0; tauto
  | try reduce; auto with *]).
Qed.

Definition sub_mask_correct' : ltac:(auto_for_auto sub_mask_correct) := sub_mask_correct.
Hint Resolve sub_mask_correct' : eval.

Lemma compare_cont_correct p: forall tp tq q,
evaluates tp (value_of_pos p) ->
evaluates tq (value_of_pos q) ->
evaluates (compare_contEqF (: term_from_value (value_of_pos p),
                              term_from_value (value_of_pos q) :))
          (value_of_comp (Pos.compare_cont Eq p q)) /\
evaluates (compare_contLtF (: term_from_value (value_of_pos p),
                              term_from_value (value_of_pos q) :))
          (value_of_comp (Pos.compare_cont Lt p q)) /\
evaluates (compare_contGtF (: term_from_value (value_of_pos p),
                              term_from_value (value_of_pos q) :))
          (value_of_comp (Pos.compare_cont Gt p q)).
Proof.
induction p; intros tp tq q; destruct q; intros Hp Hq; repeat reduce;
simpl in *;
fold value_of_pos;
eapply IHp; auto with *.
Qed.

Definition compare_cont_correct' : ltac:(auto_for_auto compare_cont_correct) := compare_cont_correct.
Hint Resolve compare_cont_correct' : eval.

Lemma compare_correct p: forall q tp tq,
evaluates tp (value_of_pos p) ->
evaluates tq (value_of_pos q) ->
evaluates (compareF (: tp, tq :)) (value_of_comp (Pos.compare p q)).
Proof.
intros q tp tq Htp Htq; reduce;
eapply (compare_cont_correct p); auto with *.
Qed.

Definition compare_correct' : ltac:(auto_for_auto compare_correct) := compare_correct.
Hint Resolve compare_correct' : eval.


Lemma succ_double_correct t n :
evaluates t (value_of_N n) ->
evaluates (succ_doubleF (: t :)) (value_of_N (N.succ_double n)).
Proof. destruct n; reduce. Qed.

Definition succ_double_correct' : ltac:(auto_for_auto succ_double_correct) := succ_double_correct.
Hint Resolve succ_double_correct' : eval.

Lemma double_correct n : forall t,
evaluates t (value_of_N n) ->
evaluates (doubleF (: t :)) (value_of_N (N.double n)).
Proof. destruct n; reduce. Qed.

Definition double_correct' : ltac:(auto_for_auto double_correct) := double_correct.
Hint Resolve double_correct' : eval.

Lemma sub_correct n m tn tm:
evaluates tn (value_of_N n) ->
evaluates tm (value_of_N m) ->
evaluates (subF (: tn , tm :)) 
          (value_of_N (N.sub n m)).
Proof.
intros Hn Hm;
destruct n, m; reduce; simpl;
case_eq (Pos.sub_mask p0 p1);
intros;
(econstructor;
[ repeat constructor;
  eapply sub_mask_correct; auto with *
| rewrite H; tauto
| try reduce; auto with eval]).
Qed.

Definition sub_correct' : ltac:(auto_for_auto sub_correct) := sub_correct.
Hint Resolve sub_correct' : eval.

Lemma compare0_correct n: forall m tn tm,
evaluates tn (value_of_N n) ->
evaluates tm (value_of_N m) ->
evaluates (compare0F (: tn, tm :)) 
          (value_of_comp (N.compare n m)).
Proof. induction n; intro m; intros; destruct m; reduce. Qed.

Definition compare0_correct' : ltac:(auto_for_auto compare0_correct) := compare0_correct.
Hint Resolve compare0_correct' : eval.

Lemma leb_aux_correct : forall tc c,
evaluates tc (value_of_comp c) ->
  evaluates (leb_auxF (: tc :)) 
             (value_of_bool (match c with Gt => false | _ => true end)).
Proof. intros tc c; destruct c; repeat split; reduce. Qed.

Definition leb_aux_correct' : ltac:(auto_for_auto leb_aux_correct) := leb_aux_correct.
Hint Resolve leb_aux_correct' : eval.

Lemma leb_correct tn tm (n m : N) :
evaluates tn (value_of_N n) ->
evaluates tm (value_of_N m) ->
evaluates (lebF (: tn, tm :)) (value_of_bool (N.leb n m)).
Proof. reduce. Qed.

Definition leb_correct' : ltac:(auto_for_auto leb_correct) := leb_correct.
Hint Resolve leb_correct' : eval.

Lemma cond_correct {A} f tc ta tb c (a b : A) :
evaluates tc (value_of_bool c) ->
evaluates ta (f a) ->
evaluates tb (f b) ->
 evaluates (condF (: tc, ta, tb :))
           (f (if c then a else b)).
Proof. destruct c; reduce. Qed.

Definition cond_correct' A : ltac:(auto_for_auto (@cond_correct A)) := cond_correct.
Hint Resolve cond_correct' : eval.


Lemma mod_succ_double_compat n m :
(if m <=? N.succ_double (n mod m)
 then N.succ_double (n mod m) - m
 else N.succ_double (n mod m)) = N.succ_double n mod m.
Proof.
destruct n as [| n].
- destruct m as [|[m|m|]]; trivial.
- unfold N.modulo.
  case_eq (N.div_eucl (N.pos n) m); intros q r Hqr.
  simpl.
  destruct m as [|m]; trivial; simpl.
  + now simpl in Hqr; inversion Hqr; subst.
  + simpl in Hqr; rewrite Hqr.
    destruct(N.pos m <=? N.succ_double r); trivial.
Qed.


Lemma mod_double_compat n m :
(if m <=? N.double (n mod m)
 then N.double (n mod m) - m
 else N.double (n mod m)) = N.double n mod m.
Proof.
destruct n as [| n].
- destruct m as [|[m|m|]]; trivial.
- unfold N.modulo.
  case_eq (N.div_eucl (N.pos n) m); intros q r Hqr.
  simpl.
  destruct m as [|m]; trivial; simpl.
  + now simpl in Hqr; inversion Hqr; subst.
  + simpl in Hqr; rewrite Hqr.
    destruct(N.pos m <=? N.double r); trivial.
Qed.

Lemma mod_aux_correct n m tn tm:
evaluates tn (value_of_pos n) ->
evaluates tm (value_of_N m) ->
evaluates (mod_auxF (: tn, tm :)) (value_of_N (N.modulo (N.pos n) m)).
Proof.
revert tn tm.
induction n; intros tn tm Hn Hm.
- reduce; evar (v1: N); evar (v2: N).
  replace (N.pos n~1 mod m) with 
          (if m <=? N.succ_double (N.pos n mod m) then v1 else v2).
  apply cond_correct.
  + apply leb_correct; simpl; auto with *.
    apply succ_double_correct; auto with *.
  + apply sub_correct.
    apply succ_double_correct.
    apply IHn; auto with *.
    simpl; auto with *.
  + apply succ_double_correct.
    apply IHn; auto with *.
  + subst v1 v2.
    apply mod_succ_double_compat.
- reduce; evar (v1: N); evar (v2: N).
  replace (N.pos n~0 mod m) with 
          (if m <=? N.double (N.pos n mod m) then v1 else v2).
  apply cond_correct.
  + apply leb_correct; simpl; auto with *.
    apply double_correct; auto with *.
  + apply sub_correct.
    apply double_correct.
    apply IHn; auto with *.
    simpl; auto with *.
  + apply double_correct.
    apply IHn; auto with *.
  + subst v1 v2.
    apply mod_double_compat.
- destruct m as [| [ m | m |]]; simpl; reduce.
Qed.

Definition mod_aux_correct' : ltac:(auto_for_auto mod_aux_correct) := mod_aux_correct.
Hint Resolve mod_aux_correct' : eval.

Lemma mod_0 n : n mod 0 = n.
Proof.
destruct n; trivial.
Qed.

Lemma mod_correct n m tn tm: 
evaluates tn (value_of_N n) ->
evaluates tm (value_of_N m) ->
evaluates (modF (: tn, tm :)) (value_of_N (N.modulo n m)).
Proof.
destruct n; reduce.
Qed.

Definition mod_correct' : ltac:(auto_for_auto mod_correct) := mod_correct.
Hint Resolve mod_correct' : eval.

Lemma succ_correct p: forall t,
evaluates t (value_of_pos p) ->
evaluates (succF (: t :)) (value_of_pos (Pos.succ p)).
Proof. induction p; intros; reduce; apply IHp; auto with *. Qed.

Lemma add_correct p: forall q tp tq,
evaluates tp (value_of_pos p) ->
evaluates tq (value_of_pos q) ->
evaluates (addF (: tp, tq :)) (value_of_pos (Pos.add p q)) /\
evaluates (add_carryF (: tp, tq :)) (value_of_pos (Pos.add_carry p q)).
Proof.
induction p; intros q tp tq Hp Hq; split; destruct q; reduce;
try (apply IHp || apply succ_correct); auto with *.
Qed.

Lemma add0_correct n m: forall tn tm,
evaluates tn (value_of_N n) ->
evaluates tm (value_of_N m) ->
evaluates (add0F (: tn, tm :)) (value_of_N (N.add n m)).
Proof.
destruct n; intros; [ reduce |];
destruct m; [ reduce | reduce; apply add_correct; auto with * ].
Qed.

Inductive larger_bound : positive -> positive -> Type :=
  | larger_1  : forall b, larger_bound xH b
  | larger_xI : forall x b, larger_bound x b -> larger_bound (xI x) (xO b)
  | larger_xO : forall x b, larger_bound x b -> larger_bound (xO x) (xO b).

Lemma larger_bound_xO p b: 
 larger_bound p b -> larger_bound p b~0.
Proof.
intro H; induction H; constructor; assumption.
Qed.

Lemma mul_mod_aux_correct p1 p2 m: forall n tp1 tp2 tn tm,
m <> 0 ->
larger_bound p1 p2 ->
evaluates tp1 (value_of_pos p1) ->
evaluates tp2 (value_of_pos p2) ->
evaluates tn (value_of_N n) ->
evaluates tm (value_of_N m) ->
evaluates (mul_mod_auxF (: tp1, tn, tm, tp2 :))
          ((N.pos p1 * n) mod m).
Proof.
revert p2.
induction p1 as [ p | p |]; intros p2 n tp1 tp2 tn tm Hpos Hb H1 H2 Hn Hm;
inversion Hb; subst; reduce.
- replace (N.pos p~1 * n) with (n + N.double (N.pos p * n)) by (now destruct n).
  rewrite <- N.add_mod_idemp_r; trivial.
  rewrite N.double_spec.
  rewrite <- N.mul_mod_idemp_r; trivial.
  rewrite <- N.double_spec.
  rewrite N.add_mod_idemp_r; trivial.
  apply mod_correct; auto with *.
  apply add0_correct; auto with *.
  apply double_correct; auto with *.
  apply IHp with (p2 := b); auto with *.
- replace (N.pos p~0 * n) with (N.double (N.pos p * n)) by (now destruct n).
  rewrite N.double_spec.
  rewrite <- N.mul_mod_idemp_r; trivial.
  rewrite <- N.double_spec.
  apply mod_correct; auto with *.
  apply double_correct; auto with *.
  apply IHp with (p2 := b); auto with *.
- apply mod_correct.
  + destruct n; auto with eval.
  + auto with *.
Qed.

Definition N_larger_bound n b := match n with
| 0 => larger_bound xH b
| Npos p0 => larger_bound p0 b
end.

Fixpoint lower_bound p0 := match p0 with
| xH => xH
| xO p0 => xO (lower_bound p0)
| xI p0 => xO (lower_bound p0)
end.

Lemma lower_bound_bound p0 : larger_bound p0 (lower_bound p0).
Proof.
induction p0; now constructor.
Qed.

Lemma lower_bound_pow2 k : (lower_bound (2^ k) = 2^k)%positive.
Proof.
induction k using Pos.peano_ind.
- simpl; trivial.
- simpl.
  rewrite Pos.pow_succ_r.
  simpl; now f_equal.
Qed.

Lemma lower_bound_div_bound (p0 b : positive) :
larger_bound p0 b -> {k | (b = k * lower_bound p0)%positive}.
Proof.
revert b; induction p0; intros b Hb; inversion Hb; subst.
- destruct (IHp0 b0 H0) as (k & Hk).
  exists k; simpl; lia.
- destruct (IHp0 b0 H0) as (k & Hk).
  exists k; simpl; lia.
- exists b; simpl; lia.
Qed.

Lemma lower_bound_le p0 p1 :
(p0 <= p1 -> {k | lower_bound p1 = k * lower_bound p0})%positive.
Proof.
revert p1.
induction p0; intros p1 Hle.
- destruct p1 as [p1|p1|].
  + simpl in Hle.
    assert(Hle' : (p0 <= p1)%positive) by lia.
    apply IHp0 in Hle'.
    destruct Hle' as [k Hk].
    exists k;simpl;lia.
  + simpl in Hle.
    assert(Hle' : (p0 <= p1)%positive) by lia.
    apply IHp0 in Hle'.
    destruct Hle' as [k Hk].
    exists k;simpl;lia.
  + contradict Hle; lia.
- destruct p1 as [p1|p1|].
  + simpl in Hle.
    assert(Hle' : (p0 <= p1)%positive) by lia.
    apply IHp0 in Hle'.
    destruct Hle' as [k Hk].
    exists k;simpl;lia.
  + simpl in Hle.
    assert(Hle' : (p0 <= p1)%positive) by lia.
    apply IHp0 in Hle'.
    destruct Hle' as [k Hk].
    exists k;simpl;lia.
  + contradict Hle; lia.
- exists (lower_bound p1); simpl; lia.
Qed.

Lemma larger_bound_spec p0 k:
  larger_bound p0 (k * lower_bound p0).
Proof.
induction p0.
- simpl; rewrite Pos.mul_xO_r; now constructor.
- simpl; rewrite Pos.mul_xO_r; now constructor.
- constructor.
Qed.

Lemma N_larger_bound_le n n' b :
 n' <= n ->
 N_larger_bound n b ->
 N_larger_bound n' b.
Proof.
intros Hle Hb.
destruct n' as [| n'].
- simpl; constructor.
- destruct n as [| n]; [ now destruct Hle |].
  simpl in *.
  destruct (lower_bound_div_bound n b Hb) as (k & Hk).
  apply lower_bound_le in Hle.
  destruct Hle as (k' & Hk').
  rewrite Hk' in Hk.
  rewrite Hk.
  replace (k * (k' * lower_bound n'))%positive 
    with (k * k' * lower_bound n')%positive by lia.
  apply larger_bound_spec.
Qed.

Lemma N_larger_bound_mod n m b :
 m <> 0 ->
 N_larger_bound m b ->
 N_larger_bound (n mod m) b.
Proof.
intro H; now apply N_larger_bound_le, N.lt_le_incl, N.mod_lt.
Qed.

Hint Resolve N_larger_bound_mod : eval.

Lemma mul_mod_correct n n' m b: forall tn tn' tm tb,
m <> 0 ->
N_larger_bound n b ->
evaluates tn (value_of_N n) ->
evaluates tn' (value_of_N n') ->
evaluates tm (value_of_N m) ->
evaluates tb (value_of_pos b) ->
evaluates (mul_modF (: tn, tn', tm, tb:))
          ((n * n') mod m).
Proof.
intros; destruct n; reduce.
apply mul_mod_aux_correct with (p2 := b); auto with eval.
Qed.

Lemma exp_mod_aux_correct y: forall x m tx ty tm b tb,
m <> 0 ->
N_larger_bound m b ->
evaluates tx (value_of_N x) ->
evaluates ty (value_of_pos y) ->
evaluates tm (value_of_N m) ->
evaluates tb (value_of_pos b) ->
evaluates (exp_mod_auxF (: tx, ty, tm, tb :))
          ( x ^ (Npos y) mod m).
Proof.
induction y as [ y | y | ]; intros x m tx ty tm b tb Hpos Hlarger Hx Hy Hm Hb.
- change (Npos y~1) with (N.succ (N.pos y~0)).
  rewrite N.pow_succ_r; [ | lia].
  change (N.pos y~0) with (2 * (N.pos y)).
  rewrite N.pow_mul_r, <- N.mul_mod_idemp_r; trivial.
  rewrite <- N.mod_mod; trivial.
  rewrite <- N.mul_mod_idemp_l; trivial.
  rewrite N.mod_mod; trivial.
  reduce.
  apply mul_mod_correct with b; auto with *.
  rewrite N.pow_2_r.
  rewrite N.pow_mul_l, N.mul_mod; trivial.
  apply mul_mod_correct with b; auto with *; 
  apply IHy with b; auto with *.
- change (N.pos y~0) with (2 * (N.pos y)).
  rewrite N.pow_mul_r, N.pow_2_r, N.pow_mul_l, N.mul_mod; trivial.
  reduce.
  apply mul_mod_correct with b; auto with *;
  apply IHy with b; auto with *.
- reduce.
  apply mod_correct; simpl; auto with *.
  destruct x; auto with *.
  rewrite Pos.pow_1_r; auto with *.
Qed.

Lemma bound_correct_pos x tx:
evaluates tx (value_of_pos x) ->
evaluates (boundF (: tx :)) (value_of_pos (2^(Pos.size x))).
Proof.
revert tx.
induction x; intros; reduce; simpl;
rewrite Pos.pow_succ_r; reduce; apply IHx; auto with *.
Qed.

Lemma exp_mod_correct x y m tx ty tm:
m <> 0 ->
evaluates tx (value_of_N x) ->
evaluates ty (value_of_N y) ->
evaluates tm (value_of_N m) ->
evaluates (exp_modF (: tx, ty, tm :))
          ( x ^ y mod m).
Proof.
intros.
destruct y as [ | y].
- reduce.
  apply mod_correct; [ reduce | auto with *].
- reduce.
  destruct m as [|m].
  + apply exp_mod_aux_correct with (b := xH); tauto.
  + apply exp_mod_aux_correct with (b := (2^(Pos.size m))%positive); auto with *.
    * assert (m <= 2^ Pos.size m)%positive by
      (apply Pos.lt_le_incl, Pos.size_gt).
      apply N_larger_bound_le with (n := N.pos (2 ^ Pos.size m)); trivial.
      simpl; rewrite <- lower_bound_pow2 at 2.
      apply lower_bound_bound.
    * reduce; apply bound_correct_pos; auto with *.
Qed.
