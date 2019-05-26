(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

(** * Object-level representation of Diophantine equations *)
(** ** Diophantine logic *)

Require Import Arith Nat Omega.
Require Import gcd.

Set Implicit Arguments.

Section diophantine_expressions.

  Inductive dio_op := do_add | do_mul.

  Definition do_eval o :=
    match o with
      | do_add => plus
      | do_mul => mult
    end.

  Inductive dio_expression : Set :=
    | de_cst  : nat -> dio_expression
    | de_var  : nat -> dio_expression
    | de_comp : dio_op -> dio_expression -> dio_expression -> dio_expression.

  Definition de_add := de_comp do_add.
  Definition de_mul := de_comp do_mul.

  Fixpoint de_size e :=
    match e with
      | de_cst n => 1
      | de_var x => 1
      | de_comp _ p q => 1 + de_size p + de_size q
    end.

  Fixpoint de_size_Z e :=
    (match e with
      | de_cst n => 1
      | de_var x => 1
      | de_comp _ p q => 1 + de_size_Z p + de_size_Z q
    end)%Z.

  Fact de_size_Z_spec e : de_size_Z e = Z.of_nat (de_size e).
  Proof.
    induction e as [ | | o f Hf g Hg ]; auto.
    simpl de_size; unfold de_size_Z; fold de_size_Z.
    rewrite Nat2Z.inj_succ, Nat2Z.inj_add; omega.
  Qed.

  Fixpoint de_eval ν e  :=
    match e with
      | de_cst n => n
      | de_var x => ν x
      | de_comp o p q => do_eval o (de_eval ν p) (de_eval ν q)
    end.

  Fact de_eval_ext e ν ω : (forall x, ν x = ω x) -> de_eval ν e = de_eval ω e.
  Proof.
    intros H; induction e as [ | | [] ]; simpl; auto.
  Qed.

  (* ρ σ ν *)

  Fixpoint de_subst σ e :=
    match e with
      | de_cst n => de_cst n
      | de_var x => σ x
      | de_comp o p q => de_comp o (de_subst σ p) (de_subst σ q)
    end.

  Fact de_eval_subst σ ν e : de_eval ν (de_subst σ e) = de_eval (fun x => de_eval ν (σ x)) e.
  Proof. induction e as [ | | [] ]; simpl; auto. Qed.

  Fact de_subst_subst σ1 σ2 e : de_subst σ1 (de_subst σ2 e) = de_subst (fun x => de_subst σ1 (σ2 x)) e.
  Proof. induction e as [ | | [] ]; simpl; f_equal; auto. Qed.

  Definition de_ren ρ := de_subst (fun x => de_var (ρ x)).

  Fact de_ren_size ρ e : de_size (de_ren ρ e) = de_size e.
  Proof.
    revert ρ; induction e as [ | | o e He f Hf ]; intros rho; auto.
    unfold de_ren; simpl de_subst; unfold de_size; fold de_size. 
    f_equal; [ f_equal | ].
    * apply He.
    * apply Hf.
  Qed.

  Fact de_ren_size_Z ρ e : de_size_Z (de_ren ρ e) = de_size_Z e.
  Proof. do 2 rewrite de_size_Z_spec; f_equal; apply de_ren_size. Qed.

  Fact de_eval_ren ρ ν e : de_eval ν (de_ren ρ e)  = de_eval (fun x => ν (ρ x)) e.
  Proof. apply de_eval_subst. Qed.

  Definition de_lift := de_ren S.

  Fact de_eval_lift ν e : de_eval ν (de_lift e) = de_eval (fun x => ν (S x)) e.
  Proof. apply de_eval_ren. Qed.

End diophantine_expressions.

Definition dio_expr t := { e | forall ν, de_eval ν e = t ν }.

Notation 𝔻P := dio_expr.

Section dio_expr.

  (* How to analyse meta-level diophantine expressions *)

  Implicit Types r t : (nat -> nat) -> nat.

  Fact dio_expr_var i : 𝔻P (fun v => v i).
  Proof. exists (de_var i); simpl; auto. Defined.

  Fact dio_expr_cst c : 𝔻P (fun _ => c).
  Proof. exists (de_cst c); simpl; auto. Defined.

  Fact dio_expr_plus r t : 𝔻P r -> 𝔻P t -> 𝔻P (fun ν => r ν + t ν).
  Proof. intros (e1 & H1) (e2 & H2); exists (de_add e1 e2); simpl; auto. Defined.
  
  Fact dio_expr_mult r t : 𝔻P r -> 𝔻P t -> 𝔻P (fun ν => r ν * t ν).
  Proof. intros (e1 & H1) (e2 & H2); exists (de_mul e1 e2); simpl; auto. Defined.

  Fact dio_expr_ren t ρ : 𝔻P t -> 𝔻P (fun ν => t (fun i => ν (ρ i))).
  Proof. intros (e & He); exists (de_ren ρ e); intros; rewrite de_eval_ren, He; tauto. Defined.

  Fact dio_expr_subst t σ : 𝔻P t -> 𝔻P (fun ν => t (fun i => de_eval ν (σ i))).
  Proof. intros (e & He); exists (de_subst σ e); intros; rewrite de_eval_subst, He; tauto. Defined.

End dio_expr.

Hint Resolve dio_expr_var dio_expr_cst dio_expr_plus dio_expr_mult dio_expr_ren.

Section diophantine_logic.

  (* De Bruin syntax for diophantine formulas of the form

         A,B ::= e1 = e2 | A /\ B | A \/ B | ∃x.A

   *)

  Inductive dio_formula : Set :=
    | df_atm  : dio_expression -> dio_expression -> dio_formula   (* a = b *)
    | df_conj : dio_formula -> dio_formula -> dio_formula 
    | df_disj : dio_formula -> dio_formula -> dio_formula
    | df_exst : dio_formula -> dio_formula.

  Fixpoint df_size f :=
    match f with
      | df_atm a b  => 1 + de_size a + de_size b
      | df_conj f g => 1 + df_size f + df_size g  
      | df_disj f g => 1 + df_size f + df_size g  
      | df_exst f   => 1 + df_size f
    end.

  Fixpoint df_size_Z f :=
    (match f with
      | df_atm a b  => 1 + de_size_Z a + de_size_Z b
      | df_conj f g => 1 + df_size_Z f + df_size_Z g  
      | df_disj f g => 1 + df_size_Z f + df_size_Z g  
      | df_exst f   => 1 + df_size_Z f
    end)%Z.

  Fact df_size_Z_spec f : df_size_Z f = Z.of_nat (df_size f).
  Proof.
    induction f as [ a b | f Hf g Hg | f Hf g Hg | f Hf ]; simpl df_size;
      rewrite Nat2Z.inj_succ; try rewrite Nat2Z.inj_add; unfold df_size_Z; fold df_size_Z; auto; try omega.
    do 2 rewrite de_size_Z_spec; omega.
  Qed.


  (* dv_lift : lifting of a diophantive valuation *)

  Definition dv_lift X ν (x : X) n :=
     match n with 
       | 0   => x 
       | S n => ν n 
     end.

  Fixpoint df_pred f ν :=
    match f with
      | df_atm a b  => de_eval ν a  = de_eval ν b
      | df_conj f g => df_pred f ν /\ df_pred g ν
      | df_disj f g => df_pred f ν \/ df_pred g ν
      | df_exst f   => exists n, df_pred f (dv_lift ν n)
    end.

  Fact df_pred_atm a b ν : df_pred (df_atm a b) ν = (de_eval ν a = de_eval ν b).
  Proof. auto. Qed.
  
  Fact df_pred_conj f g ν : df_pred (df_conj f g) ν = (df_pred f ν /\ df_pred g ν).
  Proof. auto. Qed.

  Fact df_pred_disj f g ν : df_pred (df_disj f g) ν = (df_pred f ν \/ df_pred g ν).
  Proof. auto. Qed.

  Fact df_pred_exst f ν : df_pred (df_exst f) ν = exists n, df_pred f (dv_lift ν n).
  Proof. auto. Qed.

  Fact df_pred_ext f ν ω : (forall x, ν x = ω x) -> df_pred f ν <-> df_pred f ω.
  Proof.
    revert ν ω; induction f as [ a b | f Hf g Hg | f Hf g Hg | f Hf ]; intros ν ω H; simpl.
    + do 2 rewrite de_eval_ext with (1 := H); tauto.
    + rewrite Hf, Hg; auto; tauto.
    + rewrite Hf, Hg; auto; tauto.
    + split; intros (n & Hn); exists n; revert Hn; apply Hf;
        intros []; simpl; auto.
  Qed.

  (* Lifting of a diophantine expression renaming *)

  Definition der_lift ρ x := match x with 0 => 0 | S x => S (ρ x) end.

  Fixpoint df_ren ρ f :=
    match f with
      | df_atm a b  => let σ := fun x => de_var (ρ x) in df_atm (de_subst σ a) (de_subst σ b)
      | df_conj f g => df_conj (df_ren ρ f) (df_ren ρ g)
      | df_disj f g => df_disj (df_ren ρ f) (df_ren ρ g)
      | df_exst f   => df_exst (df_ren (der_lift ρ) f)
    end.

  Fact df_ren_size ρ f : df_size (df_ren ρ f) = df_size f.
  Proof.
    revert ρ; induction f; intros; simpl; auto; do 2 f_equal; auto.
    all: apply de_ren_size.
  Qed.

  Fact df_ren_size_Z ρ f : df_size_Z (df_ren ρ f) = df_size_Z f.
  Proof.
    do 2 rewrite df_size_Z_spec; f_equal; apply df_ren_size.
  Qed.

  Fact df_pred_ren f ν ρ : df_pred (df_ren ρ f) ν <-> df_pred f (fun x => ν (ρ x)).
  Proof.
    revert ν ρ; induction f as [ a b | f Hf g Hg | f Hf g Hg | f Hf ]; intros ν ρ; simpl.
    + repeat rewrite de_eval_subst; simpl; tauto.
    + rewrite Hf, Hg; tauto.
    + rewrite Hf, Hg; tauto.
    + split; intros (n & Hn); exists n; revert Hn; rewrite Hf;
        apply df_pred_ext; intros []; simpl; auto.
  Qed.

  (* Lifting of a diophantine expression substitutions *)

  Definition des_lift σ x := match x with 0 => de_var 0 | S x => de_ren S (σ x) end. 
     
  Fixpoint df_subst σ f := 
    match f with
      | df_atm a b  => df_atm (de_subst σ a) (de_subst σ b)
      | df_conj f g => df_conj (df_subst σ f) (df_subst σ g)
      | df_disj f g => df_disj (df_subst σ f) (df_subst σ g)
      | df_exst f   => df_exst (df_subst (des_lift σ) f)
    end.

  Fact df_pred_subst f ν σ : df_pred (df_subst σ f) ν <-> df_pred f (fun x => de_eval ν (σ x)).
  Proof.
    revert ν σ; induction f as [ a b | f Hf g Hg | f Hf g Hg | f Hf ]; intros ν σ; simpl.
    + repeat rewrite de_eval_subst; simpl; tauto.
    + rewrite Hf, Hg; tauto.
    + rewrite Hf, Hg; tauto.
    + split; intros (n & Hn); exists n; revert Hn; rewrite Hf;
        apply df_pred_ext; intros []; simpl; auto;
        rewrite de_eval_ren; apply de_eval_ext; auto.
  Qed.

  Definition df_lift := df_ren S.

  Fact df_pred_lift f ν : df_pred (df_lift f) ν <-> df_pred f (fun x => ν (S x)).
  Proof. apply df_pred_ren. Qed. 

End diophantine_logic.

Section examples.

  Variable ν : nat -> nat.

  Definition df_true := df_atm (de_cst 0) (de_cst 0).
  Definition df_false := df_atm (de_cst 0) (de_cst 1).

  Fact df_true_spec : df_pred df_true ν <-> True.
  Proof. simpl; split; auto. Qed.

  Fact df_false_spec : df_pred df_false ν <-> False.
  Proof. simpl; split; try discriminate; tauto. Qed.

  Notation "'⟦' x '⟧'" := (de_eval ν x).

  Definition df_le x y := df_exst (df_atm (de_add (de_var 0) (de_lift x)) (de_lift y)).

  Fact df_le_spec x y : df_pred (df_le x y) ν <-> ⟦x⟧ <= ⟦y⟧.
  Proof.
    simpl.
    split.
    + intros (n & Hn); revert Hn; do 2 rewrite de_eval_lift; simpl.
      change (fun x => ν x) with ν; intros; omega.
    + exists (de_eval ν y - de_eval ν x); simpl.
      repeat rewrite de_eval_lift; simpl.
      change (fun x => ν x) with ν; omega.
  Qed.

  Definition df_lt x y := df_exst (df_atm (de_add (de_cst 1) (de_add (de_var 0) (de_lift x))) (de_lift y)).

  Fact df_lt_spec x y : df_pred (df_lt x y) ν <-> ⟦x⟧ < ⟦y⟧.
  Proof.
    simpl.
    split.
    + intros (? & Hn); revert Hn; simpl.
      do 2 rewrite de_eval_lift; simpl.
      change (fun x => ν x) with ν; intros; omega.
    + exists (de_eval ν y - de_eval ν x - 1); simpl.
      repeat rewrite de_eval_lift; simpl.
      change (fun x => ν x) with ν; omega.
  Qed.

  Definition df_eq x y := df_atm x y.

  Fact df_eq_spec x y : df_pred (df_eq x y) ν <-> ⟦x⟧ = ⟦y⟧.
  Proof. simpl; tauto. Qed.

  Definition df_neq x y := df_disj (df_lt x y) (df_lt y x).

  Fact df_neq_spec x y : df_pred (df_neq x y) ν <-> ⟦x⟧ <> ⟦y⟧.
  Proof.
    unfold df_neq.
    rewrite df_pred_disj, df_lt_spec, df_lt_spec.
    omega.
  Qed.

  Definition df_div x y := df_exst (df_atm (de_lift y) (de_mul (de_var 0) (de_lift x))).

  Fact df_div_spec x y : df_pred (df_div x y) ν <-> divides ⟦x⟧ ⟦y⟧.
  Proof. 
    simpl; unfold divides.
    split; intros (n & H); exists n; revert H; repeat rewrite de_eval_lift;
      simpl; change (fun x => ν x) with ν; auto.
  Qed.

End examples.

Definition dio_rel R := { f | forall ν, df_pred f ν <-> R ν }.
Notation 𝔻R := dio_rel.

Section dio_rel.

  (** How to analyse diophantine relations ... these are proved by
      explicitely given the witness which we will avoid later on *)
  
  Implicit Types R S : (nat -> nat) -> Prop.

  Fact dio_rel_True : 𝔻R (fun _ => True).
  Proof.
    exists df_true.
    intros; rewrite df_true_spec; tauto.
  Defined.

  Fact dio_rel_False : 𝔻R (fun _ => False).
  Proof.
    exists df_false.
    intros; rewrite df_false_spec; tauto.
  Defined.

  Fact dio_rel_eq r t : 𝔻P r -> 𝔻P t -> 𝔻R (fun ν => r ν = t ν).
  Proof.
    intros (e1 & H1) (e2 & H2); exists (df_atm e1 e2).
    intros; rewrite df_pred_atm, H1, H2; tauto.
  Defined.

  Fact dio_rel_le r t : 𝔻P r -> 𝔻P t -> 𝔻R (fun ν => r ν <= t ν).
  Proof. 
    intros (e1 & H1) (e2 & H2); exists (df_le e1 e2).
    intro; rewrite df_le_spec, H1, H2; tauto.
  Defined.

  Fact dio_rel_lt r t : 𝔻P r -> 𝔻P t -> 𝔻R (fun ν => r ν < t ν).
  Proof. 
    intros (e1 & H1) (e2 & H2); exists (df_lt e1 e2).
    intro; rewrite df_lt_spec, H1, H2; tauto.
  Defined.

  Fact dio_rel_neq r t : 𝔻P r -> 𝔻P t -> 𝔻R (fun ν => r ν <> t ν).
  Proof.
    intros (e1 & H1) (e2 & H2); exists (df_neq e1 e2).
    intros; rewrite df_neq_spec, H1, H2; tauto.
  Defined.

  Fact dio_rel_div r t : 𝔻P r -> 𝔻P t -> 𝔻R (fun ν => divides (r ν) (t ν)).
  Proof.
    intros (e1 & H1) (e2 & H2); exists (df_div e1 e2).
    intros; rewrite df_div_spec, H1, H2; tauto.
  Defined.

  Fact dio_rel_conj R S : 𝔻R R -> 𝔻R S -> 𝔻R (fun ν => R ν /\ S ν).
  Proof.
    intros (fR & H1) (fS & H2).
    exists (df_conj fR fS); intros v.
    rewrite df_pred_conj, H1, H2; tauto.
  Defined.

  Fact dio_rel_disj R S : 𝔻R R -> 𝔻R S -> 𝔻R (fun ν => R ν \/ S ν).
  Proof.
    intros (fR & H1) (fS & H2).
    exists (df_disj fR fS); intros v.
    rewrite df_pred_disj, H1, H2; tauto.
  Defined.

  Fact dio_rel_exst (K : nat -> (nat -> nat) -> Prop) : 
                   𝔻R (fun v => K (v 0) (fun n => v (S n))) 
      -> 𝔻R (fun ν => exists x, K x ν).
  Proof.
    intros (f & Hf).
    exists (df_exst f); intros v.
    rewrite df_pred_exst.
    split; intros (n & Hn); exists n; revert Hn; rewrite Hf; simpl; auto.
  Defined.

  Lemma dio_rel_equiv R S : (forall ν, S ν <-> R ν) -> 𝔻R R -> 𝔻R S.
  Proof. 
    intros H (f & Hf); exists f; intro; rewrite Hf, H; tauto.
  Defined.

  Lemma dio_rel_ren R f : 𝔻R R -> 𝔻R (fun v => R (fun n => v (f n))).
  Proof.
    intros (r & HR).
    exists (df_ren f r).
    intros; rewrite df_pred_ren, HR; tauto.
  Defined.

  Lemma dio_rel_subst R f : 𝔻R R -> 𝔻R (fun v => R (fun n => de_eval v (f n))).
  Proof.
    intros (r & HR).
    exists (df_subst f r).
    intros; rewrite df_pred_subst, HR; tauto.
  Defined.

End dio_rel.

Hint Resolve dio_rel_True dio_rel_False dio_rel_eq dio_rel_neq 
             dio_rel_le dio_rel_lt dio_rel_div 
             dio_rel_conj 
             dio_rel_disj 
             dio_rel_exst.

Ltac dio_rel_auto := repeat ((apply dio_rel_exst || apply dio_rel_conj || apply dio_rel_disj || apply dio_rel_eq); auto).

Section more_examples.

  Fact ndivides_eq x y : ~ (divides x y) <-> x = 0 /\ y <> 0 \/ exists a b, y = a*x+b /\ 0 < b < x.
  Proof.
    split.
    + intros H.
      destruct x as [ | x ].
      * left; split; auto; contradict H; subst; apply divides_0.
      * right; exists (div y (S x)), (rem y (S x)); split.
        - apply div_rem_spec1.
        - rewrite divides_rem_eq in H.
          generalize (@div_rem_spec2 y (S x)); intros; omega.
    + intros [ (H1 & H2) | (a & b & H1 & H2) ].
      * subst; contradict H2; revert H2; apply divides_0_inv.
      * rewrite divides_rem_eq.
        rewrite (div_rem_spec1 y x) in H1.
        apply div_rem_uniq in H1; try omega.
        apply div_rem_spec2; omega.
  Qed.
  
  Lemma dio_rel_ndivides x y : 𝔻P x -> 𝔻P y -> 𝔻R (fun ν => ~ divides (x ν) (y ν)).
  Proof.
    intros.
    apply dio_rel_equiv with (1 := fun v => ndivides_eq (x v) (y v)).
    dio_rel_auto.
  Qed.

  Hint Resolve dio_rel_ndivides.

  Fact rem_equiv p x r : r = rem x p <-> (p = 0 /\ x = r)
                                      \/ (p <> 0 /\ r < p /\ exists n, x = n*p + r).
  Proof.
    split.
    + intro; subst.
      destruct (eq_nat_dec p 0) as [ Hp | Hp ].
      * left; split; auto; subst; rewrite rem_0; auto.
      * right; split; auto; split.
        - apply div_rem_spec2; auto.
        - exists (div x p);apply div_rem_spec1.
    + intros [ (H1 & H2) | (H1 & H2 & n & H3) ].
      * subst; rewrite rem_0; auto.
      * symmetry; apply rem_prop with n; auto.
  Qed.
 
  Lemma dio_rel_remainder p x r : 𝔻P p -> 𝔻P x -> 𝔻P r  
                               -> 𝔻R (fun ν => r ν = rem (x ν) (p ν)).
  Proof.
    intros.
    apply dio_rel_equiv with (1 := fun v => rem_equiv (p v) (x v) (r v)).
    dio_rel_auto.
  Defined.

  (* Eval compute in proj1_sig (dio_rel_remainder (dio_expr_var 0) (dio_expr_var 1) (dio_expr_var 2)). *)

  Hint Resolve dio_rel_remainder.

  Fact congr_equiv x y p : rem x p = rem y p <-> (exists r, r = rem x p /\ r = rem y p).
  Proof.
    split.
    + intros H; exists (rem x p); auto.
    + intros (? & ? & ?); subst; auto.
  Qed.

  Lemma dio_rel_congruence x y p : 𝔻P x -> 𝔻P y -> 𝔻P p  
                                -> 𝔻R (fun ν => rem (x ν) (p ν) = rem (y ν) (p ν)).
  Proof.
    intros.
    apply dio_rel_equiv with (1 := fun v => congr_equiv (x v) (y v) (p v)).
    dio_rel_auto.
  Defined.

  Hint Resolve dio_rel_congruence.

  Fact not_divides_eq p x : ~ divides p x <-> exists r, r = rem x p /\ r <> 0.
  Proof.
    rewrite divides_rem_eq.
    split.
    + exists (rem x p); auto.
    + intros (? & ? & ?); subst; auto.
  Qed.

  Lemma dio_rel_not_divides x p : 𝔻P x -> 𝔻P p -> 𝔻R (fun ν => ~ divides (x ν) (p ν)).
  Proof.
    intros.
    apply dio_rel_equiv with (1 := fun v => not_divides_eq (x v) (p v)).
    dio_rel_auto.
  Defined.

End more_examples.

Hint Resolve dio_rel_congruence dio_rel_not_divides.

(* Even computation in Coq works well

Eval compute in proj1_sig (dio_rel_congruence (dio_expr_var 0) (dio_expr_var 1) (dio_expr_var 2)).
Eval compute in proj1_sig (dio_rel_not_divides (dio_expr_var 0) (dio_expr_var 1)).

*)

Section dio_rel_compose.

  Variable (f : (nat -> nat) -> nat) (R : nat -> (nat -> nat) -> Prop).
  Hypothesis (Hf : 𝔻R (fun ν => ν 0 = f (fun x => ν (S x)))) 
             (HR : 𝔻R (fun ν => R (ν 0) (fun x => ν (S x)))).

  Lemma dio_rel_compose : 𝔻R (fun ν => R (f ν) ν).
  Proof.
    apply dio_rel_equiv with (R := fun v => exists y, y = f v /\ R y v).
    + intros v; split.
      * exists (f v); auto.
      * intros (? & -> & ?); auto.
    + dio_rel_auto.
  Defined.

End dio_rel_compose.

Section multiple_exists.

  Fixpoint df_mexists n f :=
    match n with 
      | 0   => f
      | S n => df_mexists n (df_exst f)
    end.

  Fact df_mexists_size n f : df_size (df_mexists n f) = n + df_size f.
  Proof. 
    revert f; induction n as [ | n IHn ]; intros f; auto; simpl df_mexists.
    rewrite IHn; simpl; omega. 
  Qed.

  Fact df_mexists_size_Z n f : df_size_Z (df_mexists n f) = (Z.of_nat n + df_size_Z f)%Z.
  Proof.
    rewrite df_size_Z_spec, df_mexists_size, Nat2Z.inj_add, df_size_Z_spec; omega. 
  Qed.

  (* We only use it once so there is no need to automatize it *)

  Lemma df_mexists_spec n f ν : 
           df_pred (df_mexists n f) ν 
       <-> exists π, df_pred f (fun i => if le_lt_dec n i then ν (i-n) else π i).
  Proof.
    revert f ν; induction n as [ | n IHn ]; intros f v.
    + simpl; split; [ intros H; exists (fun _ => 0) | intros (_ & H) ]; revert H; 
        apply df_pred_ext; intros; f_equal; omega.
    + simpl df_mexists; rewrite IHn; split; intros (pi & Hpi).
      * revert Hpi; rewrite df_pred_exst.
        intros (u & Hu).
        exists (fun i => match i with 0 => u | S i => pi i end).
        revert Hu; apply df_pred_ext.
        intros [ | i ].
        - replace (0-S n) with 0 by omega; simpl; auto.
        - replace (S i - S n) with (i-n) by omega.
          simpl dv_lift. 
          destruct (le_lt_dec (S n) (S i)); destruct (le_lt_dec n i); auto; omega.
      * exists (fun i => pi (S i)).
        rewrite df_pred_exst; exists (pi 0).
        revert Hpi; apply df_pred_ext.
        intros [ | i ].
        - replace (0-S n) with 0 by omega; simpl; auto.
        - replace (S i - S n) with (i-n) by omega.
          simpl dv_lift. 
          destruct (le_lt_dec (S n) (S i)); destruct (le_lt_dec n i); auto; omega.
  Qed.

End multiple_exists.



