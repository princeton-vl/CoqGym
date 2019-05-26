
Require Import General.
Require Export Relations.

Unset Standard Proposition Elimination Names.

Section SortsOfV6.

  (* Definition des composantes du calcul *)

  Inductive calc : Set :=
    | Pos : calc
    | Neg : calc.

  Inductive srt_v6 : Set :=
    | Sprop : calc -> srt_v6
    | Stype : nat -> srt_v6.

  Inductive axiom_v6 : srt_v6 -> srt_v6 -> Prop :=
    | ax_prop : forall (c : calc) (n : nat), axiom_v6 (Sprop c) (Stype n)
    | ax_type : forall n m : nat, n < m -> axiom_v6 (Stype n) (Stype m).

  Inductive rules_v6 : srt_v6 -> srt_v6 -> srt_v6 -> Prop :=
    | rule_prop_l : forall (c : calc) (s : srt_v6), rules_v6 (Sprop c) s s
    | rule_prop_r :
        forall (c : calc) (s : srt_v6), rules_v6 s (Sprop c) (Sprop c)
    | rule_type :
        forall n m p : nat,
        n <= p -> m <= p -> rules_v6 (Stype n) (Stype m) (Stype p).

  Inductive univ_v6 : srt_v6 -> srt_v6 -> Prop :=
    | univ_prop : forall (c : calc) (n : nat), univ_v6 (Sprop c) (Stype n)
    | univ_type : forall n m : nat, n <= m -> univ_v6 (Stype n) (Stype m).

  Definition univ : srt_v6 -> srt_v6 -> Prop := clos_refl_trans _ univ_v6.

  Hint Resolve ax_prop ax_type rule_prop_l rule_prop_r rule_type univ_prop
    univ_type: pts.
  Hint Unfold univ: pts.

  (* Inversion et Decidabilite de l'inclusion entre sortes *)

  Let univ_trans : forall x y z : srt_v6, univ x y -> univ y z -> univ x z.
Proof rt_trans srt_v6 univ_v6.


  Inductive inv_univ : srt_v6 -> srt_v6 -> Prop :=
    | iu_prop : forall c : calc, inv_univ (Sprop c) (Sprop c)
    | iu_pr_ty : forall (c : calc) (n : nat), inv_univ (Sprop c) (Stype n)
    | iu_type : forall n m : nat, n <= m -> inv_univ (Stype n) (Stype m).

  Hint Resolve iu_prop iu_pr_ty iu_type: pts.


  Lemma inv_univ_trans :
   forall x y z : srt_v6, inv_univ x y -> inv_univ y z -> inv_univ x z.
simple induction 1; intros; auto with arith pts.
inversion_clear H0; auto with arith pts.

inversion_clear H1.
apply iu_type.
apply le_trans with m; auto with arith pts.
Qed.


  Lemma univ_inv :
   forall s s' : srt_v6,
   univ s s' -> forall P : Prop, (inv_univ s s' -> P) -> P.
simple induction 1.
simple induction 1; auto with arith pts.

simple destruct x; auto with arith pts.

intros.
apply H4.
apply inv_univ_trans with y.
apply H1; auto with arith pts.

apply H3; auto with arith pts.
Qed.



  Lemma calc_dec : forall c c' : calc, decide (c = c').
simple destruct c; simple destruct c';
 (right; discriminate) || auto with arith pts.
Qed.


  Lemma v6_sort_dec : forall s s' : srt_v6, decide (s = s').
simple destruct s; simple destruct s'; intros; try (right; discriminate).
elim calc_dec with c c0; intros.
left; elim a; auto with arith pts.

right; red in |- *; intros H; apply b; injection H; auto with arith pts.

elim eq_nat_dec with n n0; intros.
left; elim a; auto with arith pts.

right; red in |- *; intros H; apply b; injection H; auto with arith pts.
Qed.


  Lemma univ_v6_dec : forall s s' : srt_v6, decide (univ s s').
refine
 (fun s s' : srt_v6 =>
  match s, s' return (decide (univ s s')) with
  | Sprop c, Sprop c' => _
  | Sprop _, Stype _ => left _ _
  | Stype n, Stype n' => _
  | Stype n, Sprop c => right _ _
  end).
case (calc_dec c c'); [ left | right ].
elim e; auto with arith pts.

red in |- *; intro; apply n.
apply univ_inv with (Sprop c) (Sprop c'); intros; auto with arith pts.
inversion_clear H0; auto with arith pts.

auto with pts.

red in |- *; intros.
apply univ_inv with (Stype n) (Sprop c); intros; auto with arith pts.
inversion_clear H0.

case (le_gt_dec n n'); [ left | right ].
auto with pts.

red in |- *; intros.
apply univ_inv with (Stype n) (Stype n'); intros; auto with arith pts.
inversion_clear H0.
absurd (n <= n'); auto with arith pts.
Qed.


  (* Inference des axiomes et regles *)

  Lemma v6_inf_axiom :
   forall s : srt_v6, {sp : srt_v6 | ppal (axiom_v6 s) univ sp}.
refine
 (fun s : srt_v6 =>
  match s return {sp : srt_v6 | ppal (axiom_v6 s) univ sp} with
  | Sprop c => exist _ (Stype 0) _
  | Stype n => exist _ (Stype (S n)) _
  end).
split; intros; auto with arith pts.
inversion_clear H; auto with arith pts.

split; intros; auto with arith pts.
inversion_clear H; auto with arith pts.
Qed.


  Lemma v6_inf_rule :
   forall x1 x2 : srt_v6,
   {x3 : srt_v6 | rules_v6 x1 x2 x3 & 
   forall s1 s2 s3 : srt_v6,
   rules_v6 s1 s2 s3 -> univ x1 s1 -> univ x2 s2 -> univ x3 s3}.
refine
 (fun x1 x2 : srt_v6 =>
  match
    x1, x2
    return
      {x3 : srt_v6 | rules_v6 x1 x2 x3 & 
      forall s1 s2 s3 : srt_v6,
      rules_v6 s1 s2 s3 -> univ x1 s1 -> univ x2 s2 -> univ x3 s3}
  with
  | Sprop c, _ => exist2 _ _ x2 _ _
  | Stype n, Sprop c' => exist2 _ _ (Sprop c') _ _
  | Stype n, Stype n' => exist2 _ _ (Stype (max_nat n n')) _ _
  end); auto with pts.
simple induction 1; intros; auto with arith pts.
apply univ_trans with (Stype m); auto with arith pts.

intros.
apply univ_inv with (Sprop c') s2; intros; auto with arith pts.
generalize H.
inversion_clear H2; intros.
inversion_clear H2; auto with arith pts.

apply univ_inv with (Sprop c') s2; intros; auto with arith pts.
generalize H.
inversion_clear H3; intros; auto with arith pts.
inversion_clear H3; auto with arith pts.

inversion_clear H3; auto with arith pts.

unfold max_nat in |- *.
elim (le_gt_dec n n'); auto with arith pts.

intros.
apply univ_inv with (Stype n) s1; intros; auto with arith pts.
apply univ_inv with (Stype n') s2; intros; auto with arith pts.
generalize H.
inversion_clear H2.
inversion_clear H3; intros.
inversion_clear H3.
cut (max_nat n n' <= p); auto with arith pts.
apply least_upper_bound_max_nat.
apply le_trans with m; auto with arith pts.

apply le_trans with m0; auto with arith pts.
Qed.


End SortsOfV6.


(* Uniform interface of sorts *)
Require Export GenericSort.

  Definition sort_of_gen (gs : gen_sort) : Exc srt_v6 :=
    match gs with
    | Gprop => value (Sprop Neg)
    | Gset => value (Sprop Pos)
    | Gtype n => value (Stype n)
    | _ => error
    end.

  Definition gen_of_sort (s : srt_v6) : gen_sort :=
    match s with
    | Sprop Neg => Gprop
    | Sprop Pos => Gset
    | Stype n => Gtype n
    end.
