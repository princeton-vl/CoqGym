
Require Import General.
Require Export Relations.

Unset Standard Proposition Elimination Names.

Section SortsOfECC.

  Inductive calc : Set :=
    | Pos : calc
    | Neg : calc.

  Inductive srt_ecc : Set :=
    | Sprop : calc -> srt_ecc
    | Stype : calc -> nat -> srt_ecc.

  Inductive axiom_ecc : srt_ecc -> srt_ecc -> Prop :=
    | ax_prop : forall (c : calc) (n : nat), axiom_ecc (Sprop c) (Stype c n)
    | ax_type :
        forall (c : calc) (n m : nat),
        n < m -> axiom_ecc (Stype c n) (Stype c m).

  Inductive rules_ecc : srt_ecc -> srt_ecc -> srt_ecc -> Prop :=
    | rule_prop_l : forall (c : calc) (s : srt_ecc), rules_ecc (Sprop c) s s
    | rule_prop_r :
        forall (c : calc) (s : srt_ecc), rules_ecc s (Sprop c) (Sprop c)
    | rule_type :
        forall (c1 c2 : calc) (n m p : nat),
        n <= p -> m <= p -> rules_ecc (Stype c1 n) (Stype c2 m) (Stype c2 p).

  Inductive univ_ecc : srt_ecc -> srt_ecc -> Prop :=
      univ_type :
        forall (c : calc) (n m : nat),
        n <= m -> univ_ecc (Stype c n) (Stype c m).

  Definition univ : relation srt_ecc := clos_refl_trans _ univ_ecc.

  Hint Resolve ax_prop ax_type rule_prop_l rule_prop_r rule_type univ_type:
    pts.
  Hint Unfold univ: pts.


  (* Inversion et Decidabilite de l'inclusion entre sortes *)

  Let univ_trans : forall x y z : srt_ecc, univ x y -> univ y z -> univ x z.
Proof rt_trans srt_ecc univ_ecc.


  Inductive inv_univ : srt_ecc -> srt_ecc -> Prop :=
    | iu_prop : forall c : calc, inv_univ (Sprop c) (Sprop c)
    | iu_type :
        forall (c : calc) (n m : nat),
        n <= m -> inv_univ (Stype c n) (Stype c m).

  Hint Resolve iu_prop iu_type: pts.


  Lemma inv_univ_trans :
   forall x y z : srt_ecc, inv_univ x y -> inv_univ y z -> inv_univ x z.
simple induction 1; intros; auto with arith pts.
inversion_clear H1.
apply iu_type.
apply le_trans with m; auto with arith pts.
Qed.


  Lemma univ_inv :
   forall s s' : srt_ecc,
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


  Lemma ecc_sort_dec : forall s s' : srt_ecc, decide (s = s').
simple destruct s; simple destruct s'; intros; try (right; discriminate).
elim calc_dec with c c0; intros.
left; elim a; auto with arith pts.

right; red in |- *; intros H; apply b; injection H; auto with arith pts.

elim eq_nat_dec with n n0; intros.
elim calc_dec with c c0; intros.
left; elim a; elim a0; auto with arith pts.

right; red in |- *; intros H; apply b; injection H; auto with arith pts.

right; red in |- *; intros H; apply b; injection H; auto with arith pts.
Qed.


  Lemma univ_ecc_dec : forall s s' : srt_ecc, decide (univ s s').
refine
 (fun s s' : srt_ecc =>
  match s, s' return (decide (univ s s')) with
  | Sprop c, Sprop c' => _
  | Stype c n, Stype c' n' => _
  | Sprop c, Stype c0 n => right _ _
  | Stype c n, Sprop c0 => right _ _
  end).
case (calc_dec c c'); [ left | right ].
elim e; auto with arith pts.

red in |- *; intro; apply n.
apply univ_inv with (Sprop c) (Sprop c'); intros; auto with arith pts.
inversion_clear H0; auto with arith pts.

red in |- *; intros.
apply univ_inv with (Sprop c) (Stype c0 n); intros; auto with arith pts.

inversion_clear H0.

red in |- *; intros.
apply univ_inv with (Stype c n) (Sprop c0); intros; auto with arith pts.
inversion_clear H0.

case (calc_dec c c'); intros.
case (le_gt_dec n n'); [ left | right ].
elim e; auto with arith pts.

red in |- *; intros.
apply univ_inv with (Stype c n) (Stype c' n'); intros; auto with arith pts.
inversion_clear H0.
absurd (n <= n'); auto with arith pts.

right; red in |- *; intros; apply n0.
apply univ_inv with (Stype c n) (Stype c' n'); intros; auto with arith pts.
inversion_clear H0; auto with arith pts.
Qed.



  (* Inference des axiomes et regles *)

  Lemma ecc_inf_axiom :
   forall s : srt_ecc, {sp : srt_ecc | ppal (axiom_ecc s) univ sp}.
refine
 (fun s : srt_ecc =>
  match s return {sp : srt_ecc | ppal (axiom_ecc s) univ sp} with
  | Sprop c => exist _ (Stype c 0) _
  | Stype c n => exist _ (Stype c (S n)) _
  end).
split; intros; auto with arith pts.
inversion_clear H; auto with arith pts.

split; intros; auto with arith pts.
inversion_clear H; auto with arith pts.
Qed.


  Lemma ecc_inf_rule :
   forall x1 x2 : srt_ecc,
   {x3 : srt_ecc | rules_ecc x1 x2 x3 & 
   forall s1 s2 s3 : srt_ecc,
   rules_ecc s1 s2 s3 -> univ x1 s1 -> univ x2 s2 -> univ x3 s3}.
refine
 (fun x1 x2 : srt_ecc =>
  match
    x1, x2
    return
      {x3 : srt_ecc | rules_ecc x1 x2 x3 & 
      forall s1 s2 s3 : srt_ecc,
      rules_ecc s1 s2 s3 -> univ x1 s1 -> univ x2 s2 -> univ x3 s3}
  with
  | Sprop c, _ => exist2 _ _ x2 _ _
  | Stype c n, Sprop c' => exist2 _ _ (Sprop c') _ _
  | Stype c n, Stype c' n' => exist2 _ _ (Stype c' (max_nat n n')) _ _
  end).
auto with pts.

simple induction 1; intros; auto with arith pts.
apply univ_trans with (Stype c2 m); auto with arith pts.

auto with pts.

intros.
apply univ_inv with (Sprop c') s2; intros.
auto with arith pts.

generalize H.
inversion_clear H2; intros.
inversion_clear H2; auto with arith pts.

unfold max_nat in |- *.
elim (le_gt_dec n n'); auto with arith pts.

intros.
apply univ_inv with (Stype c n) s1; intros; auto with arith pts.
apply univ_inv with (Stype c' n') s2; intros; auto with arith pts.
generalize H.
inversion_clear H2.
inversion_clear H3; intros.
inversion_clear H3.
cut (max_nat n n' <= p); auto with arith pts.
apply least_upper_bound_max_nat.
apply le_trans with m; auto with arith pts.

apply le_trans with m0; auto with arith pts.
Qed.


End SortsOfECC.

(* Uniform interface of sorts *)
Require Export GenericSort.

  Definition sort_of_gen (gs : gen_sort) : Exc srt_ecc :=
    match gs with
    | Gprop => value (Sprop Neg)
    | Gset => value (Sprop Pos)
    | Gtype n => value (Stype Neg n)
    | Gtypeset n => value (Stype Pos n)
    end.

  Definition gen_of_sort (s : srt_ecc) : gen_sort :=
    match s with
    | Sprop Neg => Gprop
    | Sprop Pos => Gset
    | Stype Neg n => Gtype n
    | Stype Pos n => Gtypeset n
    end.
