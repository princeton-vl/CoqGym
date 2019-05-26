
Require Import Bool.
Require Import Arith.
Require Import Compare_dec.
Require Import Peano_dec.
Require Import General.
Require Import MyList.
Require Import MyRelations.

Require Export Main.

Section SortsOfECC.

  Inductive srt_ecc : Set :=
    | Sprop : srt_ecc
    | Stype : nat -> srt_ecc.

  Inductive axiom_ecc : srt_ecc -> srt_ecc -> Prop :=
    | ax_prop : forall (n : nat), axiom_ecc Sprop (Stype n)
    | ax_type : forall (n m : nat), n < m -> axiom_ecc (Stype n) (Stype m).

  Inductive rules_ecc : srt_ecc -> srt_ecc -> srt_ecc -> Prop :=
    | rule_prop_l : forall (s : srt_ecc), rules_ecc Sprop s s
    | rule_prop_r : forall (s : srt_ecc), rules_ecc s Sprop Sprop
    | rule_type :
        forall (n m p : nat),
        n <= p -> m <= p -> rules_ecc (Stype n) (Stype m) (Stype p).

  Inductive univ_ecc : srt_ecc -> srt_ecc -> Prop :=
      univ_type :
        forall (n m : nat),
        n <= m -> univ_ecc (Stype n) (Stype m).

  Definition univ : relation srt_ecc := clos_refl_trans _ univ_ecc.

  Hint Resolve ax_prop ax_type rule_prop_l rule_prop_r rule_type univ_type:
    pts.
  Hint Unfold univ: pts.


  (* Inversion et Decidabilite de l'inclusion entre sortes *)

  Let univ_trans : forall x y z : srt_ecc, univ x y -> univ y z -> univ x z.
Proof rt_trans srt_ecc univ_ecc.


  Inductive inv_univ : srt_ecc -> srt_ecc -> Prop :=
    | iu_prop : inv_univ Sprop Sprop
    | iu_type :
        forall (n m : nat),
        n <= m -> inv_univ (Stype n) (Stype m).

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

  Lemma ecc_sort_dec : forall s s' : srt_ecc, decide (s = s').
simple destruct s; simple destruct s'; intros; try (right; discriminate).
left; auto with arith pts.

elim eq_nat_dec with n n0; intros.
left; elim a; auto with arith pts.

right; red in |- *; intros H; apply b; injection H; auto with arith pts.
Qed.


  Lemma univ_ecc_dec : forall s s' : srt_ecc, decide (univ s s').
refine
 (fun s s' : srt_ecc =>
  match s, s' return (decide (univ s s')) with
  | Sprop, Sprop => _
  | Stype n, Stype n' => _
  | _, _ => right _ _
  end).
left; auto with arith pts.

red in |- *; intros.
apply univ_inv with Sprop (Stype n); intros; auto with arith pts.
inversion_clear H0.

red in |- *; intros.
apply univ_inv with (Stype n) Sprop; intros; auto with arith pts.
inversion_clear H0.

case (le_gt_dec n n'); [ left | right ].
auto with pts.

red in |- *; intros.
apply univ_inv with (Stype n) (Stype n'); intros; auto with arith pts.
inversion_clear H0.
absurd (n <= n'); auto with arith pts.
Qed.



  (* Inference des axiomes et regles *)

  Lemma ecc_inf_axiom :
   forall s : srt_ecc, {sp : srt_ecc | ppal (axiom_ecc s) univ sp}.
refine
 (fun s : srt_ecc =>
  match s return {sp : srt_ecc | ppal (axiom_ecc s) univ sp} with
  | Sprop => exist _ (Stype 0) _
  | Stype n => exist _ (Stype (S n)) _
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
  | Sprop, _ => exist2 _ _ x2 _ _
  | Stype n, Sprop => exist2 _ _ Sprop _ _
  | Stype n, Stype n' => exist2 _ _ (Stype (max_nat n n')) _ _
  end).
auto with pts.

simple induction 1; intros; auto with arith pts.
apply univ_trans with (Stype m); auto with arith pts.

auto with pts.

intros.
apply univ_inv with Sprop s2; intros.
auto with arith pts.

generalize H.
inversion_clear H2; intros.
inversion_clear H2; auto with arith pts.

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


End SortsOfECC.


Definition term := term srt_ecc.
Definition env := env srt_ecc.


  (* Construction du CTS *)

Definition ecc : CTS_spec srt_ecc :=
  Build_CTS_spec _ axiom_ecc rules_ecc univ_ecc (beta_delta_rule _).


  (* Construction du PTS issu du CTS *)

Definition ecc_pts : PTS_sub_spec srt_ecc := cts_pts_functor _ ecc.
Definition le_type : red_rule srt_ecc :=
  Rule _ (Le_type _ (pts_le_type _ ecc_pts)).

Definition typ : env -> term -> term -> Prop := typ _ ecc_pts.
Definition typ_ppal : env -> term -> term -> Prop := typ_ppal _ ecc_pts.
Definition wft : env -> term -> Prop := wf_type _ ecc_pts.
Definition wf : env -> Prop := wf _ ecc_pts.
Definition sn := sn srt_ecc (ctxt _ (Rule _ (head_reduct _ ecc))).
Definition red := red _ (Rule _ (beta_delta_rule srt_ecc)).
Definition conv := conv _ (Rule _ (beta_delta_rule srt_ecc)).

  Hint Unfold le_type typ wft wf sn: pts.


  (* Algorithme de mise en forme normale de tete
     Decidabilite du sous-typage pour les types bien formes *)

  Lemma whnf :
   forall (e : env) (t : term),
   sn e t ->
   {u : term | red _ (beta_delta _) e t u & 
   head_normal _ (beta_delta _) e u}.
Proof beta_delta_whnf srt_ecc.


  Lemma bd_conv_hnf :
   forall (e : env) (x y : term),
   sn e x ->
   sn e y -> decide (conv_hn_inv _ (beta_delta_rule _) e x y).
Proof
  CR_WHNF_convert_hn srt_ecc ecc_sort_dec (beta_delta_rule srt_ecc)
    (church_rosser_beta_delta srt_ecc) whnf.


  Theorem ecc_is_subtype_dec : subtype_dec_CTS _ ecc.
apply Build_subtype_dec_CTS.
exact (church_rosser_beta_delta srt_ecc).

exact (bd_hn_sort srt_ecc).

exact (bd_hn_prod srt_ecc).

exact whnf.

exact bd_conv_hnf.

exact univ_ecc_dec.
Qed.



  (* Subject-Reduction *)

  Lemma sound_ecc_bd : rule_sound _ ecc_pts (beta_delta _).
unfold beta_delta in |- *.
simpl in |- *.
unfold union in |- *.
apply union_sound.
apply beta_sound; auto with arith pts.
simpl in |- *.
apply cumul_inv_prod.
exact ecc_is_subtype_dec.

apply delta_sound.
Qed.



Definition least_nat (P:nat->Prop) (n:nat) : Prop :=
  P n /\ forall m, P m -> n <= m.

Definition greatest_nat (P:nat->Prop) (n:nat) : Prop :=
  P n /\ forall m, P m -> m <= n.



Definition sort_of_level n :=
  match n with
    0 => Sprop
  | S k => Stype k
  end.

Definition level_of_sort s :=
  match s with
    Sprop => 0
  | Stype k => S k
  end.

Definition level e t :=
  least_nat 
    (fun n => exists2 u, conv e t u & typ e u (Srt _ (sort_of_level n))).


Section ECCn.

  Variable N : nat.

  Section Degree.

  Variable j : nat.

  (* quasi nf for all levels i > j *)
  Variable quasi_nf_up : env -> term -> Prop.

  (* degree of types of level i *)

  Fixpoint base_term (t:term) : Prop :=
    match t with
      Ref _ => True
    | App u v => base_term u
    | _ => False
    end.

  (* TODO: enforce reduct is a quasi-nf ? *)
  Inductive degree : env -> term -> nat -> Prop :=
    deg_other : forall e t j, ~ level e t j -> degree e t 0
  | deg_base : forall e t u, red e t u -> base_term u -> degree e t 1
  | deg_sort : forall e t, red e t (Srt _ (sort_of_level j)) -> degree e t 1
  | deg_prod : forall e t A B n m,
      red e t (Prod _ A B) ->
      degree e A n ->
      degree (Ax _ A::e) B m ->
      degree e t (S (max_nat n m)).

  Definition major_term (t:term) :=
    match t with
      App M N => M
    | _ => t
    end.

  Definition measure_delta e t n :=
    exists2 t', beta _ e t t' &
    exists2 u, typ_ppal e (major_term t) u & degree e u n.

  Definition measure_gamma e t :=
    greatest_nat (fun n => exists2 v, clos_refl_trans _ (subterm _) v (e,t) &
                           measure_delta (fst v) (snd v) n).
 
  Definition quasi_normal e t := measure_gamma e t 0.

  End Degree.

End ECCn..


  (* L'axiome:  ECC est fortement normalisant *)

  Axiom
    ecc_normalise :
      forall (e : env) (t T : term), typ_ecc e t T -> ecc_sn e t.
