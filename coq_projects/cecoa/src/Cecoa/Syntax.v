Require Import Bool Arith Max List.
Import List.ListNotations.
Require Import Omega.
Require Import Cecoa.Lib.

Set Implicit Arguments.
Unset Strict Implicit.

Section Syntax.

(* AST *)

Variables variable function constructor : Type.
Variable max_arity : nat.

Inductive value : Type :=
| c_capply : constructor -> list value -> value.

Inductive term : Type :=
| var : variable -> term
| capply : constructor -> list term -> term
| fapply : function -> list term -> term.

Inductive pattern : Type :=
| p_var : variable -> pattern
| p_capply : constructor -> list pattern -> pattern.

Inductive rule : Type :=
| rule_intro : function -> list pattern -> term -> rule.

(* Smarter induction principles than the ones automatically generated *)

Lemma value_ind2_gen :
  forall (P : value -> Type)(Q : list value -> Type),
  Q nil ->
  (forall v l, P v -> Q l -> Q (v :: l)) ->
  (forall c l, Q l -> P (c_capply c l)) ->
  forall v, P v.
Proof.
fix H1 6; intros P Q H2 H3 H4 [c l]; apply H4; revert l; fix H5 1; intros [ | v l].

- apply H2.

- apply H3.

  + apply H1 with (Q:=Q).

    * apply H2.

    * apply H3.

    * apply H4.

  + apply H5.
Qed.

Lemma term_ind2_gen :
  forall (P : term -> Prop)(Q : list term -> Prop),
  Q nil ->
  (forall t l, P t -> Q l -> Q (t :: l)) ->
  (forall x, P (var x)) ->
  (forall c l, Q l -> P (capply c l)) ->
  (forall f l, Q l -> P (fapply f l)) ->
  forall t, P t.
Proof.
fix H1 8; intros P Q H2 H3 H4 H5 H6 [ x | c l | f l ].
- apply H4.

- apply H5; revert l; fix H7 1; intros [ | t l].

  + apply H2.

  + apply H3.

    * { apply H1 with (Q:=Q).

      - apply H2.

      - apply H3.

      - apply H4.

      - apply H5.

      - apply H6. }

    * apply H7.

- apply H6; revert l; fix H7 1; intros [ | t l].

  + apply H2.

  + apply H3.

    * { apply H1 with (Q:=Q).

      - apply H2.

      - apply H3.

      - apply H4.

      - apply H5.

      - apply H6. }

    * apply H7.
Qed.

Lemma term_ind2 :
  forall (P : term -> Prop),
  (forall x, P (var x)) ->
  (forall c l, (forall t, In t l -> P t) -> P (capply c l)) ->
  (forall f l, (forall t, In t l -> P t) -> P (fapply f l)) ->
  forall t, P t.
Proof.
intros P H1 H2 H3 t.
apply term_ind2_gen with (Q := fun l => forall t, In t l -> P t); simpl; try tauto.
clear H1 H2 H3 t; intros t1 l H1 H2 t2 [H3 | H3].

- subst; trivial.

- auto.
Qed.

Lemma pattern_ind2_gen :
  forall (P : pattern -> Prop)(Q : list pattern -> Prop),
  Q nil ->
  (forall p l, P p -> Q l -> Q (p :: l)) ->
  (forall x, P (p_var x)) ->
  (forall c l, Q l -> P (p_capply c l)) ->
  forall p, P p.
Proof.
fix H1 7; intros P Q H2 H3 H4 H5 [ x | c l ].

- apply H4.

- apply H5; revert l; fix H6 1; intros [ | p l].

  + apply H2.

  + apply H3.

    * { apply H1 with (Q:=Q).

      - apply H2.

      - apply H3.

      - apply H4.

      - apply H5. }

    * apply H6.
Qed.

Lemma pattern_ind2 :
  forall (P : pattern -> Prop),
  (forall x, P (p_var x)) ->
  (forall c l, (forall p, In p l -> P p) -> P (p_capply c l)) ->
  forall p, P p.
Proof.
intros P H1 H2 p.
apply pattern_ind2_gen with (Q := fun l => forall p, In p l -> P p); simpl; try tauto.
clear H1 H2 p; intros p1 l H1 H2 p2 [H3 | H3].

- subst; trivial.

- auto.
Qed.

(* Boolean equalities for syntax *)

Variable variable_eq_dec : forall (x1 x2 : variable), {x1=x2}+{x1<>x2}.

Definition variable_beq (x1 x2 : variable) : bool :=
  if variable_eq_dec x1 x2 then true else false.

Lemma variable_beq_eq : forall x1 x2, variable_beq x1 x2 = true <-> x1 = x2.
Proof.
unfold variable_beq.
intros x1 x2.
split; intro H; destruct (variable_eq_dec x1 x2); [ trivial | discriminate | trivial | tauto ].
Qed.

Variable function_eq_dec : forall (x1 x2 : function), {x1=x2}+{x1<>x2}.

Definition function_beq (x1 x2 : function) : bool :=
  if function_eq_dec x1 x2 then true else false.

Lemma function_beq_eq : forall x1 x2, function_beq x1 x2 = true <-> x1 = x2.
Proof.
unfold function_beq.
intros x1 x2.
split; intro H; destruct (function_eq_dec x1 x2); [ trivial | discriminate | trivial | tauto ].
Qed.

Variable constructor_eq_dec : forall (x1 x2 : constructor), {x1=x2}+{x1<>x2}.

Definition constructor_beq (x1 x2 : constructor) : bool :=
  if constructor_eq_dec x1 x2 then true else false.

Lemma constructor_beq_eq : forall x1 x2, constructor_beq x1 x2 = true <-> x1 = x2.
Proof.
unfold constructor_beq.
intros x1 x2.
split; intro H; destruct (constructor_eq_dec x1 x2); [ trivial | discriminate | trivial | tauto ].
Qed.

Fixpoint value_beq (v1 v2 : value) : bool :=
  match v1, v2 with
  | c_capply c lv, c_capply c' lv' => constructor_beq c c' && list_beq _ value_beq lv lv'
  end.

Lemma value_ind2 :
  forall (P : value -> Prop),
  (forall c l, (forall v, In v l -> P v) -> P (c_capply c l)) ->
  forall v, P v.
Proof.
intros P H1 v.
apply value_ind2_gen with (Q := fun l => forall v, In v l -> P v); simpl; try tauto.
clear H1 v; intros v1 l H1 H2 v2 [H3 | H3].

- subst; trivial.

- auto.
Qed.

Lemma value_beq_eq v1 v2 : value_beq v1 v2 = true <-> v1 = v2.
Proof.
revert v2.
induction v1 as [ c1 lv1 IH ] using value_ind2; simpl; intros [ c2 lv2 ].
rewrite andb_true_iff, constructor_beq_eq, list_beq_eq.

- split.

 + intros [ H1 H2 ].
    congruence.

  + intro H.
    injection H.
    tauto.

- firstorder.
Qed.

Fixpoint term_beq (t1 t2 : term) : bool :=
  match t1, t2 with
  | var x, var x' => variable_beq x x'
  | capply c lt, capply c' lt' => constructor_beq c c' && list_beq _ term_beq lt lt'
  | fapply f lt, fapply f' lt' => function_beq f f' && list_beq _ term_beq lt lt'
  | _, _ => false
  end.

Lemma term_beq_eq t1 t2 : term_beq t1 t2 = true <-> t1 = t2.
Proof.
revert t2.
induction t1 as [ x1 | c1 lt1 IH | f1 lt1 IH ] using term_ind2; simpl; intros [ x2 | c2 lt2 | f2 lt2 ];
try (split; congruence).

- rewrite variable_beq_eq.
  split; congruence.

- rewrite andb_true_iff, constructor_beq_eq, list_beq_eq.

  + split.

    * intros [ H1 H2 ].
      congruence.

    * intro H.
      split; congruence.

  + firstorder.

- rewrite andb_true_iff, function_beq_eq, list_beq_eq.

  + split.

    * intros [ H1 H2 ].
      congruence.

    * intro H.
      split; congruence.

  + firstorder.
Qed.

(* Automatic conversion of a [value] or [pattern] into a [term] *)

Fixpoint pattern_from_value (v : value) : pattern  :=
  match v with
    | c_capply c lv => p_capply c (map pattern_from_value lv)
  end.

Fixpoint term_from_value (v : value) : term :=
  match v with
  | c_capply c lc => capply c (map term_from_value lc)
  end.

Coercion term_from_value : value >-> term.

Lemma term_from_value_not_var : forall v x, ~ term_from_value v = var x.
Proof.
intros v x; destruct v; simpl; congruence.
Qed.

Lemma term_from_value_not_fapply : forall v f lt, ~ term_from_value v = fapply f lt.
Proof.
intros v x; destruct v; simpl; congruence.
Qed.

Lemma term_from_value_injective (v v': value) :
  term_from_value v = term_from_value v' -> v = v'.
Proof.
  revert v';
  induction v as [ c lv IH ] using value_ind2;
  intros v' Heq.
  destruct v' as [ c' lv' ].
  simpl in Heq.
  injection Heq;
    intros Heqlv Heqc.
  subst c'.
  f_equal.
  clear c Heq.
  assert (Hlen : length lv = length lv').
  {
    do 2 rewrite <- map_length with (f := term_from_value).
    rewrite Heqlv.
    trivial.
  }
  revert lv' Heqlv Hlen IH;
    induction lv as [ | v lv IH' ];
    intros lv' Heqlv Hlen IH;
    destruct lv' as [ | v' lv'];
    [ trivial
    | inversion Hlen
    | inversion Hlen
    | ].

  f_equal.

  - apply IH; [ now left | ].
    injection Heqlv; intros; assumption.
  - apply IH'.
    + injection Heqlv; intros; assumption.
    + injection Hlen; intros; assumption.
    + intros v'' Hin.
      apply IH.
      now right.
Qed.

Fixpoint term_from_pattern (p : pattern) : term :=
  match p with
  | p_var v => var v
  | p_capply c lp => capply c (map term_from_pattern lp)
  end.

Coercion term_from_pattern : pattern >-> term.

Lemma term_from_pattern_not_fapply : forall v f lt, ~ term_from_pattern v = fapply f lt.
Proof.
intros v x; destruct v; simpl; congruence.
Qed.

(* Doit-on définir explicitement term_value ? *)
Fixpoint term_value (t: term) : Prop :=
  match t with
    | capply _ lt => andl (map term_value lt)
    | _ => False
  end.

Lemma term_value_eqv (t: term) :
  term_value t <-> exists (v: value), t = term_from_value v.
Proof.
induction t as [ | c lt IH | ] using term_ind2.

- split.
  + intros Himp; inversion Himp.
  + intros Himp; destruct Himp as [ v Himp ]; destruct v; discriminate.

- split.
  + intros Hval.
    assert (exists lv, Forall2 (fun t v => t = term_from_value v) lt lv) as [ lv Hfor2 ].
    { apply forall_exists_list with (P := term_value).
      - intros t Hin Hvalt.
        apply IH; assumption.
      - simpl in Hval.
        apply forall_andl; assumption.
    }

    exists (c_capply c lv).
    simpl.
    f_equal.
    clear c Hval IH.
    revert lv Hfor2.
    induction lt as [ | t lt IH ]; intros lv Hfor2.
    * inversion Hfor2; tauto.
    * inversion Hfor2 as [ | Ba v Bc lv' Be Hfor2' Bg Bh ]; subst.
      simpl; f_equal.
      apply IH; assumption.

  + intros [ v Heq ].
    destruct v as [ c' lv ].
    inversion Heq; simpl; clear.
    rewrite map_map.
    induction lv as [ | v lv IH ].
    * simpl; trivial.
    * simpl.
      split; [ idtac | assumption ].
      clear IH lv.
      induction v as [ c lv ] using value_ind2.
      simpl.
      rewrite map_map.
      rewrite <- forall_andl; apply Forall_forall; assumption.

- split.
  + intros Himp; inversion Himp.
  + intros Himp; destruct Himp as [ v Himp ]; destruct v; discriminate.
Qed.

(* Well-formedness of a program *)

Fixpoint vars_of_term (t : term) : list variable :=
  match t with
  | var x => [x]
  | capply _ lt => flat_map vars_of_term lt
  | fapply _ lt => flat_map vars_of_term lt
  end.

Fixpoint vars_of_pattern (p : pattern) : list variable :=
  match p with
  | p_var x => [x]
  | p_capply _ lp => flat_map vars_of_pattern lp
  end.

Lemma vars_of_pattern_term p : vars_of_pattern p = vars_of_term (term_from_pattern p).
Proof.
induction p as [x | c lp IH] using pattern_ind2; simpl; trivial.
apply flat_map_comp; exact IH.
Qed.

Fixpoint functions_of_term (t:term) : list function :=
  match t with
    | var _       => []
    | capply _ lt => flat_map functions_of_term lt
    | fapply f lt => f :: flat_map functions_of_term lt
  end.

Fixpoint fapplies_in_term (t: term) : list term :=
  match t with
  | var _       => []
  | capply _ lt =>      flat_map fapplies_in_term lt
  | fapply _ lt => t :: flat_map fapplies_in_term lt
  end.

Lemma fapplies_in_term_are_fapplies t1 t2 :
  In t1 (fapplies_in_term t2) ->
  exists f lt, t1 = fapply f lt.
Proof.
  revert t1.
  induction t2 as [ x | c lt IH | f lt IH ] using term_ind2; intros t1 Hin;
  simpl in Hin; try tauto.
  - simpl in Hin.
    apply in_flat_map in Hin.
    destruct Hin as (t & Hinlt & Hinfapp).
    destruct (IH t Hinlt t1 Hinfapp) as (f' & lt' & Heq).
    exists f'; exists lt'; assumption.
  - simpl in Hin.
    destruct Hin as [ Heq | Hin ].
    + exists f; exists lt; symmetry; assumption.
    + apply in_flat_map in Hin.
      destruct Hin as (t & Hinlt & Hinfapp).
      destruct (IH t Hinlt t1 Hinfapp) as (f' & lt' & Heq).
      exists f'; exists lt'; assumption.
Qed.

Lemma fapplies_in_value_nil (v: value) :
  fapplies_in_term (@term_from_value v) = [].
Proof.
induction v as [ c lv IH ] using value_ind2.
simpl.
rewrite <- flat_map_comp with (h := fun x => fapplies_in_term (@term_from_value x)); trivial.

induction lv as [ | v' lv' IH' ]; trivial.
simpl.
rewrite IH, IH'; firstorder.
Qed.

Fixpoint max_arity_pattern (p : pattern) : nat :=
  match p with
  | p_var _ => 0
  | p_capply _ lp => max (length lp) (maxl (map max_arity_pattern lp))
  end.

Fixpoint max_arity_term (t : term) : nat :=
  match t with
    | var _ => 0
    | capply _ lt => max (length lt) (maxl (map max_arity_term lt))
    | fapply _ lt => max (length lt) (maxl (map max_arity_term lt))
  end.

Definition max_arity_rule (r : rule) : nat :=
  match r with
  | rule_intro _ lp t => max (max_arity_term t) (max (length lp) (maxl (map max_arity_pattern lp)))
  end.

Definition max_arity_prog (prog : list rule) : nat :=
  maxl (map max_arity_rule prog).

Definition rule_vars_defined (r : rule) : Prop :=
  match r with
  | rule_intro _ lp t => incl (vars_of_term t) (flat_map vars_of_pattern lp)
  end.

Definition wf_prog (prog : list rule) : Prop :=
  andl (map rule_vars_defined prog) /\ max_arity_prog prog <= max_arity.

Fixpoint subst (s : variable -> value)(t : term) : term :=
  match t with
  | var x => s x
  | capply c lt => capply c (map (subst s) lt)
  | fapply f lt => fapply f (map (subst s) lt)
  end.

Fixpoint psubst (s : variable -> value)(p : pattern) : value :=
  match p with
  | p_var x => s x
  | p_capply c lp => c_capply c (map (psubst s) lp)
  end.

Lemma subst_not_var : forall s t x, ~ subst s t = var x.
Proof.
intros s t x; destruct t; simpl; try congruence; apply term_from_value_not_var.
Qed.

Lemma subst_psubst s p : subst s (term_from_pattern p) = term_from_value (psubst s p).
Proof.
induction p as [ x | c lp IH1 ] using pattern_ind2; simpl; trivial.
f_equal; do 2 rewrite map_map; revert IH1; clear; intro IH1; induction lp as [ | p lp IH2]; simpl; trivial.
f_equal.

- apply IH1; simpl; tauto.

- apply IH2.
  intros; apply IH1; simpl; tauto.
Qed.

(* Sizes *)

Fixpoint value_size (v : value) : nat :=
  match v with
  | c_capply _ lv => 1 + suml (map value_size lv)
  end.

Fixpoint term_size (t : term) :=
  match t with
  | var _ => 1
  | capply _ lt => 1 + suml (map term_size lt)
  | fapply _ lt => 1 + suml (map term_size lt)
  end.

Lemma gt_term_size_O t : term_size t > 0.
Proof.
case t; intros ; simpl; apply gt_Sn_O.
Qed.

Lemma in_capply_term_size_lt c (t : term) lt :
  In t lt ->
  term_size t < term_size (capply c lt).
Proof.
simpl.
induction lt as [ | t' lt IH ]; simpl; try tauto.
intros [ H | H ].

- subst t'.
  omega.

- apply IH in H.
  omega.
Qed.

Lemma in_fapply_term_size_lt f (t : term) lt :
  In t lt ->
  term_size t < term_size (fapply f lt).
Proof.
simpl.
induction lt as [ | t' lt IH ]; simpl; try tauto.
intros [ H | H ].

- subst t'.
  omega.

- apply IH in H.
  omega.
Qed.

(* Right-hand side of a rule *)

Definition rhs_of_rule (r : rule) : term :=
  match r with rule_intro _ _ t => t end.

(* Injecte les membres gauches des règles dans les term *)
Definition lhs_of_rule (r : rule) : term :=
  match r with rule_intro f lp _ => fapply f (map term_from_pattern lp) end.

Definition max_rhs (prog : list rule) : nat :=
  maxl (map term_size (map rhs_of_rule prog)).

(* This lemma corresponds to the first four lines of the proof of Proposition 4. *)
(* Une règle bien formée contient uniquement des variables qui sont dans les motifs.

Soit un arbre de preuve bien formé et un programme.
Pour chaque activation, montrons que |rs| ≤ activation_bound p
Pour ça, calculons la taille de rs.
|rs| ≤ |r| (1+ plus grand substitut d’une variable) car |rs| contient au plus |r| variables.
(Lemme pour prouver ça)
par ailleurs « plus grand substitut d’une variable » ≤ |t| pour toutes les variables de r car :
le programme est bien formé, donc les variables de r apparaissent dans les motifs, donc la substitution
les fait correspondre à des sous-termes de t (lemme : un sous-terme a une taille inférieure ?)
*)

Lemma compatible_sizes: forall v, term_size (term_from_value v) = value_size v.
Proof.
induction v as [c lv IH] using value_ind2;
simpl; do 2 f_equal; rewrite map_map; apply map_in_ext; trivial.
Qed.

Definition max_size_image_subst (t : term) (s : variable -> value) : nat :=
  maxl (map value_size (map s (vars_of_term t))).

Lemma incl_le_max_size_image_subst :
  forall s t u,
  incl (vars_of_term t) (vars_of_term u) -> max_size_image_subst t s <= max_size_image_subst u s.
Proof.
intros s t u H_incl.
unfold max_size_image_subst.
apply incl_le_maxl.
do 2 rewrite map_map.
unfold incl.
intro size.
rewrite in_map_iff.
intro H_size_in_var_t.
destruct H_size_in_var_t as [ var [ H_var_size H_var_in_t ] ].
set (var_size := fun x : variable => value_size (s x)).
replace size with (var_size var).
apply in_map.
apply (H_incl var H_var_in_t).
Qed.

Lemma step_one: forall s t, term_size (subst s t) <= term_size t * (1 + max_size_image_subst t s).
Proof.
intros s t; induction t as [ x | c lt IH | f lt IH ] using term_ind2.

- unfold max_size_image_subst; simpl; rewrite plus_0_r; rewrite compatible_sizes; apply le_S; apply le_max_l.

- simpl; eapply le_trans with (S _).

  + apply le_n_S; rewrite map_map; apply suml_map_le; apply IH.

  + clear IH; apply le_n_S; induction lt as [ | t lt IH ]; simpl; trivial; etransitivity.

    * apply plus_le_compat_l; apply IH.

    * { clear IH; unfold max_size_image_subst; simpl; do 2 rewrite map_app; rewrite maxl_app.
      set (w := term_size t);
      set (x:= maxl (map value_size (map s (vars_of_term t))));
      set (y:= maxl (map value_size (map s (flat_map vars_of_term lt))));
      set (z := suml (map term_size lt)).
      replace (max x y + (w + z) * S (max x y)) with (w * S (max x y) + (max x y + z * S (max x y))).

      - apply plus_le_compat.

        + apply mult_le_compat_l; apply le_n_S.
          apply le_max_l.
        + apply plus_le_compat.

          * apply le_max_r.

          * apply mult_le_compat_l; apply le_n_S; apply le_max_r.

      - ring. }

- simpl; eapply le_trans with (S _).

  + apply le_n_S; rewrite map_map; apply suml_map_le; apply IH.

  + clear IH; apply le_n_S; induction lt as [ | t lt IH ]; simpl; trivial; etransitivity.

  * apply plus_le_compat_l; apply IH.

  * { clear IH; unfold max_size_image_subst; simpl; do 2 rewrite map_app; rewrite maxl_app.
    set (w := term_size t);
    set (x:= maxl (map value_size (map s (vars_of_term t))));
    set (y:= maxl (map value_size (map s (flat_map vars_of_term lt))));
    set (z := suml (map term_size lt)).
    replace (max x y + (w + z) * S (max x y)) with (w * S (max x y) + (max x y + z * S (max x y))).

    - apply plus_le_compat.

      + apply mult_le_compat_l; apply le_n_S.
        apply le_max_l.

      + apply plus_le_compat.

        * apply le_max_r.

        * apply mult_le_compat_l; apply le_n_S; apply le_max_r.

    - ring. }
Qed.

(* |r| ≤ |t|

   t match le motif, donc pour toute variable v du motif, |v sigma| ≤ |t|
   soit R la taille maximale d’une image de variable par la substitution
   donc |v sigma| ≤ R ≤ |t|
   
   toute variable de r est une variable du motif donc de taille ≤ |t|
   |rsig| ≤ |r|(R+1) d’après (1)
   |r| ≤ max_rhs par définition
   |rsig| ≤ max_rhs(R+1)
   
   |rsig| ≤ activ(|t|) pour activ = x → max_rhs(x+1)
*)

(* |xσ| ≤ |pσ| pour x ∈ p *)
Lemma size_subst_var_le_size_value:
  forall p s (x:variable) v, v = psubst s p -> In x (vars_of_pattern p) -> value_size (s x) <= value_size v.
Proof.
intros p s x.
induction p as [ x' | c lp IH ] using pattern_ind2 ; intros v H_match H_x_in_pattern.

- (* Cas de base p = x *)
  simpl in *.
  destruct H_x_in_pattern.

  + subst.
    trivial.

  + case H.

- (* Cas récursif *)
  simpl in * |-.
  subst v.
  simpl.
  (* On prouve d’abord que x dans le motif de départ implique qu’il est dans un des p de lp *)
  rewrite in_flat_map in H_x_in_pattern.
  destruct H_x_in_pattern as [ p [ H_p_in_lp H_x_in_p ] ].
  etransitivity.

  + apply IH with p; trivial.

  + rewrite map_map.
    etransitivity.

    * apply in_le_suml.
      instantiate (1 := map (fun x0 : pattern => value_size (psubst s x0)) lp).
      rewrite in_map_iff; exists p.
      split; trivial.

    * apply le_n_Sn.
Qed.

Lemma max_size_image_subst_bounded :
  forall t s, max_size_image_subst t s <= term_size (subst s t).
Proof.
intros t s; unfold max_size_image_subst; rewrite map_map;
induction t as [ x | c lt IH | f lt IH ] using term_ind2; simpl;
try (rewrite max_0_r; rewrite compatible_sizes; trivial);
(transitivity (suml (map term_size (map (subst s) lt))); [idtac | apply le_n_Sn]);
rewrite map_map; apply maxl_le_suml_map; exact IH.
Qed.

(* This definition corresponds to the r in the proof of Proposition 4. *)
Definition activation_bound (prog : list rule) : nat -> nat :=
  fun x => max_rhs prog * (1 + x).

Lemma activation_bound_monotone (prog : list rule) :
  forall x y, x <= y -> activation_bound prog x <= activation_bound prog y.
Proof.
intros x y H_le.
unfold activation_bound.
apply mult_le_compat_l.
apply le_n_S.
assumption.
Qed.

Definition nb_rhs_functions (r: rule) :=
  match r with
    | rule_intro _ _ t => length (functions_of_term t)
  end.

Definition max_nb_rhs_functions (prog : list rule) : nat :=
  maxl (map nb_rhs_functions prog).

Lemma no_func_in_pattern p:
  functions_of_term (term_from_pattern p) = [].
Proof.
induction p using pattern_ind2; simpl; auto.
apply flat_map_nil. intros.
induction l; simpl in *; try (now exfalso).
destruct H0.
- subst. apply H. auto.
- apply IHl; auto.
Qed.

Lemma no_funcs_in_patterns l:
  flat_map functions_of_term (map term_from_pattern l) = [].
Proof.
induction l; simpl; auto.
rewrite IHl. rewrite no_func_in_pattern. simpl. auto.
Qed.

End Syntax.

Arguments var [variable function constructor].

Arguments p_var [variable constructor].
