Require Import Recdef Relations Wellfounded.
Require Import Arith NPeano PeanoNat List Bool Psatz.
Require Import Cecoa.Lib Cecoa.Syntax Cecoa.CBV_cache Cecoa.Bounds Cecoa.Ordering.
Require Import Omega.

Import List.ListNotations.

Section Evaluates.

Variables variable function constructor : Type.

Notation value := (Syntax.value constructor).
Notation term := (Syntax.term variable function constructor).
Notation pattern := (Syntax.pattern variable constructor).
Notation rule := (Syntax.rule variable function constructor).
Notation cbv := (CBV_cache.cbv variable function constructor).
Notation cache := (CBV_cache.cache variable function constructor).

Variable variable_eq_dec : forall (x1 x2 : variable), {x1=x2}+{x1<>x2}.

Variable function_eq_dec : forall (x1 x2 : function), {x1=x2}+{x1<>x2}.

Variable constructor_eq_dec : forall (x1 x2 : constructor), {x1=x2}+{x1<>x2}.

Variable term_default : term.

Variable value_default : value.

Variable function_default : function.

Variable rule_default : rule.

Variable prog : list rule.

Variable max_arity : nat.

Notation wf :=
  (CBV_cache.wf variable_eq_dec function_eq_dec constructor_eq_dec rule_default prog max_arity).

Notation assoc_cache := (assoc (term_beq variable_eq_dec function_eq_dec constructor_eq_dec)).

(* Function ranks and compatibility *)

Variable rank: function -> nat.

Hypothesis prog_is_ppo : PPO_prog prog rank.

Hypothesis prog_is_wf : wf_prog max_arity prog.

Definition term_order (t1 t2: term): Prop :=
  In t1 (sub_terms_strict _ _ _ t2).

Set Implicit Arguments.

Lemma term_order_wf : well_founded term_order.
Proof.
intro t.
induction t as [ x | c lt IH | f lt IH ] using term_ind2;
 constructor; unfold term_order; simpl; [ tauto | | ].

- intros t Hin.
  rewrite in_flat_map in Hin.
  destruct Hin as (t' & Hin1 & Hin2).
  apply sub_term_eq_or_strict in Hin2.
  destruct Hin2 as [ Heq | Hin2 ].

  + subst t'.
     apply IH.
     exact Hin1.

  + apply Acc_inv_trans with t'.

    * constructor.
      exact Hin2.

    * apply IH.
      exact Hin1.

- intros t Hin.
  rewrite in_flat_map in Hin.
  destruct Hin as (t' & Hin1 & Hin2).
  apply sub_term_eq_or_strict in Hin2.
  destruct Hin2 as [ Heq | Hin2 ].

  + subst t'.
     apply IH.
     exact Hin1.

  + apply Acc_inv_trans with t'.

    * constructor.
      exact Hin2.

    * apply IH.
      exact Hin1.
Qed.

Definition active_term := prod function (list value).

Definition term_from_active_term (t: active_term) : term :=
  let (f, lv) := t in
  fapply f (map (@term_from_value _ _ _) lv).

Definition value_list_order (lv lv' : list value) : Prop :=
  suml (map (@value_size _) lv) < suml (map (@value_size _) lv').

Lemma value_list_order_wf : well_founded value_list_order.
Proof.
unfold value_list_order.
apply wf_inverse_image.
refine lt_wf.
Defined.

Definition active_term_order_superset t t' :=
  lexprod lt value_list_order (rank (fst t), snd t) (rank (fst t'), snd t').

Definition active_term_order_superset_wf : well_founded active_term_order_superset.
Proof.
unfold active_term_order_superset.
apply wf_inverse_image.
apply wf_lexprod.
- apply lt_wf.
- apply value_list_order_wf.
Defined.

Fixpoint unify (s : list (variable * value)) (v : value) (p : pattern) {struct p} :
  option (list (variable * value)) :=
  let unify_list := fix unify_list
    (s : list (variable * value)) (lv : list value) (lp : list pattern) {struct lp} :
    option (list (variable * value)) :=
    match lv, lp with
    | [], [] => Some s
    | v::lv', p::lp' => match unify s v p with
      | None => None
      | Some s' => unify_list s' lv' lp'
      end
    | _, _ => None
    end in
  match p with
  |  p_var x =>
    match assoc (variable_beq variable_eq_dec) x s with
    | None => Some ((x, v) :: s)
    | Some v' => if value_beq constructor_eq_dec v v' then Some s else None
    end
  | p_capply c' lp =>match v with
      | c_capply c lv => if constructor_beq constructor_eq_dec c c' then unify_list s lv lp else None
      end
  end.

Fixpoint unify_list_aux (s : list (variable * value)) (lv : list value) (lp : list pattern) :
  option (list (variable * value)) :=
  match lv, lp with
  | [], [] => Some s
  | v::lv', p::lp' => match unify s v p with
    | None => None
    | Some s' => unify_list_aux s' lv' lp'
    end
  | _, _ => None
  end.

Lemma unify_equation (s : list (variable * value)) (v : value) (p : pattern) :
  unify s v p =
  match p with
  |  p_var x =>
    match assoc (variable_beq variable_eq_dec) x s with
      | None => Some ((x, v) :: s)
      | Some v' => if value_beq constructor_eq_dec v v' then Some s else None
    end
  | p_capply c' lp =>
    match v with
      | c_capply c lv => if constructor_beq constructor_eq_dec c c' then unify_list_aux s lv lp else None
    end
  end.
Proof.
  revert s v.
  induction p as [ x | c lp IH ] using pattern_ind2;
    [ simpl; trivial | ].
  intros s [ c' lv ].
  simpl.
  case constructor_beq; [ | trivial ].
  clear c c'; revert s lv.
  induction lp as [ | p lp IHlp ];
    intros s lv;
    [ destruct lv; trivial | ].
  destruct lv as [ | [ c lv' ] lv ]; simpl; trivial.
  case unify; trivial.
  intros s'.
  apply IHlp.
  intros; apply IH; right; assumption.
Qed.

Definition unify_list
  (s : list (variable * value)) (lv : list value) (lp : list pattern) :
  option (variable -> value) :=
  option_map (assoc_default (variable_beq variable_eq_dec) value_default) (unify_list_aux s lv lp).

Lemma unify_list_unify_unify_list :
  forall s s' v lv p lp,
    unify_list_aux s (v :: lv) (p :: lp) = Some s' ->
    exists s'', unify s v p = Some s'' /\ unify_list_aux s'' lv lp = Some s'.
Proof.
  intros s s' v lv p lp.
  case_eq (unify s v p); simpl;
  [ intro s'' | ]; intro Huni; rewrite Huni; [ | discriminate ].
  intros Hunis; exists s''.
  now split.
Qed.

Lemma unify_list_length :
  forall s s' lv lp, unify_list_aux s lv lp = Some s' -> length lv = length lp.
Proof.
  intros s s' lv; revert s s';
  induction lv as [ | v lv IH ]; intros s s' lp Hunis;
  destruct lp; [ trivial | discriminate | discriminate | ].
  simpl; f_equal;
  apply unify_list_unify_unify_list in Hunis;
  destruct Hunis as (s'' & _ & Hunis); now apply IH in Hunis.
Qed.

Lemma unify_cons_eq_unify_list :
  forall s s' c lv c' lp',
    unify s (c_capply c lv) (p_capply c' lp') = Some s' ->
    c = c' /\ unify_list_aux s lv lp' = Some s'.
Proof.
  intros s s' c lv c' lp' Huni;
  rewrite unify_equation in Huni;
  case_eq (constructor_beq constructor_eq_dec c c'); intros Hc; rewrite Hc in Huni;
  [ now rewrite constructor_beq_eq in Hc | discriminate Huni ].
Qed.

Lemma unify_list_aux_extension lv lp s s':
  unify_list_aux s lv lp = Some s' ->
  exists s'',
    s' = s'' ++ s /\
    forall x, assoc (variable_beq variable_eq_dec) x s <> None -> assoc (variable_beq variable_eq_dec) x s'' = None.
Proof.
  remember (suml (map (value_size (constructor := constructor)) lv)) as size eqn: Hsize.
  revert lv lp s s' Hsize;
    induction size as [ size IH ] using lt_wf_ind; intros lv lp s s' Hsize Hunis.

  destruct lv as [ | v lv ].

  - exists [].
    assert (Hnil : 0 = length lp) by (now apply unify_list_length in Hunis).
    destruct lp; [ clear Hnil | now contradict Hnil ].
    simpl in Hunis; injection Hunis; clear Hunis; intros; now subst s'.

  - assert (Hlen : length (v :: lv) = length lp) by (apply unify_list_length in Hunis; assumption).
    destruct lp as [ | p lp ]; [ discriminate Hlen | clear Hlen ].
    apply unify_list_unify_unify_list in Hunis; destruct Hunis as (s'' & Huni & Hunis).
    set (size' := suml (map (value_size (constructor := constructor)) lv)).
    assert (Hlt: size' < size)
      by (simpl in Hsize; rewrite Hsize;
          change size' with (0 + size'); unfold size';
          apply plus_lt_compat_r;
          destruct v as [ c' lv' ];
          simpl;
          apply lt_O_Sn).
    apply (IH _ Hlt) in Hunis; [ | easy ];
    destruct Hunis as (s''' & Happ & Hconsistent); clear size' Hlt lp.

    destruct p as [ x | c lp' ].

    + simpl in Huni; case_eq (assoc (variable_beq variable_eq_dec) x s).

      * intros v'' Hsome; rewrite Hsome in Huni.
        destruct value_beq in Huni; [ | discriminate Huni ];
        injection Huni; intros; subst s' s''; clear Huni.
        now exists s'''.

      * intros Hnone; rewrite Hnone in Huni.
        injection Huni; intro; subst s''; clear Huni.
        exists (s''' ++ [(x,v)]); split; [ now rewrite <- app_assoc | ].
        intros y Hsome.
        { rewrite assoc_app_eq_None; split.
          - apply Hconsistent.
            change ((x,v) :: s) with ([(x,v)] ++ s).
            rewrite assoc_app_neq_None; now right.
          - simpl.
            case_eq (variable_beq variable_eq_dec y x); [ | easy ].
            rewrite variable_beq_eq; intro; now subst y.
        }

    + destruct v as [ c' lv' ].
      apply unify_cons_eq_unify_list in Huni; destruct Huni as (Hc' & Hunis); subst c'.
      set (size' := suml (map (value_size (constructor := constructor)) lv')).
      assert (Hlt: size' < size) by (subst size; simpl; unfold size'; omega).
      apply (IH _ Hlt) in Hunis; [ | easy ];
      destruct Hunis as (s'''' & Happ' & Hconsistent'); clear size' Hlt.

      exists (s''' ++ s'''').
      subst s' s''.
      split; [ now rewrite <- app_assoc | ].
      intros x Hsome.
      rewrite assoc_app_eq_None; split.
      * apply Hconsistent.
        rewrite assoc_app_neq_None; right; assumption.
      * apply Hconsistent'; assumption.
Qed.

Lemma unify_all_vars_defined :
  forall (s s': list (variable * value)) (v: value) (p: pattern),
    unify s v p = Some s' ->
    forall x, In x (vars_of_pattern p) -> assoc (variable_beq variable_eq_dec) x s' <> None.
Proof.
  intros s s' v p; revert s s' v.
  induction p as [ x | c lp IH ] using pattern_ind2;
    intros s s' v Huni.

  - (* cas variable : unify va forcer s' à contenir x *)
    intros x' [ Hx' | H ]; [ | tauto ]; subst x'.
    rewrite unify_equation in Huni.
    case_eq (assoc (variable_beq variable_eq_dec) x s).
    + intros v' Heq; rewrite Heq in Huni.
      destruct (value_beq _ _ _) in Huni; [ | discriminate ].
      injection Huni; intros H; subst s'.
      rewrite Heq; discriminate.
    + intros Heq; rewrite Heq in Huni; injection Huni; intros H; subst s'.
      simpl.
      case_eq ((variable_beq variable_eq_dec) x x); [ intros; discriminate | ].
      rewrite <- not_true_iff_false, variable_beq_eq; tauto.

  - simpl; destruct v as [ c' lv ].
    apply unify_cons_eq_unify_list in Huni; destruct Huni as (H & Hunis); subst c'; clear c.
    revert s s' lv Hunis.
    induction lp as [ | p lp IHlp ]; [ easy | ].
    intros s s' [ | v lv ] Hunis;
    [ apply unify_list_length in Hunis; now contradict Hunis | ].
    apply unify_list_unify_unify_list in Hunis.
    destruct Hunis as (s'' & Huni & Hunis).
    intros x; rewrite in_flat_map; intros (p' & [Hp' | Hp'] & Hx).
    + subst p'.
      apply IH with (x := x) in Huni; [ | now left | easy ].
      apply unify_list_aux_extension in Hunis.
      destruct Hunis as (s''' & Heq & _); subst s'.
      rewrite assoc_app_neq_None; now right.
    + apply IHlp with (s := s'') (lv := lv).
      * intros p'' Hin; apply IH; now right.
      * easy.
      * apply in_flat_map.
        now exists p'.
Qed.

Lemma eq_psubst_consistent_assoc_extension :
  forall s s' p,
    (forall x, assoc (variable_beq variable_eq_dec) x s <> None -> assoc (variable_beq variable_eq_dec) x s' = None) ->
    (forall x, In x (vars_of_pattern p) -> assoc (variable_beq variable_eq_dec) x s <> None) ->
    psubst (assoc_default (variable_beq variable_eq_dec) value_default (s' ++ s)) p =
    psubst (assoc_default (variable_beq variable_eq_dec) value_default s) p.
Proof.
  intros s s' p; revert s s'.
  induction p as [ x | c lp IH ] using pattern_ind2;
    intros s s' Hconsistent Hvars.

  - assert (Hsomes : assoc (variable_beq variable_eq_dec) x s <> None)
      by (apply Hvars; simpl; now left).
    assert (Hnones' : assoc (variable_beq variable_eq_dec) x s' = None)
      by (apply Hconsistent, Hsomes).
    assert (H : exists v, assoc (variable_beq variable_eq_dec) x s = Some v)
      by now apply neq_None_eq_Some.
    clear Hsomes.
    destruct H as (v & Hsome's).
    simpl; unfold assoc_default.
    rewrite Hsome's.
    case_eq (assoc (variable_beq variable_eq_dec) x (s' ++ s)).
    + intros v'; rewrite assoc_app_eq_Some.
      intros [ Hsomes' | (_ & Hsome) ];
        [ rewrite Hnones' in Hsomes'; discriminate Hsomes'
        | rewrite Hsome's in Hsome; now injection Hsome ].
    + rewrite assoc_app_eq_None; intros (_ & Himpossible); congruence.

  - simpl; f_equal.
    apply map_ext_in.
    intros p Hin; apply IH; [ assumption | assumption | ].
    simpl in Hvars.
    intros x Hx; apply Hvars.
    apply in_flat_map; now exists p.
Qed.

Lemma unify_sound :
  forall (s s': list (variable * value)) (v: value) (p: pattern),
    unify s v p = Some s' ->
    psubst (assoc_default (variable_beq variable_eq_dec) value_default s') p = v.
Proof.
  intros s s' [ c lv ] p; revert s s' c lv.
  induction p as [ x | c lp IH ] using pattern_ind2.
  - intros s s' c' lv; simpl.
    case_eq (assoc (variable_beq variable_eq_dec) x s).
    + intros [ c'' lv'' ] H'' Hassoc.
      case_eq (constructor_beq constructor_eq_dec c' c'');
        case_eq (list_beq value (value_beq constructor_eq_dec) lv lv'');
        intros Heqc Heqlv;
        rewrite Heqc, Heqlv in Hassoc;
        simpl in Hassoc;
        try discriminate.
      injection Hassoc; intros; subst.
      apply list_beq_eq in Heqc; subst;
      [ | intros; apply value_beq_eq; assumption ].
      apply constructor_beq_eq in Heqlv; subst.
      unfold assoc_default.
      rewrite H''; trivial.
    + intros Hnone Hsome; injection Hsome; intros; subst; clear Hsome.
      unfold assoc_default.
      simpl.
      case_eq ((variable_beq variable_eq_dec) x x); [ intros; trivial | ].
      intros Heq.
      rewrite <- not_true_iff_false, variable_beq_eq in Heq.
      now contradict Heq.
  - intros s s' c' lv.
    rewrite unify_equation.
    case_eq (constructor_beq constructor_eq_dec c' c); [ | intros _ H; discriminate H ].
    rewrite constructor_beq_eq.
    intros Heq; subst.
    revert s s' lv;
    induction lp as [ | p lp IHlp ]; intros s s' lv.
    + destruct lv; [ now simpl | ].
      simpl; intros H; discriminate H.
    + destruct lv as [ | [ c' lv' ] lv ]; [ intros H; discriminate H | ].
      simpl.
      case_eq (unify s (c_capply c' lv') p); [ | intros _ H; discriminate H ].
      intros s'' Hs'' Heq.
      f_equal; simpl; f_equal.
      assert (Hvars' := unify_all_vars_defined _ _ _ Hs'').
      apply IH in Hs''.
      * apply unify_list_aux_extension in Heq;
        destruct Heq as (s''' & Heq & Hconsistent);
        subst s'.
        now rewrite eq_psubst_consistent_assoc_extension.
      * left; trivial.
      * simpl in IHlp.
        assert (Hf_equal : forall lv', c_capply c lv' = c_capply c lv -> lv' = lv)
               by (intros lv'' H''; injection H''; trivial).
        apply Hf_equal.
        apply IHlp with (s := s''); [ | assumption ].
        intros p' Hin.
        apply IH.
        right; assumption.
Qed.

Lemma psubst_app p v (s s' : list (variable * value)) :
  (forall x : variable, assoc (variable_beq variable_eq_dec) x s <> None -> assoc (variable_beq variable_eq_dec) x s' = None) ->
  (forall x, In x (vars_of_pattern p) -> assoc (variable_beq variable_eq_dec) x s <> None) ->
  psubst (assoc_default (variable_beq variable_eq_dec) value_default s        ) p = v ->
  psubst (assoc_default (variable_beq variable_eq_dec) value_default (s' ++ s)) p = v.
Proof.
revert v s s'.
induction p as [ x | c lp IHp ] using pattern_ind2; simpl; intros v s s' Hconsistent Hall Hassoc.

- unfold assoc_default in *.
  case_eq (assoc (variable_beq variable_eq_dec) x (s' ++ s)).

  + intros v' Hx.
    apply assoc_app_eq_Some in Hx.
    destruct Hx as [ Hx | [ Hnone Hx ] ]; [ | rewrite Hx in Hassoc; assumption ].
    case_eq (assoc (variable_beq variable_eq_dec) x s).

    * intros v'' Hx'.
      rewrite Hx' in Hassoc.
      subst v''.
      apply eq_None_neq_Some in Hx; [contradict Hx |].
      apply Hconsistent.
      auto.

    * intro Hx'.
      rewrite Hx' in Hassoc.
      apply eq_None_neq_Some in Hx; [contradict Hx |].
      apply Hconsistent.
      auto.

  + intro Hassoc'.
    apply assoc_app_eq_None in Hassoc'.
    destruct Hassoc' as [_ Hassoc'].
    rewrite Hassoc' in Hassoc.
    assumption.

- rewrite <- Hassoc.
  f_equal.
  apply map_in_ext.
  intros p Hp.
  apply eq_psubst_consistent_assoc_extension; [ assumption | ].
  intros x Hx.
  apply Hall.
  apply in_flat_map.
  eauto.
Qed.

Lemma unify_list_sound :
  forall (lp : list pattern) (lv : list value) (s : variable -> value),
    unify_list [] lv lp = Some s -> map (psubst s) lp = lv.
Proof.
assert (
  Hgen: forall lv lp s0 s, unify_list s0 lv lp = Some s ->
  map (psubst s) lp = lv
).
{
unfold unify_list.
induction lv as [ | v lv IHlv ]; intros [ | p lp ] s0 s Hula;
 [ trivial | simpl in Hula; discriminate Hula | simpl in Hula; discriminate Hula | ].
unfold option_map in Hula.
case_eq (unify_list_aux s0 (v :: lv) (p :: lp));
 [ | intro Hnone; rewrite Hnone in Hula; discriminate Hula ].
intros s' Hs'.
rewrite Hs' in Hula.
injection Hula; clear Hula; intro; subst s.
apply unify_list_unify_unify_list in Hs'.
destruct Hs' as (s'' & Hs'' & Hs').
simpl.
f_equal.

- assert(HHs'' := Hs'').
  apply unify_sound in Hs''.
  assert(HHs' := Hs').
  apply unify_list_aux_extension in Hs'.
  destruct Hs' as (s''' & Hs' & Hconsistent).
  subst s'.
  apply psubst_app; [ assumption | | assumption ].
  intros x Hx.
  eapply unify_all_vars_defined; [ exact HHs'' | exact Hx].

- eapply IHlv with (s0 := s'').
  rewrite Hs'.
  reflexivity.
}
eauto.
Qed.

Fixpoint first_rule_rec (prog': list rule) (t: active_term) :
  option (nat * (variable -> value) * term) :=
  match prog' with
    | [] => None
  | rule_intro f lp t' :: prog'' =>
    if function_beq function_eq_dec (fst t) f
    then
      match unify_list [] (snd t) lp with
        | None =>
          match first_rule_rec prog'' t with
            | None => None
            | Some (i, s, t) => Some (S i, s, t)
            end
        | Some s => Some (0, s, subst s t')
      end
    else
      match first_rule_rec prog'' t with
        | None => None
        | Some (i, s, t) => Some (S i, s, t)
      end
  end.

Definition first_rule (t: active_term) :
  option (nat * (variable -> value) * term) :=
  first_rule_rec prog t.

Global Arguments first_rule t : simpl never.

Lemma first_rule_sound :
  forall (f: function) (lv: list value) (i: nat) (s: variable -> value) (t: term),
  first_rule (f, lv) = Some (i, s, t) ->
  { lpt : (list pattern * term)| let (lp, t') := lpt in
    i < length prog /\
    nth i prog rule_default = rule_intro f lp t' /\
    unify_list [] lv lp = Some s /\
    t = subst s t'}.
Proof.
  clear prog_is_ppo prog_is_wf.
  unfold first_rule.
  induction prog as [ | r0 prog' IHp ];
    simpl; intros f lv i s t; [ intros H; discriminate H | ].
  destruct r0 as [ f0 lp0 t0 ].
  case_eq (function_beq function_eq_dec f f0).
  - intro Heqf; rewrite function_beq_eq in Heqf.
    case_eq (unify_list [] lv lp0).
    + intros s' Hs'.
      intros H; injection H; clear H.
      intros Heqt Heqs Hi.
      subst s' t f0 i.
      exists (lp0, t0).
      repeat split; [ apply lt_O_Sn | assumption ].
    + (* ici on dispose d’une hypothèse unify_list = None *)
      intros Hnone Hrec.
      case_eq (first_rule_rec prog' (f,lv)); [ | intros H; rewrite H in Hrec; discriminate Hrec ].
      intros [ [i' s'] t'] Heq.
      rewrite Heq in Hrec.
      injection Hrec; clear Hrec; intros; subst.
      apply IHp in Heq.
      destruct Heq as [[lp t'] Hlpt].
      exists (lp, t').
      repeat split; try tauto.
      omega.

  - intros Hneq Hrec.
    case_eq (first_rule_rec prog' (f,lv)); [ | intros H; rewrite H in Hrec; discriminate Hrec ].
    intros [ [i' s'] t'] Heq.
    rewrite Heq in Hrec.
    injection Hrec; clear Hrec; intros; subst.
    apply IHp in Heq.
    destruct Heq as [[lp t'] Hlpt].
    exists (lp, t').
    repeat split; try tauto.
    omega.
Qed.

Definition active_term_order_superset_dec: forall (t t': active_term), {active_term_order_superset t t'} + {~ active_term_order_superset t t'}.
Proof.
intros t t'.
apply lex_prod_dec.
- apply eq_nat_dec.

- apply lt_dec.

- intros x y.
  unfold value_list_order.
  apply lt_dec.
Defined.

Definition lex : (active_term * term) -> (active_term * term) -> Prop :=
  lexprod active_term_order_superset term_order.

Lemma wf_lex : well_founded lex.
Proof.
exact (wf_lexprod active_term_order_superset_wf term_order_wf).
Qed.

Lemma sub_terms_trans t1 t2 t3:
  In t1 (sub_terms variable function constructor t2) ->
  In t2 (sub_terms _ _ _ t3) ->
  In t1 (sub_terms _ _ _ t3).
Proof.
induction t3 using term_ind2; intros H1 H2; simpl in *.
- destruct H2 as [Heq | Hf].
  + subst t2.
    left; now inversion H1.

  + inversion Hf.

- destruct H2 as [Heq |Hin].
  + subst t2.
    exact H1.

  + right.
    rewrite in_flat_map in *.
    destruct Hin as (x & Hin & Hx).
    exists x.
    split; [exact Hin |].
    auto.

- destruct H2 as [Heq |Hin].
  + subst t2.
    exact H1.

  + right.
    rewrite in_flat_map in *.
    destruct Hin as (x & Hin & Hx).
    exists x.
    split; [exact Hin |].
    auto.
Qed.

Lemma sub_terms_strict_trans t1 t2 t3:
  In t1 (sub_terms_strict variable function constructor t2) ->
  In t2 (sub_terms_strict _ _ _ t3) ->
  In t1 (sub_terms_strict _ _ _ t3).
Proof.
intros H1 H2.
destruct t3.
- inversion H2.

- simpl in *.
  apply in_flat_map in H2.
  apply sub_term_strict_incl in H1.
  destruct H2 as (x & Hin & Hx).
  apply in_flat_map.
  exists x; split; [exact Hin | now apply sub_terms_trans with t2].

- simpl in *.
  apply in_flat_map in H2.
  apply sub_term_strict_incl in H1.
  destruct H2 as (x & Hin & Hx).
  apply in_flat_map.
  exists x; split; [exact Hin | now apply sub_terms_trans with t2].
Qed.

Lemma lex_trans a1 a2 a3:
  lex a1 a2 -> lex a2 a3 -> lex a1 a3.
Proof.
intros H1 H2.
refine (lexprod_trans _ _ H1 H2).
- intros x1 x2 x3 Hx1 Hx2. 
  refine (lexprod_trans lt_trans _ Hx1 Hx2).
  intros v1 v2 v3 Hv1 Hv2.
  eapply lt_trans; [exact Hv1 | exact Hv2].
- intros.
  eapply sub_terms_strict_trans; eauto.
Qed.



Inductive list_order {A : Type} (R : A -> A -> Prop) : list A -> list A -> Prop :=
| lo_cons:  forall l1 l2 h, Forall (fun x => R x h) l1 -> list_order R (l1 ++ l2) (h :: l2).

Definition W {A : Type} (R : A -> A -> Prop) (l : list A) : Prop :=
  Acc (list_order R) l.
(*  forall l', list_order R l' l -> Acc (list_order R) l'. *)

Lemma deuxpointun (A : Type) (R : A -> A -> Prop) (l : list A) (a : A) :
  (forall b, R b a -> forall l', W R l' -> W R (b :: l')) ->
   W R l (* /\
   (forall l', list_order R l' l -> W R (a :: l')) *) ->
  W R (a :: l).
Proof.
  intros H1 H2.
  constructor; intros l' Hlo.
  inversion Hlo; subst.
  induction l1.
  - simpl in *.
    constructor.
    apply H2.

  - constructor.
    assert (Ha0 : R a0 a) by (inversion H3; assumption).
    apply (H1 a0 Ha0).
    unfold W.
    apply IHl1; try constructor; inversion H3; assumption.
Qed.

Lemma deuxpointdeux (A : Type) (R : A -> A -> Prop) (l : list A) (a : A) : 
  (forall b, R b a -> forall l, W R l -> W R (b :: l)) ->
  (forall l, W R l -> W R (a :: l)).
Proof.
intros H l' Hacc.
induction Hacc as [l'' Hl'' _].
apply deuxpointun.
- intros b Hb l' Hl'.
  now apply H.

- now constructor.
Qed.

Lemma deuxpointtrois (A : Type) (R : A -> A -> Prop) (l : list A) (a : A) :
  well_founded R -> W R l -> W R (a :: l).
Proof.
intros HR.
revert l.
induction (HR a).
intros l Hl.
eapply deuxpointdeux; [ exact l | | exact Hl ].
intros b Hb l' Hl'.
now apply H0.
Qed.

Lemma list_order_wf (A : Type) (R : A -> A -> Prop) :
  well_founded R -> well_founded (list_order R).
Proof.
intro HwfR.
intro l.
induction l.
- constructor.
  intros.
  inversion H.

- now apply deuxpointtrois.
Qed.

Lemma product_suml_lt l1 l2 : 
  product lt l1 l2 ->
  suml l1 < suml l2.
Proof.
intro Hprod.
induction Hprod.
- simpl; subst; omega.

- simpl.
  apply plus_lt_le_compat; [assumption|].
  induction H0.
  + trivial.

  + assert (x0 <= y0) by (destruct H0; omega).
     simpl; omega.
Qed.

Lemma PPO_active_term_order_superset act act' :
  PPO rank (term_from_active_term act) (term_from_active_term act') ->
  active_term_order_superset act act'.
Proof.
intro HPPO.
destruct act as (f & lv).
destruct act' as (f' & lv').
simpl in HPPO.
inversion HPPO; subst.
- apply in_map_iff in H1.
  destruct H1 as (v & Hv & _).
  destruct v.
  inversion Hv.

- apply in_map_iff in H2.
  destruct H2 as (v & Hv & _).
  subst t.
  contradict H3.
  apply fapply_not_PPO_value; trivial.
  apply term_value_eqv; eauto.

- now left.

- unfold active_term_order_superset.
  simpl.
  rewrite H2.
  right.
  unfold value_list_order.
  apply product_suml_lt.
  clear f f' H2 HPPO.
  revert H4; intros Hppo.
  assert (Hlen := Hppo).
  apply product_length in Hlen.
  do 2 rewrite map_length in Hlen.
  revert lv' Hppo Hlen;
    induction lv as [ | v lv IH ];
    intros lv' Hppo Hlen;
    destruct lv' as [ | v' lv' ];
    simpl in *;
    try discriminate Hlen.

  + inversion Hppo.

  + revert Hppo;
    set (lt := map (@term_from_value _ _ _) lv : list term);
    set (lt' := map (@term_from_value _ _ _) lv' : list term);
    intros Hppo.
    apply eq_add_S in Hlen.
    inversion Hppo; subst.

    * apply term_from_value_injective in H2; subst v'.
      apply product_conseq; trivial.
      apply IH; assumption.

    * apply product_consst;
      [ apply (PPO_value_lt_size variable function) with (rank := rank); assumption | ].

      { clear Hppo v v' IH H2;
        revert lt lv' lt' Hlen H4;
        induction lv as [ | v lv IH ];
        intros lt lv' lt' Hlen Hfor;
        destruct lv' as [ | v' lv' ];
        [ constructor
        | inversion Hlen
        | inversion Hlen
        | ].

        subst lt lt'.
        simpl in *.
        apply eq_add_S in Hlen.
        constructor.

        - inversion Hfor; subst.
          destruct H2.
          + left.
            apply (PPO_value_lt_size variable function) with (rank := rank); assumption.
          + right.
            f_equal.
            apply (@term_from_value_injective variable function); assumption.
        - apply IH;
          [ | inversion Hfor ];
          assumption.
      }
Qed.

Lemma term_order_PPO t1 t2 : term_order t1 t2 -> PPO rank t1 t2.
Proof.
intro Horder.
unfold term_order in Horder.
induction t2 using term_ind2.
- inversion Horder.

- simpl in Horder.
  apply in_flat_map in Horder.
  destruct Horder as (t' & Hin & Ht').
  apply PPO_trans_eq with t'.
  + apply sub_term_eq_or_strict in Ht'.
    destruct Ht' as [Heq | Ht'].
    * now subst; right.

    * left; apply H; assumption.

  + now apply ppo_constr_in.

- simpl in Horder.
  apply in_flat_map in Horder.
  destruct Horder as (t' & Hin & Ht').
  apply PPO_trans_eq with t'.
  + apply sub_term_eq_or_strict in Ht'.
    destruct Ht' as [Heq | Ht'].
    * now subst; right.

    * left; apply H; assumption.

  + now apply ppo_fun_in.
Qed.

Lemma max_arity_subst s t f lp :
  rule_vars_defined (rule_intro f lp t) ->
  let t' := fapply f (map (fun p => term_from_value variable function (@psubst variable constructor s p)) lp) in
  max_arity_term (subst s t) <= Nat.max (max_arity_rule (rule_intro f lp t)) (max_arity_term t').
Proof.
  intros Hvars t'.
  assert (Hn : forall x, In x (vars_of_term t) ->
                   max_arity_term (term_from_value variable function (s x)) <= max_arity_term t').
  { subst t'.
    intros x Hx; apply Hvars in Hx; simpl.
    rewrite PeanoNat.Nat.max_le_iff; right.
    clear t f Hvars.
    rewrite in_flat_map in Hx; destruct Hx as (p & Hp & Hvars).
    transitivity (max_arity_term (term_from_value variable function (psubst s p))).
    - clear lp Hp; revert x Hvars.
      induction p as [ x | c lp IH ] using pattern_ind2.
      + simpl.
        intros x' H; destruct H; [ subst x' | ]; easy.
      + intros x Hx; simpl in Hx.
        apply in_flat_map in Hx; destruct Hx as (p & Hp & Hvars).
        transitivity (max_arity_term (term_from_value variable function (psubst s p))).
        * now apply IH.
        * simpl.
          rewrite PeanoNat.Nat.max_le_iff; right.
          now apply maxl_is_max, in_map, in_map, in_map.
    - apply maxl_is_max, in_map.
      set (t := term_from_value _ _ _);
      change (term_from_value _ _ _) with ((fun p => term_from_value variable function (psubst s p)) p) in t;
        subst t.
      now apply in_map.
  }

  remember (max_arity_term t') as n eqn: Heq; clear Heq.
  transitivity (Nat.max (max_arity_term t) n).
  - clear f lp t' Hvars.
    induction t as [ x | c lt IH | f lt IH ] using term_ind2.
    + simpl; apply Hn.
      simpl; now left.

    + simpl; rewrite <- Max.max_assoc.
      apply Nat.max_le_compat; [ now rewrite map_length | ].
      simpl in Hn; clear c.
      induction lt as [ | t lt IHlt ]; [ now apply le_O_n | ].
      simpl.
      set (ml := maxl _) at 2.
      replace (Nat.max (Nat.max (max_arity_term t) ml) n)
      with (Nat.max (Nat.max (max_arity_term t) n) (Nat.max ml n));
        [ | now rewrite <- Max.max_assoc, (Max.max_assoc n), (Max.max_comm n),
            <- (Max.max_assoc ml), Max.max_idempotent, Max.max_assoc ].
      subst ml; apply Nat.max_le_compat.

      * apply IH; [ now left | ].
        intros x Hx; apply Hn.
        now simpl; apply in_or_app; left.

      * apply IHlt.
        now intros t' Ht'; apply IH; right.
        now intros x Hx; apply Hn; simpl; apply in_or_app; right.

    + simpl; rewrite <- Max.max_assoc.
      apply Nat.max_le_compat; [ now rewrite map_length | ].
      simpl in Hn; clear f.
      induction lt as [ | t lt IHlt ]; [ now apply le_O_n | ].
      simpl.
      set (ml := maxl _) at 2.
      replace (Nat.max (Nat.max (max_arity_term t) ml) n)
      with (Nat.max (Nat.max (max_arity_term t) n) (Nat.max ml n));
        [ | now rewrite <- Max.max_assoc, (Max.max_assoc n), (Max.max_comm n),
            <- (Max.max_assoc ml), Max.max_idempotent, Max.max_assoc ].
      subst ml; apply Nat.max_le_compat.

      * apply IH; [ now left | ].
        intros x Hx; apply Hn.
        now simpl; apply in_or_app; left.

      * apply IHlt.
        now intros t' Ht'; apply IH; right.
        now intros x Hx; apply Hn; simpl; apply in_or_app; right.

  - simpl.
    apply PeanoNat.Nat.max_le_compat_r.
    now apply PeanoNat.Nat.le_max_l.
Qed.

Lemma first_rule_max_arity act t i s :
  wf_prog max_arity prog ->
  first_rule act = Some (i, s, t) ->
  max_arity_term (term_from_active_term act) <= max_arity ->
  max_arity_term t <= max_arity.
Proof.
intros Hwfprog Hrule.
destruct act as [f lv].
apply first_rule_sound in Hrule.
destruct Hrule as ([lp'  t''] & Hlengthi & Heqi & Hunify_list & Hsubst).
subst t.
etransitivity.
- apply max_arity_subst with (f := f) (lp := lp').
  eapply andl_in; [ apply Hwfprog | ].
  apply in_map.
  rewrite <- Heqi.
  now apply nth_In.
- apply Max.max_lub.
   + etransitivity; [ apply maxl_is_max  | apply Hwfprog].
       apply in_map.
       rewrite <- Heqi.
       apply nth_In; trivial.
   + rewrite <- map_map.
      erewrite unify_list_sound; eauto.
Qed.



Inductive evaluates : term -> value -> Prop :=
| CAPPLY : forall lt lv c, evaluates_list lt lv -> evaluates (capply c lt) (c_capply c lv)
| FAPPLY : forall lt lv f v i s t, evaluates_list lt lv -> 
           first_rule (f, lv) = Some (i, s, t) -> 
           evaluates t v ->
           evaluates (fapply f lt) v
with evaluates_list : list term -> list value -> Prop :=
| E_nil : evaluates_list [] []
| E_cons : forall t v lt lv, evaluates t v -> evaluates_list lt lv -> evaluates_list (t :: lt) (v :: lv).

Scheme evaluates_mut := Induction for evaluates Sort Prop
with evaluates_list_mut := Induction for evaluates_list Sort Prop.

Lemma evaluates_ind2 : forall P,
(forall lt lv c, Forall2 evaluates lt lv ->
                 Forall2 P lt lv ->
                 P (capply c lt) (c_capply c lv)) ->
(forall lt lv f i s v t,
  Forall2 evaluates lt lv -> Forall2 P lt lv ->
  first_rule (f, lv) = Some (i, s, t) ->
  evaluates t v -> P t v ->
  P (fapply f lt) v) ->
forall (t : term) (v : value), evaluates t v -> P t v.
Proof.
intros P Hc Hf t v He.
induction He using evaluates_mut with (P := fun t v H => P t v)
(P0 := fun lt lv H => Forall2 P lt lv /\ Forall2 evaluates lt lv).
- apply Hc; tauto.
- eapply Hf; eauto; tauto.
- auto.
- split; constructor; auto; tauto.
Qed.

Inductive Forall2' (A B : Type) (R : A -> B -> Type) : list A -> list B -> Type :=
    Forall2'_nil : Forall2' R [] []
  | Forall2'_cons : forall (x : A) (y : B) (l : list A) (l' : list B),
                   R x y -> Forall2' R l l' -> Forall2' R (x :: l) (y :: l').

Lemma Forall2_trans_rel (A : Type) (R1 R2 : A -> A -> Prop) (l1 l2 : list A) : (forall x y, R1 x y -> R2 x y) -> Forall2 R1 l1 l2 -> Forall2 R2 l1 l2.
Proof.
intros H Hall.
induction Hall; auto.
Qed.

Lemma Forall2_product (A : Type) (R : A -> A -> Prop) (ls lt : list A) :
  ls <>  [] -> Forall2 R ls lt -> product R ls lt.
Proof.
induction ls; intros Hnil Hall; try tauto.
clear Hnil.
destruct lt as [ | b lt]; [inversion Hall |].
inversion Hall; subst.
constructor 2; trivial.
eapply Forall2_trans_rel.
- intros; constructor; exact H.
- trivial.
Qed.

Lemma Forall2_eq A (l1 l2 : list A) :
  Forall2 eq l1 l2 -> l1 = l2.
Proof.
intro H; induction H; subst; trivial.
Qed.

Lemma evaluates_unique t v1 v2 :
  evaluates t v1 ->
  evaluates t v2 ->
  v1 = v2.
Proof.
intro H1; revert v2.
induction H1 using evaluates_ind2.
- intros v2 H2.
  inversion H2; subst; clear H2.
  f_equal; revert lv0 H5.
  induction H; intros lv0 Hlv0; inversion Hlv0; trivial.
  subst.
  f_equal; inversion H0; subst; auto.
- intros v2 Hv2.
  inversion Hv2; subst; clear Hv2.
  assert (Heq : lv = lv0) by
   (clear H6 H1; revert lv0 H5;
    induction H; intros lv0 Hlv0; inversion Hlv0; trivial;
    subst; f_equal; inversion H0; subst; auto).
  subst lv0.
  rewrite H6 in H1; inversion H1; subst.
  now apply IHevaluates.
Qed.

Lemma evaluates_value v : 
  evaluates (term_from_value _ _ v) v.
Proof.
induction v using value_ind2.
constructor.
induction l as [|v lv]; constructor; auto with *.
Qed.

Lemma In_nth:
  forall (A : Type) (l : list A) (x d : A) n,
  n < length l -> nth n l d = x -> x ∈ l.
Proof.
intros A l x d n.
revert l.
induction n; intros [ | a l];
unfold nth; simpl; intros; try tauto; try omega.
auto with *.
Qed.

Lemma evaluates_sound t v c:
  (forall (t0 : term) (v0 : value), assoc_cache t0 c = Some v0 
    -> evaluates t0 v0 /\ max_arity_term (term_from_value variable function v0) <= max_arity) ->
  evaluates t v ->
  max_arity_term t <= max_arity ->
  exists p, wf p /\ proj_right p = v /\ proj_left p = t /\ cache_left p = c /\
            max_arity_term (term_from_value variable function v) <= max_arity /\
   (forall t0 v0, assoc_cache t0 (cache_right p) = Some v0
      -> evaluates t0 v0 /\ max_arity_term (term_from_value variable function v0) <= max_arity).
Proof.
intros Hc Heval.
revert c Hc.
induction Heval using evaluates_ind2; intros c0 Hc0 Harity.
- assert (Hlp : exists lp c1,
    andl (map wf lp) /\ map (@proj_left _ _ _) lp = lt /\
    map (@proj_right _ _ _) lp = lv /\
    cache_path variable_eq_dec function_eq_dec constructor_eq_dec c0 c1 lp = true /\
    maxl (map (@max_arity_term _ _ _) (map (@term_from_value variable function _) lv)) <= max_arity /\
    forall (t0 : term) (v : value), assoc_cache t0 c1 = Some v -> evaluates t0 v 
        /\ max_arity_term (term_from_value variable function v) <= max_arity
    ).
  { assert (Harityall: forall t, In t lt -> max_arity_term t <= max_arity) by
    ( intros t Ht; simpl in Harity; apply Max.max_lub_r in Harity;
      etransitivity; [ | apply Harity]; now apply maxl_is_max, in_map).
    clear Harity H.
    revert c0 lv H0 Hc0.
    induction lt using rev_ind; intros c0 lv H0 Hc0.
   - exists []; exists c0; simpl.
     inversion H0.
     simpl; intuition.
     now rewrite cache_beq_refl.
   - apply Forall2_app_inv_l in H0.
     destruct H0 as (lv' & ly & Hlt & Hx & Heq).
     subst lv.
     inversion Hx; subst.
     inversion H3; subst; clear H3.
     destruct IHlt with (c0 := c0) (lv := lv') as (lp & c' & Hlp);
     auto with *.
     decompose record Hlp.
     destruct H1  with (c:= c') as [p Hp]; auto with *.
     exists (lp ++ [p]); exists (cache_right p).
     decompose record Hp; subst.
     rewrite map_app, cache_path_app, andl_app.
     repeat rewrite map_app.
     simpl; repeat rewrite cache_beq_refl.
     repeat split; try tauto.
     + rewrite maxl_app.
       apply Nat.max_lub; trivial.
       simpl.
       now rewrite Max.max_0_r.
     + now apply H12.
     + now apply H12 in H0.
  }
  destruct Hlp as [lp Hlp]; decompose record Hlp.
  eexists (cbv_constr  _ _ (capply c lt) _ (c_capply c lv)); simpl.
  repeat split; eauto.
  + erewrite <- map_length; rewrite H1.
    now apply Max.max_lub_l in Harity.
  + apply Nat.max_lub; trivial.
    rewrite map_length.
    apply Max.max_lub_l in Harity.
    subst lv lt.
    now rewrite map_length in *.
  + now apply H7.
  + edestruct H7; eauto.
- assert (Hlp : exists lp c1,
    andl (map wf lp) /\ map (@proj_left _ _ _) lp = lt /\
    map (@proj_right _ _ _) lp = lv /\
    cache_path variable_eq_dec function_eq_dec constructor_eq_dec c0 c1 lp = true /\
    maxl (map (@max_arity_term _ _ _) (map (@term_from_value variable function _) lv)) <= max_arity /\
    forall (t0 : term) (v : value), assoc_cache t0 c1 = Some v -> evaluates t0 v
    /\ max_arity_term (term_from_value variable function v) <= max_arity

    ).
  { assert (Harityall: forall t, In t lt -> max_arity_term t <= max_arity) by
    ( intros t0 Ht; simpl in Harity; apply Max.max_lub_r in Harity;
      etransitivity; [ | apply Harity]; now apply maxl_is_max, in_map).
    clear Harity H1 H.
    revert c0 lv H0 Hc0.
    induction lt using rev_ind; intros c0 lv H0 Hc0.
   - exists []; exists c0; simpl.
     inversion H0.
     simpl; intuition.
     now rewrite cache_beq_refl.
   - apply Forall2_app_inv_l in H0.
     destruct H0 as (lv' & ly & Hlt & Hx & Heq).
     subst lv.
     inversion Hx; subst.
     inversion H3; subst; clear H3.
     destruct IHlt with (c0 := c0) (lv := lv') as (lp & c' & Hlp);
     auto with *.
     decompose record Hlp.
     destruct H1  with (c:= c') as [p Hp]; auto with *.
     exists (lp ++ [p]); exists (cache_right p).
     decompose record Hp; subst.
     rewrite map_app, cache_path_app, andl_app.
     repeat rewrite map_app.
     simpl; repeat rewrite cache_beq_refl.
     repeat split; try tauto.
     + rewrite maxl_app.
       apply Nat.max_lub; trivial.
       simpl.
       now rewrite Max.max_0_r.
     + now apply H12.
     + now apply H12 in H0.
  }
  destruct Hlp as (lp & cr & Hlp); decompose record Hlp.
  case_eq (assoc (term_beq variable_eq_dec function_eq_dec constructor_eq_dec) (fapply f (map (@term_from_value _ _ _) lv)) cr).
  + intros v0 Hv0.
    destruct (H8 _ _ Hv0) as [Heval0 Harity0].
    eexists (cbv_split _ (cbv_read _ (fapply f _) _) _ _ _ _).
    subst.
    assert (v0 = v).
    { eapply evaluates_unique; eauto.
      econstructor; eauto.
      clear H H1 H0 H2 H5 H6 Hv0 H8 Hlp cr IHHeval Harity Heval0.
      induction lp; constructor; trivial.
      apply evaluates_value.
    }
    subst v0.
    repeat split; trivial;simpl; repeat split; eauto.
    * apply Max.max_lub_l in Harity.
      now rewrite map_length in Harity.
    * now apply H8.
    * now apply H8 in H3.
  + assert(Hrule := H1).
    apply first_rule_sound in H1.
    destruct H1 as [[lp' t'] (Hlen & Hnth & Hunify & Hsubst)].
    destruct IHHeval with cr as [p Hp]; trivial.
    * unfold wf_prog in prog_is_wf; destruct prog_is_wf as (Hvars & Hmaxarity).
      subst t.
      apply first_rule_max_arity in Hrule; trivial.
      simpl; rewrite map_length.
      apply Nat.max_lub; trivial.
      subst lv lt.
      apply Nat.max_lub_l in Harity.
      now rewrite map_length in *.
    * intro Hcache.
      decompose record Hp; decompose record Hlp.
      set (tt := fapply f(map (term_from_value variable function (constructor:=constructor)) (map (psubst s) lp'))).
      eexists (cbv_split lp (cbv_update i s p cr (fapply f _) ((tt, v) :: (cache_right p)) v) _ (fapply f lt) ((tt, v):: (cache_right p)) v).
      simpl; subst.
      assert(Hlp_len : length lp <= max_arity) by
      (simpl in Harity; rewrite map_length in Harity; lia).
      apply unify_list_sound in Hunify.
      rewrite <- H7 in *; simpl.
      repeat split; auto.
      -- subst tt; exists lp'; rewrite Hunify.
         eexists; repeat split; eauto; try tauto.
         now repeat rewrite map_length.
      -- intros.
         case_eq (term_beq variable_eq_dec function_eq_dec constructor_eq_dec t0 tt).
         ++ intro Heq; rewrite term_beq_eq in Heq; subst t0.
            replace (term_beq variable_eq_dec function_eq_dec constructor_eq_dec tt tt) with true in H1 by
            (symmetry; now apply term_beq_eq).
            subst tt.
            eapply FAPPLY with (lv := (map (proj_right (constructor:=constructor)) lp)) (i := i) (s := s) (t := proj_left p); trivial.
            ** rewrite Hunify.
               clear H6 H3 H0 H1 Hcache Hlp H5 H6 H7 H11 H12 H13 H16 H14 H2 Harity H Hunify Hlp_len Hrule.
               induction lp; constructor.
               apply evaluates_value.
               apply IHlp; trivial.
               simpl in H17.
               now apply Nat.max_lub_r in H17.
            ** assert( Hbeq : forall t, term_beq variable_eq_dec function_eq_dec constructor_eq_dec t t = true) by
               (now intros; rewrite term_beq_eq).
               rewrite Hbeq in H3.
               now inversion H3.
         ++ intro Heq; rewrite Heq in H3.
            now apply H13.
      -- case_eq (term_beq variable_eq_dec function_eq_dec constructor_eq_dec t0 tt).
         ++ intro Heq; rewrite Heq in H3; inversion H3; now subst.
         ++ intro Hneq; rewrite Hneq in H3.
            now apply H13 in H3.
Qed.

(* Simpler, weaker version *)
Lemma evaluates_sound' (t : term) (v : value):
  evaluates t v ->
  max_arity_term t <= max_arity ->
  exists p, wf p /\ proj_right p = v /\ proj_left p = t.
Proof.
intros.
destruct (@evaluates_sound t v []); trivial.
- intros t' v' Hf; inversion Hf.
- intuition; eexists; eauto.
Qed.

End Evaluates.

Create HintDb eval.

Ltac reduce := 
  progress (repeat constructor) ||
  (econstructor; [repeat constructor; repeat reduce; eauto with eval
                              | solve [unfold first_rule; simpl; trivial]
                              | unfold assoc_default; repeat constructor; eauto with eval]).

Hint Extern 1 (@evaluates _ _ _ _ _ _ _ _ _ _)  => eapply evaluates_value: eval.
