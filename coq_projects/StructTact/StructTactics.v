(** [subst_max] performs as many [subst] as possible, clearing all
    trivial equalities from the context. *)
Ltac subst_max :=
  repeat match goal with
           | [ H : ?X = _ |- _ ]  => subst X
           | [H : _ = ?X |- _] => subst X
         end.

(** The Coq [inversion] tries to preserve your context by only adding
    new equalities, and keeping the inverted hypothesis.  Often, you
    want the resulting equalities to be substituted everywhere.  [inv]
    performs this post-substitution.  Often, you don't need the
    original hypothesis anymore.  [invc] extends [inv] and removes the
    inverted hypothesis.  Sometimes, you also want to perform
    post-simplification.  [invcs] extends [invc] and tries to simplify
    what it can. *)
Ltac inv H := inversion H; subst_max.
Ltac invc H := inv H; clear H.
Ltac invcs H := invc H; simpl in *.

(** [inv_prop] finds the first hypothesis including the term [P] and uses [inv]
    to invert it. *)
Ltac inv_prop P :=
  match goal with
  | [ H : context[P] |- _] =>
    inv H
  end.

(** [inv_prop] finds the first hypothesis including the term [P] and uses [invc]
    to invert it. *)
Ltac invc_prop P :=
  match goal with
  | [ H : context[P] |- _] =>
    invc H
  end.

(** [inv_prop] finds the first hypothesis including the term [P] and uses
    [invcs] to invert it. *)
Ltac invcs_prop P :=
  match goal with
  | [ H : context[P] |- _] =>
    invcs H
  end.

(** [break_if] finds instances of [if _ then _ else _] in your goal or
    context, and destructs the discriminee, while retaining the
    information about the discriminee's value leading to the branch
    being taken. *)
Ltac break_if :=
  match goal with
    | [ |- context [ if ?X then _ else _ ] ] =>
      match type of X with
        | sumbool _ _ => destruct X
        | _ => destruct X eqn:?
      end
    | [ H : context [ if ?X then _ else _ ] |- _] =>
      match type of X with
        | sumbool _ _ => destruct X
        | _ => destruct X eqn:?
      end
  end.

(** [break_match_hyp] looks for a [match] construct in some
    hypothesis, and destructs the discriminee, while retaining the
    information about the discriminee's value leading to the branch
    being taken. *)
Ltac break_match_hyp :=
  match goal with
    | [ H : context [ match ?X with _ => _ end ] |- _] =>
      match type of X with
        | sumbool _ _ => destruct X
        | _ => destruct X eqn:?
      end
  end.

(** [break_match_goal] looks for a [match] construct in your goal, and
    destructs the discriminee, while retaining the information about
    the discriminee's value leading to the branch being taken. *)
Ltac break_match_goal :=
  match goal with
    | [ |- context [ match ?X with _ => _ end ] ] =>
      match type of X with
        | sumbool _ _ => destruct X
        | _ => destruct X eqn:?
      end
  end.

(** [break_match] breaks a match, either in a hypothesis or in your
    goal. *)
Ltac break_match := break_match_goal || break_match_hyp.

(** [break_inner_match' t] tries to destruct the innermost [match] it
    find in [t]. *)
Ltac break_inner_match' t :=
 match t with
   | context[match ?X with _ => _ end] =>
     break_inner_match' X || destruct X eqn:?
   | _ => destruct t eqn:?
 end.

(** [break_inner_match_goal] tries to destruct the innermost [match] it
    find in your goal. *)
Ltac break_inner_match_goal :=
 match goal with
   | [ |- context[match ?X with _ => _ end] ] =>
     break_inner_match' X
 end.

(** [break_inner_match_hyp] tries to destruct the innermost [match] it
    find in a hypothesis. *)
Ltac break_inner_match_hyp :=
 match goal with
   | [ H : context[match ?X with _ => _ end] |- _ ] =>
     break_inner_match' X
 end.

(** [break_inner_match] tries to destruct the innermost [match] it
    find in your goal or a hypothesis. *)
Ltac break_inner_match := break_inner_match_goal || break_inner_match_hyp.

(** [break_exists] destructs an [exists] in your context. *)
Ltac break_exists :=
  repeat match goal with
           | [H : exists _, _ |- _ ] => destruct H
         end.

(** [break_exists_exists] destructs an [exists] in your context, and uses
    the witness found as witness for your current goal. *)
Ltac break_exists_exists :=
  repeat match goal with
           | H:exists _, _ |- _ =>
             let x := fresh "x" in
             destruct H as [x]; exists x
         end.

(** [break_and] destructs all conjunctions in context. *)
Ltac break_and :=
  repeat match goal with
           | [H : _ /\ _ |- _ ] => destruct H
         end.

(** [break_and_goal] splits a conjunctive goal into one goal per
    conjunct.  In simpler terms, it splits a goal of the shape [G1 /\
    ... /\ Gn] into [n] goals [G1], ..., [Gn]. *)
Ltac break_and_goal :=
    repeat match goal with
             | [ |- _ /\ _ ] => split
           end.

(** [solve_by_inverison' tac] succeeds if it can solve your goal by
    inverting a hypothesis and then running [tac]. *)
Ltac solve_by_inversion' tac :=
  match goal with
    | [H : _ |- _] => solve [inv H; tac]
  end.

(** [solve_by_inverison] succeeds if it can solve your goal by
    inverting a hypothesis and then running [auto]. *)
Ltac solve_by_inversion := solve_by_inversion' auto.

(** TODO: document this. *)
Ltac apply_fun f H:=
  match type of H with
    | ?X = ?Y => assert (f X = f Y)
  end.

(** [conclude H tac] assumes [H] is of the form [A -> B] and
    specializes it into [B] if it successfully proves [A] using
    [tac]. *)
Ltac conclude H tac :=
  (let H' := fresh in
   match type of H with
     | ?P -> _ => assert P as H' by (tac)
   end; specialize (H H'); clear H').

(** [concludes] specializes all implication hypotheses if it can prove
    their premise using [auto]. *)
Ltac concludes :=
  match goal with
    | [ H : ?P -> _ |- _ ] => conclude H auto
  end.

(** [forward H] performs forward reasoning in hypothesis [H] of the
    shape [A -> B] by asserting [A] to be proven.  You can
    subsequently call [concludes] to specialize [H] to [B]. *)
Ltac forward H :=
  let H' := fresh in
   match type of H with
     | ?P -> _ => assert P as H'
   end.

(** [forwards] performs forward reasoning in all hypotheses. *)
Ltac forwards :=
  match goal with
    | [ H : ?P -> _ |- _ ] => forward H
  end.

(** [find_elim_prop] finds a hypothesis that includes [P] and eliminates it with
    the built-in [elim] tactic. *)
Ltac find_elim_prop P :=
  match goal with
  | [ H : context [ P ] |- _ ] =>
    elim H
  end.

(** [find_elim_prop] finds a hypothesis that includes [P] and eliminates it with
    the built-in [eelim] tactic. *)
Ltac find_eelim_prop P :=
  match goal with
  | [ H : context [ P ] |- _ ] =>
    eelim H
  end.

(** [find_contradiction] solves a goal if two equalities are
    incompatible. *)
Ltac find_contradiction :=
  match goal with
    | [ H : ?X = _, H' : ?X = _ |- _ ] => rewrite H in H'; solve_by_inversion
  end.

(** [find_rewrite] performs a [rewrite] with some hypothesis in some
    other hypothesis. *)
Ltac find_rewrite :=
  match goal with
    | [ H : ?X _ _ _ _ = _, H' : ?X _ _ _ _ = _ |- _ ] => rewrite H in H'
    | [ H : ?X = _, H' : ?X = _ |- _ ] => rewrite H in H'
    | [ H : ?X = _, H' : context [ ?X ] |- _ ] => rewrite H in H'
    | [ H : ?X = _ |- context [ ?X ] ] => rewrite H
  end.

(** [find_rewrite_lem lem] rewrites with [lem] in some hypothesis. *)
Ltac find_rewrite_lem lem :=
  match goal with
    | [ H : _ |- _ ] =>
      rewrite lem in H; [idtac]
  end.

(** [find_rewrite_lem_by lem t] rewrites with [lem] in some
    hypothesis, discharging the generated obligations with [t]. *)
Ltac find_rewrite_lem_by lem t :=
  match goal with
    | [ H : _ |- _ ] =>
      rewrite lem in H by t
  end.

(** [find_erewrite_lem_by lem] erewrites with [lem] in some hypothesis
    if it can discharge the obligations with [eauto]. *)
Ltac find_erewrite_lem lem :=
  match goal with
    | [ H : _ |- _] => erewrite lem in H by eauto
  end.

(** [find_reverse_rewrite] performs a [rewrite <-] with some hypothesis in some
    other hypothesis. *)
Ltac find_reverse_rewrite :=
  match goal with
    | [ H : _ = ?X _ _ _ _, H' : ?X _ _ _ _ = _ |- _ ] => rewrite <- H in H'
    | [ H : _ = ?X, H' : context [ ?X ] |- _ ] => rewrite <- H in H'
    | [ H : _ = ?X |- context [ ?X ] ] => rewrite <- H
  end.

(** [find_inversion] find a symmetric equality and performs [invc] on it. *)
Ltac find_inversion :=
  match goal with
    | [ H : ?X _ _ _ _ _ _ = ?X _ _ _ _ _ _ |- _ ] => invc H
    | [ H : ?X _ _ _ _ _ = ?X _ _ _ _ _ |- _ ] => invc H
    | [ H : ?X _ _ _ _ = ?X _ _ _ _ |- _ ] => invc H
    | [ H : ?X _ _ _ = ?X _ _ _ |- _ ] => invc H
    | [ H : ?X _ _ = ?X _ _ |- _ ] => invc H
    | [ H : ?X _ = ?X _ |- _ ] => invc H
  end.

(** [prove_eq] derives equalities of arguments from an equality of
    constructed values. *)
Ltac prove_eq :=
  match goal with
    | [ H : ?X ?x1 ?x2 ?x3 = ?X ?y1 ?y2 ?y3 |- _ ] =>
      assert (x1 = y1) by congruence;
        assert (x2 = y2) by congruence;
        assert (x3 = y3) by congruence;
        clear H
    | [ H : ?X ?x1 ?x2 = ?X ?y1 ?y2 |- _ ] =>
      assert (x1 = y1) by congruence;
        assert (x2 = y2) by congruence;
        clear H
    | [ H : ?X ?x1 = ?X ?y1 |- _ ] =>
      assert (x1 = y1) by congruence;
        clear H
  end.

(** [tuple_inversion] inverses an equality of tuple into equalities for
    each component. *)
Ltac tuple_inversion :=
  match goal with
    | [ H : (_, _, _, _) = (_, _, _, _) |- _ ] => invc H
    | [ H : (_, _, _) = (_, _, _) |- _ ] => invc H
    | [ H : (_, _) = (_, _) |- _ ] => invc H
  end.

(** [f_apply H f] derives a hypothesis of type [f X = f Y] if [H] has
    type [X = Y]. *)
Ltac f_apply H f :=
  match type of H with
    | ?X = ?Y =>
      assert (f X = f Y) by (rewrite H; auto)
  end.

(** [break_let] breaks a destructuring [let] for a pair. *)
Ltac break_let :=
  match goal with
    | [ H : context [ (let (_,_) := ?X in _) ] |- _ ] => destruct X eqn:?
    | [ |- context [ (let (_,_) := ?X in _) ] ] => destruct X eqn:?
  end.

(** [break_or_hyp] breaks a disjunctive hypothesis, splitting your
    goal into two. *)
Ltac break_or_hyp :=
  match goal with
    | [ H : _ \/ _ |- _ ] => invc H
  end.

(** [copy_apply lem H] adds a hypothesis obtained by [apply]-ing [lem]
    in [H]. *)
Ltac copy_apply lem H :=
  let x := fresh in
  pose proof H as x;
    apply lem in x.

(** [copy_eapply lem H] adds a hypothesis obtained by [eapply]-ing
    [lem] in [H]. *)
Ltac copy_eapply lem H :=
  let x := fresh in
  pose proof H as x;
    eapply lem in x.

(** [conclude_using tac] specializes a hypothesis if it can prove its
    premise using [tac]. *)
Ltac conclude_using tac :=
  match goal with
    | [ H : ?P -> _ |- _ ] => conclude H tac
  end.

(** [find_higher_order_rewrite] tries to [rewrite] with
    possibly-quantified hypotheses into other hypotheses or the
    goal. *)
Ltac find_higher_order_rewrite :=
  match goal with
    | [ H : _ = _ |- _ ] => rewrite H in *
    | [ H : forall _, _ = _ |- _ ] => rewrite H in *
    | [ H : forall _ _, _ = _ |- _ ] => rewrite H in *
  end.

(** [find_reverse_higher_order_rewrite] tries to [rewrite <-] with
    possibly-quantified hypotheses into other hypotheses or the
    goal. *)
Ltac find_reverse_higher_order_rewrite :=
  match goal with
    | [ H : _ = _ |- _ ] => rewrite <- H in *
    | [ H : forall _, _ = _ |- _ ] => rewrite <- H in *
    | [ H : forall _ _, _ = _ |- _ ] => rewrite <- H in *
  end.

(** [clean] removes any hypothesis of the shape [X = X]. *)
Ltac clean :=
  match goal with
    | [ H : ?X = ?X |- _ ] => clear H
  end.

(** [find_apply_hyp_goal] tries solving the goal applying some
    hypothesis. *)
Ltac find_apply_hyp_goal :=
  match goal with
    | [ H : _ |- _ ] => solve [apply H]
  end.

(** [find_copy_apply_lem_hyp lem] tries to find a hypothesis to which
    [lem] can be applied, and adds a hypothesis resulting from the
    application. *)
Ltac find_copy_apply_lem_hyp lem :=
  match goal with
    | [ H : _ |- _ ] => copy_apply lem H
  end.

(** [find_apply_hyp_hyp] finds a hypothesis which can be applied in
    another hypothesis, and performs the application. *)
Ltac find_apply_hyp_hyp :=
  match goal with
    | [ H : forall _, _ -> _,
        H' : _ |- _ ] =>
      apply H in H'; [idtac]
    | [ H : _ -> _ , H' : _ |- _ ] =>
      apply H in H'; auto; [idtac]
  end.

(** [find_copy_apply_hyp_hyp] finds a hypothesis which can be applied
    in another hypothesis, and adds a hypothesis with the application
    performed. *)
Ltac find_copy_apply_hyp_hyp :=
  match goal with
    | [ H : forall _, _ -> _,
        H' : _ |- _ ] =>
      copy_apply H H'; [idtac]
    | [ H : _ -> _ , H' : _ |- _ ] =>
      copy_apply H H'; auto; [idtac]
  end.

(** [find_apply_lem_hyp lem] finds a hypothesis where [lem] can be
    [apply]-ed, and performes the application. *)
Ltac find_apply_lem_hyp lem :=
  match goal with
    | [ H : _ |- _ ] => apply lem in H
  end.

(** [find_eapply_lem_hyp lem] finds a hypothesis where [lem] can be
    [eapply]-ed, and performes the application. *)
Ltac find_eapply_lem_hyp lem :=
  match goal with
    | [ H : _ |- _ ] => eapply lem in H
  end.

(** TODO: document this. *)
Ltac insterU H :=
  match type of H with
    | forall _ : ?T, _ =>
      let x := fresh "x" in
      evar (x : T);
      let x' := (eval unfold x in x) in
        clear x; specialize (H x')
  end.

(** TODO: document this. *)
Ltac find_insterU :=
  match goal with
    | [ H : forall _, _ |- _ ] => insterU H
  end.

(** [eapply_prop P] finds a hypothesis proving [P] and [eapply]-es it. *)
Ltac eapply_prop P :=
  match goal with
    | H : P _ |- _ =>
      eapply H
  end.

(** [find_eapply_prop P] finds a hypothesis including [P] and [eapply]-es it. *)
Ltac find_eapply_prop P :=
  match goal with
    | H : context [ P ] |- _ =>
      eapply H
  end.

(** [isVar t] succeeds if term [t] is a variable in the context. *)
Ltac isVar t :=
    match goal with
      | v : _ |- _ =>
        match t with
          | v => idtac
        end
    end.

(** [remGen t] is useful when one wants to do induction on a
    hypothesis whose indices are not concrete.  By default, the
    [induction] tactic will first generalize them, losing information
    in the process.  By introducing an equality, one can save this
    information while generalizing the hypothesis. *)
Ltac remGen t :=
  let x := fresh in
  let H := fresh in
  remember t as x eqn:H;
    generalize dependent H.

(** [remGenIfNotVar t] performs [remGen t] unless [t] is a simple
    variable. *)
Ltac remGenIfNotVar t := first [isVar t| remGen t].

(** [rememberNonVars H] will pose an equation for all indices of [H]
    that are concrete.  For instance, given: [H : P a (S b) c], it
    will generalize into [H : P a b' c] and [EQb : b' = S b]. *)
Ltac rememberNonVars H :=
  match type of H with
    | _ ?a ?b ?c ?d ?e =>
      remGenIfNotVar a;
      remGenIfNotVar b;
      remGenIfNotVar c;
      remGenIfNotVar d;
      remGenIfNotVar e
    | _ ?a ?b ?c ?d =>
      remGenIfNotVar a;
      remGenIfNotVar b;
      remGenIfNotVar c;
      remGenIfNotVar d
    | _ ?a ?b ?c =>
      remGenIfNotVar a;
      remGenIfNotVar b;
      remGenIfNotVar c
    | _ ?a ?b =>
      remGenIfNotVar a;
      remGenIfNotVar b
    | _ ?a =>
      remGenIfNotVar a
  end.

(* [generalizeEverythingElse H] tries to generalize everything that is
   not [H]. *)
Ltac generalizeEverythingElse H :=
  repeat match goal with
           | [ x : ?T |- _ ] =>
             first [
                 match H with
                   | x => fail 2
                 end |
                 match type of H with
                   | context [x] => fail 2
                 end |
                 revert x]
         end.

(* [prep_induction H] prepares your goal to perform [induction] on [H] by:
   - remembering all concrete indices of [H] via equations;
   - generalizing all variables that are not depending on [H] to strengthen the
     induction hypothesis. *)
Ltac prep_induction H :=
  rememberNonVars H;
  generalizeEverythingElse H.

(* [econcludes] tries to specialize a hypothesis using [eauto]. *)
Ltac econcludes :=
  match goal with
    | [ H : ?P -> _ |- _ ] => conclude H eauto
  end.

(** [find_copy_eapply_lem_hyp lem] tries to find a hypothesis to which
    [lem] can be [eapply]-ed, and adds a hypothesis resulting from the
    application. *)
Ltac find_copy_eapply_lem_hyp lem :=
  match goal with
    | [ H : _ |- _ ] => copy_eapply lem H
  end.

(** [apply_prop_hyp P Q] tries to [apply] a hypothesis about [P] to a
    hypothesis about [Q]. *)
Ltac apply_prop_hyp P Q :=
  match goal with
  | [ H : context [ P ], H' : context [ Q ] |- _ ] =>
    apply H in H'
  end.

(** [apply_prop_hyp P Q] tries to [eapply] a hypothesis about [P] to a
    hypothesis about [Q]. *)
Ltac eapply_prop_hyp P Q :=
  match goal with
  | [ H : context [ P ], H' : context [ Q ] |- _ ] =>
    eapply H in H'
  end.

(** [apply_prop_hyp P Q] tries to [eapply] a hypothesis about [P] to a
    hypothesis about [Q], posing the result as a new hypothesis. *)
Ltac copy_eapply_prop_hyp P Q :=
  match goal with
    | [ H : context [ P ], H' : context [ Q ] |- _ ] =>
      copy_eapply H H'
  end.

Ltac eapply_lem_prop_hyp lem P :=
  match goal with
  | [ H : context [ P ] |- _ ] =>
    eapply lem in H
  end.

Ltac copy_eapply_lem_prop_hyp lem P :=
  match goal with
  | [ H : context [ P ] |- _ ] =>
    copy_eapply lem H
  end.

(** [find_false] finds a hypothesis of the shape [P -> False] in the
    context and cuts your goal with it, leaving you with the
    obligation of proving its premise [P]. *)
Ltac find_false :=
  match goal with
    | H : _ -> False |- _ => exfalso; apply H
  end.

(** [injc H] performs [injection] on [H], then clears [H] and
    simplifies the context. *)
Ltac injc H :=
  injection H; clear H; intros; subst_max.

(** [find_injection] looks for an [injection] in the context and
    performs [injc]. *)
Ltac find_injection :=
  match goal with
    | [ H : ?X _ _ _ _ _ _ = ?X _ _ _ _ _ _ |- _ ] => injc H
    | [ H : ?X _ _ _ _ _ = ?X _ _ _ _ _ |- _ ] => injc H
    | [ H : ?X _ _ _ _ = ?X _ _ _ _ |- _ ] => injc H
    | [ H : ?X _ _ _ = ?X _ _ _ |- _ ] => injc H
    | [ H : ?X _ _ = ?X _ _ |- _ ] => injc H
    | [ H : ?X _ = ?X _ |- _ ] => injc H
  end.

(** [aggressive_rewrite_goal] rewrites in the goal with any
    hypothesis. *)
Ltac aggressive_rewrite_goal :=
  match goal with H : _ |- _ => rewrite H end.

(** [break_exists_name x] destructs an existential in context and
    names the witness [x]. *)
Ltac break_exists_name x :=
  match goal with
  | [ H : exists _, _ |- _ ] => destruct H as [x H]
  end.
