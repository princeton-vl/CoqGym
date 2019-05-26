
(*************************************************************************)
(** The simply-typed lambda calculus in Coq. *)
(*************************************************************************)

(** An interactive tutorial on developing programming language
    metatheory.  This file uses the simply-typed lambda calculus
    (STLC) to demonstrate the locally nameless representation of
    lambda terms and cofinite quantification in judgments.

    This tutorial concentrates on "how" to formalize STLC; for more
    details about "why" we use this style of development see:
    "Engineering Formal Metatheory", Aydemir, Chargu'eraud, Pierce,
    Pollack, Weirich. POPL 2008.

    Tutorial authors: Brian Aydemir and Stephanie Weirich, with help
    from Aaron Bohannon, Nate Foster, Benjamin Pierce, Jeffrey
    Vaughan, Dimitrios Vytiniotis, and Steve Zdancewic.  Adapted from
    code by Arthur Chargu'eraud.

    Draft of 7/14/2009
*)


(*************************************************************************)
(** * Contents
    - Syntax of STLC
    - Substitution
    - Free variables
    - Open
    - Local closure
    - Properties about basic operations
    - Cofinite quantification
    - Tactic support
    - Typing environments
    - Typing relation
    - Weakening
    - Substitution
    - Values and evaluation
    - Preservation
    - Progress
    - Additional properties
    - Renaming
    - Decidability of typechecking
    - Equivalence of exist fresh and cofinite

  Solutions to exercises are in [STLCsol.v].
*)
(*************************************************************************)


(** First, we import a number of definitions from the Metatheory
    library (see Metatheory.v).  The following command makes those
    definitions available in the rest of this file.  This command will
    only succeed if you have already run "make" in the tutorial
    directory to compile the Metatheory library.
*)

Require Import Metalib.Metatheory.


(*************************************************************************)
(** * Syntax of STLC *)
(*************************************************************************)

(** We use a locally nameless representation for the simply-typed
    lambda calculus, where bound variables are represented as natural
    numbers (de Bruijn indices) and free variables are represented as
    [atom]s.

    The type [atom], defined in the MetatheoryAtom library, represents
    names.  Equality on names is decidable ([eq_atom_dec]), and it is
    possible to generate an atom fresh for any given finite set of
    atoms ([atom_fresh]).
*)

Inductive typ : Set :=
  | typ_base  : typ
  | typ_arrow : typ -> typ -> typ.

Inductive exp : Set :=
  | bvar : nat  -> exp
  | fvar : atom -> exp
  | abs  : typ -> exp  -> exp
  | app  : exp  -> exp -> exp.

Coercion bvar : nat >-> exp.
Coercion fvar : atom >-> exp.

(** We declare the constructors for indices and variables to be
    coercions.  That way, if Coq sees a [nat] where it expects an
    [exp], it will implicitly insert an application of [bvar]; and
    similarly for [atom]s.

    For example, we can encode the expression (\x:b. Y x) as below.
    Because "Y" is free variable in this term, we need to assume an
    atom for this name.
*)

Parameter Y : atom.
Definition demo_rep1 := abs typ_base (app Y 0).

(** Note that because of the coercions we may write [abs (app Y 0)]
    instead of [abs (app (fvar Y) (bvar 0))].

    Below is another example: the encoding of (\x:b. \y:b. (y x)).
*)

Definition demo_rep2 := abs typ_base (abs typ_base (app 0 1)).


(** Exercise: Uncomment and then complete the definitions of the following
	 lambda calculus terms using the locally nameless representation.

       "two"     :    \s:b->b. \z:b. s (s z)

       "COMB_K"  :    \x:b. \y:b. x

       "COMB_S"  :    \x:b -> b -> b.\y:b -> b.\z:b. x z (y z)

*)


Definition two :=
  (* SOLUTION *)
  abs (typ_arrow typ_base typ_base)
                      (abs typ_base (app 1 (app 1 0))).

Definition COMB_K :=
  (* SOLUTION *)
	abs typ_base
    (abs typ_base 1).

Definition COMB_S :=
   (* SOLUTION *)
   abs (typ_arrow typ_base (typ_arrow typ_base typ_base))
    (abs (typ_arrow typ_base typ_base)
      (abs (typ_base)
        (app (app 2 0) (app 1 0)))).


(** There are two important advantages of the locally nameless
    representation:
     - Alpha-equivalent terms have a unique representation.
       We're always working up to alpha-equivalence.
     - Operations such as free variable substitution and free
       variable calculation have simple recursive definitions
       (and therefore are simple to reason about).

    Weighed against these advantages are two drawbacks:
     - The [exp] datatype admits terms, such as [abs 3], where
       indices are unbound.
       A term is called "locally closed" when it contains
       no unbound indices.
     - We must define *both* bound variable & free variable
       substitution and reason about how these operations
       interact with each other.
*)


(*************************************************************************)
(** * Substitution *)
(*************************************************************************)

(** Substitution replaces a free variable with a term.  The definition
    below is simple for two reasons:
      - Because bound variables are represented using indices, there
        is no need to worry about variable capture.
      - We assume that the term being substituted in is locally
        closed.  Thus, there is no need to shift indices when
        passing under a binder.
*)

Fixpoint subst (z : atom) (u : exp) (e : exp)
  {struct e} : exp :=
  match e with
    | bvar i => bvar i
    | fvar x => if x == z then u else (fvar x)
    | abs t e1 => abs t (subst z u e1)
    | app e1 e2 => app (subst z u e1) (subst z u e2)
  end.

(** The [Fixpoint] keyword defines a Coq function.  As all functions
    in Coq must be total.  The annotation [{struct e}] indicates the
    termination metric---all recursive calls in this definition are
    made to arguments that are structurally smaller than [e].

    Note also that subst uses the notation [x == z] for decidable atom
    equality.  This notation is defined in the Metatheory library.

    We define a notation for free variable substitution that mimics
    standard mathematical notation.
*)

Notation "[ z ~> u ] e" := (subst z u e) (at level 68).


(** To demonstrate how free variable substitution works, we need to
    reason about atom equality.
*)

Parameter Z : atom.
(* Check (Y == Z). *)

(** The decidable atom equality function returns a sum. If the two
    atoms are equal, the left branch of the sum is returned, carrying
    a proof of the proposition that the atoms are equal.  If they are
    not equal, the right branch includes a proof of the disequality.

    The demo below uses three new tactics:
    - The tactic [simpl] reduces a Coq expression to its normal
      form.
    - The tactic [destruct (Y==Y)] considers the two possible
      results of the equality test.
    - The tactic [Case] marks cases in the proof script.
      It takes any string as its argument, and puts that string in
      the hypothesis list until the case is finished.
*)

Lemma demo_subst1:
  [Y ~> Z] (abs typ_base (app 0 Y)) = (abs typ_base (app 0 Z)).
Proof.
  simpl.
  destruct (Y==Y).
  Case "left".
    auto.
  Case "right".
    destruct n. auto.
Qed.

(** Take-home Exercise: We can use almost the same proof script as
    above to state how substitution works in the variable case. Try it
    on your own.  *)

Lemma subst_eq_var: forall (x : atom) u,
  [x ~> u]x = u.
Proof.
  (* SOLUTION *)
  intros x u.
  simpl.
  destruct (x == x).
  Case "left".
    auto.
  Case "right".
    destruct n. auto.
Qed.

Lemma subst_neq_var : forall (x y : atom) u,
  y <> x -> [x ~> u]y = y.
Proof.
  (* SOLUTION *)
  intros x y u.
  simpl.
  intro Neq.
  destruct (y == x).
  Case "left".
    destruct Neq. auto.
  Case "right".
    auto.
Qed.


(*************************************************************************)
(** * Free variables *)
(*************************************************************************)

(** The function [fv], defined below, calculates the set of free
    variables in an expression.  Because we are using a locally
    nameless representation, where bound variables are represented as
    indices, any name we see is a free variable of a term.  In
    particular, this makes the [abs] case simple.
*)

Fixpoint fv (e : exp) {struct e} : atoms :=
  match e with
    | bvar i => empty
    | fvar x => singleton x
    | abs t e1 => fv e1
    | app e1 e2 => (fv e1) `union` (fv e2)
  end.

(** The type [atoms] represents a finite set of elements of type
    [atom].  The notation for infix union is defined in the Metatheory
    library.
*)

(* Demo [f_equal]

  The tactic [f_equal] converts a goal of the form [f e1 = f e1'] in
  to one of the form [e1 = e1'], and similarly for [f e1 e2 = f e1'
  e2'], etc.
*)
Lemma f_equal_demo : forall e1 e2, e1 = e2 -> fv e1 = fv e2.
Proof.
  intros e1 e2 EQ.
  f_equal.
  assumption.
Qed.

(* Demo [fsetdec]

   The tactic [fsetdec] solves a certain class of propositions
   involving finite sets. See the documentation in [FSetWeakDecide]
   for a full specification.
*)

Lemma fsetdec_demo : forall (x :atom) (S : atoms),
  x `in` (singleton x `union` S).
Proof.
  fsetdec.
Qed.

(** Exercise [subst_fresh]
    To show the ease of reasoning with these definitions, we will prove a
    standard result from lambda calculus: if a variable does not
    appear free in a term, then substituting for it has no effect.

    HINTS: Prove this lemma by induction on [e].

    - You will need to use [simpl] in many cases.  You can [simpl]
      everything everywhere (including hypotheses) with the
      pattern [simpl in *].

    - Part of this proof includes a false assumption about free
      variables.  Destructing this hypothesis produces a goal about
      finite set membership that is solvable by [fsetdec].
*)

Lemma subst_fresh : forall (x : atom) e u,
  x `notin` fv e -> [x ~> u] e = e.
Proof.
  (* SOLUTION *)
  intros x e u H.
  induction e.
  Case "bvar".
    auto.
  Case "fvar".
    simpl.
    destruct (a == x).
    SCase "a=x".
      subst. simpl fv in H. fsetdec.
    SCase "a<>x".
      auto.
  Case "abs".
    simpl.
    f_equal.
    auto.
  Case "app".
    simpl in *.
    f_equal.
    auto.
    auto.
Qed.

(* Take-home Demo: Prove that free variables are not introduced by
   substitution.

   This proof actually is very automatable ([simpl in *; auto.] takes
   care of all but the fvar case), but the explicit proof below
   demonstrates two parts of the finite set library. These two parts
   are the tactic [destruct_notin] and the lemma [notin_union], both
   defined in the module [FSetWeakNotin].

   Before stepping through this proof, you should go to that module
   to read about those definitions and see what other finite set
   reasoning is available.

  *)
Lemma subst_notin_fv : forall x y u e,
   x `notin` fv e -> x `notin` fv u ->
   x `notin` fv ([y ~> u]e).
Proof.
  intros x y u e Fr1 Fr2.
  induction e; simpl in *.
  Case "bvar".
    assumption.
  Case "fvar".
    destruct (a == y).
      assumption.
      simpl. assumption.
  Case "abs".
    apply IHe. assumption.
  Case "app".
    destruct_notin.
    apply notin_union.
    apply IHe1.
    assumption.
    apply IHe2.
    assumption.
Qed.


(*************************************************************************)
(** * Opening *)
(*************************************************************************)

(** Opening replaces an index with a term.  It corresponds to informal
    substitution for a bound variable, such as in the rule for beta
    reduction.  Note that only "dangling" indices (those that do not
    refer to any abstraction) can be opened.  Opening has no effect
    for terms that are locally closed.

    Natural numbers are just an inductive datatype with two
    constructors: [O] (as in the letter 'oh', not 'zero') and [S],
    defined in Coq.Init.Datatypes.  Coq allows literal natural numbers
    to be written using standard decimal notation, e.g., 0, 1, 2, etc.
    The notation [k == i] is the decidable equality function for
    natural numbers (cf. [Coq.Peano_dec.eq_nat_dec]).  This notation
    is defined in the Metatheory library.

    We make several simplifying assumptions in defining [open_rec].

    First, we assume that the argument [u] is locally closed.  This
    assumption simplifies the implementation since we do not need to
    shift indices in [u] when passing under a binder.  Second, we
    assume that this function is initially called with index zero and
    that zero is the only unbound index in the term.  This eliminates
    the need to possibly subtract one in the case of indices.

    There is no need to worry about variable capture because bound
    variables are indices.
*)

Fixpoint open_rec (k : nat) (u : exp)(e : exp)
  {struct e} : exp :=
  match e with
    | bvar i => if k == i then u else (bvar i)
    | fvar x => fvar x
    | abs t e1 => abs t (open_rec (S k) u e1)
    | app e1 e2 => app (open_rec k u e1) (open_rec k u e2)
  end.

(** Many common applications of opening replace index zero with an
    expression or variable.  The following definition provides a
    convenient shorthand for such uses.  Note that the order of
    arguments is switched relative to the definition above.  For
    example, [(open e x)] can be read as "substitute the variable [x]
    for index [0] in [e]" and "open [e] with the variable [x]."
    Recall that the coercions above let us write [x] in place of
    [(fvar x)].
*)

Definition open e u := open_rec 0 u e.


(** This next demo shows the operation of [open].  For example, the
    locally nameless representation of the term (\y. (\x. (y x)) y) is
    [abs (app (abs (app 1 0)) 0)].  To look at the body without the
    outer abstraction, we need to replace the indices that refer to
    that abstraction with a name.  Therefore, we show that we can open
    the body of the abs above with Y to produce [app (abs (app Y 0))
    Y)].
*)

Lemma demo_open :
  open (app (abs typ_base (app 1 0)) 0) Y =
       (app (abs typ_base (app Y 0)) Y).
Proof.
  unfold open.
  unfold open_rec.
  simpl.
  auto.
Qed.

(* HINT for demo: To show the equality of the two sides below, use the
   tactics [unfold], which replaces a definition with its RHS and
   reduces it to head form, and [simpl], which reduces the term the
   rest of the way.  Then finish up with [auto].  *)


(*************************************************************************)
(*                                                                       *)
(*  Stretch break (5 mins)                                               *)
(*                                                                       *)
(*************************************************************************)


(*************************************************************************)
(** * Local closure *)
(*************************************************************************)

(** Recall that [exp] admits terms that contain unbound indices.  We
    say that a term is locally closed when no indices appearing in it
    are unbound.  The proposition [lc e] holds when an expression [e]
    is locally closed.

    The inductive definition below formalizes local closure such that
    the resulting induction principle serves as the structural
    induction principle over (locally closed) expressions.  In
    particular, unlike induction for type [exp], there are no cases
    for bound variables.  Thus, the induction principle corresponds
    more closely to informal practice than the one arising from the
    definition of pre-terms.
*)

Inductive lc : exp -> Prop :=
  | lc_var : forall (x:atom),
      lc x
  | lc_abs : forall (x : atom) e t,
      x `notin` fv e -> lc (open e x) ->
      lc (abs t e)
  | lc_app : forall e1 e2,
      lc e1 -> lc e2 ->
      lc (app e1 e2).

Hint Constructors lc.


(*************************************************************************)
(** Properties about basic operations *)
(*************************************************************************)

(** We also define a notation for [open_rec] to make stating some of
    the properties simpler. However, we don't need to use open_rec
    outside of this part of the tutorial so we make it a local
    notation, confined to this section. *)

Section BasicOperations.
Local Notation "{ k ~> u } t" := (open_rec k u t) (at level 67).

(** The first property we would like to show is the analogue to
    [subst_fresh]: index substitution has no effect for closed terms.

    Here is an initial attempt at the proof.
*)

Lemma open_rec_lc_0 : forall k u e,
  lc e ->
  e = {k ~> u} e.
Proof.
  intros k u e LC.
  induction LC.
  Case "lc_fvar".
    simpl.
    auto.
  Case "lc_abs".
    simpl.
    f_equal.
Admitted.

(** At this point there are two problems.  Our goal is about
    substitution for index [S k] in term [e], while our induction
    hypothesis IHLC only tells use about index [k] in term [open e x].

    To solve the first problem, we generalize our IH over all [k].
    That way, when [k] is incremented in the [abs] case, it will still
    apply.  Below, we use the tactic [generalize dependent] to
    generalize over [k] before using induction.
*)

Lemma open_rec_lc_1 : forall k u e,
  lc e ->
  e = {k ~> u} e.
Proof.
  intros k u e LC.
  generalize dependent k.
  induction LC.
  Case "lc_fvar".
    simpl. auto.
  Case "lc_abs".
    simpl.
    intro k.
    f_equal.
Admitted.

(** At this point we are still stuck because the IH concerns
    [open e x] instead of [e]. The result that we need is that if an
    index substitution has no effect for an opened term, then it has
    no effect for the raw term (as long as we are *not* substituting
    for [0], hence [S k] below).
<<
   open e x = {S k ~> u}(open e x)  -> e = {S k ~> u} e
>>
   In other words, expanding the definition of open:
<<
   {0 ~> x}e = {S k ~> u}({0 ~> x} e)  -> e = {S k ~> u} e
>>
   Of course, to prove this result, we must generalize
   [0] and [S k] to be any pair of inequal numbers to get a strong
   enough induction hypothesis for the [abs] case.
 *)

Lemma open_rec_lc_core : forall e j v i u,
  i <> j ->
  {j ~> v} e = {i ~> u} ({j ~> v} e) ->
  e = {i ~> u} e.
Proof.
  induction e; intros j v i u Neq H; simpl in *.
  Case "bvar".
    destruct (j == n);  destruct (i == n).
      SCase "j = n = i".
        subst n. destruct Neq. auto.
      SCase "j = n, i <> n".
        auto.
      SCase "j <> n, i = n".
        subst n. simpl in H.
        destruct (i == i).
           SSCase "i=i".
             auto.
           SSCase "i<>i".
             destruct n. auto.
      SCase "j <> n, i <> n".
        auto.
  Case "fvar".
    auto.
  Case "abs".
    f_equal.
    inversion H.
    apply  IHe with (j := S j) (u := u) (i := S i) (v := v).
    auto.
    auto.
  Case "app".
    inversion H.
    f_equal.
    eapply IHe1; eauto.
    eapply IHe2; eauto.
Qed.

(* Take-home Exercise: We've proven the above lemma very explicitly,
   so that you can step through it slowly to see how it
   works. However, with automation, it is possible to give a *much*
   shorter proof. Reprove this lemma on your own to see how compact
   you can make it. *)

(* SOLUTION *)
Lemma open_rec_lc_core_automated : forall e j v i u,
  i <> j ->
  {j ~> v} e = {i ~> u} ({j ~> v} e) ->
  e = {i ~> u} e.
Proof with try solve [eauto | congruence].
  induction e; intros j v i u Neq H; simpl in *;
      try solve [inversion H; f_equal; eauto].
  Case "bvar".
    destruct (j == n)...
    destruct (i == n)...
Qed.


(** With the help of this lemma, we can complete the proof. *)

Lemma open_rec_lc : forall k u e,
  lc e -> e = {k ~> u} e.
Proof.
  intros k u e LC.
  generalize dependent k.
  induction LC.
  Case "lc_fvar".
    simpl.
    auto.
  Case "lc_abs".
    simpl.
    intro k.
    f_equal.
    unfold open in *.
    apply open_rec_lc_core with
      (i := S k) (j := 0) (u := u) (v := fvar x).
    auto.
    auto.
  Case "lc_app".
    intro k.
    simpl.
    f_equal.
    auto.
    auto.
Qed.


(** Take-home Exercise [subst_open_rec] *)

(** The next lemma demonstrates that free variable substitution
    distributes over index substitution.

    The proof of this lemma is by straightforward induction over
    [e1]. When [e1] is a free variable, we need to appeal to
    [open_rec_lc], proved above.
*)

Lemma subst_open_rec : forall e1 e2 u (x : atom) k,
  lc u ->
  [x ~> u] ({k ~> e2} e1) = {k ~> [x ~> u] e2} ([x ~> u] e1).
Proof.
  (* SOLUTION *)
  induction e1; intros e2 u x k H; simpl in *; f_equal; auto.
  Case "bvar".
    destruct (k == n); auto.
  Case "fvar".
    destruct (a == x); subst; auto.
    apply open_rec_lc; auto.
Qed.


(** *** Exercise [subst_open_var] *)

(** The lemma above is most often used with [k = 0] and
    [e2] as some fresh variable. Therefore, it simplifies matters
    to define the following useful corollary.

    HINT: Do not use induction.
    Rewrite with [subst_open_rec] and [subst_neq_var].

*)

Lemma subst_open_var : forall (x y : atom) u e,
  y <> x ->
  lc u ->
  open ([x ~> u] e) y = [x ~> u] (open e y).
Proof.
  (* SOLUTION *)
  intros x y u e Neq H.
  unfold open.
  rewrite subst_open_rec with (e2 := fvar y); auto.
  rewrite subst_neq_var; auto.
Qed.

(** *** Take-home Exercise [subst_intro] *)

(** This lemma states that opening can be replaced with variable
    opening and substitution.

    HINT: Prove by induction on [e], first generalizing the
    argument to [open_rec] by using the [generalize] tactic, e.g.,
    [generalize 0].

*)

Lemma subst_intro : forall (x : atom) u e,
  x `notin` (fv e) ->
  open e u = [x ~> u](open e x).
Proof.
  (* SOLUTION *)
  intros x u e FV.
  unfold open.
  generalize 0.
  induction e; intro n0; simpl.
  Case "bvar".
    destruct (n0 == n).
    rewrite subst_eq_var. auto.
    simpl. auto.
  Case "fvar".
    destruct (a == x). subst. simpl in FV. fsetdec. auto.
  Case "abs".
    f_equal. simpl in FV. apply IHe. auto.
  Case "app".
    simpl in FV.
    f_equal.
    apply IHe1. auto.
    apply IHe2. auto.
Qed.

End BasicOperations.


(*************************************************************************)
(** Cofinite quantification *)
(*************************************************************************)

(* In the next example, we will reexamine the definition of
   [lc] in the [abs] case.

   The lemma [subst_lc] says that local closure is preserved by
   substitution.  Let's start working through this proof.
*)

Lemma subst_lc_0 : forall (x : atom) u e,
  lc e ->
  lc u ->
  lc ([x ~> u] e).
Proof.
  intros x u e He Hu.
  induction He.
  Case "lc_fvar".
    simpl.
    destruct (x0 == x).
      auto.
      auto.
  Case "lc_abs".
    simpl.
    (* Print lc_abs. *)
    apply lc_abs with (x:=x0).
    apply subst_notin_fv.
    auto.
Admitted.

(** Here we are stuck. We don't know that [x0] is not in the free
    variables of [u].

    The solution is to change the *definition* of local closure so
    that we get a different induction principle.  Currently, in the
    [lc_abs] case, we show that an abstraction is locally closed by
    showing that the body is locally closed after it has been opened
    with one particular variable.

<<
  | lc_abs : forall (x : atom) e,
      x `notin` fv e ->
      lc (open e x) ->
      lc (abs e)
>>

    Therefore, our induction hypothesis in this case only applies to
    that variable. From the hypothesis list in the [lc_abs] case:

      x0 : atom,
      IHHe : lc ([x ~> u]open e x0)

    The problem is that we don't have any assumptions about [x0]. It
    could very well be equal to [x].

    A stronger induction principle provides an IH that applies to many
    variables. In that case, we could pick one that is "fresh enough".
    To do so, we need to revise the above definition of lc and replace
    the type of lc_abs with this one:

<<
  | lc_abs_c : forall L e,
      (forall x:atom, x `notin` L -> lc (open e x)) ->
      lc (abs e)
>>

   This rule says that to show that an abstraction is locally closed,
   we need to show that the body is closed, after it has been opened by
   any atom [x], *except* those in some set [L]. With this rule, the IH
   in this proof is now:

     H0 : forall x0 : atom, x0 `notin` L -> lc ([x ~> u]open e x0)

   Below, lc_c is the local closure judgment revised to use this new
   rule in the abs case. We call this "cofinite quantification"
   because the IH applies to an infinite number of atoms [x0], except
   those in some finite set [L].

   Changing the rule in this way does not change what terms are locally
   closed.  (For more details about cofinite-quantification see:
   "Engineering Formal Metatheory", Aydemir, Chargu'eraud, Pierce,
   Pollack, Weirich. POPL 2008.)

*)

Inductive lc_c : exp -> Prop :=
  | lc_var_c : forall (x:atom),
      lc_c x
  | lc_abs_c : forall (L : atoms) e T,
      (forall x : atom, x `notin` L -> lc_c (open e x)) ->
      lc_c (abs T e)
  | lc_app_c : forall e1 e2,
      lc_c e1 ->
      lc_c e2 ->
      lc_c (app e1 e2).

Hint Constructors lc_c.

(* Reintroduce notation for [open_rec] so that we can reprove
   properties about it and the new version of lc_c. *)

Section CofiniteQuantification.
Local Notation "{ k ~> u } t" := (open_rec k u t) (at level 67).

(* With this new definition, we can almost use the same proof for
   [open_rec_lc], we only need one change. We need to add the line
   [pick fresh x for L.]  immediately before the use of [apply
   open_rec_lc_core].  This tactic, defined in [Metatheory],
   introduces a new atom [x] that is known not to be in the set [L].
*)

Lemma open_rec_lc_c : forall k u e,
  lc_c e ->
  e = {k ~> u} e.
Proof.
  intros k u e LC.
  generalize dependent k.
  induction LC.
  Case "lc_fvar".
    simpl.
    auto.
  Case "lc_abs".
    simpl.
    intro k.
    f_equal.
    unfold open in *.
    pick fresh x for L.  (* Note: NEW LINE added *)
    apply open_rec_lc_core with
      (i := S k) (j := 0) (u := u) (v := fvar x).
    auto.
    auto.
  Case "lc_app".
    intro k.
    simpl.
    f_equal.
    auto.
    auto.
Qed.

(* Take-home Exercise: The next two lemmas have exactly the same
   proofs as before. *)

Lemma subst_open_rec_c : forall e1 e2 u (x : atom) k,
  lc_c u ->
  [x ~> u] ({k ~> e2} e1) = {k ~> [x ~> u] e2} ([x ~> u] e1).
Proof.
(* SOLUTION *)
  induction e1; intros e2 u x k H; simpl in *; f_equal; auto.
  Case "bvar".
    destruct (k == n); auto.
  Case "fvar".
    destruct (a == x); subst; auto.
    apply open_rec_lc_c; auto.
Qed.

Lemma subst_open_var_c : forall (x y : atom) u e,
  y <> x ->
  lc_c u ->
  open ([x ~> u] e) y = [x ~> u] (open e y).
Proof.
  (* SOLUTION *)
  intros x y u e Neq H.
  unfold open.
  rewrite subst_open_rec_c with (e2 := fvar y); auto.
  rewrite subst_neq_var; auto.
Qed.

(* Exercise [subst_lc_c]:

   Once we have changed the definition of lc, we can complete the
   proof of subst_lc.

    HINT: apply lc_abs_c with cofinite set (L `union` singleton x).
    This gives us an atom x0, and a hypothesis that
    x0 is fresh for both L and x.
*)

Lemma subst_lc_c : forall (x : atom) u e,
  lc_c e ->
  lc_c u ->
  lc_c ([x ~> u] e).
Proof.
  intros x u e He Hu.
  induction He.
  Case "lc_var_c".
   simpl.
   destruct (x0 == x).
     auto.
     auto.
  Case "lc_abs_c".
    simpl.
    (* SOLUTION *)
    apply lc_abs_c with (L := L `union` singleton x).
    intros x0 Fr.
    rewrite subst_open_var_c. auto. auto. auto.
  Case "lc_app_c".
     simpl. auto.
Qed.

End CofiniteQuantification.


(*************************************************************************)
(** * Tactic support *)
(*************************************************************************)

(** When picking a fresh atom or applying a rule that uses cofinite
    quantification, choosing a set of atoms to be fresh for can be
    tedious.  In practice, it is simpler to use a tactic to choose the
    set to be as large as possible.

    The tactic [gather_atoms] is used to collect together all the
    atoms in the context.  It relies on an auxiliary tactic,
    [gather_atoms_with] (from MetatheoryAtom), which maps a function
    that returns a finite set of atoms over all hypotheses with the
    appropriate type.
*)

Ltac gather_atoms ::=
  let A := gather_atoms_with (fun x : atoms => x) in
  let B := gather_atoms_with (fun x : atom => singleton x) in
  let C := gather_atoms_with (fun x : list (atom * typ) => dom x) in
  let D := gather_atoms_with (fun x : exp => fv x) in
  constr:(A `union` B `union` C `union` D).

(** A number of other, useful tactics are defined by the Metatheory
    library, and each depends on [gather_atoms].  By redefining
    [gather_atoms], denoted by the [::=] in its definition below, we
    automatically update these tactics so that they use the proper
    notion of "all atoms in the context."

    For example, the tactic [(pick fresh x)] chooses an atom fresh for
    "everything" in the context.  It is the same as [(pick fresh x for
    L)], except where [L] has been computed by [gather_atoms].

    The tactic [(pick fresh x and apply H)] applies a rule [H] that is
    defined using cofinite quantification.  It automatically
    instantiates the finite set of atoms to exclude using
    [gather_atoms].
*)


(** *** Example

    Below, we reprove [subst_lc_c] using [(pick fresh and apply)].
    Step through the proof below to see how [(pick fresh and apply)]
    works.
*)

Lemma subst_lc_c_alternate_proof : forall (x : atom) u e,
  lc_c e ->
  lc_c u ->
  lc_c ([x ~> u] e).
Proof.
  intros x u e He Hu.
  induction He.
  Case "fvar".
   simpl.
   destruct (x0 == x).
     auto.
     auto.
  Case "abs".
    simpl.
    pick fresh y and apply lc_abs_c.
    (* Here, take note of the hypothesis [Fr]. *)
    rewrite subst_open_var_c. auto. auto. auto.
  Case "app".
     simpl. auto.
Qed.


(*************************************************************************)
(*                                                                       *)
(*  Coffee break                                                         *)
(*                                                                       *)
(*************************************************************************)


(*************************************************************************)
(** * Typing environments *)
(*************************************************************************)

(** We represent environments as association lists (lists of pairs of
    keys and values) whose keys are [atom]s.
*)

Notation env := (list (atom * typ)).

(** For STLC, environments bind [atom]s to [typ]s.  We define an
    abbreviation [env] for the type of these environments.  Coq will
    print [list (atom * typ)] as [env], and we can use [env] as a
    shorthand for writing [list (atom * typ)].

    Lists are defined in Coq's standard library, with the constructors
    [nil] and [cons].  The list library includes the [::] notation
    for cons as well as standard list operations such as append, map,
    and fold. The infix operation "++" is list append.

    The Metatheory library extends this reasoning by instantiating the
    AssocList library to provide support for association lists whose
    keys are [atom]s.  Everything in this library is polymorphic over
    the type of objects bound in the environment.  Look in AssocList
    for additional details about the functions and predicates that we
    mention below.
*)

(** Environment equality *)

(** When reasoning about environments, we often need to talk about
    bindings in the "middle" of an environment. Therefore, it is common
    for lemmas and definitions to use list append in their statements.
    Unfortunately, list append is associative, so two Coq expressions may
    denote the same environment even though they are not equal.

    The tactic [simpl_env] reassociates all concatenations of
    environments to the right.
*)

Lemma append_assoc_demo : forall (E0 E1 E2 E3:env),
  E0 ++ (E1 ++ E2) ++ E3 = E0 ++ E1 ++ E2 ++ E3.
Proof.
  intros.
  auto. (* Does nothing. *)
  simpl_env.
  reflexivity.
Qed.

(** To make environments easy to read, instead of building them from
    [nil] and [cons], we prefer to build them from the following
    components:
      - [nil]: The empty list.
      - [one]: Lists consisting of exactly one item.
      - [++]:  List append.

   Furthermore, we introduce compact notation for one (singleton lists):
   [(x ~ T)] is the same as [one (x, T)].
*)

(** The simpl_env tactic actually puts lists built from only nil, one
    and [++] into a "normal form". This process reassociates all appends
    to the right, removes extraneous nils converts cons to singleton
    lists with an append.
*)

Lemma simpl_env_demo : forall (x y:atom) (T1 T2:typ) (E F:env),
   ((x ~ T1) ++ nil) ++ (y,T2) :: (nil ++ E) ++ F =
   (x ~ T1) ++ (y ~ T2) ++ E ++ F.
Proof.
   intros.
   (* simpl_env puts the left side into the normal form. *)
   simpl_env.
   reflexivity.
Qed.

(** Note that the [simpl] tactic doesn't produce the "normal form" for
    environments. It should always be followed up with [simpl_env].

    Furthermore, to convert an environment to any equivalent form
    other than the normal form (perhaps to apply a lemma) use the
    tactic [rewrite_env].
*)

Lemma rewrite_env_demo : forall (x y:atom) (T:typ) P,
  (forall E, P ((x,T):: E) -> True) ->
  P (x ~ T) ->
  True.
Proof.
  intros x y T P H.
  (* apply H. fails here. *)
  rewrite_env ((x,T) :: nil).
  apply H.
Qed.

(** Environment operations. *)

(** The ternary predicate [binds] holds when a given binding is
    present somewhere in an environment.
*)

Lemma binds_demo : forall (x:atom) (T:typ) (E F:env),
  binds x T (E ++ (x ~ T) ++ F).
Proof.
  auto.
Qed.

(** The function [dom] computes the domain of an environment,
    returning a finite set of [atom]s. Note that we cannot use Coq's
    equality for finite sets, we must instead use a defined relation
    [=] for atom set equality.
 *)

Lemma dom_demo : forall (x y : atom) (T : typ),
  dom (x ~ T) [=] singleton x.
Proof.
  auto.
Qed.

(** The unary predicate [uniq] holds when each atom is bound at most
    once in an environment.
*)

Lemma uniq_demo : forall (x y : atom) (T : typ),
  x <> y -> uniq ((x ~ T) ++ (y ~ T)).
Proof.
  auto.
Qed.


(*************************************************************************)
(** * Typing relation *)
(*************************************************************************)

(** The definition of the typing relation is straightforward.  In
    order to ensure that the relation holds for only well-formed
    environments, we check in the [typing_var] case that the
    environment is [uniq].  The structure of typing derivations
    implicitly ensures that the relation holds only for locally closed
    expressions.  Finally, note the use of cofinite quantification in
    the [typing_abs] case.
*)

Inductive typing_c : env -> exp -> typ -> Prop :=
  | typing_var_c : forall E (x : atom) T,
      uniq E ->
      binds x T E ->
      typing_c E (fvar x) T
  | typing_abs_c : forall (L : atoms) E e T1 T2,
      (forall (x:atom), x `notin` L ->
        typing_c ((x ~ T1) ++ E) (open e x) T2) ->
      typing_c E (abs T1 e) (typ_arrow T1 T2)
  | typing_app_c : forall E e1 e2 T1 T2,
      typing_c E e1 (typ_arrow T1 T2) ->
      typing_c E e2 T1 ->
      typing_c E (app e1 e2) T2.

(** We add the constructors of the typing relation as hints to be used
    by the [auto] and [eauto] tactics.
*)

Hint Constructors typing_c.


(*************************************************************************)
(** * Weakening *)
(*************************************************************************)

(** Weakening states that if an expression is typeable in some
    environment, then it is typeable in any well-formed extension of
    that environment.  This property is needed to prove the
    substitution lemma.

    As stated below, this lemma is not directly proveable.  The
    natural way to try proving this lemma proceeds by induction on the
    typing derivation for [e].
*)

Lemma typing_weakening_0 : forall E F e T,
  typing_c E e T ->
  uniq (F ++ E) ->
  typing_c (F ++ E) e T.
Proof.
  intros E F e T H J.
  induction H; eauto.
  Case "typing_abs_c".
    pick fresh x and apply typing_abs_c.
    (* ... stuck here ... *)
Admitted.

(** We are stuck in the [typing_abs_c] case because the induction
    hypothesis [H0] applies only when we weaken the environment at its
    head.  In this case, however, we need to weaken the environment in
    the middle; compare the conclusion at the point where we're stuck
    to the hypothesis [H], which comes from the given typing derivation.

    We can obtain a more useful induction hypothesis by changing the
    statement to insert new bindings into the middle of the
    environment, instead of at the head.  However, the proof still
    gets stuck, as can be seen by examining each of the cases in
    the proof below.

    Note: To view subgoal n in a proof, use the command "[Show n]".
    To work on subgoal n instead of the first one, use the command
    "[Focus n]".
*)

Lemma typing_weakening_strengthened_0 : forall (E F G : env) e T,
  typing_c (G ++ E) e T ->
  uniq (G ++ F ++ E) ->
  typing_c (G ++ F ++ E) e T.
Proof.
  intros E F G e T H J.
  induction H.
  Case "typing_var_c".
    (* The E0 looks strange in the [typing_var_c] case. *)
  Focus 2.
  Case "typing_abs_c".
    (* The [typing_abs_c] case still does not have a strong enough IH. *)
Admitted.

(** The hypotheses in the [typing_var_c] case include an environment
    [E0] that that has no relation to what we need to prove.  The
    missing fact we need is that [E0 = (G ++ E)].

    The problem here arises from the fact that Coq's [induction]
    tactic let's us only prove something about all typing derivations.
    While it's clear to us that weakening applies to all typing
    derivations, it's not clear to Coq, because the environment is
    written using concatenation.  The [induction] tactic expects that
    all arguments to a judgement are variables.  So we see [E0] in the
    proof instead of [(G ++ E)].

    The solution is to restate the lemma.  For example, we can prove

<<
  forall E F E' e T, typing_c E' e T ->
  forall G, E' = G ++ E -> uniq (G ++ F ++ E) -> typing_c (G ++ F ++ E) e T.
>>

    The equality gets around the problem with Coq's [induction]
    tactic.  The placement of the [(forall G)] quantifier gives us a
    sufficiently strong induction hypothesis in the [typing_abs_c] case.

    However, we prefer not to state the lemma in the way shown above,
    since it is not as readable as the original statement.  Instead,
    we use a tactic to introduce the equality within the proof itself.
    The tactic [(remember t as t')] replaces an object [t] with the
    identifier [t'] everywhere in the goal and introduces an equality
    [t' = t] into the context.  It is often combined with [generalize
    dependent], as illustrated below.
*)


(** *** Exercise

    See how we use [remember as] in the proof below for weakening.
    Then, complete the proof below.

    HINTS:

       - The [typing_var_c] case follows from [binds_weaken], the
         weakening lemma for the [binds] relation.

       - The [typing_abs_c] case follows from the induction
         hypothesis, but the [apply] tactic may be unable to unify
         things as you might expect.

           -- Recall the [pick fresh and apply] tactic.

           -- In order to apply the induction hypothesis, use
              [rewrite_env] to reassociate the list operations.

           -- After applying the induction hypothesis, use
              [simpl_env] to use [uniq_push].

           -- Here, use [auto] to solve facts about finite sets of
              atoms, since it will simplify the [dom] function behind
              the scenes.  [fsetdec] does not work with the [dom]
              function.

       - The [typing_app_c] case follows directly from the induction
         hypotheses.
  *)

Lemma typing_c_weakening_strengthened :  forall (E F G : env) e T,
  typing_c (G ++ E) e T ->
  uniq (G ++ F ++ E) ->
  typing_c (G ++ F ++ E) e T.
Proof.
  intros E F G e T H.
  remember (G ++ E) as E'.
  generalize dependent G.
  induction H; intros G Eq Uniq; subst.
 (* SOLUTION *)
  Case "typing_var_c".
    apply typing_var_c.
      apply Uniq.
      apply binds_weaken. apply H0.
  Case "typing_abs_c".


    pick fresh x and apply typing_abs_c.
    rewrite_env (((x ~ T1) ++ G) ++ F ++ E).
    apply H0.
      auto.
      simpl_env. reflexivity.
      simpl_env. apply uniq_push.
        apply Uniq.
        auto.
  Case "typing_app_c".
    eapply typing_app_c.
      eapply IHtyping_c1. reflexivity. apply Uniq.
      eapply IHtyping_c2. reflexivity. apply Uniq.
Qed.


(** *** Example

    We can now prove our original statement of weakening.  The only
    interesting step is the use of the rewrite_env tactic.
*)

Lemma typing_c_weakening : forall (E F : env) e T,
    typing_c E e T ->
    uniq (F ++ E) ->
    typing_c (F ++ E) e T.
Proof.
  intros E F e T H J.
  rewrite_env (nil ++ F ++ E).
  apply typing_c_weakening_strengthened; auto.
Qed.


(*************************************************************************)
(** * Substitution *)
(*************************************************************************)

(** Having proved weakening, we can now prove the usual substitution
    lemma, which we state both in the form we need and in the
    strengthened form needed to make the proof go through.

<<
  typing_c_subst_simple : forall E e u S T z,
    typing_c ((z ~ S) ++ E) e T ->
    typing_c E u S ->
    typing_c E ([z ~> u] e) T

  typing_c_subst : forall E F e u S T z,
    typing_c (F ++ (z ~ S) ++ E) e T ->
    typing_c E u S ->
    typing_c (F ++ E) ([z ~> u] e) T
>>

    The proof of the strengthened statement proceeds by induction on
    the given typing derivation for [e].  The most involved case is
    the one for variables; the others follow from the induction
    hypotheses.
*)


(** *** Exercise

    Below, we state what needs to be proved in the [typing_var_c] case
    of the substitution lemma.  Fill in the proof.

    Proof sketch: The proof proceeds by a case analysis on [(x == z)],
    i.e., whether the two variables are the same or not.

      - If [(x = z)], then we need to show [(typing (F ++ E) u T)].
        This follows from the given typing derivation for [u] by
        weakening and the fact that [T] must equal [S].

      - If [(x <> z)], then we need to show [(typing (F ++ E) x T)].
        This follows by the typing rule for variables.

    HINTS: Lemmas [binds_mid_eq], [uniq_remove_mid],
    and [binds_remove_mid] are useful.

  *)

Lemma typing_subst_var_case : forall (E F : env) u S T (z x : atom),
  binds x T (F ++ (z ~ S) ++ E) ->
  uniq (F ++ (z ~ S) ++ E) ->
  typing_c E u S ->
  typing_c (F ++ E) ([z ~> u] x) T.
Proof.
  intros E F u S T z x H J K.
  simpl.
 (* SOLUTION *)
  destruct (x == z).
  Case "x = z".
    subst.
    assert (T = S).
      eapply binds_mid_eq. apply H. apply J.
    subst.
    apply typing_c_weakening.
      apply K.
      eapply uniq_remove_mid. apply J.
  Case "x <> z".
    apply typing_var_c.
      eapply uniq_remove_mid. apply J.
      eapply binds_remove_mid. apply H. apply n.
Qed.

(** *** Note

    The other two cases of the proof of the substitution lemma are
    relatively straightforward.  However, the case for [typing_abs_c]
    needs the fact that the typing relation holds only for
    locally-closed expressions.
*)

Lemma typing_c_to_lc_c : forall E e T,
  typing_c E e T -> lc_c e.
Proof.
  intros E e T H. induction H; eauto.
Qed.


(** *** Exercise

    Complete the proof of the substitution lemma. The proof proceeds
    by induction on the typing derivation for [e].  The initial steps
    should use [remember as] and [generalize dependent] in a manner
    similar to the proof of weakening.

   HINTS:
      - Use the lemma proved above for the [typing_var_c] case.

      - The [typing_abs_c] case follows from the induction hypothesis.
         -- Use [simpl] to simplify the substitution.

          -- Recall the tactic [pick fresh and apply].

          -- In order to use the induction hypothesis, use
             [subst_open_var_c] to push the substitution under the
             opening operation.

          -- Recall the lemma [typing_c_to_lc_c] and the
             [rewrite_env] and [simpl_env] tactics.

      - The [typing_app_c] case follows from the induction hypotheses.
        Use [simpl] to simplify the substitution.
*)

Lemma typing_c_subst : forall (E F : env) e u S T (z : atom),
  typing_c (F ++ (z ~ S) ++ E) e T ->
  typing_c E u S ->
  typing_c (F ++ E) ([z ~> u] e) T.
Proof.
(* SOLUTION *)
  intros E F e u S T z He Hu.
  remember (F ++ (z ~ S) ++ E) as E'.
  generalize dependent F.
  induction He.
  Case "typing_var_c".
    intros F Eq.
    subst.
    eapply typing_subst_var_case. apply H0. apply H. apply Hu.
  Case "typing_abs_c".
    intros F Eq.
    subst.
    simpl.


    pick fresh y and apply typing_abs_c.
    rewrite subst_open_var_c.
    rewrite_env (((y ~ T1) ++ F) ++ E).
    apply H0.
      auto.
      simpl_env. reflexivity.
    (* The following subgoals are from [rewrite subst_open_var]. *)
    auto.
    eapply typing_c_to_lc_c. apply Hu.
  Case "typing_app_c".
    intros F Eq. subst. simpl. eapply typing_app_c.
      apply IHHe1. reflexivity.
      apply IHHe2. reflexivity.
Qed.

(** *** Exercise

    Complete the proof of the substitution lemma stated in the form we
    need it.  The proof is similar to that of [typing_weakening].

    HINT: You'll need to use [rewrite_env] to prepend [nil],
    and [simpl_env] to simplify nil away.
*)

Lemma typing_c_subst_simple : forall (E : env) e u S T (z : atom),
  typing_c ((z ~ S) ++ E) e T ->
  typing_c E u S ->
  typing_c E ([z ~> u] e) T.
Proof.
(* SOLUTION *)
  intros E e u S T z H J.
  rewrite_env (nil ++ E).
  eapply typing_c_subst.
    simpl_env. apply H.
    apply J.
Qed.

(*************************************************************************)
(** * Values and Evaluation *)
(*************************************************************************)

(** In order to state the preservation lemma, we first need to define
    values and the small-step evaluation relation.  These inductive
    relations are straightforward to define.

    Note the hypotheses which ensure that the relations hold only for
    locally closed terms.  Below, we prove that this is actually the
    case, since it is not completely obvious from the definitions
    alone.
*)

Inductive value_c : exp -> Prop :=
  | value_abs_c : forall e T1,
      lc_c (abs T1 e) ->
      value_c (abs T1 e).

Inductive eval_c : exp -> exp -> Prop :=
  | eval_beta_c : forall e1 e2 T1,
      lc_c (abs T1 e1) ->
      value_c e2 ->
      eval_c (app (abs T1 e1) e2) (open e1 e2)
  | eval_app_1_c : forall e1 e1' e2,
      lc_c e2 ->
      eval_c e1 e1' ->
      eval_c (app e1 e2) (app e1' e2)
  | eval_app_2_c : forall e1 e2 e2',
      value_c e1 ->
      eval_c e2 e2' ->
      eval_c (app e1 e2) (app e1 e2').

(** We add the constructors for these two relations as hints to be used
    by Coq's [auto] and [eauto] tactics.
*)

Hint Constructors value_c eval_c.


(*************************************************************************)
(** * Preservation *)
(*************************************************************************)

(** *** Take-home Exercise

    Complete the proof of preservation.  In this proof, we proceed by
    induction on the given typing derivation.  The induction
    hypothesis has already been appropriately generalized by the given
    proof fragment.

    Proof sketch: By induction on the typing derivation for [e].

      - [typing_var_c] case: Variables don't step.

      - [typing_abs_c] case: Abstractions don't step.

      - [typing_app_c] case: By case analysis on how [e] steps. The
        [eval_beta] case is interesting, since it follows by the
        substitution lemma.  The others follow directly from the
        induction hypotheses.
*)

  (* HINTS:

       - Use [auto] and [eauto], especially with [;], to solve
         "uninteresting" subgoals.

       - Use [inversion] to perform case analyses and to rule out
         impossible cases.

       - In the [eval_beta] subcase of the [typing_app_c] case:

          -- Use [inversion] on a typing judgement to obtain a
             hypothesis about when the body of the abstraction is
             well-typed.

          -- Use [subst_intro] to rewrite the [open] operation into an
             [open] followed by a [subst].  You'll need to pick a
             fresh variable first.

  *)

Lemma preservation_c : forall (E : env) e e' T,
  typing_c E e T ->
  eval_c e e' ->
  typing_c E e' T.
Proof.
  intros E e e' T H.
  generalize dependent e'.
  induction H; intros e' J.
(* SOLUTION *)
  Case "typing_var_c".
    inversion J.
  Case "typing_abs_c".
    inversion J.
  Case "typing_app_c".
    inversion J; subst; eauto.
    SCase "eval_beta".
      inversion H; subst.
      pick fresh y.
      rewrite (subst_intro y); auto.
      eapply typing_c_subst_simple; auto.
Qed.

(*************************************************************************)
(** * Progress *)
(*************************************************************************)

(** *** Exercise

    Complete the proof of the progress lemma.  The induction
    hypothesis has already been appropriately generalized by the given
    proof fragment.

    Proof sketch: By induction on the typing derivation for [e].

      - [typing_var_c] case: Can't happen; the empty environment doesn't
        bind anything.

      - [typing_abs_c] case: Abstractions are values.

      - [typing_app_c] case: Applications reduce.  The result follows
        from an exhaustive case analysis on whether the two components
        of the application step or are values and the fact that a
        value must be an abstraction.
*)

  (* HINTS:

       - Use [auto] and [eauto], especially with [;], to solve
         "uninteresting" subgoals.

       - Use [inversion] to rule out impossible cases.

       - The lemma [typing_to_lc_c] will be useful for reasoning
         about local closure.

       - In the [typing_app_c] case:

          -- Use [destruct] to perform a case analysis on the
             conclusions of the induction hypotheses.

          -- Use [inversion] on a [value] judgement to determine that
             the value must be an abstraction.
  *)

Lemma progress_c : forall e T,
  typing_c nil e T ->
  value_c e \/ exists e', eval_c e e'.
Proof.
  intros e T H.

  (* It will be useful to have a "non-destructed" form of the given
     typing derivation, since [induction] takes apart the derivation
     it is called on. *)
  assert (typing_c nil e T); auto.

  (* [remember nil as E] fails here because [nil] takes an implicit
     argument that Coq is unable to infer.  By prefixing [nil] with
     [@], we can supply the argument to nil explicitly. *)
  remember (@nil (atom * typ)) as E.

  induction H; subst.

(* SOLUTION *)
  Case "typing_var_c".
    inversion H1.
  Case "typing_abs_c".
    left.
    apply value_abs_c.
    eapply typing_c_to_lc_c; eauto.
  Case "typing_app_c".
    right.
    destruct IHtyping_c1 as [V1 | [e1' Eval1]]; auto.
      SCase "e1 is a value".
      destruct IHtyping_c2 as [V2 | [e2' Eval2]]; auto.
        SSCase "e2 is a value".
          inversion V1; subst. exists (open e e2); auto.
        SSCase "e2 is not a value".
          exists (app e1 e2'); auto.
      SCase "e1 is not a value".
        exists (app e1' e2).
        apply eval_app_1_c.
          eapply typing_c_to_lc_c; eauto.
          assumption.
Qed.


(*************************************************************************)
(** * Renaming *)
(*************************************************************************)

(* Substitution and weakening together give us a property we call
   renaming: (see [typing_c_rename below] that we can change the name
   of the variable used to open an expression in a typing
   derivation. In practice, this means that if a variable is not
   "fresh enough" during a proof, we can use this lemma to rename it
   to one with additional freshness constraints.

   Renaming is used below to show the correspondence between the
   exists-fresh version of the rules with the cofinite version, and
   also to show that typechecking is decidable.
*)

(*
   However, before we prove renaming, we need an auxiliary lemma about
   typing judgments which says that terms are well-typed only in
   unique environments.
*)

Lemma typing_c_uniq : forall E e T,
  typing_c E e T -> uniq E.
Proof.
  intros E e T H.
  induction H; auto.
  Case "typing_abs_c".
    pick fresh x.
    assert (uniq ((x ~ T1) ++ E)); auto.
    inversion H1. auto.
Qed.

(*
   Demo: the proof of renaming.

   Note that this proof does not proceed by induction: even if we add
   new typing rules to the language, as long as the weakening and
   substution properties hold we can use this proof.
*)
Lemma typing_c_rename : forall (x y : atom) E e T1 T2,
  x `notin` fv e -> y `notin` (dom E `union` fv e) ->
  typing_c ((x ~ T1) ++ E) (open e x) T2 ->
  typing_c ((y ~ T1) ++ E) (open e y) T2.
Proof.
  intros x y E e T1 T2 Fr1 Fr2 H.
  destruct (x == y).
  Case "x = y".
    subst; eauto.
  Case "x <> y".
    assert (J : uniq ((x ~ T1) ++ E)).
      eapply typing_c_uniq; eauto.
    assert (J' : uniq E).
      inversion J; eauto.
    rewrite (@subst_intro x); eauto.
    rewrite_env (nil ++ (y ~ T1) ++ E).
    apply typing_c_subst with (S := T1).
    simpl_env.
    SCase "(open x s) is well-typed".
      apply typing_c_weakening_strengthened. eauto. auto.
    SCase "y is well-typed".
      eapply typing_var_c; eauto.
Qed.


(*************************************************************************)
(** * Exists-Fresh Definitions *)
(*************************************************************************)

(* The use of cofinite quantification may make some people worry that we
   are not formalizing the "right" language. Below, we show that
   the "exists-fresh" version of the rules is the same as the cofinite
   version. *)

(* First, we redefine the language with the exist-fresh version of the rules
   everywhere. *)
Inductive typing : env -> exp -> typ -> Prop :=
  | typing_var : forall E (x : atom) T,
      uniq E ->
      binds x T E ->
      typing E (fvar x) T
  | typing_abs : forall E e T1 T2 (x : atom),
      x `notin` fv e ->
      typing ((x ~ T1) ++ E) (open e x) T2 ->
      typing E (abs T1 e) (typ_arrow T1 T2)
  | typing_app : forall E e1 e2 T1 T2,
      typing E e1 (typ_arrow T1 T2) ->
      typing E e2 T1 ->
      typing E (app e1 e2) T2.

Inductive value : exp -> Prop :=
  | value_abs : forall e T1,
      lc (abs T1 e) ->
      value (abs T1 e).

Inductive eval : exp -> exp -> Prop :=
  | eval_beta : forall e1 e2 T1,
      lc (abs T1 e1) ->
      value e2 ->
      eval (app (abs T1 e1) e2) (open e1 e2)
  | eval_app_1 : forall e1 e1' e2,
      lc e2 ->
      eval e1 e1' ->
      eval (app e1 e2) (app e1' e2)
  | eval_app_2 : forall e1 e2 e2',
      value e1 ->
      eval e2 e2' ->
      eval (app e1 e2) (app e1 e2').

Hint Constructors typing value eval.

(*************************************************************************)
(** * Equivalence of Exists-Fresh and Cofinite Definitions *)
(*************************************************************************)

(* Next, we prove that these two definitions type the same
   terms. *)

(** First, we show that the two local closure predicates are equivalent.
    This lemma follows via a renaming lemma for lc_c. *)
Lemma lc_rename : forall e (x:atom) (y:atom),
  x `notin` fv e ->
  lc_c (open e x) -> lc_c (open e y).
Proof.
  intros e x y Frx LCx.
  rewrite (@subst_intro x); auto.
  apply subst_lc_c; auto.
Qed.

(* Demo: the next set of proofs are straightforward,
   so they are amenable to a fair amount of automation.
   Step through the demos, then follow the pattern
   in the take home exercises to practice with simple
   proof automation. *)
Lemma lc_to_lc_c : forall e, lc e -> lc_c e.
Proof.
  intros e LC.
  induction LC; auto.
  Case "lc_abs".
    apply lc_abs_c with (L := fv e).
    intros.
    apply lc_rename with (x := x); auto.
Qed.

(* Take-home exercise. *)
Lemma lc_c_to_lc : forall e, lc_c e -> lc e.
Proof.
(* SOLUTION *)
  intros e LCC. induction LCC; auto.
  Case "lc_abs_c".
     pick fresh x.
     apply lc_abs with (x:=x); auto.
Qed.

(** Correspondence of typing and typing_c *)

(* Demo. Again only the abs case is tricky. *)
Lemma typing_to_typing_c : forall E e T,
  typing E e T -> typing_c E e T.
Proof.
intros E e T H.
induction H; eauto.
Case "typing_abs".
  pick fresh y and apply typing_abs_c; auto.
  apply typing_c_rename with (x:=x); auto.
Qed.

(* Take-home exercise. *)
Lemma typing_c_to_typing : forall E e T,
  typing_c E e T -> typing E e T.
Proof.
(* SOLUTION *)
  intros E e T H.
  induction H; eauto.
  Case "typing_abs_c".
    pick fresh x.
    apply typing_abs with (x:=x); auto.
Qed.

(* Demo. The pattern [eauto using lemma] is a powerful way to completely
   automate all of the cases of a simple proof. *)
Lemma value_to_value_c : forall e,
  value e -> value_c e.
Proof.
  intros e H.
  induction H; eauto using lc_to_lc_c.
Qed.

(* Take-home exercise: Try to do the same for the following lemma. *)
Lemma value_c_to_value : forall e,
  value_c e -> value e.
Proof.
  (* SOLUTION *)
  intros e H.
  induction H; eauto using lc_c_to_lc.
Qed.

(* Demo: We can do the same trick with several lemmas. *)
Lemma eval_to_eval_c : forall e e',
  eval e e' -> eval_c e e'.
Proof.
  intros e e' H.
  induction H; eauto using lc_to_lc_c, value_to_value_c.
Qed.

(* Take-home exercise. *)
Lemma eval_c_to_eval : forall e e',
  eval_c e e' -> eval e e'.
Proof.
  (* SOLUTION *)
  intros e e' H.
  induction H; eauto using lc_c_to_lc, value_c_to_value.
Qed.

Lemma preservation : forall E e e' T,
  typing E e T ->
  eval e e' ->
  typing E e' T.
Proof.
  intros E e e' T HT HE.
  apply typing_c_to_typing.
  eapply preservation_c; eauto.
  eapply typing_to_typing_c. eauto.
  apply eval_to_eval_c. auto.
Qed.

Lemma progress : forall e T,
  typing nil e T ->
  value e \/ exists e', eval e e'.
Proof.
  intros e T HT.
  assert (typing_c nil e T).
  eapply typing_to_typing_c; auto.
  destruct (progress_c e T H) as [V | [e'' EV]].
  left. apply value_c_to_value. auto.
  right. exists e''. apply eval_c_to_eval. auto.
Qed.


(*************************************************************************)
(** * Regularity                                                         *)
(*************************************************************************)

(** To be fully confident about the exist-fresh rules, we can show their
   "regularity" --- that these relations only include locally closed
   terms. (For the exists-fresh definition of local closure.)
*)

(** Importantly: to prove regularity, we need to know subst_lc, and that
    we most directly prove by using the connection between lc and lc_c. *)
Lemma subst_lc : forall (x : atom) u e,
  lc e ->
  lc u ->
  lc ([x ~> u] e).
Proof.
eauto using lc_c_to_lc, subst_lc_c, lc_to_lc_c.
Qed.

(** Take-home exercise. [open_abs] is the analogue of subst_lc for bound variable
   substitution.
   HINT: use inversion, subst_intro and subst_lc to prove this lemma.
**)
Lemma open_abs : forall e u T1,
  lc (abs T1 e) ->
  lc u ->
  lc (open e u).
Proof.
  (* SOLUTION *)
  intros e u T1 H J.
  inversion H; subst; auto.
  rewrite (subst_intro x); auto.
  apply subst_lc; auto.
Qed.


(* Take-home exercise:

   Finally we can show that all of the relations only include locally-closed
   terms through very straightforward proofs. *)

Lemma value_to_lc : forall e,
  value e -> lc e.
Proof.
  (* SOLUTION *)
  intros e H. induction H; auto.
Qed.

Lemma eval_to_lc : forall e1 e2,
  eval e1 e2 -> lc e1 /\ lc e2.
Proof.
  (* SOLUTION *)
  intros e1 e2 H. induction H; try inversion IHeval; split; eauto using value_to_lc, open_abs.
Qed.

Lemma typing_to_lc : forall E e T,
  typing E e T -> lc e.
Proof.
  (* SOLUTION *)
  intros E e T H. induction H; eauto.
Qed.

(*************************************************************************)
(** * Decidability of Typechecking *)
(*************************************************************************)

(* Finally, we give another example of a proof that makes use of the
   renaming lemma. We show that determining whether a program type
   checks is decidable.
*)

(** Equality on types is decidable *)
Lemma eq_typ_dec : forall (T T' : typ),
  { T = T' } + { T <> T' }.
Proof.
  decide equality.
Qed.

(** Take-home exercise.

    To prove that ill-formed terms cannot be typechecked, we will need an
    auxiliary lemma that says that each term only has a single type.

    HINT: to prove this lemma you will need to generalize the induction
    hypothesis for T2 and use the lemma [binds_unique] from [AtomEnv.v].
*)
Lemma typing_c_unique : forall E e T1 T2,
  typing_c E e T1 ->
  typing_c E e T2 ->
  T1 = T2.
Proof.
(* SOLUTION *)
  intros E e T1 T2 Typ1 Typ2.
  generalize dependent T2.
  induction Typ1; intros T' Typ'; inversion Typ'; subst; eauto.
  Case "typing_var_c".
    eapply binds_unique; eauto.
  Case "typing_abs_c".
    f_equal; eauto.
    pick fresh x.
    apply (H0 x); eauto.
  Case "typing_app_c".
    assert (typ_arrow T1 T2 = typ_arrow T0 T') by auto.
    inversion H; eauto.
Qed.


(* A property P is decidable if we can show the proposition P \/ ~P. *)
Definition decidable (P : Prop) := (P \/ ~ P).

Lemma typing_c_decidable : forall E e,
  lc_c e -> uniq E -> decidable (exists T, typing_c E e T).
Proof.
  intros E e LC Uniq.
  generalize dependent E.
  induction LC; intros E Uniq.
  Case "typing_var_c".
    destruct (@binds_lookup_dec _ x E) as [[T H] | H].
      SCase "variable is in environment".
      left; eauto.
      SCase "variable not in environment".
      right.  intros [T J]. inversion J; subst; eauto.
  Case "typing_abs_c".
    (* To know whether the body typechecks, we must first
       pick a fresh variable to use the IH (aka HO).
    *)
        pick fresh x.
    assert (Fr' : x `notin` L) by auto.
    destruct (H0 x Fr' ((x ~ T) ++ E)) as [[S J] | J]; eauto.
    SCase "body typeable".
      left.
      exists (typ_arrow T S).
      (* Check (typing_abs_c L E (abs T e) T S). *)
      pick fresh z and apply typing_abs_c.
      apply typing_c_rename with (x := x); eauto.
    SCase "body not typeable".
      right.
      intros [S K].
      inversion K; subst.
      apply J.
      exists T2.
      pick fresh z.
      apply typing_c_rename with (x := z); eauto.
  Case "typing_app_c".
    destruct (IHLC1 E) as [[T H] | H]; eauto.
    SCase "function typeable".
      destruct (IHLC2 E) as [[S J] | J]; eauto.
      SSCase "argument typeable".
        destruct T.
          SSSCase "function has typ_base".
            right.
            intros [S' J'].
            inversion J'; subst.
            assert (K : typ_base = typ_arrow T1 S'); eauto using typing_c_unique.
            inversion K.
          SSSCase "typ_arrow".
            destruct (eq_typ_dec T1 S).
              subst. left; eauto.
              right.
                intros [S' J'].
                inversion J'; subst.
                assert (T0 = S); eauto using typing_c_unique.
                assert (typ_arrow T1 T2 = typ_arrow T0 S'); eauto using typing_c_unique.
                inversion H1; subst; eauto using typing_c_unique.
      SSCase "argument not typeable".
        right. intros [S' J']. inversion J'; subst; eauto.
    SCase "function not typeable".
      right. intros [S' J']. inversion J'; subst; eauto.
Qed.


(***********************************************************************)
(* Problematic proof of weakening. *)
(***********************************************************************)

Lemma typing_weakening_strengthened :  forall E F G e T,
  typing (G ++ E) e T ->
  uniq (G ++ F ++ E) ->
  typing (G ++ F ++ E) e T.
Proof.
  intros E F G e T H.
  remember (G ++ E) as E'.
  generalize dependent G.
  induction H; intros G Eq Ok; subst.
  Case "typing_var".
    apply typing_var.
      apply Ok.
      apply binds_weaken. apply H0.
  Case "typing_abs".
        apply typing_abs with (x:=x). auto.
Admitted.
