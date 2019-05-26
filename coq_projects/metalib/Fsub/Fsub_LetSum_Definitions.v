(** Definition of Fsub (System F with subtyping).

    Authors: Brian Aydemir and Arthur Chargu\'eraud, with help from
    Aaron Bohannon, Jeffrey Vaughan, and Dimitrios Vytiniotis.

    Table of contents:
      - #<a href="##syntax">Syntax (pre-terms)</a>#
      - #<a href="##open">Opening</a>#
      - #<a href="##lc">Local closure</a>#
      - #<a href="##env">Environments</a>#
      - #<a href="##wf">Well-formedness</a>#
      - #<a href="##sub">Subtyping</a>#
      - #<a href="##typing_doc">Typing</a>#
      - #<a href="##values">Values</a>#
      - #<a href="##reduction">Reduction</a>#
      - #<a href="##auto">Automation</a>#
*)

Require Export Metalib.Metatheory.


(* ********************************************************************** *)
(** * #<a name="syntax"></a># Syntax (pre-terms) *)

(** We use a locally nameless representation for Fsub, where bound
    variables are represented as natural numbers (de Bruijn indices)
    and free variables are represented as [atom]s.  The type [atom],
    defined in the MetatheoryAtom library, represents names: there are
    infinitely many atoms, equality is decidable on atoms, and it is
    possible to generate an atom fresh for any given finite set of
    atoms.

    We say that the definitions below define pre-types ([typ]) and
    pre-expressions ([exp]), collectively pre-terms, since the
    datatypes admit terms, such as [(typ_all typ_top (typ_bvar 3))],
    where indices are unbound.  A term is locally closed when it
    contains no unbound indices.

    Note that indices for bound type variables are distinct from
    indices for bound expression variables.  We make this explicit in
    the definitions below of the opening operations. *)

Inductive typ : Set :=
  | typ_top : typ
  | typ_bvar : nat -> typ
  | typ_fvar : atom -> typ
  | typ_arrow : typ -> typ -> typ
  | typ_all : typ -> typ -> typ
  | typ_sum : typ -> typ -> typ
.

Inductive exp : Set :=
  | exp_bvar : nat -> exp
  | exp_fvar : atom -> exp
  | exp_abs : typ -> exp -> exp
  | exp_app : exp -> exp -> exp
  | exp_tabs : typ -> exp -> exp
  | exp_tapp : exp -> typ -> exp
  | exp_let : exp -> exp -> exp
  | exp_inl : exp -> exp
  | exp_inr : exp -> exp
  | exp_case : exp -> exp -> exp -> exp
.

(** We declare the constructors for indices and variables to be
    coercions.  For example, if Coq sees a [nat] where it expects an
    [exp], it will implicitly insert an application of [exp_bvar];
    similar behavior happens for [atom]s.  Thus, we may write
    [(exp_abs typ_top (exp_app 0 x))] instead of [(exp_abs typ_top
    (exp_app (exp_bvar 0) (exp_fvar x)))]. *)

Coercion typ_bvar : nat >-> typ.
Coercion typ_fvar : atom >-> typ.
Coercion exp_bvar : nat >-> exp.
Coercion exp_fvar : atom >-> exp.


(* ********************************************************************** *)
(** * #<a name="open"></a># Opening terms *)

(** Opening replaces an index with a term.  This operation is required
    if we wish to work only with locally closed terms when going under
    binders (e.g., the typing rule for [exp_abs]).  It also
    corresponds to informal substitution for a bound variable, which
    occurs in the rule for beta reduction.

    We need to define three functions for opening due the syntax of
    Fsub, and we name them according to the following convention.
      - [tt]: Denotes an operation involving types appearing in types.
      - [te]: Denotes an operation involving types appearing in
        expressions.
      - [ee]: Denotes an operation involving expressions appearing in
        expressions.

    The notation used below for decidable equality on natural numbers
    (e.g., [K == J]) is defined in the CoqEqDec library, which is
    included by the Metatheory library.  The order of arguments to
    each "open" function is the same.  For example, [(open_tt_rec K U
    T)] can be read as "substitute [U] for index [K] in [T]."

    Note that we assume [U] is locally closed (and similarly for the
    other opening functions).  This assumption simplifies the
    implementations of opening by letting us avoid shifting.  Since
    bound variables are indices, there is no need to rename variables
    to avoid capture.  Finally, we assume that these functions are
    initially called with index zero and that zero is the only unbound
    index in the term.  This eliminates the need to possibly subtract
    one in the case of indices. *)

Fixpoint open_tt_rec (K : nat) (U : typ) (T : typ)  {struct T} : typ :=
  match T with
  | typ_top => typ_top
  | typ_bvar J => if K == J then U else (typ_bvar J)
  | typ_fvar X => typ_fvar X
  | typ_arrow T1 T2 => typ_arrow (open_tt_rec K U T1) (open_tt_rec K U T2)
  | typ_all T1 T2 => typ_all (open_tt_rec K U T1) (open_tt_rec (S K) U T2)
  | typ_sum T1 T2 => typ_sum (open_tt_rec K U T1) (open_tt_rec K U T2)
  end.

Fixpoint open_te_rec (K : nat) (U : typ) (e : exp) {struct e} : exp :=
  match e with
  | exp_bvar i => exp_bvar i
  | exp_fvar x => exp_fvar x
  | exp_abs V e1 => exp_abs  (open_tt_rec K U V)  (open_te_rec K U e1)
  | exp_app e1 e2 => exp_app  (open_te_rec K U e1) (open_te_rec K U e2)
  | exp_tabs V e1 => exp_tabs (open_tt_rec K U V)  (open_te_rec (S K) U e1)
  | exp_tapp e1 V => exp_tapp (open_te_rec K U e1) (open_tt_rec K U V)
  | exp_let e1 e2 => exp_let (open_te_rec K U e1) (open_te_rec K U e2)
  | exp_inl e1 => exp_inl (open_te_rec K U e1)
  | exp_inr e2 => exp_inr (open_te_rec K U e2)
  | exp_case e1 e2 e3 =>
      exp_case (open_te_rec K U e1) (open_te_rec K U e2) (open_te_rec K U e3)
  end.

Fixpoint open_ee_rec (k : nat) (f : exp) (e : exp)  {struct e} : exp :=
  match e with
  | exp_bvar i => if k == i then f else (exp_bvar i)
  | exp_fvar x => exp_fvar x
  | exp_abs V e1 => exp_abs V (open_ee_rec (S k) f e1)
  | exp_app e1 e2 => exp_app (open_ee_rec k f e1) (open_ee_rec k f e2)
  | exp_tabs V e1 => exp_tabs V (open_ee_rec k f e1)
  | exp_tapp e1 V => exp_tapp (open_ee_rec k f e1) V
  | exp_let e1 e2 => exp_let (open_ee_rec k f e1) (open_ee_rec (S k) f e2)
  | exp_inl e1 => exp_inl (open_ee_rec k f e1)
  | exp_inr e2 => exp_inr (open_ee_rec k f e2)
  | exp_case e1 e2 e3 =>
      exp_case (open_ee_rec k f e1)
               (open_ee_rec (S k) f e2)
               (open_ee_rec (S k) f e3)
  end.

(** Many common applications of opening replace index zero with an
    expression or variable.  The following definitions provide
    convenient shorthands for such uses.  Note that the order of
    arguments is switched relative to the definitions above.  For
    example, [(open_tt T X)] can be read as "substitute the variable
    [X] for index [0] in [T]" and "open [T] with the variable [X]."
    Recall that the coercions above let us write [X] in place of
    [(typ_fvar X)], assuming that [X] is an [atom]. *)

Definition open_tt T U := open_tt_rec 0 U T.
Definition open_te e U := open_te_rec 0 U e.
Definition open_ee e1 e2 := open_ee_rec 0 e2 e1.


(* ********************************************************************** *)
(** * #<a name="lc"></a># Local closure *)

(** Recall that [typ] and [exp] define pre-terms; these datatypes
    admit terms that contain unbound indices.  A term is locally
    closed, or syntactically well-formed, when no indices appearing in
    it are unbound.  The proposition [(type T)] holds when a type [T]
    is locally closed, and [(expr e)] holds when an expression [e] is
    locally closed.

    The inductive definitions below formalize local closure such that
    the resulting induction principles serve as structural induction
    principles over (locally closed) types and (locally closed)
    expressions.  In particular, unlike the situation with pre-terms,
    there are no cases for indices.  Thus, these induction principles
    correspond more closely to informal practice than the ones arising
    from the definitions of pre-terms.

    The interesting cases in the inductive definitions below are those
    that involve binding constructs, e.g., [typ_all].  Intuitively, to
    check if the pre-term [(typ_all T1 T2)] is locally closed, we must
    check that [T1] is locally closed and that [T2] is locally closed
    when opened with a variable.  However, there is a choice as to how
    many variables to quantify over.  One possibility is to quantify
    over only one variable ("existential" quantification), as in
<<
  type_all : forall X T1 T2,
      type T1 ->
      type (open_tt T2 X) ->
      type (typ_all T1 T2) .
>>  Or, we could quantify over as many variables as possible ("universal"
    quantification), as in
<<
  type_all : forall T1 T2,
      type T1 ->
      (forall X : atom, type (open_tt T2 X)) ->
      type (typ_all T1 T2) .
>>  It is possible to show that the resulting relations are equivalent.
    The former makes it easy to build derivations, while the latter
    provides a strong induction principle.  McKinna and Pollack used
    both forms of this relation in their work on formalizing Pure Type
    Systems.

    We take a different approach here and use "cofinite"
    quantification: we quantify over all but finitely many variables.
    This approach provides a convenient middle ground: we can build
    derivations reasonably easily and get reasonably strong induction
    principles.  With some work, one can show that the definitions
    below are equivalent to ones that use existential, and hence also
    universal, quantification. *)

Inductive type : typ -> Prop :=
  | type_top :
      type typ_top
  | type_var : forall X,
      type (typ_fvar X)
  | type_arrow : forall T1 T2,
      type T1 ->
      type T2 ->
      type (typ_arrow T1 T2)
  | type_all : forall L T1 T2,
      type T1 ->
      (forall X : atom, X `notin` L -> type (open_tt T2 X)) ->
      type (typ_all T1 T2)
  | type_sum : forall T1 T2,
      type T1 ->
      type T2 ->
      type (typ_sum T1 T2)
.

Inductive expr : exp -> Prop :=
  | expr_var : forall x,
      expr (exp_fvar x)
  | expr_abs : forall L T e1,
      type T ->
      (forall x : atom, x `notin` L -> expr (open_ee e1 x)) ->
      expr (exp_abs T e1)
  | expr_app : forall e1 e2,
      expr e1 ->
      expr e2 ->
      expr (exp_app e1 e2)
  | expr_tabs : forall L T e1,
      type T ->
      (forall X : atom, X `notin` L -> expr (open_te e1 X)) ->
      expr (exp_tabs T e1)
  | expr_tapp : forall e1 V,
      expr e1 ->
      type V ->
      expr (exp_tapp e1 V)
  | expr_let : forall L e1 e2,
      expr e1 ->
      (forall x : atom, x `notin` L -> expr (open_ee e2 x)) ->
      expr (exp_let e1 e2)
  | expr_inl : forall e1,
      expr e1 ->
      expr (exp_inl e1)
  | expr_inr : forall e1,
      expr e1 ->
      expr (exp_inr e1)
  | expr_case : forall L e1 e2 e3,
      expr e1 ->
      (forall x : atom, x `notin` L -> expr (open_ee e2 x)) ->
      (forall x : atom, x `notin` L -> expr (open_ee e3 x)) ->
      expr (exp_case e1 e2 e3)
.

(** #<a name="body_e_doc"></a># We also define what it means to be the
    body of an abstraction, since this simplifies slightly the
    definition of reduction and subsequent proofs.  It is not strictly
    necessary to make this definition in order to complete the
    development. *)

Definition body_e (e : exp) :=
  exists L, forall x : atom, x `notin` L -> expr (open_ee e x).


(* ********************************************************************** *)
(** * #<a name="env"></a># Environments *)

(** In our presentation of System F with subtyping, we use a single
    environment for both typing and subtyping assumptions.  We
    formalize environments by representing them as association lists
    (lists of pairs of keys and values) whose keys are atoms.

    The Metatheory and MetatheoryEnv libraries provide functions,
    predicates, tactics, notations and lemmas that simplify working
    with environments.  They treat environments as lists of type [list
    (atom * A)].  The notation [(x ~ a)] denotes a list consisting of
    a single binding from [x] to [a].

    Since environments map [atom]s, the type [A] should encode whether
    a particular binding is a typing or subtyping assumption.  Thus,
    we instantiate [A] with the type [binding], defined below. *)

Inductive binding : Set :=
  | bind_sub : typ -> binding
  | bind_typ : typ -> binding.

(** A binding [(X ~ bind_sub T)] records that a type variable [X] is a
    subtype of [T], and a binding [(x ~ bind_typ U)] records that an
    expression variable [x] has type [U].

    We define an abbreviation [env] for the type of environments, and
    an abbreviation [empty] for the empty environment.

    Note: Each instance of [Notation] below defines an abbreviation
    since the left-hand side consists of a single identifier that is
    not in quotes.  These abbreviations are used for both parsing (the
    left-hand side is equivalent to the right-hand side in all
    contexts) and printing (the right-hand side is pretty-printed as
    the left-hand side).  Since [nil] is normally a polymorphic
    constructor whose type argument is implicit, we prefix the name
    with "[@]" to signal to Coq that we are going to supply arguments
    to [nil] explicitly. *)

Notation env := (list (atom * binding)).
Notation empty := (@nil (atom * binding)).

(** #<b>#Examples:#</b># We use a convention where environments are
    never built using a cons operation [((x, a) :: E)] where [E] is
    non-[nil].  This makes the shape of environments more uniform and
    saves us from excessive fiddling with the shapes of environments.
    For example, Coq's tactics sometimes distinguish between consing
    on a new binding and prepending a one element list, even though
    the two operations are convertible with each other.

    Consider the following environments written in informal notation.
<<
  1. (empty environment)
  2. x : T
  3. x : T, Y <: S
  4. E, x : T, F
>>  In the third example, we have an environment that binds an
    expression variable [x] to [T] and a type variable [Y] to [S].
    In Coq, we would write these environments as follows.
<<
  1. empty
  2. x ~ bind_typ T
  3. Y ~ bind_sub S ++ x ~ bind_typ T
  4. F ++ x ~ bind_typ T ++ E
>> The symbol "[++]" denotes list concatenation and associates to the
    right.  (That notation is defined in Coq's List library.)  Note
    that in Coq, environments grow on the left, since that is where
    the head of a list is. *)


(* ********************************************************************** *)
(** * #<a name="wf"></a># Well-formedness *)

(** A type [T] is well-formed with respect to an environment [E],
    denoted [(wf_typ E T)], when [T] is locally-closed and its free
    variables are bound in [E].  We need this relation in order to
    restrict the subtyping and typing relations, defined below, to
    contain only well-formed types.  (This relation is missing in the
    original statement of the POPLmark Challenge.)

    Note: It is tempting to define the premise of [wf_typ_var] as [(X
    `in` dom E)], since that makes the rule easier to apply (no need
    to guess an instantiation for [U]).  Unfortunately, this is
    incorrect.  We need to check that [X] is bound as a type-variable,
    not an expression-variable; [(dom E)] does not distinguish between
    the two kinds of bindings. *)

Inductive wf_typ : env -> typ -> Prop :=
  | wf_typ_top : forall E,
      wf_typ E typ_top
  | wf_typ_var : forall U E (X : atom),
      binds X (bind_sub U) E ->
      wf_typ E (typ_fvar X)
  | wf_typ_arrow : forall E T1 T2,
      wf_typ E T1 ->
      wf_typ E T2 ->
      wf_typ E (typ_arrow T1 T2)
  | wf_typ_all : forall L E T1 T2,
      wf_typ E T1 ->
      (forall X : atom, X `notin` L ->
        wf_typ (X ~ bind_sub T1 ++ E) (open_tt T2 X)) ->
      wf_typ E (typ_all T1 T2)
  | wf_typ_sum : forall E T1 T2,
      wf_typ E T1 ->
      wf_typ E T2 ->
      wf_typ E (typ_sum T1 T2)
.

(** An environment [E] is well-formed, denoted [(wf_env E)], if each
    atom is bound at most at once and if each binding is to a
    well-formed type.  This is a stronger relation than the [uniq]
    relation defined in the MetatheoryEnv library.  We need this
    relation in order to restrict the subtyping and typing relations,
    defined below, to contain only well-formed environments.  (This
    relation is missing in the original statement of the POPLmark
    Challenge.)  *)

Inductive wf_env : env -> Prop :=
  | wf_env_empty :
      wf_env empty
  | wf_env_sub : forall (E : env) (X : atom) (T : typ),
      wf_env E ->
      wf_typ E T ->
      X `notin` dom E ->
      wf_env (X ~ bind_sub T ++ E)
  | wf_env_typ : forall (E : env) (x : atom) (T : typ),
      wf_env E ->
      wf_typ E T ->
      x `notin` dom E ->
      wf_env (x ~ bind_typ T ++ E).


(* ********************************************************************** *)
(** * #<a name="sub"></a># Subtyping *)

(** The definition of subtyping is straightforward.  It uses the
    [binds] relation from the MetatheoryEnv library (in the
    [sub_trans_tvar] case) and cofinite quantification (in the
    [sub_all] case). *)

Inductive sub : env -> typ -> typ -> Prop :=
  | sub_top : forall E S,
      wf_env E ->
      wf_typ E S ->
      sub E S typ_top
  | sub_refl_tvar : forall E X,
      wf_env E ->
      wf_typ E (typ_fvar X) ->
      sub E (typ_fvar X) (typ_fvar X)
  | sub_trans_tvar : forall U E T X,
      binds X (bind_sub U) E ->
      sub E U T ->
      sub E (typ_fvar X) T
  | sub_arrow : forall E S1 S2 T1 T2,
      sub E T1 S1 ->
      sub E S2 T2 ->
      sub E (typ_arrow S1 S2) (typ_arrow T1 T2)
  | sub_all : forall L E S1 S2 T1 T2,
      sub E T1 S1 ->
      (forall X : atom, X `notin` L ->
          sub (X ~ bind_sub T1 ++ E) (open_tt S2 X) (open_tt T2 X)) ->
      sub E (typ_all S1 S2) (typ_all T1 T2)
  | sub_sum : forall E S1 S2 T1 T2,
      sub E S1 T1 ->
      sub E S2 T2 ->
      sub E (typ_sum S1 S2) (typ_sum T1 T2)
.


(* ********************************************************************** *)
(** * #<a name="typing_doc"></a># Typing *)

(** The definition of typing is straightforward.  It uses the [binds]
    relation from the MetatheoryEnv library (in the [typing_var] case)
    and cofinite quantification in the cases involving binders (e.g.,
    [typing_abs] and [typing_tabs]). *)

Inductive typing : env -> exp -> typ -> Prop :=
  | typing_var : forall E x T,
      wf_env E ->
      binds x (bind_typ T) E ->
      typing E (exp_fvar x) T
  | typing_abs : forall L E V e1 T1,
      (forall x : atom, x `notin` L ->
        typing (x ~ bind_typ V ++ E) (open_ee e1 x) T1) ->
      typing E (exp_abs V e1) (typ_arrow V T1)
  | typing_app : forall T1 E e1 e2 T2,
      typing E e1 (typ_arrow T1 T2) ->
      typing E e2 T1 ->
      typing E (exp_app e1 e2) T2
  | typing_tabs : forall L E V e1 T1,
      (forall X : atom, X `notin` L ->
        typing (X ~ bind_sub V ++ E) (open_te e1 X) (open_tt T1 X)) ->
      typing E (exp_tabs V e1) (typ_all V T1)
  | typing_tapp : forall T1 E e1 T T2,
      typing E e1 (typ_all T1 T2) ->
      sub E T T1 ->
      typing E (exp_tapp e1 T) (open_tt T2 T)
  | typing_sub : forall S E e T,
      typing E e S ->
      sub E S T ->
      typing E e T
  | typing_let : forall L T1 T2 e1 e2 E,
      typing E e1 T1 ->
      (forall x : atom, x `notin` L ->
        typing (x ~ bind_typ T1 ++ E) (open_ee e2 x) T2) ->
      typing E (exp_let e1 e2) T2
  | typing_inl : forall T1 T2 e1 E,
      typing E e1 T1 ->
      wf_typ E T2 ->
      typing E (exp_inl e1) (typ_sum T1 T2)
  | typing_inr : forall T1 T2 e1 E,
      typing E e1 T2 ->
      wf_typ E T1 ->
      typing E (exp_inr e1) (typ_sum T1 T2)
  | typing_case : forall L T1 T2 T e1 e2 e3 E,
      typing E e1 (typ_sum T1 T2) ->
      (forall x : atom, x `notin` L ->
        typing (x ~ bind_typ T1 ++ E) (open_ee e2 x) T) ->
      (forall x : atom, x `notin` L ->
        typing (x ~ bind_typ T2 ++ E) (open_ee e3 x) T) ->
      typing E (exp_case e1 e2 e3) T
.


(* ********************************************************************** *)
(** * #<a name="values"></a># Values *)

Inductive value : exp -> Prop :=
  | value_abs : forall T e1,
      expr (exp_abs T e1) ->
      value (exp_abs T e1)
  | value_tabs : forall T e1,
      expr (exp_tabs T e1) ->
      value (exp_tabs T e1)
  | value_inl : forall e1,
      value e1 ->
      value (exp_inl e1)
  | value_inr : forall e1,
      value e1 ->
      value (exp_inr e1)
.


(* ********************************************************************** *)
(** * #<a name="reduction"></a># Reduction *)

Inductive red : exp -> exp -> Prop :=
  | red_app_1 : forall e1 e1' e2,
      expr e2 ->
      red e1 e1' ->
      red (exp_app e1 e2) (exp_app e1' e2)
  | red_app_2 : forall e1 e2 e2',
      value e1 ->
      red e2 e2' ->
      red (exp_app e1 e2) (exp_app e1 e2')
  | red_tapp : forall e1 e1' V,
      type V ->
      red e1 e1' ->
      red (exp_tapp e1 V) (exp_tapp e1' V)
  | red_abs : forall T e1 v2,
      expr (exp_abs T e1) ->
      value v2 ->
      red (exp_app (exp_abs T e1) v2) (open_ee e1 v2)
  | red_tabs : forall T1 e1 T2,
      expr (exp_tabs T1 e1) ->
      type T2 ->
      red (exp_tapp (exp_tabs T1 e1) T2) (open_te e1 T2)
  | red_let_1 : forall e1 e1' e2,
      red e1 e1' ->
      body_e e2 ->
      red (exp_let e1 e2) (exp_let e1' e2)
  | red_let : forall v1 e2,
      value v1 ->
      body_e e2 ->
      red (exp_let v1 e2) (open_ee e2 v1)
  | red_inl_1 : forall e1 e1',
      red e1 e1' ->
      red (exp_inl e1) (exp_inl e1')
  | red_inr_1 : forall e1 e1',
      red e1 e1' ->
      red (exp_inr e1) (exp_inr e1')
  | red_case_1 : forall e1 e1' e2 e3,
      red e1 e1' ->
      body_e e2 ->
      body_e e3 ->
      red (exp_case e1 e2 e3) (exp_case e1' e2 e3)
  | red_case_inl : forall v1 e2 e3,
      value v1 ->
      body_e e2 ->
      body_e e3 ->
      red (exp_case (exp_inl v1) e2 e3) (open_ee e2 v1)
  | red_case_inr : forall v1 e2 e3,
      value v1 ->
      body_e e2 ->
      body_e e3 ->
      red (exp_case (exp_inr v1) e2 e3) (open_ee e3 v1)
.


(* ********************************************************************** *)
(** * #<a name="auto"></a># Automation *)

(** We declare most constructors as [Hint]s to be used by the [auto]
    and [eauto] tactics.  We exclude constructors from the subtyping
    and typing relations that use cofinite quantification.  It is
    unlikely that [eauto] will find an instantiation for the finite
    set [L], and in those cases, [eauto] can take some time to fail.
    (A priori, this is not obvious.  In practice, one adds as hints
    all constructors and then later removes some constructors when
    they cause proof search to take too long.) *)

Hint Constructors type expr wf_typ wf_env value red.
Hint Resolve sub_top sub_refl_tvar sub_arrow.
Hint Resolve sub_sum typing_inl typing_inr.
Hint Resolve typing_var typing_app typing_tapp typing_sub.
Hint Resolve typing_inl typing_inr.
