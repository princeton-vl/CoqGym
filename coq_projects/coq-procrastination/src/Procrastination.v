(******************************************************************************)
(* Summary of the tactics exported by this file:                              *)
(*                                                                            *)
(* begin defer [assuming a b...] [in g]                                       *)
(* defer [in g]                                                               *)
(* defer [H] : E [in g]                                                       *)
(* end defer                                                                  *)
(*                                                                            *)
(* deferred [in g]                                                            *)
(* deferred [H] : E [in g]                                                    *)
(*                                                                            *)
(* deferred exploit tac [in g]                                                *)
(******************************************************************************)

(* The comments below describe the various tricks used for implementing the
   library. For a higher-level description of what it does, and how to use it,
   one should rather refer to the manual in `manual/manual.pdf`, and the
   `examples/` directory. For a reference of the tactics, see
   `TacticsReference.md`.
*)

(* We define a couple "marker" definitions. These are equivalent to the
   identity, but are useful to mark subterms to be used with tactics or
   notation. *)
Module Marker.

(* This marker is used in combination with a notation (see the end of the file),
   in order to hide the exact expression of a subgoal, and to indicate that
   faced with this subgoal, the user always has to call the
   [end defer] tactic. *)
Definition end_defer (P : Type) := P.

(* This marker is used to keep track of "group" assumptions in the context
   (introduced by [begin procrastination]). This is useful so that tactics can
   omit specifying a group: in that case, the first group of the context is
   used. *)
Definition group (P : Prop) := P.

Lemma group_fold : forall (P: Prop), P -> group P.
Proof. auto. Qed.

Ltac find_group :=
  match goal with
  | H : group _ |- _ => constr:(H)
  end.

End Marker.

(* This is necessary to prevent tactics like [eauto] to instantiate the evar in
   the group with e.g. [False]. *)
Global Opaque Marker.group.

(* A very simple implementation of [begin defer] could be as follows:

   ```
   Lemma L0 : forall Goal group,
     (group -> Goal) ->
     group ->
     Goal.

   Ltac begin_defer := eapply L0.
   ```

   By using [eapply L0], [group] is introduced as an evar. Then, in the first
   subgoal [group -> Goal], [defer] can be used to discharge propositions to
   defer, by raffining the [group] evar (which is of type [Prop]). Then, in the
   second subgoal, one has to prove the propositions collected in [group].


   Similarly, [begin defer assuming a] could be implemented as:

   ```
   Lemma L1 : forall A Goal (group : A -> Prop),
     (forall a, group a -> Goal) ->
     (exists a, group a) ->
     Goal.

   Ltac begin_defer_assuming_1 := eapply L1
   ```

   This allows us to defer propositions that depend on some parameter [a] of
   type [A]. However we would like to have this for an arbitrary number of
   parameters. This is the purpose of the tactics in the module below.


   More precisely, the tactics below take an arity as parameter, and build the
   statement of a lemma (similar to L0 or L1) for that arity. To achieve that
   using Ltac, we do not try to construct the term corresponding to the lemma's
   statement directly (this is not supported by Ltac). Instead, what we can do
   is produce a subgoal (of type [Prop]) corresponding to the statement of the
   lemma, and construct the statement using successive applications of the
   [refine] tactic.

   The same set of tricks is used to implement [end defer], which requires
   generating a "clean-up" lemma, whose statement depends on the number of
   "exists" introduced by [begin defer].

   We start by defining some utility tactics, that help building bits of the
   statements when following this methodology.
*)
Module MkHelperLemmas.

(* General helpers *)

(* [transparent_assert name type] produces a new subgoal of type [type], whose
   *proof term* will appear as a definition in the context of the main subgoal.

   Here, [type] will be [Prop] or [Type], and the first subgoal will be proved
   using multiple [refine], thus constructing the desired lemma statement.
*)
Ltac transparent_assert name type :=
  unshelve refine (let name := _ : type in _).

(* This is generally useful in tactics to have lists of things (e.g.
   assumptions) of heterogeneous types, by "boxing" them using [boxer]. *)
Inductive Boxer :=
| boxer : forall A : Type, A -> Boxer.
Arguments boxer : clear implicits.

(* It is useful for user-friendliness to carry around the user-provided names
   (given with ...assuming a b c). However, Ltac does not have proper
   data-structures that could be used to carry around a list of identifiers.

  We use the following trick as a workaround: given identifiers a, b, c, one can
  craft the following coq term: (fun a b c : unit => tt). Amusingly, this will
  be pretty-printed by coq as (fun _ _ _ => tt), but the information about the
  user names is still kept around. Then, one can match on this coq term to
  recover the names:

  match constr:(fun a b c : unit => tt) with
  | (fun x => _) =>
    idtac x
  end

  will print 'a', for example. Then one can apply a
  "list-of-identifiers-as-a-coq-term" to tt to get its tail, while the base case
  is having tt.
*)

(* Computes the number of identifiers, ie the "length of the list" *)
Ltac ids_nb ids :=
  lazymatch ids with
  | tt => constr:(O)
  | (fun x => _) =>
    let ids' := eval cbv beta in (ids tt) in
    let n := ids_nb ids' in
    constr:(S n)
  end.

Ltac iter_idents ids tac :=
  lazymatch ids with
  | tt => idtac
  | (fun x => _) =>
    tac x;
    iter_idents ltac:(eval cbv beta in (ids tt)) tac
  end.

(* For debugging purposes *)
Ltac print_ids ids :=
  lazymatch ids with
  | tt => idtac
  | (fun x => _) =>
    let ids' := eval cbv beta in (ids tt) in
    idtac x;
    print_ids ids'
  end.


(* [mk_forall varty goalty n cont], called on a goal of type [goalty] (e.g.
   [Type] or [Prop]), refines its proof term to be [forall x_1 ... x_n, _],
   where all [x_i] have type [varty].

   The continuation [cont] is then called, with as argument the list of variable
   names introduced, i.e. the list of (boxed) [x_i].
*)
Ltac mk_forall varty goalty n cont :=
  lazymatch n with
  | O => cont (@nil Boxer)
  | S ?n' =>
    let X := fresh in
    refine (forall (X : varty), _ : goalty);
    mk_forall varty goalty n' ltac:(fun x => cont (cons (boxer varty X) x))
  end.

(* [mk_forall_tys vartys goalty cont] is similar to [mk_forall], but the
   variables introduced can now have different types, as specified by the list
   [vartys].
*)
Ltac mk_forall_tys vartys goalty cont :=
  lazymatch vartys with
  | nil => cont (@nil Boxer)
  | cons (boxer _ ?ty) ?tys =>
    let X := fresh in
    refine (forall (X : ty), _ : goalty);
    mk_forall_tys tys goalty ltac:(fun x => cont (cons (boxer ty X) x))
  end.

(* [mk_arrow vars goalty] refines the proof term to be [x_1 -> .. -> x_n -> _],
   where [vars] is [[x_1; ..; x_n]]. *)
Ltac mk_arrow vars goalty :=
  lazymatch vars with
  | nil => idtac
  | cons (boxer _ ?v) ?vs =>
    refine (v -> _ : goalty);
    mk_arrow vs goalty
  end.

(* [mk_app f vars goalty] refines the proof term to be [f x_1 .. x_2], where
   [vars] is [[x_1; ..; x_n]]. *)
Ltac mk_app f vars goalty :=
  lazymatch vars with
  | nil => exact f
  | cons (boxer _ ?v) ?vs =>
    refine (_ v : goalty);
    let x := fresh "x" in intro x;
    mk_app (f x) vs goalty
  end.

(* [mk_sigT_sig ids goalty cont] refines the proof term to be [sigT (fun x_1 => ..
   sigT (fun x_n-1 => sig (fun x_n => _)))], then calls [cont] with the list of
   variables introduced [[x_1; .. x_n]]. *)
Ltac mk_sigT_sig ids goalty cont :=
  lazymatch ids with
  | tt => cont (@nil Boxer)
  | (fun x => tt) =>
    let X := fresh x in
    refine (sig (fun X => _) : goalty);
    cont (cons (@boxer _ X) (@nil Boxer))
  | (fun x => _) =>
    let ids' := eval cbv beta in (ids tt) in
    let X := fresh x in
    refine (sigT (fun X => _) : goalty);
    mk_sigT_sig ids' goalty ltac:(fun x => cont (cons (@boxer _ X) x))
  end.

(* Similarly, [mk_exists ids goalty cont] refines the proof term to be [exists x_1
   .. x_n, _], and calls [cont] with the list [[x_1; ..; x_n]]. *)
Ltac mk_exists ids goalty cont :=
  lazymatch ids with
  | tt => cont (@nil Boxer)
  | (fun x => _) =>
    let ids' := eval cbv beta in (ids tt) in
    let X := fresh x in
    refine (exists X, _ : goalty);
    mk_exists ids' goalty ltac:(fun x => cont (cons (@boxer _ X) x))
  end.

Ltac introsType :=
  repeat (
      match goal with
      | |- forall (_ : Type), _ =>
        intro
      end
    ).

(* [begin defer] helpers *)

(* This tactic is able to prove the statements of helper lemmas for [begin
   defer], for any arity. *)
Ltac prove_begin_defer_helper :=
  introsType;
  let H := fresh in
  intros ? ? ? H;
  unfold Marker.end_defer in *;
  repeat (let x := fresh "x" in destruct H as (x & H));
  eauto using Marker.group_fold.

(* Tests for the tactic above. *)
Goal forall (g : Prop) (P : Type),
    (Marker.group g -> P) ->
    Marker.end_defer g ->
    P.
Proof. prove_begin_defer_helper. Qed.

Goal forall A (g : A -> Prop) (P : Prop),
    (forall a, Marker.group (g a) -> P) ->
    Marker.end_defer (exists a, g a) ->
    P.
Proof. prove_begin_defer_helper. Qed.

Goal forall A B (g : A -> B -> Prop) (P : Prop),
    (forall a b, Marker.group (g a b) -> P) ->
    Marker.end_defer (exists a b, g a b) ->
    P.
Proof. prove_begin_defer_helper. Qed.

Goal forall A B (g : A -> B -> Prop) (P : Type),
    (forall a b, Marker.group (g a b) -> P) ->
    Marker.end_defer {a : A & { b | g a b } } ->
    P.
Proof. prove_begin_defer_helper. Qed.

(* Tactic that generates lemma statements as [begin defer] helpers.

   Generates a definition G := ... . G then corresponds to a statement that can
   be proved using [prove_begin_defer_helper], and is of the form:

   ```
   forall
     (A B .. Z : Type)
     (facts : A -> B -> .. -> Z -> Prop)
     (P: Prop),
   (forall a b .. z, Marker.group (facts a b .. z) -> P) ->
   end_defer (exists a b .. z, facts a b .. z) ->
   P.
   ```

   The type of P is actually taken as a parameter Pty (in practice, Prop or
   Type), and the last hypothesis is produced by the argument tactic
   [mk_exists].

   When P is of type Prop, the last hypothesis is as shown, and uses exists.
   When P is of type Type, the last hypothesis is instead of the form
     sigT (fun a => sigT (fun b => ... sig (fun z => facts_closed a b .. z)))
*)
Ltac mk_begin_defer_helper_aux n G Pty mk_exists :=
  transparent_assert G Type;
  [ mk_forall Type Type n ltac:(fun L =>
      let g_ty := fresh "g_ty" in
      transparent_assert g_ty Type;
      [ mk_arrow L Type; exact Prop | simpl in g_ty];

      let g := fresh "g" in
      refine (forall (g : g_ty), _ : Type);
      subst g_ty;

      let P := fresh "P" in
      refine (forall (P : Pty), _ : Type);

      let H1 := fresh "H1" in transparent_assert H1 Type;
      [ mk_forall_tys L Type ltac:(fun l =>
          let g_args := fresh in transparent_assert g_args Prop;
          [ mk_app g l Prop | simpl in g_args];
          refine (Marker.group g_args -> P : Type)
        )
      | simpl in H1];

      let H2 := fresh "H2" in transparent_assert H2 Type;
      [ refine (Marker.end_defer _ : Type);
        mk_exists n ltac:(fun l => mk_app g l Prop)
      | simpl in H2];

      exact (H1 -> H2 -> P)
    )
  | simpl in G].

Ltac mk_begin_defer_helper_Type ids G :=
  let n := ids_nb ids in
  mk_begin_defer_helper_aux n G Type
    ltac:(fun n cont => mk_sigT_sig ids Type cont).

Ltac mk_begin_defer_helper_Prop ids G :=
  let n := ids_nb ids in
  mk_begin_defer_helper_aux n G Prop
    ltac:(fun n cont => mk_exists ids Prop cont).

(* When the goal is of type [Type], generate a statement using constructive
   exists. When it is of type [Prop], use regular exists. *)
Ltac mk_begin_defer_helper ids :=
  let H := fresh in
  match goal with |- ?G =>
    match type of G with
    | Prop => mk_begin_defer_helper_Prop ids H
    | _ => mk_begin_defer_helper_Type ids H
    end;
    cut H; subst H; [| now prove_begin_defer_helper]
  end.

(* Tests *)
Goal True.
  mk_begin_defer_helper tt.
  intro H; eapply H; clear H.
Abort.

Goal True.
  mk_begin_defer_helper (fun a b c : unit => tt).
  intro H; eapply H; clear H.
Abort.

Goal nat.
  mk_begin_defer_helper (fun a b c : unit => tt).
  intro H; eapply H; clear H.
Abort.

(* [end defer] helpers.

   [end defer] is called on the second subgoal produced by [begin defer], of the
   form [exists a .. z, group a .. z], where [group a .. z] has been
   instantiated by [defer] into something of the form [P1 /\ P2 /\ ... /\ Pn /\
   ?P], where P1 .. Pn are the propositions that have been deferred, and [?P] is
   the "accumulator" evar.

   The role of [end defer] is to close the goal, instantiating [?P] with [True],
   and removing it from the goal.

   This is done by first applying a lemma of the form:

   ```
   forall A .. Z (G1 G2 : A -> .. -> Z -> Prop),
   (forall a .. z, G1 a .. z -> G2 a .. z) ->
   (exists a .. z, G1 a .. z) ->
   exists a .. z, G2 a .. z
   ```

   After applying this lemma, [G2] is unified with the current goal (to clean),
   and [G1] is introduced as an evar. An auxiliary tactic
   ([cleanup_conj_goal_core], defined below) is called on the first subgoal, and
   will discharge it, instantiating [G1] with the cleaned-up goal (i.e [P1 /\ P2
   /\ ... /\ Pn]).

   The helpers below help generating and proving this lemma, for any number of
   variables [a] .. [z].
*)

(* Tactic that proves the lemma above for any arity. *)
Ltac prove_end_defer_helper :=
  introsType;
  let P1 := fresh in
  let P2 := fresh in
  let H1 := fresh in
  let H2 := fresh in
  intros P1 P2 H1 H2;
  unfold Marker.end_defer in *;
  repeat (let x := fresh "x" in destruct H2 as (x & H2); exists x);
  apply H1; auto.

(* Tests. *)
Goal forall A (P1 P2 : A -> Prop),
  (forall a, P1 a -> P2 a) ->
  (exists a, P1 a) ->
  Marker.end_defer (exists a, P2 a).
Proof. prove_end_defer_helper. Qed.

Goal forall A B (P1 P2 : A -> B -> Prop),
  (forall a b, P1 a b -> P2 a b) ->
  (exists a b, P1 a b) ->
  Marker.end_defer (exists a b, P2 a b).
Proof. prove_end_defer_helper. Qed.

Goal forall A (P1 P2 : A -> Prop),
  (forall a, P1 a -> P2 a) ->
  { a | P1 a } ->
  Marker.end_defer { a | P2 a }.
Proof. prove_end_defer_helper. Qed.

(* Generates a definition G := ... . G then corresponds to a statement that can
   be proved using [prove_begin_defer_helper], and is of the form detailed
   above.

   [mk_exists] is used to refine the nested "exists", allowing the tactic to
   produce statements using either exists in [Prop] ([exists]) or [Type]
   ([sig]/[sigT]).
 *)
Ltac mk_end_defer_helper_aux n G mk_exists :=
  transparent_assert G Type;
  [ mk_forall Type Type n ltac:(fun L =>
      let P_ty := fresh "P_ty" in
      transparent_assert P_ty Type;
      [ mk_arrow L Type; exact Prop | simpl in P_ty ];

      let P1 := fresh "P1" in
      let P2 := fresh "P2" in
      refine (forall (P1 P2 : P_ty), _ : Type);
      subst P_ty;

      let H1 := fresh "H1" in transparent_assert H1 Type;
      [ mk_forall_tys L Type ltac:(fun l =>
          refine (_ -> _ : Type);
          [ mk_app P1 l Type | mk_app P2 l Type ]
        )
      | simpl in H1 ];

      refine (H1 -> _ -> Marker.end_defer _ : Type);
      [ mk_exists n ltac:(fun l => mk_app P1 l Prop)
      | mk_exists n ltac:(fun l => mk_app P2 l Prop) ]
   )
  | simpl in G].

Ltac mk_end_defer_helper_Type ids G :=
  let n := ids_nb ids in
  mk_end_defer_helper_aux n G
    ltac:(fun n cont => mk_sigT_sig ids Type cont).

Ltac mk_end_defer_helper_Prop ids G :=
  let n := ids_nb ids in
  mk_end_defer_helper_aux n G
    ltac:(fun n cont => mk_exists ids Prop cont).

(* Dispatch [mk_exists] depending on the type of the goal *)
Ltac mk_end_defer_helper ids :=
  let H := fresh in
  match goal with |- Marker.end_defer ?G =>
    match type of G with
    | Prop => mk_end_defer_helper_Prop ids H
    | _ => mk_end_defer_helper_Type ids H
    end;
    cut H; subst H; [| prove_end_defer_helper ]
  end.

Goal Marker.end_defer nat.
  mk_end_defer_helper (fun x y z : unit => tt).
  intros.
Abort.

Goal Marker.end_defer True.
  mk_end_defer_helper (fun x y z : unit => tt).
Abort.

End MkHelperLemmas.

(******************************************************************************)

(* begin defer [assuming a b...] [in g]

   If [in g] is not specified, a fresh named is used.
*)

Ltac specialize_helper_types H ids :=
  MkHelperLemmas.iter_idents ids ltac:(fun _ =>
    let e := fresh in
    evar (e : Type);
    specialize (H e);
    subst e
  ).

Ltac mkrefine_group ids :=
  lazymatch ids with
  | tt => uconstr:(_)
  | (fun x => _) =>
    let ids' := eval cbv beta in (ids tt) in
    let ret := mkrefine_group ids' in
    uconstr:(fun x => ret)
  end.

Ltac specialize_helper_group H ids :=
  let group_uconstr := mkrefine_group ids in
  let g := fresh in
  refine (let g := group_uconstr in _);
  specialize (H g);
  subst g.

Ltac begin_defer_core g ids :=
  MkHelperLemmas.mk_begin_defer_helper ids;
  let H := fresh in
  intro H;
  specialize_helper_types H ids;
  specialize_helper_group H ids;
  eapply H; clear H;
  [ MkHelperLemmas.iter_idents ids ltac:(fun x => intro x); intro g |].

(* Unfortunately, despite the fact that our core tactic
   [begin_procrastination_core] works for any arity, we have no choice but
   manually exporting it for a given set of arities, as Ltac doesn't expose any
   way of manipulating lists of identifiers.

   See e.g. https://github.com/coq/coq/pull/6081
*)

Tactic Notation "begin" "defer" :=
  let g := fresh "g" in
  begin_defer_core g tt.

Tactic Notation "begin" "defer"
       "in" ident(g) :=
  begin_defer_core g tt.

Tactic Notation "begin" "defer"
       "assuming" ident(a) :=
  let g := fresh "g" in
  begin_defer_core g (fun a : unit => tt).

Tactic Notation "begin" "defer"
       "assuming" ident(a)
       "in" ident(g) :=
  begin_defer_core g (fun a : unit => tt).

Tactic Notation "begin" "defer"
       "assuming" ident(a) ident(b) :=
  let g := fresh "g" in
  begin_defer_core g (fun a b : unit => tt).

Tactic Notation "begin" "defer"
       "assuming" ident(a) ident(b)
       "in" ident(g) :=
  begin_defer_core g (fun a b : unit => tt).

Tactic Notation "begin" "defer"
       "assuming" ident(a) ident(b) ident(c) :=
  let g := fresh "g" in
  begin_defer_core g (fun a b c : unit => tt).

Tactic Notation "begin" "defer"
       "assuming" ident(a) ident(b) ident(c)
       "in" ident(g) :=
  begin_defer_core g (fun a b c : unit => tt).

Tactic Notation "begin" "defer"
       "assuming" ident(a) ident(b) ident(c) ident(d) :=
  let g := fresh "g" in
  begin_defer_core g (fun a b c d : unit => tt).

Tactic Notation "begin" "defer"
       "assuming" ident(a) ident(b) ident(c) ident(d)
       "in" ident(g) :=
  begin_defer_core g (fun a b c d : unit => tt).

Tactic Notation "begin" "defer"
       "assuming" ident(a) ident(b) ident(c) ident(d) ident(e) :=
  let g := fresh "g" in
  begin_defer_core g (fun a b c d e : unit => tt).

Tactic Notation "begin" "defer"
       "assuming" ident(a) ident(b) ident(c) ident(d) ident(e)
       "in" ident(g) :=
  begin_defer_core g (fun a b c d e : unit => tt).

(* Test *)
Goal True.
  begin defer assuming a b in foo.
Abort.

Goal nat.
  begin defer assuming a b in foo.
Abort.

(* defer [in g] *)

(* After unfolding markers, a group is a variable [g] in the context, of type of
   the form [P1 /\ ... /\ Pk /\ ?P], where [P1 ... Pk] are the propositions that
   have been previously procrastinated.

   What [defer] does is instantiating [?P] with [G /\ ?P'], where [G] is
   the current goal, and [?P'] a newly introduced evar. The group now entails
   the current goal, which [defer] proves -- effectively delaying its
   proof.
*)
Ltac defer_aux tm ty :=
  let ty' := (eval hnf in ty) in
  lazymatch ty' with
  | and ?x ?y => defer_aux (@proj2 x y tm) y
  | _ => eapply (proj1 tm)
  end.

Ltac defer_core group :=
  let ty := type of group in
  match ty with
  | Marker.group ?G => defer_aux group G
  end.

Tactic Notation "defer" "in" ident(g) :=
  defer_core g.

Tactic Notation "defer" :=
  let g := Marker.find_group in
  defer in g.

(* defer [H] : E [in g] *)

Tactic Notation "defer" simple_intropattern(H) ":" uconstr(E) "in" ident(g) :=
  assert E as H by defer_core g.

Tactic Notation "defer" ":" uconstr(E) "in" ident(g) :=
  let H := fresh in
  defer H : E in g;
  revert H.

Tactic Notation "defer" simple_intropattern(H) ":" uconstr(E) :=
  let g := Marker.find_group in
  defer H : E in g.

Tactic Notation "defer" ":" uconstr(E) :=
  let g := Marker.find_group in
  defer: E in g.

(* Test *)
Goal True.
  begin defer in foo.
  begin defer in bar.
  assert (1 = 1) by defer. (* goes in group [bar] *)
  defer HH: (2 = 2). (* same result *)
  defer: (3 = 3). intros ?. (* same result, with the result on the goal *)
  defer _: (4 = 4) in foo. (* goes in group [foo] *)
  defer [E1 E2]: (5 = 5 /\ 6 = 6) in foo. (* same result *)
Abort.

(* exploit deferred tac [in g] *)

Ltac deferred_exploit_aux tm ty tac :=
  lazymatch ty with
  | and ?x ?y =>
    try tac (@proj1 x y tm);
    tryif is_evar y then idtac
    else deferred_exploit_aux (@proj2 x y tm) y tac
  end.

Ltac deferred_exploit_core g tac :=
  let ty := type of g in
  match ty with
  | Marker.group ?G => progress (deferred_exploit_aux g G tac)
  end.

Tactic Notation "deferred" "exploit" tactic(tac) "in" ident(g) :=
  deferred_exploit_core g tac.

Tactic Notation "deferred" "exploit" tactic(tac) :=
  let g := Marker.find_group in
  deferred exploit tac in g.

(* Test *)
Goal True.
  begin defer in foo.
  defer ?: (1 + 1 = 2).
  defer L: (forall n, n + 0 = n).
  clear L.
  assert (3 + 0 = 3).
  { deferred exploit (fun H => rewrite H).
    reflexivity. }
Abort.

(* deferred [in g]
   deferred [H] : E [in g]
*)

Ltac deferred_core g :=
  deferred exploit (fun H => generalize H) in g.

Tactic Notation "deferred" "in" ident(g) :=
  deferred_core g.

Tactic Notation "deferred" :=
  let g := Marker.find_group in
  deferred in g.

Tactic Notation "deferred" simple_intropattern(H) ":" uconstr(E) "in" ident(g) :=
  assert E as H; [ deferred in g; try now auto |].

Tactic Notation "deferred" ":" uconstr(E) "in" ident(g) :=
  let H := fresh in
  assert E as H; [ deferred in g; try now auto | revert H ].

Tactic Notation "deferred" simple_intropattern(H) ":" uconstr(E) :=
  let g := Marker.find_group in
  deferred H : E in g.

Tactic Notation "deferred" ":" uconstr(E) :=
  let g := Marker.find_group in
  deferred : E in g.

(* Test *)

Goal True.
  begin defer.
  defer _: (1 + 1 = 2).
  defer _: (1 + 2 = 3).
  deferred. intros _ _.
Abort.

(* Test *)
Goal True.
  begin defer assuming n.
  defer _: (1+2=3).
  defer _: (n + 1 = n).
  deferred ?: (n = n + 1); [].
  deferred: (n + 2 = n).
  { intros. admit. }
  intros ?.
Abort.

(* [end defer] *)

Ltac introv_rec :=
  lazymatch goal with
  | |- (?P -> ?Q) => idtac
  | |- (forall _, _) => intro; introv_rec
  | |- _ => idtac
  end.

Ltac cleanup_conj_goal_aux tm ty :=
  lazymatch ty with
  | and ?x ?y =>
    tryif is_evar y
    then
      (split; [refine tm | exact I])
    else
      (split; [refine (@proj1 x _ tm) | cleanup_conj_goal_aux uconstr:(@proj2 x _ tm) y])
  end.

(* Expose this tactic as it may be useful for procrastination-like setups *)
Ltac cleanup_conj_goal_core :=
  let H_P_clean := fresh "H_P_clean" in
  intro H_P_clean;
  match goal with
  | |- ?P =>
    cleanup_conj_goal_aux H_P_clean P
  end.

(* A tactic to collect the names of the "exists" in from of the goal. This is
   using the neat trick provided in the comment section of
   http://gallium.inria.fr/blog/how-to-quantify-quantifiers-an-ltac-puzzle/ (!)
   which is apparently inspired by Adam Chlipala's book. *)

Ltac collect_exists_ids_loop G ids :=
  lazymatch G with
  | (fun g => exists x, @?body g x) => collect_exists_ids_aux ids x body
  | (fun g => { x & @?body g x }) => collect_exists_ids_aux ids x body
  | (fun g => { x | @?body g x }) => collect_exists_ids_aux ids x body
  | _ => constr:(ids)
  end

with collect_exists_ids_aux ids x body :=
  let G' := constr:(fun (z : _ * _) => body (fst z) (snd z)) in
  let G' := eval cbn beta in G' in
  let ids' := collect_exists_ids_loop G' ids in
  constr:(fun (x : unit) => ids').

Ltac collect_exists_ids g :=
  collect_exists_ids_loop (fun (_:unit) => g) tt.

(* Test for [collect_exists_ids] *)
Goal Marker.end_defer (exists a b c, a + b = c).
  match goal with |- Marker.end_defer ?g =>
    let ids := collect_exists_ids g in
    (* MkHelperLemmas.print_ids ids; *)
    (* prints: a b c *)
    idtac
  end.
Abort.

Goal Marker.end_defer { a & { b & { c | a + b = c } } }.
  match goal with |- Marker.end_defer ?g =>
    let ids := collect_exists_ids g in
    (* MkHelperLemmas.print_ids ids; *)
    (* prints: a b c *)
    idtac
  end.
Abort.

Ltac end_defer_core :=
  match goal with
  |- Marker.end_defer ?g =>
    let ids := collect_exists_ids g in
    MkHelperLemmas.mk_end_defer_helper ids;
    let H := fresh in
    intro H; eapply H; clear H;
    [ introv_rec; cleanup_conj_goal_core | hnf ]
  end.

Tactic Notation "end" "defer" :=
  end_defer_core.

(* Tests *)
Goal True.
  begin defer in g.

  defer H1: (1 + 1 = 2).
  defer H2: (1 + 2 = 3).
  defer H3: (1 + 3 = 4) in g.

  tauto.
  end defer.

  do 3 split.
Qed.

Goal True.
  begin defer assuming a b c.
  assert (a + b = c). defer.
  exact I.

  end defer.
Abort.

Goal nat.
  begin defer assuming a b c.
  assert (a + b = c). defer.
  exact 0.
  end defer.
Abort.

Goal 1= 2 /\ 2=3.
  begin defer.
  defer.
  end defer.
Abort.

(******************************************************************************)

(* Notation for markers *)

(* We print this marker as [end defer], to informally indicate to the user that
   such a goal should always be treated by calling the [end defer] tactic. *)
Notation "'end'  'defer'" :=
  (Marker.end_defer _) (at level 0).

Notation "'Group'  P" :=
  (Marker.group P) (at level 0).
