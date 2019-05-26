Require Import RelDefinitions.

(** For a [Transitive] and possibly [Symmetric] relation [R], the
  following tactic attempts to use hypotheses from the context to
  prove a goal of the form [R m n] through a simple depth-first graph
  search algorithm as follows.

  We use [m] as the starting node. We maintain a stack of terms [t]
  together with proofs that for any [x], if [R t x] then also [R m x].
  The stack is initialized to [(m, fun x H => H) :: nil]. Then as long
  as the stack is non-empty, pop the first element [(t, Ht)], and for
  every hypothesis of the form [Htt' : R t ?t']:

    - If [t'] is [n], success! Use [Ht t' Htt'].
    - Otherwise, push [(t', fun x Hx => transitivity (Ht t' Htt') Hx)]
      on the stack.

  If the relation is symmetric, repeat with hypotheses of the form
  [R ?t' t], then go on to pop the next element. If the search
  terminates without encountering [n], fail. Once a hypothesis has
  been used, it is "deactivated" so as not to be used again, using the
  following marker. *)

Definition rgraph_done {A B} (R: rel A B) a b := R a b.

(** In addition, we roll our own data structure to make sure we avoid
  any problems related to universe inconsistencies. *)

Inductive rgraph_queue {A} (R: rel A A) (m: A) :=
  | rgraph_queue_nil:
      rgraph_queue R m
  | rgraph_queue_cons x:
      (forall y, R x y -> R m y) ->
      rgraph_queue R m ->
      rgraph_queue R m.

(** Notes: 1. it's not clear that the [not_evar] checks below are
  actually necessary. Nothing here should instantiate any evar. They
  can probably be treated like any other term.  2. Ideally, we
  probably want to do the graph traversal first, then look for
  instances of [Transitive] and [Symmetric], since the number of steps
  in the traversal is bounded by the number of hypotheses, whereas a
  typeclass resolution query is a rather open-ended thing.  3. With
  this in mind, we can likely first do a traversal without symmetry
  and see where we get, then if necessary switch symmetry on at that
  point and try to reach more vertices this way. *)

Ltac rgraph :=
  lazymatch goal with
    | |- ?R ?m ?n =>
      not_evar R;
      not_evar m;
      not_evar n;
      first
        [ assert (Transitive R) by typeclasses eauto
        | fail 1 R "is not declared transitive" ];
      try assert (Symmetric R) by typeclasses eauto;
      let rec step q :=
        lazymatch q with
          | rgraph_queue_cons _ _ ?t ?Ht ?tail =>
            gather tail t Ht
        end
      with gather q t Ht :=
        let push u Htu :=
          let Hu := constr:(fun x Hux => transitivity (z:=x) (Ht u Htu) Hux) in
          gather (rgraph_queue_cons R m u Hu q) t Ht in
        lazymatch goal with
          | Htn : R t n |- _ =>
            exact (Ht n Htn)
          | Hnt : R n t, HRsym: Symmetric R |- _ =>
            exact (Ht n (symmetry (Symmetric := HRsym) Hnt))
          | Htu: R t ?u |- _ =>
            change (rgraph_done R t u) in Htu;
            push u Htu
          | Hut: R ?u t, HRsym: Symmetric R |- _ =>
            change (rgraph_done R u t) in Hut;
            push u (symmetry (Symmetric := HRsym) Hut)
          | _ =>
            step q
        end in
      first
        [ gather (rgraph_queue_nil R m) m (fun x (H: R m x) => H)
        | fail 1 n "not reachable from" m "using hypotheses from the context" ]
    | _ =>
      fail "the goal is not an applied relation"
  end.

(** Hook [rgraph] for providing [RStep]s *)

Hint Extern 30 (RStep ?P (_ _ _)) =>
  solve [ try unify P True; intro; rgraph ] : typeclass_instances.
