# Tactics Reference

- `begin defer [assuming a b...] [in g]`

  Start a "defer" block. If `group g` is provided, give name `g` to
  the hypothesis of type `Group` introduced. If `assuming a b...` (where `a`,
  `b`, ... are one or several user-provided names) is provided, also introduce
  in the context abstract variables of the same names.

- `defer [in g]`

  Discharge the current sub-goal, deferring it for later. If `in g` is
  provided, store it in the hypothesis `g` which must be of type `Group ...`. If
  `in g` is not provided, the tactic picks the hypothesis of type `Group ...`
  which has been introduced last (if there are several).

  The sub-goal being differed has to make sense in the context of the `Group` it
  is stored in (which is the context of the `begin defer` that introduced the
  `Group`). Otherwise Coq will raise an error involving the context of the evar
  in the `Group`.

- `defer [H]: E [in g]`

  Introduces a new assumption `E`, named after `H`, and defer its proof in `g`.
  This is equivalent to `assert E as H by (defer in g)`.

  If `H` is not provided, adds `E` in front of the goal instead of adding it to
  the context -- i.e. on a goal `G`, `defer: E` produces a goal `E -> G`.

- `end defer`

  To be called on a `end defer` goal. It does some cleanup and gives back the
  variables and side-goals that have been procrastinated.

- `deferred [in g]`

  Adds to the goal all the already deferred propositions. I.e. on a goal `G`,
  gives back a goal `X1 -> .. -> Xn -> E`, where `X1`..`Xn` are the already
  deferred propositions.

- `deferred [H]: E [in g]`

  Adds an assumption `E` to the context, named after `H`, and produces a subgoal
  `X1 -> .. -> Xn -> E`, where `X1`..`Xn` are the already deferred propositions.
  As a convenience feature, when `E` is trivially provable from `X1`..`Xn`, this
  subgoal is automatically discharged using `auto`.

  This is equivalent to `assert E as H; [ deferred in g; try now auto |]`.

  If `H` is not provided, adds `E` in front of the goal instead of adding it to
  the context.

- `exploit deferred tac [in g]`

  This allows iterating a user-provided tactic `tac` on the propositions stored
  in the group `g`. It is fine for `tac` to fail for some of the propositions.
  The whole tactic (`exploit deferred tac`) will fail if `tac` did not make the
  proof progress overall (i.e. if nothing happened).

  For example, to try rewriting with all deferred facts, one would do
  `exploit deferred (fun H => rewrite H)`.
