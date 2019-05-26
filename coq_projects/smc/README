This development provides

  - BDD algorithms
  - Symbolic model checker for the modal mu-calculus, using BDDs
  - garbage collector which can be plugged into the previous two parts

together with proofs.

To compile everything type `make'.
To use them type `Require smc'.

Instructions for use
--------------------

The type of BDD configurations is `BDDconfig' which models the memory and the
data structures required for sharing and memoization.
`ad' is the type of memory locations (representing BDD nodes).

  Garbage collection:

The type of garbage collectors is `BDDconfig->(list ad)->BDDconfig'. Most
of the algorithms require a garbage collector as argument. Use `gc_inf'
if you don't want garbage collection. It's correctness is stated by
`gc_inf_OK'. Otherwise use `(gc_x_opt x)' which says that garbage
collection should be done only when all memory locations till x (of type ad)
are full. It's correctness is stated by
`Check gc_x_opt_OK'.

  Tautology checking:

The type of boolean expressions is `bool_expr'.
To build a BDD from a boolean expression use:
   BDDof_bool_expr : (BDDconfig->(list ad)->BDDconfig)->BDDconfig->(list ad)
                     ->bool_expr->BDDconfig*ad
The first argument is the garbage collector. The second is the current
BDD configuration. The third is a list of memory locations (BDDs that we
don't want to be garbage collected.) The output is a new BDD configuration
and the required BDD node.
Similar comments hold for other algorithms.
The correctness lemma is `BDDof_bool_expr_correct'.

To check whether a boolean expression is a tautology use:
  is_tauto : (BDDconfig->(list ad)->BDDconfig)->bool_expr->bool
The correctness lemma is `is_tauto_lemma'.

  Model checking:

See http://www.lsv.ens-cachan.fr/Publis/PAPERS/Ver-dea2000.ps which describes
an older version of the implementation. We give main definitions and lemmas.

The type of mu-calculus formulas is `mu_form'. 
Its semantics as a boolean expression (representing a set of states)
is given by `mu_eval'.  `mu_eval_lemma1' and `mu_eval_lemma2' state
monotonicity and other properties of `mu_eval'. `mu_eval_mu_is_lfp'
states that the `mu' operator is actually interpreted as least fixed
point by `mu_eval'.
`BDDmu_eval' computes the BDD corresponding to a mu-calculus formula. The 
correctness lemma `BDDmu_eval_ok' states the correspondence between `mu_eval'
and `BDDmu_eval'.
`mu_form2set' gives a more abstract semantics of mu-calculus formulae
as sets of states. Here, sets are defined as `Ensemble's from the Sets
library. States, which are supposed to be functions of the type
{0,...,N-1} -> Bool for some constant N, are defined as `Map's from the
IntMap library. Least fixed points are defined using the trick
lfp(f) = {x | \forall X. f(X) \subset X => x \in X}. The correspondence
between 'mu_form2set' and `mu_eval' is stated by `muevaleqset'.

For questions, comments mail Kumar Neeraj Verma (verma@lsv.ens-cachan.fr).
