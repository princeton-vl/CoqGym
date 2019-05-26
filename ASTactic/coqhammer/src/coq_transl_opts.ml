(* Coq translation options *)

(* higher debug level implies more logging; 0 - no logging; 5 - highest *)
let opt_debug_level = 0
(* should guards be generated from types of free variables?
   opt_closure_guards = true implies opt_lambda_guards = true *)
let opt_closure_guards = ref false
(* should guards be generated from types of lambda-bound variables? *)
let opt_lambda_guards = false
(* should guards be generated for injectivity axioms? *)
let opt_injectivity_guards = false
(* should guards be generated for discrimination axioms? *)
let opt_discrimination_guards = false
(* should Coq.Init.Logic.eq be translated to FOL equality? *)
(* (currently, setting this to false will result in equality being unusable) *)
let opt_translate_eq = true
(* should the arity of constants be optimized as by Paulson & Meng? *)
let opt_arity_optimization = true
(* should arity of constants be optimized even if constant occurs with different arities? *)
let opt_multiple_arity_optimization = true
(* should a zero-arity version of a constant be always generated? *)
let opt_always_zero_arity = true
(* should inversion axioms be added for non-propositional inductive types? *)
let opt_inversion_axioms = true
(* should inversion axioms be added for inductive predicates? *)
let opt_prop_inversion_axioms = true
(* should simplify input? *)
let opt_simpl = true
(* should add induction principles? *)
let opt_induction_principles = false
(* should arity of type predicates be optimized? *)
(* (never combine this with opt_multiple_arity_optimization) *)
let opt_type_optimization = false
(* should predicates be optimized? *)
let opt_predicate_optimization = true
(* should omit typing axioms for propositions? *)
let opt_omit_prop_typing_axioms = false
(* should omit typing axioms for top-level propositions? *)
let opt_omit_toplevel_prop_typing_axioms = true
(* should the typing predicate $HasType be used? *)
(* (requires either opt_multiple_arity_optimization = true or opt_arity_optimization = false) *)
let opt_hastype = true
(* should the inversion axioms be more precise for non-propositional
   inductive types? *)
let opt_precise_inversion = true
(* should guard types be lifted? *)
let opt_type_lifting = true
(* should translate Set to Type? *)
let opt_set_to_type = true

(***************************************************************************************)
(* Debugging *)

let debug n f = if opt_debug_level >= n then f () else ()
let log n str = if opt_debug_level >= n then print_endline str else ()
