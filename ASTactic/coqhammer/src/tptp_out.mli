open Coqterms

(* write an already translated problem to FOF TPTP format *)
val write_fol_problem : (string -> unit) (* output function *) ->
  fol_axioms (* axioms *) -> (string (* name *) * fol (* formula *)) (* goal *) ->
  unit
