
open Hh_term
open Coqterms

(* convert hhterm to coqterm *)
val to_coqdef : hhdef (* def *) -> hhdef list (* future def list *) -> coqdef
