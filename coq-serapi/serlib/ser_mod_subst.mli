open Sexplib

type delta_resolver = Mod_subst.delta_resolver

val sexp_of_delta_resolver : delta_resolver -> Sexp.t

type 'a substituted = 'a Mod_subst.substituted

val sexp_of_substituted : ('a -> Sexp.t) -> 'a substituted -> Sexp.t