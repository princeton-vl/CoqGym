type delta_resolver = 
  [%import: Mod_subst.delta_resolver]

let sexp_of_delta_resolver = Serlib_base.sexp_of_opaque ~typ:"Mod_subst.delta_resolver"

type 'a substituted = 
  [%import: 'a Mod_subst.substituted]

let sexp_of_substituted _ = Serlib_base.sexp_of_opaque ~typ:"Mod_subst.substituted"

(*
let sexp_of_substituted f subst = 
  let (_, a) = Mod_subst.repr_substituted subst in
  f a
*)
