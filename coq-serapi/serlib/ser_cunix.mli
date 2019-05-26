open Sexplib

type physical_path = CUnix.physical_path

val sexp_of_physical_path : physical_path -> Sexp.t
val physical_path_of_sexp : Sexp.t -> physical_path