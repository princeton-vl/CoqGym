open Sexplib

type ('a, 'b) t = ('a,'b) DAst.t

val sexp_of_t : ('a -> Sexp.t) -> ('b -> Sexp.t) -> ('a, 'b) DAst.t -> Sexp.t
val t_of_sexp : (Sexp.t -> 'a) -> (Sexp.t -> 'b) -> Sexp.t -> ('a, 'b) DAst.t

