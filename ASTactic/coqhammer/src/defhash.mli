(* Definitions hash *)

open Coqterms

val add_lazy : string -> coqdef Lazy.t -> unit
val add : coqdef -> unit
val remove : string -> unit
val clear : unit -> unit
val find : string -> coqdef
val mem : string -> bool
