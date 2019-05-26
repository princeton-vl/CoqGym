open Sexplib.Conv

type multi =
  [%import: Equality.multi]
  [@@deriving sexp]
