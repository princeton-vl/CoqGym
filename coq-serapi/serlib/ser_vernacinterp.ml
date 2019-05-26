open Sexplib.Conv

type deprecation =
  [%import: Vernacinterp.deprecation]
  [@@deriving sexp]
