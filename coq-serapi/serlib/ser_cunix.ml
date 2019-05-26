open Sexplib.Conv

type physical_path = 
  [%import: CUnix.physical_path]
  [@@deriving sexp]