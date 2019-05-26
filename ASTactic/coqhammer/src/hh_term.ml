type hhterm =
   Id of string (* may be a constant or variable *)
 | Comb of hhterm * hhterm

type hhdef =
  hhterm (* "name" term; use get_hhdef_name to extract the name string *) *
    hhterm (* kind; Comb(Id "$Sort", Id "$Prop") if type is a proposition *) *
    hhterm Lazy.t (* type *) *
    hhterm Lazy.t (* term: definiens (value or proof term) *)

let get_hhterm_name (c : hhterm) : string =
  match c with
  | Comb(Comb(Id "$Construct", _), Id constrname) ->
    constrname
  | Comb(Id "$Const", Id name) ->
    name
  | Comb(Comb(Id "$Ind", Id indname), _) ->
    indname
  | Comb(Id "$Var", Id name) ->
    name
  | _ ->
    ""

let get_hhdef_name ((c, _, _, _) : hhdef) : string =
  get_hhterm_name c

let rec string_of_hhterm t =
  match t with
  | Id(s) -> s
  | Comb(x, y) -> string_of_hhterm x ^ " @ (" ^ string_of_hhterm y ^ ")"
