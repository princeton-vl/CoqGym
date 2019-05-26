(* Convert hhterm to coqterm *)

open Hh_term
open Coqterms
open Coq_transl_opts

(***************************************************************************************)
(* Check input *)

let is_valid_name name =
  not (is_logop name) && (String.length name < 2 || String.sub name 0 2 <> "$_")
let check_name name = if not (is_valid_name name) then failwith ("check_name: " ^ name) else ()

(***************************************************************************************)
(* Convert input to coqterms *)

let to_coqsort kind =
  match kind with
  | Comb(Id "$Sort", Id "$Prop") -> SortProp
  | Comb(Id "$Sort", Id "$Type") -> SortType
  | Comb(Id "$Sort", Id "$Set") -> if opt_set_to_type then SortType else SortSet
  | _ -> SortType
(* the last case may happen with e.g.: Let U := Type. Variable A : U. Variable x : A. *)

let rec to_coqterm tm =
  let is_fix = function Comb(Id "$Fix", _) -> true | _ -> false
  and is_cofix = function Id "$CoFix" -> true | _ -> false
  in
  match tm with
  | Comb(Comb(Id "$Ind", Id "Coq.Init.Logic.True"), _) ->
    Const("$True")

  | Comb(Comb(Id "$Ind", Id "Coq.Init.Logic.False"), _) ->
    Const("$False")

  | Comb(Comb(Id "$Ind", Id "Coq.Init.Logic.and"), _) ->
    Const("&")

  | Comb(Comb(Id "$Ind", Id "Coq.Init.Logic.or"), _) ->
    Const("|")

  | Comb(Id "$Const", Id "Coq.Init.Logic.not") ->
    Const("~")

  | Comb(Id "$Const", Id "Coq.Init.Logic.iff") ->
    Const("<=>")

  | Comb(Comb(Id "$Ind", Id "Coq.Init.Logic.eq"), _) when opt_translate_eq ->
    Const("=")

  | Comb(Comb(Id "$App", Comb(Comb(Id "$Ind", Id "Coq.Init.Logic.ex"), _)),
         Comb(Comb(Id "$ConstrArray", _),
              Comb(Comb(Comb(Id "$Lambda", Comb(Id "$Name", Id varname)), vartype), body))) ->
    Quant("?", (varname, to_coqterm vartype, to_coqterm body))

  | Comb(Comb(Id "$App", Comb(Id "$Const", Id "Coq.Init.Logic.all")),
         Comb(Comb(Id "$ConstrArray", _),
              Comb(Comb(Comb(Id "$Lambda", Comb(Id "$Name", Id varname)), vartype), body))) ->
    Quant("!", (varname, to_coqterm vartype, to_coqterm body))

  | Comb(Id "$App", Comb(Comb(Id "$Ind", Id "Coq.Init.Logic.ex"), _)) ->
    Const("?")

  | Comb(Id "$Const", Id "Coq.Init.Logic.all") ->
    Const("!")

  | Comb(Id "$Rel", Id num) ->
    Var(num)

  | Comb(Id "$Const", Id name) ->
    check_name name;
    Const(name)

  | Comb(Id "$Var", Id name) ->
    check_name name;
    Const(name)

  | Comb(Comb(Id "$App", left), args) ->
    let rec build_app left args =
      match args with
      | Comb(args2, arg) ->
        App(build_app left args2, to_coqterm arg)
      | Id "$ConstrArray" ->
        to_coqterm left
      | _ ->
        failwith "to_coqterm: build_app"
    in
    build_app left args

  | Comb(Comb(Comb(Id "$Lambda", Comb(Id "$Name", Id varname)), vartype), body) ->
    check_name varname;
    Lam(varname, to_coqterm vartype, to_coqterm body)

  | Comb(Comb(Comb(Comb(Id "$Case", Comb(Comb(Comb(Comb(Id "$CaseInfo",
                                                   Comb(Comb(Id "$Ind", Id indname), _)),
                                                   Id npar), ndecls_arr), nargs_arr)),
                   return_type_lam),
              matched_term), cases) ->
    let rec parse_cases cases nargs_arr acc =
      match cases, nargs_arr with
      | Id "$ConstrArray", Id "$IntArray" -> acc
      | Comb(cases2, c), Comb(nargs_arr2, Id nargs) ->
        parse_cases cases2 nargs_arr2 ((int_of_string nargs, to_coqterm c) :: acc)
      | _ -> failwith "parse_cases"
    in
    check_name indname;
    Case(indname, to_coqterm matched_term, to_coqterm return_type_lam,
         int_of_string npar, parse_cases cases ndecls_arr [])

  | Comb(Comb(Comb(Comb(Id "$LetIn", Comb(Id "$Name", Id varname)), value), vartype), body) ->
    check_name varname;
    Let(to_coqterm value, (varname, to_coqterm vartype, to_coqterm body))

  | Comb(Comb(Id "$Construct", _), Id constrname) ->
    check_name constrname;
    Const(constrname)

  | Comb(Comb(Id "$Cast", trm), ty) ->
    Cast(to_coqterm trm, to_coqterm ty)

  | Comb(Comb(fix_or_cofix, Id result_index),
         Comb(Comb(Comb(Id "$PrecDeclaration", names), types), bodies))
      when
        (is_fix fix_or_cofix || is_cofix fix_or_cofix) ->
    let rec build_lst f (trm : hhterm) acc =
      match trm with
      | Comb(trm2, arg) ->
        build_lst f trm2 ((f arg) :: acc)
      | Id "$ConstrArray" | Id "$NameArray" ->
        acc
      | _ ->
        failwith "to_coqterm: build_lst"
    and name_to_str = function
      | Comb(Id "$Name", Id name) -> check_name name; name
      | _ -> failwith "name_to_str"
    in
    Fix((if is_fix fix_or_cofix then CoqFix else CoqCoFix), int_of_string result_index,
        build_lst name_to_str names [], build_lst to_coqterm types [],
        build_lst to_coqterm bodies [])

  | Comb(Comb(Comb(Id "$Prod", Comb(Id "$Name", Id varname)), vartype), body) ->
    check_name varname;
    Prod(varname, to_coqterm vartype, to_coqterm body)

  | Comb(Id "$Sort", Id "$Prop") ->
    SortProp

  | Comb(Id "$Sort", Id "$Set") ->
    if opt_set_to_type then SortType else SortSet

  | Comb(Id "$Sort", Id "$Type") ->
    SortType

  | Comb(Comb(Id "$Ind", Id indname), _) ->
    check_name indname;
    Const(indname)

  | _ ->
    print_endline (string_of_hhterm tm);
    failwith ("to_coqterm")

let to_coqdef (def : hhdef) (lst : hhdef list) =
  let rec parse_constrs lst cacc =
    match lst with
    | (Comb(Comb(Id "$Construct", _), Id constrname), kind, ty, _) :: t ->
        parse_constrs t (constrname :: cacc)
    | _ -> List.rev cacc
  in
  match def with
  | (Comb(Comb(Id "$Ind", Id indname), Id params_num), kind, ty, _) ->
      let constrs = parse_constrs lst []
      in
      log 2 ("to_coqdef: " ^ indname);
      (indname, IndType(indname, constrs, int_of_string params_num),
       to_coqterm (Lazy.force ty), to_coqsort kind)
  | (Comb(Id "$Const", Id name), Comb(Id "$Sort", Id "$Prop"), ty, _) ->
      log 2 ("to_coqdef (omit proof): " ^ name);
      (name, Const(name), to_coqterm (Lazy.force ty), SortProp)
  | (Comb(Id "$Const", Id name), kind, ty, prf) ->
    begin
      log 2 ("to_coqdef: " ^ name);
      let vp = Lazy.force prf in
      match vp with
      | Id "$Axiom" ->
        (name, Const(name), to_coqterm (Lazy.force ty), to_coqsort kind)
      | _ ->
        (name, to_coqterm vp, to_coqterm (Lazy.force ty), to_coqsort kind)
    end
  | (Comb(Comb(Id "$Construct", _), Id constrname), kind, ty, _) ->
      log 2 ("to_coqdef: " ^ constrname);
      (constrname, Const(constrname), to_coqterm (Lazy.force ty), to_coqsort kind)
  | _ ->
      failwith ("to_coqdef: " ^ get_hhdef_name def)
