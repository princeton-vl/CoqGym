(* Typing and type destruction *)

open Coq_transl_opts
open Coqterms

(***************************************************************************************)
(* Normalization by evaluation *)

type coqvalue =
  N of coqneutral
| PROD of coqterm Lazy.t * coqvalue_abstr
| LAM of coqterm Lazy.t * coqvalue_abstr
| FIX of coqterm Lazy.t * coqvalue Lazy.t
and coqneutral =
| VAR of string
| CONST of string
| APP of coqneutral * coqvalue Lazy.t
| TERM of coqterm Lazy.t
and coqvalue_abstr =  string * coqterm Lazy.t * (coqvalue Lazy.t -> coqvalue)

let rec reify v =
  let rec reify_neutral n =
    match n with
    | VAR x -> Var(x)
    | CONST c -> Const(c)
    | APP (x, y) -> App(reify_neutral x, reify (Lazy.force y))
    | TERM t -> Lazy.force t
  in
  match v with
  | N x -> reify_neutral x
  | PROD(t, _) -> Lazy.force t
  | LAM(t, _) -> Lazy.force t
  | FIX(t, _) -> Lazy.force t

(* evaluation to normal form *)
let eval (tm : coqterm) : coqvalue =
  let rec eval (env : (string * coqvalue Lazy.t) list) (tm : coqterm) : coqvalue =
    debug 5 (fun () -> print_newline (); print_endline "eval"; print_coqterm tm; print_newline ());
    let delay_subst env tm =
      if env = [] then
        lazy tm
      else
        lazy (dsubst (List.map (fun (n, v) -> (n, lazy (reify (Lazy.force v)))) env) tm)
    and delay_eval env tm =
      lazy (eval env tm)
    in
    let eval_abstr env (name, ty, value) =
      (name, delay_subst env ty, (fun x -> eval ((name, x) :: env) value))
    in
    match tm with
    | Var(x) ->
      begin
        try
          Lazy.force (List.assoc x env)
        with Not_found ->
          N (VAR(x))
      end
    | Const(c) ->
      begin
        let tm2 = try coqdef_value (Defhash.find c) with _ -> tm
        in
        if tm2 = tm then
          N (CONST c)
        else
          match tm2 with
          | IndType(_) ->
              N (CONST c)
          | _ ->
              eval [] tm2
      end
    | App(x, y) ->
      let rec apply x y =
        match x with
        | LAM(_, (_, _, f)) -> f y
        | FIX(_, v) -> apply (Lazy.force v) y
        | N x2 -> N (APP(x2, y))
        | _ -> failwith "apply"
      in
      apply (eval env x) (delay_eval env y)
    | Cast(x, y) ->
      eval env x
    | Lam a ->
      LAM(delay_subst env tm, eval_abstr env a)
    | Prod a ->
      PROD(delay_subst env tm, eval_abstr env a)
    | Let(value, (vname, ty, body)) ->
      eval ((vname, delay_eval env value) :: env) body
    | Case(indname, matched_term, return_type, params_num, branches) ->
      let rec eval_valapp v args =
        match args with
        | h :: t ->
          begin
            match v with
            | LAM(_, (_, _, f)) -> eval_valapp (f h) t
            | N n -> eval_valapp (N (APP(n, h))) t
            | _ -> failwith "eval_app"
          end
        | [] -> v
      and flatten_valapp v =
        let rec hlp n acc =
          match n with
          | (APP(x, y)) ->
            hlp x (y :: acc)
          | _ ->
            (N n, acc)
        in
        match v with
        | N n -> hlp n []
        | _ -> (v, [])
      in
      begin
        let mt2 = eval env matched_term
        in
        try
          begin
            let (v, args) = flatten_valapp mt2
            and (_, IndType(_, constrs, _), indtype, indsort) =
              try Defhash.find indname with _ -> raise Not_found
            in
            match v with
            | (N (CONST c)) when List.mem c constrs ->
              let i = Hhlib.index c constrs
              in
              let (n, b) = List.nth branches i
              in
              if List.length args > n + params_num then
                begin
                  print_coqterm tm;
                  print_list print_string constrs;
                  print_int i; print_newline ();
                  print_int n; print_newline ();
                  print_int params_num; print_newline ();
                  failwith ("eval: bad number of constructor arguments: " ^ c)
                end
              else
                eval_valapp (eval env b) (Hhlib.drop params_num args)
            | _ ->
              N (TERM (delay_subst env
                         (Case(indname, reify mt2, return_type, params_num, branches))))
          end
        with Not_found ->
          N (TERM (delay_subst env
                     (Case(indname, reify mt2, return_type, params_num, branches))))
      end
    | Fix(cft, k, names, types, bodies) ->
      let rec mkenv m lst acc =
        match lst with
        | h :: t ->
            let fx = Fix(cft, m, names, types, bodies)
            in
            let v =
              if cft = CoqFix then
                lazy (FIX(delay_subst env fx, delay_eval env fx))
              else
                lazy (N (TERM (delay_subst env fx)))
            in
            mkenv (m + 1) t ((h, v) :: acc)
        | [] ->
            acc
      in
      FIX(delay_subst env tm, lazy (eval (mkenv 0 names env) (List.nth bodies k)))
    | _ ->
      N (TERM (delay_subst env tm))
  in
  eval [] tm

(***************************************************************************************)
(* Limited typechecking *)

let rec check_prop args ctx tm =
  let is_prop_tgt args ty =
    let rec hlp args v =
      match v with
      | PROD(_, (_, _, f)) ->
          begin
            match args with
            | h :: args2 ->
                hlp args2 (f (lazy (eval h)))
            | _ ->
                false
          end
      | FIX(_, v2) ->
          hlp args (Lazy.force v2)
      | N (TERM tm) ->
          if args = [] then
            Lazy.force tm = SortProp
          else
            false
      | _ ->
          false
    in
    hlp args (eval ty)
  in
  debug 4 (fun () -> print_header "check_prop" tm ctx);
  match tm with
  | Var(x) ->
      begin
        try
          is_prop_tgt args (List.assoc x ctx)
        with Not_found ->
          print_list (fun (name, _) -> print_string name) (List.rev ctx);
          failwith ("check_prop: var not found: " ^ x)
      end
  | Const(c) ->
      begin
        try
          is_prop_tgt args (coqdef_type (Defhash.find c))
        with _ ->
          false
      end
  | App(x, y) ->
      check_prop (y :: args) ctx x
  | Lam(vname, ty, body) ->
      begin (* NOTE: the lambda case is incomplete, but this should be enough in practice *)
        match args with
        | _ :: args2 ->
            check_prop args2 ((vname, ty) :: ctx) body
        | _ ->
            false
      end
  | Prod(vname, ty1, ty2) ->
      if args = [] then
        check_prop [] ((vname, ty1) :: ctx) ty2
      else
        false
  | Cast(v, ty2) ->
      is_prop_tgt args ty2
  | Case(indname, matched_term, return_type, params_num, branches) ->
      (* NOTE: this is incorrect if `params_num' is smaller than the
         number of arguments of the inductive type `indname' *)
      is_prop_tgt args (App(return_type, matched_term))
  | Fix(_, k, names, types, bodies) ->
      is_prop_tgt args (List.nth types k)
  | Let(value, (name, ty, body)) ->
      check_prop args ctx (dsubst [(name, lazy (Cast(value, ty)))] body)
  | SortProp | SortSet | SortType ->
      false
  | Quant(_) | Equal(_) ->
      args = []
  | _ ->
      failwith "check_prop"

let check_prop ctx tm =
  match tm with
  | App(Const("~"), _) -> true
  | App(App(Const(c), _), _) when is_bin_logop c -> true
  | _ -> check_prop [] ctx tm

let check_proof_var ctx name =
  let rec pom ctx name =
    match ctx with
    | (n, ty) :: ctx2 when n = name ->
      check_prop ctx2 ty
    | _ :: ctx2 ->
      pom ctx2 name
    | _ ->
      failwith "check_proof_var"
  in
  pom ctx name

let check_type_target_is_prop ty =
  let rec hlp v =
    match v with
    | PROD(_, (name, _, f)) ->
      hlp (f (lazy (N (VAR name))))
    | FIX(_, v2) ->
      hlp (Lazy.force v2)
    | N (TERM tm) ->
      Lazy.force tm = SortProp
    | _ ->
      false
  in
  hlp (eval ty)

let check_type_target_is_type ty =
  let rec hlp v =
    match v with
    | PROD(_, (name, _, f)) ->
      hlp (f (lazy (N (VAR name))))
    | FIX(_, v2) ->
      hlp (Lazy.force v2)
    | N (TERM tm) ->
      let tm2 = Lazy.force tm
      in
      tm2 = SortSet || tm2 = SortType
    | _ ->
      false
  in
  hlp (eval ty)

let destruct_type_eval ty =
  let rec hlp v acc =
    match v with
    | PROD(_, (name, ty, f)) ->
      let name2 = refresh_varname name
      in
      hlp (f (lazy (N (VAR name2))))
        ((name2, refresh_bvars (Lazy.force ty)) :: acc)
    | FIX(_, v2) -> hlp (Lazy.force v2) acc
    | _ -> (v, List.rev acc)
  in
  hlp (eval ty) []

let destruct_type ty =
  let (x, y) = destruct_type_eval ty
  in
  (reify x, y)

let destruct_type_app ty =
  let (target, cargs) = destruct_type ty
  in
  let (tgt, targs) = flatten_app target
  in
  (tgt, targs, cargs)

let get_type_args ty = snd (destruct_type_eval ty)
let get_type_target ty = fst (destruct_type ty)
let get_type_app_target ty = let (t, _, _) = destruct_type_app ty in t
