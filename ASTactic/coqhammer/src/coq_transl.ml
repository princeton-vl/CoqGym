(* Translation from Coq to FOL *)

(* TODO: *)
(* 1. Omit (some) type arguments (inductive type parameters?) to
   polymorphic functions/constructors (e.g. cons). *)
(* 2. Omit (some) type guards when the type may be inferred (e.g.
   forall x : nat, Even(x) -> phi probably may be translated to
   forall x, Even(x) -> phi', because Even(x) implies nat(x)). *)
(* 3. Heuristic monomorphisation (instantiation of polymorphic
   definitions with types). *)

open Coqterms
open Coq_transl_opts
open Hh_term

(***************************************************************************************)
(* Adjust variable names *)

let adjust_varnames =
  let rename_abs n (vname, ty, body) =
    (string_of_int n ^ "_" ^ vname, ty, body)
  in
  map_coqterm0
    begin fun n ctx tm ->
      match tm with
      | Var(x) ->
        let i = int_of_string x - 1
        in
        let nthctx = List.nth ctx i
        in
        let vname = fst nthctx
        in
        Var(string_of_int (n - 1 - i) ^ "_" ^ vname)
      | Lam a ->
          Lam (rename_abs n a)
      | Prod a ->
          Prod (rename_abs n a)
      | Quant(op, a) ->
          Quant(op, rename_abs n a)
      | Let(value, a) ->
          Let(value, rename_abs n a)
      | Fix(cft, m, names, types, bodies) ->
          let names2 =
            List.rev
              (fst
                 (List.fold_left
                    (fun (acc, k) name -> ((string_of_int k ^ "_" ^ name) :: acc, k + 1))
                    ([], n)
                    names))
          in
          Fix(cft, m, names2, types, bodies)
      | _ ->
          tm
    end

(***************************************************************************************)
(* Adjust logical operators *)

let adjust_logops =
  map_coqterm
    begin fun ctx tm ->
      match tm with
      | App(Const(op), Lam a) when op = "!" || op = "?" ->
        Quant(op, a)
      | App(App(App(Const("="), ty), x), y) ->
        Equal(x, y)
      | _ ->
        tm
    end

(***************************************************************************************)
(* Initialization *)

let reinit (lst : hhdef list) =
  let conv h t =
    let def = Coq_convert.to_coqdef h t in
    let def = coqdef_map adjust_varnames def in
    let def = coqdef_map adjust_logops def in
    if opt_simpl then
      coqdef_map simpl def
    else
      def
  in
  let rec add_defs lst =
    match lst with
    | h :: t ->
      let name = get_hhdef_name h in
      if not (Defhash.mem name) then
        Defhash.add_lazy name (lazy (conv h t));
      add_defs t
    | [] ->
        ()
  in
  log 1 "Reinitializing...";
  let hastype_type = mk_fun_ty (Const("$Any")) (mk_fun_ty SortType SortProp) in
  begin
    try
      List.iter Defhash.add logop_defs;
      if opt_hastype then
        Defhash.add ("$HasType", Const("$HasType"), hastype_type, SortType)
    with _ -> ()
  end;
  add_defs lst

(***************************************************************************************)
(* Axioms monad *)

(* the second element is a function which given a list of axioms
   prepends to it a fixed list of axioms (in time proportional to the
   prepended list) and returns the result *)
type 'a axioms_monad = 'a * ((string * fol) -> (string * fol))

let return tm = (tm, fun axs -> axs)
let bind (x, mk1) f =
  let (y, mk2) = f x
  in
  (y, (fun axs -> mk2 (mk1 axs)))

let (>>=) = bind
let (>>) m1 m2 = bind m1 (fun _ -> m2)
let lift f m = m >>= fun x -> return (f x)

let listM_nth lst n =
  let rec pom lst n acc x =
    match lst with
    | [] -> return x
    | h :: t ->
       if n = 0 then
         begin
           acc >> h >>= fun r ->
           pom t (n - 1) (return r) r
         end
       else
         pom t (n - 1) (acc >> h) x
  in
  match lst with
  | [] -> failwith "listM_nth"
  | h :: t ->
     begin
       h >>= fun r ->
       pom t n (return r) r
     end

let add_axiom ax =
  log 3 ("add_axiom: " ^ fst ax);
  ((), fun axs -> ax :: axs)

let extract_axioms m = (snd m) []

(* general axioms for any Coq translation *)
let coq_axioms = [
  ("_HAMMER_COQ_TRUE", Const("$True"));
  ("_HAMMER_COQ_FALSE", App(Const("~"), Const("$False")));
  ("_HAMMER_COQ_TYPE_TYPE", mk_hastype (Const("Type")) (Const("Type")))
] @
  if opt_set_to_type then
    []
  else
    [
      ("_HAMMER_COQ_SET_TYPE", mk_hastype (Const("Set")) (Const("Type")));
      ("_HAMMER_COQ_SET_SUB_TYPE",
       mk_forall "X" type_any
         (mk_impl
            (mk_hastype (Var("X")) (Const("Set")))
            (mk_hastype (Var("X")) (Const("Type")))))
    ]

(***************************************************************************************)
(* Coqterms hash *)

let coqterm_hash = Hashing.create lift

(***************************************************************************************)
(* Inversion axioms for inductive types *)

let mk_inversion_conjs params_num args targs cacc =
  let rec mk_conjs ctx args targs cacc =
    match args, targs with
    | ((name, ty) :: args2), (y :: targs2) ->
      let cacc2 =
        if Coq_typing.check_prop ctx ty then
          cacc
        else
          (mk_eq (Var(name)) y) :: cacc
      in
      mk_conjs ((name, ty) :: ctx) args2 targs2 cacc2
    | [], [] ->
      if cacc = [] then
        Const("$True")
      else
        join_right mk_and cacc
    | _ ->
      failwith "mk_inversion_conjs"
  in
  let args2 = Hhlib.drop params_num args
  and ctx = List.rev (Hhlib.take params_num args)
  in
  mk_conjs ctx args2 targs cacc

let rec subst_params lst prms tm =
  match lst with
  | [] -> tm
  | (name, _) :: t ->
    let tm2 = subst_params t (List.tl prms) tm
    in
    if var_occurs name tm2 then
      substvar name (List.hd prms) tm2
    else
      tm2

let mk_inversion params indname constrs matched_term f =
  let rec mk_disjs constrs acc =
    match constrs with
    | cname :: constrs2 ->
      let (_, targs, cargs) = Coq_typing.destruct_type_app (coqdef_type (Defhash.find cname))
      in
      let params_num = List.length params
      in
      let cargs1 = Hhlib.take params_num cargs
      in
      let cargs2 =
        List.map
          (fun (name, ty) -> (name, subst_params cargs1 params ty))
          (Hhlib.drop params_num cargs)
      in
      let targs2 =
        List.map
          (fun tm -> subst_params cargs1 params tm)
          (Hhlib.drop params_num targs)
      in
      let eqt = mk_eq matched_term (mk_long_app (Const(cname)) (params @ mk_vars cargs2))
      in
      let disj = mk_long_exists cargs2 (f cname targs2 cargs2 eqt)
      in
      mk_disjs constrs2 (disj :: acc)
    | [] -> List.rev acc
  in
  let disjs = mk_disjs constrs []
  in
  match disjs with
  | [] -> Const("$False")
  | _ -> join_right mk_or disjs

let mk_prop_inversion params indname args constrs =
  let rec mk_disjs constrs acc =
    match constrs with
    | cname :: constrs2 ->
      let ty = coqdef_type (Defhash.find cname)
      in
      let (_, targs, cargs) = Coq_typing.destruct_type_app ty
      in
      let params_num = List.length params
      in
      let cargs1 = Hhlib.take params_num cargs
      in
      let cargs2 =
        List.map
          (fun (name, ty) -> (name, subst_params cargs1 params ty))
          (Hhlib.drop params_num cargs)
      in
      let targs2 =
        List.map
          (fun tm -> subst_params cargs1 params tm)
          (Hhlib.drop params_num targs)
      in
      let disj =
        mk_long_exists cargs2
          (mk_inversion_conjs params_num args targs2 [])
      in
      mk_disjs constrs2 (disj :: acc)
    | [] -> List.rev acc
  in
  if args = [] then
    begin
      if constrs = [] then
        Const("$False")
      else
        Const("$True")
    end
  else
    let disjs = mk_disjs constrs []
    in
    match disjs with
    | [] -> Const("$False")
    | _ -> join_right mk_or disjs

let rec mk_guards ctx vars tm =
  match vars with
  | (name, ty) :: vars2 ->
     if Coq_typing.check_prop ctx ty then
       (mk_impl ty
          (mk_guards ((name, ty) :: ctx) vars2 (subst_proof name ty tm)))
     else
       (mk_impl (App(App(Const("$HasType"), Var(name)), ty))
          (mk_guards ((name, ty) :: ctx) vars2 tm))
  | [] ->
     tm

(* The following mutually recursively defined functions return
   (coqterm axioms_monad) or (unit axioms_monad). *)

let rec add_inversion_axioms0 mkinv indname axname fvars lvars constrs matched_term f =
  (* Note: the correctness of calling `prop_to_formula' below
     depends on the implementation of `convert_term' (that it
     never invokes check_prop on an application of the form
     App(..App(Const(cname),_)..)) *)
  let inv = mkinv indname constrs matched_term f
  in
  match inv with
  | Const("$False") -> return ()
  | _ ->
     let m =
       if !opt_closure_guards then
         close (fvars @ lvars)
           (fun ctx -> prop_to_formula ctx inv)
       else if opt_lambda_guards then
         let ctx = List.rev fvars
         in
         let mtfvars = get_fvars ctx matched_term
         in
         let fvars0 =
           List.filter (fun (name, _) -> not (List.mem_assoc name mtfvars)) fvars
         and fvars1 = mtfvars
         in
         (close fvars0
            (fun ctx1 ->
              make_guarded_forall ctx1 fvars1
                (fun _ -> prop_to_formula ctx (mk_long_forall lvars inv))))
       else
         let vars = fvars @ lvars
         in
         let ctx = List.rev vars
         in
         let vars1 = get_fvars ctx matched_term
         in
         make_fol_forall [] vars (mk_guards [] vars1 inv)
     in
     m >>= fun tm -> add_axiom (mk_axiom axname tm)

(***************************************************************************************)
(* Lambda-lifting, fix-lifting and case-lifting *)

and lambda_lifting axname name fvars lvars1 tm =
  debug 3 (fun () -> print_header "lambda_lifting" tm (fvars @ lvars1));
  let rec extract_lambdas tm acc =
    match tm with
    | Lam(vname, vtype, body) -> extract_lambdas body ((vname, vtype) :: acc)
    | _ -> (List.rev acc, tm)
  in
  let (lvars2, body2) = extract_lambdas tm []
  in
  let lvars = lvars1 @ lvars2
  in
  match body2 with
  | Fix(_) ->
     fix_lifting axname name fvars lvars body2
  | Case(_) ->
     case_lifting axname name fvars lvars body2
  | _ ->
     close fvars
       begin fun ctx ->
         let mk_eqv =
           if Coq_typing.check_prop (List.rev_append lvars ctx) body2 then
             mk_equiv
           else
             mk_eq
         in
         let eqv = mk_eqv (mk_long_app (Const(name)) (mk_vars (fvars @ lvars))) body2
         in
         if !opt_closure_guards || opt_lambda_guards then
           prop_to_formula ctx (mk_long_forall lvars eqv)
         else
           make_fol_forall ctx lvars eqv
       end
     >>=
     (fun tm -> add_axiom (mk_axiom axname tm))
     >>
     convert (List.rev fvars) (mk_long_app (Const(name)) (mk_vars fvars))

and fix_lifting axname dname fvars lvars tm =
  debug 3 (fun () -> print_header "fix_lifting" tm (fvars @ lvars));
  match tm with
  | Fix(cft, k, names, types, bodies) ->
      let fix_pref = "$_fix_" ^ unique_id () ^ "_"
      in
      let names1 = List.map ((^) fix_pref) names
      in
      let names2 =
        if axname = "" then names1 else Hhlib.take k names1 @ [ dname ] @ Hhlib.drop (k + 1) names1
      and axnames =
        if axname = "" then names1 else Hhlib.take k names1 @ [ axname ] @ Hhlib.drop (k + 1) names1
      in
      let vars = mk_vars (fvars @ lvars)
      in
      let env = List.map2 (fun name name2 -> (name, mk_long_app (Const(name2)) vars)) names names2
      in
      let prep body =
        List.fold_left (fun tm (name, value) -> simple_subst name value tm) body env
      in
      List.iter2
        (fun name2 ty ->
          let ty2 = mk_long_prod fvars (mk_long_prod lvars ty)
          in
          try
            Defhash.add (mk_def name2 (Const(name2)) ty2
                           (if Coq_typing.check_prop [] ty2 then SortProp else SortType))
          with _ -> ())
        names2 types;
      listM_nth
        (List.map2
           (fun (axname2, name2) body ->
             lambda_lifting axname2 name2 fvars lvars (prep body))
           (List.combine axnames names2)
           bodies)
        k
  | _ ->
      failwith "fix_lifting"

and case_lifting axname0 name0 fvars lvars tm =
  debug 3 (fun () -> print_header "case_lifting" tm (fvars @ lvars));
  let get_params indty rt params_num =
    let args = Coq_typing.get_type_args indty
    in
    let rec pom n tm =
      match tm with
      | Lam(_, ty, body) ->
        if n = 0 then
          let (_, tyargs) = flatten_app ty
          in
          assert (List.length tyargs >= params_num);
          Hhlib.take params_num tyargs
        else
          pom (n - 1) body
      | _ -> failwith "get_params"
    in
    let n = List.length args
    in
    assert (n >= params_num);
    pom (n - params_num) rt
  in
  let generic_match () =
    let name = "$_case_" ^ unique_id ()
    in
    let def = (name, Const(name), Const("$Any"), SortType)
    in
    Defhash.add def;
    Const(name)
  in
  try
    begin
      match tm with
      | Cast(Const("$Proof"), _) | Const("$Proof") ->
         return (generic_match ())
      | Case(indname, matched_term, return_type, params_num, branches) ->
        let (_, IndType(_, constrs, pnum), indty, _) =
          try Defhash.find indname with _ -> raise Not_found
        in
        assert (pnum = params_num);
        if Coq_typing.check_type_target_is_prop indty then
          return (generic_match ())
        else
          let fname = if name0 = "" then "$_case_" ^ indname ^ "_" ^ unique_id () else name0
          in
          let axname = if name0 = "" then fname else axname0
          in
          convert (List.rev fvars) (mk_long_app (Const(fname)) (mk_vars fvars))
          >>=
          fun case_replacement ->
          let case_repl2 = mk_long_app case_replacement (mk_vars lvars)
          in
          let params = get_params indty return_type params_num
          in
          let rec hlp constrs branches params params_num vars tm =
            let rec get_branch cname cstrs brs =
              match cstrs, brs with
              | c :: cstrs2, b :: brs2 ->
                if c = cname then
                  b
                else
                  get_branch cname cstrs2 brs2
              | _ -> failwith "case_lifting: get_branch"
            in
            begin fun cname _ args eqt ->
              let (n, branch) = get_branch cname constrs branches
              in
              assert (List.length args <= n);
            (* We may have List.length args < n if there are some lets
               in the type and they get evaluated away. We do not
               properly deal with this (rare) situation: the generated
               formula will in this case not be correct (the branch
               (`cr' below) will miss arguments). *)
              let ctx = List.rev (vars @ args)
              in
              let ys = mk_vars args
              in
              let cr = simpl (mk_long_app branch ys)
              in
              match cr with
              | Case(indname2, mt2, return_type2, pnum2, branches2) ->
                let (_, IndType(_, constrs2, pn), indty2, _) =
                  try Defhash.find indname2 with _ -> raise Not_found
                in
                assert (pn = pnum2);
                if Coq_typing.check_type_target_is_prop indty2 then
                  eqt
                else
                  let params2 = get_params indty2 return_type2 pnum2
                  in
                  mk_guards []
                    (get_fvars ctx mt2)
                    (mk_and eqt (mk_inversion params2 indname constrs2 mt2
                                   (hlp constrs2 branches2 params2 pnum2 (vars @ args) cr)))
              | _ ->
                let eqv =
                  if Coq_typing.check_prop ctx cr then
                    mk_equiv case_repl2 cr
                  else
                    mk_eq case_repl2 cr
                in
                mk_and eqt eqv
            end
          in
          add_inversion_axioms0
            (mk_inversion params) indname axname fvars lvars constrs matched_term
            (hlp constrs branches params params_num (fvars @ lvars) tm)
          >>
          return case_replacement
      | _ ->
        failwith "case_lifting"
    end
  with Not_found ->
    log 2 ("case exception: " ^ name0);
    return (generic_match ())

(*****************************************************************************************)
(* Convert definitions to axioms *)

(* Invariant: there is no variable covering in `tm'; the variables
   from ctx are pairwise distinct and they do not occur bound in `tm' *)
and convert ctx tm =
  debug 3 (fun () -> print_header "convert" tm ctx);
  match tm with
  | Quant(op, (name, ty, body)) ->
     assert (ty <> type_any);
     let mk = if op = "!" then mk_impl else mk_and
     in
     if Coq_typing.check_prop ctx ty then
       (prop_to_formula ctx ty) >>= fun x1 ->
       (prop_to_formula ctx (subst_proof name ty body)) >>= fun x2 ->
       return (mk x1 x2)
     else
       (make_guard ctx ty (Var(name))) >>= fun x1 ->
       (prop_to_formula ((name, ty) :: ctx) body) >>= fun x2 ->
       return (Quant(op, (name, type_any, mk x1 x2)))
  | Equal(x, y) ->
     convert_term ctx x >>= fun x1 ->
     convert_term ctx y >>= fun x2 ->
     return (Equal(x1, x2))
  | App(App(Const(c), x), y) when is_bin_logop c ->
      prop_to_formula ctx x >>= fun x2 ->
      prop_to_formula ctx y >>= fun y2 ->
      assert (x2 <> Const("$Proof"));
      assert (y2 <> Const("$Proof"));
      return (App(App(Const(c), x2), y2))
  | App(Const("~"), x) ->
      prop_to_formula ctx x >>= fun x2 ->
      assert (x2 <> Const("$Proof"));
      return (App(Const("~"), x2))
  | App(App(Const("$HasType"), x), y) ->
      convert ctx x >>= fun x2 ->
      make_guard ctx y x2
  | App(x, y) ->
      convert ctx x >>= fun x2 ->
      if x2 = Const("$Proof") then
        return (Const("$Proof"))
      else
        convert_term ctx y >>= fun y2 ->
        if y2 = Const("$Proof") then
          return x2
        else
          return (App(x2, y2))
  | Lam(_) ->
      remove_lambda ctx tm
  | Case(_) ->
      remove_case ctx tm
  | Cast(Const("$Proof"), _) ->
      return (Const("$Proof"))
  | Cast(_) ->
      remove_cast ctx tm
  | Fix(_) ->
      remove_fix ctx tm
  | Let(_) ->
      remove_let ctx tm
  | Prod(_) ->
      if Coq_typing.check_prop ctx tm then
        prop_to_formula ctx tm
      else
        remove_type ctx tm
  | SortProp ->
      return (Const("Prop"))
  | SortSet ->
      return (Const("Set"))
  | SortType ->
      return (Const("Type"))
  | Var(name) ->
      if Coq_typing.check_proof_var ctx name then
        return (Const("$Proof"))
      else
        return (Var(name))
  | Const(_) ->
      return tm
  | IndType(_) ->
      failwith "convert"

and convert_term ctx tm =
  debug 3 (fun () -> print_header "convert_term" tm ctx);
  let should_lift =
    match tm with
    | Var(_) | Const(_) -> false
    | App(App(Const(c), _), _) when is_bin_logop c -> true
    | App(Const("~"), _) -> true
    | App(_) -> false
    | _ -> Coq_typing.check_prop ctx tm
  in
  if should_lift then
    let name = "$_prop_" ^ unique_id ()
    in
    let fvars = get_fvars ctx tm
    in
    convert ctx (mk_long_app (Const(name)) (mk_vars fvars)) >>= fun tm2 ->
    close fvars
      begin fun ctx ->
        convert ctx tm >>= fun r ->
        return (mk_equiv tm2 r)
      end >>= fun r ->
    add_axiom (mk_axiom name r) >>
    return tm2
  else
    convert ctx tm

and prop_to_formula ctx tm =
  debug 3 (fun () -> print_header "prop_to_formula" tm ctx);
  match tm with
  | Prod(vname, ty1, ty2) ->
     if Coq_typing.check_prop ctx ty1 then
       prop_to_formula ctx ty1 >>= fun tm1 ->
       prop_to_formula ctx (subst_proof vname ty1 ty2) >>= fun tm2 ->
       return (mk_impl tm1 tm2)
     else
       make_guard ctx ty1 (Var(vname)) >>= fun tm1 ->
       prop_to_formula ((vname, ty1) :: ctx) ty2 >>= fun tm2 ->
       return (mk_forall vname type_any (mk_impl tm1 tm2))
  | _ ->
    convert ctx tm

(* `x' does not get converted *)
and make_guard ctx ty x =
  debug 3 (fun () -> print_header_nonl "make_guard" ty ctx; print_coqterm x; print_newline ());
  match ty with
  | Prod(_) ->
     if opt_type_lifting then
       remove_type ctx ty >>= fun ty1 ->
       return (mk_hastype x ty1)
     else
       (* refresh_bvars is necessary here to correctly translate
          e.g. Prod(x, Prod(x, ty1, ty2), ty3) *)
       type_to_guard ctx (refresh_bvars ty) x
  | _ ->
     convert ctx ty >>= fun ty1 ->
     return (mk_hastype x ty1)

(* `x' does not get converted *)
and type_to_guard ctx ty x =
  debug 3 (fun () -> print_header_nonl "type_to_guard" ty ctx; print_coqterm x; print_newline ());
  match ty with
  | Prod(vname, ty1, ty2) ->
     if Coq_typing.check_prop ctx ty1 then
       prop_to_formula ctx ty1 >>= fun tm1 ->
       type_to_guard ctx (subst_proof vname ty1 ty2) x >>= fun tm2 ->
       return (mk_impl tm1 tm2)
     else
       make_guard ctx ty1 (Var(vname)) >>= fun tm1 ->
       type_to_guard ((vname, ty1) :: ctx) ty2 (App(x, (Var(vname)))) >>= fun tm2 ->
       return (mk_forall vname type_any (mk_impl tm1 tm2))
  | _ ->
     convert ctx ty >>= fun tm ->
     return (mk_hastype x tm)

and make_fol_forall ctx vars tm =
  let rec hlp ctx vars tm =
    match vars with
    | (name, ty) :: vars2 ->
      if Coq_typing.check_prop ctx ty then
        hlp ((name, ty) :: ctx) vars2 (subst_proof name ty tm)
      else
        hlp ((name, ty) :: ctx) vars2 tm >>= fun r ->
        return (mk_forall name type_any r)
    | [] ->
      prop_to_formula ctx tm
  in
  hlp ctx vars tm

and make_guarded_forall ctx vars cont =
  let rec hlp ctx vars =
    match vars with
    | (name, ty) :: vars2 ->
       begin
         make_guard ctx ty (Var(name)) >>= fun guard ->
         hlp ((name, ty) :: ctx) vars2 >>= fun r ->
         return (mk_forall name type_any (mk_impl guard r))
       end
    | [] ->
       cont ctx
  in
  hlp ctx vars

and close vars cont =
  if !opt_closure_guards then
    make_guarded_forall [] vars cont
  else
    let rec hlp ctx vars =
      match vars with
      | (name, ty) :: vars2 ->
         begin
           hlp ((name, ty) :: ctx) vars2 >>= fun r ->
           return (mk_forall name type_any r)
         end
      | [] ->
         cont ctx
    in
    hlp [] vars

and remove_lambda ctx tm =
  debug 3 (fun () -> print_header "remove_lambda" tm ctx);
  Hashing.find_or_insert coqterm_hash ctx tm
    begin fun cctx ctm ->
      let name = "$_lam_" ^ unique_id ()
      in
      lambda_lifting name name (ctx_to_vars cctx) [] ctm
    end

and remove_case ctx tm =
  debug 3 (fun () -> print_header "remove_case" tm ctx);
  Hashing.find_or_insert coqterm_hash ctx tm
    begin fun cctx ctm ->
      case_lifting "" "" (ctx_to_vars cctx) [] ctm
    end
(* TODO: for case lifting cctx should always include the proof
   variables tm may depend on; otherwise the resulting FOL problem
   may be inconsistent *)

and remove_cast ctx tm =
  debug 3 (fun () -> print_header "remove_cast" tm ctx);
  match tm with
  | Cast(trm, ty) ->
      let fvars = get_fvars ctx tm
      and fname = "$_cast_" ^ unique_id ()
      in
      convert ctx (mk_long_app (Const(fname)) (mk_vars fvars)) >>= fun tm2 ->
      let ty2 = mk_long_prod fvars ty
      in
      let srt = if Coq_typing.check_prop [] ty2 then SortProp else SortType
      in
      if srt <> SortProp then
        begin
          let def = mk_def fname (mk_long_lam fvars trm) ty2 srt
          in
          add_def_eq_axiom def >>
          return tm2
        end
      else
        return (Const("$Proof"))
  | _ ->
      failwith "remove_cast"

and remove_fix ctx tm =
  debug 3 (fun () -> print_header "remove_fix" tm ctx);
  Hashing.find_or_insert coqterm_hash ctx tm
    begin fun cctx ctm ->
      fix_lifting "" "" (ctx_to_vars cctx) [] ctm
    end

and remove_let ctx tm =
  debug 3 (fun () -> print_header "remove_let" tm ctx);
  match tm with
  | Let(value, (name, ty, body)) ->
      let name2 = "$_let_" ^ name ^ "_" ^ unique_id ()
      and fvars = get_fvars ctx (App(value, ty))
      in
      let ty2 = mk_long_prod fvars ty
      and val2 = mk_long_app (Const(name2)) (mk_vars fvars)
      in
      let srt = if Coq_typing.check_prop [] ty2 then SortProp else SortType
      in
      let def = mk_def name2 (mk_long_lam fvars value) ty2 srt
      in
      Defhash.add def;
      begin
        if srt <> SortProp then
          add_def_eq_axiom def
        else
          return ()
      end >>
      convert ctx (simple_subst name val2 body)
  | _ ->
      failwith "remove_let"

and remove_type ctx ty =
  debug 3 (fun () -> print_header "remove_type" ty ctx);
  Hashing.find_or_insert coqterm_hash ctx ty
    begin fun cctx cty ->
      let name = "$_type_" ^ unique_id ()
      and vars = ctx_to_vars cctx
      in
      add_def_eq_type_axiom name name vars cty >>
      convert cctx (mk_long_app (Const(name)) (mk_vars vars))
    end

and add_def_eq_type_axiom axname name fvars ty =
  debug 2 (fun () -> print_header "add_def_eq_type_axiom" ty fvars);
  let vname = "var_" ^ unique_id ()
  in
  close fvars
    begin fun ctx ->
      convert ctx (mk_long_app (Const(name)) (mk_vars fvars)) >>= fun tp ->
      type_to_guard ctx ty (Var(vname)) >>= fun guard ->
      return (mk_forall vname type_any
                (mk_equiv (mk_hastype (Var(vname)) tp) guard))
    end >>= fun r ->
  add_axiom (mk_axiom axname r)

and add_typing_axiom name ty =
  debug 2 (fun () -> print_endline ("add_typing_axiom: " ^ name));
  if not (is_logop name) && name <> "$True" && name <> "$False" && ty <> type_any then
    begin
      if opt_omit_prop_typing_axioms && Coq_typing.check_type_target_is_prop ty then
        return ()
      else if opt_type_optimization &&
          (Coq_typing.check_type_target_is_type ty || Coq_typing.check_type_target_is_prop ty) then
        begin
          let fix_ax ax =
            let xvar = refresh_varname "X"
            in
            let rec hlp tm =
              match tm with
              | Quant("!", (vname, _, body)) ->
                Quant("!", (vname, type_any, hlp body))
              | App(App(Const("=>"), x), y) ->
                App(App(Const("=>"), x), hlp y)
              | Equal(x, y) ->
                if opt_hastype then
                  mk_equiv
                    (App(App(Const "$HasType", x), Var(xvar)))
                    (App(App(Const "$HasType", y), Var(xvar)))
                else
                  mk_equiv (App(x, Var(xvar))) (App(y, Var(xvar)))
              | _ -> failwith "add_typing_axiom: fix_ax"
            in
            mk_forall xvar type_any (hlp ax)
          in
          let name2 = "$_type_" ^ name ^ "_" ^ unique_id ()
          and args = Coq_typing.get_type_args ty
          in
          (* TODO: fix proof arguments in ax *)
          let ys = mk_vars args
          in
          let ax =
            mk_long_forall args
              (mk_eq
                 (mk_long_app (Const(name2)) ys)
                 (mk_long_app (Const(name)) ys))
          in
          make_guard [] ty (Const(name2)) >>= fun guard ->
          add_axiom (mk_axiom ("$_tydef_" ^ name2) (fix_ax ax)) >>
          add_axiom (mk_axiom ("$_typeof_" ^ name) guard)
        end
      else
        begin
          make_guard [] ty (Const(name)) >>= fun guard ->
          add_axiom (mk_axiom ("$_typeof_" ^ name) guard)
        end
    end
  else
    return ()

and add_def_eq_axiom (name, value, ty, srt) =
  debug 2 (fun () -> print_endline ("add_def_eq_axiom: " ^ name));
  let axname = "$_def_" ^ name
  in
  match value with
  | Lam(_) ->
     lambda_lifting axname name [] [] value >>
     return ()
  | Fix(_) ->
     fix_lifting axname name [] [] value >>
     return ()
  | Const(c) when c = name ->
     return ()
  | _ ->
      begin
        match ty with
        | SortProp ->
           begin
             prop_to_formula [] value >>= fun r ->
             add_axiom (mk_axiom axname (mk_equiv (Const(name)) r))
           end
        | SortType | SortSet ->
           add_def_eq_type_axiom axname name [] value
        | _ ->
           begin
             convert [] value >>= fun r ->
             add_axiom (mk_axiom axname (mk_eq (Const(name)) r))
           end
      end

and add_injection_axioms constr =
  debug 2 (fun () -> print_endline ("add_injection_axioms: " ^ constr));
  let ty = coqdef_type (Defhash.find constr)
  in
  let rec hlp ty1 ty2 args1 args2 conjs =
    match ty1, ty2 with
    | Prod(name1, lty1, value1), Prod(name2, lty2, value2) ->
      let lname1 = refresh_varname name1
      and lname2 = refresh_varname name2
      in
      let lvalue1 = simple_subst name1 (Var(lname1)) value1
      and lvalue2 = simple_subst name2 (Var(lname2)) value2
      in
      mk_forall lname1 lty1
        (mk_forall lname2 lty2
           (hlp lvalue1 lvalue2
              (Var(lname1) :: args1) (Var(lname2) :: args2)
              ((mk_eq (Var(lname1)) (Var(lname2))) :: conjs)))
    | _ ->
      mk_impl
        (mk_eq (mk_long_app (Const(constr)) (List.rev args1))
           (mk_long_app (Const(constr)) (List.rev args2)))
        (join_left mk_and conjs)
  in
  let rec hlp2 ctx ty1 ty2 args1 args2 conjs =
    match ty1, ty2 with
    | Prod(name1, lty1, value1), Prod(name2, lty2, value2) ->
      let lname1 = refresh_varname name1
      and lname2 = refresh_varname name2
      in
      let lvalue1 = simple_subst name1 (Var(lname1)) value1
      and lvalue2 = simple_subst name2 (Var(lname2)) value2
      in
      (hlp2 ((lname1, lty1) :: (lname2, lty2) :: ctx) lvalue1 lvalue2
         (Var(lname1) :: args1) (Var(lname2) :: args2)
         ((mk_eq (Var(lname1)) (Var(lname2))) :: conjs)) >>= fun r ->
      return (mk_forall lname1 type_any (mk_forall lname2 type_any r))
    | _ ->
      prop_to_formula ctx
        (mk_impl
           (mk_eq (mk_long_app (Const(constr)) (List.rev args1))
              (mk_long_app (Const(constr)) (List.rev args2)))
           (join_left mk_and conjs))
  in
  match ty with
  | Prod(_) ->
     begin
       if !opt_closure_guards || opt_injectivity_guards then
         prop_to_formula [] (hlp ty ty [] [] [])
       else
         hlp2 [] ty ty [] [] []
     end >>= fun ax ->
     add_axiom (mk_axiom ("$_inj_" ^ constr) ax)
  | _ ->
     return ()

and add_discrim_axioms constr1 constr2 =
  debug 2 (fun () -> print_endline ("add_discrim_axioms: " ^ constr1 ^ ", " ^ constr2));
  let ty1 = coqdef_type (Defhash.find constr1)
  and ty2 = coqdef_type (Defhash.find constr2)
  in
  let rec hlp ty1 ty2 args1 args2 =
    match ty1, ty2 with
    | Prod(name1, lty1, value1), _ ->
      let lname1 = refresh_varname name1
      in
      let lvalue1 = simple_subst name1 (Var(lname1)) value1
      in
      mk_forall lname1 lty1 (hlp lvalue1 ty2 (Var(lname1) :: args1) args2)
    | _, Prod(name2, lty2, value2) ->
      let lname2 = refresh_varname name2
      in
      let lvalue2 = simple_subst name2 (Var(lname2)) value2
      in
      mk_forall lname2 lty2 (hlp ty1 lvalue2 args1 (Var(lname2) :: args2))
    | _ ->
      mk_not
        (mk_eq
           (mk_long_app (Const(constr1)) (List.rev args1))
           (mk_long_app (Const(constr2)) (List.rev args2)))
  in
  let rec hlp2 ctx ty1 ty2 args1 args2 =
    match ty1, ty2 with
    | Prod(name1, lty1, value1), _ ->
       let lname1 = refresh_varname name1
       in
       let lvalue1 = simple_subst name1 (Var(lname1)) value1
       in
       (hlp2 ((lname1, lty1) :: ctx) lvalue1 ty2
          (Var(lname1) :: args1) args2) >>= fun r ->
       return (mk_forall lname1 type_any r)
    | _, Prod(name2, lty2, value2) ->
       let lname2 = refresh_varname name2
       in
       let lvalue2 = simple_subst name2 (Var(lname2)) value2
       in
       (hlp2 ((lname2, lty2) :: ctx) ty1 lvalue2
          args1 (Var(lname2) :: args2)) >>= fun r ->
       return (mk_forall lname2 type_any r)
    | _ ->
       prop_to_formula ctx
         (mk_not
            (mk_eq
               (mk_long_app (Const(constr1)) (List.rev args1))
               (mk_long_app (Const(constr2)) (List.rev args2))))
  in
  begin
    if !opt_closure_guards || opt_discrimination_guards then
      prop_to_formula [] (hlp ty1 ty2 [] [])
    else
      hlp2 [] ty1 ty2 [] []
  end >>= fun ax ->
  add_axiom (mk_axiom ("$_discrim_" ^ constr1 ^ "$" ^ constr2) ax)

and add_inversion_axioms is_prop indname constrs =
  debug 2 (fun () -> print_endline ("add_inversion_axioms: " ^ indname));
  let (_, IndType(_, constrs, params_num), indtype, indsort) = Defhash.find indname
  in
  let args = Coq_typing.get_type_args indtype
  and vname = "X" ^ unique_id ()
  in
  assert (params_num <= List.length args);
  let vty = mk_long_app (Const(indname)) (mk_vars args)
  in
  let lvars = args @ [(vname, vty)]
  in
  let params = mk_vars (Hhlib.take params_num args)
  in
  if is_prop then
    add_inversion_axioms0
      (fun _ constrs _ _ -> mk_prop_inversion params indname args constrs) indname
      ("$_inversion_" ^ indname) [] lvars constrs (Var(vname)) (fun _ _ _ eqt -> eqt)
  else
    add_inversion_axioms0 (mk_inversion params)
      indname ("$_inversion_" ^ indname)
      [] lvars constrs (Var(vname))
      begin fun _ targs2 _ eqt ->
        if opt_precise_inversion then
          mk_inversion_conjs params_num args targs2 [eqt]
        else
          eqt
      end

and add_def_axioms ((name, value, ty, srt) as def) =
  debug 2 (fun () -> print_endline ("add_def_axioms: " ^ name));
  match value with
  | IndType(_, constrs, _) ->
     if srt = SortProp then
       (prop_to_formula [] ty) >>= fun r ->
       add_axiom (mk_axiom name r)
     else
       begin
         if Coq_typing.check_type_target_is_prop ty then
           begin
             begin
               if opt_prop_inversion_axioms && name <> "Coq.Init.Logic.eq" then
                 add_inversion_axioms true name constrs
               else
                 return ()
             end >>
             if not opt_omit_toplevel_prop_typing_axioms then
               add_typing_axiom name ty
             else
               return ()
           end
        else
          begin
            List.fold_left (fun acc c -> add_injection_axioms c >> acc) (return ()) constrs >>
            List.fold_left (fun acc (c1, c2) -> add_discrim_axioms c1 c2) (return ()) (Hhlib.mk_pairs constrs) >>
            add_typing_axiom name ty >>
            if opt_inversion_axioms then
              add_inversion_axioms false name constrs
            else
              return ()
          end
      end
  | _ ->
     if srt = SortProp then
       begin
         prop_to_formula [] ty >>= fun r ->
         add_axiom (mk_axiom name r)
       end
     else
       begin
         add_typing_axiom name ty >>
         add_def_eq_axiom def
       end

(***************************************************************************************)
(* Axioms hash *)

module Axhash = struct
  let axhash = Hashtbl.create 1024
  let clear () = Hashtbl.clear axhash
  let add name lst =
    if Hashtbl.mem axhash name then
      failwith ("Axhash.add: " ^ name);
    Hashtbl.add axhash name lst
  let remove name = Hashtbl.remove axhash name
  let mem name = Hashtbl.mem axhash name
  let find name =
    try Hashtbl.find axhash name with Not_found -> failwith ("Axhash.find: " ^ name)
end

(***************************************************************************************)
(* Translation *)

let translate name =
  log 1 ("translate: " ^ name);
  let axs = extract_axioms (add_def_axioms (Defhash.find name))
  in
  Hhlib.sort_uniq (fun x y -> Pervasives.compare (fst x) (fst y)) axs

let retranslate lst =
  List.iter
    begin fun name ->
      if not (Axhash.mem name) then
        Axhash.add name (translate name)
    end
    lst

let get_axioms lst =
  coq_axioms @
    Hhlib.sort_uniq (fun x y -> Pervasives.compare (fst x) (fst y))
    (List.concat (List.map Axhash.find lst))

let remove_def name =
  Defhash.remove name;
  Axhash.remove name

let cleanup () =
  Defhash.clear ();
  Axhash.clear ();
  Hashing.clear coqterm_hash

(******************************************************************************)

let write_problem fname name deps =
  let axioms = get_axioms (name :: deps)
  in
  let oc = open_out fname
  in
  try
    Tptp_out.write_fol_problem
      (output_string oc)
      (List.remove_assoc name axioms)
      (name, List.assoc name axioms);
    close_out oc
  with e ->
    close_out oc;
    raise e
