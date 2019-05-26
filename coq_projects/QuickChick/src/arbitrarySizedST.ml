open Pp
open Util
open GenericLib
open CoqLib
open GenLib
open Error
open Unify

(* arguments to handle_branch *)
let fail_exp (dt : coq_expr) =
  returnGen (gApp ~explicit:true (gInject "None") [dt])

let not_enough_fuel_exp (dt : coq_expr) =
  returnGen (gApp ~explicit:true (gInject "None") [dt])
  
let ret_exp (dt : coq_expr) (c : coq_expr) =
  msg_debug (str "Returning...." ++ fnl ());
  debug_coq_expr c;
  returnGen (gApp ~explicit:true (gInject "Some") [dt; c])

let ret_type (s : var) f = hole

let instantiate_existential_method = (gInject "arbitrary")

let instantiate_existential_methodST (n : int) (pred : coq_expr) = 
  gApp ~explicit:true (gInject "arbitraryST")
    [ hole (* Implicit argument - type A *)
    ; pred
    ; hole (* Implicit instance *)]

let rec_method (rec_name : coq_expr) (size : coq_expr) (n : int) (letbinds : unknown list option) (l : coq_expr list) =
  (* TODO: use letbinds *)
  gApp rec_name (size :: l)

let bind (opt : bool) (m : coq_expr) (x : string) (f : var -> coq_expr) =
  (if opt then bindGenOpt else bindGen) m x f

let stMaybe (opt : bool) (g : coq_expr) (x : string) (checks : ((coq_expr -> coq_expr) * int) list) =
  let rec sumbools_to_bool x lst =
    match lst with
    | [] -> gTrueb
    | (chk, _) :: lst' ->
      matchDec (chk (gVar x)) (fun heq -> gFalseb) (fun hneq -> sumbools_to_bool x lst')
  in
  let bool_pred =
    gFun [x]
      (fun [x] -> sumbools_to_bool x checks)
  in
  (gApp (gInject (if opt then "suchThatMaybeOpt" else "suchThatMaybe"))
     [ g (* Use the generator provided for base generator *)
     ; bool_pred
     ])

let ret_type_dec (s : var) (left : coq_expr) (right : coq_expr) =
      gMatch (gVar s)
      [ (injectCtr "left", ["eq"], fun _ -> left)
      ; (injectCtr "right", ["neq"], fun _ -> right) ]

let check_expr (n : int) (scrut : coq_expr) (left : coq_expr) (right : coq_expr) (out_of_fuel : coq_expr) =
  gMatchReturn scrut
    "s" (* as clause *)
    (fun v -> ret_type v ret_type_dec)
    [ (injectCtr "Some", ["res_b" ] , fun [b] ->
      (* Why as clauses/returns? *)       
      gMatch (gVar b) 
        [ (injectCtr "true", [], fun _ -> left)
        ; (injectCtr "false", [], fun _ -> right)
        ])
    ; (injectCtr "None", [], fun _ -> out_of_fuel) 
    ]

let match_inp (inp : var) (pat : matcher_pat) (left : coq_expr) (right  : coq_expr) =
  let ret v left right =
    construct_match (gVar v) ~catch_all:(Some right) [(pat, left)]
  in
  let catch_case = 
    match pat with 
    | MatchCtr (c, ls) -> 
       (* Leo: This is a hack totality check for unary matches *)
       if num_of_ctrs c = 1 && List.for_all (fun x -> match x with MatchU _ -> true | MatchCtr _ -> false) ls 
       then None
       else Some right
    | _ -> failwith "Toplevel match not a constructor?"
  in 
  construct_match_with_return
    (gVar inp) ~catch_all:(catch_case) "s" (fun v -> ret_type v ret)
    [(pat,left)]

type generator_kind = Base_gen | Ind_gen 
  
(* hoisting out base and ind gen to be able to call them from proof generation *)
let construct_generators
      (kind : generator_kind)
      (size : coq_expr)
      (full_gtyp : coq_expr)
      (gen_ctr : ty_ctr)
      (dep_type : dep_type)
      (ctrs : dep_ctr list)
      (rec_name : coq_expr)
      (input_ranges : range list)
      (init_umap : range UM.t)
      (init_tmap : dep_type UM.t)
      (result : Unknown.t)
  =
  (* partially applied handle_branch *)
  let handle_branch' =
    handle_branch dep_type (fail_exp full_gtyp) (not_enough_fuel_exp full_gtyp) (ret_exp full_gtyp)
      instantiate_existential_method instantiate_existential_methodST bind
      (rec_method rec_name size) bind
      stMaybe check_expr match_inp gLetIn gLetTupleIn
      gen_ctr init_umap init_tmap input_ranges result
  in
  let all_gens = List.map handle_branch' ctrs in
  match kind with
  | Base_gen -> List.map fst (List.filter snd all_gens)
  | Ind_gen  -> List.map fst all_gens

let base_gens = construct_generators Base_gen
let ind_gens  = construct_generators Ind_gen              
              
(* Advanced Generators *)
let arbitrarySizedST
      (gen_ctr : ty_ctr)
      (ty_params : ty_param list)
      (ctrs : dep_ctr list)
      (dep_type : dep_type)
      (input_names : var list)
      (input_ranges : range list)
      (init_umap : range UM.t)
      (init_tmap : dep_type UM.t)
      (inputs : arg list)
      (result : Unknown.t)
      (rec_name : coq_expr) =
  
  (* type constructor *)
  let coqTyCtr = gTyCtr gen_ctr in

  (* parameters of the type constructor *)
  let coqTyParams = List.map gTyParam ty_params in

  (* The type we are generating for -- not the predicate! *)
  let full_gtyp = (gType ty_params (UM.find result init_tmap)) in

  (* The type of the dependent generator *)
  let gen_type = gGen (gOption full_gtyp) in

  let aux_arb rec_name size vars =
    gMatch (gVar size)
      [ (injectCtr "O", [],
         fun _ ->
           uniform_backtracking
             (base_gens (gVar size) full_gtyp gen_ctr dep_type ctrs rec_name
                input_ranges init_umap init_tmap result))
      ; (injectCtr "S", ["size'"],
         fun [size'] ->
           let weights = List.map (fun (c,_) -> Weightmap.lookup_weight c size') ctrs in
           backtracking (List.combine weights 
                           (ind_gens (gVar size') full_gtyp gen_ctr dep_type ctrs rec_name
                              input_ranges init_umap init_tmap result)))
      ]
  in

  let generator_body : coq_expr =
    gRecFunInWithArgs
      ~assumType:(gen_type)
      "aux_arb" (gArg ~assumName:(gVar (fresh_name "size")) () :: inputs) 
      (fun (rec_name, size::vars) -> aux_arb (gVar rec_name) size vars)
      (fun rec_name -> gFun ["size"] 
          (fun [size] -> gApp (gVar rec_name) 
              (gVar size :: List.map (fun i -> gVar (arg_to_var i)) inputs)
          ))
  in

  msg_debug (fnl () ++ fnl () ++ str "`Final body produced:" ++ fnl ());
  debug_coq_expr generator_body;
  msg_debug (fnl ());
  gRecord [("arbitrarySizeST", generator_body)]
