open Pp
open Util
open GenericLib
open SetLib
open CoqLib
open GenLib
open SemLib
open Unify
open ArbitrarySizedST
open Error

(* arguments to handle_branch *)
let fail_exp = returnGenSizeMonotonicOpt (gNone hole)

let ret_exp (c : coq_expr) = returnGenSizeMonotonicOpt (gSome hole c)

let ret_type (s : var) (match_expr : var -> coq_expr -> coq_expr -> coq_expr)  =
  gApp (gInject "SizeMonotonicOpt") [match_expr s hole hole]

(* These should be inferred automatically  *)
let class_method = hole
let class_methodST (n : int) (pred : coq_expr) = hole

let rec_method (ih : var) (n : int) (l : coq_expr list) =
  gApp (gVar ih) l

let bind (opt : bool) (m : coq_expr) (x : string) (f : var -> coq_expr) =
  (if opt then bindOptMonotonicOpt else bindMonotonicOpt) m x f

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
  (if opt then suchThatMaybeOptMonotonicOpt else suchThatMaybeMonotonicOpt) g bool_pred

let ret_type_dec (s : var) (left : coq_expr) (right : coq_expr) =
      gMatch (gVar s)
      [ (injectCtr "left", ["eq"], fun _ -> left)
      ; (injectCtr "right", ["neq"], fun _ -> right) ]

let check_expr (n : int) (scrut : coq_expr) (left : coq_expr) (right : coq_expr) =
  gMatchReturn scrut
    "s" (* as clause *)
    (fun v -> ret_type v ret_type_dec)
    [ (injectCtr "left", ["eq" ] , fun _ -> left)
    ; (injectCtr "right", ["neq"], fun _ -> right) 
    ]

let match_inp (inp : var) (pat : matcher_pat) (left : coq_expr) (right  : coq_expr) =
  let ret v left right =
    construct_match (gVar v) ~catch_all:(Some right) [(pat, left)]
  in
  construct_match_with_return
    (gVar inp) ~catch_all:(Some right) "s" (fun v -> ret_type v ret)
    [(pat,left)]


let genSizedSTMon_body
      (class_name : string)
      (gen_ctr : ty_ctr)
      (ty_params : ty_param list)
      (ctrs : dep_ctr list)
      (dep_type : dep_type)
      (input_names : string list)
      (inputs : arg list)
      (n : int)
      (register_arbitrary : dep_type -> unit) =

  (* type constructor *)
  let coqTyCtr = gTyCtr gen_ctr in

  (* parameters of the type constructor *)
  let coqTyParams = List.map gTyParam ty_params in

  (* Fully applied type constructor *)
  let full_dt = gApp ~explicit:true coqTyCtr coqTyParams in

  (* The type we are generating for -- not the predicate! *)
  let full_gtyp = (gType ty_params (nthType n dep_type)) in

  (* The type of the dependent generator *)
  let gen_type = gGen (gOption full_gtyp) in

  (* Fully applied predicate (parameters and constructors) *)
  let full_pred inputs =
    gFun ["_forGen"] (fun [fg] -> gApp (full_dt) (list_insert_nth (gVar fg) inputs (n-1)))
  in

  let base_gens (input_names : var list) (rec_name : coq_expr) =
    base_gens (gInt 0) full_gtyp gen_ctr dep_type ctrs input_names n register_arbitrary rec_name
  in

  let ind_gens (input_names : var list) (size : var) (rec_name : coq_expr) =
    ind_gens (gVar size) full_gtyp gen_ctr dep_type ctrs input_names n register_arbitrary rec_name
  in

  let aux_arb (input_names : var list) (rec_name : coq_expr) size vars =
    gMatch (gVar size)
      [ (injectCtr "O", [], fun _ ->
             uniform_backtracking (base_gens input_names rec_name))
      ; (injectCtr "S", ["size'"], fun [size'] ->
            uniform_backtracking (ind_gens input_names size' rec_name))
      ]
  in

  let generator_body (input_names : var list) : coq_expr =
    gRecFunInWithArgs
      ~assumType:(gen_type)
      "aux_arb" (gArg ~assumName:(gVar (fresh_name "size")) () :: inputs) 
      (fun (rec_name, size::vars) -> aux_arb input_names (gVar rec_name) size vars)
      (fun x -> gVar x)
  in

  let add_freq gens =
    List.map gPair (List.combine (List.map (fun _ -> gInt 1) gens) gens) in

  let base_case =
    let handle_branch' (inputs : var list) =
      handle_branch n dep_type inputs
        fail_exp ret_exp class_method class_methodST
        (rec_method (make_up_name ())) bind stMaybe check_expr match_inp gLetIn
        gen_ctr (fun _ -> ())
    in
    gFunWithArgs
      inputs
      (fun inputs ->
         backtrackSizeMonotonicOpt
           (gList (add_freq (base_gens inputs (generator_body inputs))))
           (List.fold_right
              (fun (c : dep_ctr) (exp : coq_expr) ->
                 let (p, b) : coq_expr * bool = handle_branch' inputs c in
                 if b then
                   cons_subset hole hole hole p exp
                 else exp
              )
              ctrs (nil_subset hole)))
  in
  (* gen_ctr dep_type gen_type ctrs input_names inputs n register_arbitrary *)
  (* class_name full_gtyp full_pred inputs base_gen ind_gen = *)

  let ind_case =
    let handle_branch' (ih : var) (size : var) (inputs : var list) =
      handle_branch n dep_type inputs
        fail_exp ret_exp class_method class_methodST
        (rec_method ih) bind stMaybe check_expr match_inp
        (failwith "zoe fix me!")
        gen_ctr (fun _ -> ())
    in
    gFun ["size"; "IHs"]
      (fun [size; ihs] ->
         gFunWithArgs
           inputs
           (fun inputs ->
              backtrackSizeMonotonicOpt
                (gList (add_freq (ind_gens inputs size (generator_body inputs))))
                (List.fold_right
                   (fun c exp ->
                      let (p, b) = handle_branch' ihs size inputs c in
                      cons_subset hole hole hole p exp
                   )
                   ctrs (nil_subset hole))))
  in

  let ret_type =
    gFun ["s"]
      (fun [s] ->
         gProdWithArgs
           inputs
           (fun inputs ->
              gApp (gInject class_name)
                [gApp ~explicit:true (gInject "arbitrarySizeST")
                   [full_gtyp; full_pred (List.map gVar inputs); hole; gVar s]]))
  in 

  let mon_proof =
    gApp (gInject "nat_ind") [ret_type; base_case; ind_case]
  in

  msg_debug (str "mon term");
  debug_coq_expr mon_proof;
  mon_proof
