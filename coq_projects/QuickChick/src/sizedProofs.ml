open Pp
open Loc
open Names
open Extract_env
open Tacmach
open Entries
open Declarations
open Declare
open Libnames
open Util
open Constrintern
open Constrexpr
open Constrexpr_ops
open Decl_kinds
open GenericLib
open SetLib
open CoqLib
open GenLib
open Error
open Unify

type btyp = ((coq_expr -> coq_expr -> int -> (coq_expr * coq_expr) list -> (coq_expr -> coq_expr) -> coq_expr) *
             ((coq_expr -> (coq_expr * coq_expr) list -> coq_expr) -> coq_expr -> (coq_expr * coq_expr) list -> coq_expr))

type atyp = btyp -> btyp

(* Subterms for iter *)
let fail_exp = set_empty

let not_enough_fuel_exp = set_empty
             
let ret_exp (c : coq_expr) =
  set_singleton c

let ret_type (s : var) (match_expr : var -> coq_expr -> coq_expr -> coq_expr) = hole

let instantiate_existential_method = set_full

let instantiate_existential_methodST (n : int) (pred : coq_expr) =
  pred

let rec_method (rec_name : coq_expr) (size : coq_expr) (n : int) letbinds (l : coq_expr list) =
  (* TODO: use letbinds *)
  gApp rec_name (size :: l)

let bind (opt : bool) (m : coq_expr) (x : string) (f : var -> coq_expr) =
  set_bigcup x m f

let stMaybe (opt : bool) (g : coq_expr) (x : string) (checks : ((coq_expr -> coq_expr) * int) list) =
  let rec sumbools_to_bool x lst =
    match lst with
    | [] -> gApp g [gVar x]
    | (chk, _) :: lst' ->
      matchDec (chk (gVar x)) (fun heq -> gFalse) (fun hneq -> sumbools_to_bool x lst')
  in
  gFun [x] (fun [x] -> sumbools_to_bool x checks)

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
(*
    (fun v -> ret_type v ret_type_dec)
    [ (injectCtr "left", ["eq" ] , fun _ -> left)
    ; (injectCtr "right", ["neq"], fun _ -> right) 
    ]*)

let match_inp (inp : var) (pat : matcher_pat) (left : coq_expr) (right  : coq_expr) =
  let ret v left right =
    construct_match (gVar v) ~catch_all:(Some right) [(pat, left)]
  in
  construct_match_with_return
    (gVar inp) ~catch_all:(Some right) "s" (fun v -> ret_type v ret)
    [(pat,left)]


module OrdInt = struct 
  type t = int
  let compare (x : int) (y : int) : int = compare x y
end

module IntMap = Map.Make(OrdInt)

type proofMap = (coq_expr -> coq_expr) IntMap.t

type ctxMap = (coq_expr * coq_expr) IntMap.t

let sizedEqProofs_body
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

  (* Fully applied type constructor *)
  let full_dt = gApp ~explicit:true coqTyCtr coqTyParams in

  (* The type we are generating for -- not the predicate! *)
  let full_gtyp = (gType ty_params (UM.find result init_tmap)) in

  (* The type of the dependent generator *)
  let gen_type = gGen (gOption full_gtyp) in

  (* Inputs as holes *)
  let hole_inps =
    List.map (fun _ -> hole) input_ranges
  in

(*
  let make_prop (m : int) (x : coq_expr) (ls : coq_expr list) =
    gApp full_dt (list_insert_nth x ls (m-1))
  in

  let full_prop gtyp inputs =
    gApp full_dt (list_insert_nth gtyp inputs (n-1))
  in
 *)
  
  (* iter construction *)

  let zero_set inputs =
    
    let handle_branch'  =
      handle_branch dep_type fail_exp not_enough_fuel_exp ret_exp
        instantiate_existential_method instantiate_existential_methodST bind
        (rec_method rec_name (gInt 0)) bind
        stMaybe check_expr match_inp
        gLetIn gLetTupleIn
        gen_ctr init_umap init_tmap input_ranges result
    in
    (List.fold_right
       (fun c exp ->
          let (p, b) = handle_branch' c in
          if b then
            set_union p exp
          else exp
       )
       ctrs (set_empty))
  in

  let succ_set rec_name size inputs =
    let handle_branch'  =
      handle_branch dep_type 
        fail_exp not_enough_fuel_exp ret_exp
        instantiate_existential_method instantiate_existential_methodST bind
        (rec_method rec_name size) bind
        stMaybe check_expr match_inp
        gLetIn gLetTupleIn
        gen_ctr init_umap init_tmap input_ranges result
    in
    (List.fold_right
       (fun c exp ->
          let (p, b) = handle_branch' c in
          set_union p exp
       ) ctrs (set_empty))
  in

  let aux_iter rec_name size vars =
    gMatch (gVar size)
      [ (injectCtr "O", [],
         fun _ -> zero_set vars)
      ; (injectCtr "S", ["size'"],
         fun [size'] -> succ_set rec_name (gVar size') vars)
      ]
  in

  let iter_body : coq_expr =
    gRecFunInWithArgs
      "aux_iter" (gArg ~assumName:(gVar (fresh_name "size")) () :: inputs) 
      (fun (rec_name, size::vars) -> aux_iter (gVar rec_name) size vars)
      (fun rec_name -> gFun ["size"] 
                         (fun [size] -> gApp (gVar rec_name)
                                          (gVar size :: List.map (fun i -> gVar (arg_to_var i)) inputs)
                         ))
  in
(*
  (* monotonicity proof *)

  let fail_exp_mon : coq_expr * coq_expr * coq_expr =
    (set_empty, set_empty, set_incl_refl)
  in

  let ret_exp_mon (x : coq_expr) : coq_expr * coq_expr * coq_expr =
    (set_singleton x, set_singleton x, set_incl_refl)
  in

  let instantiate_existential_method_mon : coq_expr * coq_expr * coq_expr =
    (set_full, set_full, set_incl_refl)
  in

  let instantiate_existential_methodST_mon (n : int) (pred : coq_expr) : coq_expr * coq_expr * coq_expr =
    (pred, pred, set_incl_refl)
  in

  let rec_method_mon (s1 : coq_expr) (s2 : coq_expr) (ih : coq_expr list -> coq_expr) (n : int) (letbinds) (l : coq_expr list)
      : coq_expr * coq_expr * coq_expr =
    (* TODO: Use letbinds...*)
    let iter_body args : coq_expr =
      gRecFunInWithArgs
        "aux_iter" (gArg ~assumName:(gVar (fresh_name "size")) () :: inputs)
        (fun (rec_name, size::vars) -> aux_iter rec_name size vars)
        (fun rec_name -> gApp (gVar rec_name) args)
    in
    (iter_body (s1 :: l), iter_body (s2 :: l), ih l) (* ih should be already applied to the arguments, only the inputs should be missing *)
  in

  let bind_mon (opt : bool) (m : coq_expr * coq_expr * coq_expr) (x : string) (f : var -> coq_expr * coq_expr * coq_expr) =
    let (s1, s2, p) = m in 
    (set_bigcup x s1 (fun x -> let (s, _, _) =  f x in s),
     set_bigcup x s2 (fun x -> let (_, s, _) =  f x in s),
     incl_bigcup_compat p (gFun [x] (fun [x] -> let (_, _, s) = f x in s)))
  in

  let let_in_mon = failwith "whyyy" in
  let let_tuple_in_mon = failwith "NOOO" in

  let ret_type_dec (s : var) (left : coq_expr) (right : coq_expr) =
    gMatch (gVar s)
      [ (injectCtr "left", ["eq"], fun _ -> left)
      ; (injectCtr "right", ["neq"], fun _ -> right) ]
  in

  let check_expr_mon (n : int) (scrut : coq_expr)
        (left : coq_expr * coq_expr * coq_expr) (right : coq_expr * coq_expr * coq_expr)
    : coq_expr * coq_expr * coq_expr =
    let (sl1, sl2, pl) = left in
    let (sr1, sr2, pr) = right in
    (gMatchReturn scrut
       "s" (* as clause *)
       (fun v -> ret_type v ret_type_dec)
       [ (injectCtr "left", ["eq" ] , fun _ -> sl1)
       ; (injectCtr "right", ["neq"], fun _ -> sr1) 
       ],
     gMatchReturn scrut
       "s" (* as clause *)
       (fun v -> ret_type v ret_type_dec)
       [ (injectCtr "left", ["eq" ] , fun _ -> sl2)
       ; (injectCtr "right", ["neq"], fun _ -> sr2)
       ],
     gMatchReturn scrut
       "s" (* as clause *)
       (fun v -> set_incl (ret_type_dec v sl1 sr1) (ret_type_dec v sl2 sr2))
       [ (injectCtr "left", ["eq" ] , fun _ -> pl)
       ; (injectCtr "right", ["neq"], fun _ -> pr)
       ])
  in

  let match_inp_mon (inp : var) (pat : matcher_pat)
        (left : coq_expr * coq_expr * coq_expr ) (right : coq_expr * coq_expr * coq_expr )
    : coq_expr * coq_expr * coq_expr =
    let (sl1, sl2, pl) = left in
    let (sr1, sr2, pr) = right in
    let ret v left right =
      construct_match (gVar v) ~catch_all:(Some right) [(pat, left)]
    in
    (construct_match_with_return
       (gVar inp) ~catch_all:(Some sr1) "s" (fun v -> ret_type v ret)
       [(pat,sl1)],
     construct_match_with_return
       (gVar inp) ~catch_all:(Some sr2) "s" (fun v -> ret_type v ret)
       [(pat,sl2)],
     construct_match_with_return
       (gVar inp) ~catch_all:(Some pr)
       "s" (fun v -> set_incl (ret v sl1 sr1) (ret v sl2 sr2))
       [(pat, pl)])
  in

  let stMaybe_mon (opt : bool) (exp : coq_expr * coq_expr * coq_expr) (x : string) (checks : ((coq_expr -> coq_expr) * int) list)
    : coq_expr * coq_expr * coq_expr =
    let (g1, g2, p) = exp in 
    let rec sumbools_to_bool x lst g =
      match lst with
      | [] -> gApp g [gVar x]
      | (chk, _) :: lst' ->
        matchDec (chk (gVar x)) (fun heq -> gFalse) (fun hneq -> sumbools_to_bool x lst' g)
    in
    let rec sumbools_to_bool_proof x lst : coq_expr =
      match lst with
      | [] -> gApp p [gVar x]
      | (chk, n) :: lst' ->
        let s1 = sumbools_to_bool x lst' g1 in
        let s2 = sumbools_to_bool x lst' g2 in
        gMatchReturn (chk (gVar x))
          "s" (* as clause *)
          (fun v -> gImpl (ret_type_dec v gFalse s1) (ret_type_dec v gFalse s2))
          [ (injectCtr "left", ["heq"],
             fun [hn] -> gApp set_incl_refl [gVar x])
          ; (injectCtr "right", ["hneq"],
             fun [hn] -> sumbools_to_bool_proof x lst')
          ]
    in
    (gFun [x] (fun [x] -> sumbools_to_bool x checks g1),
     gFun [x] (fun [x] -> sumbools_to_bool x checks g2),
     gFun [x] (fun [x] -> sumbools_to_bool_proof x checks))
  in

  let rec elim_base_cases_mon s1 s2 (inputs : var list) ctrs =
    let handle_branch' (c : dep_ctr) =
      handle_branch dep_type 
        fail_exp_mon ret_exp_mon
        instantiate_existential_method_mon instantiate_existential_methodST_mon bind_mon
        (rec_method_mon s1 s2 (fun _ -> gVar (make_up_name ()))) bind_mon
        stMaybe_mon check_expr_mon match_inp_mon 
        let_in_mon let_tuple_in_mon 
        gen_ctr init_umap init_tmap input_ranges result c
    in
    match ctrs with
    | [] -> set_incl_refl
    | c :: ctrs' ->
      let ((_, _, p), b) = handle_branch' c in
      if b then
        setU_set_subset_compat p (elim_base_cases_mon s1 s2 inputs ctrs')
      else
        setU_subset_r hole (elim_base_cases_mon s1 s2 inputs ctrs')
  in

  let rec elim_ind_cases_mon s1 s2 (ih : coq_expr list -> coq_expr) (inputs : var list) ctrs =
    let handle_branch' (c : dep_ctr)  =
      handle_branch dep_type 
        fail_exp_mon ret_exp_mon
        instantiate_existential_method_mon instantiate_existential_methodST_mon bind_mon
        (rec_method_mon s1 s2 (fun _ -> gVar (make_up_name ()))) bind_mon
        stMaybe_mon check_expr_mon match_inp_mon 
        let_in_mon let_tuple_in_mon 
        gen_ctr init_umap init_tmap input_ranges result c
    in
    match ctrs with
    | [] -> set_incl_refl
    | c :: ctrs' ->
      let ((_, _, p), b) = handle_branch' c in
      setU_set_subset_compat p (elim_ind_cases_mon s1 s2 ih inputs ctrs')
  in

  let mon_proof input_vars : coq_expr =
    let iter_body args : coq_expr =
      gRecFunInWithArgs
        "aux_iter" (gArg ~assumName:(gVar (fresh_name "size")) () :: inputs) 
        (fun (rec_name, size::vars) -> aux_iter rec_name size vars)
        (fun rec_name -> gApp (gVar rec_name) args)
    in
    let inps = input_vars in
    let ret_type n1 n2 inps = gImpl (gLeq n1 n2) (set_incl ((iter_body (n1 :: inps))) (iter_body (n2 :: inps))) in
    let ind_ret_type = (* fun n1 => forall n2, forall inps, n1 <= n2 -> iter n1 inps \subset iter n2 inps *)
      gFun ["n1"]
        (fun [n1] ->
           gProdWithArgs ((gArg ~assumName:(gVar (fresh_name "n2")) ()) :: inputs)
             (fun (n2 :: inps) -> ret_type (gVar n1) (gVar n2) (List.map gVar inps)))
    in
    let nested_ind_type n1 inps =
      gFun ["n2"] (fun [n2] -> ret_type n1 (gVar n2) inps)
    in
    gFun ["n1"; "n2"]
      (fun [n1; n2] ->
         gApp
           (nat_ind
              ind_ret_type
              (gFun ["n2"]
                 (fun [n2] ->
                    gFunWithArgs inputs
                      (fun inps ->
                         let inps' = List.map gVar inps in
                         gApp
                           (nat_ind
                              (nested_ind_type (gInt 0) inps')
                              (gFun ["Hleq"] (fun [hleq] -> set_incl_refl))
                              (gFun ["n2"; "IHn2"; "Hleq"] (fun [n2; _; hleq] ->
                                                              elim_base_cases_mon (gInt 0) (gVar n2) inps ctrs
                                                            )))
                           [gVar n2])))
              (gFun ["n1"; "IHn1"; "n2"]
                 (fun [n1; ihn1; n2] ->
                    gFunWithArgs inputs
                      (fun inps ->
                         let inps' = List.map gVar inps in
                         gApp
                           (nat_ind
                              (nested_ind_type (gSucc (gVar n1)) inps')
                              (gFun ["Hleq"] (fun [hleq] -> false_ind hole (lt0_False (gVar hleq))))
                              (gFun ["n2"; "IHn2"; "Hleq"] (fun [n2; _; hleq]->
                                                              let ih l = gApp (gApp (gVar ihn1) ((gVar n2) :: l)) [gVar hleq] in
                                                              elim_ind_cases_mon (gVar n1) (gVar n2) ih inps ctrs
                                                            )))
                           [gVar n2]))))
           ((gVar n1) :: (gVar n2) :: inps))
  in

  (* soundness proof *)
  
  let proof_map : proofMap ref = ref IntMap.empty in

  let fail_exp_left : coq_expr * (var -> coq_expr) =
    (set_empty, fun hcur -> false_ind hole (gVar hcur))
  in

  let ret_exp_left (c : dep_ctr) (x : coq_expr) : coq_expr * (var -> coq_expr) =
    (set_singleton x,
     fun hcur ->
       let (c, typ) = c in
       let rec construct_proof typ m acc =
         match typ with
         | DTyCtr _ ->
            (* ZOE: Can you fix this? *)
           (* XXX currently not handling type parameters *)
            let pred =
              (* gFun ["g"] (fun [g] -> make_prop n (gVar g) hole_inps) *)
              gFun ["g"] (fun [g] -> gApp full_dt hole_inps)
           in
           rewrite pred (gVar hcur) (gApp (gCtr c) (List.rev acc))
         | DProd ((x, dt1), dt2) ->
           construct_proof dt2 m (hole :: acc)
         | DArrow (dt1, dt2) ->
           (* at this point the set should be a singleton and curr_set
              just and equality proof *)
           let p =
             try IntMap.find m !proof_map 
             with Not_found -> failwith "Proof not present in the environment"
           in
           construct_proof dt2 (m + 1) ((p (gVar hcur)) :: acc) 
       in
       construct_proof typ 0 [])
  in

  let class_method_left : coq_expr * (var -> (var -> coq_expr) -> coq_expr) =
    (set_full,
     fun (hc : var) (cont : var -> coq_expr) ->
       let name = "HT" in
       gMatch (gVar hc)
         [(injectCtr "conj", [name; "Hcur"],
           fun [ht; hcur] -> cont hcur)])
  in 


  let class_methodST_left (n : int) (pred : coq_expr) : coq_expr * (var -> (var -> coq_expr) -> coq_expr) =
    (pred,
     fun (hc : var) (cont : var -> coq_expr) ->
       let name = Printf.sprintf "Hp%d" n in
       gMatch (gVar hc)
         [(injectCtr "conj", [name; "Hcur"],
           fun [hn; hcur] ->
             (* Add the proof of pred to the map *)
             proof_map :=
               IntMap.add n (fun e -> gVar hn) !proof_map;
             cont hcur)])
  in

  let rec_method_left (ih : coq_expr) (size : coq_expr) (n : int) (l : coq_expr list)
    : coq_expr * (var -> (var -> coq_expr) -> coq_expr) =
    let iter_body args : coq_expr =
      gRecFunInWithArgs
        "aux_iter" (gArg ~assumName:(gVar (fresh_name "size")) () :: inputs) 
        (fun (rec_name, size::vars) -> aux_iter rec_name size vars)
        (fun rec_name -> gApp (gVar rec_name) args)
    in
    (iter_body (size :: l),
     fun (hc : var) (cont : var -> coq_expr) ->
       let name = Printf.sprintf "Hp%d" n in
       gMatch (gVar hc)
         [(injectCtr "conj", [name; "Hcur"],
           fun [hn; hcur] ->
             (* Add the proof of pred to the proof map *)
             let proof eq =
               (* rewrite the final equation in the IH and apply to the
                  inputs and hn *)
               gApp ih ((hole :: l) @ [gVar hn])
             in
             proof_map :=
               IntMap.add n proof !proof_map;
             cont hcur)])
  in

  let bind_left (opt : bool) (m : coq_expr * (var -> (var -> coq_expr) -> coq_expr))
        (x : string) (f : var -> coq_expr * (var -> coq_expr)) : coq_expr * (var -> coq_expr) =
    let (m, cont) = m in
    (set_bigcup x m (fun x -> fst (f x)),
     fun hcur ->
       gMatch (gVar hcur)
         [(injectCtr "ex_intro", [x; "Hc"],
           fun [x; hc] -> cont hc (snd (f x))
          )])
  in

  let ret_type_left set x inputs =
    gImpl
      (gApp set [(gVar x)])
      (full_prop (gVar x) (List.map gVar inputs))
  in

  let ret_type_left_hole set x =
    gImpl
      (gApp set [(gVar x)]) hole
  in

  let ret_type_left_inps s set x m =
    let ret = make_prop m (gVar s) hole_inps in
    gImpl
      (gApp set [(gVar x)]) ret
  in

  let ret_type_dec (s : var) (left : coq_expr) (right : coq_expr) =
    gMatch (gVar s)
      [ (injectCtr "left", ["eq"], fun _ -> left)
      ; (injectCtr "right", ["neq"], fun _ -> right) ]
  in

  let check_expr_left (x : var) (n : int) (scrut : coq_expr)
        (left : coq_expr * (var -> coq_expr)) (right : coq_expr * (var -> coq_expr))
    : coq_expr * (var -> coq_expr) =
    let (lset, lproof) = left in
    let (rset, rproof) = right in
    let name = Printf.sprintf "Hp%d" n in
    let namecur = Printf.sprintf "Hcur%d" n in
    (gMatchReturn scrut
       "s" (* as clause *)
       (fun v -> hole)
       [ (injectCtr "left", ["eq" ] , fun _ -> lset)
       ; (injectCtr "right", ["neq"], fun _ -> rset) 
       ],
     fun hcur ->
       gApp
         (gMatchReturn scrut
            "s" (* as clause *)
            (fun v -> ret_type_left_hole (ret_type_dec v lset rset) x)
            [ (injectCtr "left", [name],
               fun [hn] -> gFun [namecur]
                             (fun [hcur] ->
                                proof_map :=
                                  IntMap.add n (fun e -> gVar hn) !proof_map;
                                lproof hcur))
            ; (injectCtr "right", ["neq"],
               fun _ -> gFun [namecur] (fun [hcur] -> rproof hcur))
            ]) [gVar hcur]
    )
  in

  let match_inp_left (x : var) (inp : var) (pat : matcher_pat)
        (left : coq_expr * (var -> coq_expr)) (right  : coq_expr * (var -> coq_expr))
    : coq_expr * (var -> coq_expr) =
    let (lset, lproof) = left in
    let (rset, rproof) = right in
    (* The position of the input. A bit of a hack *)
    let pos =
      let rec aux n l =
        match l with
        | [] -> failwith "input not found"
        | x :: l -> if x = inp then n else aux (n+1) l
      in
      let p = aux 1 input_vars in
      if p < n then p else p + 1
    in
    let ret v left right =
      ret_type_left_inps
        v
        (construct_match (gVar v) ~catch_all:(Some rset) [(pat, lset)])
        x pos
    in
    let namecur = Printf.sprintf "Hcur%d" n in
    (construct_match_with_return
       (gVar inp) ~catch_all:(Some rset) "s" (fun v -> hole)
       [(pat, lset)],
     fun hcur ->
       gApp
         (construct_match_with_return
            (gVar inp) ~catch_all:(Some (gFun [namecur] (fun [hcur] -> rproof hcur))) "s" (fun v -> ret v lset rset)
            [(pat, gFun [namecur] (fun [hcur] ->lproof hcur))]) [gVar hcur])
  in

  let stMaybe_left (y : var) (opt : bool) (exp : coq_expr * (var -> (var -> coq_expr) -> coq_expr))
        (x : string) (checks : ((coq_expr -> coq_expr) * int) list)
    : coq_expr * (var -> (var -> coq_expr) -> coq_expr) =
    let ret_type set =
      gImpl set hole
    in
    let rec sumbools_to_bool x lst =
      match lst with
      | [] ->
        let (set, proof) = exp in
        gApp set [gVar x]
      | (chk, _) :: lst' ->
        matchDec (chk (gVar x)) (fun heq -> gFalse) (fun hneq -> sumbools_to_bool x lst')
    in
    let rec sumbools_to_bool_proof x hl hr cont lst : coq_expr =
      match lst with
      | [] ->
        let (set, proof) = exp in
        gApp (gFun ["Hcur"] (fun [hcur] -> proof hcur cont)) [(gConjIntro (gVar hl) (gVar hr))]
      | (chk, n) :: lst' ->
        let set = sumbools_to_bool x lst' in
        let name = Printf.sprintf "Hp%d" n in
        let namecur = Printf.sprintf "Hl%d" n in
        gApp
          (gMatchReturn (chk (gVar x))
             "s" (* as clause *)
             (fun v -> ret_type (ret_type_dec v gFalse set))
             [ (injectCtr "left", ["heq"],
                fun [hn] ->
                  gFun [namecur]
                    (fun [hcur] -> false_ind hole (gVar hcur)))
             ; (injectCtr "right", [name],
                fun [hn] ->
                  gFun [namecur]
                    (fun [hcur] ->
                       proof_map :=
                         IntMap.add n (fun e -> gVar hn) !proof_map;
                       sumbools_to_bool_proof x hcur hr cont lst'))
             ]) [gVar hl]
    in 
    (gFun [x] (fun [x] -> sumbools_to_bool x checks),
     fun hcur cont ->
       gMatch (gVar hcur)
         [(injectCtr "conj", ["Hl"; "Hr"],
           fun [hl; hr] ->
             sumbools_to_bool_proof (fresh_name x) hl hr cont checks)
         ])
  in 

  (* Left to right direction *)

  let ret_type_left_ind  =
    let iter_body args : coq_expr =
      gRecFunInWithArgs
        "aux_iter" (gArg ~assumName:(gVar (fresh_name "size")) () :: inputs) 
        (fun (rec_name, size::vars) -> aux_iter rec_name size vars)
        (fun rec_name -> gApp (gVar rec_name) args)
    in
    gFun ["n"]
      (fun [n] ->
         gProdWithArgs
           ((gArg ~assumName:(gVar (fresh_name "x")) ()) :: inputs)
           (fun (x :: inputs) ->
              ret_type_left (iter_body ((gVar n) :: (List.map gVar inputs))) x inputs)
      )
  in

  let rec elim_base_cases x hin ctrs m inputs : coq_expr =
    let hr = Printf.sprintf "Hl%d" m in
    let hl = Printf.sprintf "Hr%d" m in
    let handle_branch' (c : dep_ctr) : (coq_expr * (var -> coq_expr)) * bool =
      handle_branch n dep_type inputs
        fail_exp_left (ret_exp_left c) class_method_left class_methodST_left
        (rec_method_left (gVar (make_up_name ())) (gVar (make_up_name ())))
        bind_left (stMaybe_left x) (check_expr_left x) (match_inp_left x)
        (failwith "zoe fix me!")
        gen_ctr (fun _ -> ()) c
    in
    match ctrs with
    | [] -> false_ind hole (gVar hin)
    | c :: ctrs' ->
      let (p, b) : (coq_expr * (var -> coq_expr)) * bool = handle_branch' c in
      if b then
        gMatch (gVar hin)
          [(injectCtr "or_introl", [hl],
            fun [hl] -> snd p hl);
           (injectCtr "or_intror", [hr],
            fun [hr] -> elim_base_cases x hr ctrs' (m + 1) inputs)]
      else elim_base_cases x hin ctrs' (m + 1) inputs
  in

  let rec elim_ind_cases x hin size ih ctrs m inputs : coq_expr =
    let hr = Printf.sprintf "Hl%d" n in
    let hl = Printf.sprintf "Hr%d" n in
    let handle_branch' c : (coq_expr * (var -> coq_expr)) * bool =
      handle_branch n dep_type inputs
        fail_exp_left (ret_exp_left c) class_method_left class_methodST_left
        (rec_method_left (gVar ih) (gVar size))
        bind_left (stMaybe_left x) (check_expr_left x) (match_inp_left x)
        (failwith "zoe fix me!")
        gen_ctr (fun _ -> ()) c
    in
    match ctrs with
    | [] -> false_ind hole (gVar hin)
    | c :: ctrs' ->
      let (p, b) : (coq_expr * (var -> coq_expr)) * bool = handle_branch' c in
      gMatch (gVar hin)
        [(injectCtr "or_introl", [hl],
          fun [hl] -> snd p hl);
         (injectCtr "or_intror", [hr],
          fun [hr] -> elim_ind_cases x hr size ih ctrs' (m + 1) inputs)]
  in

  let left_base_case =
    gFun ["x"]
      (fun [x] ->
         gFunWithArgs
           inputs
           (fun inputs ->
              gFun ["hin"]
                (fun [hin] -> elim_base_cases x hin ctrs 0 inputs)))
  in

  let left_ind_case =
    gFun ["size"; "IHs"; "x"]
      (* XXX need inputs with gen here!!!!!! *)
      (fun [size; ihs; x] ->
         gFunWithArgs
           inputs
           (fun inputs ->
              gFun ["hin"]
                (fun [hin] ->
                   elim_ind_cases x hin size ihs ctrs 0 inputs)))
  in

  let leftp (x : var) : coq_expr =
    (* Hin : \bigcup(n : nat) (succ ^ n zero) x *)
    gFun ["Hin"]
      (fun [hin] ->
         gMatch (gVar hin)
           [(injectCtr "ex_intro", ["s"; "Hc"],
             fun [s; hc] ->
               gMatch (gVar hc)
                 [(injectCtr "conj", ["Hl"; "Hin"],
                   fun [hl; hin] ->
                     gApp
                       (nat_ind ret_type_left_ind left_base_case left_ind_case)
                       (((gVar s) :: (gVar x) :: (List.map gVar input_vars)) @ [gVar hin])
                  )]
            )])
  in

  (* completeness proof *)

  let ctx_map : ctxMap ref = ref IntMap.empty in

  let is_rec_call dt =
    match dt with
    | DTyCtr (c,dts) -> c == gen_ctr
    | _ -> false
  in

  let rec make_context typ off (orp : coq_expr -> coq_expr) (cont : btyp) : coq_expr =
    let rec aux typ off m n exp =
      match typ with
      | DArrow (_, dt2) | DProd ((_, _), dt2) when off > 0 ->
        make_context dt2 (off - 1) orp cont
      | DArrow (dt1, dt2) ->
        let hn = Printf.sprintf "H%d" n in
        if (is_rec_call dt1) then
          let ihn = Printf.sprintf "IH%d" n in
          gFun [hn; ihn]
            (fun [hn; ihn] ->
               (* add to map *)
               ctx_map :=
                 IntMap.add n (gVar hn, gVar ihn) !ctx_map;
               aux dt2 off m (n + 1) exp)
        else
          gFun [hn]
            (fun [hn] ->
               (* add to map *)
               ctx_map :=
                 IntMap.add n (gVar hn, hole) !ctx_map;
               aux dt2 off m (n + 1) exp)
      | DProd ((x, dt1), dt2) ->
        (* the assumption is that this will be implicit when needed
           so we do not need to add them to a map *)
        gFun [var_to_string x] (fun [x] -> aux dt2 off (m + 1) n exp)
      | DTyCtr (_, dts) ->
        let (proof, ctx) = cont in
        ctx
          (fun sum lst ->
             gExIntro_impl (gSucc sum)
               (gConjIntro gI (orp (proof sum hole (List.length lst) (List.rev lst) (fun id -> id)))))
          (gInt 0) []
      | _ -> failwith "Wrong type"
    in
    aux typ off 0 0 cont
  in

  (* XXX we might need to handle this locally *)
  let fail_exp_right : (coq_expr -> coq_expr) * btyp =
    ((fun s -> set_empty),
     ((fun sum fail sproof lst dstr -> fail), fun iproof sum lst -> iproof sum lst))
  in

  let ret_exp_right (x : coq_expr) : (coq_expr -> coq_expr) * btyp =
    ((fun s -> set_singleton x),
     ((fun sum fail sproof lst dstr -> gEqRefl hole), fun iproof sum lst -> iproof sum lst))
  in

  let class_method_right : (coq_expr -> coq_expr) * atyp =
    ((fun s -> set_full),
     (fun cont ->
        let (iproof, ctx) = cont in
        ((fun sum fail sproof lst dstr ->
            gExIntro_impl hole (gConjIntro (dstr gI) (iproof sum fail sproof lst (fun x -> x)))),
         ctx)))
  in

  let class_methodST_right (n : int) (pred : coq_expr) : (coq_expr -> coq_expr) * atyp =
    ((fun s -> pred),
     (fun cont ->
        let (iproof, ctx) = cont in
        ((fun sum fail sproof lst dstr ->
            let (h, _) =
              try IntMap.find n !ctx_map
              with Not_found -> failwith "class_method: Proof not found"
            in
            gExIntro_impl hole (gConjIntro (dstr h) (iproof sum fail sproof lst (fun x -> x)))),
         ctx)))
  in

  let rec_method_right (n : int) (l : coq_expr list)
    : (coq_expr -> coq_expr) * atyp =
    let iter_body args : coq_expr =
      gRecFunInWithArgs
        "aux_iter" (gArg ~assumName:(gVar (fresh_name "size")) () :: inputs) 
        (fun (rec_name, size::vars) -> aux_iter rec_name size vars)
        (fun rec_name -> gApp (gVar rec_name) args)
    in
    let xn = Printf.sprintf "y%d" n in
    let pcn = Printf.sprintf "Pc%d" n in
    let pn = Printf.sprintf "P%d" n in
    ((fun size -> iter_body (size :: l)),
     (fun cont ->
        let (iproof, ctx) = cont in
        ((fun sum fail sproof lst dstr ->
            match lst with
            | [] -> failwith "Proof list is empty"
            | (p, s) :: ps ->
              let rec make_leq_proof n =
                if n = 1 then (leq_addl s hole)
                else plus_leq_compat_l (make_leq_proof (n - 1))
              in
              (* just for debugging *)
              (* let mon_proof l = gApp (gInject "pmon") l in *)
              let h =
                gApp (mon_proof l) [hole; sum; make_leq_proof sproof; hole; p]
              in
              gExIntro_impl hole (gConjIntro (dstr h) (iproof sum fail (sproof - 1) ps (fun x -> x))))
         ,
         (fun iproof sum lst ->
            let (h, ih) =
              try IntMap.find n !ctx_map
              with Not_found -> failwith "rec method : Proof not found"
            in
            gMatch ih
              [(injectCtr "ex_intro", [xn; pcn],
                fun [xn; pcn] ->
                  gMatch (gVar pcn)
                    [(injectCtr "conj", ["HT"; pn],
                      fun [_; pn] -> ctx iproof (plus sum (gVar xn)) ((gVar pn, sum) :: lst)
                     )]
               )]
         ))))
  in

  let bind_right (opt : bool) (m : (coq_expr -> coq_expr) * atyp)
        (x : string) (f : var -> (coq_expr -> coq_expr) * btyp) : (coq_expr -> coq_expr) * btyp =
    let (m, cont) = m in
    ((fun s -> set_bigcup x (m s) (fun x -> fst (f x) s)),
     cont (snd (f (fresh_name x)))) (* XXX name hack *)
  in

  let ret_type_right (s : var) (left : coq_expr) (right : coq_expr) =
    gApp
      (gMatch (gVar s)
         [ (injectCtr "left", ["eq"], fun _ -> left)
         ; (injectCtr "right", ["neq"], fun _ -> right) ])
      [hole]
  in

  let check_expr_right (n : int) (scrut : coq_expr)
        (left : (coq_expr -> coq_expr) * btyp) (right : (coq_expr -> coq_expr) * btyp)
    : (coq_expr -> coq_expr) * btyp =
    let (lset, (lp, lctx)) = left in
    let (rset, (rp, rctx)) = right in
    let heq = Printf.sprintf "Heq%d" n in
    let hneq = Printf.sprintf "Hneq%d" n in
    let namecur = Printf.sprintf "Hcur%d" n in
    ((fun s ->
        gMatchReturn scrut
          "s" (* as clause *)
          (fun v -> hole)
          [ (injectCtr "left", ["eq" ] , fun _ -> lset s)
          ; (injectCtr "right", ["neq"], fun _ -> rset s) 
          ]),
     ((fun sum fail sproof lst dstr ->
         let proof cont =
           match
             (try
                Some (IntMap.find n !ctx_map)
              with Not_found -> None)
           with
           | Some (h, _) -> cont h
           | None ->
             cont (gEqRefl hole)
         in
         let contl heq h = gApp h [(gVar heq)] in
         let contr hneq h = gApp (gVar hneq) [h] in
         gMatchReturn scrut
           "s" (* as clause *)
           (fun v -> ret_type_right v (lset sum) (rset sum))
           [ (injectCtr "left", [heq],
              fun [heq] -> lp sum (false_ind hole (proof (contl heq))) sproof lst dstr)
           ; (injectCtr "right", [hneq],
              fun [hneq] -> rp sum (false_ind hole (proof (contr hneq))) sproof lst dstr)
           ]),
      (fun iproof sum lst -> lctx (fun sum lst -> rctx iproof sum lst) sum lst)
      (* This is OK because one of the two contexts will be empty *)
     ))
  in

  let match_inp_right (inp : var) (pat : matcher_pat)
        (left : (coq_expr -> coq_expr) * btyp) (right : (coq_expr -> coq_expr) * btyp)
    : (coq_expr -> coq_expr) * btyp =
    let (lset, lp) = left in
    let (rset, _) = right in
    let ret sum v left right =
      gApp (construct_match (gVar v) ~catch_all:(Some (rset sum)) [(pat, (lset sum))])
        [hole]
    in
    let namecur = Printf.sprintf "Hcur%d" n in
    ((fun s ->
        construct_match_with_return
          (gVar inp) ~catch_all:(Some (rset s)) "s" (fun v -> hole)
          [(pat, lset s)]),
     lp) (* because inputs should be already unified *)
  in

  let stMaybe_right (opt : bool) (exp : (coq_expr -> coq_expr) * atyp)
        (x : string) (checks : ((coq_expr -> coq_expr) * int) list)
    : (coq_expr -> coq_expr) * atyp =
    let (set, k) = exp in
    let ret_type_dec_prop (s : var) (left : coq_expr) (right : coq_expr) =
      gMatchReturn (gVar s)
        "s"
        (fun v -> gProp)
        [ (injectCtr "left", ["eq"], fun _ -> left)
        ; (injectCtr "right", ["neq"], fun _ -> right) ]
    in
    let rec sumbools_to_bool x s lst =
      match lst with
      | [] ->
        gApp (set s) [gVar x]
      | (chk, _) :: lst' ->
        matchDec (chk (gVar x)) (fun heq -> gFalse) (fun hneq -> sumbools_to_bool x s lst')
    in
    let rec sumbools_to_bool_proof x exp sum lst : coq_expr =
      match lst with
      | [] -> exp
      | (chk, n) :: lst' ->
        let set = sumbools_to_bool x sum lst' in
        let heq = Printf.sprintf "Heq%d" n in
        let hneq = Printf.sprintf "Hneq%d" n in
        let (h, _) =
          try IntMap.find n !ctx_map
          with Not_found -> failwith "stMaybe: Proof not found"
        in
        gMatchReturn (chk (gVar x))
          "s" (* as clause *)
          (fun v -> ret_type_dec_prop v gFalse set)
          [ (injectCtr "left", [heq],
             fun [heq] -> false_ind hole (gApp h [gVar heq]))
          ; (injectCtr "right", [hneq],
             fun [hneq] -> sumbools_to_bool_proof x exp sum lst')
          ]
    in 
    ((fun s -> gFun [x] (fun [x] -> sumbools_to_bool x s checks)),
     (((fun cont ->
          let (proof, ctx) = k cont in
          (fun sum fail sproof lst dstr ->
             proof sum fail sproof lst (fun e -> dstr (sumbools_to_bool_proof (fresh_name x) e sum checks))),
          ctx))))
  in

  (* Left to right direction *)

  let ret_type_right_ind inps x =
    let iter_body args : coq_expr =
      gRecFunInWithArgs
        "aux_iter" (gArg ~assumName:(gVar (fresh_name "size")) () :: inputs) 
        (fun (rec_name, size::vars) -> aux_iter rec_name size vars)
        (fun rec_name -> gApp (gVar rec_name) args)
    in
    gApp
      (set_bigcup "n" set_full (fun n -> iter_body ((gVar n) :: inps)))
      [gVar x]
  in

  let rec split_gen (i : int) (l : 'a list) acc : ('a * ('a list)) =
    if i <= 1 then
      match l with
      | [] -> failwith "Generator not found"
      | x :: l' -> (x, (List.rev acc) @ l')
    else
      match l with
      | [] -> failwith "Generator not found"
      | x :: l' -> split_gen (i-1) l' (x :: acc)
  in

  let rec inputsWithGen i l g = 
    if i <= 1 then g :: l
    else let (h::t) = l in h :: (inputsWithGen (i-1) t g)
  in


  let rec split_params dt l acc pos =
    match dt with 
    | DProd  ((x,d1), d2) ->
      begin
        match l with
        | [] -> failwith "Expecting parameter"
        | inp :: inps ->
          split_params d2 inps (inp :: acc) (pos+1)
      end
    | _ -> (List.rev acc, l, pos)
  in

  let (param_vars, index_vars, off) = split_params dep_type input_vars [] 0 in
  let (_, indexes, _) =  split_params dep_type inputs [] 0 in
  let params = List.map gVar param_vars in
  (* take out params
     calculate new position for the generator 
  *)

  let rec rightp gen : coq_expr =
    let ind = gApp (gInject ((ty_ctr_to_string gen_ctr) ^ "_ind")) params in
    let handle_branch' c : ((coq_expr -> coq_expr) * btyp) * bool =
      handle_branch n dep_type input_vars (* XXX name hack? *)
        fail_exp_right ret_exp_right class_method_right class_methodST_right
        rec_method_right
        bind_right stMaybe_right check_expr_right match_inp_right
        (failwith "zoe fix me!")
        gen_ctr (fun _ -> ()) c
    in
    let rec cases ctrs (orp : coq_expr -> coq_expr) : coq_expr list =
      match ctrs with
      | [] -> []
      | c :: ctrs' ->
        let (_, typ) = c in
        let ((_, p), b) = handle_branch' c in
        (make_context typ off orp p) :: (cases ctrs' (fun x -> gOrIntroR (orp x)))
    in
    gApp
      (gApp
         ind
         (gFunWithArgs
            (inputsWithGen (n - off) indexes (gArg ~assumName:(gVar (fresh_name "_gen")) ()))
            (fun inpg -> let (g, inps) = split_gen (n - off) inpg [] in
              ret_type_right_ind (params @ (List.map gVar inps)) g) ::
          (cases ctrs (fun e -> gOrIntroL e))))
      (List.map gVar (inputsWithGen (n - off) index_vars gen))
  in

  let spec =
    gFun ["x"]
      (fun [x] -> gConjIntro (leftp x) (rightp x))
  in
  *)
  (* msg_debug (str "zero"); *)
  (* debug_coq_expr zero_set; *)
  msg_debug (str "iter");
  debug_coq_expr iter_body;
(*  msg_debug (str "spec"); 
  debug_coq_expr spec;
  msg_debug (str ("dep type: " ^ (dep_type_to_string dep_type)));
 *)
  (* msg_debug (str "mon proof"); *)
  (* debug_coq_expr (mon_proof (List.map gVar input_vars)); *)
  (* msg_debug (str "completeness"); *)
  (* debug_coq_expr (gFun ["x"] *)
  (*                   (fun [x] -> rightp x)); *)

  gRecord [("iter", iter_body); ("mon", hole); ("spec", hole)]
           (* ("mon", mon_proof (List.map gVar input_vars)); ("spec", spec)] *)
