open Pp
open Util
open GenericLib
open SetLib
open CoqLib
open Feedback

let sizeM = gInject "QuickChick.Classes.size"

let succ_zero x = false_ind hole (succ_neq_zero_app hole x)
let base_ctrs ty_ctr ctrs = List.filter (fun (_, ty) -> isBaseBranch ty_ctr ty) ctrs

(* Produces the record of the sized typeclass *)                          
let sized_decl ty_ctr ctrs =
  let sizeOf_body x =
    (* For each constructor ctr of type ty: *)
    let create_branch rec_name (ctr, ty) =
      (ctr, generate_names_from_type "p" ty,
       (* if the constructor is not recursive, then it doesn't contribute to the depth *)
       if isBaseBranch ty_ctr ty then fun _ -> gInt 0
       (* Otherwise we recursively calculate the size of each recursive argument *)
       else
         fun vs ->
           let opts = fold_ty_vars (fun _ v ty' ->
               if sameTypeCtr ty_ctr ty' then [(gApp (gVar rec_name) [gVar v])]
               else []) (fun l1 l2 -> l1 @ l2) [] ty vs
           in
           (* And compute the maximum *)
           gApp (gInject "S") [maximum opts])
    in
    gRecFunIn "aux_size" ["x'"]
      (fun (aux_size, [x']) -> gMatch (gVar x') (List.map (create_branch aux_size) ctrs))
      (fun aux_size -> gApp (gVar aux_size) [gVar x])
  in
  gRecord [("size", gFun ["x"] (fun [x] -> sizeOf_body x))]
                          
let rec gen_args cty c_ctr n =
  match cty with
  | Arrow (ty1, ty2) ->
    if sameTypeCtr c_ctr ty1
    then
      let x  = Printf.sprintf "x%d" n in
      let ih = Printf.sprintf "IHx%d" n in
      let (args, ihargs) = gen_args ty2 c_ctr (n+1) in
      (x :: args, x :: ih :: ihargs)
    else
      let x  = Printf.sprintf "x%d" n in
      let (args, ihargs) = gen_args ty2 c_ctr (n+1) in
      (x :: args, x :: ihargs)
  | _ -> ([], [])

let rec dropIH cty ty_ctr l =
  match cty with
  | Arrow (ty1, ty2) ->
    (if sameTypeCtr ty_ctr ty1
     then
       match l with
       | x :: ihx :: l ->
         let (l1, l2) = dropIH ty2 ty_ctr l in
         (x :: l1, x :: l2)
       | _ -> failwith "Internal: Wrong number of arguments" 
     else
       match l with
       | x :: l ->
         let (l1, l2) = dropIH ty2 ty_ctr l in
         (x :: l1, l2)
       | _ -> failwith "Internal: Wrong number of arguments")
  | _ -> ([], [])



let zeroEqProof ty_ctr ctrs (ind_scheme : coq_expr) size zeroType zeroSized iargs =
  if List.is_empty ctrs then failwith "zeroEqProof call with no ctrs" else ();
  (* Common helpers, refactor? *)
  let coqTyCtr = gTyCtr ty_ctr in
  let coqTyParams = List.map gVar (list_drop_every 2 iargs) in
  let full_dt = gApp ~explicit:true coqTyCtr coqTyParams in

  let base_ctrs = base_ctrs ty_ctr ctrs in

  let rec elim_set h ty n =
    match ty with
    | Arrow (ty1, ty2) ->

      let w' = Printf.sprintf "x%d" n in
      let hw' = Printf.sprintf "Hx%d" n in
      let hc1 = Printf.sprintf "Hl%d" n in
      let hc2 = Printf.sprintf "Hr%d" n in

      gMatch (gVar h)
        [(injectCtr "ex_intro", [w'; hw'],
          fun [w'; hw'] ->
            gMatch (gVar hw')
              [(injectCtr "conj", [hc1; hc2],
                fun [hc1; hc2] ->
                  elim_set hc2 ty2 (n+1) 
                   )]
         )]
    | _ -> discriminate (gVar h)
  in

  let rec elim_unions h ctrs =
    match ctrs with
    | [(ctr, ty)] -> elim_set h ty 0
    | (ctr, ty) :: ctrs' ->
      gMatch (gVar h)
        [(injectCtr "or_introl", ["H1"],
          fun [h1] -> elim_set h1 ty 0);
         (injectCtr "or_intror", ["H1"],
          fun [h1] -> elim_unions h1 ctrs')] 
  in

  let rec intro_set ty ctr_args ctr acc =
    match ty with
    | Arrow (ty1, ty2) ->
      (match ctr_args with
       | arg :: ctr_args' ->
         gExIntro_impl arg (gConjIntro gI (intro_set ty2 ctr_args' ctr (arg :: acc)))
       | [] -> failwith "Internal: wrong number of arguments")
    | _ -> gEqRefl hole
             (* (gApp ~explicit:true (gCtr ctr) (coqTyParams @ List.rev acc)) *)
  in

  let rec intro_unions ctrs args curr_ctr =
    match ctrs with
    | [(ctr, ty)] ->
      if ctr = curr_ctr then
        intro_set ty args ctr []
      else
        failwith "Internal: cannot find constructor"
    | (ctr, ty) :: ctrs' ->
      if ctr = curr_ctr then
        gOrIntroL (intro_set ty args ctr [])
      else
        gOrIntroR (intro_unions ctrs' args curr_ctr)
  in


  let create_case (ctr, ty) =
    let (_, iargs) = gen_args ty ty_ctr 0 in
    gFun iargs (fun iargs ->
        let (args, _) = dropIH ty ty_ctr iargs in
        let elem = gApp ~explicit:true (gCtr ctr) (coqTyParams @ (List.map gVar args)) in
        let lhs = gApp zeroSized [elem] in
        let rhs = gEq (gApp size [elem]) (gInt 0) in
        if isBaseBranch ty_ctr ty then
          gConjIntro
            (gFunTyped [("H1", lhs)] (fun [h1] -> gEqRefl hole))
            (gFunTyped [("H1", rhs)] (fun [h1] -> intro_unions base_ctrs (List.map gVar args) ctr))
        else
          gConjIntro
            (gFunTyped [("H1", lhs)] (fun [h1] -> elim_unions h1 base_ctrs))
            (gFunTyped [("H1", rhs)] (fun [h1] -> succ_zero (gVar h1))))
  in
  let proofs = List.map create_case ctrs in
  gApp ~explicit:true ind_scheme (coqTyParams @ (zeroType :: proofs))


let succEqProof ty_ctr ctrs (ind_scheme : coq_expr) succType succSized iargs =
  (* Common helpers, refactor? *)
  let coqTyCtr = gTyCtr ty_ctr in
  let coqTyParams = List.map gVar (list_drop_every 2 iargs) in
  let full_dt = gApp ~explicit:true coqTyCtr coqTyParams in

  let base_ctrs = base_ctrs ty_ctr ctrs in

  let rec elim_set h leq ty n f ctr_flag size =
    match ty with
    | Arrow (ty1, ty2) ->

      let w' = Printf.sprintf "x%d" n in
      let hw' = Printf.sprintf "Hx%d" n in
      let hc1 = Printf.sprintf "Hl%d" n in
      let hc2 = Printf.sprintf "Hr%d" n in

      gMatch (gVar h)
        [(injectCtr "ex_intro", [w'; hw'],
          fun [w'; hw'] ->
            gMatch (gVar hw')
              [(injectCtr "conj", [hc1; hc2],
                fun [hc1; hc2] ->
                  let leq' =
                    if sameTypeCtr ty_ctr ty1
                    then (gVar hc1) :: leq
                    else leq
                  in
                  elim_set hc2 leq' ty2 (n+1) f ctr_flag size
               )]
         )]
    | _ ->
      if ctr_flag then 
        let rec leq_proof = function
              | [h] -> h
              | h :: hs ->
                gApp (gInject "max_lub_ssr") [hole; hole; gSucc (gVar size); h; leq_proof hs]
        in
        gMatch (gVar h) [(injectCtr "erefl", [], fun [] -> leq_proof (List.rev leq))]
      else discriminate (gVar h)
  in

  let rec elim_unions h ctrs curr_ctr size =
    match ctrs with
    | [(ctr, ty)] -> elim_set h [] ty 0 (fun x -> x) (curr_ctr = ctr) size
    | (ctr, ty) :: ctrs' ->
      gMatch (gVar h)
        [(injectCtr "or_introl", ["H1"],
          fun [h1] -> elim_set h1 [] ty 0 (fun x -> x) (curr_ctr = ctr) size);
         (injectCtr "or_intror", ["H1"],
          fun [h1] -> elim_unions h1 ctrs' curr_ctr size)] 
  in

  let rec intro_set leq ty ctr_args iargs ctr acc =
    match ty with
    | Arrow (ty1, ty2) ->
      (match ctr_args with
       | arg :: ctr_args' ->
         let (leq_l, leq_r, iargs') =
         if sameTypeCtr ty_ctr ty1
         then
           (match iargs with
            | [arg] ->
              (leq, leq, [])
            | arg :: args ->
              (gApp (gInject "max_lub_l_ssr") [hole; hole; hole; leq],
               gApp (gInject "max_lub_r_ssr") [hole; hole; hole; leq],
               args))
         else (gI, leq, iargs)
         in
         gExIntro_impl arg
           (gConjIntro leq_l (intro_set leq_r ty2 ctr_args' iargs' ctr (arg :: acc)))
       | [] -> failwith "Internal: wrong number of arguments")
    | _ -> gEqRefl (gApp ~explicit:true (gCtr ctr) (coqTyParams @ List.rev acc))
  in

  let rec intro_unions h ctrs args ihargs curr_ctr =
    match ctrs with
    | [(ctr, ty)] ->
      if ctr = curr_ctr then
        intro_set (gVar h) ty args ihargs ctr []
      else
        failwith "Internal: cannot find constructor"
    | (ctr, ty) :: ctrs' ->
      if ctr = curr_ctr then
        gOrIntroL (intro_set (gVar h) ty args ihargs ctr [])
      else
        gOrIntroR (intro_unions h ctrs' args ihargs curr_ctr)
  in

  let create_case size (ctr, ty) =
    let (_, iargs) = gen_args ty ty_ctr 0 in
    gFun iargs (fun iargs ->
        let (args, ihargs) = dropIH ty ty_ctr iargs in
        let elem = gApp ~explicit:true (gCtr ctr) (coqTyParams @ (List.map gVar args)) in
        let leq_size size = set_suchThat "x" full_dt (fun x -> gle (gApp sizeM [gVar x]) size) in
        let lhs = gApp (gApp succSized [(leq_size (gVar size))]) [elem] in
        let rhs = gApp (leq_size (gSucc (gVar size))) [elem] in
        if isBaseBranch ty_ctr ty then
          gConjIntro
            (gFunTyped [("H1", lhs)] (fun [h1] -> gApp (gInject "leq0n") [hole]))
            (gFunTyped [("H1", rhs)] (fun [h1] -> intro_unions h1 ctrs (List.map gVar args) ihargs ctr))
        else
          gConjIntro
            (gFunTyped [("H1", lhs)] (fun [h1] -> elim_unions h1 ctrs ctr size))
            (gFunTyped [("H1", rhs)] (fun [h1] -> intro_unions h1 ctrs (List.map gVar args) ihargs ctr)))
  in 
  let proofs size = List.map (create_case size) ctrs in
  gFun
    ["size"]
    (fun [size] -> gApp ~explicit:true ind_scheme (coqTyParams @ ((succType size) :: (proofs size))))


let sizeEqType ty_ctr ctrs ind_scheme iargs =

  (* Common helpers, refactor? *)
  let coqTyCtr = gTyCtr ty_ctr in
  let coqTyParams = List.map gVar (list_drop_every 2 iargs) in
  let full_dt = gApp ~explicit:true coqTyCtr coqTyParams in

  let bases = base_ctrs ty_ctr ctrs in

  (* Second reverse fold necessary *)
  let create_branch set tps (ctr,ty) =
    let rec aux i acc ty : coq_expr =
      match ty with
      | Arrow (ty1, ty2) ->
         let fi = Printf.sprintf "f%d" i in
         set_bigcup fi (if sameTypeCtr ty_ctr ty1 then set
                        else gFun [fi] (fun _ -> gInject "True"))
                    (fun f -> aux (i+1) (f::acc) ty2)
      | _ -> set_singleton (gApp ~explicit:true (gCtr ctr) (tps @ (List.map gVar (List.rev acc)))) in
    aux 0 [] ty in

  let lhs set ctrs = set_unions (List.map (create_branch set coqTyParams) ctrs) in
  let rhs size = set_suchThat "x" full_dt (fun x -> gEq (gApp sizeM [gVar x]) size) in

  let zeroSized = lhs hole bases in
  let succSized =
    gFunWithArgs [gArg ~assumName:(gInject "set") ()]
         (fun [set] -> lhs (gVar set) ctrs) in

  let zeroType =
    gFun ["f"] (fun [f] -> gIff (gApp zeroSized [gVar f]) (gApp (rhs (gInt 0)) [gVar f]))
  in

  let set_leq size = set_suchThat "x" full_dt (fun x -> gle (gApp sizeM [gVar x]) size) in
  let succType size =
    gFun ["f"] (fun [f] -> gIff (gApp (gApp succSized [set_leq (gVar size)]) [gVar f])
                                (gApp (set_leq (gSucc (gVar size))) [gVar f]))
  in

  let zeroSized_spec = zeroEqProof ty_ctr ctrs ind_scheme sizeM zeroType zeroSized iargs in
  let succSized_spec = succEqProof ty_ctr ctrs ind_scheme succType succSized iargs in

  msg_debug (str "zeroSized");
  debug_coq_expr zeroSized;
  msg_debug (str "succSized");
  debug_coq_expr succSized;
  msg_debug (str "zeroSized_spec");
  debug_coq_expr zeroSized_spec;
  debug_coq_expr succSized_spec;  
  gRecord [("zeroSized", zeroSized); ("succSized", succSized);
           ("zeroSized_spec", zeroSized_spec); ("succSized_spec", succSized_spec)]
