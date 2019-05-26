open Util
open GenericLib
open SemLib
open CoqLib
open SizeUtils

let sizeMon arg size iargs genName =

  let rec proof ih ty n =
    let x = Printf.sprintf "x%d" n in
    match ty with
    | Arrow (ty1, ty2) ->
       let h = if arg._isCurrentTyCtr ty1 then ih else hole in
       (* bindMonotonic has type: 
          forall (A B : Type) (g : G A) (f : A -> G B),
          SizeMonotonic g -> (forall x : A, SizeMonotonic (f x)) -> 
          SizeMonotonic (bindGen g f) 

          If we are in a recursive proof, we need to specify a proof that 
          g is SizeMonotonic and the function recursively.
        *)
      gApp ~explicit:true (gInject "bindMonotonic")
        [hole; hole; hole; hole; h; gFun [x] (fun [x] -> proof ih ty2 (n+1))]
    | _ -> returnGenSizeMonotonic hole
  in

  let rec elim_cases h ih ctrs n =
    let hr = Printf.sprintf "Hl%d" n in
    let hl = Printf.sprintf "Hr%d" n in

    match ctrs with
    | [] -> false_ind hole h
    | (ctr, ty) :: ctrs' ->
      gMatch h
        [(injectCtr "or_introl", [hl],
          fun [hl] -> gMatch (gVar hl) [(injectCtr "erefl", [], fun [] -> proof ih ty 0)]);
         (injectCtr "or_intror", [hr],
          fun [hr] -> elim_cases (gVar hr) ih ctrs' (n+1))]
  in

  let arb_body = ArbitrarySized.arbitrarySized_body arg._ty_ctr arg._ctrs iargs in 
  let bases = List.filter (fun (_, ty) -> isBaseBranch arg._ty_ctr ty) arg._ctrs in

  let base_gens = gList (List.map (gen_list arg hole arb_body) bases) in
  let ind_gens size =
    gList
      (List.map
         (fun (ctr,ty') ->
            gPair (Weightmap.lookup_weight ctr size,
                   (gen_list arg (gVar size) arb_body (ctr,ty')))) arg._ctrs)
  in
  let base_case =
    match bases with
    | [] -> failwith "Must have base cases"
    | [(ctr, ty)] -> proof hole ty 0
    | _ :: _ ->
      (gApp
         (gInject "oneofMonotonic")
         [hole; hole; gFun [("x")] (fun [x] -> gFunTyped [("H", gApp (gInject "seq_In") [base_gens; gVar x])] (fun [h] -> elim_cases (gVar h) hole bases 0))])
  in

  let ind_case =
    gFun ["size"; "IHs"]
      (fun [size; ihs] ->
         match arg._ctrs with
         | [] -> failwith "Must have base cases"
         | [(ctr, ty)] -> proof (gVar ihs) ty 0
         | _ :: _ ->
           gApp
             (gInject "frequencySizeMonotonic_alt")
             [hole; hole; hole; gFun [("x")]
                                  (fun [x] ->
                                     gFunTyped [("H", gApp (gInject "seq_In") [ind_gens size; gVar x])]
                                       (fun [h] -> elim_cases (gVar h) (gVar ihs) arg._ctrs 0))])
  in

  let ret_type =
    gFun ["s"]
         (fun [s] -> 
          gApp (gInject "SizeMonotonic")
            (* [gApp (gInject "arbitrarySized") [gVar s]]) *)
            [gApp ~explicit:true (gInject "arbitrarySized") [arg._full_dt; genName; gVar s]])
  in 
  let mon_proof =
    gApp (gInject "nat_ind") [ret_type; base_case; ind_case; size]
  in
  debug_coq_expr mon_proof;
  mon_proof
