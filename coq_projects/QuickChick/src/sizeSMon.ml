open Util
open GenericLib
open SetLib
open CoqLib
open SemLib
open SizeUtils
   
let sizeSMon arg iargs  =

  let bases = List.filter (fun (_, ty) -> isBaseBranch arg._ty_ctr ty) arg._ctrs in

  let rec proof ih hleq ty n =
    let x = Printf.sprintf "x%d" n in
    match ty with
    | Arrow (ty1, ty2) ->
      let h =
        if arg._isCurrentTyCtr ty1
        then gApp ih [hole; hleq]
        else set_incl_refl
      in
      subset_set_eq_compat
        (semBindSize hole hole hole)
        (semBindSize hole hole hole)
        (incl_bigcup_compat h (gFun [x] (fun [x] -> proof ih hleq ty2 (n+1))))
    | _ -> set_incl_refl
  in

  let rec genCase ih hleq ctrs =
    match ctrs with
    | [] -> set_incl_refl
    | (ctr, ty) :: ctrs' ->
      let gproof =
        if isBaseBranch arg._ty_ctr ty then set_incl_refl
        else
          subset_set_eq_compat
            (bigcup_set1 hole (gPair (hole, hole)))
            (bigcup_set1 hole (gPair (hole, hole)))
            (proof ih hleq ty 0)
      in
      subset_set_eq_compat
        (eq_bigcupl hole hole (cons_set_eq hole hole))
        (eq_bigcupl hole hole (cons_set_eq hole hole))
        (subset_set_eq_compat
           (bigcup_setU_l hole hole hole)
           (bigcup_setU_l hole hole hole)
           (setU_set_subset_compat
              gproof
              (genCase ih hleq ctrs')))
  in

  (* Code that generates the generators. Copy-pasted for the fourth time. XXX factor it out *)

  (* Code from ArbitrarySize.v. Regenerate generators for type annotations *)
  let arb_body = ArbitrarySized.arbitrarySized_body arg._ty_ctr arg._ctrs iargs in

  let base_gens =
    let lst = (List.map (gen_list arg hole arb_body) bases) in
    (List.hd lst, gList (List.tl lst))
  in

  let base_gens_with_freq =
    let lst =
      (List.map
         (fun (ctr,ty') ->
           gPair (gInt 1, (gen_list arg hole arb_body (ctr,ty'))))
         bases)
    in
    (List.hd lst, gList (List.tl lst))
  in

  let ind_gens size =
    let lst =
      (List.map
         (fun (ctr,ty') ->
           gPair
             (Weightmap.lookup_weight ctr size,
              (gen_list arg (gVar size) arb_body (ctr,ty')))) arg._ctrs)
    in
    (List.hd lst, gList (List.tl lst))
  in

  let arb_aux s =
    gApp arb_body [s]
  in

  let ind_case s s1 s2 ihs1 hleq =
    let (lg, lgs) = ind_gens s1 in
    let (rg, rgs) = ind_gens s2 in
    match arg._ctrs with
    | [] -> failwith "Empty type"
    | [(ctr, ty)] -> (* Only one constructor -- should be a base case *)
      set_incl_refl
    | _ ->
      (subset_set_eq_compat
         (semFreqSize lg lgs s (fst_leq_proof arg._ctrs))
         (semFreqSize rg rgs s (fst_leq_proof arg._ctrs))
         (genCase ihs1 hleq arg._ctrs))
  in

  let rec seq_incl_proof ctrs =
    match ctrs with
    | [] -> incl_refl
    | (ctr, ty') :: ctrs' ->
      (if isBaseBranch arg._ty_ctr ty' then
         incl_hd_same
       else
         incl_tl) (seq_incl_proof ctrs')
  in

  let base_case s s2 =
    match arg._ctrs with
    | [] -> failwith "Empty type"
    | [(ctr, ty)] -> (* Only one constructor -- should be a base case *)
      set_incl_refl
    | _ :: _ ->
      match bases with
      | [] -> failwith "No base case!"
      | [(ctr, ty)] -> (* Only on base case and at least one inductive *)
        let (ig, igs) = ind_gens s2 in
        let rec proof ctrs =
          match ctrs with
          | [] -> failwith "Could not find the constructor"
          | (ctr', ty') :: ctrs' ->
            (* found the constructor *)
            if isBaseBranch arg._ty_ctr ty' then
              subset_respects_set_eq_r
                (* rewrites in the rhs *)
                (eq_bigcupl hole hole (cons_set_eq hole hole))
                (subset_respects_set_eq_r
                   (bigcup_setU_l hole hole hole)
                   (setU_subset_l hole
                      (subset_respects_set_eq_r
                         (bigcup_set1 hole (gPair (hole, hole)))
                         set_incl_refl)
                   ))
            else
              let p = proof ctrs' in
              subset_respects_set_eq_r
                (* rewrites in the rhs *)
                (eq_bigcupl hole hole (cons_set_eq hole hole))
                (subset_respects_set_eq_r
                   (bigcup_setU_l hole hole hole)
                   (setU_subset_r hole p)
                )
        in
        subset_respects_set_eq_r
          (semFreqSize ig igs s (fst_leq_proof arg._ctrs))
          (proof arg._ctrs)
      | _ ->
        (* The generators should be explicitly passed to the lemmas *)
        let (g, gs) = base_gens in
        let (fg, fgs) = base_gens_with_freq in
        let (ig, igs) = ind_gens s2 in
        subset_respects_set_eq_l
          (* first write oneOf as freq *)
          (oneOf_freq g gs s)
          (* Rewrite with the semantics of freq left and right *)
          (subset_set_eq_compat
             (semFreqSize fg fgs s (fst_leq_proof bases))
             (semFreqSize ig igs s (fst_leq_proof arg._ctrs))
             (incl_bigcupl (incl_subset hole hole (seq_incl_proof arg._ctrs))))
  in

  let ret_type s s1 s2 =
    let sem s' s =
      semGenSize (arb_aux s') s
    in
    gImpl
      (gIsTrueLeq s1 s2)
      (set_incl (sem s1 s) (sem s2 s))
  in

  let ret_type1 s =
    gFun ["s1"]
      (fun [s1] ->
        gForall
          (gInject "nat")
          (gFun ["s2"] (fun [s2] -> ret_type s (gVar s1) (gVar s2))))
  in

  let ret_type2 s s1 =
    gFun ["s2"]
      (fun [s2] -> ret_type s s1 (gVar s2))
  in

  let smon_proof =
    gFun ["s"]
      (fun [s] ->
         gApp ~explicit:true (gInject "nat_ind")
           [ret_type1 (gVar s);
            (gApp ~explicit:true (gInject "nat_ind")
               [ret_type2 (gVar s) (gInt 0);
                gFun ["Hleq"] (fun [h] -> set_incl_refl);
                gFun
                  ["s2"; "IHs2"; "Hleq"]
                  (fun [s2; ihs2; hleq] -> base_case (gVar s) s2)
               ]
            );
            (gFun
               ["s1"; "IHs1"]
               (fun [s1; ihs1] ->
                 gApp ~explicit:true (gInject "nat_ind")
                   [ret_type2 (gVar s) (gSucc (gVar s1));
                    gFun ["Hleq"] (fun [hleq] -> false_ind hole (lt0_False (gVar hleq)));
                    gFun
                      ["s2"; "IHs2"; "Hleq"]
                        (fun [s2; ihs2; hleq] ->
                          ind_case (gVar s) s1 s2 (gVar ihs1) (gVar hleq))
                   ]
               )
            )])
  in
  debug_coq_expr smon_proof;
  gRecord [("sizeMonotonic", smon_proof)]
