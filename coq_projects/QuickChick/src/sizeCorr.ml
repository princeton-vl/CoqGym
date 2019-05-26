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
open SemLib
open Error
open SizeUtils

let genCorr arg iargs inst_name s_inst_name c_inst_name mon_inst_name =
  let bases = List.filter (fun (_, ty) -> isBaseBranch arg._ty_ctr ty) arg._ctrs in

  (*  Could reuse code from SizeMon.ml here *)
  let rec mon_proof hmon ty n =
    let x = Printf.sprintf "m%d" n in
    match ty with
    | Arrow (ty1, ty2) ->
      let h = if arg._isCurrentTyCtr ty1 then hmon else hole in
      gApp ~explicit:true (gInject "bindMonotonic")
           [hole; hole; hole; hole; h; gFun [x] (fun [x] -> mon_proof hmon ty2 (n+1))]
    | _ -> hole
  in

  let rec proof ih hmon ty n =
    let x = Printf.sprintf "x%d" n in
    match ty with
    | Arrow (ty1, ty2) ->
      let h =
        if arg._isCurrentTyCtr ty1
        then ih
        else gInject "arbitraryCorrect"
      in
      let mon_proof_l = if arg._isCurrentTyCtr ty1 then hmon else hole in
      let mon_proof_r = gFun ["m"] (fun [m] -> mon_proof hmon ty2 0) in
      set_eq_trans
        (gApp (gInject "semBindSizeMonotonic") ~explicit:true
              [hole; hole; hole; hole; mon_proof_l; mon_proof_r])
        (gApp (gInject "eq_bigcup'")
              [h; gFun [x] (fun [x] -> proof ih hmon ty2 (n+1))])
    | _ -> gApp (gInject "semReturn") [hole]
  in

  let rec genCase ih hmon list_typ ctrs =
    match ctrs with
    | [] -> failwith "Invalid type"
    | [(ctr, ty)] ->
      set_eq_trans
        (eq_bigcupl hole hole (singl_set_eq hole hole))
        (set_eq_trans (bigcup_set1 hole list_typ) (proof ih hmon ty 0))
    | (ctr, ty) :: ctrs' ->
      set_eq_trans
        (eq_bigcupl hole hole (cons_set_eq hole hole))
        (set_eq_trans
           (bigcup_setU_l hole hole hole)
           (* Take the first sets of the union *)
           (setU_set_eq_compat
              (set_eq_trans (bigcup_set1 hole list_typ) (proof ih hmon ty 0))
              (genCase ih hmon list_typ ctrs')))
  in

  let mon_proof size =
    let args = (List.flatten (List.map (fun x -> [x; hole; hole; hole]) arg._coqTyParams)) @ [size] in
    gApp ~explicit:true mon_inst_name args
  in

  let g_instance =
    let args = (List.flatten (List.map (fun x -> [x; hole]) arg._coqTyParams)) in
    gApp ~explicit:true inst_name args
  in

  let s_instance =
    let args = (List.flatten (List.map (fun x -> [x; hole]) arg._coqTyParams)) in
    gApp ~explicit:true s_inst_name args
  in  

  let c_instance =
    let args = (List.flatten (List.map (fun x -> [x; hole; hole]) arg._coqTyParams)) in
    gApp ~explicit:true c_inst_name args
  in

  (* Code that generates the generators. Copy-pasted for the third time. XXX factor it out *)

  (* Code from ArbitrarySize.v. Regenerate generators for type annotations *)
  let arb_body = ArbitrarySized.arbitrarySized_body arg._ty_ctr arg._ctrs iargs in

  let gen_list size (ctr, ty) =
    let rec aux i acc ty : coq_expr =
      match ty with
      | Arrow (ty1, ty2) ->
        bindGen (if arg._isCurrentTyCtr ty1 then
                   gApp arb_body [size]
                 else gInject "arbitrary")
          (Printf.sprintf "p%d" i)
          (fun pi -> aux (i+1) ((gVar pi) :: acc) ty2)
      | _ -> returnGen (gApp ~explicit:true (gCtr ctr) (arg._coqTyParams @ List.rev acc))
    in aux 0 [] ty
  in

  let base_gens =
    let lst = (List.map (gen_list hole) bases) in
    (List.hd lst, gList (List.tl lst))
  in

  let ind_gens size =
    let lst =
      (List.map
         (fun (ctr,ty') ->
           gPair (Weightmap.lookup_weight ctr size,
                  (gen_list (gVar size) (ctr,ty')))) arg._ctrs)
    in
    (List.hd lst, gList (List.tl lst))
  in

  let ind_case hmon =
    gFun ["n"; "s"; "IHs"]
      (fun [n; s; ihs] ->
        let (gen, gens) = ind_gens n in
         match arg._ctrs with
         | [] -> failwith "Must have base cases"
         | [(ctr, ty)] -> proof (gVar ihs) hmon ty 0
         | _ :: _ ->
           set_eq_trans
             (semFreq gen gens (fst_leq_proof arg._ctrs))
             (genCase (gVar ihs) hmon (gPair (hole, hole)) arg._ctrs))
  in

  let base_case =
    match bases with
    | [] -> failwith "Must have base cases"
    | [(ctr, ty)] -> proof hole hole ty 0
    | _ :: _ ->
      set_eq_trans
        (gApp ~explicit:true (gInject "semOneOf") [hole; fst base_gens; snd base_gens])
        (genCase hole hole hole bases)
  in

  let ret_type =
    gFun ["n"; "s"]
      (fun [n; s] ->
        set_eq
          (gApp (gInject ("semGen")) [gApp (gInject "arbitrarySized") [gVar n]])
          (gVar s))
  in

  let gen_proof =
    gFun ["n"]
      (fun [n] ->
         nat_set_ind
           arg._full_dt g_instance s_instance c_instance base_case (ind_case (mon_proof (gVar n))) (gVar n))
  in
  msg_debug (str "Sized proof");
  debug_coq_expr gen_proof;
  gRecord [("arbitrarySizedCorrect", gen_proof)]
