open Pp
open Libnames
open Util
open Constrexpr
open GenericLib
open GenLib
open ArbitrarySizedST
open CheckerSizedST
open Error
open Unify
(*   
open SizedProofs
open GenSTCorrect
open GenSizedSTMonotonic
open GenSizedSTSizeMonotonic
 *)

(** Derivable classes *)
type derivable =
  | DecOpt 
  | ArbitrarySizedSuchThat
  | GenSizedSuchThatMonotonicOpt
  | GenSizedSuchThatSizeMonotonicOpt
  | GenSizedSuchThatCorrect
  | SizedProofEqs

let derivable_to_string = function
  | DecOpt -> "DecOpt"
  | ArbitrarySizedSuchThat -> "GenSizedSuchThat"
  | GenSizedSuchThatMonotonicOpt -> "SizeMonotonicOpt"
  | SizedProofEqs -> "SizedProofEqs"
  | GenSizedSuchThatSizeMonotonicOpt -> "SizedMonotonicOpt"
  | GenSizedSuchThatCorrect -> "SizedSuchThatCorrect"

(** Name of the instance to be generated *)
let mk_instance_name der tn =
  var_to_string (fresh_name ((derivable_to_string der) ^ tn))

let derive_dependent (class_name : derivable)
                     (constructor : constr_expr)
                     (umap : range UM.t)
                     (tmap : dep_type UM.t)
                     (input_names : var list)
                     (input_ranges : range list)
                     (ty_ctr, ty_params, ctrs, dep_type)
                     (letbinds : var list option)
                     (result : unknown) =
  let ctr_name = 
    match constructor with 
    | { CAst.v = CRef (r,_); _ } -> string_of_qualid r
  in
  let instance_name = mk_instance_name class_name ctr_name in

  (* type constructor *)
  let coqTyCtr = gTyCtr ty_ctr in
  (* parameters of the type constructor *)
  let coqTyParams = List.map gTyParam ty_params in

  (* Fully applied type constructor *)
  let full_dt = gApp ~explicit:true coqTyCtr coqTyParams in

  (* Type parameters as arguments *)
  let params = List.map (fun tp -> gArg ~assumName:(gTyParam tp) ()) ty_params in

  (* List of input unknowns *)
  let actual_input_list =
    List.filter (fun u -> UM.find u umap == FixedInput) input_names in

  (* Inputs as arguments *)
  let actual_input_args = 
    List.map (fun u -> gArg ~assumName:(gVar u) ~assumType:(gType ty_params (UM.find u tmap)) ())
      actual_input_list 
  in

  (* The type we are generating for -- not the predicate! *)
  let full_gtyp = gType ty_params (UM.find result tmap) in

  let gen_needed = [] in
  let dec_needed = [] in

  (* The dependent generator  *)
  let gen =
    arbitrarySizedST ty_ctr ty_params ctrs dep_type input_names
      input_ranges umap tmap actual_input_args result coqTyCtr
  in

  (* Generate typeclass constraints. For each type parameter "A" we need `{_ : <Class Name> A} *)
  let instance_arguments = match class_name with
    | DecOpt -> params @ actual_input_args
    | ArbitrarySizedSuchThat ->
      params
(*      @ gen_needed
      @ dec_needed
      @ self_dec
      @ arb_needed *)
      @ actual_input_args
    | GenSizedSuchThatMonotonicOpt -> params 
    | SizedProofEqs -> params @ actual_input_args
    | GenSizedSuchThatCorrect -> params @ actual_input_args
    | GenSizedSuchThatSizeMonotonicOpt -> params @ actual_input_args
  in

  (* Fully applied predicate (parameters and constructors) *)
  let full_pred inputs =
    match letbinds with
    | None -> 
       gFun [Unknown.to_string result]
         (fun _ -> gApp (full_dt) (List.map gVar inputs))
    | Some letbinds ->
       gFun [Unknown.to_string result]
         (fun [result_var] ->
           gLetTupleIn result_var letbinds (gApp (gInject ctr_name) (List.map gVar inputs)))
  in

  
  (* TODO: Easy solution : add Arbitrary/DecOpt as a requirement for all type parameters. *)
  (*
  let self_dec = [] in 
  (*     (* Maybe somethign about type paramters here *)
     if !need_dec then [gArg ~assumType:(gApp (gInject (Printf.sprintf "DepDec%n" (dep_type_len dep_type))) [gTyCtr ty_ctr]) 
                            ~assumGeneralized:true ()] 
     else [] in
   *)

  (* The type of the dependent generator *)
  let gen_type = gGen (gOption full_gtyp) in


  (* Generate arbitrary parameters *)
  let arb_needed = 
    let rec extract_params = function
      | DTyParam tp -> ArbSet.singleton (DTyParam tp)
      | DTyVar _ -> ArbSet.empty
      | DTyCtr (_, dts) -> List.fold_left (fun acc dt -> ArbSet.union acc (extract_params dt)) ArbSet.empty dts
      | _ -> failwith "Unhandled / arb_needed"  in
    let tps = ArbSet.fold (fun dt acc -> ArbSet.union acc (extract_params dt)) !arbitraries ArbSet.empty in
    ArbSet.fold
      (fun dt acc ->
        (gArg ~assumType:(gApp (gInject "Arbitrary") [gType ty_params dt]) ~assumGeneralized:true ()) :: acc
      ) tps []
  in

  (* Generate typeclass constraints. For each type parameter "A" we need `{_ : <Class Name> A} *)
  let instance_arguments = match cn with
    | ArbitrarySizedSuchThat ->
      params
      @ gen_needed
      @ dec_needed
      @ self_dec
      @ arb_needed
      @ inputs
    | GenSizedSuchThatMonotonicOpt -> params 
    | SizedProofEqs -> params @ inputs
    | GenSizedSuchThatCorrect -> params @ inputs
    | GenSizedSuchThatSizeMonotonicOpt -> params @ inputs
  in

   *)  
  (* The instance type *)
  let instance_type iargs = match class_name with
    | ArbitrarySizedSuchThat ->
       gApp (gInject (derivable_to_string class_name))
         [gType ty_params (UM.find result tmap);
          full_pred input_names]
    | DecOpt ->
       gApp (gInject (derivable_to_string class_name))
         [ gApp (full_dt) (List.map gVar input_names) ]

    | SizedProofEqs ->
       gApp (gInject (derivable_to_string class_name))
         [full_pred input_names]
      
(*      
    | GenSizedSuchThatMonotonicOpt ->

      gProdWithArgs
        ((gArg ~assumType:(gInject "nat") ~assumName:(gInject "size") ()) :: inputs)
        (fun (size :: inputs) ->
(*         let (params, inputs) = list_take_drop (List.length params) paramsandinputs in *)
           gApp (gInject (class_name cn))
                (*              ((List.map gVar params) @  *)
                ([gApp ~explicit:true (gInject "arbitrarySizeST")
                  [full_gtyp; full_pred (List.map gVar inputs); hole; gVar size]]))
    | GenSizedSuchThatCorrect ->
      let pred = full_pred (List.map (fun n -> gVar (fresh_name n)) input_names) in
      gApp (gInject (class_name cn))
        [ pred 
        ; gApp ~explicit:true (gInject "arbitrarySizeST") [hole; pred; hole]]
    | GenSizedSuchThatSizeMonotonicOpt ->
      let pred = full_pred (List.map (fun n -> gVar (fresh_name n)) input_names) in
      gApp (gInject (class_name cn))
        [gApp ~explicit:true (gInject "arbitrarySizeST") [hole; pred; hole]]
   *)
  in


  let instance_record iargs =
    match class_name with
    | ArbitrarySizedSuchThat -> gen
    | DecOpt ->
       checkerSizedST ty_ctr ty_params ctrs dep_type input_names
         input_ranges umap tmap actual_input_args result coqTyCtr
   | SizedProofEqs ->
      (*       sizedEqProofs_body (class_name cn) ty_ctr ty_params ctrs dep_type input_names inputs n register_arbitrary *)
      SizedProofs.sizedEqProofs_body ty_ctr ty_params ctrs dep_type input_names input_ranges umap tmap actual_input_args result coqTyCtr

(*                              
    | GenSizedSuchThatMonotonicOpt ->
      msg_debug (str "mon type");
      debug_coq_expr (instance_type []);
      genSizedSTMon_body (class_name cn) ty_ctr ty_params ctrs dep_type input_names inputs n register_arbitrary
    | GenSizedSuchThatCorrect ->
      let moninst = (class_name GenSizedSuchThatMonotonicOpt) ^ ctr_name in
      let ginst = (class_name ArbitrarySizedSuchThat) ^ ctr_name in
      let setinst = (class_name SizedProofEqs) ^ ctr_name in
      genSizedSTCorr_body (class_name cn) ty_ctr ty_params ctrs dep_type input_names inputs n register_arbitrary
        (gInject moninst) (gInject ginst) (gInject setinst)
    | GenSizedSuchThatSizeMonotonicOpt ->
      genSizedSTSMon_body (class_name cn) ty_ctr ty_params ctrs dep_type input_names inputs n register_arbitrary
 *)
  in

  msg_debug (str "Instance Type: " ++ fnl ());
  debug_coq_expr (instance_type [gInject "input0"; gInject "input1"]);

  declare_class_instance instance_arguments instance_name instance_type instance_record
;;

                          
let create_t_and_u_maps explicit_args dep_type actual_args : (range UM.t * dep_type UM.t) =

  msg_debug (str ("create_t_u_maps for: " ^ dep_type_to_string dep_type) ++ fnl ());
  
  (* Local references - the maps to be generated *)
  let umap = ref UM.empty in
  let tmap = ref explicit_args in

  let rec populate_maps dep_type args =
    (* Recurse down the unnamed arrow arguments *)
    match dep_type,args with
    | DProd ((_, dt1), dt2), arg::args' 
    | DArrow (dt1, dt2), arg::args' ->
       msg_debug (str ("populating with: " ^ dep_type_to_string dt1) ++ fnl ());
       begin match arg with
       | ({ CAst.v = CRef (r,_) }, _) ->
          begin 
            let current_r = Unknown.from_string (string_of_qualid r ^ "_") in
            (* Lookup if the reference is meant to be generated *)
            try begin match UM.find current_r !tmap with
            | None ->
               (* First occurence, update tmap and umap *)
               tmap := UM.add current_r (Some  dt1) !tmap;
               umap := UM.add current_r (Undef dt1) !umap
            | Some dt' ->
               (* Check if the existing binding still typechecks *)
               if not (dt1 == dt') then qcfail "Ill-typed application in derivation"
            end
            with Not_found ->
              (* Logging the type in the tmap is ok, because we don't
                 update the umap in the "Some dt'" case above *)
              tmap := UM.add current_r (Some dt1) !tmap;
              umap := UM.add current_r FixedInput !umap;
          end
       (* TODO: If this is constructor applications, we need more type-checking machinery here *)
       | _ -> qcfail "Non-variable patterns not implemented"
       end;
       populate_maps dt2 args'
    (* Not an arrow -> Finalizer (TODO: add explicit fail?) *)
    | _ -> ()
  in 
  populate_maps dep_type actual_args;

  (* Remove the option from the type map and ensure all are exercised *)
  let tmap'=
    UM.mapi (fun u mt ->
        match mt with
        | Some t -> t
        | None -> failwith (Printf.sprintf "Pattern not exercised: %s\n" (var_to_string u))
      ) !tmap in
  (!umap, tmap')

                          
(* Assumption: 
   - generator-based classes include a "fun x => P ...." or "fun x => let (x1,x2,...) := x in P ..."
     where "..." are bound names (to be generated), unbound names (implicitly quantified arguments) 
     or Constructors applied to such stuff.
   - checker-based classes only include the name of the predicate "P". All arguments to P will
     be considered Fixed inputs
 *)
let dep_dispatch ind class_name : unit = 
  match ind with 
  | { CAst.v = CLambdaN ([CLocalAssum ([{ CAst.v = Name id; CAst.loc = _loc2 }], _kind, _type)], body) } -> (* {CAst.v = CApp ((_flag, constructor), args) }) } -> *)

    let idu = Unknown.from_string (Names.Id.to_string id ^ "_") in
     
    (* Extract (x1,x2,...) if any, P and arguments *)
    let (letbindsM, constructor, args) =
      match body with 
      | { CAst.v = CApp ((_flag, constructor), args) } -> (None, constructor, args)
      | { CAst.v = CLetTuple (name_list, _,
                              _shouldbeid,
                              { CAst.v = CApp ((_flag, constructor), args) } )} ->
         ( Some (List.map (function { CAst.v = name; _ } -> name ) name_list), constructor, args )
    in

    (* Parse the constructor's information into the more convenient generic-lib representation *)
    let (ty_ctr, ty_params, ctrs, dep_type) : (ty_ctr * (ty_param list) * (dep_ctr list) * dep_type) =
      match coerce_reference_to_dep_dt constructor with
      | Some dt -> msg_debug (str (dep_dt_to_string dt) ++ fnl()); dt 
      | None -> failwith "Not supported type"
    in 

    let (letbinds, init_umap, init_tmap) : (unknown list option * range UM.t * dep_type UM.t) =
      (* Create a temporary typing map for either the let binds/variable to be generated *)
      let letbinds =
        match letbindsM with
        | Some binds -> Some (List.map (fun (Names.Name id) -> Unknown.from_string (Names.Id.to_string id ^ "_")) binds)
        | None -> None
      in 
      
      let explicit_args =
        match letbinds with
        | Some binds -> 
           List.fold_left (fun map u -> UM.add u None map) UM.empty binds
        | None -> UM.singleton idu None
      in

      (* Call the actual creation function *)
      let (umap, tmap) = create_t_and_u_maps explicit_args dep_type args in

      (* Update with the toplevel variable as necessary *)
      match letbinds with
      | Some binds ->
         (* Still need to package together the tuple *)
         let bind_types = List.map (fun u ->
                              try UM.find u tmap
                              with Not_found -> failwith "All patterns should be exercised"
                            ) binds
         in
         let tmap' = UM.add idu (dtTupleType bind_types) tmap in
         let umap' =
           let pair_ctr = injectCtr "Coq.Init.Datatypes.pair" in
           let range = listToPairAux (fun (r1, r2) -> Ctr (pair_ctr, [RangeHole; RangeHole; r1; r2])) (List.map (fun u -> Unknown u) binds) in
           UM.add idu range umap in
         (letbinds, umap', tmap')
         
      | None -> (letbinds, umap, tmap)
    in

    (* Print map *)
    msg_debug (str "Initial map: " ++ fnl ());
    UM.iter (fun x r -> msg_debug (str ("Bound: " ^ (var_to_string x) ^ " to Range: " ^ (range_to_string r)) ++ fnl ())) init_umap;

    (* When we add constructors to the ranges, this needs to change *)
    let input_names = List.map (fun ({CAst.v = CRef (r, _)},_) -> fresh_name (string_of_qualid r ^ "_")) args in
    let input_ranges = List.map (fun v -> Unknown v) input_names in
    
    (* Call the derivation dispatcher *)
    derive_dependent class_name constructor init_umap init_tmap
      input_names input_ranges
      (ty_ctr, ty_params, ctrs, dep_type) letbinds idu 
  | { CAst.v = CApp ((_flag, constructor), args) } ->

     msg_debug (str "Parsing constructor information for checker" ++ fnl ());
     
    (* Parse the constructor's information into the more convenient generic-lib representation *)
    let (ty_ctr, ty_params, ctrs, dep_type) : (ty_ctr * (ty_param list) * (dep_ctr list) * dep_type) =
      match coerce_reference_to_dep_dt constructor with
      | Some dt -> msg_debug (str (dep_dt_to_string dt) ++ fnl()); dt 
      | None -> failwith "Not supported type"
    in

    (* When we add constructors to the ranges, this needs to change *)
    let input_names = List.map (fun ({CAst.v = CRef (r, _)},_) -> fresh_name (string_of_qualid r ^ "_")) args in
    let input_ranges = List.map (fun v -> Unknown v) input_names in

    (* Call the actual creation function *)
    let explicit_args = UM.empty (* No arguments to be generated *) in
    let (umap, tmap) = create_t_and_u_maps explicit_args dep_type args in

    let result = fresh_name "_result_bool" in
    let umap = UM.add result (Ctr (injectCtr "Coq.Init.Datatypes.true", [])) umap in
    let tmap = UM.add result (DTyCtr (ctr_to_ty_ctr (injectCtr "Coq.Init.Datatypes.bool"), [])) tmap in

    derive_dependent class_name constructor umap tmap input_names input_ranges
      (ty_ctr, ty_params, ctrs, dep_type) None result
  | _ -> qcfail "wrongformat/driver.ml4"

(*


(* This also has a lot of duplication.... *)
(** Checker derivation function *)
let deriveChecker (cn : derivable) (c : constr_expr) (instance_name : string) =
  let (ty_ctr, ty_params, ctrs, dep_type) : (ty_ctr * (ty_param list) * (dep_ctr list) * dep_type) =
    match coerce_reference_to_dep_dt c with
    | Some dt -> msg_debug (str (dep_dt_to_string dt) ++ fnl()); dt 
    | None -> failwith "Not supported type" in

  let ctr_name = 
    match c with 
    | { CAst.v = CRef (r,_) } -> string_of_qualid r
  in

  debug_coq_expr (gType ty_params dep_type);

  let (input_types : dep_type list) =
    let rec aux acc i = function
      | DArrow (dt1, dt2) 
      | DProd ((_,dt1), dt2) -> aux (dt1 :: acc) (i+1) dt2
      | DTyParam tp -> acc
      | DTyCtr (c,dts) -> acc
      | DTyVar _ -> acc
    in List.rev (aux [] 1 dep_type) (* 1 because of using 1-indexed counting for the arguments *)    in

  (* The instance type *)
  let instance_type iargs =
    match cn with
    | DecOpt ->
       gApp (gInject (class_name cn)) [gInject ctr_name]
  in

  let params = List.map (fun tp -> gArg ~assumName:(gTyParam tp) ()) ty_params in

  (* Name for type indices *)
  let input_names = List.mapi (fun i _ -> Printf.sprintf "input%d_" i) input_types in

  let inputs =
    List.map (fun (n,t) -> gArg ~assumName:(gVar (fresh_name n)) ~assumType:(gType ty_params t) ())
      (List.combine input_names input_types)
  in
  
  let instance_arguments =
    params @ inputs
  in 

  let instance_record =
    match cn with
    | DecOpt ->
       CheckerSized.checkerSized ty_ctr ty_params ctrs dep_type input_names inputs 
  in
  
  failwith "TODO"

(** Generic derivation function *)
let deriveDependent (cn : derivable) (c : constr_expr) (n : int) (instance_name : string) =

  let (ty_ctr, ty_params, ctrs, dep_type) : (ty_ctr * (ty_param list) * (dep_ctr list) * dep_type) =
    match coerce_reference_to_dep_dt c with
    | Some dt -> msg_debug (str (dep_dt_to_string dt) ++ fnl()); dt 
    | None -> failwith "Not supported type" in

  msg_debug (str (string_of_int n) ++ fnl ());
  debug_coq_expr (gType ty_params dep_type);

  let (input_types : dep_type list) =
    let rec aux acc i = function
      | DArrow (dt1, dt2) 
      | DProd ((_,dt1), dt2) ->
        if i == n then (* i == n means this is what we generate for - ignore *) 
          aux acc (i+1) dt2
        else (* otherwise this needs to be an input argument *)
          aux (dt1 :: acc) (i+1) dt2
      | DTyParam tp -> acc
      | DTyCtr (c,dts) -> acc
      | DTyVar _ -> acc
    in List.rev (aux [] 1 dep_type) (* 1 because of using 1-indexed counting for the arguments *)       
  in

  let ctr_name = 
    match c with 
    | { CAst.v = CRef (r,_) } -> string_of_qualid r
  in

  (* type constructor *)
  let coqTyCtr = gTyCtr ty_ctr in
  (* parameters of the type constructor *)
  let coqTyParams = List.map gTyParam ty_params in

  (* Fully applied type constructor *)
  let full_dt = gApp ~explicit:true coqTyCtr coqTyParams in

  (* Name for type indices *)
  let input_names = List.mapi (fun i _ -> Printf.sprintf "input%d_" i) input_types in
  
  let forGen = "_forGen" in


  let params = List.map (fun tp -> gArg ~assumName:(gTyParam tp) ()) ty_params in
  
  let inputs =
    List.map (fun (n,t) -> gArg ~assumName:(gVar (fresh_name n)) ~assumType:(gType ty_params t) ())
      (List.combine input_names input_types)
  in
  
  (* TODO: These should be generated through some writer monad *)
  (* XXX Put dec_needed in ArbitrarySizedSuchThat *)
  let gen_needed = [] in
  let dec_needed = [] in

  let self_dec = [] in 
  (*     (* Maybe somethign about type paramters here *)
     if !need_dec then [gArg ~assumType:(gApp (gInject (Printf.sprintf "DepDec%n" (dep_type_len dep_type))) [gTyCtr ty_ctr]) 
                            ~assumGeneralized:true ()] 
     else [] in*)

  let arbitraries = ref ArbSet.empty in

  (* this is passed as an arg to arbitrarySizedST. Yikes! *)
  let register_arbitrary dt =
    arbitraries := ArbSet.add dt !arbitraries
  in

  (* The type we are generating for -- not the predicate! *)
  let full_gtyp = (gType ty_params (nthType n dep_type)) in

  (* The type of the dependent generator *)
  let gen_type = gGen (gOption full_gtyp) in

  (* Fully applied predicate (parameters and constructors) *)
  let full_pred inputs =
    gFun [forGen] (fun [fg] -> gApp (full_dt) (list_insert_nth (gVar fg) inputs (n-1)))
  in

  (* The dependent generator  *)
  let gen =
    arbitrarySizedST
      ty_ctr ty_params ctrs dep_type input_names inputs n register_arbitrary
  in

  (* Generate arbitrary parameters *)
  let arb_needed = 
    let rec extract_params = function
      | DTyParam tp -> ArbSet.singleton (DTyParam tp)
      | DTyVar _ -> ArbSet.empty
      | DTyCtr (_, dts) -> List.fold_left (fun acc dt -> ArbSet.union acc (extract_params dt)) ArbSet.empty dts
      | _ -> failwith "Unhandled / arb_needed"  in
    let tps = ArbSet.fold (fun dt acc -> ArbSet.union acc (extract_params dt)) !arbitraries ArbSet.empty in
    ArbSet.fold
      (fun dt acc ->
        (gArg ~assumType:(gApp (gInject "Arbitrary") [gType ty_params dt]) ~assumGeneralized:true ()) :: acc
      ) tps []
  in

  (* Generate typeclass constraints. For each type parameter "A" we need `{_ : <Class Name> A} *)
  let instance_arguments = match cn with
    | ArbitrarySizedSuchThat ->
      params
      @ gen_needed
      @ dec_needed
      @ self_dec
      @ arb_needed
      @ inputs
    | GenSizedSuchThatMonotonicOpt -> params 
    | SizedProofEqs -> params @ inputs
    | GenSizedSuchThatCorrect -> params @ inputs
    | GenSizedSuchThatSizeMonotonicOpt -> params @ inputs
  in

  let rec list_take_drop n l = 
    if n <= 0 then ([], l)
    else match l with 
         | [] -> ([], [])
         | h::t -> let (take,drop) = list_take_drop (n-1) t in (h::take, drop) 
  in 
  
  (* The instance type *)
  let instance_type iargs = match cn with
    | ArbitrarySizedSuchThat ->
      gApp (gInject (class_name cn))
        [gType ty_params (nthType n dep_type);
         full_pred (List.map (fun n -> gVar (fresh_name n)) input_names)]
    | GenSizedSuchThatMonotonicOpt ->
      gProdWithArgs
        ((gArg ~assumType:(gInject "nat") ~assumName:(gInject "size") ()) :: inputs)
        (fun (size :: inputs) ->
(*         let (params, inputs) = list_take_drop (List.length params) paramsandinputs in *)
           gApp (gInject (class_name cn))
                (*              ((List.map gVar params) @  *)
                ([gApp ~explicit:true (gInject "arbitrarySizeST")
                  [full_gtyp; full_pred (List.map gVar inputs); hole; gVar size]]))
    | SizedProofEqs -> gApp (gInject (class_name cn)) [full_pred (List.map (fun n -> gVar (fresh_name n)) input_names)]
    | GenSizedSuchThatCorrect ->
      let pred = full_pred (List.map (fun n -> gVar (fresh_name n)) input_names) in
      gApp (gInject (class_name cn))
        [ pred 
        ; gApp ~explicit:true (gInject "arbitrarySizeST") [hole; pred; hole]]
    | GenSizedSuchThatSizeMonotonicOpt ->
      let pred = full_pred (List.map (fun n -> gVar (fresh_name n)) input_names) in
      gApp (gInject (class_name cn))
        [gApp ~explicit:true (gInject "arbitrarySizeST") [hole; pred; hole]]
  in

  let instance_record iargs =
    match cn with
    | ArbitrarySizedSuchThat -> gen
    | GenSizedSuchThatMonotonicOpt ->
      msg_debug (str "mon type");
      debug_coq_expr (instance_type []);
      genSizedSTMon_body (class_name cn) ty_ctr ty_params ctrs dep_type input_names inputs n register_arbitrary
    | SizedProofEqs ->
      sizedEqProofs_body (class_name cn) ty_ctr ty_params ctrs dep_type input_names inputs n register_arbitrary
    | GenSizedSuchThatCorrect ->
      let moninst = (class_name GenSizedSuchThatMonotonicOpt) ^ ctr_name in
      let ginst = (class_name ArbitrarySizedSuchThat) ^ ctr_name in
      let setinst = (class_name SizedProofEqs) ^ ctr_name in
      genSizedSTCorr_body (class_name cn) ty_ctr ty_params ctrs dep_type input_names inputs n register_arbitrary
        (gInject moninst) (gInject ginst) (gInject setinst)
    | GenSizedSuchThatSizeMonotonicOpt ->
      genSizedSTSMon_body (class_name cn) ty_ctr ty_params ctrs dep_type input_names inputs n register_arbitrary

  in

  msg_debug (str "Instance Type: " ++ fnl ());
  debug_coq_expr (instance_type [gInject "input0"; gInject "input1"]);

  declare_class_instance instance_arguments instance_name instance_type instance_record
;;
 *)

(*
VERNAC COMMAND EXTEND DeriveArbitrarySizedSuchThat
  | ["DeriveArbitrarySizedSuchThat" constr(c) "for" constr(n) "as" string(s1)] -> [deriveDependent ArbitrarySizedSuchThat c n s1]
END;;
  *)
