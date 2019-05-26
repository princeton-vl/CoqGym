open Vernacexpr
open Decl_kinds
open Pp
open Constr
open Names
open Declarations
open Libnames
open Util
open Constrexpr
open Constrexpr_ops
open Ppconstr
open Context
open Error

let cnt = ref 0 

let fresh_name n : Id.t =
    let base = Id.of_string n in

  (** [is_visible_name id] returns [true] if [id] is already
      used on the Coq side. *)
    let is_visible_name id =
      try
        ignore (Nametab.locate (Libnames.qualid_of_ident id));
        true
      with Not_found -> false
    in
    (** Safe fresh name generation. *)
    Namegen.next_ident_away_from base is_visible_name

let make_up_name () : Id.t =
  let id = fresh_name (Printf.sprintf "mu%d_" (!cnt)) in
  cnt := !cnt + 1;
  id
       
let hole = CAst.make @@ CHole (None, Misctypes.IntroAnonymous, None)

let id_of_name n = 
  match n with 
  | Name x -> x 
  | Anonymous -> failwith "id_of_name called with anonymous"

(* Everything marked "Opaque" should have its implementation be hidden in the .mli *)

type coq_expr = constr_expr (* Opaque *)

let debug_coq_expr (c : coq_expr) : unit =
  msg_debug (pr_constr_expr c)

let debug_constr env sigma (c : constr) : unit = 
  msg_debug (Printer.safe_pr_constr_env env sigma c ++ fnl ())

(* Non-dependent version *)
type var = Id.t (* Opaque *)
let var_of_id x = x         
let var_to_string = Id.to_string
let gVar (x : var) : coq_expr =
  CAst.make @@ CRef (qualid_of_ident x,None)

let qualid_to_coq_expr q = 
  mkRefC q

(* Maybe this should do checks? *)
let gInject s = 
  if s = "" then failwith "Called gInject with empty string";
  CAst.make @@ CRef (qualid_of_string s, None)

type ty_param = Id.t (* Opaque *)
let ty_param_to_string (x : ty_param) = Id.to_string x

let gTyParam = mkIdentC

type ty_ctr   = qualid (* Opaque *)
let ty_ctr_to_string (x : ty_ctr) = string_of_qualid x
let gInjectTyCtr s = 
  if s = "" then failwith "Called gInjectTyCtr with empty string";
  qualid_of_string s
let gTyCtr = qualid_to_coq_expr

type arg = local_binder_expr
let gArg ?assumName:(an=hole) ?assumType:(at=hole) ?assumImplicit:(ai=false) ?assumGeneralized:(ag=false) _ =
  let n = match an with
    | { CAst.v = CRef (qid, _); loc } -> (loc,Name (qualid_basename qid))
    | { CAst.v = CHole (v,_,_); loc } -> (loc,Anonymous)
    | a -> failwith "This expression should be a name" in
  CLocalAssum ( [CAst.make ?loc:(fst n) @@ snd n],
                  (if ag then Generalized (Implicit, Implicit, false)                       
                   else if ai then Default Implicit else Default Explicit),
                  at )

let arg_to_var (x : arg) =
  match x with
  | CLocalAssum ([{CAst.v = id; loc}], _ ,_ ) -> id_of_name id
  | _ -> qcfail "arg_to_var must be named"
  
let str_lst_to_string sep (ss : string list) = 
  List.fold_left (fun acc s -> acc ^ sep ^ s) "" ss

type coq_type = 
  | Arrow of coq_type * coq_type
  | TyCtr of ty_ctr * coq_type list
  | TyParam of ty_param

let rec coq_type_to_string ct = 
  match ct with
  | Arrow (c1, c2) -> Printf.sprintf "%s -> %s" (coq_type_to_string c1) (coq_type_to_string c2)
  | TyCtr (ty_ctr, cs) -> ty_ctr_to_string ty_ctr ^ " " ^ str_lst_to_string " " (List.map coq_type_to_string cs)
  | TyParam tp -> ty_param_to_string tp

type constructor = qualid (* Opaque *)
let constructor_to_string (x : constructor) = string_of_qualid x
let gCtr id = qualid_to_coq_expr id
let injectCtr s = 
  if s = "" then failwith "Called gInject with empty string";
  qualid_of_string s

let ty_ctr_to_ctr x = x
let ctr_to_ty_ctr x = x

let num_of_ctrs (c : constructor) =
  let env = Global.env () in
  let glob_ref = Nametab.global c in
  let ((mind,n),_) = Globnames.destConstructRef glob_ref in
  let mib = Environ.lookup_mind mind env in
  Array.length (mib.mind_packets.(n).mind_consnames)

module type Ord_ty_ctr_type = sig
  type t = ty_ctr 
  val compare : t -> t -> int
end

module type Ord_ctr_type = sig
  type t = constructor
  val compare : t -> t -> int
end

module Ord_ty_ctr = struct 
  type t = ty_ctr 
  let compare x y = Pervasives.compare (string_of_qualid x) (string_of_qualid y)
end

module Ord_ctr = struct
  type t = constructor
  let compare x y = Pervasives.compare (string_of_qualid x) (string_of_qualid y)
end

type ctr_rep = constructor * coq_type 
let ctr_rep_to_string (ctr, ct) = 
  Printf.sprintf "%s : %s" (constructor_to_string ctr) (coq_type_to_string ct)

type dt_rep = ty_ctr * ty_param list * ctr_rep list
let dt_rep_to_string (ty_ctr, ty_params, ctrs) = 
  Printf.sprintf "%s %s :=\n%s" (ty_ctr_to_string ty_ctr) 
                                (str_lst_to_string " "  (List.map ty_param_to_string ty_params))
                                (str_lst_to_string "\n" (List.map ctr_rep_to_string  ctrs))
                                 
(* Supertype of coq_type handling potentially dependent stuff - TODO : merge *)
type dep_type = 
  | DArrow of dep_type * dep_type (* Unnamed arrows *)
  | DProd  of (var * dep_type) * dep_type (* Binding arrows *)
  | DTyParam of ty_param (* Type parameters - for simplicity *)
  | DTyCtr of ty_ctr * dep_type list (* Type Constructor *)
  | DCtr of constructor * dep_type list (* Regular Constructor (for dependencies) *)
  | DTyVar of var (* Use of a previously captured type variable *)
  | DApp of dep_type * dep_type list (* Type-level function applications *)
  | DNot of dep_type (* Negation pushed up a level *)

module OrdDepType = struct
    type t = dep_type
    let compare = Pervasives.compare
end

let rec dep_type_to_string dt = 
  match dt with 
  | DArrow (d1, d2) -> Printf.sprintf "%s -> %s" (dep_type_to_string d1) (dep_type_to_string d2)
  | DProd  ((x,d1), d2) -> Printf.sprintf "(%s : %s) -> %s" (var_to_string x) (dep_type_to_string d1) (dep_type_to_string d2)
  | DTyCtr (ty_ctr, ds) -> ty_ctr_to_string ty_ctr ^ " " ^ str_lst_to_string " " (List.map dep_type_to_string ds)
  | DCtr (ctr, ds) -> constructor_to_string ctr ^ " " ^ str_lst_to_string " " (List.map dep_type_to_string ds)
  | DTyParam tp -> Printf.sprintf "(Param : %s)" (ty_param_to_string tp)
  | DTyVar tv -> var_to_string tv
  | DApp (d, ds) -> Printf.sprintf "(%s $ %s)" (dep_type_to_string d) (str_lst_to_string " " (List.map dep_type_to_string ds))
  | DNot d -> Printf.sprintf "~ ( %s )" (dep_type_to_string d)

type dep_ctr = constructor * dep_type
let dep_ctr_to_string (ctr, dt) = 
  Printf.sprintf "%s : %s" (constructor_to_string ctr) (dep_type_to_string dt)

type dep_dt = ty_ctr * ty_param list * dep_ctr list * dep_type
let dep_dt_to_string (ty_ctr, ty_params, ctrs, dep_type) = 
  Printf.sprintf "%s %s :=\n%s\n%s" (ty_ctr_to_string ty_ctr) 
                                    (str_lst_to_string " "  (List.map ty_param_to_string ty_params))
                                    (str_lst_to_string "\n" (List.map dep_ctr_to_string  ctrs))
                                    (dep_type_to_string dep_type)

let rec nthType1 i dt = 
  match i, dt with
  | 1, DArrow (dt1, _) 
  | 1, DProd  ((_, dt1), _) -> dt1
  | 1, _ -> failwith "Insufficient arrows"
  | _, DArrow (_, dt) 
  | _, DProd  (_, dt) -> nthType1 (i-1) dt
  | _, _ -> failwith "Insufficient arrows"

let nthType i dt =
  let msg =
    "type: " ^ dep_type_to_string dt ^ "\n" ^
    (Printf.sprintf "n: %n\n" i)
  in
  msg_debug (str msg);
  nthType1 i dt

let rec dep_result_type dt = 
  match dt with 
  | DArrow (_, dt') -> dep_result_type dt'
  | DProd  (_, dt') -> dep_result_type dt'
  | _ -> dt

let rec dep_type_len = function
  | DArrow (_, dt') 
  | DProd (_, dt') -> 1 + dep_type_len dt'
  | _ -> 0

(* Option monad *)
let (>>=) m f = 
  match m with
  | Some x -> f x 
  | None -> None

let isSome m = 
  match m with 
  | Some _ -> true
  | None   -> false
              
let rec cat_maybes = function 
  | [] -> []
  | (Some x :: mxs) -> x :: cat_maybes mxs
  | None :: mxs -> cat_maybes mxs

let foldM f b l = List.fold_left (fun accm x -> 
                                  accm >>= fun acc ->
                                  f acc x
                    ) b l

let sequenceM f l = 
  (foldM (fun acc x -> f x >>= fun x' -> Some (x' :: acc)) (Some []) l) >>= fun l -> Some (List.rev l)

let parse_type_params arity_ctxt =
  let param_names =
    foldM (fun acc decl ->
           match Rel.Declaration.get_name decl with 
           | Name id -> Some (id :: acc)
           | _ -> CErrors.user_err (str "Unnamed type parameter?" ++ fnl ())
          ) (Some []) arity_ctxt in
  param_names
(* For /trunk 
    Rel.fold_inside
      (fun accm decl ->
       accm >>= fun acc ->
       match Rel.Declaration.get_name decl with
       | Name id -> Some (id :: acc)
       | Anonymous -> msgerr (str "Unnamed type parameter?" ++ fnl ()); None
      ) [] arity_ctxt in 
  param_names
*)

let rec arrowify terminal l = 
  match l with
  | [] -> terminal
  | x::xs -> Arrow (x, arrowify terminal xs)

(* Receives number of type parameters and one_inductive_body.
   -> Possibly ty_param list as well? 
   Returns list of constructor representations 
 *)
let parse_constructors nparams param_names result_ty oib : ctr_rep list option =
  
  let parse_constructor (branch : constructor * constr) =
    let (ctr_id, ty_ctr) = branch in

    let (_, ty) = Term.decompose_prod_n nparams ty_ctr in
    
    let ctr_pats = if isConst ty then [] else fst (Term.decompose_prod ty) in

    let _, pat_types = List.split (List.rev ctr_pats) in

    msg_debug (str (string_of_qualid ctr_id) ++ fnl ());
    let rec aux i ty = 
      if isRel ty then begin 
        msg_debug (int (i + nparams) ++ str " Rel " ++ int (destRel ty) ++ fnl ());
        let db = destRel ty in
        if i + nparams = db then (* Current inductive, no params *)
          Some (TyCtr (qualid_of_ident oib.mind_typename, []))
        else (* [i + nparams - db]th parameter *)
          try Some (TyParam (List.nth param_names (i + nparams - db - 1)))
          with _ -> CErrors.user_err (str "nth failed: " ++ int (i + nparams - db - 1) ++ fnl ())
      end 
      else if isApp ty then begin
        let (ctr, tms) = decompose_app ty in 
        foldM (fun acc ty -> 
               aux i ty >>= fun ty' -> Some (ty' :: acc)
              ) (Some []) tms >>= fun tms' ->
        begin match aux i ctr with
        | Some (TyCtr (c, _)) -> Some (TyCtr (c, List.rev tms'))
(*        | Some (TyParam p) -> Some (TyCtr (p, tms')) *)
        | None -> CErrors.user_err (str "Aux failed?" ++ fnl ())
        | _ -> failwith "aux failed to return a TyCtr"
        end 
      end
      else if isInd ty then begin
        let ((mind,_),_) = destInd ty in
        Some (TyCtr (qualid_of_ident (Label.to_id (MutInd.label mind)), []))
      end
      else if isConst ty then begin
        let (c,_) = destConst ty in 
        (* TODO: Rethink this for constants? *)
        Some (TyCtr (qualid_of_ident (Label.to_id (Constant.label c)), []))
      end
      else CErrors.user_err (str "Case Not Handled" ++ fnl())

    in sequenceM (fun x -> x) (List.mapi aux (List.map (Vars.lift (-1)) pat_types)) >>= fun types ->
       Some (ctr_id, arrowify result_ty types)
  in

  let cns = List.map qualid_of_ident (Array.to_list oib.mind_consnames) in
  let lc  = Array.to_list oib.mind_nf_lc in
  sequenceM parse_constructor (List.combine cns lc)

(* Convert mutual_inductive_body to this representation, if possible *)
let dt_rep_from_mib mib = 
  if Array.length mib.mind_packets > 1 then begin
    CErrors.user_err (str "Mutual inductive types not supported yet." ++ fnl())
  end else 
    let oib = mib.mind_packets.(0) in
    let ty_ctr = oib.mind_typename in 
    parse_type_params oib.mind_arity_ctxt >>= fun ty_params ->
    let result_ctr = TyCtr (qualid_of_ident ty_ctr, List.map (fun x -> TyParam x) ty_params) in
    parse_constructors mib.mind_nparams ty_params result_ctr oib >>= fun ctr_reps ->
    Some (qualid_of_ident ty_ctr, ty_params, ctr_reps)

let qualid_to_mib r =
  let env = Global.env () in
  
  let glob_ref = Nametab.global r in
  let (mind,_) = Globnames.destIndRef glob_ref in
  let mib = Environ.lookup_mind mind env in

  mib

    
let coerce_reference_to_dt_rep c = 
  let r = match c with
    | { CAst.v = CRef (r,_) } -> r
    | _ -> failwith "Not a reference"
  in

  let mib = qualid_to_mib r in
  
  dt_rep_from_mib mib

(* Dependent derivations - lots of code reuse *)

(* Input : arity_ctxt [Name, Body (option) {expected None}, Type] 
   In reverse order.
   ASSUME: all type parameters are first

   Output: all type parameters (named arguments of type : Type)
           in correct order *)
let dep_parse_type_params arity_ctxt =
  let param_names =
    foldM (fun acc decl -> 
           match Rel.Declaration.get_name decl with
           | Name id -> 
              (* Actual parameters are named of type Type with some universe *)
              if is_Type (Rel.Declaration.get_type decl) then Some (id :: acc) else Some acc
           | _ -> (* Ignore *) Some acc
          ) (Some []) arity_ctxt in
  param_names

let rec dep_arrowify terminal names types = 
  match names, types with
  | [], [] -> terminal
  | (Name x)::ns , t::ts -> DProd ((x,t), dep_arrowify terminal ns ts)
  | Anonymous::ns, t::ts -> DArrow (t, dep_arrowify terminal ns ts)
  | _, _ -> failwith "Invalid argument to dep_arrowify"

(* parse a type into a dep_type option 
   i : index of product (for DeBruijn)
   nparams : number of <Type> parameters in the beginning
   arg_names : argument names (type parameters, pattern specific variables 
 *)
let parse_dependent_type i nparams ty oib arg_names = 
  let rec aux i ty =
    let env = Global.env () in
    let sigma = Evd.from_env env in
    msg_debug (str "Calling aux with: " ++ int i ++ str " "
               ++ Printer.pr_constr_env env sigma ty ++ fnl()); 
    if isRel ty then begin 
  (*        msgerr (int (i + nparams) ++ str " Rel " ++ int (destRel ty) ++ fnl ()); *)
      let db = destRel ty in
      if i + nparams = db then (* Current inductive, no params *)
        Some (DTyCtr (qualid_of_ident oib.mind_typename, []))
      else begin (* [i + nparams - db]th parameter *) 
        msg_debug (str (Printf.sprintf "Non-self-rel: %s" (dep_type_to_string (List.nth arg_names (i + nparams - db - 1)))) ++ fnl ());
        try Some (List.nth arg_names (i + nparams - db - 1))
        with _ -> CErrors.user_err (str "nth failed: " ++ int i ++ str " " ++ int nparams ++ str " " ++ int db ++ str " " ++ int (i + nparams - db - 1) ++ fnl ())
        end
    end 
    else if isApp ty then begin
      let (ctr, tms) = decompose_app ty in 
      foldM (fun acc ty -> 
             aux i ty >>= fun ty' -> Some (ty' :: acc)
            ) (Some []) tms >>= fun tms' ->
      match aux i ctr with
      | Some (DTyCtr (c, _)) -> Some (DTyCtr (c, List.rev tms'))
      | Some (DCtr (c, _)) -> Some (DCtr (c, List.rev tms'))
      | Some (DTyVar x) -> 
         let xs = var_to_string x in 
         if xs = "Coq.Init.Logic.not" || xs = "not" then 
           match tms' with 
           | [c] -> Some (DNot c)
           | _   -> failwith "Not a valid negation"
         else Some (DApp (DTyVar x, List.rev tms'))
      | Some wat -> CErrors.user_err (str ("WAT: " ^ dep_type_to_string wat) ++ fnl ())
      | None -> CErrors.user_err (str "Aux failed?" ++ fnl ())
    end
    else if isInd ty then begin
      let ((mind,_),_) = destInd ty in
      msg_debug (str (Printf.sprintf "LOOK HERE: %s - %s - %s" (MutInd.to_string mind) (Label.to_string (MutInd.label mind)) 
                                                            (Id.to_string (Label.to_id (MutInd.label mind)))) ++ fnl ());
      Some (DTyCtr (qualid_of_ident (Label.to_id (MutInd.label mind)), []))
    end
    else if isConstruct ty then begin
      let (((mind, midx), idx),_) = destConstruct ty in                               

      (* Lookup the inductive *)
      let env = Global.env () in
      let mib = Environ.lookup_mind mind env in

(*      let (mp, _dn, _) = MutInd.repr3 mind in *)

      (* HACKY: figure out better way to qualify constructors *)
      let names = Str.split (Str.regexp "[.]") (MutInd.to_string mind) in
      let prefix = List.rev (List.tl (List.rev names)) in
      let qual = String.concat "." prefix in
      msg_debug (str (Printf.sprintf "CONSTR: %s %s" qual (DirPath.to_string (Lib.cwd ()))) ++ fnl ());

      (* Constructor name *)
      let cname = Id.to_string (mib.mind_packets.(midx).mind_consnames.(idx - 1)) in
      let cid = qualid_of_string (if (qual = "") || (qual = DirPath.to_string (Lib.cwd ()))
                             then cname else qual ^ "." ^ cname) in
      Some (DCtr (cid, []))
    end
    else if isProd ty then begin
      let (n, t1, t2) = destProd ty in
      (* Are the 'i's correct? *)
      aux i t1 >>= fun t1' -> 
      aux i t2 >>= fun t2' ->
      Some (DProd ((id_of_name n, t1'), t2'))
    end
    (* Rel, App, Ind, Construct, Prod *)
    else if isConst ty then begin 
      let (x,_) = destConst ty in 
      Some (DTyVar (Label.to_id (Constant.label x)))
    end
    else (
      let env = Global.env() in
      let sigma = Evd.from_env env in
      CErrors.user_err (str "Dep Case Not Handled: " ++ Printer.pr_constr_env env sigma ty ++ fnl())
    ) in
  aux i ty

let dep_parse_type nparams param_names arity_ctxt oib =
  let len = List.length arity_ctxt in
  (* Only type parameters can be used - no dependencies on the types *)
  let arg_names = List.map (fun x -> DTyParam x) param_names in
  foldM (fun acc (i, decl) -> 
           let n = Rel.Declaration.get_name decl in
           let t = Rel.Declaration.get_type decl in
           let env = Global.env () in
           let sigma = Evd.from_env env in
           debug_constr env sigma t;
           match n with
           | Name id -> (* Check if it is a parameter to add its type / name *)
              if is_Type t then Some acc 
              else parse_dependent_type i nparams t oib arg_names >>= fun dt -> Some ((n,dt) :: acc)
           | _ ->  parse_dependent_type i nparams t oib arg_names >>= fun dt -> Some ((n,dt) :: acc)
        ) (Some []) (List.mapi (fun i x -> (len - nparams - i, x)) arity_ctxt) >>= fun nts ->
  let (names, types) = List.split nts in
  Some (dep_arrowify (DTyCtr (injectCtr "Prop", [])) names types)

(* Dependent version: 
   nparams is numver of Type parameters 
   param_names are type parameters (length = nparams)

   Returns list of constructor representations 
 *)
let dep_parse_constructors nparams param_names oib : dep_ctr list option =
  
  let parse_constructor branch : dep_ctr option =
    let (ctr_id, ty_ctr) = branch in

    let (_, ty) = Term.decompose_prod_n nparams ty_ctr in
    
    let (ctr_pats, result) = if isConst ty then ([],ty) else Term.decompose_prod ty in

    let pat_names, pat_types = List.split (List.rev ctr_pats) in

    let arg_names = 
      List.map (fun x -> DTyParam x) param_names @ 
      List.map (fun n -> match n with
                         | Name x -> DTyVar x 
                         | Anonymous -> DTyVar (make_up_name ()) (* Make up a name, but probably can't be used *)
               ) pat_names in 

(*     msgerr (str "Calculating result type" ++ fnl ()); *)
    parse_dependent_type (1 + (List.length ctr_pats)) nparams result oib arg_names >>= fun result_ty ->

(*     msgerr (str "Calculating types" ++ fnl ()); *)
    sequenceM (fun x -> x) (List.mapi (fun i ty -> parse_dependent_type i nparams ty oib arg_names) (List.map (Vars.lift (-1)) pat_types)) >>= fun types ->
    Some (ctr_id, dep_arrowify result_ty pat_names types)
  in

  let cns = List.map qualid_of_ident (Array.to_list oib.mind_consnames) in
  let lc = Array.to_list oib.mind_nf_lc in
  sequenceM parse_constructor (List.combine cns lc)

let dep_dt_from_mib mib = 
  if Array.length mib.mind_packets > 1 then begin
    CErrors.user_err (str "Mutual inductive types not supported yet." ++ fnl())
  end else 
    let oib = mib.mind_packets.(0) in
    let ty_ctr = oib.mind_typename in 
    dep_parse_type_params oib.mind_arity_ctxt >>= fun ty_params ->
    List.iter (fun tp -> msg_debug (str (ty_param_to_string tp) ++ fnl ())) ty_params;
    dep_parse_constructors (List.length ty_params) ty_params oib >>= fun ctr_reps ->
    dep_parse_type (List.length ty_params) ty_params oib.mind_arity_ctxt oib >>= fun result_ty -> 
    Some (qualid_of_ident ty_ctr, ty_params, ctr_reps, result_ty)

let coerce_reference_to_dep_dt c = 
  let r = match c with
    | { CAst.v = CRef (r,_) } -> r
    | _ -> failwith "Not a reference" in

  let env = Global.env () in
  
  let glob_ref = Nametab.global r in
  let (mind,_) = Globnames.destIndRef glob_ref in
  let mib = Environ.lookup_mind mind env in
  
  dep_dt_from_mib mib
                  
let gApp ?explicit:(expl=false) c cs =
  if expl then
    let f c = match c with
    | CRef (r,_) -> CAppExpl ((None, r, None), cs)
    | _ -> failwith "invalid argument to gApp"
    in CAst.map f c
  else mkAppC (c, cs)

let gProdWithArgs args f_body =
  let xvs = List.map (fun (CLocalAssum ([{CAst.v = n}], _, _)) ->
                      match n with
                      | Name x -> x
                      | _ -> make_up_name ()
                     ) args in
  let fun_body = f_body xvs in
  mkCProdN args fun_body

let gFunWithArgs args f_body =
  let xvs = List.map (fun (CLocalAssum ([{CAst.v = n}], _, _)) ->
                      match n with
                      | Name x -> x
                      | _ -> make_up_name ()
                     ) args in
  let fun_body = f_body xvs in
  mkCLambdaN args fun_body

let gFun xss (f_body : var list -> coq_expr) =
  match xss with
  | [] -> f_body []
  | _ ->
  let xvs = List.map (fun x -> fresh_name x) xss in
  (* TODO: optional argument types for xss *)
  let binder_list = List.map (fun x -> CLocalAssum ([CAst.make @@ Name x], Default Explicit, hole)) xvs in
  let fun_body = f_body xvs in
  mkCLambdaN binder_list fun_body 

let gFunTyped xts (f_body : var list -> coq_expr) =
  match xts with
  | [] -> f_body []
  | _ ->
  let xvs = List.map (fun (x,t) -> (fresh_name x,t)) xts in
  (* TODO: optional argument types for xss *)
  let binder_list = List.map (fun (x,t) -> CLocalAssum ([CAst.make @@ Name x], Default Explicit, t)) xvs in
  let fun_body = f_body (List.map fst xvs) in
  mkCLambdaN binder_list fun_body 

(* with Explicit/Implicit annotations *)  
let gRecFunInWithArgs ?assumType:(typ=hole) (fs : string) args (f_body : (var * var list) -> coq_expr) (let_body : var -> coq_expr) = 
  let fv  = fresh_name fs in
  let xvs = List.map (fun (CLocalAssum ([{CAst.v = n}], _, _)) ->
                      match n with
                      | Name x -> x
                      | _ -> make_up_name ()
                     ) args in
  let fix_body = f_body (fv, xvs) in
  CAst.make @@ CLetIn (CAst.make @@ Name fv,
    CAst.make @@ CFix(CAst.make fv,[(CAst.make fv, (None, CStructRec), args, typ, fix_body)]), None,
    let_body fv)
             
let gRecFunIn ?assumType:(typ = hole) (fs : string) (xss : string list) (f_body : (var * var list) -> coq_expr) (let_body : var -> coq_expr) =
  let xss' = List.map (fun s -> fresh_name s) xss in
  gRecFunInWithArgs ~assumType:typ fs (List.map (fun x -> gArg ~assumName:(gVar x) ()) xss') f_body let_body 

let gLetIn (x : string) (e : coq_expr) (body : var -> coq_expr) = 
  let fx = fresh_name x in
  CAst.make @@ CLetIn (CAst.make @@ Name fx, e, None, body fx)


let gLetTupleIn (x : var) (xs : var list) (body : coq_expr) =
  CAst.make @@ CLetTuple (List.map (fun x -> CAst.make @@ Names.Name x) xs, (None, None), gVar x, body)
  
let gMatch discr ?catchAll:(body=None) (branches : (constructor * string list * (var list -> coq_expr)) list) : coq_expr =
  CAst.make @@ CCases (RegularStyle,
          None (* return *), 
          [(discr, None, None)], (* single discriminee, no as/in *)
          (List.map (fun (c, cs, bf) -> 
                      let cvs : Id.t list = List.map fresh_name cs in
                      CAst.make ([[CAst.make @@ CPatCstr (c,
                                      None,
                                      List.map (fun s -> CAst.make @@ CPatAtom (Some (qualid_of_ident s))) cvs (* Constructor applied to patterns *)
                                    )
                           ]],
                       bf cvs)
                   ) branches) @ match body with
                                 | None -> []
                                 | Some c' -> [CAst.make ([[CAst.make @@ CPatAtom None]], c')])

let gMatchReturn (discr : coq_expr)
      ?catchAll:(body=None)
      (as_id : string)
      (ret : var -> coq_expr)
      (branches : (constructor * string list * (var list -> coq_expr)) list) : coq_expr =
  let as_id' = fresh_name as_id in
  CAst.make @@ CCases (RegularStyle,
          Some (ret as_id'), (* return *)
          [(discr, Some (CAst.make (Name as_id')), None)], (* single discriminee, no in *)
          (List.map (fun (c, cs, bf) -> 
                      let cvs : Id.t list = List.map fresh_name cs in
                       CAst.make ([[CAst.make @@ CPatCstr (c,
                                      None,
                                      List.map (fun s -> CAst.make @@ CPatAtom (Some (qualid_of_ident s))) cvs (* Constructor applied to patterns *)
                                  )]],
                                  bf cvs)
                   ) branches) @ (match body with
                                  | None -> []
                                  | Some c' -> [CAst.make ([([CAst.make @@ CPatAtom None])], c')])
         )


let gRecord names_and_bodies =
  CAst.make @@ CRecord (List.map (fun (n,b) -> (qualid_of_ident @@ Id.of_string n, b)) names_and_bodies)

let gAnnot (p : coq_expr) (tau : coq_expr) =
  CAst.make @@ CCast (p, Misctypes.CastConv tau)

(* Convert types back into coq *)
let gType ty_params dep_type = 
  let rec aux dt : coq_expr = 
    match dt with
    | DArrow (dt1, dt2) -> let t1 = aux dt1 in
                           let t2 = aux dt2 in 
                           gFunWithArgs [gArg ~assumType:t1 ()] (fun _ -> t2)
    | DProd ((x,dt1), dt2) -> let t1 = aux dt1 in
                              let t2 = aux dt2 in 
                              gProdWithArgs [gArg ~assumName:(gVar x) ~assumType:t1 ()] (fun _ -> t2)
    | DTyParam tp -> gTyParam tp
    | DTyCtr (c,dts) -> gApp (gTyCtr c) (List.map aux dts)
    | DTyVar x -> gVar x 
    | DApp (c, dts) -> gApp (aux c) (List.map aux dts) in
  aux dep_type
(*    
  match ty_params with 
  | [] -> aux dep_type 
  | _  -> gProdWithArgs (List.map (fun x -> gArg ~assumName:(gTyParam x) ()) ty_params)
                        (fun _ -> aux dep_type)
 *)

(* Lookup the type of an identifier *)
let get_type (id : Id.t) = 
  msg_debug (str ("Trying to global:" ^ Id.to_string id) ++ fnl ());
  let glob_ref = Nametab.global (qualid_of_ident id) in
  match glob_ref with 
  | VarRef _ -> msg_debug  (str "Var" ++ fnl ())
  | ConstRef _ -> msg_debug (str "Constant" ++ fnl ())
  | IndRef _ -> msg_debug (str "Inductive" ++ fnl ())
  | ConstructRef _ -> msg_debug (str "Constructor" ++ fnl ())

let is_inductive c = 
  let glob_ref = Nametab.global c in
  match glob_ref with
  | IndRef _ -> true
  | _        -> false

let is_inductive_dt dt = 
  match dt with
  | DTyCtr (c, dts) -> is_inductive c
  | _ -> false

(* Specialized match *)
type matcher_pat = 
  | MatchCtr of constructor * matcher_pat list
  | MatchU of var

let rec matcher_pat_to_string = function
  | MatchU u -> var_to_string u
  | MatchCtr (c, ms) -> constructor_to_string c ^ " " ^ str_lst_to_string " " (List.map matcher_pat_to_string ms)

let construct_match c ?catch_all:(mdef=None) alts = 
  let rec aux = function 
    | MatchU u' -> begin 
        CAst.make @@ CPatAtom (Some (qualid_of_ident u'))
      end
    | MatchCtr (c, ms) -> begin
       if is_inductive c then CAst.make @@ CPatAtom None
       else CAst.make @@ CPatCstr (c,
                   Some (List.map (fun m -> aux m) ms),
                   []) 
                        end 
  in CAst.make @@ CCases (RegularStyle,
             None (* return *), 
              [ (c, None, None)], (* single discriminee, no as/in *)
              List.map (fun (m, body) -> CAst.make @@ ([[aux m]], body)) alts
              @ (match mdef with 
                 | Some body -> [(CAst.make @@ ([[CAst.make @@ CPatAtom None]], body))]
                 | _ -> []
                )
            )

let construct_match_with_return c ?catch_all:(mdef=None) (as_id : string) (ret : var -> coq_expr) (alts : (matcher_pat * coq_expr) list) =
  let as_id' = fresh_name as_id in
  let rec aux = function
    | MatchU u' -> begin
        CAst.make @@ CPatAtom (Some (qualid_of_ident u'))
      end
    | MatchCtr (c, ms) -> begin
       if is_inductive c then begin 
         CAst.make @@ CPatAtom None
       end
       else begin 
         CAst.make @@ CPatCstr (c,
                   Some (List.map (fun m -> aux m) ms),
                   []) 
         end
       end in
  let main_opts = 
        List.map (fun (m, body) -> CAst.make @@ ([[aux m]], body)) alts in
  let default =
    match mdef with 
    | Some body -> [CAst.make ([[CAst.make @@ CPatAtom None]], body)]
    | _ -> [] in
  CAst.make @@ CCases (RegularStyle,
             Some (ret as_id') (* return *), 
             [ (c, Some (CAst.make @@ Name as_id'), None)], (* single discriminee, no as/in *)
             main_opts @ default
         )

(* Generic List Manipulations *)
let list_nil = gInject "Coq.Lists.List.nil"
let lst_append c1 c2 = gApp (gInject "Coq.Lists.List.app") [c1; c2]
let rec lst_appends = function
  | [] -> list_nil
  | c::cs -> lst_append c (lst_appends cs)
let gCons x xs = gApp (gInject "Coq.Lists.List.cons") [x; xs]                        
let rec gList = function 
  | [] -> gInject "Coq.Lists.List.nil"
  | x::xs -> gCons x (gList xs)

(* Generic String Manipulations *)
let string_scope ast = CAst.make @@ CDelimiters ("string", ast)
let gStr s = string_scope (CAst.make @@ CPrim (String s))
let emptyString = gInject "Coq.Strings.String.EmptyString"
let str_append c1 c2 = gApp (gInject "Coq.Strings.String.append") [c1; c2]
let rec str_appends cs = 
  match cs with 
  | []  -> emptyString
  | [c] -> c
  | c1::cs' -> str_append c1 (str_appends cs')
let smart_paren c = gApp (gInject "QuickChick.Show.smart_paren") [c]

(* Pair *)
let gPair (c1, c2) = gApp (gInject "Coq.Init.Datatypes.pair") [c1;c2]
let gProd (c1, c2) = gApp (gInject "Coq.Init.Datatypes.prod") [c1;c2]

let listToPairAux (f : ('a *'b) -> 'a) (l : 'b list) : 'a =
  match l with
  | [] -> qcfail "listToPair called with empty list"
  | c :: cs' ->
     let rec go (l : 'a list) (acc : 'a) : 'a =
       match l with
       | [] -> acc
       | x :: xs -> go xs (f (acc, x))
     in go cs' c
(*      
let gTupleAux f cs =
  match cs with
  | []  -> qcfail "gTuple called with empty list" (* Should this be unit? *)
  | c :: cs' ->
     let rec go l acc =
       match l with
       | [] -> acc
       | x :: xs -> go xs (f (acc, x))
     in go cs' cx
 *)
let gTuple = listToPairAux gPair
let gTupleType = listToPairAux gProd
let dtTupleType =
  listToPairAux (fun (acc,x) -> DTyCtr (injectCtr "Coq.Init.Datatypes.prod", [acc;x]))
                                                      
(*
                        match dts with
  | [] -> qcfail "dtTuple called with empty list"
  | dt :: dts' ->
     let rec go l acc =
       match l with
       | [] -> acc
       | x :: xs -> go xs (DTyCtr (injectCtr "Coq.Init.Datatypes.Prod", [acc; x]))
     in go dts' dt
 *)

(* Int *)

let mkNumeral n =
  if n >= 0 then Numeral (string_of_int n, true)
  else Numeral (string_of_int (-n), false)

let nat_scope ast = CAst.make @@ CDelimiters ("nat", ast)
let gInt n = nat_scope (CAst.make @@ CPrim (mkNumeral n))
let gSucc x = gApp (gInject "Coq.Init.Datatypes.S") [x]
let rec maximum = function
  | [] -> failwith "maximum called with empty list"
  | [c] -> c
  | (c::cs) -> gApp (gInject "Coq.Init.Peano.max") [c; maximum cs]

let gle x y = gApp (gInject "mathcomp.ssreflect.ssrnat.leq") [x; y]
let glt x y = gle (gApp (gInject "Coq.Init.Datatypes.S") [x]) y


let gEq x y = gApp (gInject "Coq.Init.Logic.eq") [x; y]
            
(* option type in Coq *)
let gNone typ = gApp ~explicit:true (gInject "Coq.Init.Datatypes.None") [typ]
let gSome typ c = gApp ~explicit:true (gInject "Coq.Init.Datatypes.Some") [typ; c]
              
let gOption c = gApp (gInject "Coq.Init.Datatypes.option") [c]

(* Boolean *)

let g_true  = gInject "Coq.Init.Datatypes.true"
let g_false = gInject "Coq.Init.Datatypes.false"

let gNot c = gApp (gInject "Coq.Init.Datatypes.negb") [c]
let gBool  = gInject "Coq.Init.Datatypes.bool"           

let decToBool c = 
  gMatch c [ (injectCtr "Coq.Init.Specif.left" , ["eq" ], fun _ -> g_true )
           ; (injectCtr "Coq.Init.Specif.right", ["neq"], fun _ -> g_false)
    ]

(* Unit *)
let gUnit = gInject "Coq.Init.Datatypes.unit"
let gTT   = gInject "Coq.Init.Datatypes.tt"

(* Recursion combinators / fold *)
(* fold_ty : ( a -> coq_type -> a ) -> ( ty_ctr * coq_type list -> a ) -> ( ty_param -> a ) -> coq_type -> a *)
let rec fold_ty arrow_f ty_ctr_f ty_param_f ty = 
  match ty with
  | Arrow (ty1, ty2) -> 
     let acc = fold_ty arrow_f ty_ctr_f ty_param_f ty2 in 
     arrow_f acc ty1 
  | TyCtr (ctr, tys) -> ty_ctr_f (ctr, tys)
  | TyParam tp -> ty_param_f tp

let fold_ty' arrow_f base ty = 
  fold_ty arrow_f (fun _ -> base) (fun _ -> base) ty

let rec dep_fold_ty arrow_f prod_f ty_ctr_f ctr_f ty_param_f var_f ty = 
  match ty with
  | DArrow (ty1, ty2) -> 
     let acc = dep_fold_ty arrow_f prod_f ty_ctr_f ctr_f ty_param_f var_f ty2 in
     arrow_f acc ty1 
  | DProd ((x,ty1), ty2) -> 
     let acc = dep_fold_ty arrow_f prod_f ty_ctr_f ctr_f ty_param_f var_f ty2 in
     prod_f acc x ty1 
  | DTyCtr (ctr, tys) -> ty_ctr_f (ctr, tys)
  | DCtr (ctr, tys) -> ctr_f (ctr, tys)
  | DTyParam tp -> ty_param_f tp
  | DTyVar tp -> var_f tp

(* Generate Type Names *)
let generate_names_from_type base_name ty =
  List.rev (snd (fold_ty' (fun (i, names) _ -> (i+1, (Printf.sprintf "%s%d" base_name i) :: names)) (0, []) ty))

(* a := var list -> var -> a *)
let fold_ty_vars (f : var list -> var -> coq_type -> 'a) (mappend : 'a -> 'a -> 'a) (base : 'a) ty : var list -> 'a =
  fun allVars -> fold_ty' (fun acc ty -> fun (v::vs) -> mappend (f allVars v ty) (acc vs)) (fun _ -> base) ty allVars

(* Declarations *)
(* LEO : There used to be defineConstant stuff here. WHY? *)
(*
let defineTypedConstant s c typ =
  let id = fresh_name s in
  (* TODO: DoDischarge or NoDischarge? *)
   let v = Constrintern.interp_constr (Global.env())
      (Evd.from_env (Global.env())) e in
  (* Borrowed from CIW tutorial *)
 *)
                          
(* Declare an instance *)
let create_names_for_anon a =
  match a with 
  | CLocalAssum ([{CAst.v = n; loc}], x, y) ->
     begin match n with
           | Name x -> (x, a)
           | Anonymous -> let n = make_up_name () in
                          (n, CLocalAssum ([CAst.make ?loc:loc @@ Names.Name n], x, y))
     end
  | _ -> failwith "Non RawAssum in create_names"
    
let declare_class_instance ?(global=true) ?(priority=42) instance_arguments instance_name instance_type instance_record =
  msg_debug (str "Declaring class instance..." ++ fnl ());
  msg_debug (str (Printf.sprintf "Total arguments: %d" (List.length instance_arguments)) ++ fnl ());
  let (vars,iargs) = List.split (List.map create_names_for_anon instance_arguments) in
  let instance_type_vars = instance_type vars in
  msg_debug (str "Calculated instance_type_vars" ++ fnl ());
  let instance_record_vars = instance_record vars in
  msg_debug (str "Calculated instance_record_vars" ++ fnl ());
  let cid = Classes.new_instance ~global:global false
              ~program_mode:false (* TODO: true or false? *)
                               iargs
                       ((CAst.make @@ Name (Id.of_string instance_name), None)
                       , Decl_kinds.Explicit, instance_type_vars)
                       (Some (true, instance_record_vars)) (* TODO: true or false? *)
                       { hint_priority = Some priority; hint_pattern = None }
  in
  msg_debug (str (Id.to_string cid) ++ fnl ())

(* List Utils. Probably should move to a util file instead *)
let list_last l = List.nth l (List.length l - 1)
let list_init l = List.rev (List.tl (List.rev l))
let list_drop_every n l =
  let rec aux i = function
    | [] -> []
    | x::xs -> if i == n then aux 1 xs else x::aux (i+1) xs
  in aux 1 l

let rec take_last l acc =
  match l with
  | [x] -> (List.rev acc, x)
  | x :: l' -> take_last l' (x :: acc)

let rec list_insert_nth x l n = 
  match n, l with 
  | 0, _  
  | _, [] -> x :: l
  | _, h::t -> h :: list_insert_nth x t (n-1)
  

(* Leo: Where should these util functions live? *)
let sameTypeCtr c_ctr = function
  | TyCtr (ty_ctr', _) -> c_ctr = ty_ctr'
  | _ -> false

let isBaseBranch ty_ctr ty =
  fold_ty' (fun b ty' -> b && not (sameTypeCtr ty_ctr ty')) true ty
