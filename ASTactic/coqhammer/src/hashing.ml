open Coqterms
open Hhlib
open Coq_transl_opts

type namesubst = (string * string) list

(***************************************************************************************)
(* Coqterm hashing *)

let var i =
  "v_CANONICAL_" ^ (string_of_int i)

(* creates a list of m canonical vars starting at n *)
let vars n m =
  List.map var (range n (n+m))

(* substitutes all occ. of the name oldn with the name newn in term t *)
let sub newn oldn t = substvar oldn (Var(newn)) t

let subs pairs t = dsubst (List.map (fun (newn,oldn) -> (oldn, lazy (Var(newn)))) pairs) t

(* canonical representation using variable renaming starting at n
   along with variable substitutions *)
let rec can_aux n t =
  let f = can_aux n in
    match t with
    | Var x                 -> Var x
    | Const x               -> Const x
    | App(t1,t2)            -> App (f t1, f t2)
    | Lam(x,t1,t2)          -> let v = var n in Lam(v, f t1, can_aux (n+1) (sub v x t2))
    | Case(indt,t1,t2,m,cs) -> Case(indt, f t1, f t2, m, List.map (fun (p,u) -> (p, f u)) cs)
    | Cast(t1,t2)           -> Cast(f t1, f t2)
    | Fix(t,i,xs,ts1,ts2)   -> let m = List.length xs in
                               let newvars = vars n m in
                               let newbodies = List.map (fun b -> can_aux (n+m) (subs (zip (vars n m) xs) b)) ts2
                               in Fix(t, i, newvars, List.map f ts1, newbodies)
    | Let(t1,(x,t2,t3))     -> let v = var n in Let(f t1, (v,f t2, can_aux (n+1) (sub v x t2)))
    | Prod(x,t1,t2)         -> let v = var n in Prod(v, f t1, can_aux (n+1) (sub v x t2))
    | IndType(indt,xs,n)    -> IndType(indt,xs,n)
    | SortProp              -> SortProp
    | SortSet               -> SortSet
    | SortType              -> SortType
    | Quant(q,(x,t1,t2))    -> let v = var n in Quant(q,(v,f t1,can_aux (n+1) (sub v x t2)))
    | Equal(t1,t2)          -> Equal(f t1,f t2)

let canonical ctx tm =
  let rec can_ctx_aux acc subacc n ctx tm =
    match ctx with
    | []            -> (acc, can_aux n tm, subacc)
    | (x,tp) :: rest ->
       can_ctx_aux ((var n, tp) :: acc) ((var n, x) :: subacc) (n+1)
         (List.map (fun (y, t1) -> (y, sub (var n) x t1)) rest) (sub (var n) x tm)
  in can_ctx_aux [] [] 0 (List.rev ctx) tm

type 'a lift_fun = (coqterm -> coqterm) -> 'a -> 'a
type 'a coqterms_hash = (coqcontext * coqterm, 'a) Hashtbl.t * 'a lift_fun

let create lift = (Hashtbl.create 128, lift)

let clear tbl = Hashtbl.clear (fst tbl)

let find_or_insert tbl ctx tm mk =
  debug 4 (fun () -> print_header "find_or_insert" tm ctx);
  let (tbl, lift) = tbl in
  let ctx' = vars_to_ctx (get_fvars ctx tm) in
  let (cctx,ctm,sigma) = canonical ctx' tm in
  debug 4 begin fun () ->
    print_header "canonical (result)" ctm cctx;
    print_list (fun (x,y) -> print_string ("(" ^ x ^ "," ^ y ^ ")")) sigma
  end;
  let revsigma = List.map (fun (x,y) -> (y,x)) sigma in
  try
    lift (subs revsigma) (Hashtbl.find tbl (cctx,ctm))
  with _ ->
    let x = mk cctx ctm in
    Hashtbl.add tbl (cctx,ctm) x;
    lift (subs revsigma) x
