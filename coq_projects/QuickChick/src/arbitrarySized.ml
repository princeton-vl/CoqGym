open Pp
open Util
open GenericLib
open GenLib
open Error
   
(* Derivation of ArbitrarySized. Contains mostly code from derive.ml *)

let rec replace v x = function
  | [] -> []
  | y::ys -> if y = v then x::ys else y::(replace v x ys)

let arbitrarySized_body (ty_ctr : ty_ctr) (ctrs : ctr_rep list) iargs = 
  
  let isCurrentTyCtr = function
    | TyCtr (ty_ctr', _) -> ty_ctr = ty_ctr'
    | _ -> false in
  let isBaseBranch ty = fold_ty' (fun b ty' -> b && not (isCurrentTyCtr ty')) true ty in

  let tyParams = List.map gVar (list_drop_every 2 iargs) in

  (* Need reverse fold for this *)
  let create_for_branch tyParams rec_name size (ctr, ty) =
    let rec aux i acc ty : coq_expr =
      match ty with
      | Arrow (ty1, ty2) ->
         bindGen (if isCurrentTyCtr ty1 then
                     gApp (gVar rec_name) [gVar size]
                  else gInject "arbitrary")
           (Printf.sprintf "p%d" i)
           (fun pi -> aux (i+1) ((gVar pi) :: acc) ty2)
      | _ -> returnGen (gApp ~explicit:true (gCtr ctr) (tyParams @ List.rev acc))
    in aux 0 [] ty in
  
  let bases = List.filter (fun (_, ty) -> isBaseBranch ty) ctrs in

  gRecFunInWithArgs
    "arb_aux" [gArg ~assumName:(gInject "size") ()]
    (fun (aux_arb, [size]) ->
      gMatch (gVar size)
        [(injectCtr "O", [],
          fun _ -> oneof (List.map (create_for_branch tyParams aux_arb size) bases))
        ;(injectCtr "S", ["size'"],
          fun [size'] -> frequency (List.map (fun (ctr,ty') ->
                                        (Weightmap.lookup_weight ctr size',
                                         create_for_branch tyParams aux_arb size' (ctr,ty'))) ctrs))
    ])
    (fun x -> gVar x)
  
let arbitrarySized_decl ty_ctr ctrs iargs =

  let arb_body = arbitrarySized_body ty_ctr ctrs iargs in
  let arbitrary_decl = gFun ["s"] (fun [s] -> gApp arb_body [gVar s]) in

  gRecord [("arbitrarySized", arbitrary_decl)]


(** Shrinking Derivation *)
let shrink_decl ty_ctr ctrs iargs =

  let isCurrentTyCtr = function
    | TyCtr (ty_ctr', _) -> ty_ctr = ty_ctr'
    | _ -> false in

  let tyParams = List.map gVar (list_drop_every 2 iargs) in

  let shrink_fun = 
    let shrink_body x =
      let create_branch aux_shrink (ctr, ty) =
        (ctr, generate_names_from_type "p" ty,
         fold_ty_vars (fun allParams v ty' ->
             let liftNth = gFun ["shrunk"]
                 (fun [shrunk] -> gApp ~explicit:true (gCtr ctr)
                     (tyParams @ (replace (gVar v) (gVar shrunk) (List.map gVar allParams)))) in
             lst_appends (if isCurrentTyCtr ty' then
                            [ gList [gVar v] ; gApp (gInject "List.map") [liftNth; gApp (gVar aux_shrink) [gVar v]]]
                          else
                            [ gApp (gInject "List.map") [liftNth; gApp (gInject "shrink") [gVar v]]]))
           lst_append list_nil ty) in

      let aux_shrink_body rec_fun x' = gMatch (gVar x') (List.map (create_branch rec_fun) ctrs) in

      gRecFunIn "aux_shrink" ["x'"]
        (fun (aux_shrink, [x']) -> aux_shrink_body aux_shrink x')
        (fun aux_shrink -> gApp (gVar aux_shrink) [gVar x])
    in
    (* Create the function body by recursing on the structure of x *)
    gFun ["x"] (fun [x] -> shrink_body x)
  in
  debug_coq_expr shrink_fun;
  gRecord [("shrink", shrink_fun)]

let show_decl ty_ctr ctrs iargs =
  msg_debug (str "Deriving Show Information:" ++ fnl ());
  msg_debug (str ("Type constructor is: " ^ ty_ctr_to_string ty_ctr) ++ fnl ());
  msg_debug (str (str_lst_to_string "\n" (List.map ctr_rep_to_string ctrs)) ++ fnl());

  let isCurrentTyCtr = function
    | TyCtr (ty_ctr', _) -> ty_ctr = ty_ctr'
    | _ -> false in

  (* Create the function body by recursing on the structure of x *)
  let show_body x =
    
    let branch aux (ctr,ty) =
      
      (ctr, generate_names_from_type "p" ty,
       fun vs -> match vs with 
                 | [] -> gStr (constructor_to_string ctr) 
                 |_ -> str_append (gStr (constructor_to_string ctr ^ " "))
                                  (fold_ty_vars (fun _ v ty' -> smart_paren (gApp (if isCurrentTyCtr ty' then gVar aux else gInject "show") [gVar v]))
                                                (fun s1 s2 -> if s2 = emptyString then s1 else str_appends [s1; gStr " "; s2]) emptyString ty vs))
    in
    
    gRecFunIn "aux" ["x'"]
              (fun (aux, [x']) -> gMatch (gVar x') (List.map (branch aux) ctrs))
              (fun aux -> gApp (gVar aux) [gVar x])
  in
  
  let show_fun = gFun ["x"] (fun [x] -> show_body x) in
  gRecord [("show", show_fun)]
          
