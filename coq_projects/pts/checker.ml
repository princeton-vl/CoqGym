(*+all+*)
open Genlex;;   
open Kernel;;

type expr=
    SRT of gen_sort
  | REF of string
  | ABS of string * expr * expr
  | APP of expr * expr
  | PROD of string * expr * expr
;;


let rec nat_of_int = function
  0 -> O
| k -> S (nat_of_int (k-1))
;;

let rec int_of_nat = function
  O -> 0
| S k -> succ (int_of_nat k)
;;

let rec nat_item l n =
  match (l,n) with
    ([], _) -> None
  | ((x::_), O) -> Some x
  | ((_::l), (S k)) -> nat_item l k
;;

let nat_index ctx x =
  let rec nat_index_rec n = function
    [] -> None
  | y::l -> if x=y then Some n
                   else nat_index_rec (S n) l
  in nat_index_rec O ctx
;;

(*> conversions term <=> expr *)
let var_of_ref n = "x"^(string_of_int n);;         

let first_fv = ref 0;;

let rec find_free_var ctx =
  let v=var_of_ref !first_fv in
    if (List.mem v ctx) then (incr first_fv; find_free_var ctx) else v
;;

let rec var_indep x = function
   SRT _ -> true
 | REF y -> x<>y
 | ABS (y,tt,t) -> (var_indep x tt) & (x=y or (var_indep x t))
 | APP (u,v) -> (var_indep x u) & (var_indep x v)
 | PROD (y,tt,u) -> (var_indep x tt) & (x=y or (var_indep x u))
;;

let rec term_of_expr ctx=function
    SRT gs ->
      (match sort_of_gen gs with
        (Some s) -> Srt s
      | None -> failwith "sorte incorrecte")
  | REF x -> (match (nat_index ctx x) with
                Some n -> Ref n
              | None -> failwith ("identificateur "^x^" inconnu"))
  | ABS (x,tt,t) -> Abs (term_of_expr ctx tt, term_of_expr (x::ctx) t)
  | APP (u,v) -> App (term_of_expr ctx u, term_of_expr ctx v)
  | PROD (x,tt,u) -> Prod (term_of_expr ctx tt, term_of_expr (x::ctx) u)
;;

let expr_of_term ctx t = 
 let rec exp_of_trm ctx = function
    Srt s -> SRT (gen_of_sort s)
  | Ref n -> (match nat_item ctx n with
                Some x -> REF x
              | None -> assert false)
  | Abs (tt,t)-> let v = find_free_var ctx in
                 ABS (v, exp_of_trm ctx tt, exp_of_trm (v::ctx) t)
  | App (u,v)-> APP (exp_of_trm ctx u, exp_of_trm ctx v)
  | Prod (tt,u)-> let v = find_free_var ctx in
                 PROD (v, exp_of_trm ctx tt, exp_of_trm (v::ctx) u) in
 let _ = first_fv:=0 in
 exp_of_trm ctx t
;;


(*> affichage *)

let string_of_sort = function
  Gprop      -> "Prop"
| Gset       -> "Set"
| Gtype n    -> "Type(" ^ (string_of_int (int_of_nat n)) ^ ")"
| Gtypeset n -> "Typeset(" ^ (string_of_int (int_of_nat n)) ^ ")"
;;

let rec string_of_expr = function
    SRT s -> string_of_sort s
  | REF x -> x
  | ABS (x,tt,t) -> "["^x^":"^(string_of_expr tt)^"]"^(string_of_expr t)
  | APP (u,v) -> "("^(string_of_app u)^" "^(string_of_expr v)^")"
  | PROD (x,tt,u) -> if var_indep x u
                     then (string_of_arrow tt)^"->"^(string_of_expr u)
                     else "("^x^":"^(string_of_expr tt)^")"^(string_of_expr u)

and string_of_app = function
    APP (u,v) -> (string_of_app u)^" "^(string_of_expr v)
  | t -> string_of_expr t

and string_of_arrow = function
    ABS (x0,x1,x2) -> "("^(string_of_expr (ABS (x0,x1,x2)))^")"
  | PROD (x0,x1,x2) -> "("^(string_of_expr (PROD (x0,x1,x2)))^")"
  | t -> string_of_expr t
;;

let print_sort s = print_string (string_of_sort (gen_of_sort s));;
let print_term ctx t=print_string (string_of_expr (expr_of_term ctx t));;


(*> messages d'erreur *)

let rec print_type_err ctx = function
    Under (e,err) ->
      let x = find_free_var ctx in
      print_string x;
      print_string " : ";
      print_term ctx e;
      print_newline();
      print_type_err (x::ctx) err
  | Expected_type(m,at,et) ->
      print_string "le terme ";
      print_term ctx m;
      print_string " : ";
      print_term ctx at;
      print_string " n'a pas le type ";
      print_term ctx et;
      print_endline "."
  | Topsort s ->
      print_sort s;
      print_endline " est une sorte non typable."
  | Db_error n ->
      print_string "variable de de Bruijn #";
      print_int (int_of_nat n);
      print_endline " libre."
  | Lambda_topsort (t,s) ->
      print_string "le corps de l'abstraction ";
      print_term ctx t;
      print_string " est apprtient à la sorte non typable ";
      print_sort s;
      print_endline "."
  | Not_a_type(m,t) ->
      print_string "le type de ";
      print_term ctx m;
      print_string ", qui est ";
      print_term ctx t;
      print_endline " ne se réduit pas vers une sorte."
  | Not_a_fun(m,t) ->
      print_string "le type de ";
      print_term ctx m;
      print_string ", qui est ";
      print_term ctx t;
      print_endline " ne se réduit pas vers un produit."
  | Apply_err(u,tu,v,tv) ->
      print_string "le terme ";
      print_term ctx u;
      print_string " : ";
      print_term ctx tu;
      print_string " ne peut être appliqué à ";
      print_term ctx v;
      print_string " : ";
      print_term ctx tv;
      print_endline "."
;;

let print_type_error ctx err =
  print_string "Erreur: ";
  begin
    match err with
        Under _ ->
          print_endline "dans le contexte:";
      | _ -> ()
  end;
  print_type_err ctx err
;;

(*> code noyau *)
let cTX = ref [];;

let eNV = ref Nil;;

let print_error err = print_type_error !cTX err;;

let exec_infer t =
  (match (infer_type !eNV t) with
    (Inl tt)->
      print_string "Type infere: ";
      print_term !cTX tt; print_newline()
  | (Inr err) -> print_error err)
;;

let exec_axiom x a =
  if (List.mem x !cTX) then print_endline "Nom deja utilise."
  else match (add_type !eNV a) with
    Dcl_ok ->
      eNV:=Cons (Ax(a),!eNV);
      cTX:=(x::!cTX);
      print_endline (x^" admis.")
  | Dcl_fail err ->  print_error err
;;

let exec_def x d t =
  if (List.mem x !cTX) then print_endline "Nom deja utilise."
  else match (add_def !eNV d t) with
    Dcl_ok ->
      eNV:=Cons (Def(d,t),!eNV);
      cTX:=(x::!cTX);
      print_endline (x^" defini.")
  | Dcl_fail err -> print_error err
;;

let exec_check trm typ =
  match (check_type !eNV trm typ) with
    Chk_ok -> print_endline "Correct."
  | Chk_fail err -> print_error err
;;

let exec_quit() =
  print_endline "\nAu revoir..."; exit 0;;

let exec_delete() = match !eNV with
  Nil -> print_endline "environement deja vide."
| Cons(_,env) ->
    print_endline ((List.hd !cTX)^" supprime.");
    eNV:=env;
    cTX:=(List.tl !cTX) 
;;

let exec_list() =
  List.iter (fun x -> print_string (x^" ")) (List.rev !cTX);
  print_newline()
;;

type 'sort command =
    Infer of 'sort term
  | Axiom of string * 'sort term
  | Definition of string * 'sort term * 'sort term
  | Check of 'sort term * 'sort term
  | Quit
  | Delete
  | List
;;

let mk_check = function
    (trm, None)     -> Infer trm
  | (trm, Some typ) -> Check (trm,typ)
;;

let exec_command = function
    Infer t           -> exec_infer t
  | Axiom(x,a)        -> exec_axiom x a
  | Definition(x,d,t) -> exec_def x d t
  | Check(trm,typ)    -> exec_check trm typ
  | Quit              -> exec_quit()
  | Delete            -> exec_delete()
  | List              -> exec_list()
;;

(*> lexer *)
let lexer = make_lexer
      ["Prop"; "Set"; "Type"; "Typeset";
       "["; "]"; "("; ")"; ":"; "::"; "->"; "let"; "in"; "_"; ","; ":="; ".";
       "Definition";"Lemma";"Axiom";"Variable";"Infer";"Check";"Proof";
       "Quit";"Delete";"List"]
;;

(*> parser *)
let rec parse_star p = parser       
    [< x = p ; l = (parse_star p) >] -> x::l
  | [< >] -> []
;;

let anon_var = parser
    [< 'Kwd "_" >] -> "_"
  | [< 'Ident x >] -> x
;;

let virg_an_var = parser
    [< 'Kwd "," ; x = anon_var >] -> x
;;

let lident = parser
    [< x = anon_var ; l = (parse_star virg_an_var) >] -> x::l
;;

let parse_univ = parser
    [< 'Kwd "("; 'Int n; 'Kwd ")" >] -> (nat_of_int n)
  | [< >] -> O
;;

let parse_atom = parser
    [< 'Kwd "Prop" >] -> SRT Gprop
  | [< 'Kwd "Set" >] -> SRT Gset
  | [< 'Kwd "Type"; u = parse_univ >] -> SRT (Gtype u)
  | [< 'Kwd "Typeset"; u = parse_univ >] -> SRT (Gtypeset u)
  | [< 'Ident x >] -> REF x
;;

let rec parse_expr= parser
    [< 'Kwd "[" ; l = lident ; 'Kwd ":" ; typ = parse_expr ; 'Kwd "]" ; trm = parse_expr >]
               -> List.fold_right (fun x t->ABS (x,typ,t)) l trm
  | [< 'Kwd "let" ; x = anon_var ; 'Kwd ":" ; typ = parse_expr ; 'Kwd ":=" ; arg = parse_expr ;
        'Kwd "in" ; trm = parse_expr >] -> (APP ((ABS (x,typ,trm)),arg))
  | [< 'Kwd "(" ; r = parse_expr1 >] -> r
  | [< at = parse_atom ; r = (parse_expr2 at) >] -> r 

and parse_expr1=parser
    [< 'Kwd "_" ; r = (parse_end_pi ["_"]) >] -> r
  | [< 'Ident x ; r = (parse_expr3 x) >] -> r
  | [< t1 = parse_expr ; l = (parse_star parse_expr) ; 'Kwd ")" ;
        r = (parse_expr2 (List.fold_left (fun t a->APP (t,a)) t1 l)) >] -> r

and parse_expr2 at= parser
    [< 'Kwd "->" ; t = parse_expr >] -> PROD ("_",at,t)
  | [< >] -> at

and parse_expr3 x=parser
    [< 'Kwd ","; y = anon_var; r = (parse_end_pi [x;y]) >] -> r
  | [< 'Kwd ":"; typ = parse_expr; 'Kwd ")"; trm = parse_expr >] -> PROD(x,typ,trm)
  | [< 'Kwd "->" ; t = parse_expr ; l = (parse_star parse_expr) ; 'Kwd ")"; str >]
               -> parse_expr2 (List.fold_left (fun t a->APP(t,a)) (PROD ("_",(REF x),t)) l) str
  | [< l = (parse_star parse_expr) ; 'Kwd ")" ; str>]
               -> parse_expr2 (List.fold_left (fun t a->APP(t,a)) (REF x) l) str

and parse_end_pi lb=parser
    [< l = (parse_star virg_an_var); 'Kwd ":" ; typ = parse_expr; 'Kwd ")" ; trm = parse_expr >] 
               -> List.fold_right (fun x t->PROD(x,typ,t)) (lb@l) trm
;;

let parse_term ctx strm=term_of_expr ctx (parse_expr strm);;


let parse_def_sep = parser
    [< 'Kwd ":=" >] -> ()
  | [< 'Kwd "."; 'Kwd "Proof" >] -> ()
;;

let parse_typ_cstr ctx = parser
    [< 'Kwd "::" ; typ = (parse_term ctx) >] -> Some typ
  | [< >] -> None
;;

let parse_cmd ctx = parser
    [< 'Kwd "Infer" ; t = (parse_term ctx) ; 'Kwd "." >] -> Infer t
  | [< 'Kwd "Check" ; trm = (parse_term ctx) ; otyp = (parse_typ_cstr ctx); 'Kwd "." >]
              -> mk_check(trm,otyp)  
  | [< 'Kwd ("Axiom" | "Variable"); 'Ident x ; 'Kwd ":" ; ax = (parse_term ctx) ;
        'Kwd "." >]
              -> Axiom(x,ax)
  | [< 'Kwd ("Definition" | "Lemma"); 'Ident x ; 'Kwd ":" ;
        typ = (parse_term ctx) ; _ = parse_def_sep; proof = (parse_term ctx);
         'Kwd "." >]
              -> Definition(x,proof,typ)
  | [< 'Kwd "Quit" ; 'Kwd "." >] -> Quit
  | [< 'Kwd "Delete" ; 'Kwd "." >] -> Delete
  | [< 'Kwd "List" ; 'Kwd "." >] -> List
;;

(*> boucle toplevel *)
let rec skip_til_dot strm =
  let rec skip_tok = parser
    [< 'Kwd "." >] -> ()
  | [< '_ ; strm >] -> skip_til_dot strm in
  try skip_tok strm
  with Stream.Error _ -> skip_til_dot strm
;;

let error_string =  function
    Failure s -> ": "^s
  | Stream.Error _ | Stream.Failure -> " de syntaxe"
  | e -> raise e
;;

let prompt() = print_string "\nEcc < "; flush stdout;;

let rec parse_commande strm =
  prompt();
  try parse_cmd !cTX strm
  with e ->
    let err = "Erreur"^error_string e in
    skip_til_dot strm;
    print_endline err;
    parse_commande strm
;;

let parse ts =
  Stream.from
    (fun _ ->
      try Some (parse_commande ts)
      with Stream.Failure -> None)
;;

let top_loop cs = Stream.iter exec_command (parse (lexer cs));;

let go() = top_loop (Stream.of_channel stdin);;

go();;
(*+all+*)
