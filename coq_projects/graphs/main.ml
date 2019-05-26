open Checker
open Genlex
open Unix 


let nb_var = ref 1 (* because var zero is the zero constant *)
let h_var = Hashtbl.create 103


let lexer = 
  make_lexer 
    [ "+" ; "=" ; "<" ; ">" ; "<=" ; ">=" ; 
      "(" ; ")" ; "#" ; "&" ; "~" ; "->" ; "<->" ]

(* We do not put - as a keyword. It will be part of a Caml integer. 
   Be sure to leave a blank before a - to help the parser. 
   For example [x+ -1<x] *)

let get_nv v = 
  try 
    i2a (Hashtbl.find h_var v) 
  with Not_found -> 
    let p = !nb_var in 
    nb_var:=p+1;
    Hashtbl.add h_var v p; 
    i2a p

type expr = 
    V of ad
  | K of z 
  | P of ad * z
      

type op = Eq | Lt | Gt | Le | Ge 

let  op_of_Kwd = function 
    "=" -> Eq
  | "<" -> Lt 
  | ">" -> Gt
  | "<=" -> Le
  | ">=" -> Ge
  | _ -> assert false 

let rec expr = parser 
    [< 'Ident s ; p = rest_expr s >] -> p
  | [< 'Int n >] -> K (i2z n)

and rest_expr s = parser 
    [< 'Kwd "+" ; 'Int n >] -> P (get_nv s, i2z n)
  | [<>] -> V (get_nv s)

and logic_5 = parser
    [< p = logic_4 ; q = logic_rest_5 p >] -> q

and logic_rest_5 p = parser
    [< 'Kwd "<->" ; q = logic_4 ; 
       r = logic_rest_5 (ZCGiff (p,q)) >] -> r
  | [<>] -> p

and logic_4 = parser
    [< p = logic_3 ; q = logic_rest_4 p >] -> q

and logic_rest_4 p = parser
    [< 'Kwd "->" ; q = logic_3 ; 
       r = logic_rest_4 q >] -> ZCGimp (p,r)
  | [<>] -> p

and logic_3 = parser
    [< p = logic_2 ; q = logic_rest_3 p >] -> q

and logic_rest_3 p = parser
    [< 'Kwd "#" ; q = logic_2 ; 
       r = logic_rest_3 (ZCGor (p,q)) >] -> r
  | [<>] -> p

and logic_2 = parser
    [< p = logic_1 ; q = logic_rest_2 p >] -> q

and logic_rest_2 p = parser
    [< 'Kwd "&" ; q = logic_1 ; 
       r = logic_rest_2 (ZCGand (p,q)) >] -> r
  | [<>] -> p

and logic_1 = parser
    [< 'Kwd "~" ; p = logic_1 >] -> p
  | [< 'Kwd "(" ; p = logic_5 ; 'Kwd ")" >] -> p
  | [< p = expr ; 'Kwd o ; r = expr >] -> 
      let op = (try op_of_Kwd o with _ -> raise (Stream.Error o))
      in (match p,op,r with 
	| (V x),Le,(V y) -> ZCGle (x,y) 
	| (V x),Ge,(V y) -> ZCGge (x,y)
	| (V x),Lt,(V y) -> ZCGlt (x,y)
	| (V x),Gt,(V y) -> ZCGgt (x,y)      
	| (V x),Le,(P (y,k)) -> ZCGlep (x,y,k) 
	| (V x),Ge,(P (y,k)) -> ZCGgep (x,y,k)
	| (V x),Lt,(P (y,k)) -> ZCGltp (x,y,k)
	| (V x),Gt,(P (y,k)) -> ZCGgtp (x,y,k)      
	| (P (x,k)),Le,(V y) -> ZCGlem (x,y,k) 
	| (P (x,k)),Ge,(V y) -> ZCGgem (x,y,k)
	| (P (x,k)),Lt,(V y) -> ZCGltm (x,y,k)
	| (P (x,k)),Gt,(V y) -> ZCGgtm (x,y,k)  
	| (P (x,k)),Le,(P (y,k')) -> ZCGlepm (x,y,k,k') 
	| (P (x,k)),Ge,(P (y,k')) -> ZCGgepm (x,y,k,k')
	| (P (x,k)),Lt,(P (y,k')) -> ZCGltpm (x,y,k,k')
	| (P (x,k)),Gt,(P (y,k')) -> ZCGgtpm (x,y,k,k')  
	| (V x),Eq,(V y) -> ZCGeq (x,y)
	| (V x),Eq,(P (y,k)) -> ZCGeqp (x,y,k)
	| (P (x,k)),Eq,(V y) -> ZCGeqm (x,y,k)
	| (P (x,k)),Eq,(P (y,k')) -> ZCGeqpm (x,y,k,k')
	| (K k),Le,(V y) -> ZCGzylem (y,k) 
	| (K k),Ge,(V y) -> ZCGzygem (y,k)
	| (K k),Lt,(V y) -> ZCGzyltm (y,k)
	| (K k),Gt,(V y) -> ZCGzygtm (y,k)    
	| (K k),Le,(P (y,k')) -> ZCGzylepm (y,k,k') 
	| (K k),Ge,(P (y,k')) -> ZCGzygepm (y,k,k')
	| (K k),Lt,(P (y,k')) -> ZCGzyltpm (y,k,k')
	| (K k),Gt,(P (y,k')) -> ZCGzygtpm (y,k,k')    
	| (K k),Eq,(V y) -> ZCGzyeqm (y,k)
	| (K k),Eq,(P (y,k')) -> ZCGzyeqpm (y,k,k')
	| (V x),Le,(K k) -> ZCGxzlep (x,k) 
	| (V x),Ge,(K k) -> ZCGxzgep (x,k)
	| (V x),Lt,(K k) -> ZCGxzltp (x,k)
	| (V x),Gt,(K k) -> ZCGxzgtp (x,k) 
	| (P (x,k)),Le,(K k') -> ZCGxzlepm (x,k,k') 
	| (P (x,k)),Ge,(K k') -> ZCGxzgepm (x,k,k')
	| (P (x,k)),Lt,(K k') -> ZCGxzltpm (x,k,k')
	| (P (x,k)),Gt,(K k') -> ZCGxzgtpm (x,k,k')
	| (V x),Eq,(K k) -> ZCGxzeqp (x,k)
	| (P (x,k)),Eq,(K k') -> ZCGxzeqpm (x,k,k')
	| (K k),Le,(K k') -> ZCGzzlep (k,k') 
	| (K k),Ge,(K k') -> ZCGzzgep (k,k')
	| (K k),Lt,(K k') -> ZCGzzltp (k,k')
	| (K k),Gt,(K k') -> ZCGzzgtp (k,k') 	      
	| (K k),Eq,(K k') -> ZCGzzeq (k,k'))      


let parse_all = parser [< e = logic_5; _ = Stream.empty >] -> e

let _ =
  let fd = if Array.length Sys.argv > 1 then
    openfile Sys.argv.(1) [O_RDONLY] 0644
  else stdin
  in let channel = in_channel_of_descr fd
  in let e = parse_all (lexer (Stream.of_channel channel))
  in 
  if zCG_prove e = True then 
    (print_string "Tautology!\n"; exit 0)
  else 
    (print_string "Not a tautology!\n"; exit 1)

