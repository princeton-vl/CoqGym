(* This code is copyrighted by its authors; it is distributed under  *)
(* the terms of the LGPL license (see LICENSE and description files) *)

(*****************************************************************************)
(*                                                                           *)
(*          Buchberger : extraction                                          *)
(*                                                                           *)
(*          Laurent Thery 	                                             *)
(*                                                                           *)
(*****************************************************************************)

Require Import LexiOrder.
Require Import BuchRed.
Require Extraction.

Extraction
 "sin_num.ml" redbuch splus smult sscal spO sp1 sgen orderc_dec degc
             total_orderc_dec.

(*

(***********************************************************************)
(* To run the code on examples you first need a top level that includes
   the bignum. To create that under unix do 
     ocamlmktop -custom -o ocaml_num nums.cma -cclib -lnums
   then start ocaml_num and enter the following ML code 
 *)

open Ratio;;
open Big_int;;


#use "sin_num.ml";;

type r6 =  (ratio, mon) prod list;;

let rec n_to_p n  =  if n = 0 then O else (S (n_to_p (n-1)));;

let eqd n m = if (eq_ratio n m) then  Left else Right;;

let ri = ratio_of_int;;

let plusP: int -> r6 -> r6 -> r6 =  
  fun n -> 
   let n = n_to_p n in 
   (splus (ri 0) (add_ratio) eqd n (total_orderc_dec n) n);;



let multP: int -> r6 -> r6 -> r6  = 
  fun n -> 
   let n = n_to_p n in 
  (smult (ri 0)(ri 1) (add_ratio) (minus_ratio) (sub_ratio) (mult_ratio)
         (div_ratio) n eqd n (total_orderc_dec n) n);;

let sscal a0 a1 plusA invA minusA multA divA _ eqA_dec n _ a p =

let scalP: int -> int -> r6 -> r6  = 
  fun n -> 
   let n = n_to_p n in 
      fun m -> 
      (sscal (ri 0) (ri 1) (add_ratio) (minus_ratio) (sub_ratio) (mult_ratio)
         (div_ratio) n eqd n n (ri m));;

let spO a0 n =
  Nil


let p0 : int -> r6 = fun n -> (spO  (ri 0) (n_to_p n));;

let p1 : int -> r6 = (fun n -> (sp1 (ri 0) (ri 1) (add_ratio) (minus_ratio) (sub_ratio) (mult_ratio)
         (div_ratio) n (n_to_p n) )) ;;

let sgen a0 a1 plusA invA minusA multA divA _ n m =

let mon : int -> int -> r6 = fun n -> fun m -> sgen (ri 0) (ri 1) (add_ratio) (minus_ratio) (sub_ratio) (mult_ratio)
         (div_ratio) n (n_to_p n)  (n_to_p m);;

let div1_ratio a b c = div_ratio a b;;


let redbuch a0 a1 plusA invA minusA multA divA _ eqA_dec n ltM_dec _ l =

let tbuch : int -> r6 list -> r6 list =
    (fun n ->
      let n = n_to_p n in 
      redbuch (ri 0) (ri 1) (add_ratio) (minus_ratio) (sub_ratio) (mult_ratio)
         (div1_ratio) n eqd  n  (total_orderc_dec n) n);;

let rec l2l l = match l with [] -> Nil | (a::tl) -> Cons (a, l2l tl);;
let rec l5l l = match l with Nil -> [] | Cons (a,tl) -> a :: (l5l tl);;

let tbuchl = fun n -> fun l -> (l5l (tbuch n (l2l l)));;

(* Pretty printer a la Maple *)
open Format;;


let name_var = ref ["X";"Y";"Z";"T";"U";"V";"W"];;

let rec is_null_coef a = match a with
  N_0  -> true
| (C_n (_,a,b)) -> if (a = O) then is_null_coef b else false;;

let string_of_S a = 
  let rec s_S a d = match a with
     (S b) -> s_S b (1+d)
    | O -> string_of_int d
  in s_S a 0;;

let rec printP_mon d l =
    match d with
          N_0 -> ()
         |(C_n (_, a, b)) -> if (a = O) then
                             printP_mon b (List.tl l) else
                             if (a = (S O)) then
                             begin
                             print_string(List.hd l);
                             printP_mon b (List.tl l)
                             end              else
                             begin
                             print_string(List.hd l);
                             print_string("^");
                             print_string(string_of_S a);
                             printP_mon b (List.tl l)
                             end;;

let rec printP_mon_m d l =
    match d with
          N_0 -> ()
         |(C_n (_, a, b)) -> if (a = O) then
                             printP_mon_m b (List.tl l)   else
                             if (a = (S O)) then
                             begin
                             print_string(""^List.hd l);
                             printP_mon b (List.tl l)
                             end              else
                             begin
                             print_string(""^List.hd l);
                             print_string("^");
                             print_string(string_of_S a);
                             printP_mon b (List.tl l)
                             end;;


let ratio0 = (ri 0);;
let ratio1 = (ri 1);;

let string_of_ratio1 r = 
  if (is_integer_ratio r) then
    string_of_big_int (numerator_ratio r)
  else
    string_of_ratio r
;;

let rec printP_rec p f=
    match p with
	  Nil -> if f=0
	         then ()
		 else print_string "0"
	  |Cons(Pair(a,coef),p')->
                if (eq_ratio a ratio0) then
	           printP_rec p' f
                else if (lt_ratio ratio0 a) then
		  begin
                          if f=0 then print_string "+" else ();
		          if (is_null_coef coef)
		            then print_string(string_of_ratio1 a)
			    else (
 		                  if (not (eq_ratio a ratio1))
			            then (print_string(string_of_ratio1 a);
			                  printP_mon_m coef !name_var)
		                    else printP_mon coef !name_var);
		          print_space();
			  print_cut();
		          printP_rec  p' 0
                  end
                else 
                 begin
		          if (is_null_coef coef)
		            then print_string(string_of_ratio1 a)
			    else (
 		                  if (not (eq_ratio (abs_ratio a) ratio1))
			          then (print_string(string_of_ratio1 a);
				        printP_mon_m coef !name_var)
		                  else (print_string "-";printP_mon coef !name_var));
		          print_space();
			  print_cut();
		          printP_rec p' 0
                 end;;
		
let printP p =
    open_hovbox 3;
    printP_rec  p 1;
    print_flush ();;
    
#install_printer printP;;

let dim = 6;;
let plus = plusP dim;;
let mult = multP dim;;
let scal = scalP dim;;
let p1 = p1 dim;;
let gen = mon dim;;
let tbuch = tbuchl dim;;

name_var := ["a";"b";"c";"d";"e";"f"];;

let a = gen 0;;
let b = gen 1;;
let c = gen 2;;
let p1 =  gen 6;;

let r0 = (plus a (plus b c));;
let r1 = (plus (mult a b) (plus (mult b c) (mult c a)));;
let r2 = (plus (mult a (mult b c)) (scal (-1) p1));;


tbuch [r2;r1;r0];;

let d = gen 3;;

let r0 = (plus a (plus b (plus c d)));;
let r1 = (plus (mult a b) (plus (mult b c) (plus (mult c d) (mult d a))));;
let r2 = (plus (mult a (mult b c)) (plus (mult b (mult c d)) (plus (mult c (mult d a)) 
             (mult d (mult a b)))));;
let r3 = (plus (mult a (mult b (mult c d))) (scal (-1) p1));;




tbuch [r3;r2;r1;r0];;

let e = gen 4;;

let r0 = (plus a (plus b (plus c (plus d e))));;
let r1 = (plus (mult a b) (plus (mult b c) (plus (mult c d) (plus (mult d e) (mult e a)))));;
let r2 = (plus (mult a (mult b c)) (plus (mult b (mult c d)) (plus (mult c (mult d e))
(plus (mult d (mult e a))
             (mult e(mult a b))))));;
let r3= (plus (mult a (mult b (mult c d))) (plus (mult b (mult c (mult d e))) 
(plus (mult c (mult d (mult e a)))
(plus (mult d (mult e (mult a b)))
             (mult e(mult a (mult b c)))))));;
let r4 = (plus (mult a (mult b (mult c (mult d e)))) (scal (-1) p1));;



tbuch [r4;r3;r2;r1;r0];;


let f = gen 5;;

let r0 = (plus a (plus b (plus c (plus d (plus e f)))));;
let r1 = (plus (mult a b) (plus (mult b c) (plus (mult c d) (plus (mult d e) (plus (mult e f) (mult f a))))));;
let r2 = (plus (mult a (mult b c)) (plus (mult b (mult c d)) (plus (mult c (mult d e))
(plus (mult d (mult e f))
(plus (mult e (mult f a))
             (mult f (mult a b)))))));;
let r3= (plus (mult a (mult b (mult c d))) (plus (mult b (mult c (mult d e))) 
(plus (mult c (mult d (mult e f)))
(plus (mult d (mult e (mult f a)))
(plus (mult e (mult f (mult a b)))
             (mult f(mult a (mult b c))))))));;
let r4= (plus (mult a (mult b (mult c (mult d e)))) (plus (mult b (mult c (mult d (mult e f)))) 
(plus (mult c (mult d (mult e (mult f a))))
(plus (mult d (mult e (mult f (mult a b))))
(plus (mult e (mult f (mult a (mult b c))))
             (mult f(mult a (mult b (mult c d)))))))));;
let r5 = (plus (mult a (mult b (mult c (mult d (mult e f))))) (scal (-1) p1));;

tbuch [r5;r4;r3;r2;r1;r0];;


*)
