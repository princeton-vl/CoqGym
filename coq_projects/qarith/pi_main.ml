open Pi
open Big_int

(* [int] <-> [nat], for positive [int], tail recursive *)

let i2n = 
  let rec acc p = function 0 -> p | n -> acc (S p) (n-1)
  in acc O  

(* [positive] -> [big_int] *)

let rec p2b = function 
 XH -> unit_big_int
| XO p -> (mult_int_big_int 2 (p2b p))
| XI p -> (succ_big_int (mult_int_big_int 2 (p2b p)))

(* [z] -> [big_int] *)

let z2b = function 
  Z0 -> zero_big_int
| Zpos p -> (p2b p)
| Zneg p -> (minus_big_int (p2b p))       

let print n m =  
  string_of_big_int 
   (z2b(get_first_n_decimal_digits (i2n n) (pi_frac (i2n m))));;
  
let _ = print_string (print (int_of_string (Sys.argv.(1))) (int_of_string (Sys.argv.(2)))); 
        print_newline ();
