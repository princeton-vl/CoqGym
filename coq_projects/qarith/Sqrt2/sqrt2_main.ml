open Sqrt2
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

let usage () = 
  print_string ("Usage: sqrt <n>\n"^  
		"Returns a rational close to sqrt(2) at precision 2^-<n>\n"); 
  exit 1

let _ = 
  if Array.length Sys.argv <> 2 then usage (); 
  let nb = int_of_string Sys.argv.(1) in 
  let q = sqrt2.cauchy (sqrt2.modulus (i2n nb)) in
  Printf.printf "%s / %s\n" 
    (string_of_big_int (z2b q.qnum)) 
    (string_of_big_int (p2b q.qden))
  
