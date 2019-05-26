open Comp

(* from positive [int] to [nat] *)

let rec i2nat = function 0 -> O | n -> (S (i2nat (pred n))) 

(* builds the list of length [size] containing the digits 
   of [n] in base [base]. [n] should be less than [base^size] *)

let i2num base n size = 
  let rec accum l n k = 
    if k = size then l 
    else let d = i2nat (n mod base) in 
       accum (Cons (i2nat k, d, l)) (n/base) (k+1)
  in accum Nil n 0



let _ = 
  let a = int_of_string (Sys.argv.(1))
  and b = int_of_string (Sys.argv.(2))
  in 
  if (a < 0) || (b < 0) then begin
    print_string "non-positive numbers !\n"; exit 1
  end 
  else begin
    (* the caml [int] are signed 31-bits, so positive [int] can be coded in 30-bits *)
    let c = comparator (i2nat 30) E (i2num 2 a 30) (i2num 2 b 30)  
    in 
    match c with 
      | E -> print_int a; print_string " = "; print_int b; print_newline(); 
	  if a=b then exit 0 else exit 1 
      | L -> print_int a; print_string " < "; print_int b; print_newline();
          if a<b then exit 0 else exit 1
      | G -> print_int a; print_string " > "; print_int b; print_newline();
          if a>b then exit 0 else exit 1
  end
