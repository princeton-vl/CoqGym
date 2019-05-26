(* tests the multiplication with and without continuations *)

#use "leavemult.ml";;

let rec i2n = function 0 -> O | n -> (S (i2n (pred n)));;

let rec n2i = function O -> 0 | (S n) -> succ (n2i n);;

(* we use the prefix ! and the infix * for coding Leaf and Cons *)

let ( ! ) n = Leaf (i2n n);;

let ( * ) n m = Cons (n,m);;

let rec print_tree = function 
  | Leaf n -> print_int (n2i n) 
  | Cons (g,d) -> 
      begin	
	print_string "(" ; 
	print_tree g; 
	print_string "*" ;
	print_tree d; 
	print_string ")" 
      end;;

let _ = 
   let c = ( !4 * ( !6 * !0) ) * ( ( !3 * ( !7 * !1) ) * ( !3 * !8 ) * !5 * !8) in
   let res1 = (n2i (trivialalgo c)) 
   and res2 = (n2i (cpsalgo c)) in
   print_string "Trivial algorithm gives :\n";
   print_tree c; 
   print_string " = "; 
   print_int res1;
   print_newline();
   print_string "Algorithm with continuation gives :\n";
   print_tree c;
   print_string " = ";
   print_int res2;
   print_newline();
   if res1 <> 0 || res2 <>0 then exit 1;;
		 

