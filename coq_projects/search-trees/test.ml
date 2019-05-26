(* test of the search trees *)

#use "searchtrees.ml";;

(* int <-> nat *)

let rec i2n = function 0 -> O | n -> (S (i2n (pred n)));;

let rec n2i = function O -> 0 | (S n) -> succ (n2i n);;

(* int list <-> nat list *)

let rec il2nl = function 
  | [] -> Nil 
  | a :: t -> Cons (i2n a,il2nl t);;

let rec random_list p = function 
  | 0 -> []
  | n -> (Random.int p) :: (random_list p (pred n));;

let print_list l = 
   print_string "[";
   let rec print = function 
     | [] -> print_string "]";
     | [t] -> print_int t;print_string "]";
     | t :: q -> print_int t; print_string ";"; print q
   in print l;;

(* printing a tree by a left-right visit *)

let rec print_tree = function 
  | NIL -> print_string "" 
  | Bin (n,g,d) -> 
     begin	 
	print_string "(" ; 
	print_tree g; 
	print_int (n2i n);
	print_tree d; 
	print_string ")" 
     end;;


let _ = 
   Random.self_init();
   let l = random_list 20 20 in 	
   let t = list2trees (il2nl l) in 		
   print_string "Today's Random List is : ";
   print_list l; 
   print_newline ();  
   print_string "This gives the Search Tree : "; 
   print_tree t; 
   print_newline (); 
   print_string "Which maximum element is : ";
   print_int (let ExistT (n,_) = rmax t in n2i n); 
   print_newline ();;
		 

