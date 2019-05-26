(* test of the search trees *)

#use "searchtrees.ml";;

(** val i2p : int -> positive **)

let i2p = 
  let rec i2p = function 
    1 -> XH 
    | n -> let n' = i2p (n/2) in if (n mod 2)=0 then XO n' else XI n'
  in i2p

(** val i2z : int -> z **)

let i2z =  function
    0 -> Z0
  | n -> if n < 0 then Zneg (i2p (-n)) else Zpos (i2p n)

(** val p2i : positive -> int **)

let rec p2i = function XH -> 1 | XO n -> 2 * p2i n | XI n -> 2 * p2i n + 1

(** val z2i : Z -> int **)

let rec z2i = function Z0 -> 0 | Zneg n -> - p2i n | Zpos n -> p2i n 

(* int list <-> Z list *)

let rec il2zl = function 
  | [] -> Nil 
  | a :: t -> Cons (i2z a,il2zl t);;

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
  | Z_leaf -> print_string "" 
  | Z_bnode (n,g,d) -> 
     begin	 
	print_string "(" ; 
	print_tree g; 
	print_int (z2i n);
	print_tree d; 
	print_string ")" 
     end;;


let _ = 
   Random.self_init();
   let l = random_list 20 20 in 	
   let t = list2trees (il2zl l) in 		
   print_string "Today's Random List is : ";
   print_list l; 
   print_newline ();  
   print_string "This gives the Search Tree : "; 
   print_tree t; 
   print_newline (); 
   print_string "Which maximum element is : ";
   print_int (let ExistT (n,_) = rmax t in z2i n); 
   print_newline ();;
		 

