open Chinese

let rec i2n n = if n=0 then O else S (i2n (n-1)) 

let rec n2i = function 
    O -> 0
  | S n -> succ (n2i n) 

let i2z = function 
 0 -> OZ
| n -> if n<0 then Neg (i2n (-n-1)) else Pos (i2n (n-1)) 

let z2i = function
  OZ -> 0
| Pos p -> succ (n2i p)
| Neg p -> (-(succ (n2i p)))

let chinese a b x y = z2i (chinese_remaindering_theorem (i2z a) (i2z b) (i2z x) (i2z y)) 

let _ = 
	let a = int_of_string Sys.argv.(1) 
	and b = int_of_string Sys.argv.(2)
	and x = int_of_string Sys.argv.(3)
	and y = int_of_string Sys.argv.(4)
	in let z = chinese a b x y 
	in 
	print_int z; print_newline(); 
	if (z-x) mod a=0 && (z-y) mod b=0 then exit 0 else exit 1




