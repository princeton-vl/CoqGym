open Fibo
open Big_int

let fib n = z2b (fibonacci (i2n n))
        
let _ = 
  print_string 
    (string_of_big_int (fib (int_of_string Sys.argv.(1)))); 
  print_newline()


