Require Extraction.
Require Import Zgcd.

Axiom int : Set.
Axiom i2p : int -> positive.
Axiom p2i : positive -> int. 
Axiom i2z : int -> Z.
Axiom z2i : Z -> int. 

Extract Inlined Constant int => "int". 

Extract Constant i2p =>
 "  
  let rec i2p = function 
    1 -> XH 
  | n -> let n' = i2p (n/2) in if (n mod 2)=0 then XO n' else XI n'
  in i2p
".
 
Extract Constant p2i =>
 "
  let rec p2i = function 
    XH -> 1
  | XO p -> 2*(p2i p)
  | XI p -> 2*(p2i p)+1
  in p2i 
".


  Extract Constant i2z =>
   " function 
    0 -> Z0
  | n -> if n < 0 then Zneg (i2p (-n)) else Zpos (i2p n)
"
  
  .
  Extract Constant z2i =>
   "function
    Z0 -> 0 
  | Zpos p -> p2i p
  | Zneg p -> -(p2i p)
"
  .

Set Extraction AccessOpaque.
Extraction "chinese.ml" chinese_remaindering_theorem int i2p p2i z2i i2z.
