
(* A simple tactic to do the parallel replacement of the first occurence of term1
    with term3 and the firs occurrence of term2 with term4 
*)
Ltac replace2_tac term1 term2 term3 term4 :=
let tmp1 := fresh "tmp" in
let tmp2 := fresh "tmp" in
let tmp3 := fresh "tmp" in
let tmp4 := fresh "tmp" in
  (set (tmp1 := term1) in |- * at 1; 
   set (tmp2 := term2) in |-* at 1;
   (set (tmp3 := term1); set (tmp4 := term2));
   unfold tmp1; clear tmp1; replace term1 with term3;
   set (tmp1 := term3);
   unfold tmp2; clear tmp2;
  [ replace term2 with term4 | idtac]; unfold tmp1, tmp3, tmp4; clear tmp1 tmp3 tmp4). 
