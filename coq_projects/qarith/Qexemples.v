
Require Import Znumtheory.
Require Import Qreduction.

Open Scope Q_scope.

Coercion inject_Z : Z >-> Q.

Fixpoint fib_pair (n:nat) : Z*Z := match n with 
 | O => (0,1)%Z
 | S n => let (p,q) := fib_pair n in (q,p+q)%Z
 end.

Definition fibonacci (n:nat) := snd (fib_pair n). 

Definition fibo_frac (n:nat) := Qred (fibonacci (S n) # Z2P (fibonacci n)).

Time Eval vm_compute in fibo_frac 1000.

(* display for humans: *)

Definition get_first_n_decimal_digits (n:nat)(q:Q) : Z :=
 let q' := q*(10^n) in 
 Zdiv (Qnum q') (QDen q').

Eval vm_compute in get_first_n_decimal_digits 30 (fibo_frac 1000).

(*
From bc: 
scale=30
(1+sqrt(5))/2
1.618033988749894848204586834365
*)

Fixpoint sqrt2_newton (n:nat) : Q := match n with 
 | O => 1%Q
 | S n => let q := sqrt2_newton n in  
               Qred ( (1/2)*q + /q)
 end.

(*
Time Eval vm_compute in sqrt2_newton 10.
*)

Eval vm_compute in get_first_n_decimal_digits 100 (sqrt2_newton 10).
(*
1414213562373095048801688724209698078569671875376948073176679737990\
7324784621070388503875343276415727
*)

(* from bc: 
scale=100
sqrt(2)
1.414213562373095048801688724209698078569671875376948073176679737990\
7324784621070388503875343276415727
*)

Fixpoint e_frac_aux (n:nat) : Q*(Z*Z) := match n with 
 | O => (1,(1%Z,1%Z))
 | S n => let (q,pr) := e_frac_aux n in 
               let (fact,next) := pr in 
               let nextfact:=(next*fact)%Z in
               (Qred (q+/nextfact), (nextfact,Zsucc next))
 end.

Definition e_frac (n:nat) := fst (e_frac_aux n).

Time Eval vm_compute in e_frac 150.
Time Eval vm_compute in get_first_n_decimal_digits 100 (e_frac 150).
(*
2718281828459045235360287471352662497757247093699959574966967627724\
0766303535475945713821785251664274
*) 

(* from bc: 
scale=100
2.718281828459045235360287471352662497757247093699959574966967627724\
0766303535475945713821785251664274
*)

Fixpoint atan_aux (n:nat)(q:Q) {struct n } : (Q*(Q*Z)) := match n with 
	                          (* part sum / last term / (-1)^n*(2n+1) *)
  | O => (q,(q,1%Z)) 
  | S n => let (sum,pr) := atan_aux n q in 
                let (power,div) := pr in 
                let nextpower:=q*q*power in 
	        let nextdiv:= ((-2)*Zsgn(div)-div)%Z in 
                (Qred (sum+nextpower/nextdiv), (nextpower, nextdiv))
 end.

Definition atan (n:nat)(q:Q) := fst (atan_aux n q).

Definition pi_frac (n:nat) := Qred (16*(atan n (1#5))-4*(atan n (1#239))).

Time Eval vm_compute in get_first_n_decimal_digits 100 (pi_frac 70).
(*
3141592653589793238462643383279502884197169399375105820974944592307\
8164062862089986280348253421170679

bc:
3.141592653589793238462643383279502884197169399375105820974944592307\
8164062862089986280348253421170680
*)

Extraction "pi.ml" pi_frac get_first_n_decimal_digits.
