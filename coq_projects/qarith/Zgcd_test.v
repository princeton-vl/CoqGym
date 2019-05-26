Require Import ZArith Znumtheory Ndigits.

Open Scope Z_scope.

(* A few tests of Zgcd *)

Fixpoint fib_pair (n:nat) : Z*Z := match n with 
 | O => (0,1)
 | S n => let (p,q) := fib_pair n in (q,p+q)
 end.

Definition fibonacci (n:nat) := snd (fib_pair n). 

Definition Zsize (z:Z) := match z with Z0 => O  | Zpos p | Zneg p => Psize p end.


Time Definition fib_1000 := Eval vm_compute in (fibonacci 1000).
Time Definition fib_1001 := Eval vm_compute in (fibonacci 1001).
Time Definition fib_5000 := Eval vm_compute in (fibonacci 5000).
Time Definition fib_5001 := Eval vm_compute in (fibonacci 5001).

Time Eval vm_compute in Zsize (fib_1000).
Time Eval vm_compute in Zsize (fib_5000).
Time Eval vm_compute in (Zgcd fib_1000 fib_1001).
Time Eval vm_compute in (Zgcd fib_5000 fib_5001).

Definition big := Eval vm_compute in fib_5000 * fib_5001 * fib_1000 * fib_1001.
Definition big2 := Eval vm_compute in fib_5000 * fib_5000 * fib_1000 * fib_1000.

Time Eval vm_compute in Zsize big.

Time Eval vm_compute in Zgcd big big2.

(* slow previous Euclid algorithm:
Require Zgcd_old.
Time Eval vm_compute in (Zgcd fib_1000 fib_1001).
*)
