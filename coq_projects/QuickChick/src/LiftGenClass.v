Require Import QuickChick.

Class liftable (A B : Type) :=
  {
    lift_m : A -> B 
  }.

Instance lift0 {A} : liftable (G A) (G A) :=
  { 
    lift_m := id 
  }.

Instance liftN {A B R} `(liftable (G B) R) : liftable (G (A -> B)) (G A -> R):=
   { 
     lift_m f ga := 
       lift_m (liftGen2 id f ga) 
   }.

Definition liftM {A B R} `{liftable (G B) R} (f : A -> B) (g : G A) : R :=
  lift_m (fmap f g).

Definition ex1 : G nat := liftM (fun x => x + 3) (returnGen 0).
Definition ex2 : G nat := liftM (fun x y => x + y) (returnGen 0) (returnGen 1).
Definition ex3 : G nat := liftM (fun x y z => x + y + z)
                                (returnGen 0) (returnGen 1) (returnGen 2).

Eval cbv -[plus] in ex1.
(* = fmap (fun x : nat => x + 3) (returnGen 0) -- fair enough *)

Eval cbv -[plus] in ex2.
(* = liftGen2 id (fmap (fun x y : nat => x + y) (returnGen 0)) (returnGen 1)
where
fmap : (nat -> (nat -> nat)) -> G nat -> G (nat -> nat)
liftGen2 : ((nat -> nat) -> nat -> nat) ->
            (G (nat -> nat)) -> G nat -> G nat
 *)

Eval cbv -[plus] in ex3.
(* = liftGen2 (fun x : nat -> nat => x)
         (liftGen2 (fun x : nat -> nat -> nat => x)
            (fmap (fun x y z : nat => x + y + z) (returnGen 0)) 
            (returnGen 1)) (returnGen 2)
*)

(* this is not well typed ... wtf? *)
Check (liftM (fun x y => x + y + y) (returnGen 0) (returnGen 1) (returnGen 2)
  : G nat).

(* it's even worse ... all kinds of stuff are accepted in Check and Eval *)
Eval simpl in (liftM (fun x => x + 1) (returnGen 0) 0 0 : G nat).
(*
liftM nat nat (nat -> nat -> G nat) `{liftable (G nat) (nat -> nat -> G nat)} ...
-- but we don't have such an instance!
We need to use definitions to get a type error
Definition xxx := (liftM (fun x => x + 1) (returnGen 0) 0 0 : G nat).
Toplevel input, characters 19-24:
Error: Cannot infer the implicit parameter H of
liftM.
Could not find an instance for "liftable (G nat) (nat -> nat -> G nat)".
*)
