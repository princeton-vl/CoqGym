Require Import PolSBase.

Section PolFactorSimpl.

(* The set of the coefficient usually Z or better Q *)
Variable C : Set.

(* Usual operations *)
Variable Cplus : C -> C ->  C.
Variable Cmul : C -> C ->  C.
Variable Cop : C ->  C.

(* Constant *)
Variable C0 : C.
Variable C1 : C.

(* Test to 1 *)
Variable isC1 : C ->  bool.

(* Test to 0 *)
Variable isC0 : C ->  bool.

(* Test if positive *)
Variable isPos : C ->  bool.

(* Divisibility *)
Variable Cdivide : C -> C ->  bool.

(* Division *)
Variable Cdiv : C -> C ->  C.

(* Gcd *)
Variable Cgcd: C -> C -> C.

(* Test if the difference of two terms is zero *)
Definition is_eq :=  fun x y => 
  let r :=  simpl C Cplus Cmul Cop C0 C1 isC1 isC0 isPos Cdivide Cdiv (PEsub x y) in
   match r with
     PEc c  => isC0 c
  |  _          => false
  end.
(*
Axiom is_eq: (PExpr C) -> (PExpr C) -> bool.
*)

(* Test if the sum of two term is zero *)

Definition is_op :=  fun x y => 
  let r :=  simpl C Cplus Cmul Cop C0 C1 isC1 isC0 isPos Cdivide Cdiv (PEadd x y) in
   match r with
     PEc c  => isC0 c
  |  _          => false
  end.

(* 
Axiom is_op: (PExpr C) -> (PExpr C) -> bool.
*)

Definition test_in :=
   fun x y => 
        match x, y with
          PEc c1, PEc c2 =>  if (isC1 (Cgcd c1 c2)) then false else true
         | _ , _ => match (is_eq x y) with true => true | false => is_op x y end
        end.

(* Return the first factor of a sum *)
Fixpoint first_factor (e: PExpr C) : PExpr C :=
match e with
  PEadd e1 _  =>  first_factor e1
| PEsub e1 _  =>  first_factor e1
| PEopp e1     =>  first_factor e1
| _                    =>  e
end.

(* Split a product in list of products *)
Fixpoint split_factor (e: PExpr C) : list (PExpr C) :=
match e with
  PEmul e1 e2  =>  (split_factor e1)++(split_factor e2)
| PEopp e1        =>  match  (split_factor e1) with (_::nil) => e::nil | l1 => l1 end 
| _                    =>  e::nil
end.

(* Split a product in list of products *)
Fixpoint split_factors (e: PExpr C) : list (list (PExpr C)) :=
match e with
  PEadd e1 e2  =>  (split_factors e1)++(split_factors e2)
| PEsub e1 e2  =>  (split_factors e1)++(split_factors e2)
| PEopp e1        =>  match  (split_factors e1) with ((_::nil)::nil) => (e::nil)::nil | l1 => l1 end 
| _                    =>  (split_factor e)::nil
end.

(* Application on an optional type *)
Definition oapp:= 
   fun (A B:Set) (a: A) (f: A -> B -> B) (l: option B) => 
       match l with Some l1 => Some (f a l1) | _ => None end.

Let ocons := fun  x => oapp _ _ x (@cons (PExpr C)).

(* Remove an element in a list *)
Fixpoint remove_elem (e: PExpr C) (l: list (PExpr C)) {struct l}: option (list (PExpr C)) :=
match l with
   nil   =>  None
| cons e1 l1  =>  if (test_in e e1) then Some l1 else (ocons e1 (remove_elem e l1))
end.

Let oconst := fun (A:Set) x =>  oapp _ _ x (fun x (y: A * list (PExpr C)) => let (v1,l1) := y in (v1, x::l1)).


(* Remove a constant in a list *)
Fixpoint remove_constant (c: C) (l: list (PExpr C)) {struct l}: option (C * list (PExpr C)) :=
match l with
   nil   =>  None
| cons (PEc c1)  l1  =>  if (isC1 (Cgcd c c1)) then oconst  _ (PEc c1) (remove_constant c l1)
                                                                             else Some (Cgcd c c1, cons (PEc (Cdiv c (Cgcd c c1))) l1)
| cons c1 l1 => oconst _  c1 (remove_constant c l1)
end.
        
(* Strip the element that are not in the list *)

Fixpoint strip (l1 l2: list (PExpr C)) {struct l1} : list (PExpr C) :=
match l1 with
  nil => nil
| cons (PEc c) l3 => match remove_constant c l2 with 
                                     None => strip l3 l2
                                  | Some (c1, l4) => cons (PEc c1) (strip l3 l4)
                                   end
| cons e l3 =>  match remove_elem e l2 with 
                                     None => strip l3 l2
                                  | Some l4 => cons e (strip l3 l4)
                           end
end.

(* iter strip for all the element l2 *)
Fixpoint delta (l1: list (PExpr C))  (l2:  list (list (PExpr C))) {struct l2} : list (PExpr C) :=
match l2 with
nil => l1
| cons l l4 => match strip l1 l with 
                         nil  => nil
                       | l3 => delta l3 l4
                      end
end.

Let mkMul := mkPEmul C Cmul Cop C0 isC1 isC0.
Let mkOpp := mkPEopp  C Cop.
Let mkAdd := mkPEadd C Cplus Cmul Cop C0 isC1 isC0 isPos.
Let mkSub := mkPEsub C Cplus Cmul Cop C0 isC1 isC0 isPos.


(* Remove an element in a list *)
Fixpoint subst_elem (e: PExpr C) (l: list (PExpr C)) {struct l}: option (bool * list (PExpr C)) :=
match l with
   nil   =>  None
| cons e1 l1  =>  if is_eq e e1 then Some (true, l1) else
                             if is_op e e1 then Some (false, l1) else  (oconst _ e1 (subst_elem e l1))
end.


(* Remove a constant in a list *)
Fixpoint subst_constant (c: C) (l: list (PExpr C)) {struct l}: option (C * list (PExpr C)) :=
match l with
   nil   =>  None
| cons (PEc c1)  l1  =>  if (Cdivide c1 c) then  Some (Cdiv c c1,  l1)
                                                                      else oconst _ (PEc c1) (subst_constant c l1)
| cons e1 l1 => oconst _ e1 (subst_constant c l1)
end.
    

(* Split a product in list of products *)
Fixpoint subst_one_factor (e: PExpr C) (l: list (PExpr C)) {struct e}: PExpr C * list (PExpr C) :=
match e with
  PEmul e1 e2  => let (e3, l1) := subst_one_factor e1 l in
                                let (e4, l2) := subst_one_factor e2 l1 in
                                  (mkMul e3 e4, l2)
| PEopp e1        =>  let (e3, l1) := subst_one_factor e1 l in
                                     (mkOpp e3, l1) 
| PEc c               => match subst_constant c l with
                                     None => (e, l)
                                 |   Some (c1, l1) => (PEc c1, l1)
                                 end 
| _ =>  match subst_elem e l with
              None => (e, l) 
           | Some (true, l1) => (PEc C1, l1)
           | Some (false, l1) => (PEc (Cop C1), l1)
           end
end.

(* Return the first factor of a sum *)
Fixpoint subst_factor (l: list (PExpr C)) (e: PExpr C) {struct e} : PExpr C :=
match e with
  PEadd e1 e2  =>  mkAdd (subst_factor l e1) (subst_factor l e2)
| PEsub e1 e2=>  mkSub (subst_factor l e1) (subst_factor l e2)
| PEopp e1  =>   mkOpp (subst_factor l e1)
| _                 => fst (subst_one_factor e l) 
end.

Definition get_delta := fun e => match split_factors e with
                                                        l1::l => delta l1 l
                                                      | _ => nil
                                                      end.

Fixpoint mkProd (l: (list (PExpr C))) {struct l} : (PExpr C) :=
   match l with 
      nil => (PEc C1)
  | e::nil => e
  | e::l1 => mkMul e (mkProd l1)
  end.

Fixpoint find_trivial_factor (e: PExpr C) (l: list (list (PExpr C))) {struct l}: PExpr C :=
  match l with
     l1::ll2 => let e1 := mkProd l1 in
                     let e2 := simpl C Cplus Cmul Cop C0 C1 isC1 isC0 isPos Cdivide Cdiv (mkSub e e1) in
                     match subst_elem e2 l1 with
                       None => find_trivial_factor e ll2
                     | Some (true, l2) =>  PEmul e2 (mkAdd (mkProd l2) (PEc C1)) 
                     | Some (false, l2) =>   PEmul e2 (mkSub (PEc C1) (mkProd l2))
                     end 
|   _ => (PEmul (PEc C1) e)
    end.

Definition isPC1 := fun x => match x with (PEc c) => (isC1 c) | _ => false end.
Definition isPC0 := fun x => match x with (PEc c) => (isC0 c) | _ => false end.

Fixpoint factor (e:  PExpr C) : PExpr C :=
  let e1 := match e with
     PEmul e1 e2  => PEmul (factor e1) (factor e2)
|     PEadd e1 e2  => PEadd (factor e1) (factor e2)
|     PEsub e1 e2  => PEsub (factor e1) (factor e2)
|     PEopp e1        =>  PEopp (factor e1)  
| _ => e end in
     let e2 := get_delta e1 in
                                   if (isPC1 (mkProd e2)) then
                                     find_trivial_factor e1 (split_factors e1)
                                   else
                                     (PEmul (mkProd e2) (subst_factor e2 e1)).

Definition factor_sub := fun f => 
 let e := match f with
     PEmul e1 e2  => PEmul (factor e1) (factor e2)
|     PEadd e1 e2  => PEadd (factor e1) (factor e2)
|     PEsub e1 e2  => PEsub (factor e1) (factor e2)
|     PEopp e1        =>  PEopp (factor e1)  
| _ => f end in
  match e with
    PEsub e1 e2 =>   
           if (isPC0 e1)  then
               let d1 :=  (get_delta e2) in
                  PEmul (mkProd d1) (PEsub (PEc C0) (subst_factor d1 e2))
          else if (isPC0 e2) then
               let d1 := (get_delta e1) in
                  PEmul (mkProd d1) (PEsub (subst_factor d1 e2) (PEc C0))
         else
               let d := get_delta e in
                  (PEmul (mkProd d) 
                    (PEsub (subst_factor d e1) 
                                       (subst_factor d e2)))
    |  _   => let d := get_delta e in
                  (PEmul (mkProd d) (subst_factor d e))
  end.

Definition factor_sub_val := fun e d1 => 
  let d2 := split_factor d1 in
  match e with
    PEsub e1 e2 =>   
           if (isPC0 e1)  then
                  PEmul d1 (PEsub (PEc C0) (subst_factor d2 e2))
          else if (isPC0 e2) then
                  PEmul d1 (PEsub (subst_factor d2 e2) (PEc C0))
         else
                  (PEmul d1 
                    (PEsub (subst_factor d2 e1) 
                                       (subst_factor d2 e2)))
    |  _   => (PEmul d1 (subst_factor d2 e))
  end.


End PolFactorSimpl.
