Require Import Arith.
Require Import PolSBase.


Section PolReplaceBase.

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


Let mkMul := mkPEmul C Cmul Cop C0 isC1 isC0.
Let mkOpp := mkPEopp  C Cop.
Let mkAdd := mkPEadd C Cplus Cmul Cop C0 isC1 isC0 isPos.
Let mkSub := mkPEsub C Cplus Cmul Cop C0 isC1 isC0 isPos.
Let mkAdd0 e1 e2 := if isP0 _ isC0 e1 then e2 else PEadd e1 e2.
Let mkSub0 e1 e2 := if isP0 _ isC0 e1 then (PEopp e2) else PEsub e1 e2.

(* Test if the difference of two terms is zero *)
Definition is_replace_eq :=  fun x y => 
  let r :=  simpl_minus C Cplus Cmul Cop C0 C1 isC1 isC0 isPos Cdivide Cdiv (PEsub y x) in
   match r with
     PEsub (PEc c) r1  => if (isC0 c) then true else false
  |  _          => false
  end.


Definition replace_eq :=  fun x y z => 
  let r :=  simpl_minus C Cplus Cmul Cop C0 C1 isC1 isC0 isPos Cdivide Cdiv (PEsub y x) in
   match r with
     PEsub (PEc c) r1  => if (isC0 c) then (Some (mkAdd0 r1 z)) else None
  |  _          => None
  end.

(* Test if the sum of two term is zero *)

Definition is_replace_op :=  fun x y => 
  let r :=  simpl_minus C Cplus Cmul Cop C0 C1 isC1 isC0 isPos Cdivide Cdiv (PEsub (PEopp y) x) in
   match r with
     PEsub (PEc c) r1  => if (isC0 c) then true else false
  |  _          => false
  end.

Definition replace_op :=  fun x y z => 
  let r :=  simpl_minus C Cplus Cmul Cop C0 C1 isC1 isC0 isPos Cdivide Cdiv (PEsub (PEopp y) x) in
   match r with
     PEsub (PEc c) r1  => if (isC0 c) then (Some (mkSub0 r1 z)) else None
  |  _          => None
  end.

Definition is_replace_eq_or_op :=
   fun x y => 
         match (is_replace_eq x y) with true => true | _ => is_replace_op x y end.

Definition replace_eq_or_op :=
   fun x y  z=> 
         match (replace_eq x y z) with Some r => Some r| _ => replace_op x y z end.

Definition bool_nat:= fun x => match x with true => 1%nat | false => 0 %nat end.
 
(* Count the number of possible replacement *)
Fixpoint bcount_replace  (b: bool) (e from: PExpr C) {struct e}: nat  :=
 let (b1, n) := if b then (b,0) else
                 if is_replace_eq_or_op  e from then (true, 1) else (true, 0)
          in
          n + 
          match e with
               PEadd e1 e2  =>  
                 bcount_replace b1 e1 from + bcount_replace b1 e2 from
            | PEsub e1 e2  =>  
                 bcount_replace b1 e1 from + bcount_replace b1 e2 from
             | PEopp e1        =>
                bcount_replace b1 e1 from
            | PEmul e1 e2  =>  
                 bcount_replace false e1 from + bcount_replace false e2 from
            | _ => 0
            end.

Definition count_replace :=  bcount_replace false.

(* Return the replaced term  *)
Fixpoint replace_aux (b: bool) (l: list bool) (e from to: PExpr C) {struct e}: list bool * PExpr C :=
  let v := replace_eq_or_op e from to in
  let b1 := if b then b else if  v then true else false in
  let b2 := if b then false else if b1 then (nth 0 l false) else false in
  let ll := if b then l else if  b1 then tail l else l in
  let el := match v with (Some v1) => v1 | None => e end in
            match e with
               PEadd e1 e2  =>  
                 let (l1,e3) := replace_aux b1 ll e1 from to in 
                 let (l2,e4) := replace_aux b1 l1 e2 from to in
                   (l2, if b2 then el else PEadd e3 e4)
            | PEsub e1 e2  =>  
                let (l1,e3) := replace_aux b1 ll e1 from to in 
                 let (l2,e4) := replace_aux b1 l1 e2 from to in
                   (l2, if b2 then el else PEsub e3 e4)
            | PEopp e1        =>
               let (l1,e3) := replace_aux b1 ll e1 from to in 
                   (l1, if b2 then el else PEopp e3)
            | PEmul e1 e2  =>  
                let (l1,e3) := replace_aux false ll e1 from to in 
                 let (l2,e4) := replace_aux false l1 e2 from to in
                   (l2, if b2 then el else PEmul e3 e4)
            | _ => (ll, if b2 then el else e)
            end.

Fixpoint make_all_const (b: bool) (n:nat) {struct n}: list bool :=
match n with 0 => nil | (S n1) => b::make_all_const b n1 end.

Fixpoint make_one_true  (n1 n2:nat)  {struct n1}: list bool :=
match n1, n2 with O, _ => nil 
   | S n3, O => true::make_all_const false n3  
   | S n3, S n4 => false::make_one_true n3 n4 
 end.

Definition replace (e from to: PExpr C) (n: Z) := 
  let c := count_replace e from in
  let l :=
    match n with
      Z0 => make_all_const true c
   | Zpos n1 => make_one_true c  (pred (nat_of_P n1))
   | Zneg n1 => if (Zlt_bool (Z_of_nat c) n) 
                          then make_all_const false c 
                          else make_one_true c (c - (nat_of_P n1))%nat
    end
    in
     snd (replace_aux false l e from to).


End PolReplaceBase.

