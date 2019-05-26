Require Import List.
Require Import ZArith.

Section AUXLIST.

 Variable A:Set.
 Variable default:A.


 Definition hd l := match l with hd :: _ => hd | _ => default end. 

 Definition tl (l: list A) := match l with _ :: tl => tl | _ => nil end. 

 Fixpoint jump (p:positive) (l:list A) {struct p} : (list A) :=
  match p with
  | xH => tl l
  | xO p => jump p (jump p l)
  | xI p  => jump p (jump p (tl l))
  end.

 Fixpoint pos_nth (p:positive) (l:list A) {struct p} : A:=
  match p with
  | xH => hd l
  | xO p => pos_nth p (jump p l)
  | xI p => pos_nth p (jump p (tl l))
  end. 

End AUXLIST.

Arguments pos_nth [A] _ _ _.

 Ltac Trev l :=  
  let rec rev_append rev l :=
   match l with
   |  nil  => constr:(rev)
   | (cons ?h ?t) => let rev := constr:(cons h rev) in rev_append rev t 
   end in
 match type of l with
  (list ?X) => rev_append (@nil X) l
 end.

