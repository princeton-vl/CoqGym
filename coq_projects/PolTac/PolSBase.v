(* Some code to perform simple simplification over a ring *)

Require Export ZArith.
Require Export List.
Require Import PolAuxList.
 
Section PolSimplBase.

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

(*********************************************************************)
(*                                                                   *)
(*             Auxillary functions on positive                       *)
(*                                                                   *)
(*********************************************************************)


(*   One positive is smaller than another *)
 
Definition le_pos p1 p2 := Zle_bool (Zpos p1) (Zpos p2).

(* Two positives are equal *)
 
Definition eq_pos p1 p2 := Zeq_bool (Zpos p1) (Zpos p2).



(*********************************************************************)
(*                                                                   *)
(*                      Polynomial Expressions                       *)
(*                                                                   *)
(*********************************************************************)
 
Inductive PExpr : Set :=
  PEc: C ->  PExpr
 | PEX: positive ->  PExpr
 | PEadd: PExpr -> PExpr ->  PExpr
 | PEsub: PExpr -> PExpr ->  PExpr
 | PEmul: PExpr -> PExpr ->  PExpr
 | PEopp: PExpr ->  PExpr .

(* Check if a constant is 0 *)
 
Definition isP0 e :=
   match e with PEc c => isC0 c | _ => false end.
(* Check if a constant is 0 *)
 
Definition isP1 e :=
   match e with PEc c => isC1 c | _ => false end.

(* Simplification for mul when 1 or 0 *)

Definition mkPEmulc (c: C) (e: PExpr) := 
  if isC0 c then  PEc C0 else
  if isC1 c then e else
  match e with
     (PEc c1) => PEc (Cmul c c1)
   | (PEopp e1) =>  PEmul (PEc (Cop c)) e1
   | (PEmul (PEc c1) e1)  => PEmul (PEc (Cmul c c1)) e1
   | _ => PEmul (PEc c) e
  end.
 
Definition mkPEmul (e1 e2 : PExpr) := 
   match e1 with
     (PEc c1) => mkPEmulc c1 e2
   | (PEopp e3) => 
                match e2 with
                 (PEc c2) => mkPEmulc (Cop c2) e3
                | (PEmul (PEc c2) e4) => mkPEmulc (Cop c2) (PEmul e3 e4)
                | (PEopp e4) => PEmul e3 e4
                |  _ => PEopp (PEmul e3 e2)
                end
   | (PEmul (PEc c1) e3)  => 
                match e2 with
                 (PEc c2) => mkPEmulc (Cmul c1 c2) e3
                | (PEmul (PEc c2) (PEopp e4)) => mkPEmulc (Cmul c1 c2)
                                                    (PEmul e3 e4)
                | (PEopp e4) => mkPEmulc (Cop c1) (PEmul e3 e4)
                |  _ => mkPEmulc c1 (PEmul e3 e2)
                end
   | _ => 
                match e2 with
                 (PEc c2) => mkPEmulc c2 e1
                | (PEmul (PEc c2) e4) => mkPEmulc c2 (PEmul e1 e4)
                | (PEopp e4) => PEopp (PEmul e1 e4)
                | _ => PEmul e1 e2
                end
   end.

(* Simplification for add when 0 or when to turn it into a substraction *)
 
Definition mkPEadd (e1 e2 : PExpr) :=
   match e1, e2 with
    (PEc c1), (PEc c2) => (PEc (Cplus c1 c2))
  | _, _ => 
   if isP0 e1 then e2
     else if isP0 e2 then e1
            else match e2 with
                   PEmul (PEc c1) e3 =>
                     if isPos c1 then PEadd e1 e2
                       else PEsub e1 (mkPEmul (PEc (Cop c1)) e3)
                  | PEc c1 =>
                      if isPos c1 then PEadd e1 e2 else PEsub e1 (PEc (Cop c1))
                  | _ => PEadd e1 e2
                 end
end.

(* Simplification for opp when double opp and when there is a coefficient *)
 
Definition mkPEopp (e1 : PExpr) :=
   match e1 with
     PEopp e2 => e2
    | PEc c1 => PEc (Cop c1)
    | PEmul (PEc c1) e2 => PEmul (PEc (Cop c1)) e2
    | _ => PEopp e1
   end.

(* Simplification for sub when 0 or when to turn it into an addition *)
 
Definition mkPEsub (e1 e2 : PExpr) :=
  match e1, e2 with
    (PEc c1), (PEc c2) => (PEc (Cplus c1 (Cop c2)))
  | _ , _ => 
   if isP0 e1 then mkPEopp e2
     else if isP0 e2 then e1
            else match e2 with
                   PEmul (PEc c1) e3 =>
                     if isPos c1 then PEsub e1 e2
                       else PEadd e1 (mkPEmul (PEc (Cop c1)) e3)
                  | PEc c1 =>
                      if isPos c1 then PEsub e1 e2 else PEadd e1 (PEc (Cop c1))
                  | _ => PEsub e1 e2
                 end
end.

(*********************************************************************)
(*                                                                   *)
(*     First step of the algorithm:                                  *)
(*     put a constant at the beginning of each sequence of products. *)
(*     These constants play the role of positions                    *)
(*                                                                   *)
(*********************************************************************)

(* Factorize the constant in a product. Always return a product by a constant*)
 
Definition lift_make_mul (e1 e2 : PExpr) : PExpr :=
   match e1 with
     PEc c1 =>
       match e2 with
         PEc c2 => PEc (Cmul c1 c2)
        | PEmul (PEc c2) e4 => PEmul (PEc (Cmul c1 c2)) e4
        | _ => PEmul (PEc c1) e2
       end
    | PEmul (PEc c1) e3 =>
        match e2 with
          PEc c2 => PEmul (PEc (Cmul c1 c2)) e3
         | PEmul (PEc c2) e4 => PEmul (PEc (Cmul c1 c2)) (PEmul e3 e4)
         | _ => PEmul (PEc c1) (PEmul e3 e2)
        end
    | _ =>
        match e2 with
          PEc c2 => PEmul (PEc c2) e1
         | PEmul (PEc c2) e4 => PEmul (PEc c2) (PEmul e1 e4)
         | _ => PEmul (PEc C1) (PEmul e1 e2)
        end
   end.

(* Multiply an expression by the constant 1 if necessary *)
 
Definition list_mult_one e :=
   match e with PEX _ => PEmul (PEc C1) e | _ => e end.
(* Put a product by a constant in top of each list of products *)
 
Fixpoint lift_const (e : PExpr) : PExpr :=
 match e with
   PEadd e1 e2 =>
     PEadd (list_mult_one (lift_const e1)) (list_mult_one (lift_const e2))
  | PEsub e1 e2 =>
      PEsub (list_mult_one (lift_const e1)) (list_mult_one (lift_const e2))
  | PEmul e1 e2 => lift_make_mul (lift_const e1) (lift_const e2)
  | PEopp e1 => PEopp (list_mult_one (lift_const e1))
  | _ => list_mult_one e
 end.

(*********************************************************************)
(*                                                                   *)
(*                        Monomial of Positions                      *)
(*                                                                   *)
(*********************************************************************)

(* Variable of position are encoded by a positive *)
 
Definition pos := positive.

(* Initial pos *)
 
Definition init_pos : pos := 1%positive.

(* Generate a new position from an old one  *)
 
Definition next_pos (p : pos) : pos := (1 + p)%positive.

(* Monomials for positions are encoded by a list  positive *)
 
Definition mon_pos := list pos.

(* Do the product of two monomials of position  *)
 
Definition prod_pos (e1 e2 : mon_pos) : mon_pos := app e1 e2.

(* Check if a variable of position is in a monomial *)
 
Fixpoint pos_in_mon (p : pos) (l : mon_pos) {struct l} : bool :=
 match l with
   nil => false
  | cons p1 l1 => if eq_pos p p1 then true else pos_in_mon p l1
 end.

(* Remove a position from a monomial of positions *)
 
Fixpoint pos_remove (p : pos) (l : mon_pos) {struct l} : mon_pos :=
 match l with
   nil => nil
  | cons p1 l1 => if eq_pos p p1 then l1 else cons p1 (pos_remove p l1)
 end.

(* Insert a variable in an ordered list of position with no repetition *)
 
Fixpoint insert_list_pos (p1 : pos) (l : list pos) {struct l} : list pos :=
 match l with
   nil => cons p1 nil
  | cons p2 l1 =>
      if eq_pos p1 p2 then l
        else if le_pos p1 p2 then cons p1 l else cons p2 (insert_list_pos p1 l1)
 end.

(* Append two ordered list of variable of positions with no repetition *)
 
Definition append_pos (l1 l2 : list pos) : list pos :=
   fold_left (fun l a => insert_list_pos a l) l1 l2.
(* Check if list of positive intersect *)
 
Fixpoint list_pos_intersect (l1 l2 : list pos) {struct l2} : bool :=
 match l2 with
   nil => false
  | cons p1 l3 => if pos_in_mon p1 l1 then true else list_pos_intersect l1 l3
 end.

(*********************************************************************)
(*                                                                   *)
(*                       Monomial of Expressions                     *)
(*                                                                   *)
(*********************************************************************)

(* Variable of expression are encoded by a positive *)

Definition exp := positive.

(* Monomials for expressions are encoded by a list  positive *)
 
Definition mon_exp := list exp.

(* Check if two monomials of expressions are equal *)
 
Fixpoint mon_exp_eq (l1 l2 : mon_exp) {struct l1} : bool :=
 match l1, l2 with
   nil, nil => true
  | cons p1 l3, cons p2 l4 => if eq_pos p1 p2 then mon_exp_eq l3 l4 else false
  | _, _ => false
 end.

(* Insert a variable in a monomial of expression *)
 
Fixpoint insert_exp (p1 : exp) (l : mon_exp) {struct l} : mon_exp :=
 match l with
   nil => cons p1 nil
  | cons p2 l1 => if le_pos p1 p2 then cons p1 l else cons p2 (insert_exp p1 l1)
 end.

(* Do the product of two monomials of expression *)
 
Definition prod_exp (l1 l2 : mon_exp) : mon_exp :=
   fold_left (fun l a => insert_exp a l) l1 l2.

(* An environment associates a value to each position *)
 
Definition env := (list (pos * C))%type.

(* Empty environment *)
 
Definition empty_env : env := nil.

(* Add an element in an enviroment *)
 
Definition add_env n c e : env := cons (n, c) e.

(* Check if the variable is bound in an environment
   Check if a position is bounded in an environment *)
 
Fixpoint is_bound_env (n : pos) (e : env) {struct e} : bool :=
 match e with
   nil => false
  | cons ((n1, c)) e1 => if eq_pos n n1 then true else is_bound_env n e1
 end.

(* The number of times a position is associated to zero in an environment*)
 
Fixpoint number_of_zero_env (e : env) : Z :=
 match e with
   nil => 0%Z
  | cons ((n1, c)) e1 =>
      if isC0 c then (1 + number_of_zero_env e1)%Z else number_of_zero_env e1
 end.

(* Get the value of a position in an  enviroment*)
 
Fixpoint value_env (n : pos) (e : env) {struct e} : C :=
 match e with
   nil => C0
  | cons ((n1, c)) e1 => if eq_pos n n1 then c else value_env n e1
 end.

(* Update  the value of a position in an  enviroment*)
 
Fixpoint update_env (n : pos) (c : C) (e : env) {struct e} : env :=
 match e with
   nil => cons (n, c) nil
  | cons ((n1, c1)) e1 =>
      if eq_pos n n1 then cons (n, c) e1 else cons (n1, c1) (update_env n c e1)
 end.

(* Merge two environments *)
 
Definition merge_env (e1 e2 : env) : env :=
   fold_left (fun env x =>
                 match x with (y, val) => update_env y val env end) e1 e2.

(* Restrict an environment with respect a list of position *)
 
Let restrict_env (l : list pos) (e : env) : env :=
   map (fun x => (x, value_env x e)) l.

(* The number of equal associations between two environments*)
 
Fixpoint number_of_equality_env (e1 e2 : env) {struct e1} : Z :=
 match e1 with
   nil => 0%Z
  | cons ((n1, c)) e3 =>
(*      if isC0 (Cplus c (Cop (value_env n1 e2))) *)
      if isC0 c then number_of_equality_env e3 e2
      else if isC0 (value_env n1 e2) then number_of_equality_env e3 e2
      else if isPos (Cmul c (value_env n1 e2))
        then (1 + number_of_equality_env e3 e2)%Z
        else number_of_equality_env e3 e2
 end.

(*********************************************************************)
(*                                                                   *)
(*                        Monomial                                   *)
(*                                                                   *)
(*********************************************************************)

(* Definition of a monomial composed of a position part and an  *)
(* expression part                                              *)
 
Definition mon := ((C * mon_pos) * mon_exp)%type.

(* Get the positions information of a monomial *)
 
Definition get_pos (m : mon) := fst m.

(* Get the expression information of a monomial *)
 
Definition get_exp (m : mon) := snd m.

(* Create a monomial with an empty monomial expression *)
 
Definition make_const_mon n : list mon := cons ((C1, cons n nil), nil) nil.

(* Create a monomial with an empty position *)
 
Definition make_exp_mon x : list mon := cons ((C1, nil), cons x nil) nil.

(* The opposite of a monomial *)
 
Definition opp_mon (m : mon) : mon :=
   match m with
     ((c, l1), l2) => ((Cop c, l1), l2)
   end.

(* Product of two monomials *)
 
Definition prod_mon (m1 m2 : mon) : mon :=
   match m1, m2 with
     ((c1, l1), l2), ((c2, l3), l4) =>
       ((Cmul c1 c2, prod_pos l1 l3), prod_exp l2 l4)
   end.

(* Distribute a monomial inside a list of monomials *)
 
Definition insert_mon (m : mon) (l : list mon) : list mon := map (prod_mon m) l.
(* Do the product of two list of monomials *)
 
Definition app_mon (l1 l2 : list mon) : list mon :=
   flat_map (fun x => insert_mon x l1) l2.

(*********************************************************************)
(*                                                                   *)
(*    Second step of the algorithm:                                  *)
(*    generate the list of all monomials by applying distributivity. *)
(*    The constant at the beginning of each product are replaced by  *)
(*    variable of position                                           *)
(*********************************************************************)

(* The result of creating the list of monomials:                    *)
(*   the list of monomials                                          *)
(*   an environment that associates variable of positions to their  *)
(*       initial value  the position counter                        *)
 
Definition list_res := ((list mon * env) * pos)%type.

(*Get the list of monomials from a result *)
 
Definition list_get_list (r : list_res) : list mon := fst (fst r).

(* Get the default value of the positions *)
 
Definition list_get_env (e : list_res) :=
   match e with ((_, e), _) => e end.

(* Get the number of positions that are generated *)
 
Definition list_get_pos (e : list_res) : pos :=
   match e with ((_, _), n) => n end.

(* Create a result *)
 
Definition make_list_res l e n : list_res := ((l, e), n).

(* Create the list of monomials *)
 
Fixpoint make_list (p : PExpr) (e : env) (n : pos) {struct p} : list_res :=
 match p with
   PEc c => make_list_res (make_const_mon n) (add_env n c e) (next_pos n)
  | PEX x => make_list_res (make_exp_mon x) e n
  | PEopp p1 =>
      let r1 := make_list p1 e n in
        make_list_res
         (map opp_mon (list_get_list r1)) (list_get_env r1) (list_get_pos r1)
  | PEadd p1 p2 =>
      let r1 := make_list p1 e n in
        let r2 := make_list p2 (list_get_env r1) (list_get_pos r1) in
          make_list_res
           (app (list_get_list r1) (list_get_list r2)) (list_get_env r2)
           (list_get_pos r2)
  | PEsub p1 p2 =>
      let r1 := make_list p1 e n in
        let r2 := make_list p2 (list_get_env r1) (list_get_pos r1) in
          make_list_res
           (app (list_get_list r1) (map opp_mon (list_get_list r2)))
           (list_get_env r2) (list_get_pos r2)
  | PEmul p1 p2 =>
      let r1 := make_list p1 e n in
        let r2 := make_list p2 (list_get_env r1) (list_get_pos r1) in
          make_list_res
           (app_mon (list_get_list r1) (list_get_list r2)) (list_get_env r2)
           (list_get_pos r2)
 end.

(*********************************************************************)
(*                                                                   *)
(*     Third step of the algorithm:                                  *)
(*     regroup the list of monomial by monomials of expressions.     *)
(*                                                                   *)
(*********************************************************************)

(* A factor is a constant multiplied by a monomial of position *)
 
Definition factor := (C * mon_pos)%type.

(* Get the list of positions that appear in a list of factors *)
 
Definition factor_pos (l : list factor) : list pos :=
   fold_left (fun l a => append_pos (snd a) l) l nil.

(* Eval a list of factors *)
 
Fixpoint eval_factors (e : env) (eq : list factor) {struct eq} : C :=
 match eq with
   nil => C0
  | cons ((c, l1)) eq1 =>
      Cplus
       (Cmul c (fold_left (fun a b => Cmul a (value_env b e)) l1 C1))
       (eval_factors e eq1)
 end.

(* A group is composed of the monomial expression and it is *)
(* associated list of factor                                *)
 
Definition group := (mon_exp * list factor)%type.

(* Create a group *)
 
Definition make_group e1 e2 : group := (e1, e2).

(* Add a monomial in a list of groups *)
 
Fixpoint add_groups (m : mon) (l : list group) {struct l} : list group :=
 match l with
   nil => cons (make_group (get_exp m) (cons (get_pos m) nil)) nil
  | cons ((e, p)) l1 =>
      if mon_exp_eq e (get_exp m) then cons (e, cons (get_pos m) p) l1
        else cons (e, p) (add_groups m l1)
 end.

(* Convert a list of monomials into a list of groups *)
 
Definition make_groups (l : list mon) : list group :=
   fold_left (fun l a => add_groups a l) l nil.

(**********************************************************************)
(*                                                                    *)
(*      Forth step of the algorithm:                                  *)
(*      turn groups into a system, composed of subsystems with        *)
(*      related equations, so we can resolve subsystems independantly *)
(*                                                                    *)
(**********************************************************************)

(* Define an equation as a constant associated to a list of factors *)
 
Definition equation := (C * list factor)%type.

(* Create an equation *)
 
Definition make_equation (c : C) (f : list factor) : equation := (c, f).

(* Get the constant in an equation *)
 
Definition get_const (f : equation) : C := fst f.

(* Get the factors *)
 
Definition get_factors (f : equation) : list factor := snd f.

(* A system is composed of a list of associated positions and list of  *)
(*   equations                                                         *)
 
Definition system := list (list pos * list equation).
 
Fixpoint add_equation_to_system_aux
 (l : list pos) (f : list equation) (s : system) {struct s} : system :=
 match s with
   nil => cons (l,f) nil
  | cons ((l1, f1)) s1 =>
      if list_pos_intersect l l1 
        then add_equation_to_system_aux 
               (append_pos l l1) (app f f1) s1
        else cons (l1, f1) (add_equation_to_system_aux l f s1)
 end.

Definition add_equation_to_system (l : list pos) (f : equation) (s : system)
                                 : system :=
  add_equation_to_system_aux l (cons f nil) s.

(* Create a system *)
 
Fixpoint make_system (e : env) (l : list group) {struct l} : system :=
 match l with
   nil => nil
  | cons ((_, f)) l1 =>
      add_equation_to_system
       (factor_pos f) (make_equation (eval_factors e f) f) (make_system e l1)
 end.

(************************************************************************)
(*                                                                      *)
(*     Forth step of the algorithm:                                     *)
(*     try to solve the different subsystem                             *)
(*                                                                      *)
(************************************************************************)

(* Substitute a position p with a value c  in the equation is l = cumul,*)
(*   to get a new equation                                              *)
 
Fixpoint pos_subst (p : pos) (c : C) (cumul : C) (l : list factor) {struct l} :
 equation :=
 match l with
   nil => (cumul, nil)
  | cons ((c1, l1)) l2 =>
      if pos_in_mon p l1
        then if isC0 (Cmul c c1) then pos_subst p c cumul l2
               else match pos_remove p l1 with
                      nil => pos_subst p c (Cplus cumul (Cop (Cmul c c1))) l2
                     | cons x y =>
                         let r1 := pos_subst p c cumul l2 in
                           (fst r1, cons (Cmul c c1, cons x y) (snd r1))
                    end else let r1 := pos_subst p c cumul l2 in
                               (fst r1, cons (c1, l1) (snd r1))
 end.

 
Definition update_res := option (equation * option (pos * C)).

(* Update an equation if impossible return None, otherwise the new equation *)
(*  and a possible propagation                                              *)
 
Definition update_equation (p : pos) (c : C) (e : equation) : update_res :=
   match pos_subst p c (get_const e) (get_factors e) with
     (c1, nil) => if isC0 c1 then Some ((c1, nil), None) else None
    | (c1, cons ((c2, cons p1 nil)) nil) =>
        if Cdivide c2 c1 then Some ((C0, nil), Some (p1, Cdiv c1 c2)) else None
    | (c1, cons ((c2, l1)) nil) =>
        if Cdivide c2 c1 then Some ((c1, cons (c2, l1) nil), None) else None
    | (c1, l1) => Some ((c1, l1), None)
   end.

(* Result of an update of equations*)
 
Definition updates_res := option (list equation * list (positive * C)).
 
Definition list_of_option (e : option (positive * C)) :=
   match e with None => nil | Some e => cons e nil end.
 
Definition ocons := fun (x: equation) y =>
  match x with (_, nil) => y | _ => (cons x y) end.

Fixpoint update_equations (p : pos) (c : C) (l : list equation) {struct l} :
 updates_res :=
 match l with
   nil => Some (nil, nil)
  | cons eq l1 =>
      match update_equation p c eq with
        None => None
       | Some ((eq1, v1)) =>
           match update_equations p c l1 with
             None => None
            | Some ((l2, l3)) => Some (ocons eq1 l2, app (list_of_option v1) l3)
           end
      end
 end.

(* Result of the propagation of an update of equations,  *)
(* we use a natural to get the fixpoint behaviour        *)
 
Definition propagate_res := option (list equation * env).
 
Fixpoint propagate (n : nat) (p : pos) (c : C) (e : env) (l : list equation)
                   {struct n} : propagate_res :=
 match update_equations p c l with
   None => None
  | Some ((l1, nil)) => Some (l1, update_env p c e)
  | Some ((l1, l2)) =>
      match n with
        0 => None
       | S n1 =>
           fold_left
            (fun res a =>
                match res with
                  None => None
                 | Some ((l1, e1)) => propagate n1 (fst a) (snd a) e1 l1
                end) l2 (Some (l1, update_env p c e))
      end
 end.

(* A candidat is a solution to a subsystem with it is associated      *)
(* weight. The weight is used to decide with candidat is the best one *)
 
Definition candidat := option ((Z * Z) * env).
(* Get the best of two candidats*)
 
Definition get_best (c1 c2 : candidat) : candidat :=
   match c1 with
     None => c2
    | Some (((i1, j1), _)) =>
        match c2 with
          None => c1
         | Some (((i2, j2), _)) =>
             if Zeq_bool i1 i2 then if Zle_bool j2 j1 then c1 else c2
               else if Zle_bool i1 i2 then c2 else c1
        end
   end.

(* Check if a better solution is possible  *)
 
Definition is_possible (best : candidat) (e : env) (vars : list pos) : bool :=
   match best with
     None => true
    | Some (((i1, j1), _)) => Zeq_bool i1 (number_of_zero_env e + Zlength vars)
   end.
 
Definition make_candidat (init_e e : env) : candidat :=
   Some ((number_of_zero_env e, number_of_equality_env e init_e), e).


(* Try a find a solution using a backtracking algorithm        *)
(* that takes the first variable in a list and tries to assign *)
(* it to 0 or to its initial value or leaves it unassigned     *)
 
Fixpoint search_best_aux (best : candidat) (n: nat) (init_e e : env) (l : list equation)
                         (vars : list pos)  {struct vars} : candidat :=
 if is_possible best e vars
   then match vars with
          nil => match l with nil => get_best best (make_candidat init_e e)
                    | _ => best
                    end
        | cons x vars1 =>
             if is_bound_env x e then search_best_aux best n init_e e l vars1
               else let best1 :=
                     match propagate n x C0 e l with
                       None => best
                      | Some ((l1, e1)) =>
                          search_best_aux best n init_e e1 l1 vars1
                     end in
                      let best2 :=
                       match propagate n x (value_env x init_e) e l
                        with
                         None => best
                        | Some ((l1, e1)) =>
                            search_best_aux best1 n init_e e1 l1 vars1
                       end in
                        search_best_aux best2 n init_e e l vars1
        end else best.
 
Definition search_best (init_e : env) (s : system) : env :=
   flat_map
    (fun x =>
        match x with
          (vars, eqs) =>
            match search_best_aux None  (S (length vars)) (restrict_env vars init_e) nil eqs vars
             with None => nil | Some ((_, e)) => e end
        end) s.

(**********************************************************************)
(*                                                                    *)
(*    Last step of the algorithm:                                     *)
(*    put back the new values of positions into the expression        *)
(*    to get the new expression                                       *)
(*                                                                    *)
(**********************************************************************)
 
Fixpoint make_PExpr_aux (p : PExpr) (e : env) (n : pos) {struct p} :
 (PExpr * pos)%type :=
 match p with
   PEc c => (PEc (value_env n e), next_pos n)
  | PEX x => (p, n)
  | PEopp p1 => let (fr1,sr1) := make_PExpr_aux p1 e n in
                  (mkPEopp fr1, sr1)
  | PEadd p1 p2 =>
      let (fr1, sr1) := make_PExpr_aux p1 e n in
        let (fr2, sr2) := make_PExpr_aux p2 e sr1 in
          (mkPEadd fr1 fr2, sr2)
  | PEsub p1 p2 =>
      let (fr1, sr1) := make_PExpr_aux p1 e n in
        let (fr2, sr2) := make_PExpr_aux p2 e sr1 in
          (mkPEsub fr1 fr2, sr2)
  | PEmul p1 p2 =>
      let (fr1, sr1) := make_PExpr_aux p1 e n in
        let (fr2, sr2) := make_PExpr_aux p2 e sr1 in
          (mkPEmul fr1 fr2, sr2)
 end.
 
Definition make_PExpr (p : PExpr) (e : env) :=
   fst (make_PExpr_aux p e init_pos).

(* Ensure that the top minus is preserved *)
 
Definition make_PExpr_minus (p : PExpr) (e : env) :=
   fst match p with
         PEsub p1 p2 =>
           let r1 := make_PExpr_aux p1 e init_pos in
             let r2 := make_PExpr_aux p2 e (snd r1) in
               (PEsub (fst r1) (fst r2), snd r2)
        | _ => make_PExpr_aux p e init_pos
       end.

(*********************************************************************)
(*                                                                   *)
(*      Put everything together                                      *)
(*                                                                   *)
(*********************************************************************)
 
Definition simpl (e : PExpr) : PExpr :=
   let exp := lift_const e in
     let res := make_list exp empty_env init_pos in
       make_PExpr
        exp
        (search_best
          (list_get_env res)
          (make_system (list_get_env res) (make_groups (list_get_list res)))).

(* Ensure that the top minus is preserved *)
 
Definition simpl_minus (e : PExpr) :=
   let exp := lift_const e in
     let res := make_list exp empty_env init_pos in
       make_PExpr_minus
        exp
        (search_best
          (list_get_env res)
          (make_system (list_get_env res) (make_groups (list_get_list res)))).

(*********************************************************************)
(*                                                                   *)
(*                          Interfaces                               *)
(*                                                                   *)
(*********************************************************************)
 
Fixpoint convert_back (F : Set) (f : F) (Fadd Fsub Fmult : F -> F ->  F)
                      (Fop : F ->  F) (C2F : C ->  F) (l : list F) (e : PExpr)
                      {struct e} : F :=
 match e with
   PEc c => C2F c
  | PEX x => pos_nth f x l
  | PEopp e1 => Fop (convert_back F f Fadd Fsub Fmult Fop C2F l e1)
  | PEadd e1 e2 =>
      Fadd
       (convert_back F f Fadd Fsub Fmult Fop C2F l e1)
       (convert_back F f Fadd Fsub Fmult Fop C2F l e2)
  | PEsub e1 e2 =>
      Fsub
       (convert_back F f Fadd Fsub Fmult Fop C2F l e1)
       (convert_back F f Fadd Fsub Fmult Fop C2F l e2)
  | PEmul e1 e2 =>
      Fmult
       (convert_back F f Fadd Fsub Fmult Fop C2F l e1)
       (convert_back F f Fadd Fsub Fmult Fop C2F l e2)
 end.

End PolSimplBase.

Arguments PEc [C].
Arguments PEX [C].
Arguments PEadd [C].
Arguments PEsub [C].
Arguments PEmul [C].
Arguments PEopp [C].


(* Code taken from Ring *)

(* Path to handle evar 
Ltac IN a l :=
 match l with
 | (cons a ?l) => constr:true
 | (cons _ ?l) => IN a l
 |  nil => constr:false
 end.
*)

Ltac term_eq t1 t2 :=
  constr:(ltac:(first[constr_eq t1 t2; exact true| exact false])).

Ltac IN a l :=
 match l with
 | (cons ?b ?l1) => 
    let t := term_eq a b in
    match t with
    true => constr:(true)
    | _ => IN a l1
    end
 |  nil => false
 end.

Ltac AddFv a l :=
 match (IN a l) with
 | true => constr:(l)
 | _ => constr:(cons a l)
 end.

Ltac Find_at a l :=
 match l with
 | nil  => constr:(xH)
 | (cons ?b ?l) => 
     let t := term_eq a b in
     match t with
     | true =>  constr:(xH)
     | false => let p := Find_at a l in eval compute in (Pos.succ p)
     end
 end.
		      
Ltac FV Cst add mul sub opp t fv :=
 let rec TFV t fv :=
  match t with
  | (add ?t1 ?t2) => 
    let fv1 := TFV t1 fv in let fv2 := TFV t2 fv1 in constr:(fv2)
  | (mul ?t1 ?t2) => 
    let fv1 := TFV t1 fv in let fv2 := TFV t2 fv1 in constr:(fv2)
  | (sub ?t1 ?t2) => 
    let fv1 := TFV t1 fv in let fv2 := TFV t2 fv1 in constr:(fv2)
  | (opp ?t1) => 
    let fv1 := TFV t1 fv in constr:(fv1)
  | _ =>  
    match Cst t with
    | false => let fv1 := AddFv t fv in constr:(fv1)
    | _ => constr:(fv)
    end
  end 
 in TFV t fv.

 Ltac mkPolexpr T Cst add mul sub opp t fv := 
 let rec mkP t :=
 match Cst t with
    | false => 
       match t with 
        | (add ?t1 ?t2) => 
          let e1 := mkP t1 in
          let e2 := mkP t2 in constr:(PEadd e1 e2)
        | (mul ?t1 ?t2) => 
          let e1 := mkP t1 in
          let e2 := mkP t2 in constr:(PEmul e1 e2)
        | (sub ?t1 ?t2) => 
          let e1 := mkP t1 in
          let e2 := mkP t2 in constr:(PEsub e1 e2)
        | (opp ?t1) =>
          let e1 := mkP t1 in constr:(PEopp e1)
        | _ => let p := Find_at t fv in constr:(@PEX T p)
        end
    | ?c => constr:(PEc c)
  end
  in mkP t.

