(***************************************************************************)
(* Formalization of the Chou, Gao and Zhang's decision procedure.          *)
(* Julien Narboux (Julien@narboux.fr)                                      *)
(* LIX/INRIA FUTURS 2004-2006                                              *)
(* University of Strasbourg 2008                                           *)
(***************************************************************************)

Require Export geometry_tools_lemmas.
Require Export general_tactics.
Require Import List.
Require Import Quote.

Inductive AVars : Type :=  
  | PVar : Point -> AVars
  | FVar : F -> AVars.

Inductive AP : Type := 
  | APvar : nat -> AP.

Inductive AF : Type :=
  | AS : nat -> nat -> nat -> AF
  | AD : nat -> nat -> AF
  | AFvar : nat -> AF
  | AF0 : AF
  | AF1 : AF
  | AFplus : AF -> AF -> AF
  | AFmult : AF -> AF -> AF
  | AFopp : AF -> AF
  | AFinv : AF -> AF.

(* Checks if var is in lvar *)

Ltac List_mem var lvar :=
  match constr:(lvar) with
  | nil => constr:(false)
  | cons ?X1 ?X2 =>
      match constr:(X1 = var) with
      | (?X1 = ?X1) => constr:(true)
      | _ => List_mem var X2
      end
  end.

(* Build the list of variables  *)

Ltac build_var_point_list_aux lvar point :=
     let res := List_mem (PVar point) lvar in
      match constr:(res) with
      | true => lvar
      | false => constr:(cons (PVar point) lvar)
      end.

Ltac build_var_list_aux lvar trm :=
  match constr:(trm) with
  | F0 => lvar
  | F1 => lvar
  | (Fplus ?X1 ?X2) =>
      let l2 := build_var_list_aux lvar X2 in
      build_var_list_aux  l2 X1
  | (Fmult ?X1 ?X2) =>
      let l2 := build_var_list_aux  lvar X2 in
      build_var_list_aux l2 X1
  | (Fopp ?X1) => build_var_list_aux lvar X1
  | (Finv ?X1) => build_var_list_aux lvar X1
  | (S ?X1 ?X2 ?X3) =>  
  let l1 := build_var_point_list_aux lvar X3 in
  let l2 := build_var_point_list_aux l1 X2 in
  build_var_point_list_aux l2 X1
  | (DSeg ?X1 ?X2) => 
  let l1 := build_var_point_list_aux lvar X2 in
  build_var_point_list_aux l1 X1
  | (?X1 = ?X2) => 
  let l2 := build_var_point_list_aux lvar X2 in
  build_var_point_list_aux l2 X1

  | ?X1 =>
    let res := List_mem (FVar X1) lvar in
      match constr:(res) with
      | true => lvar
      | false => constr:(cons (FVar X1) lvar)
      end
  end.

Ltac build_var_list trm :=
  build_var_list_aux (@nil AVars) trm.

Ltac List_assoc elt lst :=
  match constr:(lst) with
  | nil => fail
  | (cons (@pairT AVars nat ?X1 ?X2) ?X3) =>
      match constr:(elt = X1) with
      | (?X1 = ?X1) => constr:(X2)
      | _ => List_assoc elt X3
      end
  end.

Ltac number_aux lvar cpt :=
  match constr:(lvar) with
  | nil => constr:(@nil (prodT AVars nat))
  | cons ?X2 ?X3 =>
      let l2 := number_aux X3 (Datatypes.S cpt) in
      constr:(cons (@pairT  AVars nat X2 cpt) l2)
  end.

Ltac number lvar := number_aux lvar (Datatypes.O).

Ltac build_numbered_var_list trm := let lvar := build_var_list trm in
                             number lvar.

Definition list_assoc_inv :=
  (fix list_assoc_inv_rec (A:Type) (B:Set)
                     (eq_dec:forall e1 e2:B, {e1 = e2} + {e1 <> e2})
                     (lst:list (prodT A B)) {struct lst} :
   B -> A -> A :=
     fun (key:B) (default:A) =>
       match lst with
       | nil => default
       | cons (pairT v e) l =>
           match eq_dec e key with
           | left _ => v
           | right _ => list_assoc_inv_rec A B eq_dec l key default
           end
       end).

(* Interpretation *)
Parameter SomeValue :AVars.
Parameter SomePoint :Point.

Definition interp_AP_to_Point (lvar:list (prodT AVars nat)) (e:nat) : Point :=
 match(list_assoc_inv  AVars nat eq_nat_dec lvar e SomeValue) with
    | PVar p => p
    | _ => SomePoint
  end
.

Fixpoint interp_AF_to_F (lvar:list (prodT AVars nat)) (e:AF) {struct e} : F :=
  match e with
  | AF0 => F0
  | AF1 => F1
  | AS e1 e2 e3 => let idx1 := (interp_AP_to_Point lvar e1) in 
S idx1 (interp_AP_to_Point lvar e2) (interp_AP_to_Point lvar e3)
  | AD e1 e2 => DSeg (interp_AP_to_Point lvar e1) (interp_AP_to_Point lvar e2) 
  | AFplus e1 e2 => Fplus (interp_AF_to_F lvar e1) (interp_AF_to_F lvar e2)
  | AFmult e1 e2 => Fmult (interp_AF_to_F lvar e1) (interp_AF_to_F lvar e2)
  | AFopp e => Fopp (interp_AF_to_F lvar e)
  | AFinv e => Finv (interp_AF_to_F lvar e)
  | AFvar n => 
  match(list_assoc_inv  AVars nat eq_nat_dec lvar n SomeValue) with
    | FVar f => f
    | _ => F0
  end
  end.

(* Metaification *)

Ltac interp_A lvar trm :=
  match constr:(trm) with
  | F0 => constr:(AF0)
  | F1 => constr:(AF1)
  | (Fplus ?X1 ?X2) =>
      let e1 := interp_A lvar X1 with e2 := interp_A lvar X2 in
      constr:(AFplus e1 e2)
  | (Fmult ?X1 ?X2) =>
      let e1 := interp_A lvar X1 with e2 := interp_A lvar X2 in
      constr:(AFmult e1 e2)
  | (Fopp ?X1) =>
      let e := interp_A lvar X1 in
      constr:(AFopp e)
  | (Finv ?X1) => 
      let e := interp_A lvar X1 in
      constr:(AFinv e)
 | (S ?X1 ?X2 ?X3) =>
   let idx1 := List_assoc (PVar X1) lvar with 
   idx2 := List_assoc (PVar X2) lvar with 
   idx3 := List_assoc (PVar X3) lvar in 
   constr:(AS idx1 idx2 idx3)
 | (DSeg ?X1 ?X2) =>
  let idx1 := List_assoc (PVar X1) lvar with
  idx2 := List_assoc (PVar X2) lvar in 
  constr:(AD idx1 idx2)
 | ?X1 => let idx := List_assoc (FVar X1) lvar in
           constr:(AFvar idx)
  end.

Fixpoint nateq (n m:nat) {struct m} : bool :=
  match n, m with
  | O, O => true
  | Datatypes.S n', Datatypes.S m' => nateq n' m'
  | _, _ => false
  end.

Lemma nateq_prop : forall n m:nat, (Is_true (nateq n m))-> n=m.
Proof.
 simple induction n; simple induction m; intros; try contradiction.
  trivial.
  unfold Is_true in H1.
  rewrite (H n1 H1).
  trivial.
Qed.

Fixpoint simplif (e:AF) {struct e} : AF :=
  match e with 
   | AFplus e1 e2 => 
   let s1 := (simplif e1) in 
   let s2 := (simplif e2) in 
   match s1 with 
     AF0 => s2
     |_ => match s2 with 
        AF0 => s1
        |_ =>  AFplus s1 s2
        end
     end
   | AFmult e1 e2 =>
    let s1 := (simplif e1) in 
    let s2 := (simplif e2) in 
    match s1 with 
      AF0 => AF0
      |AF1 => s2
      |_ => match s2 with 
        AF0 => AF0
        |AF1 => s1
        |_ =>  AFmult s1 s2
        end
    end
  | AFopp e =>    
    let s := (simplif e) in 
    match s with 
       AF0 => AF0
       | AFopp e1 => e1
       | _ => AFopp s
    end
  | AS e1 e2 e3 => if (nateq e1 e2) then AF0 else
  (if (nateq e1 e3) then AF0 else (if (nateq e2 e3) then AF0 else e))
  | AD e1 e2 => if (nateq e1 e2) then AF0 else e
  | _ => e
end.

Lemma simplif_correct : 
forall (e:AF) (lvar:list (prodT AVars nat)),
   interp_AF_to_F lvar (simplif e) =
   interp_AF_to_F lvar e.
Proof.
intros.
induction e;trivial;simpl interp_AF_to_F at 2.
simpl.
assert (T:=(nateq_prop n n0)).
destruct (nateq n n0).
replace n with n0.
replace (S (interp_AP_to_Point lvar n0) (interp_AP_to_Point lvar n0)
  (interp_AP_to_Point lvar n1)) with 0;auto;apply trivial_col1.
symmetry;apply T;unfold Is_true;auto.
assert (T2:=(nateq_prop n n1)).
destruct (nateq n n1).
replace n with n1.
replace (S (interp_AP_to_Point lvar n1) (interp_AP_to_Point lvar n0)
  (interp_AP_to_Point lvar n1)) with 0;auto;apply trivial_col3.
symmetry;apply T2;unfold Is_true;auto.
assert (T3:=(nateq_prop n0 n1)).
destruct (nateq n0 n1).
replace n0 with n1.
replace (S (interp_AP_to_Point lvar n) (interp_AP_to_Point lvar n1)
  (interp_AP_to_Point lvar n1)) with 0;auto;apply trivial_col2.
symmetry;apply T3;unfold Is_true;auto.
simpl;auto.
simpl.
assert (T:=(nateq_prop n n0)).
destruct (nateq n n0).
replace n with n0.
apply nuldirseg.
symmetry;apply T;unfold Is_true;auto.
simpl;auto.
rewrite <- IHe1;rewrite <- IHe2;simpl simplif at 1;destruct (simplif e1);destruct (simplif e2);trivial;simpl;ring.
rewrite <- IHe1;rewrite <- IHe2;simpl simplif at 1;destruct (simplif e1);destruct (simplif e2);trivial;simpl;ring.
rewrite <- IHe;simpl simplif at 1;destruct (simplif e);trivial;simpl;ring.
Qed.

Ltac simplif_term exp :=
  let lvar := build_numbered_var_list exp in 
  let trm := interp_A lvar exp in 
  let trm2 :=constr:(interp_AF_to_F lvar (simplif trm)) in 
 (replace exp with trm2 in *;[simpl|rewrite simplif_correct;trivial]).

Ltac Rbasic_simpl := match goal with 
_:_ |- ?X1 = ?X2 => simplif_term X1;simplif_term X2;unfold interp_AP_to_Point;simpl
end.


Fixpoint natle (n m:nat) {struct m} : bool :=
  match n, m with
  | O, O => true
  | O, Datatypes.S n' => true
  | Datatypes.S n', Datatypes.S m' => natle n' m'
  | _, _ => false
  end.

Fixpoint uniformize_areas (e:AF) {struct e} : AF :=
match e with 
  | AFplus e1 e2 => 
    let s1 := (uniformize_areas e1) in 
    let s2 := (uniformize_areas e2) in 
    AFplus s1 s2
  | AFmult e1 e2 =>
    let s1 := (uniformize_areas e1) in 
    let s2 := (uniformize_areas e2) in 
    AFmult s1 s2
  | AFopp e1 =>
    let s1 := (uniformize_areas e1) in 
    AFopp s1
  | AFinv e1 =>
    let s1 := (uniformize_areas e1) in 
    AFinv s1
  | AS e1 e2 e3 => if (natle e1 e2) then 
                                 (if (natle e2 e3) then (AS e1 e2 e3) else 
                                            (if (natle e1 e3)  then  (AFopp (AS e1 e3 e2)) else (AS e3 e1 e2))) 
                               else (if (natle e2 e3) then 
						(if (natle e1 e3) then (AFopp (AS e2 e1 e3)) else (AS e2 e3 e1)) 
					else (AFopp (AS e3 e2 e1))) 
  | AD e1 e2 => if (natle e1 e2) then (AD e1 e2) else  (AFopp (AD e2 e1))
  | _ => e
end.

Lemma uniformize_areas_correct : 
forall (e:AF) (lvar:list (prodT AVars nat)),
   interp_AF_to_F lvar (uniformize_areas e) =
   interp_AF_to_F lvar e.
intros.
induction e;trivial;simpl interp_AF_to_F at 2.
simpl;case (natle n n0);case (natle n0 n1);case (natle n n1);simpl;Geometry.
simpl;case (natle n n0);simpl;symmetry;Geometry.
rewrite <- IHe1;rewrite <- IHe2;simpl uniformize_areas at 1;destruct (uniformize_areas e1);destruct (uniformize_areas e2);trivial;ring.
rewrite <- IHe1;rewrite <- IHe2;simpl uniformize_areas at 1;destruct (uniformize_areas e1);destruct (uniformize_areas e2);trivial;ring.
rewrite <- IHe;simpl uniformize_areas at 1;destruct (uniformize_areas e);trivial;ring.
rewrite <- IHe;simpl uniformize_areas at 1;destruct (uniformize_areas e);trivial;ring.
Qed.

Ltac generalize_all := 
   repeat match goal with
          H:_ |- _ => revert H
end.


Ltac uniformize_term exp lvar :=
  let trm := interp_A lvar exp in 
  let trm2 :=constr:(interp_AF_to_F lvar (uniformize_areas trm)) in
(replace exp with trm2;[idtac|rewrite uniformize_areas_correct;trivial]).

(* This is a metaification to collect the list of all points *)

Inductive formula : Type :=
  | f_imp : formula -> formula -> formula (* binary constructor *)
  | f_const : Prop -> formula (* contructor for constants *).


Inductive formula2 : Type :=
  | f_imp2 : formula2 -> formula2 -> formula2 (* binary constructor *)
  | f_neq : AF -> AF -> formula2 
  | f_eq : AF -> AF -> formula2.

Fixpoint uniformize_areas_formula2 (e:formula2) {struct e} : formula2 :=
match e with 
  | f_imp2 e1 e2 => 
    let s1 := (uniformize_areas_formula2 e1) in 
    let s2 := (uniformize_areas_formula2 e2) in 
    f_imp2 s1 s2
  | f_neq e1 e2 =>
    let s1 := (uniformize_areas e1) in 
    let s2 := (uniformize_areas e2) in 
    f_neq s1 s2
  | f_eq e1 e2 =>
    let s1 := (uniformize_areas e1) in 
    let s2 := (uniformize_areas e2) in 
    f_eq s1 s2
end.

Fixpoint interp_formula2_to_prop (lvar:list (prodT AVars nat)) (e:formula2) {struct e} : Prop :=
  match e with
  | f_imp2 e1 e2 => 
        let s1 := interp_formula2_to_prop lvar e1 in
        let s2 := interp_formula2_to_prop lvar e2 in
      s1 -> s2
  | f_neq e1 e2 => 
        let s1 := interp_AF_to_F lvar e1 in
        let s2 := interp_AF_to_F lvar e2 in
        s1 <> s2
 | f_eq e1 e2 => 
        let s1 := interp_AF_to_F lvar e1 in
        let s2 := interp_AF_to_F lvar e2 in
        s1 = s2
end.

Lemma uniformize_areas_formula2_correct_gen : 
forall (e:formula2) (lvar:list (prodT AVars nat)),
   interp_formula2_to_prop lvar (uniformize_areas_formula2 e) <->
   interp_formula2_to_prop lvar e.
Proof.
intros.
induction e;simpl interp_formula2_to_prop;
repeat rewrite uniformize_areas_correct ;intuition.
Qed.

Lemma uniformize_areas_formula2_correct :
forall (e:formula2) (lvar:list (prodT AVars nat)),
   interp_formula2_to_prop lvar (uniformize_areas_formula2 e) ->
   interp_formula2_to_prop lvar e.
Proof.
intros.
assert 
(   interp_formula2_to_prop lvar (uniformize_areas_formula2 e) <->
   interp_formula2_to_prop lvar e).
apply uniformize_areas_formula2_correct_gen.
intuition.
Qed.

Definition implies := fun A B :Prop => A->B. 
Definition neqF := fun A B : F => A<>B.
Definition eqF := fun A B : F => A=B.

Fixpoint interp_f (f: formula) : Prop :=
   match f with
   | f_imp f1 f2 => implies (interp_f f1) (interp_f f2)
   | f_const c => c
   end.

Ltac put_implies :=
 repeat
 match goal with 
  _:_ |- context [?X1 -> ?X2] => replace (X1 -> X2) with (implies X1 X2);[idtac|auto]
end.

Ltac put_eq_neqF :=
 repeat
 match goal with 
  _:_ |- context [?X1 <> ?X2] => replace (X1 <> X2) with (neqF X1 X2);[idtac|auto]
  |H:context [?X1 <> ?X2] |- _ => replace (X1 <> X2) with (neqF X1 X2) in H;[idtac|auto]
  |_:_ |- context [?X1 = ?X2] => replace (X1 = X2) with (eqF X1 X2);[idtac|auto]
  |H:context [?X1 = ?X2] |- _ => replace (X1 = X2) with (eqF X1 X2) in H;[idtac|auto]

end.



Ltac generalize_all_eq :=
   repeat match goal with
   H: context [?X1 = ?X2] |- _=> revert H
end.

Ltac generalize_all_eq_neqF :=
   repeat match goal with
   H: context [eqF ?X1 ?X2] |- _=> revert H
   | H: context [neqF ?X1 ?X2] |- _=> revert H
 end.

Ltac interp_formula2 lvar trm :=
match constr:(trm) with
  | (implies ?X1 ?X2) =>
      let e1 := interp_formula2 lvar X1 in
      let e2 := interp_formula2 lvar X2 in
      constr:(f_imp2 e1 e2)
 | (eqF ?X1 ?X2) =>
      let e1 := interp_A lvar X1 in
      let e2 := interp_A lvar X2 in
      constr:(f_eq e1 e2)
 | (neqF ?X1 ?X2) =>
     let e1 := interp_A lvar X1 in
     let e2 := interp_A lvar X2 in
     constr:(f_neq e1 e2)
end.

Ltac interp_formula2_goal lvar := 
 match goal with
 _:_ |- ?X1 => interp_formula2 lvar X1
end.

Ltac uniformize_formula2_goal lvar :=
  let trm := interp_formula2_goal lvar in
  let trm2 :=constr:(interp_formula2_to_prop lvar (uniformize_areas_formula2 trm)) in
  let id := fresh in (
assert (id:(trm2-> interp_formula2_to_prop lvar trm));
[apply uniformize_areas_formula2_correct|idtac];
simpl in id;
(* voir problème de changement de nom d'hypothèse
vm_compute in id; *) 
unfold interp_AP_to_Point in id;simpl in id;unfold implies;
apply id;clear id
).
(*
Ltac uniformize_formula2_goal lvar :=
  match goal with
 _:_ |- ?X1 => uniformize_formula2 X1 lvar 
end.
*)
Ltac prepare_goal2 lvar := generalize_all_eq_neqF;put_implies;interp_formula2_goal lvar.

Ltac prepare_goal := generalize_all_eq;put_implies;quote interp_f.
Ltac un_prepare_goal := simpl;unfold implies;intros.

Ltac build_var_list_eq varlist x :=
 match constr:(x) with 
     	?X2=?X3 => 
           let l1 := build_var_list_aux varlist X2 in
   	   let l2 := build_var_list_aux l1 X3 in
           constr:(l2) 
       | ?X2<>?X3 => 
          let l1 := build_var_list_aux varlist X2 in
          let l2 := build_var_list_aux l1 X3 in
          constr:(l2)
   | _ => varlist
end.

Ltac union_vars_aux varlist trm :=  
  match constr:(trm) with
   | interp_f ?X1 => union_vars_aux varlist X1 
   | f_imp ?X1 ?X2 => 
        let lvar1 := union_vars_aux varlist X1 in 
        let lvar2 := union_vars_aux lvar1 X2 in
        constr:(lvar2)
   | f_const ?X1 => build_var_list_eq varlist X1
 end.

Ltac union_vars trm :=  union_vars_aux (@nil AVars) trm .
      
Ltac compute_vars_of_the_goal :=
  match goal with 
  _:_ |- ?X1 => 
        let lvar := union_vars X1 in
        let varlist := number lvar in
       varlist
end.

Ltac uniformize_quantities varlist trm :=
  match constr:(trm) with
   | interp_f ?X1 => uniformize_quantities varlist X1 
   | f_imp ?X1 ?X2 => uniformize_quantities varlist X1;uniformize_quantities varlist X2
   | f_const ?X1 => 
                (match constr:(X1) with 
                    ?X1 = ?X2 => uniformize_term X1 varlist;uniformize_term X2 varlist
                  | ?X1 <> ?X2 => uniformize_term X1 varlist;uniformize_term X2 varlist
                    |_ => idtac
                   end)
   end.

Ltac uniformize_quantities_of_the_goal varlist :=
 match goal with 
  _:_ |- ?XG => uniformize_quantities varlist  XG
end.

Ltac uniformize_quantities_of_all varlist :=
 repeat
  match goal with 
	  _:_ |- context [?X1 = ?X2] => progress uniformize_term X1 varlist
          |_:_ |- context [?X1 = ?X2] => progress uniformize_term X2 varlist
	  |H: context [?X1 <> ?X2] |- _ => progress uniformize_term X1 varlist
          |H: context [?X1 <> ?X2] |- _ => progress uniformize_term X2 varlist
	  |H: context [?X1 = ?X2] |- _ => progress uniformize_term X1 varlist
	  |H: context [?X1 = ?X2] |- _ => progress uniformize_term X2 varlist
end.
(*
Ltac Runiformize_signed_areas := 
  unfold Fminus, Fdiv in *;   
  prepare_goal;
  let varlist := compute_vars_of_the_goal in
 (repeat (progress uniformize_quantities_of_the_goal varlist);un_prepare_goal).
*)
(*
  (uniformize_quantities_of_the_goal varlist;
   unfold interp_AP_to_Point;simpl;
   un_prepare_goal
   ). *)

Ltac Runiformize_signed_areas := 
  unfold Fminus, Fdiv in *;   
  prepare_goal;
  let varlist := compute_vars_of_the_goal in
  (un_prepare_goal; put_eq_neqF;generalize_all_eq_neqF;put_implies;
    uniformize_formula2_goal varlist;intros).

