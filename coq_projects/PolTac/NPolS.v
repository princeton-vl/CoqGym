Require Import PolSBase.
Require Import PolAuxList.
Require Import PolAux.
Require Import NAux.
Require Export ArithRing.

Open Scope nat_scope.

Definition Nconvert_back (e : PExpr Z) (l : list N) : N :=
   convert_back Z N 0%N Nplus Nminus Nmult Nopp Z.abs_N l e.
 
Definition Nsimpl_minus (e : PExpr Z) :=
   simpl_minus
    Z Zplus Zmult Z.opp Z0 1%Z is_Z1 is_Z0 is_Zpos is_Zdiv Z.div e.
 
Definition Nsimpl (e : PExpr Z) :=
   simpl
    Z Zplus Zmult Z.opp Z0 1%Z is_Z1 is_Z0 is_Zpos is_Zdiv Z.div e.


Ltac
Ns term1 term2 :=
let term := constr:(Nminus term1 term2) in
let rfv := FV NCst Nplus Nmult Nminus Nopp term (@nil N) in
let fv := Trev rfv in
let expr1 := mkPolexpr Z NCst Nplus Nmult Nminus Nopp term1 fv in
let expr2 := mkPolexpr Z NCst Nplus Nmult Nminus Nopp term2 fv in
let re := eval vm_compute in (Nsimpl_minus (PEsub expr1 expr2)) in
let expr3 := match re with (PEsub ?X1 _) => X1 end in
let expr4 := match re with (PEsub _ ?X1 ) => X1 end in
let re1 := eval vm_compute in (Nsimpl (PEsub expr1 expr3)) in
let
 re1' :=
  eval
     unfold
      Nconvert_back, convert_back,  PolAuxList.pos_nth,  PolAuxList.jump, 
         PolAuxList.hd,  PolAuxList.tl in (Nconvert_back (PEadd re1 expr3) fv) in
let re1'' := eval lazy beta in re1' in
let re1''' := clean_zabs_N re1'' in
let
 re2' :=
  eval
     unfold
      Nconvert_back, convert_back,  PolAuxList.pos_nth,  PolAuxList.jump, 
         PolAuxList.hd,  PolAuxList.tl in (Nconvert_back (PEadd re1 expr4) fv) in
let re2'' := eval lazy beta in re2' in
let re2''' := clean_zabs_N re2'' in
replace2_tac term1 term2 re1''' re2'''; [idtac | ring | ring].
(*
(replace term with re2; [idtac | try ring]).
*)

Ltac
Npols :=
match goal with
| |- (?X1 = ?X2)%N =>
Ns X1 X2; apply Nplus_eq_compat_l
| |- (?X1 <> ?X2)%N =>
Ns X1 X2; apply Nplus_neg_compat_l
| |- (?X1 < ?X2)%N =>
Ns X1 X2; apply Nplus_lt_compat_l
| |- (?X1 > ?X2)%N =>
Ns X1 X2; apply Nplus_gt_compat_l
| |- (?X1 <= ?X2)%N =>
Ns X1 X2; apply Nplus_le_compat_l
| |- (?X1 >= ?X2)%N =>
Ns X1 X2; apply Nplus_ge_compat_l
| _ => fail end.


Ltac
hyp_Npols H :=
generalize H;
let tmp := fresh "tmp" in
match (type of H) with
   (?X1 = ?X2)%N =>
Ns X1 X2; intros tmp; generalize (Nplus_reg_l _ _ _ tmp); clear H tmp; intro H
|  (?X1 <> ?X2)%N =>
Ns X1 X2; intros tmp; generalize (Nplus_neg_reg_l _ _ _ tmp); clear H tmp; intro H
|  (?X1 < ?X2)%N =>
Ns X1 X2; intros tmp; generalize (Nplus_lt_reg_l _ _ _ tmp); clear H tmp; intro H
|  (?X1 > ?X2)%N =>
Ns X1 X2; intros tmp; generalize (Nplus_gt_reg_l _ _ _ tmp); clear H tmp; intro H
|  (?X1 <= ?X2)%N =>
Ns X1 X2; intros tmp; generalize (Nplus_le_reg_l _ _ _ tmp); clear H tmp; intro H
|  (?X1 >= ?X2)%N =>
Ns X1 X2; intros tmp; generalize (Nplus_ge_reg_l _ _ _ tmp); clear H tmp; intro H
| _ => fail end.
