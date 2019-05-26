Require Import PolSBase.
Require Import PolAuxList.
Require Import PolAux.
Require Export ArithRing.

Open Scope nat_scope.

Definition Natconvert_back (e : PExpr Z) (l : list nat) : nat :=
   convert_back Z nat 0 plus minus mult Natopp Z.abs_nat l e.
 
Definition Natsimpl_minus (e : PExpr Z) :=
   simpl_minus
    Z Zplus Zmult Z.opp Z0 1%Z is_Z1 is_Z0 is_Zpos is_Zdiv Z.div e.
 
Definition Natsimpl (e : PExpr Z) :=
   simpl
    Z Zplus Zmult Z.opp Z0 1%Z is_Z1 is_Z0 is_Zpos is_Zdiv Z.div e.


Ltac
ns term1 term2 :=
let term := constr:(minus term1 term2) in
let rfv := FV NatCst plus mult minus Natopp term (@nil nat) in
let fv := Trev rfv in
let expr1 := mkPolexpr Z NatCst plus mult minus Natopp term1 fv in
let expr2 := mkPolexpr Z NatCst plus mult minus Natopp term2 fv in
let re := eval vm_compute in (Natsimpl_minus (PEsub expr1 expr2)) in
let expr3 := match re with (PEsub ?X1 _) => X1 end in
let expr4 := match re with (PEsub _ ?X1 ) => X1 end in
let re1 := eval vm_compute in (Natsimpl (PEsub expr1 expr3)) in
let
 re1' :=
  eval
     unfold
      Natconvert_back, convert_back,  PolAuxList.pos_nth,  PolAuxList.jump, 
         PolAuxList.hd,  PolAuxList.tl in (Natconvert_back (PEadd re1 expr3) fv) in
let re1'' := eval lazy beta in re1' in
let re1''' := clean_zabs re1'' in
let
 re2' :=
  eval
     unfold
      Natconvert_back, convert_back,  PolAuxList.pos_nth,  PolAuxList.jump, 
         PolAuxList.hd,  PolAuxList.tl in (Natconvert_back (PEadd re1 expr4) fv) in
let re2'' := eval lazy beta in re2' in
let re2''' := clean_zabs re2'' in
replace2_tac term1 term2 re1''' re2'''; [idtac | ring | ring].
(*
(replace term with re2; [idtac | try ring]).
*)

Ltac
npols :=
match goal with
| |- (?X1 = ?X2)%nat =>
ns X1 X2; apply plus_eq_compat_l
| |- (?X1 <> ?X2)%nat =>
ns X1 X2; apply plus_neg_compat_l
| |- lt ?X1 ?X2 =>
ns X1 X2; apply plus_lt_compat_l
| |- gt ?X1 ?X2 =>
ns X1 X2; apply plus_gt_compat_l
| |- le ?X1 ?X2 =>
ns X1 X2; apply plus_le_compat_l
| |- ge ?X1 ?X2 =>
ns X1 X2; apply plus_ge_compat_l
| _ => fail end.


Ltac
hyp_npols H :=
generalize H;
let tmp := fresh "tmp" in
match (type of H) with
   (?X1 = ?X2)%nat =>
ns X1 X2; intros tmp; generalize (plus_reg_l _ _ _ tmp); clear H tmp; intro H
|  (?X1 <> ?X2)%nat =>
ns X1 X2; intros tmp; generalize (plus_neg_reg_l _ _ _ tmp); clear H tmp; intro H
|  lt ?X1 ?X2 =>
ns X1 X2; intros tmp; generalize (plus_lt_reg_l _ _ _ tmp); clear H tmp; intro H
|  gt ?X1 ?X2 =>
ns X1 X2; intros tmp; generalize (plus_gt_reg_l _ _ _ tmp); clear H tmp; intro H
|  le ?X1 ?X2 =>
ns X1 X2; intros tmp; generalize (plus_le_reg_l _ _ _ tmp); clear H tmp; intro H
|  ge ?X1 ?X2 =>
ns X1 X2; intros tmp; generalize (plus_ge_reg_l _ _ _ tmp); clear H tmp; intro H
| _ => fail end.
