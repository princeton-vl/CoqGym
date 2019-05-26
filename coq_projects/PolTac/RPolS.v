Require Import Reals.
Require Import PolSBase.
Require Import PolAuxList.
Require Import PolAux.



Definition Rconvert_back (e : PExpr Z) (l : list R) : R :=
   convert_back Z R R0 Rplus Rminus Rmult Ropp Z2R l e.

Definition Rsimpl_minus (e : PExpr Z) :=
    (simpl_minus
      Z Zplus Zmult Z.opp Z0 1%Z is_Z1 is_Z0 is_Zpos is_Zdiv Z.div e).

Definition Rsimpl (e : PExpr Z) :=
    (simpl
      Z Zplus Zmult Z.opp Z0 1%Z is_Z1 is_Z0 is_Zpos is_Zdiv Z.div e).

Ltac
rs term1 term2 :=
let term := constr:(Rminus term1 term2) in
let rfv := FV RCst Rplus Rmult Rminus Ropp term (@nil R) in
let fv := Trev rfv in
let expr1 := mkPolexpr Z RCst Rplus Rmult Rminus Ropp term1 fv in
let expr2 := mkPolexpr Z RCst Rplus Rmult Rminus Ropp term2 fv in
let re := eval vm_compute in (Rsimpl_minus (PEsub expr1 expr2)) in
let expr3 := match re with (PEsub ?X1 _) => X1 end in
let expr4 := match re with (PEsub _ ?X1 ) => X1 end in
let re1 :=  constr:(PEsub expr1 expr3) in
let
 re1' :=
  eval
     unfold
      Rconvert_back, convert_back,  pos_nth,  jump,
         hd,  tl, Z2R, P2R in (Rconvert_back (PEadd re1 expr3) fv) in
let re1'' := eval lazy beta in re1' in
let
 re2' :=
  eval
     unfold
      Rconvert_back, convert_back,  pos_nth,  jump,
         hd,  tl, Z2R, P2R in (Rconvert_back (PEadd re1 expr4) fv) in
let re2'' := eval lazy beta in re2' in
replace2_tac term1 term2 re1'' re2''; [idtac| ring | ring].

Ltac
rpols :=
match goal with
| |- (?X1 = ?X2)%R =>
rs X1 X2; try apply Rplus_eq_compat_l
| |- (?X1 <> ?X2)%R =>
rs X1 X2; apply Rplus_neg_compat_l
| |- Rlt ?X1 ?X2 =>
rs X1 X2; apply Rplus_lt_compat_l
| |- Rgt ?X1 ?X2 =>
rs X1 X2; apply Rplus_gt_compat_l
| |- Rle ?X1 ?X2 =>
rs X1 X2; apply Rplus_le_compat_l
| |- Rge ?X1 ?X2 =>
rs X1 X2; apply Rplus_ge_compat_l
| _ => fail end.

Ltac
hyp_rpols H :=
generalize H;
let tmp := fresh "tmp" in
match (type of H) with
   (?X1 = ?X2)%R =>
rs X1 X2; intros tmp; generalize (Rplus_eq_reg_l _ _ _ tmp); clear H tmp; intro H
|  (?X1 <> ?X2)%nat =>
rs X1 X2; intros tmp; generalize (Rplus_neg_reg_l _ _ _ tmp); clear H tmp; intro H
|  Rlt ?X1 ?X2 =>
rs X1 X2; intros tmp; generalize (Rplus_lt_reg_r _ _ _ tmp); clear H tmp; intro H
|  Rgt ?X1 ?X2 =>
rs X1 X2; intros tmp; generalize (Rplus_gt_reg_l _ _ _ tmp); clear H tmp; intro H
|  Rle ?X1 ?X2 =>
rs X1 X2; intros tmp; generalize (Rplus_le_reg_l _ _ _ tmp); clear H tmp; intro H
|  Rge ?X1 ?X2 =>
rs X1 X2; intros tmp; generalize (Rplus_ge_reg_l _ _ _ tmp); clear H tmp; intro H
| _ => fail end.
