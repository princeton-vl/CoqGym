Require Import ZArith.
Require Import Reals.
Require Import RPolS.
Require Import PolSBase.
Require Import PolFBase.
Require Import PolAux.
Require Import PolAuxList.
Require Import RSignTac.


Definition Rfactor :=
  factor Z Zplus Zmult Z.opp 0%Z 1%Z is_Z1 is_Z0 is_Zpos is_Zdiv Z.div Zgcd.

Definition Rfactor_minus :=
  factor_sub Z Zplus Zmult Z.opp 0%Z 1%Z is_Z1 is_Z0 is_Zpos is_Zdiv Z.div Zgcd.


Ltac Rfactor_term term1 term2 :=
let term := constr:(Rminus term1 term2) in
let rfv := FV RCst Rplus Rmult Rminus Ropp term (@nil R) in
let fv := Trev rfv in
let expr1 := mkPolexpr Z RCst Rplus Rmult Rminus Ropp term1 fv in
let expr2 := mkPolexpr Z RCst Rplus Rmult Rminus Ropp term2 fv in
let re := eval vm_compute in (Rfactor_minus (PEsub expr1 expr2)) in
let factor := match re with (PEmul ?X1 _) => X1 end in
let expr3 := match re with (PEmul _ (PEsub ?X1 _)) => X1 end in
let expr4 := match re with (PEmul _ (PEsub _ ?X1 )) => X1 end in
let
 re1' :=
  eval
     unfold
      Rconvert_back, convert_back,  pos_nth,  jump,
         hd,  tl, Z2R, P2R in (Rconvert_back (PEmul factor expr3) fv) in
let re1'' := eval lazy beta in re1' in
let
 re2' :=
  eval
     unfold
      Rconvert_back, convert_back,  pos_nth,  jump,
         hd,  tl, Z2R, P2R in (Rconvert_back (PEmul factor expr4) fv) in
let re2'' := eval lazy beta in re2' in
replace2_tac term1 term2 re1'' re2''; [idtac| ring | ring].

Ltac rpolf :=
progress (
(try
match goal with
| |- (?X1 = ?X2)%R =>  Rfactor_term X1 X2
| |- (?X1 <> ?X2)%R =>  Rfactor_term X1 X2
| |- Rlt ?X1 ?X2 => Rfactor_term X1 X2
| |- Rgt ?X1 ?X2 =>Rfactor_term X1 X2
| |- Rle ?X1 ?X2 => Rfactor_term X1 X2
| |- Rge ?X1 ?X2 =>Rfactor_term X1 X2
| _ => fail end)); try (rsign_tac); try repeat (rewrite Rmult_1_l || rewrite Rmult_1_r).


Ltac hyp_rpolf H :=
progress (
generalize H;
(try
match type of H with
  (?X1 = ?X2)%R =>  Rfactor_term X1 X2
| (?X1 <> ?X2)%R =>  Rfactor_term X1 X2
| Rlt ?X1 ?X2 => Rfactor_term X1 X2
| Rgt ?X1 ?X2 =>Rfactor_term X1 X2
| Rle ?X1 ?X2 => Rfactor_term X1 X2
| Rge ?X1 ?X2 =>Rfactor_term X1 X2
| _ => fail end)); clear H; intros H; try (hyp_rsign_tac H); try repeat rewrite Rmult_1_l in H.
