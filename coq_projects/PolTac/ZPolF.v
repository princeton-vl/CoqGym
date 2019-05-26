Require Import ZArith.
Require Import ZPolS.
Require Import PolSBase.
Require Import PolFBase.
Require Import PolAux.
Require Import PolAuxList.
Require Import ZSignTac.


Definition Zfactor := 
  factor Z Zplus Zmult Z.opp 0%Z 1%Z is_Z1 is_Z0 is_Zpos is_Zdiv Z.div Zgcd.

Definition Zfactor_minus := 
  factor_sub Z Zplus Zmult Z.opp 0%Z 1%Z is_Z1 is_Z0 is_Zpos is_Zdiv Z.div Zgcd.

Definition Zget_delta := 
 get_delta Z Zplus Zmult Z.opp 0%Z 1%Z is_Z1 is_Z0 is_Zpos is_Zdiv Z.div Zgcd.

Ltac
Zfactor_term term1 term2 :=
let term := constr:(Zminus term1 term2) in
let rfv := FV ZCst Zplus Zmult Zminus Z.opp term (@nil Z) in
let fv := Trev rfv in
let expr1 := mkPolexpr Z ZCst Zplus Zmult Zminus Z.opp term1 fv in
let expr2 := mkPolexpr Z ZCst Zplus Zmult Zminus Z.opp term2 fv in
let re := eval vm_compute in (Zfactor_minus (PEsub expr1 expr2)) in
let factor := match re with (PEmul ?X1 _) => X1 end in
let expr3 := match re with (PEmul _ (PEsub ?X1 _)) => X1 end in
let expr4 := match re with (PEmul _ (PEsub _ ?X1 )) => X1 end in
let
 re1' :=
  eval
     unfold
      Zconvert_back, convert_back,  pos_nth,  jump, 
         hd,  tl in (Zconvert_back (PEmul factor expr3) fv) in
let re1'' := eval lazy beta in re1' in
let
 re2' :=
  eval
     unfold
      Zconvert_back, convert_back,  pos_nth,  jump, 
         hd,  tl in (Zconvert_back (PEmul factor expr4) fv) in
let re2'' := eval lazy beta in re2' in 
replace2_tac term1 term2 re1'' re2''; [idtac| ring | ring].

Ltac zpolf :=
(* progress *) (
(try 
match goal with
| |- (?X1 = ?X2)%Z =>  Zfactor_term X1 X2 
| |- (?X1 <> ?X2)%Z =>  Zfactor_term X1 X2 
| |- Z.lt ?X1 ?X2 => Zfactor_term X1 X2
| |- Z.gt ?X1 ?X2 =>Zfactor_term X1 X2
| |- Z.le ?X1 ?X2 => Zfactor_term X1 X2
| |- Z.ge ?X1 ?X2 =>Zfactor_term X1 X2
| _ => fail end));  try (zsign_tac); try repeat (rewrite Zmult_1_l || rewrite Zmult_1_r).

Ltac hyp_zpolf H := 
progress (
generalize H; 
(try 
match type of H with
  (?X1 = ?X2)%Z =>  Zfactor_term X1 X2 
| (?X1 <> ?X2)%Z =>  Zfactor_term X1 X2 
| Z.lt ?X1 ?X2 => Zfactor_term X1 X2
| Z.gt ?X1 ?X2 =>Zfactor_term X1 X2
| Z.le ?X1 ?X2 => Zfactor_term X1 X2 
| Z.ge ?X1 ?X2 =>Zfactor_term X1 X2
| _ => fail end)); clear H; intros H; try hyp_zsign_tac H; try repeat rewrite Zmult_1_l.
