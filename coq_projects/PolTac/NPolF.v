Require Import ZArith.
Require Import NAux.
Require Import NPolS.
Require Import PolSBase.
Require Import PolFBase.
Require Import PolAux.
Require Import PolAuxList.
Require Import NSignTac.


Definition Zfactor := 
  factor Z Zplus Zmult Z.opp 0%Z 1%Z is_Z1 is_Z0 is_Zpos is_Zdiv Z.div Zgcd.

Definition Zfactor_minus := 
  factor_sub Z Zplus Zmult Z.opp 0%Z 1%Z is_Z1 is_Z0 is_Zpos is_Zdiv Z.div Zgcd.


Definition Zget_delta := 
 get_delta Z Zplus Zmult Z.opp 0%Z 1%Z is_Z1 is_Z0 is_Zpos is_Zdiv Z.div Zgcd.


Ltac
Nfactor_term term1 term2 :=
let term := constr:(Nminus term1 term2) in
let rfv := FV NCst Nplus Nmult Nminus Nopp term (@nil N) in
let fv := Trev rfv in
let expr1 := mkPolexpr Z NCst Nplus Nmult Nminus Nopp term1 fv in
let expr2 := mkPolexpr Z NCst Nplus Nmult Nminus Nopp term2 fv in
let re := eval vm_compute in (Zfactor_minus (PEsub expr1 expr2)) in
let factor := match re with (PEmul ?X1 _) => X1 end in
let expr3 := match re with (PEmul _ (PEsub ?X1 _)) => X1 end in
let expr4 := match re with (PEmul _ (PEsub _ ?X1 )) => X1 end in
let
 re1' :=
  eval
     unfold
      Nconvert_back, convert_back,  pos_nth,  jump, 
         hd,  tl in (Nconvert_back (PEmul factor expr3) fv) in
let re1'' := eval lazy beta in re1' in
let re1''' := clean_zabs_N re1'' in
let
 re2' :=
  eval
     unfold
      Nconvert_back, convert_back,  pos_nth,  jump, 
         hd,  tl in (Nconvert_back (PEmul factor expr4) fv) in
let re2'' := eval lazy beta in re2' in 
let re2''' := clean_zabs_N re2'' in
replace2_tac term1 term2 re1''' re2'''; [idtac| ring | ring].


Ltac Npolf :=
progress (
(try 
match goal with
| |- (?X1 = ?X2)%N =>  Nfactor_term X1 X2 
| |- (?X1 <> ?X2)%N =>  Nfactor_term X1 X2 
| |- N.lt ?X1 ?X2 => Nfactor_term X1 X2
| |- N.gt ?X1 ?X2 =>Nfactor_term X1 X2
| |- N.le ?X1 ?X2 => Nfactor_term X1 X2
| |- N.ge ?X1 ?X2 =>Nfactor_term X1 X2
| _ => fail end)); try (Nsign_tac); try repeat (rewrite Nmult_1_l || rewrite Nmult_1_r).


Ltac hyp_Npolf H := 
progress (
generalize H; 
(try 
match type of H with
  (?X1 = ?X2)%N =>  Nfactor_term X1 X2 
| (?X1 <> ?X2)%N =>  Nfactor_term X1 X2 
| N.lt ?X1 ?X2 => Nfactor_term X1 X2
| N.gt ?X1 ?X2 =>Nfactor_term X1 X2
| N.le ?X1 ?X2 => Nfactor_term X1 X2 
| N.ge ?X1 ?X2 =>Nfactor_term X1 X2
| _ => fail end)); clear H; intros H; try hyp_Nsign_tac H; try repeat rewrite Nmult_1_l in H.
