Require Import ZArith.
Require Import NatPolS.
Require Import PolSBase.
Require Import PolFBase.
Require Import PolAux.
Require Import PolAuxList.
Require Import NatSignTac.


Definition Zfactor := 
  factor Z Zplus Zmult Z.opp 0%Z 1%Z is_Z1 is_Z0 is_Zpos is_Zdiv Z.div Zgcd.

Definition Zfactor_minus := 
  factor_sub Z Zplus Zmult Z.opp 0%Z 1%Z is_Z1 is_Z0 is_Zpos is_Zdiv Z.div Zgcd.


Definition Zget_delta := 
 get_delta Z Zplus Zmult Z.opp 0%Z 1%Z is_Z1 is_Z0 is_Zpos is_Zdiv Z.div Zgcd.


Ltac
Natfactor_term term1 term2 :=
let term := constr:(minus term1 term2) in
let rfv := FV NatCst plus mult minus Natopp term (@nil nat) in
let fv := Trev rfv in
let expr1 := mkPolexpr Z NatCst plus mult minus Natopp term1 fv in
let expr2 := mkPolexpr Z NatCst plus mult minus Natopp term2 fv in
let re := eval vm_compute in (Zfactor_minus (PEsub expr1 expr2)) in
let factor := match re with (PEmul ?X1 _) => X1 end in
let expr3 := match re with (PEmul _ (PEsub ?X1 _)) => X1 end in
let expr4 := match re with (PEmul _ (PEsub _ ?X1 )) => X1 end in
let
 re1' :=
  eval
     unfold
      Natconvert_back, convert_back,  pos_nth,  jump, 
         hd,  tl in (Natconvert_back (PEmul factor expr3) fv) in
let re1'' := eval lazy beta in re1' in
let re1''' := clean_zabs re1'' in
let
 re2' :=
  eval
     unfold
      Natconvert_back, convert_back,  pos_nth,  jump, 
         hd,  tl in (Natconvert_back (PEmul factor expr4) fv) in
let re2'' := eval lazy beta in re2' in 
let re2''' := clean_zabs re2'' in
replace2_tac term1 term2 re1''' re2'''; [idtac| ring | ring].

Ltac npolf :=
progress (
(try 
match goal with
| |- (?X1 = ?X2)%nat =>  Natfactor_term X1 X2 
| |- (?X1 <> ?X2)%nat =>  Natfactor_term X1 X2 
| |- lt ?X1 ?X2 => Natfactor_term X1 X2
| |- gt ?X1 ?X2 =>Natfactor_term X1 X2
| |- le ?X1 ?X2 => Natfactor_term X1 X2
| |- ge ?X1 ?X2 =>Natfactor_term X1 X2
| _ => fail end)); try (nsign_tac); try repeat (rewrite mult_1_l || rewrite mult_1_r).


Ltac hyp_npolf H := 
progress (
generalize H; 
(try 
match type of H with
  (?X1 = ?X2)%nat =>  Natfactor_term X1 X2 
| (?X1 <> ?X2)%nat =>  Natfactor_term X1 X2 
| lt ?X1 ?X2 => Natfactor_term X1 X2
| gt ?X1 ?X2 =>Natfactor_term X1 X2
| le ?X1 ?X2 => Natfactor_term X1 X2 
| ge ?X1 ?X2 =>Natfactor_term X1 X2
| _ => fail end)); clear H; intros H; try hyp_nsign_tac H; try repeat rewrite mult_1_l in H.
