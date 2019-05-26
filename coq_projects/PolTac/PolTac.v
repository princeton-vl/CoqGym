Require Import RSignTac.
Require Import NSignTac.
Require Import NatSignTac.
Require Import ZSignTac.

Ltac sign_tac :=  nsign_tac || Nsign_tac || zsign_tac || rsign_tac.

Ltac hyp_sign_tac H :=  hyp_nsign_tac H || hyp_Nsign_tac H || hyp_zsign_tac H || hyp_rsign_tac H.


Require Import RPolS.
Require Import ZPolS.
Require Import NatPolS.
Require Import NPolS.
Require Export ArithRing.
Require Export NArithRing.

Ltac pols :=  npols || Npols || zpols || rpols.

Ltac hyp_pols H :=  hyp_npols H || hyp_Npols H || hyp_zpols H || hyp_rpols H.


Require Import RPolF.
Require Import ZPolF.
Require Import NatPolF.
Require Import NPolF.
Require Export ArithRing.


Ltac polf :=  npolf || Npolf || zpolf || rpolf.

Ltac hyp_polf H := hyp_npolf H || hyp_Npolf H || hyp_zpolf H || hyp_rpolf H.


Require Import RPolR.
Require Import ZPolR.
Require Import NatPolR.
Require Import NPolR.


Ltac polr term :=  
match goal with |- ?G => 
 (let u := npol_is_compare G in npolr term)
||
 (let u := Npol_is_compare G in Npolr term)
||
(let u := zpol_is_compare G in zpolr term)
||
(let u := rpol_is_compare G in rpolr term)
end.


Ltac polrx term dir1 dir2 occ :=  
match goal with |- ?G => 
  (let u := npol_is_compare G in npolrx term dir1 dir2 occ)
||
  (let u := Npol_is_compare G in Npolrx term dir1 dir2 occ)
||
(let u := zpol_is_compare G in zpolrx term dir1 dir2 occ)
||
(let u := rpol_is_compare G in rpolrx term dir1 dir2 occ)
end.
