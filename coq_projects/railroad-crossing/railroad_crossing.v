(* This program is free software; you can redistribute it and/or      *)
(* modify it under the terms of the GNU Lesser General Public License *)
(* as published by the Free Software Foundation; either version 2.1   *)
(* of the License, or (at your option) any later version.             *)
(*                                                                    *)
(* This program is distributed in the hope that it will be useful,    *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of     *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the      *)
(* GNU General Public License for more details.                       *)
(*                                                                    *)
(* You should have received a copy of the GNU Lesser General Public   *)
(* License along with this program; if not, write to the Free         *)
(* Software Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA *)
(* 02110-1301 USA                                                     *)


(***** System TCG: Train || Controller || Gate  "the Railroad Crossing Example" *****)
(*                                                                                  *)
(* Temporal Automatas:                                                              *)
(*                                                                                  *)
(*          TRAIN:          CONTROLLER:	             GATE:                          *)
(*                                                                                  *)
(*                                 App y:=0                  Lower z:=0             *)
(*          --> Far         -->Sc1 -------> Sc2      -->Open ---------> Lowering    *)
(*            /    \            |            |           |               |          *)
(*          Exit   App         Raise        Lower       Up              Down        *)
(*          x<kt2  x:=0        y<kc2        y=kc1       kg2<=z<kg3      z<kg        *)
(*         /          \         |            |           |               |          *)
(*   Inside <-------- Near     Sc4 <------- Sc3      Raising <--------- Closed      *)
(*         In kt1<x<kt2            Exit y:=0                 Raise z:=0             *)
(*                                                                                  *)
(************************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.

Require Import time_clocks. (* Temporal notions for discrete time *)

Section Automatas_TCG.   

(* System TCG: Especification *)

  (* Set of Labels *)

  Inductive Label : Set :=
    | Approach : Label
    | In : Label
    | Exit : Label
    | Lower : Label
    | Raise : Label
    | Up : Label
    | Down : Label
    | Tick : Label. 

  (* Tick represent temporal transitions *)  

  
  (* Locations: ST (Train), SC (Controller) and SG (Gate) *)
  
  Inductive ST : Set :=
    | Far : ST
    | Near : ST
    | Inside : ST.
  Inductive SC : Set :=
    | Sc1 : SC
    | Sc2 : SC
    | Sc3 : SC
    | Sc4 : SC.
  Inductive SG : Set :=
    | Open : SG
    | Lowering : SG
    | Closed : SG
    | Raising : SG.


  (* States with one clock *)

  Definition S_Ck (S : Set) := (S * Clock)%type.


  (* TCG constants *)

  Definition kt1 : Instant := 8. 
  Definition kt2 : Instant := 20.
  Definition kc1 : Instant := 4.
  Definition kc2 : Instant := 4.
  Definition kg1 : Instant := 4.
  Definition kg2 : Instant := 4.
  Definition kg3 : Instant := 8.


  (* Invariants of locations for the Train *)

  Inductive InvT : S_Ck ST -> Prop :=
    | Ifar : forall x : Clock, InvT (Far, x)
    | Inear : forall x : Clock, lt_Ck x kt2 -> InvT (Near, x)
    | Iinside : forall x : Clock, lt_Ck x kt2 -> InvT (Inside, x).


  (* Invariants of locations for the Controller *)

  Inductive InvC : S_Ck SC -> Prop :=
    | Isc1 : forall y : Clock, InvC (Sc1, y)
    | Isc2 : forall y : Clock, le_Ck y kc1 -> InvC (Sc2, y)
    | Isc3 : forall y : Clock, InvC (Sc3, y)
    | Isc4 : forall y : Clock, lt_Ck y kc2 -> InvC (Sc4, y).


   (* Invariants of locations for the Gate *)

  Inductive InvG : S_Ck SG -> Prop :=
    | Iopen : forall z : Clock, InvG (Open, z)
    | Ilowering : forall z : Clock, lt_Ck z kg1 -> InvG (Lowering, z)
    | Iclosed : forall z : Clock, InvG (Closed, z)
    | Iraising : forall z : Clock, lt_Ck z kg3 -> InvG (Raising, z).


  (* Train transitions *)

  Inductive TrT : S_Ck ST -> Label -> S_Ck ST -> Prop :=
    | ttApproach : forall x : Clock, TrT (Far, x) Approach (Near, Reset)
    | ttIn :
        forall x : Clock,
        gt_Ck x kt1 -> lt_Ck x kt2 -> TrT (Near, x) In (Inside, x)
    | ttExit : forall x : Clock, lt_Ck x kt2 -> TrT (Inside, x) Exit (Far, x)
    | ttTick :
        forall (x : Clock) (s : ST),
        InvT (s, Inc x) -> TrT (s, x) Tick (s, Inc x). 


  (* Controller transitions *)

  Inductive TrC : S_Ck SC -> Label -> S_Ck SC -> Prop :=
    | tcApproach : forall y : Clock, TrC (Sc1, y) Approach (Sc2, Reset)
    | tcLower : forall y : Clock, eq_Ck y kc1 -> TrC (Sc2, y) Lower (Sc3, y)
    | tcExit : forall y : Clock, TrC (Sc3, y) Exit (Sc4, Reset)
    | tcRaise : forall y : Clock, lt_Ck y kc2 -> TrC (Sc4, y) Raise (Sc1, y)
    | tcTick :
        forall (y : Clock) (s : SC),
        InvC (s, Inc y) -> TrC (s, y) Tick (s, Inc y). 


  (* Gate transitions *)

  Inductive TrG : S_Ck SG -> Label -> S_Ck SG -> Prop :=
    | tgLower : forall z : Clock, TrG (Open, z) Lower (Lowering, Reset)
    | tgDown :
        forall z : Clock, lt_Ck z kg1 -> TrG (Lowering, z) Down (Closed, z)
    | tgRaise : forall z : Clock, TrG (Closed, z) Raise (Raising, Reset)
    | tgUp :
        forall z : Clock,
        ge_Ck z kg2 -> lt_Ck z kg3 -> TrG (Raising, z) Up (Open, z)
    | tgTick :
        forall (z : Clock) (s : SG),
        InvG (s, Inc z) -> TrG (s, z) Tick (s, Inc z). 
  

  (* States for the system: train||controller||gate *)

  Definition StGlobal := (S_Ck ST * (S_Ck SC * S_Ck SG))%type.


  (* Transitions for the system: train||controller||gate *)

  Inductive TrGlobal : StGlobal -> Label -> StGlobal -> Prop :=
    | tGl_In :
        forall st1 st2 : S_Ck ST,
        TrT st1 In st2 ->
        forall (sc : S_Ck SC) (sg : S_Ck SG),
        TrGlobal (st1, (sc, sg)) In (st2, (sc, sg))
    | tGl_Down :
        forall sg1 sg2 : S_Ck SG,
        TrG sg1 Down sg2 ->
        forall (st : S_Ck ST) (sc : S_Ck SC),
        TrGlobal (st, (sc, sg1)) Down (st, (sc, sg2))
    | tGl_Up :
        forall sg1 sg2 : S_Ck SG,
        TrG sg1 Up sg2 ->
        forall (st : S_Ck ST) (sc : S_Ck SC),
        TrGlobal (st, (sc, sg1)) Up (st, (sc, sg2))
    | tGl_Approach :
        forall (st1 st2 : S_Ck ST) (sc1 sc2 : S_Ck SC),
        TrT st1 Approach st2 ->
        TrC sc1 Approach sc2 ->
        forall sg : S_Ck SG,
        TrGlobal (st1, (sc1, sg)) Approach (st2, (sc2, sg))
    | tGl_Exit :
        forall (st1 st2 : S_Ck ST) (sc1 sc2 : S_Ck SC),
        TrT st1 Exit st2 ->
        TrC sc1 Exit sc2 ->
        forall sg : S_Ck SG, TrGlobal (st1, (sc1, sg)) Exit (st2, (sc2, sg))
    | tGl_Lower :
        forall (sc1 sc2 : S_Ck SC) (sg1 sg2 : S_Ck SG),
        TrC sc1 Lower sc2 ->
        TrG sg1 Lower sg2 ->
        forall st : S_Ck ST, TrGlobal (st, (sc1, sg1)) Lower (st, (sc2, sg2))
    | tGl_Raise :
        forall (sc1 sc2 : S_Ck SC) (sg1 sg2 : S_Ck SG),
        TrC sc1 Raise sc2 ->
        TrG sg1 Raise sg2 ->
        forall st : S_Ck ST, TrGlobal (st, (sc1, sg1)) Raise (st, (sc2, sg2))
    | tGl_Tick :
        forall (st1 st2 : S_Ck ST) (sc1 sc2 : S_Ck SC) (sg1 sg2 : S_Ck SG),
        TrT st1 Tick st2 ->
        TrC sc1 Tick sc2 ->
        TrG sg1 Tick sg2 -> TrGlobal (st1, (sc1, sg1)) Tick (st2, (sc2, sg2)). 
 

  (* Initial states *) 

  Definition ini_CkT := 0.
  Definition ini_CkC := 0.
  Definition ini_CkG := 0.

  Definition SiniT : S_Ck ST := (Far, ini_CkT).
  Definition SiniC : S_Ck SC := (Sc1, ini_CkC).
  Definition SiniG : S_Ck SG := (Open, ini_CkG).

  Definition SiniTCG : StGlobal := (SiniT, (SiniC, SiniG)).

End Automatas_TCG.

Hint Constructors InvT: sysTCG.
Hint Constructors InvC: sysTCG.
Hint Constructors InvG: sysTCG.
Hint Constructors TrT: sysTCG.
Hint Constructors TrC: sysTCG.
Hint Constructors TrG: sysTCG.
Hint Constructors TrGlobal: sysTCG.


(****************************************************************************)
(*                               System TCG: Analysis                       *)
(****************************************************************************)

Load "TemporalOperators.v". 
(* Temporal operators. CTL -computation tree logic- and TCTL -timed computation tree logic- *)


(* Elemental properties of clocks and constants of the System TCG *)

Lemma Trivial1 : eq_Ck ini_CkT ini_CkC.
Proof.
  unfold eq_Ck, ini_CkT, ini_CkC in |- *; trivial.
Qed.

Lemma Trivial2 : forall x : Clock, eq_Ck x x.
Proof.
  unfold eq_Ck in |- *; trivial.
Qed.

Lemma Trivial3 : forall x y : Clock, eq_Ck x y -> eq_Ck (Inc x) (Inc y).
Proof.
  unfold eq_Ck, Inc in |- *; intros x y eq_x_y; rewrite eq_x_y; trivial.
Qed.

Lemma Trivial4 :
 forall x y z : Clock,
 eq_Ck x (plus_Ck y z) -> eq_Ck (Inc x) (plus_Ck (Inc y) z).
Proof.
  unfold eq_Ck, Inc, plus_Ck in |- *; intros.
  rewrite H; rewrite (plus_assoc_reverse y z tick);
   rewrite (plus_comm z tick); auto with *.
Qed.

Lemma Trivial5 : forall x : Clock, ge_Ck x Reset.
Proof.
  unfold Clock, ge_Ck, Reset in |- *; auto with *.
Qed.

Lemma Trivial6 : forall x y : Clock, ge_Ck x y -> ge_Ck (Inc x) (Inc y). 
Proof.
  unfold Clock, ge_Ck, Inc, plus_Ck in |- *; auto with *. 
Qed.

Lemma Trivial7 : forall x y : Clock, eq_Ck x y -> ge_Ck x y.
Proof.
  unfold Clock, ge_Ck, eq_Ck in |- *; intros.
  rewrite H; auto with *.
Qed.

Lemma Trivial8 : forall x y : Clock, ge_Ck x y -> ge_Ck (Inc x) y.
Proof.
  unfold Clock, ge_Ck, Inc, plus_Ck, tick, plus in |- *; auto with *.
Qed.

Lemma Trivial9 : forall x y : Clock, gt_Ck x y -> gt_Ck (Inc x) y.
Proof.
  unfold Clock, gt_Ck, Inc, plus_Ck in |- *; auto with *.
Qed.

Lemma Trivial10 : forall x : Clock, gt_Ck x kt1 -> gt_Ck x kc1.
Proof.
  unfold Clock, gt_Ck, kt1, kc1 in |- *; intros.
  apply (gt_trans x 8 4 H).
  unfold gt in |- *; repeat apply lt_n_S; apply lt_O_Sn.
Qed.

Lemma Trivial11 : forall x : Clock, ~ gt_Ck Reset x.
Proof.
  unfold Clock, gt_Ck, Reset in |- *; auto with *.
Qed.

Lemma Trivial12 :
 forall x y : Clock, gt_Ck (Inc x) y -> eq_Ck x y \/ gt_Ck x y.
Proof.
  unfold Clock, Inc, eq_Ck, gt_Ck, plus_Ck, tick in |- *; intros x y.
  rewrite (plus_comm x 1); simpl in |- *; intros.
  elim (le_lt_or_eq y x (gt_S_le y x H)); auto with *.
Qed.

Lemma Trivial13 :
 forall x y z : Clock, gt_Ck (Inc x) z -> eq_Ck x y -> ~ le_Ck (Inc y) z.
Proof.
  unfold Clock, Inc, plus_Ck, tick, eq_Ck, le_Ck, gt_Ck in |- *; intros x y z.
  rewrite (plus_comm x 1); rewrite (plus_comm y 1); simpl in |- *; intros.
  rewrite <- H0; apply gt_not_le; assumption.
Qed.

Lemma Trivial14 : forall x : Clock, gt_Ck x kt1 \/ eq_Ck x kt1 -> gt_Ck x kc1.
Proof.
  unfold Clock, kt1, kc1, tick, eq_Ck, gt_Ck in |- *; intros.
  elim H; intro H1; [ apply (gt_trans x 8 4 H1) | rewrite H1 ];
   unfold gt in |- *; repeat apply lt_n_S; apply lt_O_Sn.
Qed.

Lemma Trivial15 :
 forall x y z : Clock,
 eq_Ck x kt1 -> eq_Ck x y -> eq_Ck y (plus_Ck z kc1) -> ~ lt_Ck (Inc z) kg1.
Proof.
  unfold Clock, kt1, kc1, kg1, Inc, plus_Ck, tick, eq_Ck, lt_Ck in |- *;
   intros.
  rewrite H in H0; rewrite <- H0 in H1.
  apply lt_asym.
  rewrite (plus_comm z 4) in H1; rewrite (plus_comm z 1); simpl in |- *.
  rewrite (plus_minus 8 4 z H1); simpl in |- *.
  repeat apply lt_n_S; apply lt_O_Sn.
Qed.

Lemma Trivial16 :
 forall x y : Clock, lt_Ck x kc2 -> ~ eq_Ck x (plus_Ck y kc1).
Proof.
  unfold Clock, kc1, kc2, eq_Ck, plus_Ck, tick, lt_Ck, not in |- *; intros.
  rewrite H0 in H; elim (le_not_lt 4 (y + 4) (le_plus_r y 4) H).
Qed.

Lemma Trivial17 :
 forall x y z : Clock, eq_Ck x y -> eq_Ck x z -> ~ le_Ck (Inc z) y.
Proof.
  unfold Clock, eq_Ck, Inc, plus_Ck, tick, le_Ck in |- *; intros.
  rewrite <- H0; rewrite <- H.
  rewrite plus_comm; simpl in |- *; unfold not in |- *; intro.
  elim (n_Sn x (le_antisym x (S x) (le_n_Sn x) H1)).
Qed.

Lemma Trivial18 : lt_Ck (Inc Reset) kc2.
Proof.
  unfold lt_Ck, Inc, tick, plus_Ck, Reset, kc2 in |- *.
  rewrite (plus_comm 0 1); simpl in |- *.
  apply lt_n_S; apply lt_O_Sn.
Qed.

Lemma Trivial19 :
 forall x y z : Clock,
 lt_Ck x kg1 -> eq_Ck y (plus_Ck x kc1) -> eq_Ck z y -> lt_Ck (Inc z) kt2.
Proof.
  unfold Clock, lt_Ck, eq_Ck, Inc, tick, plus_Ck, kg1, kc1, kt2 in |- *;
   intros.
  rewrite H0 in H1; rewrite H1.
  rewrite (plus_comm x 4); rewrite (plus_comm (4 + x) 1); simpl in |- *.
  repeat apply lt_n_S.
  apply (lt_le_trans x 4 15 H).
  repeat apply le_n_S; apply le_O_n.
Qed.

Lemma Trivial20 :
 forall x y z : Clock,
 lt_Ck x kg1 -> eq_Ck y (plus_Ck x kc1) -> eq_Ck z y -> ~ gt_Ck z kt1.
Proof.
  unfold Clock, gt_Ck, lt_Ck, eq_Ck, plus_Ck, kg1, kc1, kt1, gt in |- *;
   intros.
  apply le_not_lt.
  rewrite <- H1 in H0; rewrite H0.
  generalize (plus_lt_compat_r x 4 4 H); simpl in |- *; intro.
  apply (lt_le_weak (x + 4) 8 (plus_lt_compat_r x 4 4 H)).
Qed.

Lemma Trivial21 : lt_Ck (Inc Reset) kg3.
Proof.
  unfold lt_Ck, Inc, tick, plus_Ck, Reset, kg3 in |- *.
  rewrite (plus_comm 0 1); simpl in |- *.
  apply lt_n_S; apply lt_O_Sn.
Qed.

Lemma Trivial22 : forall x y : Clock, le_Ck x y -> lt_Ck x y \/ eq_Ck x y.
Proof.
  unfold Clock, le_Ck, lt_Ck, eq_Ck in |- *; intros.
  apply (le_lt_or_eq x y H).
Qed.

Lemma Trivial23 : forall x y : Clock, lt_Ck x kc1 -> eq_Ck y x -> Inc y < kt2. 
Proof.
  unfold Clock, lt_Ck, eq_Ck, Inc, tick, plus_Ck, kc1, kt2 in |- *; intros.
  rewrite <- H0 in H; rewrite (plus_comm y 1); simpl in |- *.
  apply lt_n_S.
  apply (lt_le_trans y 4 19 H).
  repeat apply le_n_S; apply le_O_n.
Qed.

Lemma Trivial24 : forall x y : Clock, lt_Ck x y -> le_Ck (Inc x) y.
Proof.
  unfold Clock, lt_Ck, le_Ck, Inc, tick, plus_Ck in |- *; intros.
  rewrite (plus_comm x 1); simpl in |- *.
  apply (lt_le_S x y H).
Qed.

Lemma Trivial25 :
 forall x y : Clock, eq_Ck y kc1 -> eq_Ck x y -> lt_Ck (Inc x) kt2.
Proof.
  unfold Clock, eq_Ck, lt_Ck, Inc, tick, plus_Ck, kc1, kt2 in |- *; intros. 
  rewrite (plus_comm x 1); simpl in |- *.
  apply lt_n_S.
  rewrite H in H0; rewrite H0.
  repeat apply lt_n_S; apply lt_O_Sn.
Qed.

Lemma Trivial26 : lt_Ck (Inc Reset) kg1.
Proof.
  unfold lt_Ck, Inc, plus_Ck, tick, kg1, Reset in |- *.
  rewrite (plus_comm 0 1); simpl in |- *.
  apply lt_n_S; apply lt_O_Sn.
Qed.

Lemma Trivial27 : lt_Ck (Inc Reset) kt2.
Proof.
  unfold lt_Ck, Inc, plus_Ck, tick, kt2, Reset in |- *.
  rewrite (plus_comm 0 1); simpl in |- *.
  apply lt_n_S; apply lt_O_Sn.
Qed.

Lemma Trivial28 : le_Ck (Inc Reset) kc1.
Proof.
  unfold le_Ck, Inc, plus_Ck, tick, kc1, Reset in |- *.
  rewrite (plus_comm 0 1); simpl in |- *.
  apply le_n_S; apply le_O_n.
Qed.

Lemma Trivial29 :
 forall x : Clock, lt_Ck x kg3 -> lt_Ck x kg2 \/ ge_Ck x kg2 /\ lt_Ck x kg3.
Proof.
  unfold Clock, lt_Ck, ge_Ck, kg2, kg3, ge in |- *; intros.
  elim (le_or_lt 4 x); auto with *.
Qed.

Lemma Trivial30 : forall x : Clock, lt_Ck x kg2 -> lt_Ck (Inc x) kg3.
Proof.
  unfold Clock, lt_Ck, Inc, plus_Ck, tick, kg2, kg3 in |- *; intros.
  rewrite (plus_comm x 1); simpl in |- *.
  apply lt_n_S.
  apply (lt_le_trans x 4 7 H).
  repeat apply le_n_S; apply le_O_n.
Qed.

Lemma Trivial31 : forall x y : Clock, eq_Ck x kc1 -> ge_Ck y x -> ge_Ck y kg2.
Proof.
  unfold Clock, ge_Ck, eq_Ck, kc1, kg2, ge in |- *; intros.
  rewrite H in H0; assumption.
Qed.

Lemma not_lt_le : forall x y : nat, ~ x < y -> y <= x.
Proof.
  unfold not in |- *; intros x y no_lt_x_y.
  elim (le_or_lt y x); [ trivial | intro lt_x_y; elim (no_lt_x_y lt_x_y) ].
Qed.

Lemma Trivial32 :
 forall x : Clock, lt_Ck x kt2 -> ~ lt_Ck (Inc x) kt2 -> gt_Ck x kt1.
Proof.
  unfold Clock, lt_Ck, gt_Ck, Inc, plus_Ck, tick, kt1, kt2, gt in |- *;
   intros.
  generalize (not_lt_le H0); rewrite (plus_comm x 1); simpl in |- *; intro.
  generalize (le_antisym 19 x (le_S_n 19 x H1) (lt_n_Sm_le x 19 H)); intro H4;
   rewrite <- H4.
  repeat apply lt_n_S; apply lt_O_Sn.
Qed.

Axiom not_le_lt : forall x y : nat, ~ x <= y -> y < x.
Lemma Trivial33 :
 forall x : Clock, le_Ck x kc1 -> ~ le_Ck (Inc x) kc1 -> eq_Ck x kc1.
Proof.
  unfold Clock, le_Ck, eq_Ck, Inc, plus_Ck, tick, kc1 in |- *; intros.
  generalize (not_le_lt H0); rewrite (plus_comm x 1); simpl in |- *; intro.
  apply (le_antisym x 4 H (lt_n_Sm_le 4 x H1)).
Qed.

Lemma Trivial34 :
 forall x : Clock, lt_Ck x kg3 -> ~ lt_Ck (Inc x) kg3 -> ge_Ck x kg2.
Proof.
  unfold Clock, lt_Ck, ge_Ck, Inc, plus_Ck, tick, kg3, kg2 in |- *; intros.
  generalize (not_lt_le H0); rewrite (plus_comm x 1); simpl in |- *; intro.
  generalize (le_antisym 7 x (le_S_n 7 x H1) (lt_n_Sm_le x 7 H)); intro H4;
   rewrite <- H4.
  unfold ge in |- *; repeat apply le_n_S; apply le_O_n.
Qed.

Lemma trivial_inv_1 : lt_Ck Reset kt2.
Proof.
  unfold lt_Ck, Reset, kt2 in |- *; auto with *.
Qed.

Lemma trivial_inv_2 : forall x : Clock, le_Ck Reset x.
Proof.
  unfold Clock, le_Ck, Reset in |- *; auto with *.
Qed.

Lemma trivial_inv_3 : lt_Ck Reset kc2.
  unfold lt_Ck, Reset, kc2 in |- *; auto with *.
Qed.

Lemma trivial_inv_4 : lt_Ck Reset kg1.
Proof.
  unfold lt_Ck, Reset, kg1 in |- *; auto with *.
Qed.

Lemma trivial_inv_5 : lt_Ck Reset kg3.
Proof.
  unfold lt_Ck, Reset, kg3 in |- *; auto with *.
Qed.


(* Invertion principles for transitions and location invariants *)

Derive Inversion_clear cl_TRT_APPROACH with
 (forall st1 st2 : S_Ck ST, TrT st1 Approach st2) Sort Prop.
Derive Inversion_clear cl_TRT_IN with
 (forall st1 st2 : S_Ck ST, TrT st1 In st2) Sort Prop.
Derive Inversion_clear cl_TRT_EXIT with
 (forall st1 st2 : S_Ck ST, TrT st1 Exit st2) Sort Prop.
Derive Inversion_clear cl_TRT_INC_TIME with
 (forall st1 st2 : S_Ck ST, TrT st1 Tick st2) Sort Prop.

Derive Inversion_clear cl_TRC_APPROACH with
 (forall sc1 sc2 : S_Ck SC, TrC sc1 Approach sc2) Sort Prop.
Derive Inversion_clear cl_TRC_LOWER with
 (forall sc1 sc2 : S_Ck SC, TrC sc1 Lower sc2) Sort Prop.
Derive Inversion_clear cl_TRC_EXIT with
 (forall sc1 sc2 : S_Ck SC, TrC sc1 Exit sc2) Sort Prop.
Derive Inversion_clear cl_TRC_RAISE with
 (forall sc1 sc2 : S_Ck SC, TrC sc1 Raise sc2) Sort Prop.
Derive Inversion_clear cl_TRC_INC_TIME with
 (forall sc1 sc2 : S_Ck SC, TrC sc1 Tick sc2) Sort Prop.

Derive Inversion_clear cl_TRG_LOWER with
 (forall sg1 sg2 : S_Ck SG, TrG sg1 Lower sg2) Sort Prop.
Derive Inversion_clear cl_TRG_DOWN with
 (forall sg1 sg2 : S_Ck SG, TrG sg1 Down sg2) Sort Prop.
Derive Inversion_clear cl_TRG_RAISE with
 (forall sg1 sg2 : S_Ck SG, TrG sg1 Raise sg2) Sort Prop.
Derive Inversion_clear cl_TRG_UP with
 (forall sg1 sg2 : S_Ck SG, TrG sg1 Up sg2) Sort Prop.
Derive Inversion_clear cl_TRG_INC_TIME with
 (forall sg1 sg2 : S_Ck SG, TrG sg1 Tick sg2) Sort Prop.

Derive Inversion_clear cl_Ifar with (forall x : Clock, InvT (Far, x)) Sort
 Prop.
Derive Inversion_clear cl_Inear with (forall x : Clock, InvT (Near, x)) Sort
 Prop.
Derive Inversion_clear cl_Iinside with (forall x : Clock, InvT (Inside, x))
 Sort Prop.

Derive Inversion_clear cl_Isc1 with (forall y : Clock, InvC (Sc1, y)) Sort
 Prop.
Derive Inversion_clear cl_Isc2 with (forall y : Clock, InvC (Sc2, y)) Sort
 Prop.
Derive Inversion_clear cl_Isc3 with (forall y : Clock, InvC (Sc3, y)) Sort
 Prop.
Derive Inversion_clear cl_Isc4 with (forall y : Clock, InvC (Sc4, y)) Sort
 Prop.

Derive Inversion_clear cl_Iopen with (forall z : Clock, InvG (Open, z)) Sort
 Prop.
Derive Inversion_clear cl_Ilowering with
 (forall z : Clock, InvG (Lowering, z)) Sort Prop.
Derive Inversion_clear cl_Iclosed with (forall z : Clock, InvG (Closed, z))
 Sort Prop.
Derive Inversion_clear cl_Iraising with (forall z : Clock, InvG (Raising, z))
 Sort Prop.


(* Some tactics *)

Ltac Easy := try discriminate; auto with *.

Ltac Easy2 := intros; try discriminate; auto with *.


Ltac Simpl_or eq := elim eq; intro; Easy.

Ltac Simpl_and eq := elim eq; intros; Easy.

Ltac Generalize_Easy eq := generalize eq; intro; Easy.

Ltac Split3_Trivial := split; [ auto with * | split; auto with * ].

Ltac BeginForAll :=
  unfold ForAll in |- *; simple induction 1;
   [ simpl in |- *; intros; Easy | idtac ].

Ltac SplitTrans :=
  intros s1 s2 l rs_s1 p_s1 tr_gl; generalize rs_s1; clear rs_s1;
   generalize p_s1; clear p_s1; elim tr_gl.

Ltac SplitTrans_Simpl :=
  SplitTrans;
   [ Simpl_In
   | Simpl_Down
   | Simpl_Up
   | Simpl_Approach
   | Simpl_Exit
   | Simpl_Lower
   | Simpl_Raise
   | Simpl_Tick ]
 with Simpl_In :=
  intros st1 st2 trt_In; inversion trt_In using cl_TRT_IN;
   intros x gt_x_kt1 lt_x_kt2 sc sg; elim sc; elim sg; 
   simpl in |- *; intros; Easy
 with Simpl_Down :=
  intros sg1 sg2 trg_Down; inversion trg_Down using cl_TRG_DOWN;
   intros z lt_z_kg1 st sc; elim st; elim sc; simpl in |- *; 
   intros; Easy
 with Simpl_Up :=
  intros sg1 sg2 trg_Up; inversion trg_Up using cl_TRG_UP;
   intros z ge_z_kg2 lt_z_kg3 st sc; elim st; elim sc; 
   simpl in |- *; intros; Easy
 with Simpl_Approach :=
  intros st1 st2 sc1 sc2 trt_Approach trc_Approach;
   inversion trt_Approach using cl_TRT_APPROACH;
   inversion trc_Approach using cl_TRC_APPROACH; intros y x sg; 
   elim sg; simpl in |- *; intros; Easy
 with Simpl_Exit :=
  intros st1 st2 sc1 sc2 trt_Exit trc_Exit;
   inversion trt_Exit using cl_TRT_EXIT; inversion trc_Exit using cl_TRC_EXIT;
   intros y x lt_x_kt2 sg; elim sg; simpl in |- *; 
   intros; Easy
 with Simpl_Lower :=
  intros sc1 sc2 sg1 sg2 trc_Lower trg_Lower;
   inversion trc_Lower using cl_TRC_LOWER;
   inversion trg_Lower using cl_TRG_LOWER; intros z y eq_y_kc1 st; 
   elim st; simpl in |- *; intros; Easy
 with Simpl_Raise :=
  intros sc1 sc2 sg1 sg2 trc_Raise trg_Raise;
   inversion trc_Raise using cl_TRC_RAISE;
   inversion trg_Raise using cl_TRG_RAISE; intros z y lt_y_kc2 st; 
   elim st; simpl in |- *; intros; Easy
 with Simpl_Tick :=
  intros st1 st2 sc1 sc2 sg1 sg2 trt_Tick trc_Tick trg_Tick;
   inversion trt_Tick using cl_TRT_INC_TIME;
   inversion trc_Tick using cl_TRC_INC_TIME;
   inversion trg_Tick using cl_TRG_INC_TIME; simpl in |- *; 
   intros; Easy.


Notation InvTCG :=
  (fun s : StGlobal =>
   match s with
   | (st_x, (sc_y, sg_z)) => InvT st_x /\ InvC sc_y /\ InvG sg_z
   end) (only parsing).

Notation ForAll_TCG := (ForAll TrGlobal) (only parsing).

Notation Exists_TCG := (Exists TrGlobal) (only parsing).


(* The initial state of the system TCG satisfy the location invariants *)

Lemma Inv_SiniTCG :
 (fun s : StGlobal =>
  match s with
  | (st_x, (sc_y, sg_z)) => InvT st_x /\ InvC sc_y /\ InvG sg_z
  end) SiniTCG.
Proof.
  simpl in |- *; unfold SiniT, SiniC, SiniG in |- *; Split3_Trivial.
Qed.



(* Some invariants of the system TCG *)

Definition Inv1 (s : StGlobal) :=
  match s with
  | ((st, _), ((sc, _), (sg, _))) =>
      st = Near \/ st = Inside -> sc = Sc3 -> sg = Closed \/ sg = Lowering
  end.

Lemma lema_Inv1 : ForAll TrGlobal SiniTCG Inv1.
Proof.
  BeginForAll.
  SplitTrans_Simpl.
  Simpl_or (p_s1 H0 H1).
Qed.



Definition Inv2 (s : StGlobal) :=
  match s with
  | ((st, _), ((sc, _), (sg, _))) =>
      st = Far -> sg = Open \/ sg = Raising -> sc = Sc1
  end.

Lemma lema_Inv2 : ForAll TrGlobal SiniTCG Inv2.
Proof.
  BeginForAll.
  SplitTrans_Simpl.
  Simpl_or H1.
  elim
   (lema_Inv1 rs_s1 (or_intror (Inside = Near) (refl_equal Inside))
      (refl_equal Sc3)); intro H2; rewrite H2 in H1; 
   Simpl_or H1.
  Simpl_or H1.
Qed.



Definition Inv3 (s : StGlobal) :=
  match s with
  | ((st, x), ((_, y), _)) => st = Near \/ st = Inside -> eq_Ck x y
  end.

Lemma lema_Inv3 : ForAll TrGlobal SiniTCG Inv3.
Proof.
  BeginForAll.
  apply Trivial1.
  SplitTrans_Simpl.
  Simpl_or H0.
  apply (Trivial3 (p_s1 H3)).
Qed.



Definition Inv4 (s : StGlobal) :=
  match s with
  | ((st, _), ((sc, _), _)) => st = Near -> sc = Sc2 \/ sc = Sc3
  end.

Lemma lema_Inv4 : ForAll TrGlobal SiniTCG Inv4.
Proof.
  BeginForAll.
  SplitTrans_Simpl.
  Simpl_or (p_s1 H0).
Qed.



Definition Inv5 (s : StGlobal) :=
  match s with
  | ((st, _), ((sc, y), (_, z))) =>
      st = Near -> sc = Sc3 -> eq_Ck y (plus_Ck z kc1)
  end.

Lemma lema_Inv5 : ForAll TrGlobal SiniTCG Inv5.
Proof.
  BeginForAll.
  SplitTrans_Simpl.
  apply (Trivial4 (p_s1 H3 H4)).
Qed.



Definition Inv6 (s : StGlobal) :=
  match s with
  | ((st, x), ((sc, _), _)) =>
      st = Near /\ gt_Ck x kc1 \/ st = Inside -> sc = Sc3
  end.

Lemma lema_Inv6 : ForAll TrGlobal SiniTCG Inv6.

Proof.
  BeginForAll.
  decompose [and or] H0; discriminate.
  SplitTrans_Simpl.
  apply p_s1; left; split; [ auto with * | apply (Trivial10 gt_x_kt1) ].
  decompose [and or] H0; [ elim (Trivial11 H3) | discriminate ].
  decompose [and or] H0; discriminate.
  Generalize_Easy (p_s1 H0).
  decompose [and or] H3; [ elim (Trivial12 H6) | auto with * ].
  elim (lema_Inv4 rs_s1 H5); auto with *.
    generalize (lema_Inv3 rs_s1 (or_introl (s4 = Inside) H5)); intros.
  rewrite H7 in H1. inversion H1 using cl_Isc2; intro H9. elim (Trivial13 H6 H4 H9).
  intro H7; apply p_s1; left; split;
   [ assumption | Generalize_Easy (Trivial9 H7) ].
Qed.



Definition Inv7 (s : StGlobal) :=
  match s with
  | ((st, _), ((sc, _), (sg, _))) =>
      st = Near \/ st = Inside -> sc = Sc3 -> sg = Lowering \/ sg = Closed
  end.

Lemma lema_Inv7 : ForAll TrGlobal SiniTCG Inv7.
Proof.
  BeginForAll.
  SplitTrans_Simpl.
  Simpl_or (p_s1 H0 H1).
Qed.



Definition Inv8 (s : StGlobal) :=
  match s with
  | ((st, x), ((sc, _), (sg, _))) =>
      st = Near /\ gt_Ck x kt1 \/ st = Inside -> sg = Closed
  end.

Lemma lema_Inv8 : ForAll TrGlobal SiniTCG Inv8.
Proof.
  BeginForAll.
  decompose [and or] H0; discriminate.
  SplitTrans_Simpl.
  Generalize_Easy (p_s1 H0).
  decompose [and or] H0; [ elim (Trivial11 H3) | discriminate ].
  Generalize_Easy (p_s1 H0).
  generalize (lema_Inv6 rs_s1); simpl in |- *; intro.
  decompose [and or] H0.
  Generalize_Easy
   (H1
      (or_introl (a = Inside)
         (conj H3 (Trivial14 (or_introl (eq_Ck b kt1) H4))))).
  Generalize_Easy (H1 (or_intror (a = Near /\ gt_Ck b kc1) H2)).
  decompose [and or] H3; [ Simpl_or (Trivial12 H6) | auto with * ].
  generalize
   (lema_Inv6 rs_s1
      (or_introl (s4 = Inside)
         (conj H5 (Trivial14 (or_intror (gt_Ck x kt1) H4))))); 
   intro.
  Simpl_or (lema_Inv1 rs_s1 (or_introl (s4 = Inside) H5) H7).
  rewrite H8 in H0; inversion H0 using cl_Ilowering; intro.
  elim
   (Trivial15 H4 (lema_Inv3 rs_s1 (or_introl (s4 = Inside) H5))
      (lema_Inv5 rs_s1 H5 H7) H9).
Qed.



Definition safeTCG (s : StGlobal) :=
  match s with
  | ((st, _), (_, (sg, _))) => st = Inside -> sg = Closed
  end.

(* The safety property of the system TCG *)

Lemma lema_safeTCG : ForAll TrGlobal SiniTCG safeTCG.
  Proof.
  apply Mon_I with (Pg := Inv8) (Pp := safeTCG);
   [ exact lema_Inv8 | unfold Inv8, safeTCG in |- *; simpl in |- * ].
  unfold Inv8, safeTCG in |- *; simpl in |- *; intro s; elim s.
  intros y y0; elim y; elim y0. 
  intros y1 y2 y3 y4; elim y1; elim y2; auto with *.
Qed.



Definition Inv9 (s : StGlobal) :=
  match s with
  | ((st, x), ((_, y), (_, z))) =>
      st = Near /\ gt_Ck x kc1 \/ st = Inside -> eq_Ck y (plus_Ck z kc1)
  end.

Lemma lema_Inv9 : ForAll TrGlobal SiniTCG Inv9.
Proof.
  BeginForAll.
  decompose [and or] H0; discriminate.
  SplitTrans_Simpl.
  apply p_s1; left; split; [ auto with * | apply (Trivial10 gt_x_kt1) ].
  decompose [and or] H0; [ elim (Trivial11 H3) | discriminate ].
  decompose [and or] H0; discriminate.
  elim (Trivial16 lt_y_kc2 (p_s1 H0)).
  decompose [and or] H3.
  elim (Trivial12 H6); intro.
  elim (lema_Inv4 rs_s1 H5); intro.
  rewrite H7 in H1; inversion H1 using cl_Isc2; intro.
  generalize (lema_Inv3 rs_s1 (or_introl (s4 = Inside) H5)); intro.
  elim (Trivial17 H4 H9 H8).
  apply (Trivial4 (lema_Inv5 rs_s1 H5 H7)).
  apply Trivial4; apply p_s1; left; split; assumption.
  apply (Trivial4 (p_s1 (or_intror (s4 = Near /\ gt_Ck x kc1) H4))).
Qed.



Definition Inv10 (s : StGlobal) :=
  match s with
  | (_, ((sc, _), (sg, _))) =>
      sc = Sc1 \/ sc = Sc2 -> sg = Open \/ sg = Raising
  end.

Lemma lema_Inv10 : ForAll TrGlobal SiniTCG Inv10.
Proof.
  BeginForAll.
  SplitTrans_Simpl.
  Simpl_or (p_s1 H0).
  Simpl_or H0.
  Simpl_or H0.
Qed. 



Definition Inv11 (s : StGlobal) :=
  match s with
  | (_, ((sc, _), (sg, _))) =>
      sg = Lowering \/ sg = Closed -> sc = Sc3 \/ sc = Sc4
  end.

Lemma lema_Inv11 : ForAll TrGlobal SiniTCG Inv11. 
Proof.
  generalize (Mon_I (tr:=TrGlobal) (Sini:=SiniTCG) (Pg:=Inv10) (Pp:=Inv11));
   unfold ForAll in |- *; intros.
  apply H; [ exact lema_Inv10 | idtac | assumption ].
  unfold Inv10, Inv11 in |- *; simpl in |- *; intro.
  elim s0; intros y y0; elim y; elim y0; intros y1 y2 y3 y4; elim y1; elim y2.
  intros sg ck sc; elim sg.
  intros ck1 H1 H2; Simpl_or H2.
  elim sc; intros ck1 H1;
   [ elim H1; Easy2
   | elim H1; Easy2
   | left; auto with *
   | right; auto with * ].
  elim sc; intros ck1 H1;
   [ elim H1; Easy2
   | elim H1; Easy2
   | left; auto with *
   | right; auto with * ].
  intros ck1 H1 H2; Simpl_or H2.
Qed.



Definition Inv12 (s : StGlobal) :=
  match s with
  | (_, ((sc, y), (_, z))) => sc = Sc2 -> ge_Ck z y
  end.

Lemma lema_Inv12 : ForAll TrGlobal SiniTCG Inv12. 
Proof.
  BeginForAll.
  SplitTrans_Simpl.
  apply Trivial5.
  apply (Trivial6 (p_s1 H3)).
Qed.



Definition Inv13 (s : StGlobal) :=
  match s with
  | ((st, _), ((sc, _), _)) => sc = Sc2 -> st = Near
  end.

Lemma lema_Inv13 : ForAll TrGlobal SiniTCG Inv13.
Proof.
  BeginForAll.
  SplitTrans_Simpl.
  generalize (lema_Inv6 rs_s1); simpl in |- *.
  rewrite H0.
  intro H1;
   Generalize_Easy
    (H1
       (or_introl (Near = Inside)
          (conj (refl_equal Near) (Trivial10 gt_x_kt1)))).
Qed.



Definition Inv14 (s : StGlobal) :=
  match s with
  | ((st, _), ((sc, _), (sg, _))) => sc = Sc4 -> st = Far /\ sg = Closed
  end.

Lemma lema_Inv14 : ForAll TrGlobal SiniTCG Inv14.
Proof.
  BeginForAll.
  SplitTrans_Simpl.
  Simpl_and (p_s1 H0).
  Simpl_and (p_s1 H0).
  Simpl_and (p_s1 H0).
  split; [ auto with * | apply (lema_safeTCG rs_s1 (refl_equal Inside)) ].
Qed.



Definition InvSc3 (s : StGlobal) :=
  match s with
  | (_, ((sc, y), _)) => sc = Sc3 -> ge_Ck y kc1
  end.

Lemma lema_InvSc3 : ForAll TrGlobal SiniTCG InvSc3.
Proof.
  BeginForAll.
  SplitTrans_Simpl.
  apply (Trivial7 eq_y_kc1).
  apply (Trivial8 (p_s1 H3)).
Qed.



Definition InvInside (s : StGlobal) :=
  match s with
  | ((st, x), _) => st = Inside -> gt_Ck x kt1
  end.

Lemma lema_InvInside : ForAll TrGlobal SiniTCG InvInside.
Proof.
  BeginForAll.
  SplitTrans_Simpl.
  apply (Trivial9 (p_s1 H3)).
Qed.



(* Lemmas, definitions and auxiliar tactics for the NonZeno property *)

Lemma InvT' :
 forall s : S_Ck ST,
 match s with
 | (st, x) =>
     st = Far \/ st = Near /\ lt_Ck x kt2 \/ st = Inside /\ lt_Ck x kt2 ->
     InvT s
 end.
Proof.
  intro s; elim s.
  intros.
  elim H;
   [ intro st; rewrite st; auto with *
   | intro n_i; elim n_i; intro H1; elim H1; intros st cond; rewrite st;
      [ apply Inear | apply Iinside ]; auto with * ].
Qed.


Lemma InvC' :
 forall s : S_Ck SC,
 match s with
 | (sc, y) =>
     sc = Sc1 \/
     sc = Sc2 /\ le_Ck y kc1 \/ sc = Sc3 \/ sc = Sc4 /\ lt_Ck y kc2 -> 
     InvC s
 end.
Proof.
  intro s; elim s.
  intros.
  elim H;
   [ intro sc; rewrite sc; auto with *
   | intro sc2_4; elim sc2_4;
      [ intro H1; elim H1; intros sc cond; rewrite sc; apply Isc2;
         auto with *
      | intro sc3_4; elim sc3_4;
         [ intro sc; rewrite sc; auto with *
         | intro H1; elim H1; intros sc cond; rewrite sc; apply Isc4;
            auto with * ] ] ].
Qed.


Lemma InvG' :
 forall s : S_Ck SG,
 match s with
 | (sg, z) =>
     sg = Open \/
     sg = Lowering /\ lt_Ck z kg1 \/
     sg = Closed \/ sg = Raising /\ lt_Ck z kg3 -> 
     InvG s
 end.
Proof.
  intro s; elim s.
  intros.
  elim H;
   [ intro sg; rewrite sg; auto with *
   | intro sg2_4; elim sg2_4;
      [ intro H1; elim H1; intros sg cond; rewrite sg; apply Ilowering;
         auto with *
      | intro sg3_4; elim sg3_4;
         [ intro sg; rewrite sg; auto with *
         | intro H1; elim H1; intros sg cond; rewrite sg; apply Iraising;
            auto with * ] ] ].
Qed.


Lemma NoImpl : forall A B : Prop, (A -> B) -> ~ B -> ~ A.
Proof.
  unfold not in |- *; auto with *.
Qed.


Lemma not_3_and :
 forall A B C : Prop, ~ (A /\ B /\ C) -> ~ A \/ A /\ ~ B \/ A /\ B /\ ~ C.
Proof.
  intros.
  elim (not_and_or _ _ H); intro H2;
   [ idtac | elim (not_and_or _ _ H2); intro ].
  auto with *. 
  elim (classic A); auto with *.
  elim (classic A); elim (classic B); auto with *.
Qed.


Notation no_invT :=
  (fun s : S_Ck ST =>
   match s with
   | (st, x) => st = Near /\ ~ lt_Ck x kt2 \/ st = Inside /\ ~ lt_Ck x kt2
   end) (only parsing).

Lemma No_invT :
 forall s : S_Ck ST,
 ~ InvT s ->
 (fun s : S_Ck ST =>
  match s with
  | (st, x) => st = Near /\ ~ lt_Ck x kt2 \/ st = Inside /\ ~ lt_Ck x kt2
  end) s.
Proof.
  intro s; elim s.
  intros st x inv.
  generalize (not_or_and _ _ (NoImpl (InvT' (st, x)) inv)); elim st; intro H0;
   elim H0; intros H1 H2; elim (not_or_and _ _ H2); 
   intros.
  absurd (Far = Far); auto with *.
  elim (not_and_or _ _ H); intros;
   [ absurd (Near = Near); auto with * | auto with * ].
  elim (not_and_or _ _ H3); intros;
   [ absurd (Inside = Inside); auto with * | auto with * ].
Qed.


Notation no_invC :=
  (fun s : S_Ck SC =>
   match s with
   | (sc, y) => sc = Sc2 /\ ~ le_Ck y kc1 \/ sc = Sc4 /\ ~ lt_Ck y kc2
   end) (only parsing).

Lemma No_invC :
 forall s : S_Ck SC,
 ~ InvC s ->
 (fun s : S_Ck SC =>
  match s with
  | (sc, y) => sc = Sc2 /\ ~ le_Ck y kc1 \/ sc = Sc4 /\ ~ lt_Ck y kc2
  end) s.
Proof.
  intro s; elim s.
  intros sc y inv.
  generalize (not_or_and _ _ (NoImpl (InvC' (sc, y)) inv)); elim sc; intro H0;
   elim H0; intros H1 H2; elim (not_or_and _ _ H2); 
   intros.
  absurd (Sc1 = Sc1); auto with *.
  elim (not_and_or _ _ H); intros;
   [ absurd (Sc2 = Sc2); auto with * | auto with * ].
  elim (not_or_and _ _ H3); intros; absurd (Sc3 = Sc3); auto with *.
  elim (not_or_and _ _ H3); intros H4 H5; elim (not_and_or _ _ H5); intros;
   [ absurd (Sc4 = Sc4); auto with * | auto with * ].
Qed.


Notation no_invG :=
  (fun s : S_Ck SG =>
   match s with
   | (sg, z) =>
       sg = Lowering /\ ~ lt_Ck z kg1 \/ sg = Raising /\ ~ lt_Ck z kg3
   end) (only parsing).

Lemma No_invG :
 forall s : S_Ck SG,
 ~ InvG s ->
 (fun s : S_Ck SG =>
  match s with
  | (sg, z) =>
      sg = Lowering /\ ~ lt_Ck z kg1 \/ sg = Raising /\ ~ lt_Ck z kg3
  end) s.
Proof.
  intro s; elim s.
  intros sc y inv.
  generalize (not_or_and _ _ (NoImpl (InvG' (sc, y)) inv)); elim sc; intro H0;
   elim H0; intros H1 H2; elim (not_or_and _ _ H2); 
   intros.
  absurd (Open = Open); auto with *.
  elim (not_and_or _ _ H); intros;
   [ absurd (Lowering = Lowering); auto with * | auto with * ].
  elim (not_or_and _ _ H3); intros; absurd (Closed = Closed); auto with *.
  elim (not_or_and _ _ H3); intros H4 H5; elim (not_and_or _ _ H5); intros;
   [ absurd (Raising = Raising); auto with * | auto with * ].
Qed.


Lemma INV_TCG_general :
 forall s : StGlobal,
 (fun s : StGlobal =>
  match s with
  | (st_x, (sc_y, sg_z)) => InvT st_x /\ InvC sc_y /\ InvG sg_z
  end) s ->
 ForAll TrGlobal s
   (fun s : StGlobal =>
    match s with
    | (st_x, (sc_y, sg_z)) => InvT st_x /\ InvC sc_y /\ InvG sg_z
    end).
Proof.
  intros.
  BeginForAll.
  SplitTrans_Simpl; elim p_s1; intros H1 H2; elim H2; intros; auto with *;
   (split; [ auto with * | split; auto with * ]).
  apply Inear; apply trivial_inv_1.
  apply Isc2; apply trivial_inv_2.
  apply Isc4; apply trivial_inv_3.
  apply Ilowering; apply trivial_inv_4.
  apply Iraising; apply trivial_inv_5.
Qed.



Lemma INV_T_general :
 forall s1 s2 : StGlobal,
 (fun s : StGlobal =>
  match s with
  | (st_x, (sc_y, sg_z)) => InvT st_x /\ InvC sc_y /\ InvG sg_z
  end) s1 -> RState TrGlobal s1 s2 -> InvT (fst s2).
Proof.
  intros.
  generalize (INV_TCG_general H H0).
  elim s2; simpl in |- *.
  intros st sc_sg.
  elim sc_sg; intros.
  elim H1; auto with *.
Qed.


Lemma INV_C_general :
 forall s1 s2 : StGlobal,
 (fun s : StGlobal =>
  match s with
  | (st_x, (sc_y, sg_z)) => InvT st_x /\ InvC sc_y /\ InvG sg_z
  end) s1 -> RState TrGlobal s1 s2 -> InvC (fst (snd s2)).
Proof.
  intros.
  generalize (INV_TCG_general H H0).
  elim s2; simpl in |- *.
  intros st sc_sg.
  elim sc_sg; simpl in |- *; intros.
  elim H1; intros inv_T inv_C_G; elim inv_C_G; auto with *.
Qed.


Lemma INV_G_general :
 forall s1 s2 : StGlobal,
 (fun s : StGlobal =>
  match s with
  | (st_x, (sc_y, sg_z)) => InvT st_x /\ InvC sc_y /\ InvG sg_z
  end) s1 -> RState TrGlobal s1 s2 -> InvG (snd (snd s2)).
Proof.
  intros.
  generalize (INV_TCG_general H H0).
  elim s2; simpl in |- *.
  intros st sc_sg.
  elim sc_sg; simpl in |- *; intros.
  elim H1; intros inv_T inv_C_G; elim inv_C_G; auto with *.
Qed.


Definition InvTick (s : StGlobal) :=
  match s with
  | ((st, x), ((sc, y), (sg, z))) =>
      (fun s : StGlobal =>
       match s with
       | (st_x, (sc_y, sg_z)) => InvT st_x /\ InvC sc_y /\ InvG sg_z
       end) (st, Inc x, (sc, Inc y, (sg, Inc z)))
  end.


Definition noInvTick (s : StGlobal) :=
  match s with
  | ((st, x), ((sc, y), (sg, z))) =>
      ~ InvTick (st, x, (sc, y, (sg, z))) ->
      RState TrGlobal SiniTCG (st, x, (sc, y, (sg, z))) ->
      (st = Near /\ gt_Ck x kt1 \/ st = Inside) \/
      InvT (st, Inc x) /\ (sc = Sc2 /\ eq_Ck y kc1 \/ sc = Sc4) \/
      InvT (st, Inc x) /\
      InvC (sc, Inc y) /\ (sg = Lowering \/ sg = Raising /\ ge_Ck z kg2)
  end.


Lemma NoInvTick : forall s : StGlobal, noInvTick s.
Proof.
  intro s; elim s.
  intros st sc_sg; elim sc_sg; intros sc sg; elim st; elim sc; elim sg;
   intros.
  simpl in |- *; intros.
  elim (not_3_and H); [ intro no_invt | intro H1; decompose [and or] H1 ].
  elim (No_invT no_invt); intro H1; elim H1; intros st' x; rewrite st';
   rewrite st' in H0.
  generalize (INV_T_general (s1:=SiniTCG) Inv_SiniTCG H0); simpl in |- *;
   intro inv_near; inversion inv_near using cl_Inear; 
   intro lt_x_kt2.
  left; left; split; [ auto with * | apply (Trivial32 lt_x_kt2 x) ].
  auto with *.
  elim (No_invC H4); intro H5; elim H5; intros sc' y'; rewrite sc';
   rewrite sc' in H0.
  generalize (INV_C_general (s1:=SiniTCG) Inv_SiniTCG H0); simpl in |- *;
   intro inv_sc2; inversion inv_sc2 using cl_Isc2; 
   intro le_y_kc1.
  generalize (Trivial33 le_y_kc1 y'); intro.
  right; left; auto with *.
  auto with *.
  elim (No_invG H5); intro H6; elim H6; intros sg' z; rewrite sg';
   rewrite sg' in H0.
  right; right; auto with *.
  generalize (INV_G_general (s1:=SiniTCG) Inv_SiniTCG H0); simpl in |- *;
   intro inv_raising; inversion inv_raising using cl_Iraising; 
   intro lt_z_kg3.
  generalize (Trivial34 lt_z_kg3 z); intro.
  right; right; auto with *.
Qed.


Notation rsNext_In :=
  (fun (x : Clock) (gt_x_kt1 : gt_Ck x kt1) (lt_x_kt2 : lt_Ck x kt2)
     (sc_y : S_Ck SC) (sg_z : S_Ck SG) =>
   rsNext (rsIni TrGlobal (Near, x, (sc_y, sg_z)))
     (tGl_In (ttIn (x:=x) gt_x_kt1 lt_x_kt2) sc_y sg_z)) 
  (only parsing).

Notation rsNext_Down :=
  (fun (z : Clock) (lt_z_kg1 : lt_Ck z kg1) (st_x : S_Ck ST) (sc_y : S_Ck SC) =>
   rsNext (rsIni TrGlobal (st_x, (sc_y, (Lowering, z))))
     (tGl_Down (tgDown lt_z_kg1) st_x sc_y)) (only parsing).

Notation rsNext_Up :=
  (fun (z : Clock) (ge_z_kg2 : ge_Ck z kg2) (lt_z_kg3 : lt_Ck z kg3)
     (st_x : S_Ck ST) (sc_y : S_Ck SC) =>
   rsNext (rsIni TrGlobal (st_x, (sc_y, (Raising, z))))
     (tGl_Up (tgUp ge_z_kg2 lt_z_kg3) st_x sc_y)) (only parsing).

Notation rs_Next_Approach :=
  (fun (x y : Clock) (sg_z : S_Ck SG) =>
   rsNext StGlobal (rsIni StGlobal TrGlobal (Far, x, (Sc1, y, sg_z)))
     (tGl_Approach (ttApproach x) (tcApproach y) sg_z)) 
  (only parsing).

Notation rsNext_Exit :=
  (fun (x y : Clock) (lt_x_kt2 : lt_Ck x kt2) (sg_z : S_Ck SG) =>
   rsNext (rsIni TrGlobal (Inside, x, (Sc3, y, sg_z)))
     (tGl_Exit (ttExit lt_x_kt2) (tcExit y) sg_z)) 
  (only parsing).

Notation rsNext_Lower :=
  (fun (y z : Clock) (eq_y_kc1 : eq_Ck y kc1) (st_x : S_Ck ST) =>
   rsNext (rsIni TrGlobal (st_x, (Sc2, y, (Open, z))))
     (tGl_Lower (tcLower eq_y_kc1) (tgLower z) st_x)) 
  (only parsing).

Notation rsNext_Raise :=
  (fun (y z : Clock) (lt_y_kc2 : lt_Ck y kc2) (st_x : S_Ck ST) =>
   rsNext (rsIni TrGlobal (st_x, (Sc4, y, (Closed, z))))
     (tGl_Raise (tcRaise lt_y_kc2) (tgRaise z) st_x)) 
  (only parsing).


Ltac SplitTrans' :=
  intros s1 s2 l rs_s1 p_s1 tr_gl; generalize (rsNext rs_s1 tr_gl);
   generalize rs_s1; clear rs_s1; generalize p_s1; 
   clear p_s1; elim tr_gl.


Ltac SplitTrans'_Simpl :=
  SplitTrans';
   [ Simpl_In
   | Simpl_Down
   | Simpl_Up
   | Simpl_Approach
   | Simpl_Exit
   | Simpl_Lower
   | Simpl_Raise
   | Simpl_Tick ].


Ltac ExistsHere_ITick s :=
  apply exists_ with (tr := TrGlobal) (P := InvTick) (1 := rsIni TrGlobal s).


(* NonZeno proof for the system TCG *)

Lemma NonZeno :
 ForAll TrGlobal SiniTCG (fun s : StGlobal => Exists TrGlobal s InvTick).
Proof.
  BeginForAll.
  ExistsHere_ITick SiniTCG.
  Split3_Trivial.
  SplitTrans'_Simpl; generalize H0.
  rewrite
   (lema_Inv6 H0
      (or_intror (Inside = Near /\ gt_Ck x kc1) (refl_equal Inside)))
   .
  rewrite (lema_safeTCG H0 (refl_equal Inside)); intro rs_s2.
  apply StepsEX with (s2 := (Far, x, (Sc4, Reset, (Closed, b)))).
  apply
   ((fun (x y : Clock) (lt_x_kt2 : lt_Ck x kt2) (sg_z : S_Ck SG) =>
     rsNext (rsIni TrGlobal (Inside, x, (Sc3, y, sg_z)))
       (tGl_Exit (ttExit lt_x_kt2) (tcExit y) sg_z)) x b0 lt_x_kt2
      (Closed, b)).
  ExistsHere_ITick (Far, x, (Sc4, Reset, (Closed, b))).
  Split3_Trivial; (apply Isc4; apply Trivial18).
  elim (lema_Inv11 H0 (or_intror (Closed = Lowering) (refl_equal Closed)));
   intro sc_closed; rewrite sc_closed.
  elim a0; intro rs_s2.
  ExistsHere_ITick (Far, b0, (Sc3, b, (Closed, z))).
  Split3_Trivial.
  ExistsHere_ITick (Near, b0, (Sc3, b, (Closed, z))).
  Split3_Trivial.
  apply Inear.
  apply
   (Trivial19 lt_z_kg1 (lema_Inv5 rs_s2 (refl_equal Near) (refl_equal Sc3))
      (lema_Inv3 rs_s2 (or_introl (Near = Inside) (refl_equal Near)))).
  elim
   (Trivial20 lt_z_kg1
      (lema_Inv9 rs_s2
         (or_intror (Inside = Near /\ gt_Ck b0 kc1) (refl_equal Inside)))
      (lema_Inv3 rs_s2 (or_intror (Inside = Near) (refl_equal Inside)))
      (lema_InvInside rs_s2 (refl_equal Inside))).
  elim a0; intro rs_s2.
  generalize (INV_C_general (s1:=SiniTCG) Inv_SiniTCG rs_s2); simpl in |- *;
   intro inv_sc4; inversion inv_sc4 using cl_Isc4; 
   intro le_y0_kc2.
  apply StepsEX with (s2 := (Far, b0, (Sc1, b, (Raising, Reset)))).
  apply
   ((fun (y z : Clock) (lt_y_kc2 : lt_Ck y kc2) (st_x : S_Ck ST) =>
     rsNext (rsIni TrGlobal (st_x, (Sc4, y, (Closed, z))))
       (tGl_Raise (tcRaise lt_y_kc2) (tgRaise z) st_x)) b z le_y0_kc2
      (Far, b0)).
  ExistsHere_ITick (Far, b0, (Sc1, b, (Raising, Reset))).
  Split3_Trivial; (apply Iraising; apply Trivial21).
  elim (lema_Inv4 rs_s2 (refl_equal Near)); intro sc_near;
   rewrite sc_near in sc_closed; discriminate.
  elim
   (Trivial20 lt_z_kg1
      (lema_Inv9 rs_s2
         (or_intror (Inside = Near /\ gt_Ck b0 kc1) (refl_equal Inside)))
      (lema_Inv3 rs_s2 (or_intror (Inside = Near) (refl_equal Inside)))
      (lema_InvInside rs_s2 (refl_equal Inside))).
  elim a0.
  intro rs_s2; generalize rs_s2;
   rewrite
    (lema_Inv2 rs_s2 (refl_equal Far)
       (or_introl (Open = Raising) (refl_equal Open)))
    ; intro rs_s2fin.
  ExistsHere_ITick (Far, b0, (Sc1, b, (Open, z))).
  Split3_Trivial.
  intro rs_s2; generalize rs_s2; elim (lema_Inv4 rs_s2 (refl_equal Near));
   intro sc_near; rewrite sc_near. 
  intro rs_s2'; generalize (INV_C_general (s1:=SiniTCG) Inv_SiniTCG rs_s2');
   simpl in |- *; intro inv_sc2; inversion inv_sc2 using cl_Isc2;
   intro le_y0_kc1.
  elim (Trivial22 le_y0_kc1); intro.
  ExistsHere_ITick (Near, b0, (Sc2, b, (Open, z))).
  split; [ apply Inear | split; [ apply Isc2 | auto with * ] ]. 
  apply
   (Trivial23 H1
      (lema_Inv3 rs_s2' (or_introl (Near = Inside) (refl_equal Near)))).
  apply (Trivial24 H1).
  apply StepsEX with (s2 := (Near, b0, (Sc3, b, (Lowering, Reset)))).
  apply
   ((fun (y z : Clock) (eq_y_kc1 : eq_Ck y kc1) (st_x : S_Ck ST) =>
     rsNext (rsIni TrGlobal (st_x, (Sc2, y, (Open, z))))
       (tGl_Lower (tcLower eq_y_kc1) (tgLower z) st_x)) b z H1 
      (Near, b0)).
  ExistsHere_ITick (Near, b0, (Sc3, b, (Lowering, Reset))).
  split; [ apply Inear | split; [ auto with * | apply Ilowering ] ].
  apply
   (Trivial25 H1
      (lema_Inv3 rs_s2' (or_introl (Near = Inside) (refl_equal Near)))).
  apply Trivial26.
  intro rs_s2fin;
   elim
    (lema_Inv1 rs_s2fin (or_introl (Near = Inside) (refl_equal Near))
       (refl_equal Sc3)); intro; discriminate.
  intro rs_s2; Generalize_Easy (lema_safeTCG rs_s2 (refl_equal Inside)).
  elim (lema_Inv10 H0 (or_intror (Sc2 = Sc1) (refl_equal Sc2))); intros H1;
   rewrite H1; intro rs_s2. 
  ExistsHere_ITick (Near, Reset, (Sc2, Reset, (Open, b))).
  split;
   [ apply Inear; apply Trivial27
   | split; [ apply Isc2; apply Trivial28 | auto with * ] ].
  generalize (INV_G_general (s1:=SiniTCG) Inv_SiniTCG rs_s2); simpl in |- *;
   intro inv_raising; inversion inv_raising using cl_Iraising;
   intro lt_y1_kg3.
  elim (Trivial29 lt_y1_kg3); intro.
  ExistsHere_ITick (Near, Reset, (Sc2, Reset, (Raising, b))).
  split;
   [ apply Inear; apply Trivial27
   | split;
      [ apply Isc2; apply Trivial28 | apply Iraising; apply (Trivial30 H2) ] ].
  apply StepsEX with (s2 := (Near, Reset, (Sc2, Reset, (Open, b)))). 
  elim H2; intros H3 H4.
  apply
   ((fun (z : Clock) (ge_z_kg2 : ge_Ck z kg2) (lt_z_kg3 : lt_Ck z kg3)
       (st_x : S_Ck ST) (sc_y : S_Ck SC) =>
     rsNext (rsIni TrGlobal (st_x, (sc_y, (Raising, z))))
       (tGl_Up (tgUp ge_z_kg2 lt_z_kg3) st_x sc_y)) b H3 H4 
      (Near, Reset) (Sc2, Reset)).
  ExistsHere_ITick (Near, Reset, (Sc2, Reset, (Open, b))).
  split;
   [ apply Inear; apply Trivial27
   | split; [ apply Isc2; apply Trivial28 | auto with * ] ].
  elim a; intro rs_s2.
  ExistsHere_ITick (Far, x, (Sc4, Reset, (Open, b))).
  Split3_Trivial.
  apply Isc4; apply Trivial18.
  generalize (INV_G_general (s1:=SiniTCG) Inv_SiniTCG rs_s2); simpl in |- *;
   intro inv_lowering; inversion inv_lowering using cl_Ilowering;
   intro lt_y1_kg1.
  apply StepsEX with (s2 := (Far, x, (Sc4, Reset, (Closed, b)))).
  apply
   ((fun (z : Clock) (lt_z_kg1 : lt_Ck z kg1) (st_x : S_Ck ST)
       (sc_y : S_Ck SC) =>
     rsNext (rsIni TrGlobal (st_x, (sc_y, (Lowering, z))))
       (tGl_Down (tgDown lt_z_kg1) st_x sc_y)) b lt_y1_kg1 
      (Far, x) (Sc4, Reset)).
  ExistsHere_ITick (Far, x, (Sc4, Reset, (Closed, b))).
  Split3_Trivial.
  apply Isc4; apply Trivial18.
  ExistsHere_ITick (Far, x, (Sc4, Reset, (Closed, b))).
  Split3_Trivial.
  apply Isc4; apply Trivial18.
  Generalize_Easy
   (lema_Inv2 rs_s2 (refl_equal Far)
      (or_intror (Raising = Open) (refl_equal Raising))).
  intro rs_s2; ExistsHere_ITick (a, b, (Sc3, y, (Lowering, Reset))).
  split;
   [ generalize rs_s2; elim a; intro rs_s2'
   | split; [ auto with * | apply Ilowering; apply Trivial26 ] ].
  auto with *.
  apply Inear;
   apply
    (Trivial25 eq_y_kc1
       (lema_Inv3 rs_s2' (or_introl (Near = Inside) (refl_equal Near)))).
  Generalize_Easy (lema_safeTCG rs_s2' (refl_equal Inside)).
  intro rs_s2; ExistsHere_ITick (a, b, (Sc1, y, (Raising, Reset))).
  split;
   [ generalize rs_s2; elim a; intro rs_s2'
   | split; [ auto with * | apply Iraising; apply Trivial21 ] ].
  auto with *.
  Simpl_or (lema_Inv4 rs_s2' (refl_equal Near)).
  Generalize_Easy (lema_safeTCG rs_s2' (refl_equal Inside)).
  intro; elim (classic (InvTick (s4, Inc x, (s3, Inc y, (s0, Inc z)))));
   intro inv_tick.
  ExistsHere_ITick (s4, Inc x, (s3, Inc y, (s0, Inc z))); auto with *.
  generalize H3;
   elim (NoInvTick (s4, Inc x, (s3, Inc y, (s0, Inc z))) inv_tick H3).
  intro no_st; decompose [and or] no_st; [ rewrite H6 | rewrite H5 ].
  intro rs_near; generalize (INV_T_general (s1:=SiniTCG) Inv_SiniTCG rs_near);
   simpl in |- *; intro inv_near; inversion inv_near using cl_Inear;
   intro lt_incx_kt2.
  generalize
   ((fun (x : Clock) (gt_x_kt1 : gt_Ck x kt1) (lt_x_kt2 : lt_Ck x kt2)
       (sc_y : S_Ck SC) (sg_z : S_Ck SG) =>
     rsNext (rsIni TrGlobal (Near, x, (sc_y, sg_z)))
       (tGl_In (ttIn (x:=x) gt_x_kt1 lt_x_kt2) sc_y sg_z)) 
      (Inc x) H7 lt_incx_kt2 (s3, Inc y) (s0, Inc z)); 
   intro rs_inside.
  generalize rs_near; generalize rs_inside;
   rewrite
    (lema_Inv6 (RState_Trans rs_near rs_inside)
       (or_intror (Inside = Near /\ gt_Ck (Inc x) kc1) (refl_equal Inside)))
    .
  rewrite (lema_safeTCG (RState_Trans rs_near rs_inside) (refl_equal Inside)).
  intros;
   apply StepsEX with (s2 := (Far, Inc x, (Sc4, Reset, (Closed, Inc z)))).
  apply
   (RState_Trans rs_inside0
      ((fun (x y : Clock) (lt_x_kt2 : lt_Ck x kt2) (sg_z : S_Ck SG) =>
        rsNext (rsIni TrGlobal (Inside, x, (Sc3, y, sg_z)))
          (tGl_Exit (ttExit lt_x_kt2) (tcExit y) sg_z)) 
         (Inc x) (Inc y) lt_incx_kt2 (Closed, Inc z))).
  ExistsHere_ITick (Far, Inc x, (Sc4, Reset, (Closed, Inc z))).
  Split3_Trivial; apply Isc4; apply Trivial18.
  intro rs_inside; generalize rs_inside;
   rewrite (lema_safeTCG rs_inside (refl_equal Inside)); 
   intro rs_inside0.
  generalize rs_inside0;
   rewrite
    (lema_Inv6 rs_inside0
       (or_intror (Inside = Near /\ gt_Ck (Inc x) kc1) (refl_equal Inside)))
    ; intro rs_inside1.
  apply StepsEX with (s2 := (Far, Inc x, (Sc4, Reset, (Closed, Inc z)))).
  generalize (INV_T_general (s1:=SiniTCG) Inv_SiniTCG rs_inside0);
   simpl in |- *; intro inv_inside; inversion inv_inside using cl_Iinside;
   intro lt_incx_kt2.
  apply
   ((fun (x y : Clock) (lt_x_kt2 : lt_Ck x kt2) (sg_z : S_Ck SG) =>
     rsNext (rsIni TrGlobal (Inside, x, (Sc3, y, sg_z)))
       (tGl_Exit (ttExit lt_x_kt2) (tcExit y) sg_z)) 
      (Inc x) (Inc y) lt_incx_kt2 (Closed, Inc z)).
  ExistsHere_ITick (Far, Inc x, (Sc4, Reset, (Closed, Inc z))).
  Split3_Trivial; apply Isc4; apply Trivial18.
  intro no_sc_sg; elim no_sc_sg;
   [ intro st_no_sc; decompose [and or] st_no_sc | intro no_sg ].
  rewrite H6; rewrite H6 in rs_s1.
  elim (lema_Inv10 rs_s1 (or_intror (Sc2 = Sc1) (refl_equal Sc2))); intro sg';
   rewrite sg'.
  intro rs_s2;
   apply StepsEX with (s2 := (s4, Inc x, (Sc3, Inc y, (Lowering, Reset)))).
  apply
   ((fun (y z : Clock) (eq_y_kc1 : eq_Ck y kc1) (st_x : S_Ck ST) =>
     rsNext (rsIni TrGlobal (st_x, (Sc2, y, (Open, z))))
       (tGl_Lower (tcLower eq_y_kc1) (tgLower z) st_x)) 
      (Inc y) (Inc z) H8 (s4, Inc x)).
  ExistsHere_ITick (s4, Inc x, (Sc3, Inc y, (Lowering, Reset))).
  Split3_Trivial; apply Ilowering; apply Trivial26.
  intro rs_s2;
   apply StepsEX with (s2 := (s4, Inc x, (Sc2, Inc y, (Open, Inc z)))).
  generalize (lema_Inv12 rs_s2 (refl_equal Sc2)); intro ge_incz_incy.
  generalize (INV_G_general (s1:=SiniTCG) Inv_SiniTCG rs_s2); simpl in |- *;
   intro inv_raising; inversion inv_raising using cl_Iraising;
   intro lt_incz_kg3.
  apply
   ((fun (z : Clock) (ge_z_kg2 : ge_Ck z kg2) (lt_z_kg3 : lt_Ck z kg3)
       (st_x : S_Ck ST) (sc_y : S_Ck SC) =>
     rsNext (rsIni TrGlobal (st_x, (sc_y, (Raising, z))))
       (tGl_Up (tgUp ge_z_kg2 lt_z_kg3) st_x sc_y)) 
      (Inc z) (Trivial31 H8 ge_incz_incy) lt_incz_kg3 
      (s4, Inc x) (Sc2, Inc y)).
  apply StepsEX with (s2 := (s4, Inc x, (Sc3, Inc y, (Lowering, Reset)))).
  apply
   ((fun (y z : Clock) (eq_y_kc1 : eq_Ck y kc1) (st_x : S_Ck ST) =>
     rsNext (rsIni TrGlobal (st_x, (Sc2, y, (Open, z))))
       (tGl_Lower (tcLower eq_y_kc1) (tgLower z) st_x)) 
      (Inc y) (Inc z) H8 (s4, Inc x)).
  ExistsHere_ITick (s4, Inc x, (Sc3, Inc y, (Lowering, Reset))).
  Split3_Trivial; apply Ilowering; apply Trivial26.
  rewrite H7; intro rs_s2; generalize rs_s2;
   generalize (lema_Inv14 rs_s2 (refl_equal Sc4)); 
   intro far_closed; elim far_closed; intros far closed; 
   rewrite closed.
  intro rs_s2';
   apply StepsEX with (s2 := (s4, Inc x, (Sc1, Inc y, (Raising, Reset)))).
  generalize (INV_C_general (s1:=SiniTCG) Inv_SiniTCG rs_s2'); simpl in |- *;
   intro inv_sc4; inversion inv_sc4 using cl_Isc4; 
   intro le_incy_kc2.
  apply
   ((fun (y z : Clock) (lt_y_kc2 : lt_Ck y kc2) (st_x : S_Ck ST) =>
     rsNext (rsIni TrGlobal (st_x, (Sc4, y, (Closed, z))))
       (tGl_Raise (tcRaise lt_y_kc2) (tgRaise z) st_x)) 
      (Inc y) (Inc z) le_incy_kc2 (s4, Inc x)).
  ExistsHere_ITick (s4, Inc x, (Sc1, Inc y, (Raising, Reset))).
  Split3_Trivial; apply Iraising; apply Trivial21.
  decompose [and or] no_sg.
  rewrite H6; intro rs_s2;
   generalize (INV_G_general (s1:=SiniTCG) Inv_SiniTCG rs_s2); 
   simpl in |- *; intro inv_lowering;
   inversion inv_lowering using cl_Ilowering; intro lt_incz_kg1.
  apply StepsEX with (s2 := (s4, Inc x, (s3, Inc y, (Closed, Inc z)))).
  apply
   ((fun (z : Clock) (lt_z_kg1 : lt_Ck z kg1) (st_x : S_Ck ST)
       (sc_y : S_Ck SC) =>
     rsNext (rsIni TrGlobal (st_x, (sc_y, (Lowering, z))))
       (tGl_Down (tgDown lt_z_kg1) st_x sc_y)) (Inc z) lt_incz_kg1
      (s4, Inc x) (s3, Inc y)).
  ExistsHere_ITick (s4, Inc x, (s3, Inc y, (Closed, Inc z))).
  Split3_Trivial.
  rewrite H8; intro rs_s2;
   apply StepsEX with (s2 := (s4, Inc x, (s3, Inc y, (Open, Inc z)))).
  generalize (INV_G_general (s1:=SiniTCG) Inv_SiniTCG rs_s2); simpl in |- *;
   intro inv_raising; inversion inv_raising using cl_Iraising;
   intro lt_incz_kg3.
  apply
   ((fun (z : Clock) (ge_z_kg2 : ge_Ck z kg2) (lt_z_kg3 : lt_Ck z kg3)
       (st_x : S_Ck ST) (sc_y : S_Ck SC) =>
     rsNext (rsIni TrGlobal (st_x, (sc_y, (Raising, z))))
       (tGl_Up (tgUp ge_z_kg2 lt_z_kg3) st_x sc_y)) 
      (Inc z) H9 lt_incz_kg3 (s4, Inc x) (s3, Inc y)).
  ExistsHere_ITick (s4, Inc x, (s3, Inc y, (Open, Inc z))).
  Split3_Trivial.
Qed.


(* 
Other specification of NonZeno: 

Definition S_true := [s:StGlobal] True. 
Lemma NonZeno : (ForAll_TCG SiniTCG ([s:StGlobal] (Exists_T TrGlobal s S_true (eq_Ck tick)))).
*)

