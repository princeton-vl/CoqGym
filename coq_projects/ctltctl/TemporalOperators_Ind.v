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


Set Implicit Arguments.
Unset Strict Implicit.

Require Import time_clocks. (* Temporal notions for discrete time *)


Section TemporalOperators_Ind.

(*** Temporal operators with inductive types: definition and properties ***)

  Variable Label : Set.               (* labels: dicrete transitions *) 
  Variable S : Set.               (* states                      *) 
  Variable tr : S -> Label -> S -> Prop. (* transitions                 *)
  Variable inv : S -> Prop.         (* location invariants         *)
  Variable inc : S -> Instant -> S. (* increase clocks of states   *) 


  (*  Reachable states from "Sini" with transitions "tr"  *)

  Inductive RState (Sini : S) : S -> Prop :=
    | rsIni : RState Sini Sini
    | rsNextTick :
        forall s : S,
        RState Sini s -> inv (inc s tick) -> RState Sini (inc s tick)
    | rsNextDisc :
        forall (s1 s2 : S) (l : Label),
        RState Sini s1 -> tr s1 l s2 -> inv s2 -> RState Sini s2.


  (*  Reachable states from "Sini" with transitions "tr" in time units  *)

  Inductive RState_T (Sini : S) : S -> Instant -> Prop :=
    | rsIni_T : RState_T Sini Sini time0
    | rsNextTick_T :
        forall (s : S) (t : Instant),
        RState_T Sini s t ->
        inv (inc s tick) -> RState_T Sini (inc s tick) (Inc t)
    | rsNextDisc_T :
        forall (s1 s2 : S) (l : Label) (t : Instant),
        RState_T Sini s1 t -> tr s1 l s2 -> inv s2 -> RState_T Sini s2 t.  


  (**************************************************************************)
  (*                       Invariants and Reachability                      *)
  (**************************************************************************)  

  (*  Init => FA[] P  *)

  Definition ForAll (Sini : S) (P : S -> Prop) :=
    forall s : S, RState Sini s -> P s. 


  (*  Init => FA[](bound t) P  *)

  Definition ForAll_T (Sini : S) (P : S -> Prop) (bound : Instant -> Prop) :=
    forall (s : S) (t : Instant), bound t -> RState_T Sini s t -> P s.


  (*  Init => EX<> P  *)

  Inductive Exists (Sini : S) (P : S -> Prop) : Prop :=
      exists_ : forall s : S, RState Sini s -> P s -> Exists Sini P.


  (*  Init => EX<>(bound t) P  *)

  Inductive Exists_T (Sini : S) (P : S -> Prop) (bound : Instant -> Prop) :
  Prop :=
      exists_T :
        forall (s : S) (t : Instant),
        bound t -> RState_T Sini s t -> P s -> Exists_T Sini P bound.


  (**************************************************************************)
  (*                            Some Properties                             *)
  (**************************************************************************)

	  Theorem Mon_I :
    forall (Sini : S) (Pg Pp : S -> Prop),
    ForAll Sini Pg -> (forall s : S, Pg s -> Pp s) -> ForAll Sini Pp.  
  Proof.  
    unfold ForAll in |- *; intros.
    apply H0.
    apply H; assumption.
  Qed.


  Theorem Mon_I_T :
   forall (Sini : S) (Pg Pp : S -> Prop) (bound : Instant -> Prop),
   ForAll_T Sini Pg bound ->
   (forall s : S, Pg s -> Pp s) -> ForAll_T Sini Pp bound.  
  Proof. 
    unfold ForAll_T in |- *; intros.
    apply H0.
    apply (H s t); assumption.
  Qed.


 Theorem Conj :
  forall (Sini : S) (P1 P2 : S -> Prop),
  ForAll Sini P1 -> ForAll Sini P2 -> ForAll Sini (fun s : S => P1 s /\ P2 s).
  Proof.
    unfold ForAll in |- *; intros.
    split; [ apply H | apply H0 ]; assumption.
  Qed.


  Theorem Conj_T :
   forall (Sini : S) (P1 P2 : S -> Prop) (bound : Instant -> Prop),
   ForAll_T Sini P1 bound ->
   ForAll_T Sini P2 bound -> ForAll_T Sini (fun s : S => P1 s /\ P2 s) bound.
  Proof.
    unfold ForAll_T in |- *; intros.
    split; [ apply (H s t) | apply (H0 s t) ]; assumption.
  Qed.
 

  Theorem Mon_I_EX :
   forall (Sini : S) (Pg Pp : S -> Prop),
   Exists Sini Pg -> (forall s : S, Pg s -> Pp s) -> Exists Sini Pp.
  Proof.
    intros.
    inversion_clear H.
    apply (exists_ H1 (H0 s H2)).
  Qed.


  Theorem Mon_I_EX_T :
   forall (Sini : S) (Pg Pp : S -> Prop) (bound : Instant -> Prop),
   Exists_T Sini Pg bound ->
   (forall s : S, Pg s -> Pp s) -> Exists_T Sini Pp bound.
  Proof.
    intros.
    inversion_clear H.
    apply (exists_T H1 H2 (H0 s H3)).
  Qed.
   

  Lemma RState_Trans :
   forall s1 s2 s3 : S, RState s1 s2 -> RState s2 s3 -> RState s1 s3.
  Proof.
    simple induction 2; intros.
    assumption.
    apply rsNextTick; trivial.
    apply (rsNextDisc H2 H3 H4).
  Qed.

  
  Lemma RState_Trans_T :
   forall (s1 s2 s3 : S) (t1 t2 : Instant),
   RState_T s1 s2 t1 -> RState_T s2 s3 t2 -> RState_T s1 s3 (plus_Ck t1 t2).
  Proof.
    simple induction 2; unfold plus_Ck in |- *; intros.
    rewrite (plus_comm t1 time0); unfold time0 in |- *; simpl in |- *;
     assumption.
    unfold Inc in |- *; unfold plus_Ck in |- *;
     rewrite (plus_assoc t1 t tick).
    apply (rsNextTick_T H2 H3).
    apply (rsNextDisc_T H2 H3 H4).
  Qed.

  Theorem StepsEX :
   forall (s1 s2 : S) (P : S -> Prop),
   RState s1 s2 -> Exists s2 P -> Exists s1 P.
  Proof.
    intros.
    inversion H0.
    apply (exists_ (RState_Trans H H1) H2).
  Qed.


  Require Import Classical.

  Theorem ForAll_EX :
   forall (Sini : S) (P : S -> Prop),
   ForAll Sini P <-> ~ Exists Sini (fun s : S => ~ P s).
  Proof.
    unfold not in |- *; unfold ForAll in |- *; red in |- *; intros; split;
     intros.
    inversion H0.
    apply (H2 (H s H1)).
    elim (classic (P s));
     [ trivial | intro; absurd (Exists Sini (fun s : S => P s -> False)) ].
    assumption.
    apply exists_ with (1 := H0); assumption.
  Qed.


  Theorem ForAll_EX_T :
   forall (Sini : S) (P : S -> Prop) (bound : Instant -> Prop),
   ForAll_T Sini P bound <-> ~ Exists_T Sini (fun s : S => ~ P s) bound.
  Proof.
    unfold not in |- *; unfold ForAll_T in |- *; red in |- *; intros; split;
     intros.
    inversion H0.
    apply (H3 (H s t H1 H2)).
    elim (classic (P s));
     [ trivial
     | intro; absurd (Exists_T Sini (fun s : S => P s -> False) bound) ].
    assumption.
    apply exists_T with (2 := H1); assumption.
  Qed.


  (**************************************************************************)
  (*                        Other definitions                               *)
  (**************************************************************************)

  (*  FA[] (Q => FA[] P)  *)

  Definition ForAll_from (Sini : S) (Q P : S -> Prop) :=
    ForAll Sini (fun s : S => Q s -> ForAll s P). 
     (* (s:S) (RState Sini s) -> (Q s) -> (ForAll s P). *)


  (*  FA[] (Q => FA[](bound t) P)  *)

  Definition ForAll_from_T (Sini : S) (Q P : S -> Prop)
    (bound : Instant -> Prop) :=
    ForAll Sini (fun s : S => Q s -> ForAll_T s P bound). 
     (* (s:S) (RState Sini s) -> (Q s) -> (ForAll_T s P bound). *)

  
  (*  FA[] (Q => EX<> P)  *)

  Definition Exists_from (Sini : S) (Q P : S -> Prop) :=
    ForAll Sini (fun s : S => Q s -> Exists s P). 
     (* (s:S) (RState Sini s) -> (Q s) -> (Exists s P). *)


  (*  FA[] (Q => EX<>(bound t) P)  *)

  Definition Exists_from_T (Sini : S) (Q P : S -> Prop)
    (bound : Instant -> Prop) :=
    ForAll Sini (fun s : S => Q s -> Exists_T s P bound). 
     (* (s:S) (RState Sini s) -> (Q s) -> (Exists_T s P bound). *)


End TemporalOperators_Ind.