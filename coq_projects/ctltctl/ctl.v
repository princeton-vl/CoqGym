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

Require Export Streams.
Require Import time_clocks. (* Temporal notions for discrete time *)

Infix "^" := Cons.

Section TemporalOperators_CTL.

(*** operators CTL with co-inductives types: definitions and properties ***)

  Variable Label : Set.               (* labels: dicrete transitions *) 
  Variable S : Set.               (* states                      *) 
  Variable tr : S -> Label -> S -> Prop. (* transitions                 *)
  Variable inv : S -> Prop.         (* location invariants         *)
  Variable inc : S -> Instant -> S. (* increase clocks of states   *) 
 
  Notation SPath := (Stream S) (only parsing).
  

  CoInductive ForAllS (P : Stream S -> Prop) : Stream S -> Prop :=
      forallS :
        forall (x : Stream S) (s : S),
        P (s ^ x) -> ForAllS P x -> ForAllS P (s ^ x).

  Inductive ExistsS (P : Stream S -> Prop) : Stream S -> Prop :=
    | Here : forall x : Stream S, P x -> ExistsS P x
    | Further :
        forall (x : Stream S) (s : S), ExistsS P x -> ExistsS P (s ^ x).


  (* Ejecution traces *)
  
  CoInductive isTrace : Stream S -> Prop :=
    | isTraceTick :
        forall (x : Stream S) (s : S),
        inv (inc s tick) ->
        isTrace (inc s tick ^ x) -> isTrace (s ^ inc s tick ^ x)
    | isTraceDisc :
        forall (x : Stream S) (s1 s2 : S) (l : Label),
        tr s1 l s2 -> inv s2 -> isTrace (s2 ^ x) -> isTrace (s1 ^ s2 ^ x).  

  Definition isTraceFrom (Sini : S) (x : Stream S) :=
    Sini = hd x /\ isTrace x.
  

  (* operator Until *)

  Inductive Until (P Q : Stream S -> Prop) : Stream S -> Prop :=
    | UntilFurther :
        forall (s : S) (x : Stream S),
        P (s ^ x) -> Until P Q x -> Until P Q (s ^ x)
    | UntilHere : forall x : Stream S, Q x -> Until P Q x.

  Inductive EX_Until (Sini : S) (P Q : Stream S -> Prop) : Prop :=
      ExUntil :
        forall x : Stream S,
        isTraceFrom Sini x -> Until P Q x -> EX_Until Sini P Q.

  Definition FA_Until (Sini : S) (P Q : Stream S -> Prop) :=
    forall x : Stream S, isTraceFrom Sini x -> Until P Q x.


  (* Init => FA[] P *)

  Definition Always (Sini : S) (P : Stream S -> Prop) :=
    forall x : Stream S, isTraceFrom Sini x -> ForAllS P x.


  (* Init => FA<> P *)

  Definition Inevitable (Sini : S) (P : Stream S -> Prop) :=
    forall x : Stream S, isTraceFrom Sini x -> ExistsS P x.


  (* Init => EX<> P *)

  Inductive Posible (Sini : S) (P : Stream S -> Prop) : Prop :=
      posible :
        forall x : Stream S,
        isTraceFrom Sini x -> ExistsS P x -> Posible Sini P.


  (* Init => EX[] P *)

  Inductive SafePath (Sini : S) (P : Stream S -> Prop) : Prop :=
      safePath :
        forall x : Stream S,
        isTraceFrom Sini x -> ForAllS P x -> SafePath Sini P.


  (**************************************************************************)
  (*                          Some Properties                               *)
  (**************************************************************************)

  Theorem Equiv1 :
   forall (Sini : S) (P : Stream S -> Prop),
   Posible Sini P <-> EX_Until Sini (fun _ : Stream S => True) P. 
  Proof.
    unfold iff in |- *; intros; split; intro.
    inversion_clear H.
    apply ExUntil with (P := fun _ : Stream S => True) (1 := H0).
    elim H1; intros.
    constructor 2; assumption.
    constructor 1; trivial.
    inversion_clear H.
    apply posible with (1 := H0).
    elim H1; intros.
    constructor 2; assumption.
    constructor 1; assumption.
  Qed.


  Theorem Equiv2 :
   forall (Sini : S) (P : Stream S -> Prop),
   Inevitable Sini P <-> FA_Until Sini (fun _ : Stream S => True) P.
  Proof.
    unfold iff, Inevitable, FA_Until in |- *; intros; split; intros.
    elim (H x H0); intros.
    constructor 2; assumption.
    constructor 1; trivial.
    elim (H x H0); intros.
    constructor 2; assumption.
    constructor 1; assumption.
  Qed.


  Lemma ConsTrace :
   forall (s1 s2 : S) (x z : Stream S),
   isTraceFrom s2 z ->
   isTraceFrom s1 (s1 ^ s2 ^ x) -> isTraceFrom s1 (s1 ^ z).
  Proof.
    unfold isTraceFrom in |- *; simpl in |- *.
    simple destruct z; simple destruct 1; simple destruct 3; simpl in |- *;
     intros.
    compute in H0; rewrite H0 in H4.
    inversion_clear H4 in H1.
    split; [ trivial | apply (isTraceTick H5 H1) ].
    split; [ trivial | apply (isTraceDisc H5 H6 H1) ].
  Qed.


  Lemma notPosible :
   forall (P : Stream S -> Prop) (s1 : S),
   ~ Posible s1 P ->
   forall (z : Stream S) (s2 : S),
   isTraceFrom s1 (s1 ^ s2 ^ z) -> ~ Posible s2 P.
  Proof.
    unfold not at 2 in |- *; intros.
    elim H1; intros.
    apply H; cut (isTraceFrom s1 (s1 ^ x)). 
    intro H4; apply (posible (P:=P) H4).
    apply Further; assumption.
    apply ConsTrace with (1 := H2) (2 := H0); assumption.
  Qed.

  Require Import Classical.

  Theorem Equiv3 :
   forall (Sini : S) (P : Stream S -> Prop),
   Always Sini P <-> ~ Posible Sini (fun s : Stream S => ~ P s).
  Proof.
    unfold iff, Always, not in |- *; intros; split.
    intros H H0; inversion_clear H0.
    generalize (H x H1); elim H2; intros.
    inversion_clear H3 in H0.
    apply (H0 H4).
    inversion_clear H4.
    apply (H3 H6).
    generalize Sini; cofix u.
    simple destruct x; intros; constructor.
    elim (classic (P (s ^ s0))); [ trivial | intros ].
    absurd (Posible Sini0 (fun s : Stream S => ~ P s)).
    assumption.
    apply posible with (1 := H0).
    constructor 1; assumption.
    elim H0; simpl in |- *; intros.
    apply (u (hd s0)); intros.
    generalize H0; clear H0; generalize H3; clear H3.
    rewrite <- H1; case s0; simpl in |- *; intros.
    apply (notPosible (P:=fun s : Stream S => ~ P s) H H0); assumption.
    inversion_clear H2; simpl in |- *.
    unfold isTraceFrom in |- *; split; trivial.
    unfold isTraceFrom in |- *; split; trivial.
  Qed.


  Lemma not_EX :
   forall (P : Stream S -> Prop) (x : Stream S) (s : S),
   ~ ExistsS P (s ^ x) -> ~ ExistsS P x.
  Proof.
      unfold not in |- *; intros.
      apply (H (Further s H0)).
  Qed.


  Theorem Equiv4 :
   forall (Sini : S) (P : Stream S -> Prop),
   SafePath Sini P <-> ~ Inevitable Sini (fun s : Stream S => ~ P s).
  Proof.
    unfold iff, Inevitable, not in |- *; intros; split.
    intro sp; inversion sp; intros.
    generalize H0; elim (H1 x H); intros.
    inversion_clear H3 in H2.
    apply (H2 H4).
    apply H3; inversion_clear H4; assumption.
    intro H;
     elim
      (not_all_ex_not (Stream S)
         (fun x : Stream S =>
          isTraceFrom Sini x -> ExistsS (fun s : Stream S => P s -> False) x)
         H).
    intros.
    generalize
     (not_imply_elim2 (isTraceFrom Sini x)
        (ExistsS (fun s : Stream S => ~ P s) x) H0).
    generalize
     (not_imply_elim (isTraceFrom Sini x)
        (ExistsS (fun s : Stream S => ~ P s) x) H0); 
     intros.
    apply safePath with (1 := H1).
    generalize H1; clear H1; generalize H2; clear H2.
    generalize x; generalize Sini; cofix u.
    simple destruct x0; intros; constructor.
    elim (classic (P (s ^ s0))); [ trivial | intro ].
    elim (H2 (Here (P:=fun s : Stream S => ~ P s) H3)).
    apply u with (Sini := hd s0).
    generalize H2; clear H2; case s0; unfold not in |- *; intros.
    apply (not_EX H2 H3).
    elim H1; intros ig trace; inversion_clear trace.
    unfold isTraceFrom in |- *; split; trivial.
    unfold isTraceFrom in |- *; split; trivial.
  Qed.


  Theorem Mon_I_S :
   forall (x : Stream S) (Pg Pp : Stream S -> Prop),
   ForAllS Pg x -> (forall s : Stream S, Pg s -> Pp s) -> ForAllS Pp x.
  Proof.
    cofix u; intro x; case x; intros.
    case H; constructor.
    apply (H0 (s1 ^ x0) H1).
    apply (u x0 Pg Pp H2 H0).
  Qed.


  Theorem Conj_S :
   forall (x : Stream S) (P1 P2 : Stream S -> Prop),
   ForAllS P1 x ->
   ForAllS P2 x -> ForAllS (fun s : Stream S => P1 s /\ P2 s) x.
  Proof. 
    cofix u; intro x; case x; intros. 
    inversion_clear H; inversion_clear H0.
    constructor; [ split | apply (u s0) ]; assumption.
  Qed.


  Theorem Mon_I_EX_S :
   forall (x : Stream S) (Pg Pp : Stream S -> Prop),
   ExistsS Pg x -> (forall s : Stream S, Pg s -> Pp s) -> ExistsS Pp x.
  Proof.
    simple induction 1; intros.
    constructor 1; apply (H1 x0 H0).
    constructor 2; apply (H1 H2). 
  Qed.


  Theorem OneStep_EX :
   forall (x : Stream S) (P : Stream S -> Prop),
   ExistsS P x -> forall s : S, ExistsS P (s ^ x).
  Proof.
    intros; constructor 2; assumption.
  Qed.


End TemporalOperators_CTL.




