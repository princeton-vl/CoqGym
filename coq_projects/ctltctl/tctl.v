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
Require Import ctl.

Infix "^" := Cons.

Section TemporalOperators_TCTL.

(*** operators TCTL with co-inductives types: definitions and properties ***)
  Variable Label : Set.               (* labels: dicrete transitions *) 
  Variable S : Set.               (* states                      *) 
  Variable tr : S -> Label -> S -> Prop. (* transitions                 *)
  Variable inv : S -> Prop.         (* location invariants         *)
  Variable inc : S -> Instant -> S. (* increase clocks of states   *)  
  Variable bound : Instant -> Prop.     (* Belonging to temporal intervals *)
 
  Notation State_T := (S * Instant)%type (only parsing).
  Notation SPath_T := (Stream (S * Instant)) (only parsing).


  (* Ejecution traces *)

  CoInductive isTrace_T : Stream (S * Instant) -> Prop :=
    | isTraceTick_T :
        forall (x : Stream (S * Instant)) (s : S) (t : Instant),
        inv (inc s tick) ->
        isTrace_T ((inc s tick, Inc t) ^ x) ->
        isTrace_T ((s, t) ^ (inc s tick, Inc t) ^ x)
    | isTraceDisc_T :
        forall (x : Stream (S * Instant)) (s1 s2 : S) 
          (t : Instant) (l : Label),
        tr s1 l s2 ->
        inv s2 ->
        isTrace_T ((s2, t) ^ x) -> isTrace_T ((s1, t) ^ (s2, t) ^ x). 

  Definition isTraceFrom_T (Sini : S * Instant) (x : Stream (S * Instant)) :=
    Sini = hd x /\ isTrace_T x.
 
 
  (* operator Until *)

  Inductive Until_bound (P Q : Stream (S * Instant) -> Prop) :
  Stream (S * Instant) -> Prop :=
    | UntilFurther_bound :
        forall (s : S * Instant) (x : Stream (S * Instant)),
        P (s ^ x) -> Until_bound P Q x -> Until_bound P Q (s ^ x)
    | UntilHere_bound :
        forall (s : S) (t : Instant) (x : Stream (S * Instant)),
        bound t -> Q ((s, t) ^ x) -> Until_bound P Q ((s, t) ^ x).

  Inductive EX_Until_bound (Sini : S * Instant)
  (P Q : Stream (S * Instant) -> Prop) : Prop :=
      ExUntil_bound :
        forall x : Stream (S * Instant),
        isTraceFrom_T Sini x -> Until_bound P Q x -> EX_Until_bound Sini P Q.

  Definition FA_Until_bound (Sini : S * Instant)
    (P Q : Stream (S * Instant) -> Prop) :=
    forall x : Stream (S * Instant),
    isTraceFrom_T Sini x -> Until_bound P Q x.


  (* Init => FA[](bound t) P *)

  Definition Always_T (Sini : S * Instant)
    (P : Stream (S * Instant) -> Prop) :=
    forall x : Stream (S * Instant),
    isTraceFrom_T Sini x ->
    ForAllS (fun s : Stream (S * Instant) => bound (snd (hd s)) -> P s) x.


  (* Init => FA<>(bound t) P *)

  Definition Inevitable_T (Sini : S * Instant)
    (P : Stream (S * Instant) -> Prop) :=
    forall x : Stream (S * Instant),
    isTraceFrom_T Sini x ->
    ExistsS (fun s : Stream (S * Instant) => bound (snd (hd s)) /\ P s) x.


  (* Init => EX<>(bound t) P *)

  Inductive Posible_T (Sini : S * Instant) (P : Stream (S * Instant) -> Prop)
  : Prop :=
      posible_T :
        forall x : Stream (S * Instant),
        isTraceFrom_T Sini x ->
        ExistsS (fun s : Stream (S * Instant) => bound (snd (hd s)) /\ P s) x ->
        Posible_T Sini P.


  (* Init => EX[](bound t) P *)

  Inductive SafePath_T (Sini : S * Instant)
  (P : Stream (S * Instant) -> Prop) : Prop :=
      safePath_T :
        forall x : Stream (S * Instant),
        isTraceFrom_T Sini x ->
        ForAllS (fun s : Stream (S * Instant) => bound (snd (hd s)) -> P s) x ->
        SafePath_T Sini P.

 
  (**************************************************************************)
  (*                            Some Properties                             *)
  (**************************************************************************)

  Theorem Equiv1_T :
   forall (Sini : S * Instant) (P : Stream (S * Instant) -> Prop),
   Posible_T Sini P <->
   EX_Until_bound Sini (fun _ : Stream (S * Instant) => True) P.
  Proof.
    unfold iff in |- *; intros; split; intro.
    inversion_clear H.
    apply
     ExUntil_bound with (P := fun _ : Stream (S * Instant) => True) (1 := H0).
    elim H1.
    simple destruct x0; simpl in |- *.
    simple destruct p; simple destruct 1; simpl in |- *; intros.
    constructor 2; assumption.
    simple destruct s; intros.
    constructor 1; trivial.
    inversion_clear H.
    apply posible_T with (1 := H0).
    elim H1.
    simple destruct s; intros.
    constructor 2; assumption.
    intros; constructor 1; simpl in |- *; split; assumption.
  Qed.


  Theorem Equiv2_T :
   forall (Sini : S * Instant) (P : Stream (S * Instant) -> Prop),
   Inevitable_T Sini P <->
   FA_Until_bound Sini (fun _ : Stream (S * Instant) => True) P.
  Proof.
    unfold iff, Inevitable_T, FA_Until_bound in |- *; intros; split; intros.
    elim (H x H0); simple destruct x0.
    simple destruct p; intros.
    elim H1; intros.
    constructor 2; assumption.
    constructor 1; trivial.
    elim (H x H0); intros.
    constructor 2; assumption.
    constructor 1; split; assumption.
  Qed.

  Lemma ConsTrace_T :
   forall (s1 s2 : S * Instant) (x z : Stream (S * Instant)),
   isTraceFrom_T s2 z ->
   isTraceFrom_T s1 (s1 ^ s2 ^ x) -> isTraceFrom_T s1 (s1 ^ z).
  Proof.
    unfold isTraceFrom_T in |- *; simpl in |- *.
    simple destruct z; simple destruct 1; simple destruct 3; simpl in |- *;
     intros.
    compute in H0; rewrite H0 in H4.
    inversion_clear H4 in H1.
    split; [ trivial | apply (isTraceTick_T H5 H1) ].
    split; [ trivial | apply (isTraceDisc_T H5 H6 H1) ].
  Qed.


  Lemma notPosible_T :
   forall (P : Stream (S * Instant) -> Prop) (s1 : S * Instant),
   ~ Posible_T s1 P ->
   forall (z : Stream (S * Instant)) (s2 : S * Instant),
   isTraceFrom_T s1 (s1 ^ s2 ^ z) -> ~ Posible_T s2 P.
  Proof.
    unfold not at 2 in |- *; intros.
    elim H1; intros.
    apply H; cut (isTraceFrom_T s1 (s1 ^ x)).
    intro H4; apply (posible_T (P:=P) H4).
    apply Further; assumption.
    apply ConsTrace_T with (1 := H2) (2 := H0); assumption.
  Qed.

  Require Import Classical.

  Theorem Equiv3_T :
   forall (Sini : S * Instant) (P : Stream (S * Instant) -> Prop),
   Always_T Sini P <->
   ~ Posible_T Sini (fun s : Stream (S * Instant) => ~ P s).
  Proof.
    unfold iff, Always_T, not in |- *; intros; split.
    intros H H0; inversion_clear H0.
    generalize (H x H1); elim H2; intros.
    inversion_clear H3 in H0.
    elim H0; intros.
    elim (H6 (H4 H3)).
    inversion_clear H4.
    apply (H3 H6).
    generalize Sini; cofix u.
    simple destruct x; intros; constructor.
    intro; elim (classic (P (p ^ s))); [ trivial | intros ].
    absurd (Posible_T Sini0 (fun s : Stream (S * Instant) => ~ P s)).
    assumption.
    apply posible_T with (1 := H0).
    constructor 1; split; assumption.
    elim H0; simpl in |- *; intros.
    apply (u (hd s)); intros.
    generalize H0; clear H0; generalize H3; clear H3.
    rewrite <- H1; case s; simpl in |- *; intros.
    apply (notPosible_T (P:=fun s : Stream (S * Instant) => ~ P s) H H0);
     assumption.
    unfold isTraceFrom_T in |- *; inversion_clear H2; simpl in |- *.
    split; trivial.
    split; trivial.
  Qed.


  Theorem Equiv4_T :
   forall (Sini : S * Instant) (P : Stream (S * Instant) -> Prop),
   SafePath_T Sini P <->
   ~ Inevitable_T Sini (fun s : Stream (S * Instant) => ~ P s).
  Proof.
    unfold iff, Inevitable_T, not in |- *; intros; split.
    intro sp; inversion sp; intros.
    generalize H0; elim (H1 x H); intros.
    inversion_clear H3 in H2.
    elim H2; intros.
    apply (H6 (H4 H3)).
    apply H3; inversion_clear H4; assumption.
    intro H;
     elim
      (not_all_ex_not (Stream (S * Instant))
         (fun x : Stream (S * Instant) =>
          isTraceFrom_T Sini x ->
          ExistsS
            (fun s : Stream (S * Instant) =>
             bound (snd (hd s)) /\ (P s -> False)) x) H).
    intros.
    generalize
     (not_imply_elim2 (isTraceFrom_T Sini x)
        (ExistsS
           (fun s : Stream (S * Instant) =>
            bound (snd (hd s)) /\ (P s -> False)) x) H0).
    generalize
     (not_imply_elim (isTraceFrom_T Sini x)
        (ExistsS
           (fun s : Stream (S * Instant) =>
            bound (snd (hd s)) /\ (P s -> False)) x) H0); 
     intros.
    apply safePath_T with (1 := H1).
    generalize H1; clear H1; generalize H2; clear H2.
    generalize x; generalize Sini; cofix u.
    simple destruct x0; intros; constructor.
    elim (classic (P (p ^ s))); [ trivial | intros ].
    cut
     (ExistsS
        (fun s0 : Stream (S * Instant) =>
         bound (snd (hd s0)) /\ (P s0 -> False)) (p ^ s)).
    intro ex; elim (H2 ex).
    apply
     Here
      with
        (P := fun s : Stream (S * Instant) =>
              bound (snd (hd s)) /\ (P s -> False)).
    split; assumption.
    apply u with (Sini := hd s).
    generalize H2; clear H2; case s; unfold not in |- *; intros.
    apply (not_EX H2 H3).
    unfold isTraceFrom_T in |- *; elim H1; intros ig trace;
     inversion_clear trace.
    split; trivial.
    split; trivial.
  Qed.


End TemporalOperators_TCTL.

