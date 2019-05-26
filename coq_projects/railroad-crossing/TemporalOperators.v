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


 (* Computation Tree Logic (CTL) and Timed Computation Tree Logic (TCTL) *)

Set Implicit Arguments.
Unset Strict Implicit.

Require Import Streams.
Require Import time_clocks. (* Temporal notions for discrete time *)

(****************************************************************************)
(* Hypothesis: type Label with label Tick                                   *)
(* Inductive Label : Set := L1 : Label | ... | Ln : Label | Tick : Label.   *)
(****************************************************************************)


Section TemporalOperators_Ind.

(* Temporal operators with inductive types: definitions and properties *)

  Variable S : Set.                (* States *) 
  Variable tr : S -> Label -> S -> Prop.  (* Transitions *)

  (* Reachable states form "Sini" with transitions "tr" *)

  Inductive RState (Sini : S) : S -> Prop :=
    | rsIni : RState Sini Sini
    | rsNext :
        forall (s1 s2 : S) (l : Label),
        RState Sini s1 -> tr s1 l s2 -> RState Sini s2.


  (* Reachable states form "Sini" with transitions "tr" in time units *)

  Inductive RState_T (Sini : S) : S -> Instant -> Prop :=
    | rsIni_T : RState_T Sini Sini time0
    | rsTime_T :
        forall (s1 s2 : S) (t : Instant),
        RState_T Sini s1 t -> tr s1 Tick s2 -> RState_T Sini s2 (Inc t)
    | rsNoTime_T :
        forall (s1 s2 : S) (l : Label) (t : Instant),
        RState_T Sini s1 t -> l <> Tick -> tr s1 l s2 -> RState_T Sini s2 t.  


  (**************************************************************************)
  (*                       Invariants and Reachability                      *)
  (**************************************************************************)  

  (* Init => FA[] P *)

  Definition ForAll (Sini : S) (P : S -> Prop) :=
    forall s : S, RState Sini s -> P s. 


  (* Init => FA[](bound t) P *)

  Definition ForAll_T (Sini : S) (P : S -> Prop) (bound : Instant -> Prop) :=
    forall (s : S) (t : Instant), bound t -> RState_T Sini s t -> P s.


  (* Init => EX<> P *)

  Inductive Exists (Sini : S) (P : S -> Prop) : Prop :=
      exists_ : forall s : S, RState Sini s -> P s -> Exists Sini P.


  (* Init => EX<>(bound t) P *)

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
    intros.
    elim H0; [ assumption | intros ].
    apply (rsNext H2 H3).
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
    apply (rsTime_T H2 H3). 
    apply (rsNoTime_T H2 H3 H4).
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
  (*                             Other Definitions                          *)
  (**************************************************************************)

  (* FA[] (Q => FA[] P) *)

  Definition ForAll_from (Sini : S) (Q P : S -> Prop) :=
    ForAll Sini (fun s : S => Q s -> ForAll s P). 
     (* (s:S) (RState Sini s) -> (Q s) -> (ForAll s P). *)


  (* FA[] (Q => FA[](bound t) P) *)

  Definition ForAll_from_T (Sini : S) (Q P : S -> Prop)
    (bound : Instant -> Prop) :=
    ForAll Sini (fun s : S => Q s -> ForAll_T s P bound). 
     (* (s:S) (RState Sini s) -> (Q s) -> (ForAll_T s P bound). *)

  
  (* FA[] (Q => EX<> P) *)

  Definition Exists_from (Sini : S) (Q P : S -> Prop) :=
    ForAll Sini (fun s : S => Q s -> Exists s P). 
     (* (s:S) (RState Sini s) -> (Q s) -> (Exists s P). *)


  (* FA[] (Q => EX<>(bound t) P) *)

  Definition Exists_from_T (Sini : S) (Q P : S -> Prop)
    (bound : Instant -> Prop) :=
    ForAll Sini (fun s : S => Q s -> Exists_T s P bound). 
     (* (s:S) (RState Sini s) -> (Q s) -> (Exists_T s P bound). *)


End TemporalOperators_Ind.



Infix "^" := Cons.

Section TemporalOperators_CTL.

(* CTL operators with co-inductives types: definitions and properties *)

  Variable S : Set.                (* States *) 
  Variable tr : S -> Label -> S -> Prop.  (* Transitions *)
  
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
      is_trace :
        forall (x : Stream S) (s1 s2 : S) (l : Label),
        tr s1 l s2 -> isTrace (s2 ^ x) -> isTrace (s1 ^ s2 ^ x).      

  Definition isTraceFrom (Sini : S) (x : Stream S) :=
    Sini = hd x /\ isTrace x.
  

  (* Operator Until *)

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
  (*                            Some Properties                             *)
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
    inversion_clear H4.
    split; [ trivial | apply (is_trace H5 H1) ].
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



Section TemporalOperators_TCTL.

(* TCTL operators with co-inductives types: definitions and properties *)

  Variable S : Set.                (* States *) 
  Variable tr : S -> Label -> S -> Prop.  (* Transitions *)
  Variable bound : Instant -> Prop.    (* Location invariants *)
 
  Notation State_T := (S * Instant)%type (only parsing).
  Notation SPath_T := (Stream (S * Instant)) (only parsing).


  (* Ejecution traces *)

  CoInductive isTrace_T : Stream (S * Instant) -> Prop :=
    | isTraceTick :
        forall (x : Stream (S * Instant)) (s1 s2 : S) (t : Instant),
        tr s1 Tick s2 ->
        isTrace_T ((s2, Inc t) ^ x) -> isTrace_T ((s1, t) ^ (s2, Inc t) ^ x)
    | isTraceDisc :
        forall (x : Stream (S * Instant)) (s1 s2 : S) 
          (t : Instant) (l : Label),
        tr s1 l s2 ->
        l <> Tick ->
        isTrace_T ((s2, t) ^ x) -> isTrace_T ((s1, t) ^ (s2, t) ^ x). 

  Definition isTraceFrom_T (Sini : S * Instant) (x : Stream (S * Instant)) :=
    Sini = hd x /\ isTrace_T x.
 
 
  (* Until operator *)

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
  (*                              Some Properties                           *)
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
    split; [ trivial | apply (isTraceTick H5 H1) ].
    split; [ trivial | apply (isTraceDisc H5 H6 H1) ].
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

