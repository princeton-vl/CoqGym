(* Julien Narboux *)
(* Formalization of *)
(* Tarski's axiomatic *)

Require Export Ch02_congruence_properties.

(** Axiom 12 of Givant. *)

Lemma beetween_trivial : forall A B : Point, Bet A B B.
Proof with eTarski.
intros.
assert (exists x : Point, Bet A B x /\ Cong B x B B)...
DecompExAnd H x.
assert (B = x).
assert (Cong B B B x)...
congruence.
Qed.

Hint Resolve beetween_trivial : Tarski.

(** Axiom 14 of Givant. *)

Lemma between_symmetry : forall A B C : Point, 
   Bet A B C -> Bet C B A.
Proof with eTarski.
intros.
assert (Bet B C C)...
assert (exists x, Bet B x B /\ Bet C x A)...
DecompExAnd H1 x.
assert (B=x)...
congruence.
Qed.

Hint Resolve between_symmetry : sTarski.

Lemma beetween_trivial2 : forall A B : Point, Bet A A B.
Proof.
intros.
sTarski.
Qed.

Hint Resolve beetween_trivial beetween_trivial2 : Tarski.

Lemma between_egality : forall A B C : Point, Bet A B C -> Bet B A C -> A = B.
Proof with Tarski.
intros.
assert
 (exists x : Point,
     Bet B x B /\ Bet A x A).
eapply inner_pasch;eauto.
DecompExAnd H1 x.
assert (A = x)...
assert (B = x)...
rewrite <- H2 in H1.
assumption.
Qed.

Hint Resolve between_egality : Tarski.

(** Inner transitivity 'axiom' for betweenness. *)

Lemma between_inner_transitivity : forall A B C D,
Bet A B D -> Bet B C D -> Bet A B C.
Proof with eTarski.
intros.
assert (exists x,Bet B x B /\ Bet C x A)...
DecompExAnd H1 x.
apply between_symmetry.
assert (B=x)...
congruence.
Qed.

Lemma between_exchange3 : forall A B C D,
Bet A B C -> Bet A C D -> Bet B C D.
Proof.
intros.
apply between_symmetry.
eapply between_inner_transitivity.
apply between_symmetry.
apply H0.
sTarski.
Qed.

Hint Resolve between_exchange3 : Tarski.

Lemma outer_transitivity_between2 : forall A B C D,
Bet A B C -> Bet B C D -> B<>C -> Bet A C D.
Proof with eTarski.
intros.
assert (exists x, Bet A C x /\ Cong C x C D)...
DecompExAnd H2 x.
assert (Bet B C x)...
assert (x=D).
eapply construction_unicity;try apply H1...
subst x...
Qed.

Lemma between_exchange2 : forall A B C D,
Bet A B D -> Bet B C D -> Bet A C D.
Proof with eTarski.
intros.
cases_equality B C.
subst B...
eapply outer_transitivity_between2.
3:apply H1.
eapply between_inner_transitivity...
assumption.
Qed.

(** Axiom 16 of Givant. *)

Lemma outer_transitivity_between : forall A B C D,
Bet A B C -> Bet B C D -> B<>C -> Bet A B D.
Proof with eTarski.
intros.
eapply between_symmetry.
eapply between_exchange2;apply between_symmetry.
2:apply H.
eapply outer_transitivity_between2...
Qed.

Lemma between_exchange4 : forall A B C D,
Bet A B C -> Bet A C D -> Bet A B D.
Proof.
intros.
apply between_symmetry.
apply between_exchange2 with (B:=C);sTarski.
Qed.

Hint Resolve between_inner_transitivity : Tarski.
Hint Resolve between_exchange2 between_exchange3 between_exchange4 : Tarski.
Hint Resolve outer_transitivity_between outer_transitivity_between2 : Tarski.

Hint Resolve between_inner_transitivity 
 between_exchange2 between_exchange3 between_exchange4 
 outer_transitivity_between outer_transitivity_between2
 between_symmetry : Between.

Ltac Between := eauto with Between.

(*
Axiom 20.1 of Givant
Lemma unique_triangle : forall A B C C' D,
A <> B -> Cong A C A C' -> Cong B C B C' -> 
Bet B D C' -> (Bet A D C \/ Bet A C D) -> C=C'.
Axiom 21 of Givant
Lemma existence_triangle : forall A B A' B' C',
 Cong A B A' B' -> exists C X, Cong A C A' C' /\ Cong B C B' C' /\ Bet C X P /\ Col A B X.
*)

(** We formalize $Bet_n$ only for n=4. *)

Definition Bet_4 := fun A1 A2 A3 A4 =>
   Bet A1 A2 A3 /\ Bet A2 A3 A4 /\ Bet A1 A3 A4 /\ Bet A1 A2 A4. 

Lemma l_3_9_4 : forall A1 A2 A3 A4, 
 Bet_4 A1 A2 A3 A4 -> Bet_4 A4 A3 A2 A1.
Proof.
unfold Bet_4.
intros.
intuition.
Qed.

(** There are two distinct points ! *)
(** This is the first use of the lower dimension axiom *)
		
Lemma two_distinct_points : exists x, exists y: Point, x <> y.
Proof.
assert (ld := lower_dim).
DecompEx ld A.
DecompEx H B.
DecompEx H0 C.
unfold Col in H.
cases_equality A B.
subst A.
exists B.
exists C.
intuition.
exists A.
exists B.
assumption.
Qed.

Hint Resolve two_distinct_points : Tarski.

Lemma point_construction_different : forall A B,
  exists C, Bet A B C /\ B <> C.
Proof with Tarski.
intros.
assert (exists x, exists y:Point, x <> y)...
DecompEx H U.
DecompEx H0 V.
assert (exists C, Bet A B C /\ Cong B C U V)...
DecompEx H0 C.
exists C.
intuition.
rewrite H1 in H2.
assert (U=V).
eapply cong_identity.
apply cong_symmetry.
eauto.
auto.
Qed.

Hint Resolve point_construction_different : Tarski.

(** Given a point, we can build another one which is different from the first one. *)

Lemma another_point : forall A:Point, exists B, A<>B.
Proof.
assert (T:=two_distinct_points ).
DecompEx T X.
DecompEx H Y.
intros.
cases_equality A X.
subst X.
exists Y;auto.
exists X;auto.
Qed.

(** From the last two lemmas we can conclude that models of the first seven axioms are infinite *)
 

Lemma l3_17 : forall A B C A' B' P,
  Bet A B C ->  Bet A' B' C ->  Bet A P A' ->  
  exists Q, Bet P Q C /\ Bet B Q B'.
Proof with Tarski.
intros.
assert (exists Q', Bet B' Q' A /\ Bet P Q' C).
eapply inner_pasch.
2:apply H1.
sTarski.
DecompExAnd H2 Q'.
assert (exists x : Point, Bet B x B' /\ Bet Q' x C).
eapply (inner_pasch C B' A B Q');auto.
sTarski.
DecompExAnd H2 Q.
exists Q.
intuition.
clear H H1 H0 H4 H6.
clear A B A' B'.
esTarski.
Qed.

  (** Inner five segment configuration. *)
  
Definition IFSC := fun A B C D A' B' C' D' =>
   Bet A B C /\ Bet A' B' C' /\
   Cong A C A' C' /\ Cong B C B' C' /\ 
   Cong A D A' D' /\ Cong C D C' D'.

(* Require Export Eqdep_dec. *)

(** This tactic asserts Col X Y Z, for each Bet X Y Z in the context. *)

Ltac assert_cols := 
repeat
 match goal with
      | H:Bet ?X1 ?X2 ?X3 |- _ => not_exist_hyp (Col X1 X2 X3);assert (Col X1 X2 X3);[Tarski|idtac] 
 end.

Ltac clean_trivial_hyps :=
  repeat 
  match goal with
   |  H:(Cong ?X1 ?X1 ?X2 ?X2) |- _ => clear H
   |  H:(Cong ?X1 ?X2 ?X2 ?X1) |- _ => clear H
   |  H:(Cong ?X1 ?X2 ?X1 ?X2) |- _ => clear H
   |  H:(Bet ?X1 ?X1 ?X2) |- _ => clear H
   |  H:(Bet ?X2 ?X1 ?X1) |- _ => clear H
   |  H:(Col ?X1 ?X1 ?X2) |- _ => clear H
   |  H:(Col ?X2 ?X1 ?X1) |- _ => clear H
   |  H:(Col ?X1 ?X2 ?X1) |- _ => clear H
end.

Ltac smart_subst X := subst X;clean_trivial_hyps;clean_duplicated_hyps.

Ltac treat_equalities_aux := 
  match goal with
   |  H:(?X1 = ?X2) |- _ => smart_subst X2
end.

(** This tactic looks for an equality, perform the substitution and then attempts
 to prove other equalities and apply reccursively. 
 It cleans the hypothesis which become trivial or duplicated*)

Ltac treat_equalities :=  
try treat_equalities_aux;
repeat
  match goal with
   |  H:(Cong ?X3 ?X3 ?X1 ?X2) |- _ => 
      assert (X1=X2);[apply cong_identity with (A:=X1) (B:=X2) (C:=X3);apply cong_symmetry;assumption|idtac];smart_subst X2
   |  H:(Cong ?X1 ?X2 ?X3 ?X3) |- _ => 
      assert (X1=X2);[apply cong_identity with (A:=X1) (B:=X2) (C:=X3);assumption|idtac];smart_subst X2
   |  H:(Bet ?X1 ?X2 ?X1) |- _ => 
      assert (X1=X2);[apply between_identity;assumption|idtac];smart_subst X2
end.