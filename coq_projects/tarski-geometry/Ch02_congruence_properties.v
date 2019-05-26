(* Julien Narboux *)
(* Formalization of *)
(* Tarski's axiomatic *)

Require Export  Ch01_tarski_axioms.

(** Some basic properties about Cong. *)
  
Lemma cong_reflexivity : forall A B : Point, Cong A B A B.
Proof.
eTarski.
Qed.

Hint Resolve cong_reflexivity : Tarski.

Lemma cong_symmetry : forall A B C D : Point, Cong A B C D -> Cong C D A B.
Proof.
eTarski.
Qed.

Hint Immediate cong_symmetry : sTarski.

Ltac sTarski := auto with Tarski sTarski.
Ltac esTarski := eauto with Tarski sTarski.

Lemma cong_transitivity :
 forall A B C D E F : Point, Cong A B C D -> Cong C D E F -> Cong A B E F.
Proof.
eTarski.
Qed.

(* The following hint has been disabled since it isn't necessary
   (cf. cong_inner_transitivity + cong_symmetry) and it may interact badly
   with cong_inner_transitivity to create proofs with remaining evars *)

(*Hint Resolve cong_transitivity : Tarski.*)

Lemma cong_left_commutativity : forall A B C D,
  Cong A B C D -> Cong B A C D.
Proof.
eTarski.
Qed.

Lemma cong_right_commutativity : forall A B C D,
  Cong A B C D -> Cong A B D C.
Proof.
eTarski.
Qed.

Hint Resolve cong_left_commutativity cong_right_commutativity : sTarski.

Lemma cong_trivial_identity : forall A B : Point, Cong A A B B.
Proof.
intros.
assert (exists E : Point, Bet A B E /\ Cong B E A A).
apply segment_construction with (B := B) (C := A) (D := A).
DecompExAnd H x.
apply cong_symmetry.
assert (B = x).
eTarski.
rewrite <- H in H2.
assumption.
Qed.

Hint Resolve cong_trivial_identity : Tarski.

Lemma cong_reverse_identity : forall A C D, Cong A A C D -> C=D.
Proof with eTarski.
intros.
assert (Cong C D A A)...
Qed.

Hint Resolve cong_reverse_identity : Tarski.

Lemma cong_commutativity : forall A B C D, Cong A B C D -> Cong B A D C.
Proof with eTarski. 
intros...
Qed.

Hint Resolve cong_commutativity : sTarski.
		
(** (Outer) Five segments configuration. *)

Definition OFSC := fun A B C D A' B' C' D' => 
  Bet A B C /\ Bet A' B' C' /\ 
  Cong A B A' B' /\ Cong B C B' C' /\ 
  Cong A D A' D' /\ Cong B D B' D'.

Hint Unfold OFSC : Tarski.

Lemma five_segments_with_def : forall A B C D A' B' C' D',
OFSC A B C D A' B' C' D' -> A<>B -> Cong C D C' D'.
Proof.
unfold  OFSC.
intuition.
eapply five_segments;try apply H2;Tarski.
Qed.

Hint Resolve five_segments_with_def : Tarski.

Lemma l2_11 :
 forall A B C A' B' C',
 Bet A B C -> Bet A' B' C' -> 
 Cong A B A' B' -> Cong B C B' C' -> Cong A C A' C'.
Proof with eTarski.
intros.
cases_equality A B.
assert (A' = B').
assert (Cong A' B' A B).
sTarski.
eapply cong_identity.
rewrite H3 in H4.
apply H4.
rewrite <- H3 in H2.
rewrite <- H4 in H2.
assumption.
assert (Cong C A C' A').
eapply five_segments; try apply H1...
eTarski.
Qed.

(** Unicity of segment construction. *)
  
Lemma construction_unicity : forall Q A B C x y,
   ~(Q=A) -> 
  Bet Q A x -> Cong A x B C ->
  Bet Q A y -> Cong A y B C -> 
  x=y.
Proof.
intros.
assert (Cong Q x Q y).
eapply l2_11;eTarski.
assert (Cong A x A y).
eapply cong_transitivity;eauto.
sTarski.
assert (OFSC Q A x x Q A x y).
unfold OFSC.
intuition.
assert (Cong x x x y).
eapply five_segments_with_def;eTarski.
esTarski.
Qed.