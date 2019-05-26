(* Julien Narboux *)
(* Formalization of *)
(* Tarski's axiomatic *)

Require Export  general_tactics.

(** We use the axioms used in the book of Schwabäuser, Szmielew and Tarski. *)

(** We assume that we have a set of points. This axiomatic is based only on points, lines are implicit. *)

Parameter Point : Set.

(* Here we use classical logic, for a intuitionnist approach 
use von Plato axiomatic for instance. 
In this development, the classic axiom is mainly applied to formulas of the form :
- Col A B C, 
- A=B
*)

Require Export Classical.

(** Tarski's axiomatic is based on two predicates over points, 
one ternary and one quaternary. *)

(** Cong A B C D informally means that the distance AB 
is equal to the distance CD. *)

Parameter Cong : Point -> Point -> Point -> Point -> Prop.

(** Bet A B C, informally means that : 
A, B and C are on the same line
B is between A and C.
Note that they are not necessarily distinct. 
This is the difference between 
the Between predicate of Tarski and the BetweenH prdicate of Hilbert
*)

Parameter Bet : Point -> Point -> Point -> Prop.

Definition Col (A B C : Point) : Prop :=
  Bet A B C \/ Bet B C A \/ Bet C A B.

Ltac cases_col A B C := elim (classic (Col A B C));intros.

(** %\textbf{% Identity axiom for betweenness. %}% *)

Axiom between_identity : forall A B, Bet A B A -> A=B.

(** %\textbf{% Reflexivity axiom for equidistance.%}% *)
  
Axiom cong_pseudo_reflexivity : forall A B : Point, Cong A B B A.

(** %\textbf{% Identity axiom for equidistance.%}% *)
  
Axiom cong_identity : forall A B C : Point, Cong A B C C -> A = B.

(** %\textbf{% Transitivity axiom for equidistance.%}% *)
  
Axiom cong_inner_transitivity : forall A B C D E F : Point, 
   Cong A B C D -> Cong A B E F -> Cong C D E F.

(** %\textbf{% Pasch Axiom (Inner form).%}% *)
     
Axiom inner_pasch : forall A B C P Q : Point,
      Bet A P C -> Bet B Q C ->
      exists x, Bet P x B /\ Bet Q x A.

(** %\textbf{% Euclid Axiom.%}% *)
	
Axiom euclid : forall A B C D T : Point,
    Bet A D T -> Bet B D C -> A<>D ->
    exists x, exists y,
    Bet A B x /\ Bet A C y /\ Bet x T y.

(** %\textbf{% Five segments axiom.%}% *)
      
Axiom five_segments : forall A A' B B' C C' D D' : Point,
    Cong A B A' B' ->
    Cong B C B' C' ->
    Cong A D A' D' ->
    Cong B D B' D' ->
    Bet A B C -> Bet A' B' C' -> A <> B -> Cong C D C' D'.

(** %\textbf{% Axiom of segment construction.%}% *)
      
Axiom segment_construction : forall A B C D : Point, 
    exists E : Point, Bet A B E /\ Cong B E C D.

(** %\textbf{% Lower dimension axiom (2).%}% *)
      
Axiom lower_dim :
    exists A, exists B, exists C, ~ Col A B C.

(** %\textbf{% Upper dimension axiom  (2).%}% *)
      
Axiom upper_dim : forall A B C P Q : Point,
    P <> Q -> Cong A P A Q -> Cong B P B Q -> Cong C P C Q ->
    Col A B C.

(** %\textbf{% Continuity axioms.%}% *)
      
Axiom continuity :
    forall X Y : Point -> Prop,
    (exists A : Point, (forall x y : Point, X x -> Y y -> Bet A x y)) ->
    exists B : Point, (forall x y : Point, X x -> Y y -> Bet x B y).

Hint Resolve segment_construction five_segments inner_pasch euclid : Tarski.
Hint Resolve cong_pseudo_reflexivity cong_identity between_identity : Tarski.
Hint Resolve cong_inner_transitivity  : Tarski.

Ltac eTarski := eauto with Tarski.
Ltac Tarski := auto with Tarski.


(** We use classical logic, to emphasize the fact that it is mainly for the decidability of point equality we use the 
following lemma *)

Lemma eq_dec_points : forall A B:Point, A=B \/ ~ A=B.
Proof.
intros.
apply classic.
Qed.

Ltac cases_equality A B := elim (eq_dec_points A B);intros.
