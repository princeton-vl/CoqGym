(* This code is copyrighted by its authors; it is distributed under  *)
(* the terms of the LGPL license (see LICENSE and description files) *)

(* Contribution to the Coq Library   V6.3 (July 1999)                    *)
(****************************************************************************)
(*                                                                          *)
(*                                                                          *)
(*                   Solange Coupet-Grimal & Line Jakubiec                  *)
(*                                                                          *)
(*                                                                          *)
(*                 Laboratoire d'Informatique de Marseille                  *)
(*                   Technopole de Chateau-Gombert                          *)
(*                   39, Rue F. Joliot Curie                                *)
(*                   13453 MARSEILLE Cedex 13                               *)
(*           e-mail:{Solange.Coupet,Line.Jakubiec}@lim.univ-mrs.fr          *)
(*                                                                          *)
(*                                                                          *)
(*                                Coq V5.10                                 *)
(*                              May 30th 1996                               *)
(*                                                                          *)
(****************************************************************************)
(*                               Lib_Prop.v                                 *)
(****************************************************************************)


Inductive or3 (A B C : Prop) : Set :=
  | or3_Left : A -> or3 A B C
  | or3_Middle : B -> or3 A B C
  | or3_Right : C -> or3 A B C.




Lemma sym_and : forall A B : Prop, A /\ B -> B /\ A.
intros A B H; elim H; split; auto.
Qed.
Hint Immediate sym_and.



Lemma sym_or : forall A B : Prop, A \/ B -> B \/ A.
simple induction 1; auto.
Qed.
Hint Immediate sym_or.


Lemma no_and_l : forall A B : Prop, ~ A -> ~ (A /\ B).
unfold not in |- *.
intros A B H G; apply H.
elim G; auto.
Qed.
Hint Resolve no_and_l.


Lemma no_and_r : forall A B : Prop, ~ B -> ~ (A /\ B).
unfold not in |- *.
intros A B H G; apply H.
elim G; auto.
Qed.
Hint Resolve no_and_r.


Lemma no_or : forall A B : Prop, ~ A -> B \/ A -> B.
intros A B H G; elim G; auto.
intro; absurd A; auto.
Qed.


Lemma no_or_inv : forall A B : Prop, ~ A -> A \/ B -> B.
intros A B H G; elim G; auto.
intro; absurd A; auto.
Qed.


Lemma no_or_and : forall A B C D : Prop, ~ C -> A /\ B \/ C /\ D -> A /\ B.
intros.
apply no_or with (C /\ D); auto.
Qed.


Lemma no_or_and_inv :
 forall A B C D : Prop, ~ D -> C /\ D \/ A /\ B -> A /\ B.
intros.
apply no_or_inv with (C /\ D); auto.
Qed.


Lemma no_no_A : forall A : Prop, A -> ~ ~ A.
unfold not in |- *; auto.
Qed.
Hint Resolve no_no_A.


Lemma impl_no_no : forall A B : Prop, (A -> B) -> ~ B -> ~ A.
unfold not in |- *; auto.
Qed.


Lemma no_or_r : forall A B : Prop, ~ A -> A \/ B -> B.
intros A B not_A A_or_B.
elim A_or_B; auto.
intro; absurd A; auto.
Qed.


Lemma no_or_l : forall A B : Prop, ~ B -> A \/ B -> A.
intros A B not_A A_or_B.
elim A_or_B; auto.
intro; absurd B; auto.
Qed.

(************************************************************************)

