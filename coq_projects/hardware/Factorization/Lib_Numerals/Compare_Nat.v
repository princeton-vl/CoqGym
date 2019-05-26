(* This code is copyrighted by its authors; it is distributed under  *)
(* the terms of the LGPL license (see LICENSE and description files) *)

(* Contribution to the Coq Library   V6.3 (July 1999)                    *)
(****************************************************************************)
(*                                                                          *)
(*                                                                          *)
(*                   Solange Coupet-Grimal & Line Jakubiec                  *)
(*                                                                          *)
(*                                                                          *)
(*              Laboratoire d'Informatique de Marseille                     *)
(*               CMI-Technopole de Chateau-Gombert                          *)
(*                   39, Rue F. Joliot Curie                                *)
(*                   13453 MARSEILLE Cedex 13                               *)
(*           e-mail:{Solange.Coupet,Line.Jakubiec}@lim.univ-mrs.fr          *)
(*                                                                          *)
(*                                                                          *)
(*                                Coq V5.10                                 *)
(*                              May 30th 1996                               *)
(*                                                                          *)
(****************************************************************************)
(*                              Compare_Nat.v                               *)
(****************************************************************************)

Require Export Arith.

Global Set Asymmetric Patterns.

Inductive Or3 (A B C : Prop) : Set :=
  | First : A -> Or3 A B C
  | Second : B -> Or3 A B C
  | Third : C -> Or3 A B C.
Hint Resolve First Second Third.

Lemma Lt_eq_Gt : forall n m : nat, Or3 (n < m) (n = m) (n > m).
simple induction n; simple induction m.
apply Second; try trivial with arith.
intros; apply First; try trivial with arith.
apply Third; try trivial with arith.
intros.
elim (H n1); intros Hyp.
apply First; auto with arith.
apply Second; auto with arith.
apply Third; auto with arith.
Defined.


Inductive order : Set :=
  | L : order
  | E : order
  | G : order.

Definition comparison (v1 v2 : nat) :=
  match Lt_eq_Gt v1 v2 return order with
  | First _ => L
  | Second _ => E
  | Third _ => G
  end.

Lemma comparisonL :
 forall v1 v2 : nat, v1 < v2 -> Compare_Nat.comparison v1 v2 = L.
intros.
unfold Compare_Nat.comparison in |- *.
elim (Lt_eq_Gt v1 v2).
auto with arith.
intros e; absurd (v1 < v2); auto with arith.
rewrite e; auto with arith.
intro; absurd (v1 > v2); auto with arith.
Qed.
Hint Resolve comparisonL.

Lemma comparisonG :
 forall v1 v2 : nat, v1 > v2 -> Compare_Nat.comparison v1 v2 = G.
intros.
unfold Compare_Nat.comparison in |- *.
elim (Lt_eq_Gt v1 v2); auto with arith.
intro; absurd (v1 > v2); auto with arith.
intros e; absurd (v1 > v2); auto with arith.
rewrite e; auto with arith.
Qed.
Hint Resolve comparisonG.

Lemma comparisonE :
 forall v1 v2 : nat, v1 = v2 -> Compare_Nat.comparison v1 v2 = E.
intros.
unfold Compare_Nat.comparison in |- *.
elim (Lt_eq_Gt v1 v2); auto with arith.
intro; absurd (v1 < v2); auto with arith.
rewrite H; auto with arith.
intro; absurd (v1 > v2); auto with arith.
rewrite H; auto with arith.
Qed. 
Hint Resolve comparisonE.

Lemma inv_comparisonL :
 forall v1 v2 : nat, Compare_Nat.comparison v1 v2 = L -> v1 < v2.
intros.
elim (Lt_eq_Gt v1 v2); auto with arith.
intros e.
absurd (Compare_Nat.comparison v1 v2 = L); auto with arith.
rewrite (comparisonE v1 v2 e); discriminate.
intros g.
absurd (Compare_Nat.comparison v1 v2 = L); auto with arith.
rewrite (comparisonG v1 v2 g); discriminate.
Qed.
Hint Resolve inv_comparisonL.

Lemma inv_comparisonE :
 forall v1 v2 : nat, Compare_Nat.comparison v1 v2 = E -> v1 = v2.
intros v1 v2 c.
elim (Lt_eq_Gt v1 v2); auto with arith.
intros l; absurd (Compare_Nat.comparison v1 v2 = E); auto with arith.
rewrite (comparisonL v1 v2 l); discriminate.
intros g; absurd (Compare_Nat.comparison v1 v2 = E); auto with arith.
rewrite (comparisonG v1 v2 g); discriminate.
Qed.
Hint Resolve inv_comparisonE.

Lemma inv_comparisonG :
 forall v1 v2 : nat, Compare_Nat.comparison v1 v2 = G -> v1 > v2.
intros v1 v2 c.
elim (Lt_eq_Gt v1 v2); auto with arith.
intros l; absurd (Compare_Nat.comparison v1 v2 = G); auto with arith.
rewrite (comparisonL v1 v2 l); discriminate.
intros e; absurd (Compare_Nat.comparison v1 v2 = G); auto with arith.
rewrite (comparisonE v1 v2 e); discriminate.
Qed.
Hint Resolve inv_comparisonG.

Lemma inv_comparison :
 forall v1 v2 : nat,
 match Compare_Nat.comparison v1 v2 return Prop with
 | L => v1 < v2
 | E => v1 = v2
 | G => v1 > v2
 end.
intros v1 v2.
cut (Compare_Nat.comparison v1 v2 = Compare_Nat.comparison v1 v2);
 auto with arith.
pattern (Compare_Nat.comparison v1 v2) at 2 3 in |- *.
case (Compare_Nat.comparison v1 v2); intro; auto with arith.
Qed.

Lemma comp_sym_LG :
 forall v1 v2 : nat,
 Compare_Nat.comparison v1 v2 = L -> Compare_Nat.comparison v2 v1 = G.
intros v1 v2 H.
apply comparisonG.
auto with arith.
Qed.
Hint Resolve comp_sym_LG.

Lemma comp_sym_GL :
 forall v1 v2 : nat,
 Compare_Nat.comparison v1 v2 = G -> Compare_Nat.comparison v2 v1 = L.
intros v1 v2 H.
apply comparisonL; auto with arith.
Qed.
Hint Resolve comp_sym_GL.


Lemma comp_sym_E :
 forall v1 v2 : nat,
 Compare_Nat.comparison v1 v2 = E -> Compare_Nat.comparison v2 v1 = E.
intros v1 v2 H.
apply comparisonE.
apply sym_equal.
auto with arith.
Qed.
Hint Resolve comp_sym_E.
