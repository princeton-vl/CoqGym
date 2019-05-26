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
(*                         Comparator_Relations.v                            *)
(****************************************************************************)


Require Export Compare_Nat.
Require Export Factorization.
Require Export Compare_Num.


Section Comparator_Rel.
   
   Variable BASE : BT.
   
   Definition FR (n : nat) (o : order) (x y : inf n) : order :=
     match o return order with
     | L => L
     | E => Compare_Nat.comparison (val_inf n x) (val_inf n y)
     | G => G
     end.

   
   Definition R (n : nat) (o : order) (x y : inf n) 
     (o' : order) : Prop := o' = FR n o x y.
   
        
  (*Is R proper ?*)

  Notation Proper := (proper _) (only parsing).

Lemma is_proper : proper _ BASE R.
unfold proper in |- *.
intros a; case a; unfold R in |- *; simpl in |- *; auto with arith.
Qed.


  (*Is R factorizable ?*)

  Notation Factorizable := (factorizable _) (only parsing).

Lemma is_factorizable : factorizable _ R.
unfold factorizable in |- *; unfold R in |- *;
 intros M N q q' r r' a a1 a' x x' H1 H2; case a.

(*a=L*)
simpl in |- *; intro R1; rewrite R1; simpl in |- *; auto with arith.

(*a=E*)
case a1.
  (*a1=L*) 
  intros R1 R2.
  replace a' with L; simpl in |- *; apply sym_equal; apply comparisonL.
  unfold Diveucl in H1; unfold Diveucl in H2; elim H1; elim H2; clear H1 H2;
   intros H1 H2 H3 H4; rewrite H1; rewrite H3;
   elim (mult_comm (val_inf M q) N); elim (mult_comm (val_inf M q') N);
   auto with arith.

  (*a1=E*)
  case a'; intros R1 R2.
  simpl in |- *; apply sym_equal; apply comparisonL.
  unfold Diveucl in H1; unfold Diveucl in H2; elim H1; elim H2; clear H1 H2;
   intros H1 H2 H3 H4; rewrite H1; rewrite H3.
  replace (val_inf M q') with (val_inf M q); auto with arith.
  simpl in |- *; apply sym_equal; apply comparisonE.
  unfold Diveucl in H1; unfold Diveucl in H2; elim H1; elim H2; clear H1 H2;
   intros H1 H2 H3 H4; rewrite H1; rewrite H3.
  replace (val_inf M q') with (val_inf M q); auto with arith.


  simpl in |- *; apply sym_equal; apply comparisonG.
  unfold Diveucl in H1; unfold Diveucl in H2; elim H1; elim H2; clear H1 H2;
   intros H1 H2 H3 H4; rewrite H1; rewrite H3.
  replace (val_inf M q') with (val_inf M q); auto with arith.

  (*a1=G*)
  intros R1 R2.
  replace a' with G; simpl in |- *; apply sym_equal; apply comparisonG.
  unfold Diveucl in H1; unfold Diveucl in H2; elim H1; elim H2; clear H1 H2;
   intros H1 H2 H3 H4; rewrite H1; rewrite H3; unfold gt in |- *;
   elim (mult_comm (val_inf M q) N); elim (mult_comm (val_inf M q') N);
   auto with arith. 
 
(*a=G*)
simpl in |- *; intro R1; rewrite R1; simpl in |- *; auto with arith.

Qed.


End Comparator_Rel.