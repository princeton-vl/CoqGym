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
(*                            Factorization.v                               *)
(****************************************************************************)


Require Export Numerals.

Section factorization.

   Variable A : Set.
   Variable BASE : BT.
   Let b := base BASE.
   Let Num := num BASE.
   Let Digit := digit BASE.
   Let Tl := tl Digit.

   Let Cons := cons Digit.
   Let Nil := nil Digit.
   Let Val_bound := val_bound BASE.

 Section Definitions_for_Relations.
   
   Definition Diveucl (a b q r : nat) : Prop := a = b * q + r /\ r < b.
   Definition Zero : inf 1 := Val_bound 0 Nil.


   Variable R : forall n : nat, A -> inf n -> inf n -> A -> Prop.
         
   Definition factorizable : Prop :=
     forall (m n : nat) (q q' : inf m) (r r' : inf n) 
       (a a1 a' : A) (x x' : inf (m * n)),
     Diveucl (val_inf (m * n) x) n (val_inf m q) (val_inf n r) ->
     Diveucl (val_inf (m * n) x') n (val_inf m q') (val_inf n r') ->
     R m a q q' a1 -> R n a1 r r' a' -> R (m * n) a x x' a'.

    Definition proper : Prop := forall a : A, R 1 a Zero Zero a.

 End Definitions_for_Relations.

 Section Three_inputs.

   
  Variable FR : forall n : nat, A -> inf n -> inf n -> A.

  Let R (n : nat) (a : A) (x y : inf n) (a' : A) : Prop := a' = FR n a x y.

  Lemma prop_Rel :
   proper R ->
   forall (X Y : Num 0) (a : A), R 1 a (Val_bound 0 X) (Val_bound 0 Y) a.
  intros P X Y a.
  replace X with (nil (digit BASE)); auto with arith.
  replace Y with (nil (digit BASE)); auto with arith.
  Qed.

   Lemma fact_Rel :
    factorizable R ->
    forall (n : nat) (X Y : Num (S n)) (a a' : A),
    R (exp b n) (FR b a (Hd Digit n X) (Hd Digit n Y))
      (Val_bound n (Tl (S n) X)) (Val_bound n (Tl (S n) Y)) a' ->
    R (exp b (S n)) a (Val_bound (S n) X) (Val_bound (S n) Y) a'.

  intros F n X Y a a' H.
  simpl in |- *.
  generalize (non_empty (inf b) n X).
  generalize (non_empty (inf b) n Y).
  intros H1 H2.
  elim H1; elim H2; clear H1 H2.
  intros d D d' D'.
  elim D; elim D'; clear D D'.
  intros D' HD' D HD.
  rewrite HD; rewrite HD'.
  apply
   F
    with
      d
      d'
      (Val_bound n (Tl (S n) X))
      (Val_bound n (Tl (S n) Y))
      (FR b a (Hd Digit n X) (Hd Digit n Y)).
  unfold Diveucl in |- *; split; simpl in |- *.
  rewrite HD; simpl in |- *.
  elim (mult_comm (val_inf b d) (exp b n)); auto with arith.
  rewrite HD; simpl in |- *.
  unfold b in |- *; apply upper_bound.
  unfold Diveucl in |- *; split; simpl in |- *.
  rewrite HD'; simpl in |- *.
  elim (mult_comm (val_inf b d') (exp b n)); auto with arith.
  rewrite HD'; simpl in |- *.
  unfold b in |- *; apply upper_bound.
  unfold R in |- *.
  rewrite HD; rewrite HD'.
  rewrite Non_empty_Hd; rewrite Non_empty_Hd; auto with arith.
  try trivial with arith.
  Qed.

 End Three_inputs.

End factorization.


(*************************************************************************************)