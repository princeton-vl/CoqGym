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
(*                               Comp_Simpl.v                               *)
(****************************************************************************)


Require Export Numerals.
Require Export Compare_Num.
Require Export Linear_Structures.

Section comparator.

(*system of numeration*)

  Variable BASE : BT.
  Let Digit := digit BASE.
  Let valB := val BASE.
  Let ValB := Val BASE.
  Let Num := num BASE.
  Let Val_bound := val_bound BASE.
  Let Cons := cons Digit.
  Let Nil := nil Digit.

(*cell semantics*)

  Let f_cell (o : order) (x y : Digit) : order :=
    match o return order with
    | L => L
    | E => Compare_Nat.comparison (valB x) (valB y)
    | G => G
    end.

  Inductive cell : order -> Digit -> Digit -> order -> Prop :=
      cell_constr :
        forall (o o' : order) (x y : Digit),
        o' = f_cell o x y -> cell o x y o'.


  Let f_circ (n : nat) (o : order) (X Y : Num n) : order :=
    match o return order with
    | L => L
    | E => Compare_Nat.comparison (ValB n X) (ValB n Y)
    | G => G
    end.			

(*structure of the systolic comparator*)

  Let Connection := connection order Digit Digit cell.
  Let Comparator (n : nat) (o : order) (X Y : Num n) := Connection n E X Y o.

(*specification of the comparator *)

  Let Specif (n : nat) (X Y : inf n) : order :=
    Compare_Nat.comparison (val_inf n X) (val_inf n Y).

(*correctness*)

  Remark general_correct :
   forall (n : nat) (X Y : Num n) (o o' : order),
   Connection n o X Y o' -> o' = f_circ n o X Y.
  simple induction 1.
  clear H o' o Y X n.
  intros o; case o; simpl in |- *; auto.
  auto.

  clear H o' o Y X n.
  intros n o o1 o' x y X Y H_cell H_n H_rec.
  inversion_clear H_cell.
  rewrite H_rec; rewrite H.
  cut (o = o); auto.
  pattern o at 2 3 in |- *; case o; intros e; rewrite e;
   unfold f_cell in |- *; unfold f_circ in |- *; auto.
  cut
   (Compare_Nat.comparison (valB x) (valB y) =
    Compare_Nat.comparison (valB x) (valB y)); auto.
  pattern (Compare_Nat.comparison (valB x) (valB y)) at 2 3 in |- *;
   case (Compare_Nat.comparison (valB x) (valB y)); 
   intros C; apply sym_equal; unfold ValB in |- *; 
   unfold Digit in |- *; auto.
  Qed.

  Remark correctness :
   forall (n : nat) (X Y : Num n) (o : order),
   Comparator n o X Y ->
   o = Specif (exp (base BASE) n) (Val_bound n X) (Val_bound n Y).
  unfold Comparator in |- *; unfold Specif in |- *.
  intros n X Y o H. rewrite (general_correct n X Y E o H).
  auto.
  Qed.

End comparator.


