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
(*                              August 6th 1996                             *)
(*                                                                          *)
(****************************************************************************)
(*                            Lists_of_Numerals.v                           *)
(****************************************************************************)

Require Export Lists_of_lists.
Require Export Numerals.

Section lists_of_numerals.

  Variable BASE : BT.
  Let b := base BASE.
  Let Digit := digit BASE.
  Let Num := num BASE.
  Let Val_bound := val_bound BASE.

(*from a list of lists of naturals, namely the inputs of the cells,
builds the list of the values corresponding to the numerals obtained
by taking the first elements of each components).*)

  Definition val_first_components (n i : nat)
    (X : list (list Digit (S i)) n) :=
    Val_bound n (list_of_heads Digit i n X).

(*from a list of lists of naturals, namely the inputs of the cells,
builds the list of the values corresponding to the numerals obtained
by taking the ith element of each components, for 1<=i<=n).*)


  Fixpoint list_of_values (n i : nat) {struct i} :
   list (list Digit i) n -> list (inf (exp b n)) i :=
    match
      i as x return (list (list Digit x) n -> list (inf (exp b n)) x)
    with
    | O => fun l : list (list Digit 0) n => nil (inf (exp b n))
    | S p =>
        fun l : list (list Digit (S p)) n =>
        cons (inf (exp b n)) p (val_first_components n p l)
          (list_of_values n p (list_of_tails Digit (S p) n l))
    end.

End lists_of_numerals.