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
(*                            Lib_Set_Products.v                            *)
(****************************************************************************)

Lemma pair_fst_snd : forall (A B : Set) (c : A * B), (fst c, snd c) = c.
intros.
pattern c in |- *; elim c; auto.
Qed.


Inductive prod_3 (A B C : Set) : Set :=
    triplet : A -> B -> C -> prod_3 A B C.

Section programming_3.
        
Variable A B C : Set.

Theorem fst_3 : prod_3 A B C -> A.
simple induction 1; try trivial.
Defined.

Theorem snd_3 : prod_3 A B C -> B.
simple induction 1; try trivial.
Defined.

Theorem thd_3 : prod_3 A B C -> C.
simple induction 1; try trivial.
Defined.

End programming_3.

Notation Fst_3 := (fst_3 _ _ _) (only parsing).
Notation Snd_3 := (snd_3 _ _ _) (only parsing).
Notation Thd_3 := (thd_3 _ _ _) (only parsing).
Notation Triplet := (triplet _ _ _) (only parsing).



(************************************************************************)

Lemma triplet_fst_snd_thd :
 forall (A B C : Set) (c : prod_3 A B C),
 triplet _ _ _ (fst_3 _ _ _ c) (snd_3 _ _ _ c) (thd_3 _ _ _ c) = c.
intros.
pattern c in |- *; elim c; auto.
Qed.


(************************************************************************)
Definition ifProp (C : Type) (b : bool) (x y : C) : C :=
  match b return C with
  | true => x
  | false => y
  end.

Lemma ifProp_or : forall (b : bool) (P Q : Prop), ifProp Prop b P Q -> P \/ Q.
simple induction b; auto.
Qed.
(************************************************************************)