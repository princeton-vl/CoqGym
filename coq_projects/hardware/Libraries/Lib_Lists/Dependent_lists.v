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
(*                          Dependent_lists.v                               *)
(****************************************************************************)

Require Export Eqdep.
Require Export Arith.

Global Set Asymmetric Patterns.
Section Dependent_lists.

  Variable A : Set.

  Inductive list : nat -> Set :=
    | nil : list 0
    | cons : forall n : nat, A -> list n -> list (S n).

  Definition eq_list := eq_dep nat list.

  Definition hd (n : nat) (l : list n) : Exc A :=
    match l in (list m) return (Exc A) with
    | nil => error
    | cons p a l' => value a
    end.

  Definition head (n : nat) (l : list n) :=
    match l in (list p) return (0 < p -> A) with
    | nil =>
        (* nil*)	
        fun h : 0 < 0 => False_rec A (lt_irrefl 0 h)
        (*cons p a l' *)
    | cons p a l' => fun h : 0 < S p => a
    end.

                           
  Definition Head (n : nat) (l : list (S n)) := head (S n) l (lt_O_Sn n).

  Definition tl (n : nat) (l : list n) : list (pred n) :=
    match l in (list m) return (list (pred m)) with
    | nil => nil
    | cons p a l' => l'
    end.


  Lemma empty_dep : forall (n : nat) (l : list n), n = 0 -> eq_list 0 nil n l.
  unfold eq_list in |- *; intros n l.
  dependent inversion_clear l; auto.
  intros H; absurd (S n0 = 0); auto.
  Qed.

  Hint Resolve empty_dep.

  Lemma empty : forall l : list 0, nil = l.
  intros l.
  apply (eq_dep_eq nat list 0).
  apply empty_dep; auto.
  Qed.

  Hint Resolve empty.

  Remark non_empty_dep :
   forall n m : nat,
   m = S n ->
   forall l : list (S n),
   {h : A &  {t : list n | eq_list (S n) l (S n) (cons n h t)}}.
  intros n m H l.
  generalize H; clear H.
  dependent inversion_clear l
   with
    (fun (n' : nat) (l : list n') =>
     m = n' -> {a : A &  {l' : list n | eq_list n' l (S n) (cons n a l')}}).
  unfold eq_list in |- *.
  intros H; exists a; exists l0; auto.

  Defined.


  Lemma non_empty :
   forall (n : nat) (l : list (S n)),
   {a : A &  {t : list n | l = cons n a t}}. 
  intros n l.
  cut
   (sigS
      (fun a : A =>
       sig (fun t : list n => eq_list (S n) l (S n) (cons n a t)))).
  intros H; elim H; clear H.
  intros a H; elim H; clear H.
  intros t H.
  exists a; exists t.
  apply eq_dep_eq with (U := nat) (P := list) (p := S n).
  unfold eq_list in H; auto.
  apply (non_empty_dep n (S n)); auto.
  Defined.


  Lemma split_list :
   forall (n : nat) (l : list (S n)),
   l = cons n (head (S n) l (lt_O_Sn n)) (tl (S n) l).
  intros n l.
  elim (non_empty n l).
  intros h H; elim H; clear H.
  intros t e.
  rewrite e; simpl in |- *.
  auto.
  Qed.

  Definition Hd (n : nat) (l : list (S n)) :=
    let (a, P) return A := non_empty n l in a.

  Lemma Non_empty_Hd :
   forall (n : nat) (a : A) (l : list n), Hd n (cons n a l) = a.
  intros n a l; unfold Hd in |- *.
  elim (non_empty n (cons n a l)).
  intros x H; elim H.
  clear H; intros X H.
  injection H; auto.
  Qed.

End Dependent_lists.

Hint Resolve empty_dep empty non_empty Non_empty_Hd.

Fixpoint map (A B : Set) (f : A -> B) (n : nat) (l : list A n) {struct l} :
 list B n :=
  match l in (list _ x) return (list B x) with
  | nil =>
      (*(nil A)*)  nil B
      (*(cons A p a t*) 
  | cons p a t => cons B p (f a) (map A B f p t)
  end.


(**********************************************************************)