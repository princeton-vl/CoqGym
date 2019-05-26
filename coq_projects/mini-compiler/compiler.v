(* This program is free software; you can redistribute it and/or      *)
(* modify it under the terms of the GNU Lesser General Public License *)
(* as published by the Free Software Foundation; either version 2.1   *)
(* of the License, or (at your option) any later version.             *)
(*                                                                    *)
(* This program is distributed in the hope that it will be useful,    *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of     *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the      *)
(* GNU General Public License for more details.                       *)
(*                                                                    *)
(* You should have received a copy of the GNU Lesser General Public   *)
(* License along with this program; if not, write to the Free         *)
(* Software Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA *)
(* 02110-1301 USA                                                     *)



(* Correctness proof of a (very) simple compiler *)

Require Import Arith.
Require Import Omega.

Unset Standard Proposition Elimination Names.

(* source language *)

Parameter string : Set.

Inductive expr : Set :=
  | Lit : nat -> expr
  | Var : string -> expr
  | Plus : expr -> expr -> expr.

(* semantics of source language *)

Definition state := string -> nat.

Fixpoint E (s : state) (e : expr) {struct e} : nat :=
  match e with
  | Lit n => n
  | Var v => s v
  | Plus e1 e2 => E s e1 + E s e2
  end.

(* target language *)

Inductive instr : Set :=
  | LI : nat -> instr
  | LOAD : nat -> instr
  | STO : nat -> instr
  | ADD : nat -> instr.

(* memory *)

Inductive cell : Set :=
  | Acc : cell
  | Reg : nat -> cell.

Definition store := cell -> nat.

Lemma cell_eq_dec : forall c1 c2 : cell, {c1 = c2} + {c1 <> c2}.
simple destruct c1; simple destruct c2; intros; try (right; discriminate).
left; trivial.
elim (eq_nat_dec n n0); intuition.
right; intro; injection H; trivial.
Defined.

Definition update (s : store) (c : cell) (v : nat) : store :=
  fun c' : cell =>
  match cell_eq_dec c' c with
  | left _ => v
  | right _ => s c'
  end.

(* semantics of target language *)

Definition Si (s : store) (i : instr) : store :=
  match i with
  | LI n => update s Acc n
  | LOAD r => update s Acc (s (Reg r))
  | STO r => update s (Reg r) (s Acc)
  | ADD r => update s Acc (s (Reg r) + s Acc)
  end.

Require Import List.
Definition list1 (i : instr) := i :: nil.

Fixpoint Sl (s : store) (l : list instr) {struct l} : store :=
  match l with
  | nil => s
  | i :: l' => Sl (Si s i) l'
  end.

(* the compiler *)

Definition symt := string -> nat.

Fixpoint C (m : symt) (r : nat) (e : expr) {struct e} : 
 list instr :=
  match e with
  | Lit n => list1 (LI n)
  | Var s => list1 (LOAD (m s))
  | Plus e1 e2 =>
      (C m r e1 ++ list1 (STO r)) ++ C m (S r) e2 ++ list1 (ADD r)
  end.

(* lemmas *)

Lemma Sl_append :
 forall (l1 l2 : list instr) (s : store), Sl s (l1 ++ l2) = Sl (Sl s l1) l2.
Proof.
simple induction l1; simpl in |- *; intuition.
Qed.

Lemma Sl_invariant :
 forall (m : symt) (e : expr) (r r' : nat),
 r' < r -> forall s : store, Sl s (C m r e) (Reg r') = s (Reg r').
Proof.
simple induction e; simpl in |- *; intuition.
repeat rewrite Sl_append.
generalize (H r r' H1); intuition.
set (s' := Sl (Sl s (C m (S r) e0)) (list1 (STO (S r)))) in *.
assert (r' < S r). omega.
generalize (H0 (S r) r' H3); intuition.
simpl in |- *; unfold update in |- *; simpl in |- *.
rewrite H4.
case (cell_eq_dec (Reg r') (Reg r)); intro.
injection e2; omega.
rewrite H2; trivial.
Qed.

(* correctness *)

Theorem correctness :
 forall (e : expr) (m : symt) (s : state) (s' : store) (r : nat),
 (forall v : string, m v < r) ->
 (forall v : string, s v = s' (Reg (m v))) ->
 Sl s' (C m r e) Acc = E s e /\
 (forall x : nat, x < r -> Sl s' (C m r e) (Reg x) = s' (Reg x)).
Proof.
simple induction e; simpl in |- *; intros.
intuition.
intuition.
unfold update in |- *; simpl in |- *; intuition.
repeat rewrite Sl_append.
generalize (H m s s' r H1 H2).
intros (H3, H4).
set (s'' := Sl (Sl s' (C m r e0)) (list1 (STO r))) in *.
assert (H01 : forall v : string, m v < S r).
intuition.
assert (H02 : forall v : string, s v = s'' (Reg (m v))).
intro; unfold s'' in |- *; simpl in |- *; unfold update in |- *.
case (cell_eq_dec (Reg (m v)) (Reg r)); intro.
injection e2; generalize (H1 v); omega.
rewrite H2. rewrite H4. trivial.
intuition.
generalize (H0 m s s'' (S r) H01 H02); intuition.
simpl in |- *.
rewrite H6.
unfold s'' in |- *; simpl in |- *.
rewrite H3.
unfold update in |- *; simpl in |- *.
apply (f_equal2 plus); trivial.
rewrite Sl_invariant. 
case (cell_eq_dec (Reg r) (Reg r)); intro.
trivial.
elim n; trivial. omega.
simpl in |- *.
rewrite H7.
unfold s'' in |- *; simpl in |- *.
rewrite H3.
unfold update in |- *; simpl in |- *.
rewrite Sl_invariant. 
case (cell_eq_dec (Reg x) (Reg r)); intro.
injection e2; omega.
rewrite H4; trivial.
omega.
omega.
Qed.






