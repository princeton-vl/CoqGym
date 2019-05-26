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


(** %\subsection*{ support :  conshdtl.v }%*)
Set Implicit Arguments.
Unset Strict Implicit.
Require Export finite.
From Algebra Require Export Parts.

(** - This file introduces the "cons" operator on sequences (called "conseq" here to
 avoid confusion with the normal notion for Lists). It is denoted as "a;;v" instead
 of "a::v" since the latter is already taken in coq.
 - Also it defines "Seqtl" (the "tail" operator) and "head". *)

Section MAIN.

(* conseq adjoins an element x of X to finite functions f:(fin N)->X *)
(* This is done by {0->x; m+1->f(m)} : (fin N+1)->X, ie. the new element *)
(* is inserted at the front. That's why it's called conseq: it's the seq *)
(* variant of the cons operator as seen in lists *)

(** %\label{conseq}% *)

Definition conseq :
  forall (A : Setoid) (n : Nat) (a : A) (v : seq n A), seq (S n) A.
intros.
apply
 (Build_Map
    (Ap:=fun m : fin (S n) =>
         match m return (A:Type) with
         | Build_finiteT x0 x1 =>
             match x0 as x2 return (x2 < S n -> (A:Type)) with
             | O => fun _ : 0 < S n => a
             | S m' =>
                 fun HSm' : S m' < S n =>
                 Ap v (Build_finiteT (lt_S_n m' n HSm'))
             end x1
         end)).
red in |- *.
simpl in |- *.
intros x0 y.
case x0.
case y.
simpl in |- *.
intros x2 y1.
induction x2.
intros x2 y2.
induction x2.
intro; apply Refl.
intro H.
inversion H.
clear IHx2.
simple induction index.
intros h H.
inversion H.
intros. 
clear H.
apply Ap_comp; auto with algebra.
Defined.

Notation "a ;; b" := (conseq a b) (at level 60, right associativity).

Variables (A : Setoid) (n : Nat) (a : A).

Lemma cons_comp :
 forall (a' : A) (v v' : seq n A),
 a =' a' in _ -> v =' v' in _ -> a;; v =' a';; v' in _.
intros.
simpl in |- *.
red in |- *.
intro i'.
elim i'.
intro i.
simpl in |- *.
case i.
auto.
intros.
apply Ap_comp; auto with algebra.
Qed.

Hint Resolve cons_comp: algebra.

Lemma cons_first_element :
 forall (v : seq n A) (H : 0 < S n), (a;; v) (Build_finiteT H) =' a in _.
auto with algebra.
Qed.

(** %\label{head}% *)
Definition head (A : Setoid) (n : Nat) (v : seq (S n) A) :=
  v (Build_finiteT (lt_O_Sn n)).

Lemma head_comp :
 forall (A : Setoid) (n : Nat) (v v' : seq (S n) A),
 v =' v' in _ -> head v =' head v' in _.
unfold head in |- *.
auto with algebra.
Qed.

Hint Resolve head_comp cons_first_element: algebra.

(** - these two lemmas are mainly useful for the algebra Hints database 
 (hence the names) *)
Lemma head_unfolding1 :
 forall v : seq (S n) A,
 v (Build_finiteT (lt_O_Sn n)) =' a in _ -> head v =' a in _.
auto with algebra.
Qed.

Lemma head_unfolding2 :
 forall v : seq (S n) A,
 a =' v (Build_finiteT (lt_O_Sn n)) in _ -> a =' head v in _.
auto with algebra.
Qed.

Hint Resolve head_unfolding1 head_unfolding2: algebra.
Hint Extern 0 (head _ =' _ in _) => unfold head in |- *: algebra.
Hint Extern 0 (_ =' head _ in _) => unfold head in |- *: algebra.

Lemma head_cons_inv : forall v : seq n A, head (a;; v) =' a in _.
auto with algebra.
Qed.

Hint Resolve head_cons_inv: algebra.

Lemma seq_S_O_contains_single_elt :
 forall (A : Setoid) (v : seq 1 A) (i : fin 1), v i =' head v in _.
intros.
unfold head in |- *.
apply Ap_comp; auto with algebra.
Qed.

Hint Resolve seq_S_O_contains_single_elt: algebra.

Lemma seq_S_O_head_fixes_everything :
 forall (A : Setoid) (v v' : seq 1 A), head v =' head v' in _ -> v =' v' in _.
intros.
simpl in |- *.
red in |- *.
intro.
apply Trans with (head v).
apply seq_S_O_contains_single_elt; auto with algebra.
apply Trans with (head v'); auto with algebra.
Qed.

Hint Resolve seq_S_O_head_fixes_everything: algebra.

Lemma cons_later_elements :
 forall (v : seq n A) (i : Nat) (Hi : S i < S n) (Hi' : i < n),
 (a;; v) (Build_finiteT Hi) =' v (Build_finiteT Hi') in _.
intros.
simpl in |- *.
apply Ap_comp; auto with algebra.
Qed.

Hint Resolve cons_later_elements: algebra.

(* Taking the "tl" of a sequence *)
(** %\label{Seqtl}% *)
Definition Seqtl : forall n : Nat, seq n A -> seq (pred n) A. 
clear n.
intro n.
case n.
intro f.
exact f.
intros m f.
apply
 (Build_Map
    (Ap:=fun i' : fin m =>
         match i' with
         | Build_finiteT i Hi => f (Build_finiteT (lt_n_S _ _ (Hi:i < m)))
         end)).
red in |- *.
intros x y.
case x.
case y.
simpl in |- *.
intros.
apply Ap_comp; auto with algebra.
Defined.

Lemma Seqtl_comp :
 forall v v' : seq n A, v =' v' in _ -> Seqtl v =' Seqtl v' in _.
induction n.
intros.
simpl in |- *.
auto.
intros.
simpl in |- *.
red in |- *.
simpl in |- *.
intro.
elim x.
intros.
apply Ap_comp; auto with algebra.
Qed.

Hint Resolve Seqtl_comp: algebra.

(** - "hdtl" is a 'tool' for writing a sequence as the cons of its head and its tail
 %\label{hdtl}% *)

Definition hdtl (v : seq (S n) A) := head v;; Seqtl v:seq (S n) A.

Lemma conseq_hdtl :
 forall (v : seq (S n) A) (H : 0 < S n),
 v =' v (Build_finiteT H);; Seqtl v in _.
(* note we don't say v='(head v);;(Seqtl v): we want freedom in the choice of the proof H *)
intros.
simpl in |- *.
red in |- *.
simpl in |- *.
intro x.
case x.
intro.
case index.
intros; apply Ap_comp; simpl in |- *; auto with algebra arith.
red in |- *; auto with algebra.
intros; apply Ap_comp; simpl in |- *; auto with algebra arith.
red in |- *; auto with algebra.
Qed.

Hint Resolve conseq_hdtl: algebra.

Lemma hdtl_x_is_x : forall v : seq (S n) A, v =' hdtl v in _.
unfold hdtl in |- *.
intros.
unfold head in |- *.
apply conseq_hdtl.
Qed.

Hint Resolve hdtl_x_is_x: algebra.
Hint Extern 0 (head _;; Seqtl _ =' _ in _) =>
  fold hdtl in |- *; apply Sym; apply hdtl_x_is_x: algebra.
Hint Extern 0 (_ =' head _;; Seqtl _ in _) =>
  fold hdtl in |- *; apply hdtl_x_is_x: algebra.

Lemma cons_lemma_nice :
 forall P : Predicate (seq (S n) A),
 (forall (a : A) (v : seq n A), Pred_fun P (a;; v)) ->
 forall w : seq (S n) A, Pred_fun P w.
intro.
elim P.
intros.
unfold pred_compatible in Pred_compatible_prf.
apply Pred_compatible_prf with (hdtl w); auto with algebra.
unfold hdtl in |- *.
apply H.
Qed.

Lemma cons_lemma_verynice :
 forall (P : Predicate (seq (S n) A)) (H : 0 < S n) (w : seq (S n) A),
 Pred_fun P (w (Build_finiteT H);; Seqtl w) -> Pred_fun P w.
intros P H w. 
elim P.
intros.
unfold pred_compatible in Pred_compatible_prf.
apply Pred_compatible_prf with (w (Build_finiteT H);; Seqtl w);
 auto with algebra.
Qed.

Lemma Seqtl_cons_inv : forall v : seq n A, Seqtl (a;; v) =' v in _.
intros.
simpl in |- *.
red in |- *.
simpl in |- *.
intro i.
elim i.
intros.
apply Ap_comp; auto with algebra.
Qed.

Hint Resolve Seqtl_cons_inv: algebra.

Lemma Seqtl_to_seq :
 forall (v : seq (S n) A) (i : Nat) (Hi : i < n) (HSi : S i < S n),
 Seqtl v (Build_finiteT Hi) =' v (Build_finiteT HSi) in _.
intros.
simpl in |- *.
apply Ap_comp; auto with algebra.
Qed.

Hint Resolve Seqtl_to_seq: algebra.

Lemma split_hd_tl_equality :
 forall v w : seq (S n) A,
 head v =' head w in _ -> Seqtl v =' Seqtl w in _ -> v =' w in _.
intros.
intro.
destruct x.
destruct index as [| n0].
apply Trans with (head v); auto with algebra.
apply Trans with (head w); auto with algebra.
apply Trans with (Seqtl v (Build_finiteT (lt_S_n _ _ in_range_prf)));
 auto with algebra.
apply Trans with (Seqtl w (Build_finiteT (lt_S_n _ _ in_range_prf)));
 auto with algebra.
Qed.

Hint Resolve split_hd_tl_equality: algebra.
End MAIN.

(* Hints and notation inside sections is forgotten... *)
Notation "a ;; b" := (conseq a b) (at level 60, right associativity).

Hint Resolve cons_comp: algebra.
Hint Resolve head_comp cons_first_element: algebra.
Hint Resolve head_unfolding1 head_unfolding2: algebra.
Hint Extern 0 (head _ =' _ in _) => unfold head in |- *: algebra.
Hint Extern 0 (_ =' head _ in _) => unfold head in |- *: algebra.
Hint Resolve head_cons_inv: algebra.
Hint Resolve cons_later_elements: algebra.
Hint Resolve Seqtl_comp: algebra.
Hint Resolve conseq_hdtl: algebra.
Hint Resolve hdtl_x_is_x: algebra.
Hint Extern 0 (head _;; Seqtl _ =' _ in _) =>
  fold hdtl in |- *; apply Sym; apply hdtl_x_is_x: algebra.
Hint Extern 0 (_ =' head _;; Seqtl _ in _) =>
  fold hdtl in |- *; apply hdtl_x_is_x: algebra.
Hint Resolve Seqtl_cons_inv: algebra.
Hint Resolve Seqtl_to_seq: algebra.
Hint Resolve split_hd_tl_equality: algebra.
Hint Resolve seq_S_O_contains_single_elt: algebra.
Hint Resolve seq_S_O_head_fixes_everything: algebra.
