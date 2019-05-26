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


(** %\subsection*{ support :  omit.v }%*)
(** - (omit v i) = $\langle v_0...v_{i-1},v_{i+1}...v_{n-1}\rangle$ *)
Set Implicit Arguments.
Unset Strict Implicit.
Require Export empty.
Require Export conshdtl.

(** %\label{omit}% *)
Definition omit :
  forall (A : Setoid) (n : Nat), seq n A -> fin n -> seq (pred n) A.
destruct n.
auto.
induction  n as [| n Hrecn].
intros.
apply (empty_seq A).
intros.
case X0.
intro x; case x.
intro.
exact (Seqtl X).
intros.
exact (head X;; Hrecn (Seqtl X) (Build_finiteT (lt_S_n _ _ in_range_prf))).
Defined.

Lemma omit_comp :
 forall (A : Setoid) (n : Nat) (v v' : seq n A) (i i' : fin n),
 v =' v' in _ -> i =' i' in _ -> omit v i =' omit v' i' in _.
destruct n.
intros.
auto with algebra.
induction  n as [| n Hrecn].
intros.
unfold omit in |- *.
unfold nat_rect in |- *.
auto with algebra.
intros v v' i.
case i.
intros x l i'.
case i'.
intros.
apply Trans with (omit v' (Build_finiteT l)).
unfold omit in |- *.
unfold nat_rect in |- *.
generalize l H0; clear H0 l.
destruct x as [| n0].
intros.
change (Seqtl v =' Seqtl v' in _) in |- *. 
apply Seqtl_comp; auto with algebra.
intros.
simpl in |- *.
apply cons_comp; auto with algebra.
unfold omit in Hrecn.
unfold nat_rect in Hrecn.
apply Hrecn.
change (Seqtl v =' Seqtl v' in _) in |- *.
apply Seqtl_comp; auto with algebra.
auto with algebra.
unfold omit in |- *.
unfold nat_rect in |- *.
generalize l H0; clear H0 l.
destruct x as [| n0].
destruct index as [| n0].
intros; auto with algebra.
intros.
simpl in H0.
inversion H0.
intros.
generalize l H0; clear H0 l.
destruct index as [| n1].
intros.
simpl in H0.
inversion H0.
intros.
simpl in |- *.
apply cons_comp; auto with algebra.
unfold omit in Hrecn.
unfold nat_rect in Hrecn.
apply Hrecn; auto with algebra.
Qed.

Hint Resolve omit_comp: algebra.


(** - The following are actually definitions. omit_removes does the following: 
 suppose v:(seq n A) and i:(fin n). Define w:=(omit v i). Then given j, (w j)
 = (v j') for some j'. Omit_removes returns this j' and a proof of this fact
 (packed together in a sigma-type). *)

Lemma omit_removes :
 forall (n : Nat) (A : Setoid) (v : seq n A) (i : fin n) (j : fin (pred n)),
 sigT (fun i' => v i' =' omit v i j in _).
destruct n.
intros.
apply False_rect; auto with algebra.

intros.
generalize (j:fin n).
clear j.
intro j.

induction  n as [| n Hrecn].
apply False_rect.
apply fin_O_nonexistent; auto with algebra.

case i.
intro x; case x.
intros.
set (l := in_range_prf) in *.
case j.
intros.
set (l0 := in_range_prf0) in *.
apply
 (existT
    (fun i' : fin (S (S n)) =>
     Ap v i' =' omit v (Build_finiteT l) (Build_finiteT l0) in _)
    (Build_finiteT (lt_n_S _ _ l0))).
apply Trans with (Seqtl v (Build_finiteT l0)); auto with algebra.

intros.
rename in_range_prf into l.
case j.
intro x0; case x0.
intro l0.
apply
 (existT
    (fun i' : fin (S (S n)) =>
     Ap v i' =' Ap (omit v (Build_finiteT l)) (Build_finiteT l0) in _)
    (Build_finiteT (lt_O_Sn (S n)))).
apply Trans with (head (omit v (Build_finiteT l))); auto with algebra.

intros.
rename in_range_prf into l0.
generalize
 (Hrecn (Seqtl v) (Build_finiteT (lt_S_n _ _ l))
    (Build_finiteT (lt_S_n _ _ l0))).
intro.
inversion_clear X.
generalize H.
clear H.
case x1.
intros.
apply
 (existT
    (fun i' : fin (S (S n)) =>
     Ap v i' =' Ap (omit v (Build_finiteT l)) (Build_finiteT l0) in _)
    (Build_finiteT (lt_n_S _ _ in_range_prf))).
apply
 Trans
  with
    ((head v;; omit (Seqtl v) (Build_finiteT (lt_S_n _ _ l)))
       (Build_finiteT l0)); auto with algebra.
Defined.

(** - omit_removes' on the other hand does this: suppose again v:(seq n A) and i:(fin n)
 and define w:=(omit v i). Suppose that this time j:(fin n). If [~i='j] then (v j)='(w j')
 for some j'; again omit_removes' returns this j' and a proof. *)

Lemma omit_removes' :
 forall (n : Nat) (A : Setoid) (v : seq n A) (i j : fin n),
 ~ i =' j in _ -> sigT (fun j' => v j =' omit v i j' in _).
destruct n.
intros.
apply False_rect; auto with algebra.

induction  n as [| n Hrecn].
intros.
absurd (i =' j in _).
auto.
apply fin_S_O_unique; auto with algebra.
intros A v i.
elim i.
intro i'; case i'.
intros Hi j.
elim j.
intro j'; case j'.
intros.
simpl in H.
absurd (0 = 0); auto.
intros n0 p0 H.
exists (Build_finiteT (lt_S_n _ _ p0)).
simpl in |- *.
apply Ap_comp; auto with algebra.
simpl in |- *.
auto.

intros gat Hg vraag. 
elim vraag.
intro vr; case vr.
intros Hvr H.
exists (Build_finiteT (lt_O_Sn n)).
simpl in |- *.
unfold head in |- *.
apply Ap_comp; auto with algebra.
simpl in |- *.
auto.

intros vr' Hvr H.
assert
 (~ Build_finiteT (lt_S_n _ _ Hg) =' Build_finiteT (lt_S_n _ _ Hvr) in fin _).
simpl in |- *; simpl in H; auto.
set (aw := Hrecn _ (Seqtl v) _ _ H0) in *.
case aw.
intro x; elim x.
intros.
exists (Build_finiteT (lt_n_S _ _ in_range_prf)).
apply Trans with (Seqtl v (Build_finiteT (lt_S_n vr' (S n) Hvr))).
apply Sym.
apply Seqtl_to_seq; auto with algebra.
apply
 Trans
  with
    (omit (Seqtl v) (Build_finiteT (lt_S_n gat (S n) Hg))
       (Build_finiteT in_range_prf)); auto with algebra.
Defined.