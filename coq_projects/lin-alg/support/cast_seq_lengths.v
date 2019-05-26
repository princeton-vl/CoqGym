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


(** %\subsection*{ support :  cast\_seq\_lengths.v }%*)
Set Implicit Arguments.
Unset Strict Implicit.
Require Export finite.

(** - An important and annoying obstacle when dealing with seqs is that 
 v and w belong to the same setoid only if their types are convertible. 
 This means that v:(seq n A) and w:(seq k A) cannot be compared, even if 
 we have a proof that n=k. We cannot even %{\em state}% the equality because 
 the expression v='w is ill-typed! 
 - In this file we provide tools to convert between sequences (and their indices) 
 of the same length, if only we are given a proof of the fact. Note that these 
 casting-functions get in the way of many useful lemmas, unfortunately... *)

Section MAIN.
Lemma lt_comp : forall m n n' : Nat, m < n -> n =' n' in _ -> m < n'.
intros.
rewrite <- H0.
auto.
Qed.

(** %\label{castfin}% *)
Definition cast_fin : forall n n' : Nat, fin n -> n =' n' in _ -> fin n'.
intros.
destruct X.
exact (Build_finiteT (lt_comp in_range_prf H)).
Defined.

Lemma cast_fin_comp :
 forall (n n' : Nat) (i i' : fin n) (H H' : n =' n' in _),
 i =' i' in _ -> cast_fin i H =' cast_fin i' H' in _.
intros until H'.
unfold cast_fin in |- *.
case i; case i'.
simpl in |- *.
auto.
Qed.

Hint Resolve cast_fin_comp: algebra.

Variable A : Setoid.

Definition cast_seq : forall n n' : Nat, seq n A -> n =' n' in _ -> seq n' A.
intros.
destruct X.
set (Ap' := fun i : fin n' => Ap (cast_fin i (sym_eq H))) in *.
assert (Mcp' : fun_compatible Ap').
red in |- *; red in Map_compatible_prf.
unfold Ap' in |- *.
intros.
apply Map_compatible_prf; auto with algebra.
exact (Build_Map Mcp').
Defined.

Lemma cast_seq_comp :
 forall (n n' : Nat) (v v' : seq n A) (H H' : n =' n' in _),
 v =' v' in _ -> cast_seq v H =' cast_seq v' H' in _.
unfold cast_seq in |- *.
intros until H'.
case v; case v'.
simpl in |- *.
red in |- *.
simpl in |- *.
intros.
red in H0.
simpl in H0.
apply Trans with (Ap0 (cast_fin x (sym_eq H'))); auto with algebra.
Qed.

Hint Resolve cast_seq_comp: algebra.

Variable n n' : Nat.
Variable v : seq n A.

Lemma cast_seq_cast_fin :
 forall (i : fin n) (H H' : n =' n' in _),
 v i =' cast_seq v H (cast_fin i H') in _.
intros.
unfold cast_seq, cast_fin in |- *.
destruct v.
simpl in |- *.
destruct i.
apply Map_compatible_prf; auto with algebra.
Qed.

Lemma cast_seq_cast_fin' :
 forall (i : fin n') (H : n =' n' in _) (H' : n' =' n in _),
 cast_seq v H i =' v (cast_fin i H') in _.
intros.
unfold cast_seq, cast_fin in |- *.
destruct v.
simpl in |- *.
destruct i.
apply Map_compatible_prf; auto with algebra.
Qed.

Hint Resolve cast_seq_cast_fin cast_seq_cast_fin': algebra.
End MAIN.
Hint Resolve cast_fin_comp: algebra.
Hint Resolve cast_seq_comp: algebra.
Hint Resolve cast_seq_cast_fin cast_seq_cast_fin': algebra.