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


(** %\subsection*{ support :  seq\_equality.v }%*)
Set Implicit Arguments.
Unset Strict Implicit.
Require Export cast_seq_lengths.

(** - We cannot compare v++w and w++v using =' since they have non-convertible
 lengths (n+k $v.$ k+n) and hence are judged to stem from different setoids. 
 We have two complementing ways of dealing with sequences of equal 
 but non-convertible lengths: one is using casting functions (see cast_seq_lengths.v),
 the other is defining a different equality predicate for sequences: seq_equal.
 Two sequences v:(seq n A) and w:(seq k A) are seq_equal if every i:nat 
 is either out of both sequences' bounds (ie. $i\geq n$ and $i\geq k$), or there 
 exist proofs that we can use to turn i into a (fin n) and (fin k), so 
 that "v(i)=w(i)"

 %\label{seqequal}% *)

Definition seq_equal (A : Setoid) (n m : Nat) (v : seq n A) 
  (w : seq m A) :=
  forall i : Nat,
  (exists p : i < n,
     (exists q : i < m, v (Build_finiteT p) =' w (Build_finiteT q) in _)) \/
  n <= i /\ m <= i.


(** - Of course seq_equal holds for ='-equal sequences *)
Lemma Map_eq_seq_equal :
 forall (A : Setoid) (n : Nat) (v w : seq n A), v =' w in _ -> seq_equal v w.
intros.
red in |- *.
intro.
generalize (le_or_lt n i).
intro p; inversion_clear p.
right; split; auto.
left.
repeat exists H0.
simpl in H; red in H; simpl in H; apply H.
Qed.

(** - And the other way around, if v and w happen to have the same type *)

Lemma seq_equal_map_equal :
 forall (A : Setoid) (n : Nat) (v w : seq n A), seq_equal v w -> v =' w in _.
intros.
simpl in |- *.
red in |- *.
intro.
red in H.
destruct x.
rename index into i.
generalize (H i); clear H; intro.
inversion_clear H.
inversion_clear H0.
inversion_clear H.
apply Trans with (v (Build_finiteT x)).
apply Ap_comp; auto with algebra; simpl in |- *; auto.
apply Trans with (w (Build_finiteT x0)); auto with algebra.
apply Ap_comp; auto with algebra; simpl in |- *; auto.
inversion_clear H0; (apply False_ind; auto with algebra).
apply (le_not_lt n i); auto with algebra.
Qed.

Hint Resolve seq_equal_map_equal: algebra.



(* Of course it's an equivalence relation: refl, symm, trans *)
Lemma seq_equal_refl :
 forall (A : Setoid) (n : Nat) (v : seq n A), seq_equal v v.
intros.
apply Map_eq_seq_equal; auto with algebra.
Qed.

Hint Resolve seq_equal_refl: algebra.


Lemma seq_equal_symm :
 forall (A : Setoid) (n m : Nat) (v : seq n A) (w : seq m A),
 seq_equal v w -> seq_equal w v.
intros.
red in |- *; red in H; intro; generalize (H i); clear H; intro.
inversion_clear H.
left.
inversion_clear H0.
inversion_clear H.
exists x0.
exists x.
apply Sym; auto with algebra.
right.
inversion_clear H0; split; trivial.
Qed.

Hint Immediate seq_equal_symm: algebra.


Lemma seq_equal_trans :
 forall (A : Setoid) (n m l : Nat) (v : seq n A) (w : seq m A) (u : seq l A),
 seq_equal v w -> seq_equal w u -> seq_equal v u.
intros.
red in H, H0.
red in |- *; intro.
generalize (H i) (H0 i); clear H H0; intros.
inversion_clear H; inversion_clear H0.
left.
inversion_clear H1; inversion_clear H.
exists x.
inversion_clear H0; inversion_clear H1.
exists x2.
apply Trans with (w (Build_finiteT x1)); auto with algebra.
apply Trans with (w (Build_finiteT x0)); auto with algebra.
inversion_clear H1; inversion_clear H.
inversion_clear H0.
apply False_ind; auto with algebra.
generalize (lt_not_le i m); intro p; red in p.
auto.
inversion_clear H1; inversion_clear H.
apply False_ind; auto with algebra.
generalize (lt_not_le i m); intro p; red in p.
auto.
right.
inversion_clear H; inversion_clear H1; split; auto.
Qed.

Hint Resolve seq_equal_trans: algebra.




(* Finally, the interplay with casting functions: *)
Lemma cast_seq_preserves_seq_equal :
 forall (A : Setoid) (n m : Nat) (v : seq n A) (H : n =' m in _),
 seq_equal v (cast_seq v H).
red in |- *; intros.
generalize (le_or_lt n i).
intro p; inversion_clear p.
right.
split; try trivial.
rewrite <- H.
trivial.
left.
exists H0.
exists (lt_comp H0 H).
apply Trans with (cast_seq v H (cast_fin (Build_finiteT H0) H)).
apply cast_seq_cast_fin; auto with algebra.
unfold cast_fin in |- *.
auto with algebra.
Qed.

Hint Resolve cast_seq_preserves_seq_equal: algebra.