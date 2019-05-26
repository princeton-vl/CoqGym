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


(** * lin_comb_facts.v *)
Set Implicit Arguments.
Unset Strict Implicit.
Require Export algebraic_span_facts.
Require Export seq_set_seq.

(** - Miscellaneous facts about linear combinations:

 - Suppose $x$ is a linear combination of $W$, and all $w\in W$ are linear combinations
 of $W'$, then $x$ is a linear combination of $W'$ *)

Lemma lin_comb_casting :
 forall (F : field) (V : vectorspace F) (W W' : part_set V) (x : V),
 is_lin_comb x W ->
 (forall w : W, is_lin_comb (subtype_elt w) W') -> is_lin_comb x W'.
intros.
change (in_part x (span W')) in |- *.
elim (span_idempotent W' x).
intros.
apply H2; auto with algebra; clear H1 H2.
simpl in |- *.
assert (forall w : W, in_part (subtype_elt w) (span_set W')).
auto.
clear H0.
inversion_clear H.
inversion_clear H0.
inversion_clear H.
red in |- *.
exists x0.
exists x1.
assert (forall i : fin x0, in_part (Map_embed x2 i) (span_set W')).
intro i.
change (in_part (subtype_elt (x2 i)) (span_set W')) in |- *.
auto.
exists (cast_map_to_subset H).
apply Trans with (sum (mult_by_scalars x1 (Map_embed x2))); auto with algebra.
Qed.


(** - If all $w\in W$ are linear combinations of $W'$ then $span(W)\subset span(W')$ *)

Lemma span_casting :
 forall (F : field) (V : vectorspace F) (W W' : part_set V),
 (forall w : W, is_lin_comb (subtype_elt w) W') ->
 included (span W) (span W').
intros; simpl in |- *.
red in |- *; simpl in |- *.
intros.
apply lin_comb_casting with W; auto with algebra.
Qed.

Lemma lin_comb_scalar_multiplied :
 forall (F : field) (V : vectorspace F) (x : V) (n : Nat) 
   (a : seq n F) (v : seq n V) (c : F),
 x =' c mX sum (mult_by_scalars a v) in _ -> is_lin_comb x (seq_set v).
intros.
red in |- *.
exists n.
set (axc_fun := fun i : fin n => c rX a i) in *.
assert (axc_comp : fun_compatible axc_fun).
red in |- *.
intros.
unfold axc_fun in |- *.
apply RING_comp; auto with algebra.
set (axc := Build_Map axc_comp:seq _ _) in *.
exists axc.
exists (seq_set_seq v).
apply Trans with (sum (mult_by_scalars axc v)).
apply Trans with (c mX sum (mult_by_scalars a v)); auto with algebra.
apply
 Trans with (sum (mult_by_scalars (const_seq n c) (mult_by_scalars a v)));
 auto with algebra.
apply sum_comp; auto with algebra.
simpl in |- *.
red in |- *; intros.
unfold mult_by_scalars, axc in |- *.
simpl in |- *.
unfold axc_fun in |- *.
auto with algebra.
apply sum_comp; auto with algebra.
Qed.

Lemma lin_comb_omit :
 forall (F : field) (V : vectorspace F) (x : V) (n : Nat) 
   (a : seq n F) (v : seq n V) (i : fin n),
 x =' sum (omit (mult_by_scalars a v) i) in _ -> is_lin_comb x (seq_set v).
intros.
red in |- *.
exists n.
exists (modify_seq a i (zero F)).
exists (seq_set_seq v).
apply Trans with (sum (mult_by_scalars (modify_seq a i (zero F)) v)).
2: apply sum_comp; auto with algebra.
apply Trans with (sum (modify_seq (mult_by_scalars a v) i ((zero F) mX v i))).
2: apply sum_comp; auto with algebra.

apply
 Trans
  with
    (sum (mult_by_scalars a v) +' (min mult_by_scalars a v i) +'
     (zero F) mX v i); auto with algebra.

apply
 Trans
  with (sum (mult_by_scalars a v) +' (min mult_by_scalars a v i) +' (zero V));
 auto with algebra.
apply Trans with (sum (mult_by_scalars a v) +' (min mult_by_scalars a v i));
 auto with algebra.
apply Trans with (sum (omit (mult_by_scalars a v) i)); auto with algebra.
Qed.