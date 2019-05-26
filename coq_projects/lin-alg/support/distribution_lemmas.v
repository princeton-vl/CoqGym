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


(** %\subsection*{ support :  distribution\_lemmas.v }%*)
Set Implicit Arguments.
Unset Strict Implicit.
Require Export mult_by_scalars.
Require Export const.
Require Export sums.

(** - $r\sum_i a_i = \sum_i ra_i$ (in rings),
 - $r\sum_i v_i = \sum_i rv_i$ (in modules) and 
 - $\sum_i r_i(r'_iv_i) = \sum_i (r_ir'_i)v_i$ *)

Lemma RING_sum_mult_dist_l :
 forall (R : ring) (n : Nat) (r : R) (a : seq n R),
 r rX sum a =' sum (pointwise (uncurry (RING_comp (R:=R))) (const_seq n r) a)
 in _.
simple induction n.
simpl in |- *.
auto with algebra.
intros.
apply Trans with (r rX sum (hdtl a)); auto with algebra; unfold hdtl in |- *.
apply Trans with (r rX (head a +' sum (Seqtl a))); auto with algebra.
apply Trans with (r rX head a +' r rX sum (Seqtl a)); auto with algebra.
apply
 Trans
  with
    (r rX head a +'
     sum
       (pointwise (uncurry (RING_comp (R:=R))) (Seqtl (const_seq (S n0) r))
          (Seqtl a))).
apply SGROUP_comp; auto with algebra.
apply
 Trans
  with
    (sum (pointwise (uncurry (RING_comp (R:=R))) (const_seq n0 r) (Seqtl a)));
 auto with algebra.
apply sum_comp.
apply toMap.
apply pointwise_comp; auto with algebra.
apply Sym.
change (Seqtl (const_seq (S n0) r) =' const_seq (pred (S n0)) r in _) in |- *.
apply Seqtl_const_seq.
apply Sym.
apply
 Trans
  with
    (sum
       (hdtl (pointwise (uncurry (RING_comp (R:=R))) (const_seq (S n0) r) a)));
 auto with algebra.
unfold hdtl in |- *.
apply
 Trans
  with
    (head (pointwise (uncurry (RING_comp (R:=R))) (const_seq (S n0) r) a) +'
     sum
       (pointwise (uncurry (RING_comp (R:=R))) (Seqtl (const_seq (S n0) r))
          (Seqtl a))); auto with algebra.
apply
 Trans
  with
    (head (pointwise (uncurry (RING_comp (R:=R))) (const_seq (S n0) r) a) +'
     sum
       (Seqtl (pointwise (uncurry (RING_comp (R:=R))) (const_seq (S n0) r) a)));
 auto with algebra.
Qed.

Lemma MODULE_sum_mult_dist_l :
 forall (R : ring) (M : module R) (n : Nat) (r : R) (a : seq n M),
 r mX sum a =' sum (mult_by_scalars (const_seq n r) a) in _.
simple induction n.
simpl in |- *.
auto with algebra.
intros.
apply Trans with (r mX sum (hdtl a)); auto with algebra; unfold hdtl in |- *.
apply Trans with (r mX (head a +' sum (Seqtl a))); auto with algebra.
apply Trans with (r mX head a +' r mX sum (Seqtl a)); auto with algebra.
apply
 Trans
  with
    (r mX head a +'
     sum (mult_by_scalars (Seqtl (const_seq (S n0) r)) (Seqtl a))).
apply SGROUP_comp; auto with algebra.
apply Trans with (sum (mult_by_scalars (const_seq n0 r) (Seqtl a)));
 auto with algebra.
apply sum_comp.
apply toMap.
apply mult_by_scalars_comp; auto with algebra.
apply Sym.
change (Seqtl (const_seq (S n0) r) =' const_seq (pred (S n0)) r in _) in |- *.
apply Seqtl_const_seq.
apply Trans with (sum (hdtl (mult_by_scalars (const_seq (S n0) r) a)));
 auto with algebra.
unfold hdtl in |- *.
apply
 Trans
  with
    (head (mult_by_scalars (const_seq (S n0) r) a) +'
     sum (mult_by_scalars (Seqtl (const_seq (S n0) r)) (Seqtl a)));
 auto with algebra.
apply
 Trans
  with
    (head (mult_by_scalars (const_seq (S n0) r) a) +'
     sum (Seqtl (mult_by_scalars (const_seq (S n0) r) a))); 
 auto with algebra.
Qed.

Hint Resolve RING_sum_mult_dist_l MODULE_sum_mult_dist_l: algebra.


Lemma pointwise_module_assoc :
 forall (R : ring) (M : module R) (n : Nat) (r r' : seq n R) (m : seq n M),
 let rmult := uncurry (RING_comp (R:=R)) in
 mult_by_scalars r (mult_by_scalars r' m) ='
 mult_by_scalars (pointwise rmult r r') m in _.
intros.
intro i; simpl in |- *.
auto with algebra.
Qed.

Hint Resolve pointwise_module_assoc: algebra.