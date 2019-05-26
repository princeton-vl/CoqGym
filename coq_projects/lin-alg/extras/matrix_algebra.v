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


(** %\subsection*{ extras :  matrix\_algebra.v }%*)
(** - This is not used, but nice anyway: $n\times n$-matrices over $F$ form
 an algebra (over $F$) *)

Set Nested Proofs Allowed.
Require Export Matrices. 
From Algebra Require Export Algebra.

Require Export vecspace_Mmn.
From Algebra Require Export Cfield_facts.
Variable F : cfield.
Definition Mmn_alg (n : nat) : algebra F.
intros.
apply Build_algebra with (Mmn F n n).
apply Build_algebra_on.
simpl in |- *.
Require Export Matrix_multiplication.

Let mult_arr :
  forall n : nat, Mmn F n n -> sgroup_hom (Mmn F n n) (Mmn F n n).
intros.
apply Build_sgroup_hom with (Ap2_Map (matXmat F n n n) X).
red in |- *.
intros.
simpl in |- *.
intros.
apply
 Trans
  with
    (sum
       (pointwise (uncurry (RING_comp (R:=F))) (row X i) (col x j +' col y j)));
 auto with algebra.
apply
 Trans
  with
    (sum (pointwise (uncurry (RING_comp (R:=F))) (row X i) (col x j)) +'
     sum (pointwise (uncurry (RING_comp (R:=F))) (row X i) (col y j))).
Require Export random_facts.
apply
 Trans
  with
    (sum
       (pointwise (sgroup_law_map F)
          (pointwise (uncurry (RING_comp (R:=F))) (row X i) (col x j))
          (pointwise (uncurry (RING_comp (R:=F))) (row X i) (col y j)))).
2: apply
    (sum_of_sums (n:=n) (M:=F)
       (pointwise (uncurry (RING_comp (R:=F))) (row X i) (col x j))
       (pointwise (uncurry (RING_comp (R:=F))) (row X i) (col y j)));
    auto with algebra.
apply sum_comp; auto with algebra.
simpl in |- *.
red in |- *.
intros.
simpl in |- *.
apply Trans with (X i x0 rX x x0 j +' X i x0 rX y x0 j); auto with algebra.
generalize row_comp; intro Hr; simpl in Hr.
generalize col_comp; intro Hc; simpl in Hc.
apply SGROUP_comp.
apply sum_comp.
simpl in |- *.
red in |- *.
simpl in |- *.
destruct x; destruct X.
intro.
simpl in |- *.
apply RING_comp.
red in Ap2_comp_proof0.
auto with algebra.
red in Ap2_comp_proof.
auto with algebra.
apply sum_comp.
simpl in |- *.
red in |- *.
simpl in |- *.
destruct y; destruct X.
intro.
simpl in |- *.
apply RING_comp.
red in Ap2_comp_proof0.
auto with algebra.
red in Ap2_comp_proof.
auto with algebra.
Defined.

Let mult_arr_mon :
  forall n : nat, Mmn F n n -> monoid_hom (Mmn F n n) (Mmn F n n).
intros.
apply Build_monoid_hom with (mult_arr n X).
red in |- *.
simpl in |- *.
intros.
apply Trans with (sum (const_seq n (zero F))); auto with algebra.
apply sum_comp.
simpl in |- *.
red in |- *.
simpl in |- *.
auto with algebra.
Defined.

Let mult_arr_mod :
  forall n : nat, Mmn F n n -> module_hom (Mmn F n n) (Mmn F n n).
intros.
apply Build_module_hom with (mult_arr_mon n X).
red in |- *.
intros.
simpl in |- *.
intros.
apply
 Trans
  with
    (a rX sum (pointwise (uncurry (RING_comp (R:=F))) (row X i) (col x j))).
2: apply RING_comp; auto with algebra.
2: apply sum_comp.
2: simpl in |- *.
2: red in |- *.
2: simpl in |- *.
2: intro.
2: apply RING_comp; auto with algebra.
2: destruct X.
2: simpl in |- *.
2: red in Ap2_comp_proof.
2: auto with algebra.
2: destruct x.
2: simpl in |- *.
2: red in Ap2_comp_proof.
2: auto with algebra.
apply
 Trans
  with
    (sum
       (pointwise (uncurry (RING_comp (R:=F))) (const_seq n a)
          (pointwise (uncurry (RING_comp (R:=F))) (row X i) (col x j)))).
apply sum_comp.
simpl in |- *.
red in |- *.
intro.
simpl in |- *.
auto with algebra.
apply Sym.
Require Export distribution_lemmas.
apply RING_sum_mult_dist_l.
Defined.

Let mult_map_mod :
  forall n : nat, Map (Mmn F n n) (Hom_module (Mmn F n n) (Mmn F n n)).
intros.
apply Build_Map with (mult_arr_mod n).
red in |- *.
intros; simpl in |- *.
simpl in H.
red in |- *; simpl in |- *.
intros.
apply sum_comp.
simpl in |- *.
red in |- *.
intro.
simpl in |- *.
destruct x0.
simpl in |- *.
red in Ap2_comp_proof.
apply RING_comp; auto with algebra.
Defined.

Let mult_sgp_mod :
  forall n : nat, sgroup_hom (Mmn F n n) (Hom_module (Mmn F n n) (Mmn F n n)).
intros.
apply Build_sgroup_hom with (mult_map_mod n).
red in |- *.
intros; simpl in |- *.
red in |- *; intros.
simpl in |- *.
intros.
apply
 Trans
  with
    (sum
       (pointwise (uncurry (RING_comp (R:=F))) (row (x +' y) i') (col x0 j')));
 auto with algebra.
apply sum_comp.
simpl in |- *.
red in |- *.
simpl in |- *.
intro.
destruct x; destruct y; destruct x0; simpl in |- *.
red in Ap2_comp_proof, Ap2_comp_proof0, Ap2_comp_proof1.
apply RING_comp; auto with algebra.
apply
 Trans
  with
    (sum
       (pointwise (sgroup_law_map F)
          (pointwise (uncurry (RING_comp (R:=F))) (row x i') (col x0 j'))
          (pointwise (uncurry (RING_comp (R:=F))) (row y i') (col x0 j')))).
apply sum_comp.
simpl in |- *.
red in |- *.
simpl in |- *.
intro.
apply Trans with (x i' x1 rX x0 x1 j' +' y i' x1 rX x0 x1 j');
 auto with algebra.
generalize sum_of_sums.
intros.
apply
 (H1 n F (pointwise (uncurry (RING_comp (R:=F))) (row x i') (col x0 j'))
    (pointwise (uncurry (RING_comp (R:=F))) (row y i') (col x0 j'))).
Defined.

Let mult_mon_mod :
  forall n : nat, monoid_hom (Mmn F n n) (Hom_module (Mmn F n n) (Mmn F n n)).
intros.
apply Build_monoid_hom with (mult_sgp_mod n).
red in |- *.
simpl in |- *.
red in |- *.
intro.
simpl in |- *.
intros.
apply Trans with (sum (const_seq n (zero F))).
apply sum_comp.
simpl in |- *.
red in |- *.
simpl in |- *.
auto with algebra.
apply sum_of_zeros; auto with algebra.
Defined.

apply Build_module_hom with (mult_mon_mod n).
red in |- *.
intros; simpl in |- *.
red in |- *.
intro; simpl in |- *.
intros.
apply
 Trans
  with
    (sum
       (pointwise (uncurry (RING_comp (R:=F))) (const_seq n a)
          (pointwise (uncurry (RING_comp (R:=F))) (row x i') (col x0 j')))).
apply sum_comp.
simpl in |- *.
red in |- *.
simpl in |- *.
intro.
apply Trans with ((a rX x i' x1) rX x0 x1 j'); auto with algebra.
apply RING_comp; auto with algebra.
apply RING_comp; auto with algebra.
destruct x; red in Ap2_comp_proof; simpl in |- *; auto with algebra.
destruct x0; red in Ap2_comp_proof; simpl in |- *; auto with algebra.
apply Sym.
auto with algebra.
Defined.

(* <Warning> : Grammar is replaced by Notation *)
(* <Warning> : Syntax is discontinued *)
