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


(** * direct_sum.v *)
Local Unset Standard Proposition Elimination Names.

Set Implicit Arguments.
Unset Strict Implicit.
Require Export algebraic_span_facts.

Section MAIN.
Variable F : field.
Variable V : vectorspace F.
(** - A vectorspace being a direct sum is only defined as a predicate; the sum_set
 however is defined as a construction:
%\tocdef{sum\_set}% *)
Definition sum_set (S1 S2 : part_set V) : part_set V.
intros.
simpl in |- *.
apply
 Build_Predicate
  with
    (fun x : V =>
     exists s1 : S1,
       (exists s2 : S2, x =' subtype_elt s1 +' subtype_elt s2 in _)).
red in |- *.
intros.
inversion_clear H.
inversion_clear H1.
exists x0.
exists x1.
apply Trans with x; auto with algebra.
Defined.

Lemma subspace_sum_set :
 forall W1 W2 : part_set V,
 is_subspace W1 -> is_subspace W2 -> is_subspace (sum_set W1 W2).
unfold is_subspace in |- *; intuition.
simpl in |- *.
red in H1, H.
exists (Build_subtype H1).
exists (Build_subtype H).
simpl in |- *.
auto with algebra.

simpl in H3, H6.
inversion_clear H3; inversion_clear H6.
inversion_clear H7; inversion_clear H3.
destruct x0; destruct x1; destruct x2; destruct x3.
generalize (H0 _ _ subtype_prf subtype_prf0).
generalize (H2 _ _ subtype_prf1 subtype_prf2).
intros.
red in H3, H8.
exists (Build_subtype H8).
exists (Build_subtype H3).
simpl in |- *.
simpl in H6, H7.
apply
 Trans with (subtype_elt +' subtype_elt1 +' (subtype_elt0 +' subtype_elt2));
 auto with algebra.

simpl in H3.
inversion_clear H3.
inversion_clear H6.
destruct x0; destruct x1.
generalize (H4 c _ subtype_prf).
generalize (H5 c _ subtype_prf0).
intros.
simpl in H3; simpl in |- *.
red in H6, H7.
exists (Build_subtype H7).
exists (Build_subtype H6).
simpl in |- *.
apply Trans with (c mX (subtype_elt +' subtype_elt0)); auto with algebra.
Qed.

(** %\tocdef{form\_direct\_sum}% *)
Definition form_direct_sum (W1 W2 : subspace V) : Prop :=
  inter W1 W2 =' single (zero V) in _ /\ sum_set W1 W2 =' full V in _.
End MAIN.

Section Example.
Require Import symmetric_matrices.
Require Import antisymmetric_matrices.

(** - Example 26 on page 20 is actually WRONG, or at least incomplete: if the field is
 $\mathbf Z/2\mathbf Z = \{0,1\}$, where $-1=1$, then symmetric and antisymmetric
 matrices coincide, and $M_{nn}$ cannot be split in just the symmetric and
 antisymmetric part. Hence the extra condition that $1+1\neq0$: *)
Lemma matrixspace_sym_antisym :
 forall (n : nat) (F : field),
 ~ one +' one =' (zero F) in _ ->
 form_direct_sum (symm_subspace n F) (antisym_subspace n F).
split.
intro.
split.
simpl in |- *; intuition.
clear H3 H0 j' i'.
cut (x i j =' x j i in _).
intro.
cut (x i j =' (min x j i) in _).
intro.
assert (x i j +' x i j =' x j i +' (min x j i) in _); auto with algebra.
assert (x i j +' x i j =' (zero F) in _).
apply Trans with (x j i +' (min x j i)); auto with algebra.
assert (one rX x i j +' one rX x i j =' (zero F) in _).
apply Trans with (x i j +' x i j); auto with algebra.
assert ((one +' one) rX x i j =' (one +' one) rX (zero F) in _).
apply Trans with (one rX x i j +' one rX x i j); auto with algebra.
apply Trans with (zero F); auto with algebra.
apply FIELD_reg_left with ((one:F) +' (one:F)); auto with algebra.

unfold antisym_subspace in H2.
unfold alt_Build_subspace in H2.
generalize dependent H2.
case (subspace_construction (antisymm_matr_subspace n F)).
intros.
simpl in e.
red in e.
elim (e x); intros.
generalize dependent (H3 H2); intro p; simpl in p.
red in p.
auto.

unfold symm_subspace in H1.
unfold alt_Build_subspace in H1.
generalize dependent H1.
case (subspace_construction (symm_matr_subspace n F)).
intros.
simpl in e.
red in e.
elim (e x); intros.
generalize dependent (H0 H1); intro p; simpl in p.
red in p.
auto.

intro p; simpl in p.
simpl in |- *.
split.
unfold symm_subspace in |- *.
unfold alt_Build_subspace in |- *.
case (subspace_construction (symm_matr_subspace n F)).
intros.
simpl in e; red in e.
elim (e x); intros.
apply H1.
simpl in |- *.
red in |- *.
assert (forall i j : fin n, x i j =' (zero F) in _).
intros; apply p with i j; auto with algebra.

intros; apply Trans with (zero F); auto with algebra.

unfold antisym_subspace in |- *.
unfold alt_Build_subspace in |- *.
case (subspace_construction (antisymm_matr_subspace n F)).
intros.
simpl in e; red in e.
elim (e x); intros.
apply H1.
simpl in |- *.
red in |- *.
assert (forall i j : fin n, x i j =' (zero F) in _).
intros; apply p with i j; auto with algebra.

intros; apply Trans with (zero F); auto with algebra.
apply Trans with (min (zero F)); auto with algebra.

split; intros.
simpl in |- *.
auto.

clear H0.
simpl in |- *.
set (x_s := field_inverse ((one:F) +' (one:F)) mX (x +' transpose x)) in *.
assert (in_part x_s (symm_subspace n F)).
unfold symm_subspace in |- *.
unfold alt_Build_subspace in |- *.
case (subspace_construction (symm_matr_subspace n F)).
intros.
simpl in e; red in e.
elim (e x_s); intros.
apply H1.
simpl in |- *.
red in |- *.
unfold x_s in |- *.
intros.
apply
 Trans
  with
    (field_inverse (K:=F) (ring_unit F +' ring_unit F)
     rX (x +' transpose x) i j); auto with algebra.
apply
 Trans
  with
    (field_inverse (K:=F) (ring_unit F +' ring_unit F)
     rX (x +' transpose x) j i); auto with algebra.
apply RING_comp; auto with algebra.
unfold transpose in |- *; simpl in |- *.
case x.
simpl in |- *.
auto with algebra.

set
 (x_a :=
  field_inverse ((one:F) +' (one:F)) mX (x +' (min (transpose x:Mmn F n n))))
 in *.
assert (in_part x_a (antisym_subspace n F)).
unfold antisym_subspace in |- *.
unfold alt_Build_subspace in |- *.
case (subspace_construction (antisymm_matr_subspace n F)).
intros.
simpl in e; red in e.
elim (e x_a); intros.
apply H2.
simpl in |- *.
red in |- *.
unfold x_a in |- *.
intros.
apply
 Trans
  with
    (field_inverse (K:=F) (ring_unit F +' ring_unit F)
     rX (x +' (min (transpose x:Mmn F n n))) i j); 
 auto with algebra.
apply
 Trans
  with
    (min field_inverse (K:=F) (ring_unit F +' ring_unit F)
         rX (x +' (min (transpose x:Mmn F n n))) j i); 
 auto with algebra.
apply
 Trans
  with
    (field_inverse (K:=F) (ring_unit F +' ring_unit F)
     rX (min (x +' (min (transpose x:Mmn F n n))) j i)); 
 auto with algebra.
apply RING_comp; auto with algebra.
unfold transpose in |- *; simpl in |- *.
case x.
simpl in |- *.
intros.
apply Trans with ((min Ap2 j i) +' (min (min Ap2 i j))).
apply Trans with ((min (min Ap2 i j)) +' (min Ap2 j i)); auto with algebra.
apply Sym.
apply Trans with ((min (min Ap2 i j)) +' (min Ap2 j i)); auto with algebra.

red in H0, H1.
exists (Build_subtype H0).
exists (Build_subtype H1).
simpl in |- *.
intros.
set (half := field_inverse ((one:F) +' one)) in *.
apply
 Trans
  with
    (half rX x i' j' +' half rX transpose x i' j' +'
     (half rX x i' j' +' half rX (min transpose x i' j'))); 
 auto with algebra.
apply
 Trans
  with
    (half rX x i' j' +' half rX x i' j' +'
     (half rX transpose x i' j' +' half rX (min transpose x i' j')));
 auto with algebra.
apply Trans with (half rX x i' j' +' half rX x i' j' +' (zero F)).
apply Trans with (half rX x i' j' +' half rX x i' j'); auto with algebra.
apply Trans with (half rX x i j +' half rX x i j); auto with algebra.
apply Trans with (one rX x i j); auto with algebra.
apply Trans with (((one +' one) rX half) rX x i j); auto with algebra.
apply RING_comp; auto with algebra.
apply Sym; unfold half in |- *; auto with algebra.
apply Trans with ((one +' one) rX half rX x i j); auto with algebra.
apply Trans with (one rX half rX x i j +' one rX half rX x i j);
 auto with algebra.
assert (x i j =' x i' j' in _).
generalize dependent (Ap2_comp_proof x); intro p; red in p; auto with algebra.
auto with algebra.
apply SGROUP_comp; auto with algebra.
apply
 Trans with (half rX transpose x i' j' +' (min half rX transpose x i' j'));
 auto with algebra.
Qed.
End Example.