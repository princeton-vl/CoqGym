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


(** * bases.v *)
Set Implicit Arguments.
Unset Strict Implicit.
Require Export lin_dependence.
Require Export spans.
Require Export random_facts.

Section MAIN.
Variable F : field.
Variable V : vectorspace F.

Section Defs.
(** %\tocdef{is\_basis}% *)
Definition is_basis (X : part_set V) : Prop :=
  generates X (full V) /\ lin_indep X.

Lemma is_basis_comp :
 forall X Y : part_set V, X =' Y in _ -> is_basis X -> is_basis Y.
intros.
red in |- *; red in H0.
inversion_clear H0; split.
apply generates_comp with X (full V); auto with algebra.
apply lin_indep_comp with X; auto with algebra.
Qed.

(** %\tocdef{basis}% *)
Record basis : Type := 
  {basis_carrier :> Predicate V; is_basis_prf : is_basis basis_carrier}.
End Defs.

Lemma basis_prop : forall (X : basis) (x : V), is_lin_comb x X.
intros.
red in |- *.
elim X.
clear X.
intros X H.
red in H.
inversion_clear H.
red in H0.
unfold span in H0.
unfold is_lin_comb in H0.
simpl in H0.
red in H0.
simpl in H0.
generalize (H0 x).
clear H0.
unfold is_lin_comb in |- *.
intros (H', H0).
apply H0; auto with algebra.
Qed.

Lemma basis_prop_strong :
 forall (n : Nat) (v : seq n V),
 is_basis (seq_set v) ->
 forall x : V, exists a : seq n F, sum (mult_by_scalars a v) =' x in _.
intros.
generalize (basis_prop (Build_basis H) x).
intro.
generalize (span_ind_eqv_span (seq_set v) x).
intros.
inversion_clear H1.
generalize (H2 H0).
clear H0 H2 H3; intro H'.
inversion_clear H'.
generalize H0; clear H0.
generalize x; clear x.
elim x0.
intros.
exists (const_seq n (zero F)).
simpl in H0.
apply Trans with (zero V); auto with algebra.
apply sum_of_zeros; intro; simpl in |- *; auto with algebra arith.
intro c.
simpl in c.
elim c.
simpl in |- *.
intros.
inversion_clear subtype_prf.
generalize H1; clear H1.
elim x1.
intros x2 y H1.
exists (Basisvec_Fn F y).
apply Trans with subtype_elt; auto with algebra.
apply Trans with (v (Build_finiteT y)); auto with algebra.
apply Sym.
apply projection_via_mult_by_scalars.
intros.
generalize (H0 (span_ind_injection s) (Refl (span_ind_injection s))).
generalize (H1 (span_ind_injection s0) (Refl (span_ind_injection s0))).
intros.
clear H0 H1.
inversion_clear H3.
inversion_clear H4.
exists (pointwise (sgroup_law_map F:Map _ _) x1 x2).
simpl in H2.
apply
 Trans
  with
    (sum
       (pointwise (sgroup_law_map V) (mult_by_scalars x1 v)
          (mult_by_scalars x2 v))).
apply sum_comp.
simpl in |- *.
red in |- *.
intro.
simpl in |- *.
apply Trans with ((x1 x3 +' x2 x3) mX v x3); auto with algebra.
apply Trans with (x1 x3 mX v x3 +' x2 x3 mX v x3); auto with algebra.
apply Trans with (sum (mult_by_scalars x1 v) +' sum (mult_by_scalars x2 v)).
generalize sum_of_sums.
intro.
generalize (H3 n V (mult_by_scalars x1 v) (mult_by_scalars x2 v)).
intros.
simpl in H4.
apply H4.
apply Trans with (span_ind_injection s0 +' span_ind_injection s);
 auto with algebra.
apply Trans with (span_ind_injection s +' span_ind_injection s0);
 auto with algebra.
intros.
generalize (H0 (span_ind_injection s) (Refl (span_ind_injection s))).
intro.
clear H0.
inversion_clear H2.
exists (pointwise (uncurry (RING_comp (R:=F))) (const_seq n c) x1).
apply
 Trans with (sum (mult_by_scalars (const_seq n c) (mult_by_scalars x1 v))).
apply sum_comp.
simpl in |- *.
red in |- *.
intro.
simpl in |- *.
auto with algebra.
apply Trans with (c mX sum (mult_by_scalars x1 v)); auto with algebra.
simpl in H1.
apply Trans with (c mX span_ind_injection s); auto with algebra.
Qed.

Section Nice_basis_properties.

Variable x : V.
Variable n : Nat.
Variable b : seq n V.
Variable Db : distinct b.
Variable Bb : is_basis (seq_set b).

Let difference_seq : forall (G : group) (a a' : seq n G), seq n G.
intros.
apply (Build_Map (Ap:=fun i : fin n => a i +' (min a' i))); auto with algebra.
red in |- *.
intros.
apply SGROUP_comp; auto with algebra.
Defined.

(** - %\intoc{\bf Theorem 1.7}% *)
Lemma basis_expansion_uniqueness :
 forall a a' : seq n F,
 sum (mult_by_scalars a b) =' x in _ ->
 sum (mult_by_scalars a' b) =' x in _ -> a =' a' in _.
intros.
cut (sum (mult_by_scalars (difference_seq a a') b) =' (zero V) in _).
intro.
cut (forall i : fin n, a i +' (min a' i) =' (zero F) in _).
intro.
cut (forall i : fin n, a i =' a' i in _).
simpl in |- *.
red in |- *.
auto.
intro.
apply min_inj; auto with algebra.
unfold is_basis in Bb.
inversion_clear Bb.
generalize (lin_indep_prop Db H3 H1).
auto.
apply Trans with (x +' (min x)); auto with algebra.
apply
 Trans with (sum (mult_by_scalars a b) +' (min sum (mult_by_scalars a' b)));
 auto with algebra.
apply
 Trans
  with (sum (mult_by_scalars a b) +' (min one) mX sum (mult_by_scalars a' b)).
apply
 Trans
  with
    (sum (mult_by_scalars a b) +'
     sum (mult_by_scalars (const_seq _ (min one)) (mult_by_scalars a' b))).
apply
 Trans
  with
    (sum
       (pointwise (sgroup_law_map V) (mult_by_scalars a b)
          (mult_by_scalars (const_seq _ (min one)) (mult_by_scalars a' b)))).
apply sum_comp.
simpl in |- *.
red in |- *.
simpl in |- *.
intro.
apply Trans with (a x0 mX b x0 +' (min one) mX a' x0 mX b x0);
 auto with algebra.
apply Trans with (a x0 mX b x0 +' ((min one) rX a' x0) mX b x0);
 auto with algebra.
apply Trans with ((a x0 +' (min one) rX a' x0) mX b x0); auto with algebra.
apply Trans with ((a x0 +' (min a' x0)) mX b x0); auto with algebra.
apply MODULE_comp; auto with algebra.
apply SGROUP_comp; auto with algebra.
apply Trans with (min one rX a' x0); auto with algebra.
apply
 (sum_of_sums (n:=n) (M:=V) (mult_by_scalars a b)
    (mult_by_scalars (const_seq n (min one)) (mult_by_scalars a' b)));
 auto with algebra.
apply SGROUP_comp; auto with algebra.
apply SGROUP_comp; auto with algebra.
apply Trans with (min one mX sum (mult_by_scalars a' b)); auto with algebra.
Qed.

End Nice_basis_properties.

(* Alas, we may not make a function, eating a vector and a basis, and returning the *)
(* associated scalars of the expansion :-( The reason being: we only know that *)
(* such a sequence EXTsists, ie we only have a noninformative proof of the fact *)
(* and we may not make an informative object (sequence) from the proof :-( :-( :'-( *)

End MAIN.