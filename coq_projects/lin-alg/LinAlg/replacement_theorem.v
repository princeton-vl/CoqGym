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


(** * replacement_theorem.v *)
Set Implicit Arguments.
Unset Strict Implicit.
Require Export has_n_elements.
Require Export bases.
Require Export lin_dep_facts.

(** - %\intoc{\bf Theorem 1.10}% in this file, nothing else *)
Lemma replacement_theorem :
 forall (F : field) (V : vectorspace F) (beta : basis V) (n : Nat),
 has_n_elements n beta ->
 forall Sset : part_set V,
 lin_indep Sset ->
 forall m : Nat,
 m <= n ->
 has_n_elements m Sset ->
 exists S1 : part_set beta,
   has_n_elements (n - m) S1 /\
   generates (union Sset (inject_subsets S1)) (full V).
(* If you thought that was bad - the original formulation of this lemma said

Lemma replacement_theorem : (F:field;V:(vectorspace F);n:Nat;beta:(basis V);
  Hbeta:(has_n_elements n beta);m:Nat;Hmn:(le m n);
  Sset:(part_set V);HSset:(lin_indep Sset);H'Sset:(has_n_elements m Sset))
  (EXT S1:(part_set beta) | (has_n_elements (minus n m) S1) /\ 
                            (generates (union Sset (inject_subsets S1)))).

Anyways - hence first some renaming to get the original script running
*)

intros.
rename H into Hbeta.
rename H0 into HSset.
rename H1 into Hmn.
rename H2 into H'Sset.
generalize dependent Sset.
generalize dependent m.
simple induction m.
intros.
simpl in n.
exists (full beta).
split.
replace (n - 0) with n; auto with arith.
apply full_preserves_has_n_elements; auto with algebra.
red in |- *.
elim (is_basis_prf beta).
intros.
red in H.
apply Trans with (span beta:part_set _); auto with algebra.
apply Trans with (span (inject_subsets (full beta)):part_set _).
apply span_comp; auto with algebra.
apply Trans with (union (empty _) (inject_subsets (full beta)));
 auto with algebra.
apply span_comp; auto with algebra.

clear m; intro m; intros.
generalize (n_element_subset_sequence H'Sset).
intro.
inversion_clear H0.
rename x into ys.
inversion_clear H1.
assert (m <= n); auto with arith.
set (Sset' := seq_set (Seqtl ys)) in *.

assert (lin_indep Sset').
apply lin_indep_include with Sset; auto with algebra.
apply included_comp with (seq_set (Seqtl ys)) (seq_set ys); auto with algebra. 
red in |- *.
simpl in |- *.
intros.
inversion_clear H3.
destruct x0.
exists (Build_finiteT (lt_n_S _ _ in_range_prf)).
assumption.

assert (has_n_elements m Sset').
apply seq_set_n_element_subset; auto with algebra.
exists (Seqtl ys).
split.
auto with algebra.
apply Seqtl_preserves_distinct with (v := ys); auto with algebra.

generalize (H H1 Sset' H3 H4).
intro.
inversion_clear H5.
rename x into XS.
inversion_clear H6.
generalize (n_element_subset_sequence H5).
intro.
inversion_clear H6.
rename x into xs.
inversion_clear H8.
assert
 (generates (union (seq_set (Seqtl ys)) (seq_set (Map_embed xs))) (full V)).
apply generates_comp with (union Sset' (inject_subsets XS)) (full V);
 auto with algebra.
apply union_comp; auto with algebra.
apply Trans with (inject_subsets (seq_set xs)); auto with algebra.
apply inject_map_embed_seq_set; auto with algebra.
assert (generates (seq_set (Seqtl ys ++ Map_embed xs)) (full V)).
apply
 generates_comp
  with (union (seq_set (Seqtl ys)) (seq_set (Map_embed xs))) (full V);
 auto with algebra.
apply Sym.
apply seq_set_concat_union.

assert
 (exists a : seq m F,
    (exists b : seq (n - m) F,
       head ys =' sum (mult_by_scalars (a ++ b) (Seqtl ys ++ Map_embed xs))
       in _)).
assert (is_lin_comb (head ys) (seq_set (Seqtl ys ++ Map_embed xs))).
apply is_lin_comb_from_generates with (full V); auto with algebra.
generalize
 (lin_comb_condensed (Refl (seq_set (Seqtl ys ++ Map_embed xs))) H11).
intro.
inversion_clear H12.
assert (sigT (fun a => sigT (fun b => x =' a ++ b in _))).
apply split_to_concat; auto with algebra.
inversion_clear X.
exists x0.
inversion_clear X0.
exists x1.
apply Trans with (sum (mult_by_scalars x (Seqtl ys ++ Map_embed xs)));
 auto with algebra.

inversion_clear H11.
rename x into As.
inversion_clear H12.
rename x into Bs.

assert (exists i : fin (n - m), ~ Bs i =' (zero F) in _).
apply NNPP.
intro.
assert (forall i : fin (n - m), Bs i =' (zero F) in _).
intro.
apply NNPP.
intro.
apply H12.
exists i; auto with algebra.
assert (head ys =' sum (mult_by_scalars As (Seqtl ys)) in _).
apply
 Trans with (sum (mult_by_scalars (As ++ Bs) (Seqtl ys ++ Map_embed xs)));
 auto with algebra.
apply
 Trans
  with
    (sum (mult_by_scalars As (Seqtl ys) ++ mult_by_scalars Bs (Map_embed xs))).
unfold mult_by_scalars in |- *.
apply sum_comp; auto with algebra.
apply
 Trans
  with (sum (mult_by_scalars As (Seqtl ys) ++ const_seq (n - m) (zero V))).
unfold mult_by_scalars in |- *.
apply sum_comp.
apply concat_comp; auto with algebra.
simpl in |- *.
red in |- *.
simpl in |- *.
intro i.
apply Trans with ((zero F) mX subtype_elt (xs i)); auto with algebra.
apply Trans with (sum (mult_by_scalars As (Seqtl ys)) +' (zero V));
 auto with algebra.
apply
 Trans
  with
    (sum (mult_by_scalars As (Seqtl ys)) +' sum (const_seq (n - m) (zero V)));
 auto with algebra.
assert (lin_indep (seq_set ys)).
apply lin_indep_comp with Sset; auto with algebra.
red in H15.
unfold lin_dep in H15.
apply H15.
exists m.
exists ((min one);; As).
exists (seq_set_seq ys).
split.
red in |- *; red in |- *; intros; red in H2; red in H2.
apply (H2 i j H16).
simpl in H17.
red in H17.
simpl in H17.
auto.
split.
intro.
simpl in H16.
red in H16.
generalize (H16 (Build_finiteT (lt_O_Sn m))).
simpl in |- *.
intro.
assert (one =' (zero F) in _).
apply min_inj.
apply Trans with (zero F); auto with algebra.
generalize H18.
elim F.
intros Fr Fd; elim Fd.
simpl in |- *.
tauto.
apply Trans with (sum (mult_by_scalars ((min one);; As) ys)).
apply sum_comp; auto with algebra.

apply Trans with (sum (mult_by_scalars ((min one);; As) (hdtl ys))).
unfold mult_by_scalars in |- *; (apply sum_comp; auto with algebra);
 (apply pointwise_comp; auto with algebra).
unfold mult_by_scalars, hdtl in |- *.
apply
 Trans
  with
    (sum
       (uncurry (MODULE_comp (R:=F) (Mod:=V)) (couple (min one) (head ys));;
        pointwise (uncurry (MODULE_comp (R:=F) (Mod:=V))) As (Seqtl ys)));
 auto with algebra.
apply
 Trans
  with
    (uncurry (MODULE_comp (R:=F) (Mod:=V)) (couple (min one) (head ys)) +'
     sum (pointwise (uncurry (MODULE_comp (R:=F) (Mod:=V))) As (Seqtl ys)));
 auto with algebra.
apply
 Trans
  with
    ((min one) mX head ys +'
     sum (pointwise (uncurry (MODULE_comp (R:=F) (Mod:=V))) As (Seqtl ys)));
 auto with algebra.
apply
 Trans
  with
    ((min one mX head ys) +'
     sum (pointwise (uncurry (MODULE_comp (R:=F) (Mod:=V))) As (Seqtl ys)));
 auto with algebra.
apply
 Trans
  with
    ((min head ys) +'
     sum (pointwise (uncurry (MODULE_comp (R:=F) (Mod:=V))) As (Seqtl ys)));
 auto with algebra.
apply
 Trans
  with
    ((min sum (mult_by_scalars As (Seqtl ys))) +'
     sum (pointwise (uncurry (MODULE_comp (R:=F) (Mod:=V))) As (Seqtl ys)));
 auto with algebra.

inversion_clear H12.
rename x into i.
generalize (rewrite_lin_comb_term (F:=F) (V:=V)).
intro.
set (asbs := As ++ Bs) in *.
set (ys'xs := Seqtl ys ++ Map_embed xs) in *.

generalize (H12 _ ((min one);; asbs) (head ys;; ys'xs)).
clear H12; intro.
destruct i.
rename index into i.
rename in_range_prf into ip.
set (i_AsBs := Build_finiteT (lt_n_S _ _ (plus_lt_compat_l _ _ m ip))) in *.
assert (~ ((min one);; asbs) i_AsBs =' (zero F) in _). 
simpl in |- *.
unfold i_AsBs in |- *.
unfold asbs in |- *.
intro.
apply H13.
apply
 Trans
  with
    ((As ++ Bs)
       (Build_finiteT
          (lt_S_n (m + i) (m + (n - m))
             (lt_n_S (m + i) (m + (n - m)) (plus_lt_compat_l i (n - m) m ip)))));
 auto with algebra.
generalize (H12 _ H14); clear H12 H14; intro.
assert
 (sum (mult_by_scalars ((min one);; asbs) (head ys;; ys'xs)) =' (zero V) in _).
apply Trans with ((min one) mX head ys +' sum (mult_by_scalars asbs ys'xs)).
apply
 Trans
  with
    (uncurry (MODULE_comp (Mod:=V)) (couple (min one) (head ys)) +'
     sum (mult_by_scalars asbs ys'xs)); auto with algebra.
apply
 Trans
  with
    (sum
       (uncurry (MODULE_comp (Mod:=V)) (couple (min one) (head ys));;
        mult_by_scalars asbs ys'xs)); auto with algebra.
unfold mult_by_scalars in |- *.
auto with algebra.
apply Trans with ((min head ys) +' head ys); auto with algebra.
apply SGROUP_comp; auto with algebra.
apply Trans with (min one mX head ys); auto with algebra.
generalize (H12 H14); clear H12 H14; intro.
set (i_Bs := Build_finiteT ip) in *.
assert (Map_embed xs i_Bs =' (head ys;; ys'xs) i_AsBs in _).
simpl in |- *.
unfold i_AsBs in |- *.
unfold ys'xs in |- *.
apply Trans with (Map_embed xs i_Bs); auto with algebra.
apply Sym; auto with algebra.
generalize concat_second_part; intro p.
unfold i_Bs in |- *.
apply p.
assert
 (Map_embed xs i_Bs ='
  field_inverse (((min one);; asbs) i_AsBs)
  mX (min sum
            (omit (mult_by_scalars ((min one);; asbs) (head ys;; ys'xs))
               i_AsBs)) in _).
apply Trans with ((head ys;; ys'xs) i_AsBs); auto with algebra.
clear H12.
set
 (asbs' :=
  pointwise (uncurry (RING_comp (R:=F)))
    (const_seq _ (field_inverse (((min one);; asbs) i_AsBs)))
    (pointwise (uncurry (RING_comp (R:=F))) (const_seq _ (min one))
       (omit ((min one);; asbs) i_AsBs))) in *.
set (ysxs' := omit (head ys;; ys'xs) i_AsBs) in *.
assert (in_part (Map_embed xs i_Bs) (span (seq_set ysxs'))).
simpl in |- *.
red in |- *.
exists (m + (n - m)).
exists asbs'.
assert (forall i : fin _, in_part (ysxs' i) (seq_set ysxs')).
intro.
unfold ysxs' in |- *.
simpl in |- *.
exists i0.
auto with algebra.
exists (cast_map_to_subset H12).
apply Trans with (sum (mult_by_scalars asbs' ysxs')).
2: unfold mult_by_scalars in |- *; apply sum_comp; apply toMap;
    (apply pointwise_comp; auto with algebra).
apply Trans with (Map_embed xs i_Bs); auto with algebra.
apply
 Trans
  with
    (field_inverse (((min one);; asbs) i_AsBs)
     mX (min sum
               (omit (mult_by_scalars ((min one);; asbs) (head ys;; ys'xs))
                  i_AsBs))); auto with algebra.
apply
 Trans
  with
    (field_inverse (((min one);; asbs) i_AsBs)
     mX (min one
             mX sum
                  (omit
                     (mult_by_scalars ((min one);; asbs) (head ys;; ys'xs))
                     i_AsBs))); auto with algebra.
apply
 Trans
  with
    (field_inverse (((min one);; asbs) i_AsBs)
     mX (min one)
        mX sum
             (omit (mult_by_scalars ((min one);; asbs) (head ys;; ys'xs))
                i_AsBs)); auto with algebra.
apply
 Trans
  with
    (field_inverse (((min one);; asbs) i_AsBs)
     mX sum
          (mult_by_scalars (const_seq _ (min one))
             (omit (mult_by_scalars ((min one);; asbs) (head ys;; ys'xs))
                i_AsBs))); auto with algebra.
apply
 Trans
  with
    (sum
       (mult_by_scalars
          (const_seq _ (field_inverse (((min one);; asbs) i_AsBs)))
          (mult_by_scalars (const_seq _ (min one))
             (omit (mult_by_scalars ((min one);; asbs) (head ys;; ys'xs))
                i_AsBs)))); auto with algebra.
apply
 Trans
  with
    (sum
       (mult_by_scalars
          (const_seq _ (field_inverse (((min one);; asbs) i_AsBs)))
          (mult_by_scalars (const_seq _ (min one))
             (mult_by_scalars (omit ((min one);; asbs) i_AsBs)
                (omit (head ys;; ys'xs) i_AsBs))))).
apply sum_comp; auto with algebra.
apply sum_comp.
unfold asbs', ysxs' in |- *.
apply
 Trans
  with
    (mult_by_scalars
       (const_seq (m + (n - m)) (field_inverse (((min one);; asbs) i_AsBs)))
       (mult_by_scalars
          (pointwise (uncurry (RING_comp (R:=F)))
             (const_seq (m + (n - m)) (min one))
             (omit ((min one);; asbs) i_AsBs))
          (omit (head ys;; ys'xs) i_AsBs))).
apply toMap.
apply mult_by_scalars_comp; auto with algebra.
apply toMap.
apply pointwise_module_assoc; auto with algebra.

assert (n - m = S (n - S m)).
transitivity (S n - S m); auto.
symmetry  in |- *; auto with arith.

cut (included (seq_set ys'xs) (span (seq_set ysxs'))).
intros.
assert (included (span (seq_set ys'xs)) (span (seq_set ysxs'))).
apply span_smallest_subspace_containing_subset; auto with algebra.
assert (included (full V) (span (seq_set ysxs'))).
apply
 included_comp
  with (span (seq_set ys'xs):part_set _) (span (seq_set ysxs'):part_set _);
 auto with algebra.

exists (seq_set (omit (cast_seq xs H16) (cast_fin i_Bs H16))).
split.
red in |- *.
exists (seq_set_seq (omit (cast_seq xs H16) (cast_fin i_Bs H16))).
split.
apply included_antisym; auto with algebra.
red in |- *.
intros.
clear H20.
elim x.
intros x' x'p.
unfold in_part in |- *.
inversion_clear x'p.
exists x0.
simpl in |- *.
red in |- *.
apply
 Trans with (subtype_elt (omit (cast_seq xs H16) (cast_fin i_Bs H16) x0));
 auto with algebra.
apply seq_set_seq_preserves_distinct; auto with algebra.
red in |- *.
apply Trans with (span (seq_set ysxs'):part_set _).
2: apply included_antisym; auto with algebra.
apply span_comp; auto with algebra.
apply
 Trans with (union (seq_set ys) (inject_subsets (seq_set (omit xs i_Bs)))).

apply Trans with (union Sset (inject_subsets (seq_set (omit xs i_Bs)))).
apply union_comp; auto with algebra.
apply inject_subsets_comp; auto with algebra.
apply seq_equal_seq_set.
apply seq_equal_omit; auto with algebra.

apply union_comp; auto with algebra.


apply Trans with (seq_set (ys ++ Map_embed (omit xs i_Bs))).
apply Sym.
apply Trans with (union (seq_set ys) (seq_set (Map_embed (omit xs i_Bs)))).
apply seq_set_concat_union.
apply union_comp; auto with algebra.
apply Sym.
apply inject_map_embed_seq_set.
unfold ysxs', ys'xs in |- *.
apply Trans with (seq_set (omit (ys ++ Map_embed xs) i_AsBs));
 auto with algebra.
apply Trans with (seq_set (ys ++ omit (Map_embed xs) i_Bs));
 auto with algebra.
change
  (eq_part (seq_set (ys ++ omit (Map_embed xs) i_Bs))
     (seq_set (omit (ys ++ Map_embed xs) i_AsBs))) 
 in |- *.
split; intros.
inversion_clear H20.
change (exists i : fin _, x =' omit (ys ++ Map_embed xs) i_AsBs i in _)
 in |- *.
assert (S m + pred (n - m) = m + (n - m)).
rewrite H16.
simpl in |- *.
auto with arith.
exists (cast_fin x0 H20).
apply Trans with ((ys ++ omit (Map_embed xs) i_Bs) x0); auto with algebra.
generalize seq_equal_equal_elements.
intro p; (apply p; auto with algebra).
generalize omit_concat_second_part'.
intro.
apply seq_equal_symm.
unfold i_AsBs, i_Bs in |- *.
generalize (H22 _ _ _ ys (Map_embed xs)); clear H22; intro.
generalize
 (H22 _ ip (lt_n_S (m + i) (m + (n - m)) (plus_lt_compat_l i (n - m) m ip)));
 clear H22; intro.
apply H22.
transitivity (m + S (pred (n - m))).
apply plus_Snm_nSm.
simpl in |- *.
apply (f_equal2 plus); auto with algebra.
symmetry  in |- *.
apply S_pred with i; auto with algebra.
destruct x0.
simpl in |- *.
auto.

lapply
 (seq_equal_seq_set (v:=omit (ys ++ Map_embed xs) i_AsBs)
    (w:=ys ++ omit (Map_embed xs) i_Bs)).
intro.
change
  (eq_part (seq_set (omit (ys ++ Map_embed xs) i_AsBs))
     (seq_set (ys ++ omit (Map_embed xs) i_Bs))) in H21.
red in H21.
generalize (H21 x); intro p; inversion_clear p; auto with algebra.
generalize omit_concat_second_part'.
intro.
unfold i_AsBs, i_Bs in |- *.
generalize (H21 _ _ _ ys (Map_embed xs)); clear H21; intro.
generalize
 (H21 _ ip (lt_n_S (m + i) (m + (n - m)) (plus_lt_compat_l i (n - m) m ip)));
 clear H21; intro.
apply H21.
transitivity (m + S (pred (n - m))).
apply plus_Snm_nSm.
simpl in |- *.
apply (f_equal2 plus); auto with algebra.
symmetry  in |- *.
apply S_pred with i; auto with algebra.



red in |- *.
intros.
simpl in H17.
elim H17; clear H17; intros x0.
elim x0; clear x0; intros.
rename H17 into H18.

rename index into ix.
case (le_or_lt m ix).

intro.
assert (exists q : Nat, ix = m + q).
exists (ix - m).
apply le_plus_minus; auto with algebra.
elim H19; clear H19; intro; intro H20.
rename x0 into ix_xs.
assert (ix_xs < n - m).
clear H18.
rewrite H20 in in_range_prf.
apply plus_lt_reg_l with m; auto with algebra.

assert (x =' Map_embed xs (Build_finiteT H19) in _).
apply Trans with (ys'xs (Build_finiteT in_range_prf)); auto with algebra.
unfold ys'xs in |- *.
generalize concat_second_part.
intro p.
generalize (p _ _ _ (Seqtl ys) (Map_embed xs)).
clear p; intro.

assert (m + ix_xs < m + (n - m)).
rewrite <- H20.
auto.

apply Trans with ((Seqtl ys ++ Map_embed xs) (Build_finiteT H22));
 auto with algebra.

case (classic ((i_Bs:fin _) =' Build_finiteT H19 in _)); intros.
apply in_part_comp_l with (Map_embed xs (Build_finiteT H19));
 auto with algebra.
apply in_part_comp_l with (Map_embed xs i_Bs); auto with algebra.

assert (m + ix_xs < m + (n - m)).
rewrite <- H20.
auto.

apply in_part_comp_r with (span_ind (seq_set ysxs'):part_set _);
 auto with algebra.
apply in_part_included with (seq_set ysxs').
2: apply included_comp with (seq_set ysxs') (span (seq_set ysxs'):part_set _);
    auto with algebra.
apply in_part_included with (seq_set (omit (Map_embed xs) i_Bs));
 auto with algebra.

generalize (omit_removes' (Map_embed xs) H22).
intro.
inversion_clear X.
apply in_part_comp_l with (Map_embed xs (Build_finiteT H19));
 auto with algebra.
simpl in |- *.
exists x0.
auto.

apply
 included_comp
  with
    (seq_set (omit (Map_embed xs) i_Bs))
    (seq_set (ys ++ omit (Map_embed xs) i_Bs)); auto with algebra.

apply seq_equal_seq_set; auto with algebra.
apply seq_equal_trans with (w := omit (ys ++ Map_embed xs) i_AsBs).
apply seq_equal_symm.
unfold i_AsBs, i_Bs in |- *.
generalize omit_concat_second_part'.
intro p.
generalize (p _ _ _ ys (Map_embed xs)).
clear p; intro p.
generalize (p _ ip); clear p; intro p.
generalize
 (p (lt_n_S (m + i) (m + (n - m)) (plus_lt_compat_l i (n - m) m ip))).
intro q; apply q.
clear p q.
simpl in |- *.
rewrite H16.
simpl in |- *.
transitivity (S m + (n - S m)); auto with arith.
apply plus_Snm_nSm.
unfold ysxs' in |- *.
unfold ys'xs in |- *.
apply Map_eq_seq_equal.
apply omit_comp; auto with algebra.

apply
 included_comp
  with
    (seq_set (omit (Map_embed xs) i_Bs))
    (union (seq_set ys) (seq_set (omit (Map_embed xs) i_Bs)));
 auto with algebra.
apply Sym; auto with algebra.
apply seq_set_concat_union; auto with algebra.

intro.
apply
 in_part_comp_r with (span_set (seq_set (ys ++ omit (Map_embed xs) i_Bs)));
 auto with algebra.

assert (x =' Seqtl ys (Build_finiteT H17) in _).
generalize concat_first_part.
intro.
apply Trans with (ys'xs (Build_finiteT in_range_prf)); auto with algebra;
 unfold ys'xs in |- *.
apply H19; auto with algebra.

assert (in_part x (seq_set (ys ++ omit (Map_embed xs) i_Bs))).
apply
 in_part_comp_r
  with (union (seq_set ys) (seq_set (omit (Map_embed xs) i_Bs)));
 auto with algebra.
simpl in |- *.
left.
exists (Build_finiteT (lt_n_S _ _ H17)).
apply Trans with (Seqtl ys (Build_finiteT H17)); auto with algebra.
apply Sym; auto with algebra.
apply seq_set_concat_union; auto with algebra.

apply
 in_part_comp_r
  with (span_ind (seq_set (ys ++ omit (Map_embed xs) i_Bs)):part_set _);
 auto with algebra.
red in H20.
exists (Immediately (Build_subtype H20)).
simpl in |- *.
auto with algebra.
apply Trans with (span (seq_set (ys ++ omit (Map_embed xs) i_Bs)):part_set _);
 auto with algebra.

apply Trans with (span_set (seq_set (omit (head ys;; ys'xs) i_AsBs)));
 auto with algebra.
generalize span_comp.
intro p; simpl in p.
change
  (eq_part (span_set (seq_set (ys ++ omit (Map_embed xs) i_Bs)))
     (span_set (seq_set (omit (head ys;; ys'xs) i_AsBs)))) 
 in |- *.
apply p.
apply seq_equal_seq_set; auto with algebra.
generalize omit_concat_second_part'.
intro.
unfold i_AsBs, i_Bs in |- *.
generalize (H19 _ _ _ ys (Map_embed xs)); clear H19; intro.
generalize
 (H19 _ ip (lt_n_S (m + i) (m + (n - m)) (plus_lt_compat_l i (n - m) m ip)));
 clear H19; intro.
apply seq_equal_symm.
apply H19.
transitivity (m + S (pred (n - m))).
apply plus_Snm_nSm.
simpl in |- *.
apply (f_equal2 plus); auto with algebra.
symmetry  in |- *.
apply S_pred with i; auto with algebra.
Qed.