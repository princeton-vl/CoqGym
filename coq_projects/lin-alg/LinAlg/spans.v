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


(** * spans.v *)
Set Implicit Arguments.
Unset Strict Implicit.
(** - Spans can be defined in two ways: (1) the span of a subset $S\subset V$ is
 the subspace of all linear combinations of $S$ or (2) it is the set defined
 inductively by
  -- $0\in span(S)$
  -- $v\in S\to v\in span(S)$
  -- $v,v'\in S\to v+v'\in span(S)$
  -- $v\in S, c\in F\to cv\in span(S)$

 These definitions are proved equivalent. Notice how we must first define the formal
 expressions for these vectors and then inject them into the final set.

 Also $span(S)$ is the smallest subspace containing $S$ and some other easy lemmas *)

Require Export lin_combinations.
Require Export subspaces.

Section spans.
Variable F : field.
Variable V : vectorspace F.
Definition span_set (S : part_set V) : part_set V := is_lin_comb_pred S.

(** %\tocdef{span}% *)
Definition span : part_set V -> subspace V.
intro S.
apply alt_Build_subspace with (span_set S).
red in |- *; split; try split.
simpl in |- *.
red in |- *.
exists 0.
exists (empty_seq F).
exists (empty_seq S).
simpl in |- *.
auto with algebra.
intros; simpl in H, H0; simpl in |- *; red in H, H0; red in |- *.
inversion_clear H; inversion_clear H0; inversion_clear H; inversion_clear H1;
 inversion_clear H0; inversion_clear H.
exists (x0 + x1).
exists (x3 ++ x2).
exists (x5 ++ x4).
apply
 Trans
  with
    (sum (mult_by_scalars x3 (Map_embed x5)) +'
     sum (mult_by_scalars x2 (Map_embed x4))); auto with algebra.
apply
 Trans
  with
    (sum
       (mult_by_scalars x3 (Map_embed x5) ++
        mult_by_scalars x2 (Map_embed x4))); auto with algebra.
apply
 Trans with (sum (mult_by_scalars (x3 ++ x2) (Map_embed x5 ++ Map_embed x4)));
 auto with algebra.
intros.
red in |- *; red in H.
simpl in |- *; simpl in H.
red in |- *; red in H.
inversion_clear H; inversion_clear H0; inversion_clear H.
exists x0;
 exists (pointwise (uncurry (RING_comp (R:=F))) (const_seq x0 c) x1);
 exists x2.
apply
 Trans
  with
    (sum
       (mult_by_scalars (const_seq x0 c) (mult_by_scalars x1 (Map_embed x2))));
 auto with algebra.
apply Trans with (c mX sum (mult_by_scalars x1 (Map_embed x2)));
 auto with algebra.
Defined.

Lemma span_comp :
 forall S S' : part_set V, S =' S' in _ -> span S =' span S' in part_set V.
intros.
simpl in |- *.
red in |- *.
simpl in |- *.
intro.
split.
intro.
apply is_lin_comb_comp with x S; auto with algebra.
intro.
apply is_lin_comb_comp with x S'; auto with algebra.
Qed.

(** - %\intoc{\bf Theorem 1.5}% *)
Lemma span_is_subspace : forall S : part_set V, is_subspace (span S).
intro; apply is_subspace_OK.
Qed.
End spans.

Hint Resolve span_comp: algebra.

Section spans_inductively_defined.
Variable F : field.
Variable V : vectorspace F.
Variable S : part_set V.
(** - The type of formal expressions *)
Inductive span_ind_formal : Type :=
  | Zerovector : span_ind_formal
  | Immediately : S -> span_ind_formal
  | Plusvector : span_ind_formal -> span_ind_formal -> span_ind_formal
  | Multvector : F -> span_ind_formal -> span_ind_formal.

(** - The injection into the `inductively defined' span *)
Fixpoint span_ind_injection (X : span_ind_formal) : V :=
  match X with
  | Zerovector => zero V
  | Immediately s => subtype_elt s
  | Plusvector x y => span_ind_injection x +' span_ind_injection y
  | Multvector a x => a mX span_ind_injection x
  end.

Definition span_ind_set : part_set V.
simpl in |- *.
apply
 (Build_Predicate
    (Pred_fun:=fun v : V =>
               exists X : span_ind_formal, v =' span_ind_injection X in _)).
red in |- *.
intros.
inversion H.
exists x0.
apply Trans with x; auto with algebra.
Defined.

(** %\tocdef{span\_ind}% *)
Definition span_ind : subspace V.
apply alt_Build_subspace with span_ind_set; auto with algebra.
red in |- *.
split; try split; simpl in |- *.
exists Zerovector.
simpl in |- *.
auto with algebra.
intros.
inversion_clear H; inversion_clear H0.
exists (Plusvector x0 x1).
simpl in |- *.
auto with algebra.
intros.
inversion_clear H.
exists (Multvector c x0).
simpl in |- *.
auto with algebra.
Defined.

Definition lin_comb_ind (v : V) : Prop := in_part v span_ind.
End spans_inductively_defined.

Section spans_eqv.

Variable F : field.
Variable V : vectorspace F.

Lemma span_ind_eqv_span :
 forall (S : part_set V) (v : V), is_lin_comb v S <-> lin_comb_ind S v.
intros.
split.
intro.
inversion_clear H.
generalize H0; clear H0.
generalize v.
induction  x as [| x Hrecx].
intros v0 H0.
inversion_clear H0.
inversion_clear H.
simpl in H0.
unfold lin_comb_ind in |- *.
simpl in |- *.
exists (Zerovector S).
simpl in |- *.
assumption.
(* Induction step *)
intros.
inversion_clear H0.
inversion_clear H.
unfold lin_comb_ind in |- *.
simpl in |- *.
(********)
set (x0_0 := head x0) in *.
set (x1_0 := head x1) in *. 
set (vhd := x0_0 mX S x1_0) in *.
set (vtl := mult_by_scalars (Seqtl x0) (Map_embed (Seqtl x1)):seq x V) in *. 
cut (v0 =' vhd +' sum vtl in _).
intro.
generalize (Hrecx (sum vtl)).
intro.
cut
 (exists a : seq x F,
    (exists w : seq x S,
       sum vtl =' sum (mult_by_scalars a (Map_embed w)) in _)).
intro.
generalize (H1 H2).
intro.
unfold lin_comb_ind in H3.
simpl in H3.
inversion H3.
exists (Plusvector (Multvector x0_0 (Immediately x1_0)) x2).
simpl in |- *.
apply Trans with (x0_0 mX S x1_0 +' sum vtl); auto with algebra.
(* that was the real work *)
exists (Seqtl x0).
exists (Seqtl x1).
unfold vtl in |- *.
apply sum_comp; auto with algebra.
(**)
unfold vhd, vtl, x0_0, x1_0 in |- *.
apply Trans with (sum (mult_by_scalars x0 (Map_embed x1))); auto with algebra.
apply Trans with (sum (mult_by_scalars (hdtl x0) (Map_embed (hdtl x1)))).
unfold mult_by_scalars in |- *.
apply sum_comp.
apply toMap.
apply pointwise_comp; auto with algebra.
unfold hdtl in |- *.
unfold mult_by_scalars in |- *.
apply
 Trans
  with
    (sum
       (uncurry (MODULE_comp (R:=F) (Mod:=V))
          (couple (head x0) (S (head x1)));;
        pointwise (uncurry (MODULE_comp (R:=F) (Mod:=V))) 
          (Seqtl x0) (Map_embed (Seqtl x1)))); auto with algebra.
intros.
inversion_clear H.
generalize H0; clear H0.
generalize v; clear v.
elim x.
intros.
unfold is_lin_comb in |- *.
exists 0.
exists (const_seq 0 (zero F)).
simpl in |- *.
exists (empty_seq S).
assumption.
intros.
unfold is_lin_comb in |- *.
exists 1.
exists (const_seq 1 (one:F)).
exists (const_seq 1 c).
simpl in |- *.
apply Trans with (subtype_elt c); auto with algebra.
apply Trans with (one mX subtype_elt c); auto with algebra.
unfold is_lin_comb in |- *.
intros.
generalize (H _ (Refl (span_ind_injection s))).
generalize (H0 _ (Refl (span_ind_injection s0))).
clear H H0.
intros.
inversion_clear H0.
inversion_clear H2.
inversion_clear H0.
inversion_clear H.
inversion_clear H0.
inversion_clear H.
exists (x0 + x3).
exists (x1 ++ x4).
exists (x2 ++ x5).
apply Trans with (span_ind_injection s +' span_ind_injection s0);
 auto with algebra.
apply
 Trans
  with (sum (mult_by_scalars x1 (Map_embed x2)) +' span_ind_injection s0);
 auto with algebra.
apply
 Trans
  with
    (sum (mult_by_scalars x1 (Map_embed x2)) +'
     sum (mult_by_scalars x4 (Map_embed x5))); auto with algebra.
apply
 Trans
  with
    (sum
       (mult_by_scalars x1 (Map_embed x2) ++
        mult_by_scalars x4 (Map_embed x5))); auto with algebra.
unfold mult_by_scalars in |- *.
apply sum_comp; auto with algebra.
apply
 Trans
  with
    (pointwise (uncurry (MODULE_comp (R:=F) (Mod:=V))) 
       (x1 ++ x4) (Map_embed x2 ++ Map_embed x5)); 
 auto with algebra.

intros.
generalize (H _ (Refl (span_ind_injection s))).
unfold is_lin_comb in |- *.
intro.
inversion_clear H1.
inversion_clear H2.
inversion_clear H1.
exists x0.
exists (pointwise (uncurry (RING_comp (R:=F))) (const_seq x0 c) x1).
exists x2.
simpl in H0.
apply Trans with (c mX span_ind_injection s); auto with algebra.
apply Trans with (c mX sum (mult_by_scalars x1 (Map_embed x2)));
 auto with algebra.
apply
 Trans
  with
    (sum
       (mult_by_scalars (const_seq x0 c) (mult_by_scalars x1 (Map_embed x2))));
 auto with algebra.
Qed.

Lemma span_is_span_ind :
 forall S : part_set V, span S =' span_ind S in part_set V.
intro.
simpl in |- *.
red in |- *.
simpl in |- *.
intro.
generalize (span_ind_eqv_span S x).
intro.
unfold lin_comb_ind in H.
simpl in H.
unfold iff in H.
auto.
Qed.

Lemma span_ind_comp :
 forall S S' : part_set V,
 S =' S' in _ -> span_ind S =' span_ind S' in part_set V.
intros.
apply Trans with (span S:part_set V); auto with algebra.
apply Sym; (apply span_is_span_ind; auto with algebra).
apply Trans with (span S':part_set V); auto with algebra.
apply span_is_span_ind; auto with algebra.
Qed.

End spans_eqv.

Hint Resolve span_is_span_ind span_ind_comp: algebra.

Section a_nice_fact_on_spans.
(** - %\intoc{Theorem 1.5 (cont'd)}% *)
Lemma span_smallest_subspace_containing_subset :
 forall (F : field) (V : vectorspace F) (W : subspace V) (S : part_set V),
 included S W -> included (span S) W.
intros.
red in |- *.
simpl in |- *.
red in H.
intros.
generalize (span_ind_eqv_span S x).
unfold iff in |- *.
intros (LC1, LC2).
generalize (LC1 H0).
intro.
inversion H1.
generalize H2; clear H2.
cut (is_subspace W).
unfold is_subspace in |- *.
intros (W1, (W2, W3)).
2: apply is_subspace_OK; auto with algebra.
clear H0 H1 LC1 LC2.
generalize x.
clear x.
elim x0.
simpl in |- *.
intros.
apply in_part_comp_l with (zero V); auto with algebra.
simpl in |- *.
intros.
apply in_part_comp_l with (subtype_elt c); auto with algebra.
intros.
simpl in H2.
apply in_part_comp_l with (span_ind_injection s +' span_ind_injection s0);
 auto with algebra.
intros.
simpl in H2.
apply in_part_comp_l with (c mX span_ind_injection s); auto with algebra.
Qed.

(* and of course the obvious *)
Lemma set_included_in_its_span :
 forall (F : field) (V : vectorspace F) (S : part_set V), included S (span S).
intros.
red in |- *.
intros.
apply in_part_comp_r with (span_ind S:part_set V); auto with algebra.
simpl in |- *.
exists (Immediately (Build_subtype H)).
simpl in |- *.
apply Refl.
Qed.

End a_nice_fact_on_spans.

Hint Resolve set_included_in_its_span: algebra.


(** %\tocdef{generates}% *)
Definition generates (F : field) (V : vectorspace F) 
  (S W : part_set V) := span S =' W in part_set V.

Lemma generates_comp :
 forall (F : field) (V : vectorspace F) (S S' W W' : part_set V),
 S =' S' in _ -> W =' W' in _ -> generates S W -> generates S' W'.
intros.
red in |- *; red in H1.
apply Trans with (span S:part_set V); auto with algebra.
apply Trans with (W:part_set V); auto with algebra.
Qed.

Lemma generated_subsets_are_subspaces :
 forall (F : field) (V : vectorspace F) (S W : part_set V),
 generates S W -> is_subspace W.
intros.
red in H.
apply is_subspace_comp with (span S:part_set V); auto.
apply is_subspace_OK.
Qed.

Lemma is_lin_comb_from_generates :
 forall (F : field) (V : vectorspace F) (S W : part_set V),
 generates S W -> forall x : V, in_part x W -> is_lin_comb x S.
intros.
red in H.
simpl in H.
red in H.
generalize (H x); intro.
inversion_clear H1.
simpl in H3.
auto.
Qed.

Lemma generates_then_is_lin_comb :
 forall (F : field) (V : vectorspace F) (S W : part_set V),
 generates S W -> forall x : V, in_part x W -> is_lin_comb x S.
exact is_lin_comb_from_generates.
Qed.

Lemma is_lin_comb_from_generates' :
 forall (F : field) (V : vectorspace F) (S : part_set V) (W : subspace V),
 generates S W -> forall x : W, is_lin_comb (subtype_elt x) S.
intros.
apply is_lin_comb_from_generates with (W:part_set V); auto with algebra.
Qed.