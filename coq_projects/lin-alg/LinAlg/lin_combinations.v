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


(** * lin_combinations.v *)
Set Implicit Arguments.
Unset Strict Implicit.
Require Export distinct.
Require Export distribution_lemmas.
Require Export sums2.
Require Export omit_facts.
Require Export cast_between_subsets.

Section lin_dep_def.

(** %\tocdef{is\_lin\_comb}% *)
Definition is_lin_comb (F : field) (V : vectorspace F) 
  (x : V) (S : part_set V) :=
  exists n : Nat,
    (exists a : seq n F,
       (exists v : seq n S, x =' sum (mult_by_scalars a (Map_embed v)) in _)).

Lemma is_lin_comb_comp :
 forall (F : field) (V : vectorspace F) (x y : V) (S T : part_set V),
 S =' T in _ -> x =' y in _ -> is_lin_comb x S -> is_lin_comb y T.
intros.
assert (is_lin_comb x T).
red in |- *; red in H1.
inversion_clear H1.
exists x0.
inversion_clear H2.
exists x1.
inversion_clear H1.
exists (Map_to_equal_subsets H x2).
apply Trans with (sum (mult_by_scalars x1 (Map_embed x2))); auto with algebra.
red in |- *.
red in H2.
inversion H2.
inversion H3.
inversion H4.
exists x0.
exists x1.
exists x2.
apply Trans with x; auto with algebra.
Qed.

Hint Resolve is_lin_comb_comp: algebra.

(** - Being a linear combination is in fact a setoid-Predicate. *)
Definition is_lin_comb_pred :
  forall (F : field) (V : vectorspace F), part_set V -> Predicate V.
intros.
apply (Build_Predicate (Pred_fun:=fun x : V => is_lin_comb x X)).
red in |- *.
intros.
apply is_lin_comb_comp with x X; auto with algebra.
Defined.
End lin_dep_def.


Section condensing.

(** - Easy to see but not easy to prove: if $x=\sum_{i=1}^n a_ib_i$ then in fact
 $x=\sum_{i=1}^{n'} a_ib'_i$ where all $b'_i$ are distinct vectors.*)

Lemma lin_comb_with_distinct_vectors :
 forall (F : field) (V : vectorspace F) (x : V) (B : part_set V),
 is_lin_comb x B ->
 exists n : Nat,
   (exists a : seq n F,
      (exists v : seq n B,
         x =' sum (mult_by_scalars a (Map_embed v)) in _ /\ distinct v)).
intros.
red in H.
inversion_clear H.
generalize x0 H0; clear H0 x0.
intro n; induction  n as [| n Hrecn].
intros.
inversion_clear H0.
inversion_clear H.
exists 0.
exists x0.
exists x1.
split.
auto.
red in |- *.
intros.
apply False_ind; auto with algebra.
intros.
inversion_clear H0.
inversion_clear H.
assert (distinct x1 \/ ~ distinct x1).
apply classic.
case H.
intro.
exists (S n).
exists x0; exists x1; split; auto.
intro.
unfold distinct in H1.
assert
 (exists i : fin (S n),
    (exists j : fin (S n), ~ i =' j in _ /\ x1 i =' x1 j in _)).
apply NNPP.
red in |- *.
red in H1.
intros; apply H1.
intros.
red in |- *; red in H2.
intro; apply H2.
exists i; exists j; auto.
inversion_clear H2; inversion_clear H3.
inversion_clear H2.
apply Hrecn.
exists (omit (modify_seq x0 x2 (x0 x2 +' x0 x3)) x3).
exists (omit x1 x3).
apply
 Trans
  with
    (sum
       (mult_by_scalars (omit (modify_seq x0 x2 (x0 x2 +' x0 x3)) x3)
          (omit (Map_embed x1) x3))).
apply
 Trans
  with
    (sum
       (omit
          (mult_by_scalars (modify_seq x0 x2 (x0 x2 +' x0 x3)) (Map_embed x1))
          x3)); auto with algebra.
apply
 Trans
  with
    (sum (mult_by_scalars (modify_seq x0 x2 (x0 x2 +' x0 x3)) (Map_embed x1)) +'
     (min mult_by_scalars (modify_seq x0 x2 (x0 x2 +' x0 x3)) 
            (Map_embed x1) x3)); auto with algebra.
apply
 Trans
  with
    (sum (mult_by_scalars (modify_seq x0 x2 (x0 x2 +' x0 x3)) (Map_embed x1)) +'
     (min x0 x3 mX Map_embed x1 x3)).
apply
 Trans
  with
    (sum
       (modify_seq (mult_by_scalars x0 (Map_embed x1)) x2
          ((x0 x2 +' x0 x3) mX Map_embed x1 x2)) +'
     (min x0 x3 mX Map_embed x1 x3)); auto with algebra.

apply
 Trans
  with
    (sum (mult_by_scalars x0 (Map_embed x1)) +'
     (min mult_by_scalars x0 (Map_embed x1) x2) +'
     (x0 x2 +' x0 x3) mX Map_embed x1 x2 +' (min x0 x3 mX Map_embed x1 x3));
 auto with algebra.

apply
 Trans
  with
    (sum (mult_by_scalars x0 (Map_embed x1)) +'
     ((min mult_by_scalars x0 (Map_embed x1) x2) +'
      (x0 x2 +' x0 x3) mX Map_embed x1 x2 +' (min x0 x3 mX Map_embed x1 x3))).
2: apply
    Trans
     with
       (sum (mult_by_scalars x0 (Map_embed x1)) +'
        ((min mult_by_scalars x0 (Map_embed x1) x2) +'
         (x0 x2 +' x0 x3) mX Map_embed x1 x2) +'
        (min x0 x3 mX Map_embed x1 x3)); auto with algebra.

apply Trans with (sum (mult_by_scalars x0 (Map_embed x1))); auto with algebra.
apply Trans with (sum (mult_by_scalars x0 (Map_embed x1)) +' (zero V));
 auto with algebra.
apply SGROUP_comp; auto with algebra.
unfold mult_by_scalars in |- *.
simpl in |- *.
apply GROUP_reg_right with (x0 x3 mX subtype_elt (x1 x3)).
apply Trans with (x0 x3 mX subtype_elt (x1 x3)); auto with algebra.
apply
 Trans
  with
    ((min x0 x2 mX subtype_elt (x1 x2)) +'
     (x0 x2 +' x0 x3) mX subtype_elt (x1 x2) +'
     ((min x0 x3 mX subtype_elt (x1 x3)) +' x0 x3 mX subtype_elt (x1 x3)));
 auto with algebra.
apply
 Trans
  with
    ((min x0 x2 mX subtype_elt (x1 x2)) +'
     (x0 x2 +' x0 x3) mX subtype_elt (x1 x2) +' (zero V)); 
 auto with algebra.
apply
 Trans
  with
    ((min x0 x2 mX subtype_elt (x1 x2)) +'
     (x0 x2 +' x0 x3) mX subtype_elt (x1 x2)); auto with algebra.
(* mind the change x3->x2 *)
apply Trans with (x0 x3 mX subtype_elt (x1 x2)); auto with algebra.
apply
 Trans
  with
    ((min x0 x2) mX subtype_elt (x1 x2) +'
     (x0 x2 +' x0 x3) mX subtype_elt (x1 x2)); auto with algebra.
apply Trans with (((min x0 x2) +' (x0 x2 +' x0 x3)) mX subtype_elt (x1 x2));
 auto with algebra.
apply MODULE_comp; auto with algebra.
apply Trans with ((min x0 x2) +' x0 x2 +' x0 x3); auto with algebra.
apply Trans with ((zero F) +' x0 x3); auto with algebra.

apply SGROUP_comp; auto with algebra.
apply GROUP_comp; auto with algebra.
unfold mult_by_scalars in |- *.
apply Trans with (modify_seq x0 x2 (x0 x2 +' x0 x3) x3 mX Map_embed x1 x3);
 auto with algebra.
apply MODULE_comp; auto with algebra.
apply Sym.
apply modify_seq_modifies_one_elt; auto with algebra.

unfold mult_by_scalars in |- *.
apply sum_comp.
apply toMap.
apply pointwise_comp; auto with algebra.
change (omit (Map_embed x1) x3 =' Map_embed (omit x1 x3) in _) in |- *.
apply omit_Map_embed.
Qed.

(** - Similarly easy to see, not easy to prove: if $B=\{b_0...b_{n-1}\}$, then
 any linear combination $x=\sum_{i=0}^{p-1} a_i b_{k_i}$ can be written as
 $x=\sum_{i=01}^{n-1} a_ib_i$*)

Lemma lin_comb_condensed :
 forall (F : field) (V : vectorspace F) (B : part_set V) 
   (n : Nat) (b : seq n V),
 B =' seq_set b in _ ->
 forall x : V,
 is_lin_comb x B -> exists a : seq n F, x =' sum (mult_by_scalars a b) in _.
intros.
red in H0.
inversion_clear H0.
generalize x H1; clear H1 x.
induction x0.
intros.
exists (const_seq n (zero F)).
inversion_clear H1.
inversion_clear H0.
simpl in H1.
apply Trans with (zero V); auto with algebra.
apply Trans with (sum (const_seq n (zero V))); auto with algebra.
apply Sym.
apply sum_of_zeros; auto with algebra.
unfold const_seq in |- *.
apply sum_comp.
intro; simpl in |- *; auto with algebra.

intros.
inversion_clear H1.
inversion_clear H0.
assert (exists i : fin n, B (head x2) =' b i in _).
simpl in H.
red in H.
simpl in H.
generalize (H (B (head x2))); intros (p, q).
apply p; auto with algebra.
apply in_part_comp_l with (subtype_elt (head x2)); auto with algebra.
inversion_clear H0.
assert
 (x ='
  head x1 mX B (head x2) +'
  sum (mult_by_scalars (Seqtl x1) (Map_embed (Seqtl x2))) in _).
apply Trans with (sum (mult_by_scalars x1 (Map_embed x2))); auto with algebra.
apply Trans with (sum (mult_by_scalars (hdtl x1) (Map_embed (hdtl x2)))).
unfold hdtl, mult_by_scalars in |- *.
apply sum_comp.
unfold head in |- *.
apply toMap.
apply pointwise_comp; auto with algebra.
unfold hdtl in |- *.
apply
 Trans
  with
    (sum
       (uncurry (MODULE_comp (Mod:=V)) (couple (head x1) (B (head x2)));;
        mult_by_scalars (Seqtl x1) (Map_embed (Seqtl x2))));
 auto with algebra.

assert
 (exists a : seq x0 F,
    (exists v : seq x0 B,
       x +' (min head x1 mX B (head x2)) ='
       sum (mult_by_scalars a (Map_embed v)) in _)).
exists (Seqtl x1).
exists (Seqtl x2).
apply
 Trans
  with
    (head x1 mX B (head x2) +'
     sum (mult_by_scalars (Seqtl x1) (Map_embed (Seqtl x2))) +'
     (min head x1 mX B (head x2))); auto with algebra.
apply
 Trans
  with
    (sum (mult_by_scalars (Seqtl x1) (Map_embed (Seqtl x2))) +'
     head x1 mX B (head x2) +' (min head x1 mX B (head x2)));
 auto with algebra.
apply
 Trans
  with
    (sum (mult_by_scalars (Seqtl x1) (Map_embed (Seqtl x2))) +'
     (head x1 mX B (head x2) +' (min head x1 mX B (head x2))));
 auto with algebra.
apply
 Trans
  with (sum (mult_by_scalars (Seqtl x1) (Map_embed (Seqtl x2))) +' (zero V));
 auto with algebra.
generalize (IHx0 _ H3).
intro.
inversion_clear H4.
exists (modify_seq x4 x3 (x4 x3 +' head x1)).
apply
 Trans
  with
    (sum (modify_seq (mult_by_scalars x4 b) x3 ((x4 x3 +' head x1) mX b x3)));
 auto with algebra.
apply
 Trans
  with
    (sum (mult_by_scalars x4 b) +' (min mult_by_scalars x4 b x3) +'
     (x4 x3 +' head x1) mX b x3).
2: apply Sym; auto with algebra.

apply
 Trans
  with
    (x +' (min head x1 mX B (head x2)) +' (min mult_by_scalars x4 b x3) +'
     (x4 x3 +' head x1) mX b x3); auto with algebra.
unfold mult_by_scalars in |- *.
simpl in |- *.
apply
 Trans
  with
    (x +' (min head x1 mX subtype_elt (head x2)) +' (min x4 x3 mX b x3) +'
     (x4 x3 mX b x3 +' head x1 mX b x3)); auto with algebra.
apply
 Trans
  with
    (x +' (min head x1 mX subtype_elt (head x2)) +'
     ((min x4 x3 mX b x3) +' (x4 x3 mX b x3 +' head x1 mX b x3)));
 auto with algebra.
apply
 Trans
  with
    (x +' (min head x1 mX subtype_elt (head x2)) +'
     ((min x4 x3 mX b x3) +' x4 x3 mX b x3 +' head x1 mX b x3));
 auto with algebra.
apply
 Trans
  with
    (x +' (min head x1 mX subtype_elt (head x2)) +'
     ((zero V) +' head x1 mX b x3)); auto with algebra.
apply
 Trans with (x +' (min head x1 mX subtype_elt (head x2)) +' head x1 mX b x3);
 auto with algebra.
apply
 Trans
  with
    (x +' (min head x1 mX subtype_elt (head x2)) +'
     head x1 mX subtype_elt (head x2)); auto with algebra.
apply
 Trans
  with
    (x +'
     ((min head x1 mX subtype_elt (head x2)) +'
      head x1 mX subtype_elt (head x2))); auto with algebra.
apply Trans with (x +' (zero V)); auto with algebra.
Qed.




End condensing.
