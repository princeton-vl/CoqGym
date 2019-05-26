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


(** %\subsection*{ support :  arb\_intersections.v }%*)
(** - This stuff could be put in the algebra contribution as well. We 
 define indexed intersections $\bigcap_{i\in I} X_i$ whenever all 
 $X_i\subset X$, and arbitrary intersections $\bigcap_{X\in P}X$ for
 $P\subset{\cal P}(A)$.
 - Suppose we have a collection of subsets $A_i$ of a setoid $A$, 
 indexed by some index set $I$. Then we may define the 
 intersection $\bigcap_{i\in I} A_i \subset A$ as 
 $\{a\in A | \forall i\in I.a\in A_i\}$ *)

Set Implicit Arguments.
Unset Strict Implicit.
From Algebra Require Export Parts2.
Require Export Classical_Pred_Type.
Section MAIN.
Section indexed_int.

Variable A : Setoid.
Variable I : Setoid.
Variable f : MAP I (part_set A). (* Picks A_i for i\in I *)
 
(** - so, given an index set $I$ and an indexing function $f$ mapping 
 this set to the part_set (powerset) of X,  (ie. $f(i) = A_i\ (\in (part\_set A))$,) 
 then (indexed_intersection f) will be $\bigcap_{i\in I} A_i$. *)

Definition indexed_intersection : part_set A.
simpl in |- *.
apply
 (Build_Predicate (Pred_fun:=fun a : A => forall i : I, in_part a (f i))).
red in |- *.
intros.
apply in_part_comp_l with x.
apply H.
assumption.
Defined.


(* Note that as we used "Variable"s, in this section we can write *)
(* "indexed_intersection" instead of (indexed_intersection f). *)
(* The following Lemma then states that \forall i \in I: intersection \subseteq A_i *)
Lemma indexed_intersection_included_in_subsets :
 forall i : I, included indexed_intersection (f i).
intro.
red in |- *.
intros.
unfold indexed_intersection in H.
simpl in H.
apply H.
Qed.

(* if a \in indexed_intersection then a \in A_i (\forall i \in I) *)
Lemma in_indexed_intersection_then_in_subsets :
 forall a : A,
 in_part a indexed_intersection -> forall i : I, in_part a (f i).
intros.
unfold indexed_intersection in H.
simpl in H.
apply H.
Qed.


(* if a is an element of all A_i, then it is an element of the intersection *)
Lemma in_subsets_then_in_indexed_intersection :
 forall a : A,
 (forall i : I, in_part a (f i)) -> in_part a indexed_intersection.
intros.
unfold indexed_intersection in |- *.
simpl in |- *.
assumption.
Qed.

(* contrarily, if for some i \in I a is not in A_i, then neither is it in *)
(* the indexed intersection *)
Lemma not_in_part_then_not_in_indexed_intersection :
 forall a : A,
 (exists i : I, ~ in_part a (f i)) -> ~ in_part a indexed_intersection.
intros.
inversion H.
simpl in |- *.
intro.
apply H0.
apply H1.
Qed.

Lemma not_in_indexed_intersection_then_not_in_part :
 forall a : A,
 ~ in_part a indexed_intersection -> exists i : I, ~ in_part a (f i).
intros.
simpl in H.
apply (not_all_ex_not I (fun i : I => in_part a (f i))).
assumption.
Qed.

(* if one of the A_i is contained in some subset B, then so is the intersection *)
Lemma subset_included_then_indexed_intersection_included :
 forall B : part_set A,
 (exists i : I, included (f i) B) -> included indexed_intersection B.
intros.
inversion H.
unfold included in |- *.
unfold included in H0.
intros.
apply H0.
simpl in H1.
apply H1.
Qed.

End indexed_int.

(* The following is 'predefined' as "image_map"; I prefer this name: *)
Let range (A B : Setoid) (f : MAP A B) := image f (full A).

Section Compatibility_of_indexed_intersections.
Variable A : Setoid.
Variable I : Setoid.

(** - If $(F_i)_i$ (indexed by $f$) and $(G_j)_j$ (indexed by $g$) denote the same set 
 of subsets of $A$, then the indexed intersections of the $F_i$ and $G_j$ are equal *)
Lemma indexed_intersection_comp :
 forall f g : MAP I (part_set A),
 Equal f g -> Equal (indexed_intersection f) (indexed_intersection g).
intros.
simpl in |- *.
unfold eq_part in |- *.
intros.
split.
intro.
simpl in |- *.
simpl in H0.
intro.
apply in_part_comp_r with (f i); auto.
intro.
simpl in |- *.
simpl in H0.
intro.
apply in_part_comp_r with (g i); auto.
apply Sym.
apply H.
Qed.

(** - in fact, even if only the images of the indexing functions are the same, so 
 is their intersection (ie. the index sets $I,J$ may not be equal, but (indexing the 
 subsets by $F$ and $G$) for all $F_i, i \in I$, there is some $G_j, j \in J$ equal 
 to it and vice versa) *)


Variable J : Setoid.
Lemma indexed_intersection_indep_of_indexing :
 forall (f : MAP I (part_set A)) (g : MAP J (part_set A)),
 Equal (range f) (range g) ->
 Equal (indexed_intersection f) (indexed_intersection g).
intros.
simpl in |- *.
unfold eq_part in |- *.
intro a.
split.
simpl in |- *.
intros H0 j.
unfold image in H.
simpl in H.
unfold eq_part in H.
simpl in H.
generalize (H (g j)).
intros (H1, H2).
cut
 (exists j' : J,
    True /\
    (forall a0 : A,
     (in_part a0 (g j) -> in_part a0 (g j')) /\
     (in_part a0 (g j') -> in_part a0 (g j)))).
intro.
generalize (H2 H3).
intro.
inversion_clear H4.
inversion_clear H5.
elim (H6 a).
auto.
exists j.
intuition.
simpl in |- *.
intros H0 i.
unfold image in H.
simpl in H.
unfold eq_part in H.
simpl in H.
generalize (H (f i)).
intros (H1, H2).
cut
 (exists i' : I,
    True /\
    (forall x0 : A,
     (in_part x0 (f i) -> in_part x0 (f i')) /\
     (in_part x0 (f i') -> in_part x0 (f i)))).
intro.
generalize (H1 H3).
intro.
inversion_clear H4.
inversion_clear H5.
elim (H6 a).
auto.
exists i.
intuition.
Qed.
End Compatibility_of_indexed_intersections.

(** - If $I=\emptyset$ then $\bigcap_{i\in I} X_i = A$ *)

Lemma empty_indexed_intersection_gives_full_set :
 forall (A : Setoid) (f : MAP (empty A) (part_set A)),
 Equal (indexed_intersection f) (full A).
intros.
unfold indexed_intersection in |- *; simpl in |- *.
red in |- *; simpl in |- *; simpl in f.
intro a; split.
auto.
intros _ i; inversion_clear i.
simpl in subtype_prf.
contradiction.
Qed.



(** - Fully general intersections of (a set of) sets is introduced as follows: *)

Definition intersection :
  forall A : Setoid, part_set (part_set A) -> part_set A.
intros A P.
simpl in |- *.
apply
 Build_Predicate
  with (fun a : A => forall p : part_set A, in_part p P -> in_part a p).
red in |- *; simpl in |- *.
intros.
apply in_part_comp_l with x; auto with algebra.
Defined.

Section intersection_v_indexed_intersection.

Lemma intersection_to_indexed_intersection :
 forall (A I : Setoid) (f : MAP I (part_set A)),
 Equal (intersection (range f)) (indexed_intersection f).
intros.
simpl in |- *.
red in |- *.
split; simpl in |- *; intros.
generalize (H (f i)).
intro p; apply p.
exists i; split; auto with algebra.
red in |- *.
split; auto.
inversion_clear H0.
inversion_clear H1.
apply in_part_comp_r with (f x0); auto with algebra.
Qed.

End intersection_v_indexed_intersection.
End MAIN.
