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


(** %\subsection*{ support :  cast\_between\_subsets.v }%*)
Set Implicit Arguments.
Unset Strict Implicit.
Require Export Map_embed.
Require Export algebra_omissions.

(** - Various casting functions between equal but non-convertible types *)

(** - This one maps elements of a subset to the same subset under a different name
 %\label{mapbetweenequalsubsets}% *)
Definition map_between_equal_subsets :
  forall (A : Setoid) (X Y : part_set A), X =' Y in _ -> X -> Y.
intros A X Y H x.
inversion_clear x.
apply (Build_subtype (E:=A) (P:=Y) (subtype_elt:=subtype_elt)).
simpl in H.
red in H.
generalize (H subtype_elt).
intro H'.
inversion_clear H'.
apply H0; auto with algebra.
Defined.

Lemma subtype_elt_eats_map_between_equal_subsets :
 forall (A : Setoid) (X Y : part_set A) (H : X =' Y in _) (x : X),
 subtype_elt (map_between_equal_subsets H x) =' subtype_elt x in _.
intros.
elim x.
simpl in |- *.
auto with algebra.
Qed.

Hint Resolve subtype_elt_eats_map_between_equal_subsets: algebra.

Lemma map_between_equal_subsets_inj :
 forall (A : Setoid) (X Y : part_set A) (H H' : X =' Y in _) (x x' : X),
 map_between_equal_subsets H x =' map_between_equal_subsets H' x' in _ ->
 x =' x' in _.
simpl in |- *.
unfold subtype_image_equal in |- *; simpl in |- *.
intros.
apply Trans with (subtype_elt (map_between_equal_subsets H x));
 auto with algebra.
apply Trans with (subtype_elt (map_between_equal_subsets H' x'));
 auto with algebra.
Qed.

(** - This one turns $f:A\to X$ into $A\to Y$ whenever $X='Y$ *)

(** %\label{Maptoequalsubsets}% *)
Definition Map_to_equal_subsets :
  forall (A B : Setoid) (X Y : part_set A), X =' Y in _ -> MAP B X -> MAP B Y.
intros.
apply (Build_Map (Ap:=fun b : B => map_between_equal_subsets H (X0 b))).
red in |- *; simpl in |- *; red in |- *.
intros.
unfold map_between_equal_subsets in |- *.
generalize (Map_compatible_prf X0 H0).
case (X0 x); case (X0 y).
simpl in |- *.
auto.
Defined.

Lemma subtype_elt_eats_Map_to_equal_subsets :
 forall (A B : Setoid) (X Y : part_set A) (H : X =' Y in _) 
   (b : B) (M : Map B X),
 subtype_elt (Map_to_equal_subsets H M b) =' subtype_elt (M b) in _.
intros.
simpl in |- *.
case (M b).
simpl in |- *.
auto with algebra.
Qed.

Hint Resolve subtype_elt_eats_Map_to_equal_subsets: algebra.

Lemma Map_embed_eats_Map_to_equal_subsets :
 forall (A B : Setoid) (X Y : part_set A) (H : X =' Y in _) (M : Map B X),
 Map_embed (Map_to_equal_subsets H M) =' Map_embed M in _.
intros.
simpl in |- *.
red in |- *.
intros b.
simpl in |- *.
auto with algebra.
Qed.

Hint Resolve Map_embed_eats_Map_to_equal_subsets: algebra.

Lemma Map_to_equal_subsets_inj :
 forall (A B : Setoid) (X Y : part_set A) (H H' : X =' Y in _)
   (f g : Map B X),
 Map_to_equal_subsets H f =' Map_to_equal_subsets H' g in _ ->
 f =' g in MAP _ _.
unfold Map_to_equal_subsets in |- *; simpl in |- *; unfold Map_eq in |- *;
 simpl in |- *; unfold subtype_image_equal in |- *; 
 simpl in |- *.
intros.
apply subtype_elt_comp.
apply map_between_equal_subsets_inj with Y H H'; auto with algebra.
simpl in |- *; red in |- *; simpl in |- *.
auto.
Qed.

(** - if $\forall b\in B, f(b)\in W\subset A$ for $f:B\to A$ then $f$ can be seen as
 $f:B\to W$. This is done by cast_map_to_subset. *)

Definition cast_to_subset_fun :
  forall (A B : Setoid) (v : MAP B A) (W : part_set A),
  (forall i : B, in_part (v i) W) -> (B -> W:Type).
intros A B v.
elim v.
intros vseq vprf; intros.
generalize X; clear X.
simpl in |- *.
exact (fun i : B => Build_subtype (H i)).
Defined.

Lemma cast_doesn't_change :
 forall (A B : Setoid) (v : MAP B A) (W : part_set A)
   (H : forall i : B, in_part (v i) W) (i : B),
 subtype_elt (cast_to_subset_fun H i) =' v i in _.
intros A B v.
elim v.
simpl in |- *.
auto with algebra.
Qed.

Hint Resolve cast_doesn't_change: algebra.

(** %\label{castmaptosubset}% *)
Definition cast_map_to_subset :
  forall (A B : Setoid) (v : MAP B A) (W : part_set A),
  (forall i : B, in_part (v i) W) -> MAP B W.
intros.
cut (fun_compatible (cast_to_subset_fun H)).
intro.
exact (Build_Map H0).
red in |- *.
simpl in |- *.
red in |- *.
intros.
apply Trans with (v x); auto with algebra.
apply Trans with (v y); auto with algebra.
Defined.

Lemma cast_map_to_subset_doesn't_change :
 forall (A B : Setoid) (v : MAP B A) (W : part_set A)
   (H : forall i : B, in_part (v i) W) (i : B),
 subtype_elt (cast_map_to_subset H i) =' v i in _.
intros.
simpl in |- *.
auto with algebra.
Qed.

Hint Resolve cast_map_to_subset_doesn't_change: algebra.

Lemma Map_embed_cast_map_to_subset_inv :
 forall (A B : Setoid) (v : MAP B A) (W : part_set A)
   (H : forall i : B, in_part (v i) W),
 Map_embed (cast_map_to_subset H) =' v in _.
intros.
simpl in |- *.
red in |- *.
simpl in |- *.
auto with algebra.
Qed.

Hint Resolve Map_embed_cast_map_to_subset_inv: algebra.

Lemma Map_embed_eats_cast_map_to_subset :
 forall (A D : Setoid) (B C : part_set A) (v : MAP D B)
   (H : forall i : D, in_part (Map_embed v i) C),
 Map_embed (cast_map_to_subset H) =' Map_embed v in _.
intros.
auto with algebra.
Qed.

Hint Resolve Map_embed_eats_cast_map_to_subset: algebra.

Lemma seq_castable :
 forall (A B : Setoid) (v : MAP B A) (W : part_set A),
 (forall i : B, in_part (v i) W) -> exists w : MAP B W, Map_embed w =' v in _.
intros.
exists (cast_map_to_subset H).
auto with algebra.
Qed.

Hint Resolve seq_castable: algebra.

Lemma subset_seq_castable :
 forall (A D : Setoid) (B C : part_set A) (v : MAP D B)
   (H : forall i : D, in_part (Map_embed v i) C),
 exists w : MAP D C, Map_embed w =' Map_embed v in _.
intros.
exists (cast_map_to_subset H).
auto with algebra.
Qed.

Hint Resolve subset_seq_castable: algebra.

Lemma cast_seq_nice :
 forall (A B : Setoid) (v : MAP B A) (W : part_set A)
   (H : forall i : B, in_part (v i) W) (P : Predicate (MAP B A)),
 Pred_fun P v -> Pred_fun P (Map_embed (cast_map_to_subset H)).
destruct P.
intros.
red in Pred_compatible_prf.
simpl in |- *.
simpl in H0.
apply Pred_compatible_prf with v; auto with algebra.
Qed.

Hint Resolve cast_seq_nice: algebra.

Lemma cast_subset_seq_nice :
 forall (A D : Setoid) (B C : part_set A) (v : MAP D B)
   (H : forall i : D, in_part (Map_embed v i) C) (P : Predicate (MAP D A)),
 Pred_fun P (Map_embed v) -> Pred_fun P (Map_embed (cast_map_to_subset H)).
intros.
auto with algebra.
Qed.

Hint Resolve cast_subset_seq_nice: algebra.

Lemma cast_respects_predicates_per_elt :
 forall (A D : Setoid) (B C : part_set A) (v : MAP D B) 
   (P : Predicate A) (H : forall i : D, in_part (Map_embed v i) C) 
   (i : D),
 Pred_fun P (Map_embed v i) ->
 Pred_fun P (Map_embed (cast_map_to_subset H) i).
intros.
generalize H0; clear H0; elim P.
intros Pf pc H0.
simpl in |- *.
simpl in H0.
auto.
Qed.

Lemma cast_respects_all_elt_predicates :
 forall (A D : Setoid) (B C : part_set A) (v : MAP D B) 
   (P : Predicate A) (H : forall i : D, in_part (Map_embed v i) C),
 (forall i : D, Pred_fun P (Map_embed v i)) ->
 forall j : D, Pred_fun P (Map_embed (cast_map_to_subset H) j).
intros.
generalize H0; clear H0; elim P.
intros Pf pc H0.
simpl in |- *.
simpl in H0.
auto.
Qed.

Hint Resolve cast_respects_predicates_per_elt
  cast_respects_all_elt_predicates: algebra.

(** - Similarly, if $B\subset C$ are subsets of $A$, then $f:D\to B$ is also $f:D\to C$. *)

Definition Map_include :
  forall (A D : Setoid) (B C : part_set A),
  included B C -> MAP D B -> MAP D C.
intros.
apply (cast_map_to_subset (v:=Map_embed X)).
red in H.
intro.
apply H; auto with algebra.
apply Map_embed_prop; auto with algebra.
Defined.

Definition Map_include_map :
  forall (A D : Setoid) (B C : part_set A),
  included B C -> MAP (MAP D B) (MAP D C).
intros.
simpl in |- *.
apply Build_Map with (Map_include (D:=D) H).
red in |- *.
intuition.
Defined.