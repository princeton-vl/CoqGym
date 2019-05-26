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


(** %\subsection*{ support :  Map\_embed.v }%*)
Set Implicit Arguments.
Unset Strict Implicit.
Require Export concat.

(** - Any element of $A\subset E$ is of course also an element of $E$ itself.
 Map_embed takes setoid functions $X\to A$ to setoid functions $X\to E$ by embedding

 %\label{Mapembed}% *)
Definition Map_embed :
  forall (X E : Setoid) (A : part_set E) (f : Map X A), MAP X E.
intros.
apply (Build_Map (Ap:=fun n : X => A (f n))).
red in |- *.
intros x y.
case f.
intros.
red in Map_compatible_prf.
generalize Map_compatible_prf.
intro H0.
generalize (H0 x y).
intros.
simpl in |- *.
apply H1.
assumption.
Defined.

Lemma Map_embed_comp :
 forall (X E : Setoid) (A : part_set E) (f g : Map X A),
 f =' g in MAP _ _ -> Map_embed f =' Map_embed g in _.
intros.
unfold Map_embed in |- *; simpl in |- *; red in |- *; simpl in |- *.
intuition.
Qed.

Hint Resolve Map_embed_comp: algebra.

Lemma Map_embed_cons :
 forall (E : Setoid) (A : part_set E) (a : A) (n : Nat) (f : seq n A),
 Map_embed (a;; f) =' subtype_elt a;; Map_embed f in seq _ _.
intros.
simpl in |- *.
red in |- *.
intro x; case x; intro i; case i.
simpl in |- *.
auto with algebra.
intros.
simpl in |- *.
apply Refl.
Qed.

Hint Resolve Map_embed_cons: algebra.

Lemma cons_Map_embed :
 forall (E : Setoid) (A : part_set E) (a : A) (n : Nat) (f : seq n A),
 subtype_elt a;; Map_embed f =' Map_embed (a;; f) in seq _ _.
auto with algebra.
Qed.

Hint Resolve cons_Map_embed: algebra.

Lemma Map_embed_Seqtl :
 forall (E : Setoid) (A : part_set E) (n : Nat) (f : seq n A),
 Map_embed (Seqtl f) =' Seqtl (Map_embed f) in seq _ _.
simple induction n.
simpl in |- *.
red in |- *.
auto with algebra.
intros.
simpl in |- *.
red in |- *.
simpl in |- *.
intro i.
case i.
auto with algebra.
Qed.

Hint Resolve Map_embed_Seqtl: algebra.

Lemma Seqtl_Map_embed :
 forall (E : Setoid) (A : part_set E) (n : Nat) (f : seq n A),
 Seqtl (Map_embed f) =' Map_embed (Seqtl f) in seq _ _.
auto with algebra.
Qed.

Hint Resolve Seqtl_Map_embed: algebra.

Lemma Map_embed_concat :
 forall (E : Setoid) (A : part_set E) (n m : Nat) (f : seq n A) (g : seq m A),
 Map_embed (f ++ g) =' Map_embed f ++ Map_embed g in seq _ _.
simple induction n.
intros.
unfold concat in |- *.
unfold nat_rect in |- *.
apply Refl.
intros.
(* Change =' to Map_eq *)
change (Map_eq (Map_embed (f ++ g)) (Map_embed f ++ Map_embed g)) in |- *.
red in |- *.
intros.
apply Trans with (hdtl (Map_embed (f ++ g)) x); auto with algebra.
case x; intro i; case i.
intro l.
unfold hdtl in |- *.
unfold head in |- *.
unfold concat in |- *.
unfold nat_rect in |- *.
simpl in |- *.
apply Refl.
intros.
unfold hdtl in |- *.
unfold head in |- *.
set (l := in_range_prf) in *.
apply Trans with (Seqtl (Map_embed (f ++ g)) (Build_finiteT (lt_S_n _ _ l)));
 auto with algebra.
fold (n0 + m) in |- *.
apply Sym.
apply
 Trans
  with (Seqtl (Map_embed f ++ Map_embed g) (Build_finiteT (lt_S_n _ _ l))).
fold (n0 + m) in |- *.
apply Sym.
apply (Seqtl_to_seq (Map_embed f ++ Map_embed g)); auto with algebra.
apply Ap_comp; auto with algebra.
apply Trans with (Seqtl (Map_embed f) ++ Map_embed g); auto with algebra.
apply Trans with (Map_embed (Seqtl (f ++ g))).
2: apply (Map_embed_Seqtl (f ++ g)); auto with algebra.
apply Trans with (Map_embed (Seqtl f ++ g)).
2: apply Map_embed_comp; auto with algebra.
apply Trans with (Map_embed (Seqtl f) ++ Map_embed g).
apply
 (concat_comp (f:=Seqtl (Map_embed f)) (f':=Map_embed (Seqtl f))
    (g:=Map_embed g) (g':=Map_embed g)); auto with algebra.
apply Sym.
change
  (Map_embed (Seqtl f ++ g) =' Map_embed (Seqtl f) ++ Map_embed g in seq _ _)
 in |- *.
apply H; auto with algebra.
Qed.

Hint Resolve Map_embed_concat: algebra.

Lemma concat_Map_embed :
 forall (E : Setoid) (A : part_set E) (n m : Nat) (f : seq n A) (g : seq m A),
 Map_embed f ++ Map_embed g =' Map_embed (f ++ g) in seq _ _.
auto with algebra.
Qed.

Hint Resolve concat_Map_embed.

Lemma Map_embed_prop :
 forall (A D : Setoid) (B : part_set A) (v : MAP D B) (i : D),
 in_part (Map_embed v i) B.
simpl in |- *.
intros.
destruct (v i).
simpl in |- *.
red in |- *; auto with algebra.
Qed.