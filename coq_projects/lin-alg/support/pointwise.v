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


(** %\subsection*{ support :  pointwise.v }%*)
Set Implicit Arguments.
Unset Strict Implicit.
Require Export concat.
From Algebra Require Export Cartesian.

(** - The pointwise operation of a binary operator: suppose $f:A\to B, g:A\to C,
 \circ:B\times C\to D$, then (pointwise $\circ$ f g) = $a\mapsto f(a)\circ g(a): A\to D$.
 This is used almost solely to define linear combinations: we have a sequence $\vec a$
 of scalars and a sequence $\vec v$ of vectors, then (sum (pointwise (mX) a v)) = 
 $\sum_{i=0}^{n-1} a_i v_i$.

 %\label{pointwise}% *)

Definition pointwise :
  forall (A B C D : Setoid) (op : Map (cart B C) D) 
    (f : Map A B) (g : Map A C), MAP A D.
intros.
apply (Build_Map (Ap:=fun a : A => op (couple (f a) (g a)))).
red in |- *.
intros.
apply Ap_comp; auto with algebra.
Defined.

Lemma pointwise_comp_general :
 forall (A B C D : Setoid) (op op' : Map (cart B C) D) 
   (f f' : Map A B) (g g' : Map A C),
 op =' op' in MAP _ _ ->
 f =' f' in MAP _ _ ->
 g =' g' in MAP _ _ -> pointwise op f g =' pointwise op' f' g' in _.
intros.
intro.
unfold pointwise in |- *.
simpl in |- *.
apply Ap_comp; auto with algebra.
Qed.

Lemma pointwise_comp :
 forall (n : Nat) (B C D : Setoid) (op op' : Map (cart B C) D)
   (f f' : seq n B) (g g' : seq n C),
 op =' op' in MAP _ _ ->
 f =' f' in _ -> g =' g' in _ -> pointwise op f g =' pointwise op' f' g' in _.
intros.
apply (pointwise_comp_general H H0 H1).
Qed.

Hint Resolve pointwise_comp: algebra.

Lemma pointwise_hd :
 forall (A B C : Setoid) (n : Nat) (v : seq (S n) A) 
   (w : seq (S n) B) (op : Map (cart A B) C) (H : 0 < S n),
 pointwise op v w (Build_finiteT H) ='
 op (couple (v (Build_finiteT H)) (w (Build_finiteT H))) in _.
intros.
unfold pointwise in |- *.
simpl in |- *.
apply Refl.
Qed.

Hint Resolve pointwise_hd: algebra.

Lemma pointwise_cons :
 forall (A B C : Setoid) (a : A) (b : B) (n : Nat) 
   (v : seq n A) (w : seq n B) (op : Map (cart A B) C),
 pointwise op (a;; v) (b;; w) =' op (couple a b);; pointwise op v w
 in seq _ _.
intros.
apply split_hd_tl_equality; auto with algebra.
Qed.

Hint Resolve pointwise_cons: algebra.

Lemma pointwise_hd_tl :
 forall (A B C : Setoid) (n : Nat) (v : seq (S n) A) 
   (w : seq (S n) B) (op : Map (cart A B) C),
 pointwise op v w ='
 op (couple (head v) (head w));; pointwise op (Seqtl v) (Seqtl w) in 
 seq _ _.
intros.
apply split_hd_tl_equality; auto with algebra.
unfold pointwise in |- *; intro; simpl in |- *.
destruct x; (apply Ap_comp; auto with algebra).
Qed.

Hint Resolve pointwise_hd_tl: algebra.

Lemma pointwise_Seqtl :
 forall (A B C : Setoid) (n : Nat) (v : seq n A) (w : seq n B)
   (op : Map (cart A B) C),
 pointwise op (Seqtl v) (Seqtl w) =' Seqtl (pointwise op v w) in seq _ _.
induction n.
simpl in |- *.
red in |- *.
auto with algebra.
intros.
apply
 Trans
  with
    (Seqtl (op (couple (head v) (head w));; pointwise op (Seqtl v) (Seqtl w)));
 auto with algebra.
Qed.

Hint Resolve pointwise_Seqtl: algebra.

Lemma pointwise_concat :
 forall (A B C : Setoid) (n m : Nat) (v : seq n A) 
   (w : seq m A) (x : seq n B) (y : seq m B) (op : MAP (cart A B) C),
 pointwise op (v ++ w) (x ++ y) =' pointwise op v x ++ pointwise op w y
 in seq _ _.
induction n.
intuition.
intros.
apply
 (split_hd_tl_equality (v:=pointwise op (v ++ w) (x ++ y))
    (w:=pointwise op v x ++ pointwise op w y)); auto with algebra.
apply Trans with (pointwise op (Seqtl (v ++ w)) (Seqtl (x ++ y)));
 auto with algebra.
apply Trans with (pointwise op (Seqtl v ++ w) (Seqtl x ++ y)).
apply
 (pointwise_comp (op:=op) (op':=op) (f:=Seqtl (v ++ w)) (f':=
    Seqtl v ++ w) (g:=Seqtl (x ++ y)) (g':=Seqtl x ++ y)); 
 auto with algebra.
apply Trans with (Seqtl (pointwise op v x) ++ pointwise op w y);
 auto with algebra.
apply Trans with (pointwise op (Seqtl v) (Seqtl x) ++ pointwise op w y);
 auto with algebra.
apply (IHn _ (Seqtl v) w (Seqtl x) y).
generalize concat_comp.
intro p.
apply
 (p _ _ _ (pointwise op (Seqtl v) (Seqtl x)) (Seqtl (pointwise op v x))
    (pointwise op w y) (pointwise op w y)); auto with algebra.
apply Sym.
apply (Seqtl_concat (pointwise op v x) (pointwise op w y)).
Qed.

Hint Resolve pointwise_concat: algebra.
