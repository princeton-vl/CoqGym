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


(** %\subsection*{ support :  sums.v }%*)
Set Implicit Arguments.
Unset Strict Implicit.
Require Export Map_embed.
Require Export algebra_omissions.
From Algebra Require Export Sub_monoid.
Require Export more_syntax.

(** - A sequence of v1...vn of elements in a monoid V is a map (fin n)->V.
 We define the sum of a sequence of these elements.
 Of course we take the sum of an empty sequence to be zero 

 %\label{sum}% *)
Fixpoint sum (V : monoid) (n : Nat) {struct n} : seq n V -> V :=
  match n return (seq n V -> V) with
  | O => fun x : seq 0 V => zero V
  | S m => fun x : seq (S m) V => head x +' sum (Seqtl x)
  end.

Lemma sum_comp :
 forall (M : monoid) (n : Nat) (f f' : seq n M),
 f =' f' in _ -> sum f =' sum f' in _.
induction n.
intros.
simpl in |- *.
apply Refl.
intros.
unfold sum in |- *.
apply SGROUP_comp; auto with algebra.
apply IHn.
change (Seqtl f =' Seqtl f' in _) in |- *.
apply Seqtl_comp; auto with algebra.
Qed.

Hint Resolve sum_comp: algebra.

Lemma sum_cons :
 forall (M : monoid) (m : M) (n : Nat) (f : seq n M),
 sum (m;; f) =' m +' sum f in _.
intros.
induction  n as [| n Hrecn].
simpl in |- *.
apply Refl.
unfold sum at 1 in |- *.
apply SGROUP_comp; auto with algebra.
apply sum_comp.
generalize dependent (Seqtl_cons_inv m f); intro p.
apply p.
Qed.

Hint Resolve sum_cons: algebra.

Lemma sum_concat :
 forall (n m : Nat) (G : monoid) (a : seq n G) (b : seq m G),
 sum (a ++ b) =' sum a +' sum b in _.
induction n.
intros.
apply Trans with ((zero G) +' sum b); auto with algebra.
intros.
apply Trans with (sum (hdtl a) +' sum b); auto with algebra.
apply Trans with (sum (hdtl a ++ b)); auto with algebra.
apply Trans with (sum (head a;; Seqtl a ++ b)).
unfold hdtl in |- *.
apply sum_comp; auto with algebra.
unfold hdtl in |- *.
apply Trans with (head a +' sum (Seqtl a ++ b)); auto with algebra.
apply Trans with (head a +' sum (Seqtl a) +' sum b); auto with algebra.
apply Trans with (head a +' (sum (Seqtl a) +' sum b)); auto with algebra.
Qed.

Hint Resolve sum_concat: algebra.

Lemma subtype_sum :
 forall (n : nat) (A : monoid) (B : submonoid A) (c : seq n B),
 subtype_elt (sum c) =' sum (Map_embed c) in _.
intros.
apply Sym.
induction n.
simpl in |- *.
auto with algebra.
apply Trans with (head (Map_embed c) +' sum (Seqtl (Map_embed c)));
 auto with algebra.
apply Trans with (subtype_elt (head c +' sum (Seqtl c))).
apply Trans with (subtype_elt (head c) +' subtype_elt (sum (Seqtl c)));
 auto with algebra.
apply Trans with (head (Map_embed c) +' sum (Map_embed (Seqtl c)));
 auto with algebra.
apply SGROUP_comp; auto with algebra.
apply sum_comp; auto with algebra.
apply Sym; auto with algebra.
generalize Map_embed_Seqtl.
intro p.
apply (p _ _ _ (c:seq _ _)).
apply subtype_elt_comp.
apply Sym; auto with algebra.
Qed.
