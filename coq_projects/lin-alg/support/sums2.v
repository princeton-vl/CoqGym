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


(** %\subsection*{ support :  sums2.v }%*)
Set Implicit Arguments.
Unset Strict Implicit.
From Algebra Require Export Abelian_group_facts.
Require Export sums.
Require Export omit.
Require Export modify_seq.
Require Export const.

Lemma sum_omit_zeros :
 forall (M : monoid) (n : Nat) (v : seq n M) (i : fin n),
 v i =' (zero M) in _ -> sum v =' sum (omit v i) in _.
destruct n.
auto with algebra.

induction  n as [| n Hrecn].
intros.
simpl in |- *.
generalize H.
unfold head in |- *.
elim i.
intro x; case x.
intros.
apply Trans with (v (Build_finiteT (lt_O_Sn 0))); auto with algebra.
apply Trans with (v (Build_finiteT in_range_prf)); auto with algebra.
intros.
inversion in_range_prf.
inversion H2.
intros.
generalize H; clear H.
case i.
intro x; case x.
intros.
apply Trans with (sum (hdtl v)); auto with algebra.
unfold hdtl in |- *.
unfold head in |- *.
apply Trans with ((zero M) +' sum (Seqtl v)); auto with algebra.
apply Trans with (v (Build_finiteT (lt_O_Sn (S n))) +' sum (Seqtl v));
 auto with algebra.
apply SGROUP_comp; auto with algebra.
apply Trans with (v (Build_finiteT in_range_prf)); auto with algebra.
intros.
apply Trans with (sum (hdtl v)); auto with algebra.
apply
 Trans
  with
    (sum (head v;; omit (Seqtl v) (Build_finiteT (lt_S_n _ _ in_range_prf))));
 auto with algebra.
unfold hdtl in |- *.
apply Trans with (head v +' sum (Seqtl v)); auto with algebra.
apply
 Trans
  with
    (head v +' sum (omit (Seqtl v) (Build_finiteT (lt_S_n _ _ in_range_prf))));
 auto with algebra.
apply SGROUP_comp; auto with algebra.
apply Hrecn; auto with algebra.
apply Trans with (v (Build_finiteT in_range_prf)); auto with algebra.
generalize Seqtl_to_seq.
intro.
apply (H0 M (S n) v n0 (lt_S_n n0 (S n) in_range_prf) in_range_prf).
Qed.

Lemma sum_modify :
 forall (AG : abelian_group) (n : Nat) (v : seq n AG) (i : fin n) (a : AG),
 sum (modify_seq v i a) =' sum v +' (min v i) +' a in _.
simple induction n.
intros.
inversion i.
inversion in_range_prf.
intros.
destruct i.
destruct index as [| n1].
apply Trans with (sum (a;; Seqtl v)); auto with algebra.
apply Trans with (sum (hdtl v) +' (min head v) +' a).
apply Trans with (a +' sum (Seqtl v)); auto with algebra.
apply Trans with (sum (Seqtl v) +' a); auto with algebra.
apply SGROUP_comp; auto with algebra.
unfold hdtl in |- *.
apply Trans with (head v +' sum (Seqtl v) +' (min head v)); auto with algebra.
apply Trans with (sum (Seqtl v) +' head v +' (min head v)); auto with algebra.
apply Trans with (sum (Seqtl v) +' (head v +' (min head v)));
 auto with algebra.
apply Trans with (sum (Seqtl v) +' (zero AG)); auto with algebra.

apply SGROUP_comp; auto with algebra.
apply SGROUP_comp; auto with algebra.

apply Trans with (sum (hdtl (modify_seq v (Build_finiteT in_range_prf) a)));
 auto with algebra.
unfold hdtl in |- *.
apply
 Trans
  with
    (head (modify_seq v (Build_finiteT in_range_prf) a) +'
     sum (Seqtl (modify_seq v (Build_finiteT in_range_prf) a)));
 auto with algebra.
apply
 Trans
  with (head v +' sum (Seqtl (modify_seq v (Build_finiteT in_range_prf) a)));
 auto with algebra.
apply Trans with (sum (hdtl v) +' (min v (Build_finiteT in_range_prf)) +' a);
 auto with algebra.
unfold hdtl in |- *.
apply
 Trans
  with (head v +' sum (Seqtl v) +' (min v (Build_finiteT in_range_prf)) +' a);
 auto with algebra.
apply
 Trans
  with
    (head v +' (sum (Seqtl v) +' (min v (Build_finiteT in_range_prf)) +' a)).
apply SGROUP_comp; auto with algebra.
apply
 Trans
  with
    (sum (modify_seq (Seqtl v) (Build_finiteT (lt_S_n _ _ in_range_prf)) a));
 auto with algebra.

apply
 Trans
  with
    (sum (Seqtl v) +' (min Seqtl v (Build_finiteT (lt_S_n _ _ in_range_prf))) +'
     a); auto with algebra.
apply
 Trans
  with
    (head v +' (sum (Seqtl v) +' (min v (Build_finiteT in_range_prf))) +' a);
 auto with algebra.
Qed.

Lemma sum_of_zeros :
 forall (M : monoid) (n : Nat) (v : seq n M),
 v =' const_seq n (zero M) in _ -> sum v =' (zero M) in _.
simple induction n; intros.
simpl in |- *.
apply Refl.
apply Trans with (sum (hdtl v)); auto with algebra.
unfold hdtl in |- *.
apply Trans with (head v +' sum (Seqtl v)); auto with algebra.
apply Trans with ((zero M) +' sum (Seqtl v)).
apply SGROUP_comp; auto with algebra.
unfold head in |- *.
simpl in H0.
red in H0.
apply Trans with (const_seq (S n0) (zero M) (Build_finiteT (lt_O_Sn n0)));
 auto with algebra.
apply Trans with ((zero M) +' (zero M)); auto with algebra.
apply SGROUP_comp; auto with algebra.
apply H; auto with algebra.
simpl in |- *; simpl in H0.
red in |- *; red in H0.
simpl in |- *; simpl in H0.
intro.
destruct x.
auto with algebra.
Qed.

Hint Resolve sum_omit_zeros sum_modify sum_of_zeros: algebra.
