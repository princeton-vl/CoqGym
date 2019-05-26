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


(** %\subsection*{ examples :  trivial\_spaces.v }%*)
Set Implicit Arguments.
Unset Strict Implicit.
Require Export bases_finite_dim.
From Algebra Require Export Singleton.
Require Export alt_build_vecsp.
(** - Here we will make the trivial vectorspace as an example of vectorspaces. Notice
 this differs from the trivial subspace defined in subspaces.v *)

(** -  The underlying set contains only the zero vector; we can take an arbitrary set
 and an arbitrary element on which we build the trivial vectorspace containing only 
 that element as the zero vector *)

Section MAIN.
Variable A : Setoid.
Variable a : A.

Let T := single a.

Definition Tplus : Map2 T T T.
apply
 Build_Map2
  with (fun t t' : single a => Build_subtype (Refl a:Pred_fun (single a) a)).
red in |- *.
intros.
auto with algebra.
Defined.

Definition Tzero : T := Build_subtype (Refl a:Pred_fun (single a) a).

Definition Tminus : Map T T.
apply Build_Map with (fun t : T => t).
red in |- *.
auto.
Defined.

Variable F : field.

Definition Tmult : Map2 F T T.
apply Build_Map2 with (fun (f : F) (t : T) => t).
red in |- *.
auto.
Defined.

Definition trivvecsp : vectorspace F.
apply alt_Build_vectorspace with T Tplus Tmult Tzero Tminus; red in |- *;
 auto with algebra.
simpl in |- *.
red in |- *.
intro; destruct x.
simpl in subtype_prf.
simpl in |- *.
auto with algebra.
simpl in |- *.
red in |- *.
simpl in |- *.
intros; destruct x; simpl in subtype_prf; simpl in |- *; auto with algebra.
Defined.
End MAIN.

Section basis.
Variable F : field.
Require Export bases.
Variable A : Setoid.
Variable a : A.
Definition triv_basis : basis (trivvecsp a F).
apply Build_basis with (empty (trivvecsp a F)).
red in |- *.
split.
red in |- *.
cbn - [trivvecsp].
red in |- *.
cbn - [trivvecsp].
Opaque trivvecsp.
split; auto; intros _.
Transparent trivvecsp.
red in |- *.
exists 0.
exists (empty_seq F).
Transparent trivvecsp.
exists (empty_seq (empty (single a))).
cbn - [trivvecsp].
unfold trivvecsp in x.
repeat red in x.
destruct x.
red in |- *.
simpl in subtype_prf.
auto.
apply empty_lin_indep.
Defined.

(* More generally: *)
Definition trivial_basis :
  forall V : vectorspace F, full V =' single (zero V) in _ -> basis V.
intros.
apply Build_basis with (empty V).
red in |- *.
split.
2: apply empty_lin_indep.
red in |- *.
apply Trans with (single (zero V)); auto with algebra.
simpl in |- *.
red in |- *.
simpl in |- *.
split; intros.
red in H0.
inversion_clear H0.
inversion_clear H1.
inversion_clear H0.
assert (x0 =' 0 in _).
generalize no_seq_n_empty; intro p.
apply (p _ V (empty V) (Refl (empty V)) x2).
simpl in H0.
move H0 after x1.
generalize dependent x0.
intros x0 H0.
rewrite H0.
clear H0 x0.
simpl in |- *.
auto.

apply is_lin_comb_comp with (zero V) (empty V); auto with algebra.
red in |- *.
exists 0.
simpl in |- *.
exists (empty_seq F).
exists (empty_seq (empty V)).
auto with algebra.
Defined.


Lemma trivial_then_has_dim_zero :
 forall V : vectorspace F, full V =' single (zero V) in _ -> has_dim 0 V.
intros.
red in |- *.
exists (trivial_basis H).
simpl in |- *.
apply empty_then_has_zero_elements; auto with algebra.
Qed.

Lemma trivvecsp_has_dim_zero : has_dim 0 (trivvecsp a F).
red in |- *.
exists triv_basis.
apply has_n_elements_comp with 0 (empty (trivvecsp a F)); auto with algebra.
Qed.
End basis.
