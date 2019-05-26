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


(** * subspaces.v *)
Section MAIN.
Set Implicit Arguments.
Unset Strict Implicit.
Require Export vecspaces_verybasic.
Require Export arb_intersections.
From Algebra Require Export Sub_module.
From Algebra Require Export Singleton.
Require Export algebra_omissions.

Variable F : field.
Variable V : vectorspace F.
Section Subspace_def.

(** %\tocdef{subspace}% *)
Definition subspace (F : field) (V : vectorspace F) := submodule V.

(** - Some finger-flexing first *)
Variable W : subspace V.
Definition inj_subspace : Hom (W:VECSP F) V.
apply
 (BUILD_HOM_MODULE (R:=F) (Mod:=W:VECSP F) (Mod':=V)
    (ff:=fun x : W => subtype_elt x)); auto with algebra.
Defined.
(* This injects the subspace into its "parent" space *)

Lemma inj_subspace_injective : injective inj_subspace.
red in |- *.
auto with algebra.
Qed.

Lemma mult_inherited :
 forall (c : F) (x : W), inj_subspace (c mX x) =' c mX inj_subspace x in _.
intros.
case inj_subspace.
intros.
simpl in |- *.
apply module_hom_prf.
Qed.
End Subspace_def.

Section subspace_awkward_utils.
(** - Officially, "a subspace is a subset that is itself a vectorspace..." We cannot
 have both W:(part_set V) and W:(subspace V). Therefore we need to define subspace-ness
 on the predicate-level as well. *)
(** %\tocdef{is\_subspace}% *)
Definition is_subspace (W : part_set V) : Prop :=
  in_part (zero V) W /\
  (forall x y : V, in_part x W -> in_part y W -> in_part (x +' y) W) /\
  (forall (c : F) (x : V), in_part x W -> in_part (c mX x) W).

Lemma is_subspace_comp :
 forall S S' : part_set V, S =' S' in _ -> is_subspace S -> is_subspace S'.
intros.
red in |- *.
red in H0.
inversion_clear H0.
inversion_clear H2.
split.
apply in_part_comp_r with S; auto with algebra.
split.
intros.
apply in_part_comp_r with S; auto with algebra.
apply H0; auto with algebra.
apply in_part_comp_r with S'; auto with algebra.
apply in_part_comp_r with S'; auto with algebra.
intros.
apply in_part_comp_r with S; auto with algebra.
apply H3; auto with algebra.
apply in_part_comp_r with S'; auto with algebra.
Qed.

(** - From the predicate, then, we may define (uniformly) a subspace having the
 part_set as a carrier *)
Definition subspace_construction :
  forall Ws : part_set V,
  is_subspace Ws -> sigT (fun W : subspace V => W =' Ws in part_set V).
unfold is_subspace in |- *.
intros Ws (H1, (H2, H3)).
cut (sigT (fun Wmod : submodule V => Wmod =' Ws in part_set V)).
intro.
inversion_clear X.
exists x.
assumption.
cut (sigT (fun Wgp : subgroup V => Wgp =' Ws in part_set V)).
intro.
inversion_clear X.
exists
 (Build_submodule
    (fun (a : F) (v : V) (Hyp : in_part v (x:part_set V)) =>
     in_part_comp_r (H3 a v (in_part_comp_r Hyp H)) (Sym H))).
simpl in |- *.
assumption.
cut (sigT (fun Wmon : submonoid V => Wmon =' Ws in part_set V)).
intro.
inversion X.
cut (forall v : V, (min one) mX v =' (min v) in _).
intro.
exists
 (Build_subgroup
    (fun (v : V) (Hyp : in_part v (x:part_set V)) =>
     in_part_comp_r
       (in_part_comp_l (H3 (min one) v (in_part_comp_r Hyp H)) (Sym (H0 v)))
       (Sym H))).
simpl in |- *.
assumption.
intro.
apply Trans with (min one mX v); auto with algebra.
cut (sigT (fun Wsgp : subsgroup V => Wsgp =' Ws in part_set V)).
intro.
inversion_clear X.
exists (Build_submonoid (in_part_comp_r H1 (Sym H))).
simpl in |- *.
assumption.
exists
 (Build_subsgroup
    (fun (x y : V) (Hx : in_part x Ws) (Hy : in_part y Ws) => H2 x y Hx Hy)).
simpl in |- *.
exact
 (fun x : V =>
  conj (fun Hx : in_part x Ws => Hx) (fun Hx : in_part x Ws => Hx)).
Defined.

Definition alt_Build_subspace (W : part_set V) (H : is_subspace W) :
  subspace V := let (w, _) := subspace_construction H in w.

Lemma alt_Build_subspace_OK :
 forall (W : part_set V) (HW : is_subspace W),
 W =' alt_Build_subspace HW in _.
intros.
unfold alt_Build_subspace in |- *.
case (subspace_construction HW).
auto with algebra.
Qed.

Lemma is_subspace_OK : forall W : subspace V, is_subspace W.
intro.
split; try split; auto with algebra.
Qed.

(** - %\intoc{\bf Theorem 1.3}% literally (more-or-less; now easy to prove): *)
Lemma subspace_alt_characterization :
 forall Ws : part_set V,
 in_part (zero V) Ws /\
 (forall x y : V, in_part x Ws -> in_part y Ws -> in_part (x +' y) Ws) /\
 (forall (c : F) (x : V), in_part x Ws -> in_part (c mX x) Ws) <->
 (exists W : subspace V, W =' Ws in part_set V).
split. 
intros.
elim (subspace_construction H).
intros.
exists x; auto.
intro; inversion_clear H.
generalize (is_subspace_OK x).
intro H; red in H; split; try split; intuition;
 (apply in_part_comp_r with (x:part_set V); auto with algebra).
apply H; auto with algebra; (apply in_part_comp_r with Ws; auto with algebra).
apply H3; auto with algebra;
 (apply in_part_comp_r with Ws; auto with algebra).
Qed.


Definition Set_of_subspaces : part_set (part_set V).
apply (Build_Predicate (Pred_fun:=fun W => is_subspace W)).
red in |- *.
intros.
red in |- *; red in H.
inversion_clear H.
inversion_clear H2.
split; try split.
apply in_part_comp_r with x; auto with algebra.
intros; (apply in_part_comp_r with x; auto with algebra).
apply H; auto with algebra.
apply in_part_comp_r with y; auto with algebra.
apply in_part_comp_r with y; auto with algebra.
intros.
apply in_part_comp_r with x; auto with algebra.
apply H3; auto with algebra; (apply in_part_comp_r with y; auto with algebra).
Defined.


(** - %\intoc{\bf Theorem 1.4}% *)
Lemma Set_of_subspaces_closed_under_intersection :
 forall WS : part_set Set_of_subspaces,
 is_subspace (intersection (inject_subsets WS)).
red in |- *.
repeat split.
simpl in |- *.
intros; inversion_clear H.
destruct x.
rename subtype_elt into S.
simpl in H0.
destruct S.
simpl in H0, subtype_prf, subtype_prf0.
apply in_part_comp_r with subtype_elt.
red in subtype_prf0.
inversion_clear subtype_prf0.
auto.
auto with algebra.

simpl in |- *.
intros.
generalize dependent (H p H1); generalize dependent (H0 p H1).
inversion_clear H1.
destruct x0.
destruct subtype_elt.
simpl in H2.
intros; simpl in subtype_prf0.
red in subtype_prf0.
inversion_clear subtype_prf0.
inversion_clear H5.
apply in_part_comp_r with subtype_elt; auto with algebra.
apply H6; apply in_part_comp_r with p; auto with algebra.
intros.
simpl in |- *.
intros; simpl in H.
generalize dependent (H p H0).
inversion_clear H0.
destruct x0.
destruct subtype_elt.
simpl in H1, subtype_prf0.
red in subtype_prf0.
inversion_clear subtype_prf0.
inversion_clear H2.
intro; apply in_part_comp_r with subtype_elt; auto with algebra.
apply H4; apply in_part_comp_r with p; auto with algebra.
Qed.
End subspace_awkward_utils.

End MAIN.

Section Examples.
Variable F : field.
Variable V : vectorspace F.

Lemma singleton_zero_is_subspace : is_subspace (single (zero V)).
intros.
repeat split.
simpl in |- *.
apply Refl.
intros.
simpl in H, H0.
apply in_part_comp_l with ((zero V) +' (zero V)); simpl in |- *;
 auto with algebra.
intros.
simpl in H.
apply in_part_comp_l with (c mX (zero V)); simpl in |- *; auto with algebra.
Qed.

Definition triv_subspace : subspace V.
apply alt_Build_subspace with (single (zero V)).
apply singleton_zero_is_subspace.
Defined.

Definition full_subspace : subspace V.
apply alt_Build_subspace with (full V).
repeat split.
Defined.
End Examples.
