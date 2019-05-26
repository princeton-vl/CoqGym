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


(** %\subsection*{ examples :  vecspace\_Fn.v }%*)
(** - In this file I define the vectorspaces $F^n$ (for arbitrary fields $F$); 
 this is done without using the 'tool' alt_build_vecspace, just to 
 show the tediousness of having to build all successive structures from the
 algebraic hierarchy by hand *)
Set Automatic Coercions Import.
Set Implicit Arguments.
Unset Strict Implicit.

Section Fn_vectors.

Require Export vecspaces_verybasic.
Require Export finite.

(**************************************)
(* In the beginning there was the set *)
(**************************************)

Definition Fn_set (F : Setoid) (n : Nat) : SET := seq n F.

(******************************************)
(* And Coq said, "let there be an sgroup" *)
(******************************************)

Let Fn_plus_fun :
  forall (F : sgroup) (n : Nat), Fn_set F n -> Fn_set F n -> Fn_set F n.
intros F n x y.
simpl in |- *.
apply (Build_Map (Ap:=fun i : fin n => x i +' y i)).
red in |- *.
elim x.
elim y.
intros.
red in Map_compatible_prf.
red in Map_compatible_prf0.
apply SGROUP_comp; auto with algebra.
Defined.

Definition Fn_plus :
  forall (F : sgroup) (n : Nat), law_of_composition (Fn_set F n).
intros F n.
apply (uncurry (f:=Fn_plus_fun (F:=F) (n:=n))).
red in |- *.
simpl in |- *.
intros.
red in |- *.
intro i.
simpl in |- *.
apply SGROUP_comp; auto with algebra.
Defined.

Lemma Fn_plus_associative :
 forall (F : sgroup) (n : Nat), associative (Fn_plus F n).
red in |- *.
intros.
simpl in |- *.
red in |- *.
intro i.
simpl in |- *.
apply SGROUP_assoc.
Qed.

Definition Fn_sgroup (F : sgroup) (n : Nat) : SGROUP :=
  Build_sgroup (Build_sgroup_on (Fn_plus_associative (F:=F) (n:=n))).

(*****************************************************)
(* And there was an sgroup, and Abel saw it was good *)
(*****************************************************)

Lemma Fn_plus_commutative :
 forall (F : abelian_sgroup) (n : Nat), commutative (Fn_plus F n).
red in |- *.
intros.
simpl in |- *.
red in |- *.
intro i.
simpl in |- *.
auto with algebra.
Qed.

Definition Fn_absgp (F : abelian_sgroup) (n : Nat) : ABELIAN_SGROUP :=
  Build_abelian_sgroup
    (Build_abelian_sgroup_on (A:=Fn_sgroup F n)
       (Fn_plus_commutative (F:=F) (n:=n))).

(******************************************************)
(* It is a monoid, Jim, but... exactly as we know it. *)
(******************************************************)

Definition Fn_zero : forall (F : monoid) (n : Nat), Fn_sgroup F n.
intros F n.
apply (Build_Map (Ap:=fun i : fin n => zero F)).
red in |- *.
intros.
apply Refl.
Defined.

Lemma Fn_zero_is_r_unit :
 forall (F : monoid) (n : Nat),
 unit_r (sgroup_law_map (Fn_sgroup F n)) (Fn_zero F n).
intros F n.
red in |- *.
intro.
simpl in |- *.
red in |- *.
intro i.
simpl in |- *.
apply MONOID_unit_r.
Qed.

Lemma Fn_zero_is_l_unit :
 forall (F : monoid) (n : Nat),
 unit_l (sgroup_law_map (Fn_sgroup F n)) (Fn_zero F n).
intros F n.
red in |- *.
intro.
simpl in |- *.
red in |- *.
intro i.
simpl in |- *.
apply MONOID_unit_l.
Qed.

Definition Fn_monoid (F : monoid) (n : Nat) : MONOID :=
  Build_monoid
    (Build_monoid_on (A:=Fn_sgroup F n) (monoid_unit:=
       Fn_zero F n) (Fn_zero_is_r_unit (F:=F) (n:=n))
       (Fn_zero_is_l_unit (F:=F) (n:=n))).

(*********************************)
(* And Abel saw that it was good *)
(*********************************)

Lemma Fn_monoid_is_abelian :
 forall (F : abelian_monoid) (n : Nat), abelian_monoid_on (Fn_monoid F n).
intros F n.
apply Build_abelian_monoid_on.
apply Build_abelian_sgroup_on.
exact (Fn_plus_commutative (F:=F) (n:=n)).
Qed.

Definition Fn_abmon (F : abelian_monoid) (n : Nat) : ABELIAN_MONOID :=
  Build_abelian_monoid (Fn_monoid_is_abelian F n).

(***********************************)
(* What's in a name? That which we *)
(* call a group by any other word  *)
(* would smell as sweet.           *)
(***********************************)


Let Fn_inv_fun : forall (F : group) (n : Nat), Fn_monoid F n -> Fn_monoid F n.
simpl in |- *.
intros F n v.
apply (Build_Map (Ap:=fun i : fin n => group_inverse F (v i))).
red in |- *.
intros i i' H.
apply GROUP_comp; auto with algebra.
Defined.

Definition Fn_inv :
  forall (F : group) (n : Nat), Map (Fn_monoid F n) (Fn_monoid F n).
intros F n.
apply (Build_Map (Ap:=Fn_inv_fun (F:=F) (n:=n))).
red in |- *.
intros.
simpl in |- *.
red in |- *.
intro i.
simpl in H.
red in H.
simpl in |- *.
apply GROUP_comp; auto with algebra.
Defined.

Lemma Fn_inv_is_r_inverse :
 forall (F : group) (n : Nat),
 inverse_r (Fn_plus F n) (Fn_zero F n) (Fn_inv F n).
intros F n.
red in |- *.
intro.
simpl in |- *.
red in |- *.
intro i.
simpl in |- *.
auto with algebra.
Qed.

Lemma Fn_inv_is_l_inverse :
 forall (F : group) (n : Nat),
 inverse_l (Fn_plus F n) (Fn_zero F n) (Fn_inv F n).
intros F n.
red in |- *.
intro.
simpl in |- *.
red in |- *.
intro i.
simpl in |- *.
auto with algebra.
Qed.

Definition Fn_group (F : group) (n : Nat) : GROUP :=
  Build_group
    (Build_group_on (group_inverse_map:=Fn_inv F n)
       (Fn_inv_is_r_inverse (F:=F) (n:=n))
       (Fn_inv_is_l_inverse (F:=F) (n:=n))).

(****************************)
(* Once more, Abel spoke... *)
(****************************)

Lemma Fn_group_is_abelian :
 forall (F : abelian_group) (n : Nat), abelian_group_on (Fn_group F n).
intros.
apply Build_abelian_group_on.
apply Build_abelian_monoid_on.
apply Build_abelian_sgroup_on.
exact (Fn_plus_commutative (F:=F) (n:=n)).
Qed.

Definition Fn_abgp (F : abelian_group) (n : Nat) : ABELIAN_GROUP :=
  Build_abelian_group (Fn_group_is_abelian F n).

(*******************************)
(* Alle modulen werden brueder *)
(*******************************)

Definition Fn_scmult_fun :
  forall (F : ring) (n : Nat), F -> Fn_set F n -> Fn_set F n.
simpl in |- *.
intros F n c v.
apply (Build_Map (Ap:=fun i : fin n => c rX v i)).
red in |- *.
auto with algebra.
Defined.

Lemma Fn_scmult_fun_comp :
 forall (F : ring) (n : Nat) (c c' : F) (v v' : Fn_set F n),
 c =' c' in _ ->
 v =' v' in _ -> Fn_scmult_fun c v =' Fn_scmult_fun c' v' in _.
simpl in |- *.
intros.
red in |- *.
intro i.
simpl in |- *.
apply RING_comp; auto with algebra.
Qed.

(********************************)
(* But that takes quite a while *)
(********************************)

Section necessary_module_stuff.

Let Fn_scmult_fun_map :
  forall (F : ring) (n : Nat), F -> MAP (Fn_set F n) (Fn_set F n).
intros F n c.
apply (Build_Map (Ap:=fun v : Fn_set F n => Fn_scmult_fun c v)).
red in |- *.
intros v v' H.
apply Fn_scmult_fun_comp; auto with algebra.
Defined.

Let Fn_scmult_F_to_EndoSet :
  forall (F : ring) (n : Nat),
  Map (Build_monoid (ring_monoid F)) (Endo_SET (Fn_set F n)).
intros F n.
simpl in |- *.
apply (Build_Map (Ap:=fun c : F => Fn_scmult_fun_map (F:=F) n c)).
red in |- *.
intros c c' H.
simpl in |- *.
red in |- *.
intro v.
generalize
 (Fn_scmult_fun_comp (F:=F) (n:=n) (c:=c) (c':=c') (v:=v) (v':=v) H).
simpl in |- *.
generalize (Refl v).
auto.
Defined.

Let Fn_scmult_sgroup_hom :
  forall (F : ring) (n : Nat),
  sgroup_hom (Build_monoid (ring_monoid F)) (Endo_SET (Fn_set F n)).
intros F n.
apply (Build_sgroup_hom (sgroup_map:=Fn_scmult_F_to_EndoSet F n)).
red in |- *.
simpl in |- *.
red in |- *.
intros c c' v.
simpl in |- *.
red in |- *.
intro i.
simpl in |- *.
apply Trans with ((c rX c') rX Ap v i); auto with algebra.
Defined.

Let Fn_scmult_monoid_hom :
  forall (F : ring) (n : Nat),
  monoid_hom (Build_monoid (ring_monoid F)) (Endo_SET (Fn_set F n)).
intros.
apply (Build_monoid_hom (monoid_sgroup_hom:=Fn_scmult_sgroup_hom F n)).
red in |- *.
simpl in |- *.
red in |- *.
intro v.
simpl in |- *.
red in |- *.
intro i.
simpl in |- *.
apply Trans with (one rX v i); auto with algebra.
Defined.

Definition Fn_scmult :
  forall (F : ring) (n : Nat),
  operation (Build_monoid (ring_monoid F)) (Fn_abgp F n).
intros.
simpl in |- *.
exact (Fn_scmult_monoid_hom F n).
Defined.

End necessary_module_stuff.

Lemma Fn_scmult_l_lin :
 forall (F : ring) (n : Nat), op_lin_left (Fn_scmult F n).
red in |- *.
intros F n c c' v.
simpl in |- *.
red in |- *.
intro i.
simpl in |- *.
apply RING_dist_r.
Qed.

Lemma Fn_scmult_r_lin :
 forall (F : ring) (n : Nat), op_lin_right (Fn_scmult F n).
intros F n.
red in |- *.
intros c c' v.
simpl in |- *.
red in |- *.
intro i.
simpl in |- *.
apply RING_dist_l.
Qed.

Definition Fn_mod (F : ring) (n : Nat) : MODULE F :=
  Build_module
    (Build_module_on (Fn_scmult_l_lin (F:=F) (n:=n))
       (Fn_scmult_r_lin (F:=F) (n:=n))).

Definition Fn (F : field) (n : Nat) : VECSP F := Fn_mod F n:vectorspace F.

End Fn_vectors.


(** - Defining the standard basis vectors needs a generalised Kronecker since
 0 and 1 from [nat] cannot be used in $F$ *)
Section Basis_vectors.

Fixpoint Kronecker (A : Setoid) (t f : A) (n m : Nat) {struct m} : A :=
  match n, m with
  | O, O => t
  | S n', O => f
  | O, S m' => f
  | S n', S m' => Kronecker t f n' m'
  end.

Lemma Kronecker_case_equal :
 forall (A : Setoid) (t f : A) (n m : Nat),
 n =' m in _ -> Kronecker t f n m =' t in _.
induction n; induction m; auto with algebra; intros.
inversion_clear H.
inversion_clear H.
simpl in |- *.
apply IHn; auto with algebra.
simpl in |- *; simpl in H; auto with arith.
Qed.

Lemma Kronecker_case_unequal :
 forall (A : Setoid) (t f : A) (n m : Nat),
 ~ n =' m in _ -> Kronecker t f n m =' f in _.
intros until n.
induction n.
induction m; auto with algebra.
intros; absurd (0 = 0); auto.
intros.
induction m; auto with algebra.
simpl in |- *.
apply IHn; auto with algebra.
intro p; red in H; apply H; simpl in p; simpl in |- *; auto with arith.
Qed.

Definition Basisvec_Fn :
  forall (F : field) (n i : Nat) (H : i < n), Fn F n:Type.
intros.
simpl in |- *.
apply
 (Build_Map
    (Ap:=fun j : fin n =>
         match j with
         | Build_finiteT j' _ => Kronecker one (zero F) i j'
         end)).
red in |- *.
intros x y.
elim x.
elim y.
simpl in |- *.
intros.
rewrite H0.
apply Refl.
Defined.
End Basis_vectors.