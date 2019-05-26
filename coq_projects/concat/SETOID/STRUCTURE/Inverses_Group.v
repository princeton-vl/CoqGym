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


(****************************************************************************)
(*                 The Calculus of Inductive Constructions                  *)
(*                                                                          *)
(*                                Projet Coq                                *)
(*                                                                          *)
(*                     INRIA                        ENS-CNRS                *)
(*              Rocquencourt                        Lyon                    *)
(*                                                                          *)
(*                                 Coq V6.1                                 *)
(*                               Oct 1st 1996                               *)
(*                                                                          *)
(****************************************************************************)
(*                              Inverses_Group.v                            *)
(****************************************************************************)

Require Export Group.

Set Implicit Arguments.
Unset Strict Implicit.
    
(* The Monoid of inverse pairs on a Monoid *)

Section inv_def.

Variable A : Monoid.

(* The set Inverses_set of inverse pairs on A *)

Structure Inverses : Type := 
  {Inv_elt_l : A;
   Inv_elt_r : A;
   Prf_invs1 : Inverses_rel Inv_elt_l Inv_elt_r;
   Prf_invs2 : Inverses_rel Inv_elt_r Inv_elt_l}.

Definition Inverses_eq (x y : Inverses) := Inv_elt_l x =_S Inv_elt_l y.

Lemma Inverses_equiv : Equivalence Inverses_eq.
Proof.
apply Build_Equivalence.
unfold Reflexive in |- *.
intro x; unfold Inverses_eq in |- *. 
apply Refl.
apply Build_Partial_equivalence.
unfold Transitive in |- *.
intros x y z H1 H2; unfold Inverses_eq in |- *. 
apply Trans with (Inv_elt_l y); assumption.
unfold Symmetric in |- *.
intros x y H; unfold Inverses_eq in |- *. 
apply Sym; assumption.
Qed.

Canonical Structure Inverses_setoid : Setoid := Inverses_equiv.

(* General group theory equational reasoning *)

Lemma Eq_abb'a' :
 forall a b a' b' : A,
 Inverses_rel a a' -> Inverses_rel b b' -> Inverses_rel (a +_M b) (b' +_M a').
Proof.
intros a b a' b' i j.
red in |- *.
(* (a.b).b'.a' = e *)
(* *) apply Trans with (a +_M (b +_M (b' +_M a'))).
apply Mass1.
(* a.b.b'.a' = e *)
(* *) apply Trans with (a +_M a'). 
(* a.b.b'.a' = a.a' *)
apply (Map2_l (Mop A) (b1:=b +_M (b' +_M a')) (b2:=a') a).
(* b.b'.a' = a' *)
(* *) apply Trans with (b +_M b' +_M a').
apply Mass.
(* (b.b').a' = a' *)
(* *) apply Trans with (Munit A +_M a'). 
apply (Map2_r (Mop A) (a1:=b +_M b') (a2:=Munit A) a').
apply j.
(* e.a' = a' *)
apply Midl.
apply i.
Qed.

(* Composition operation on Inverses_setoid *)

 Section inverses_comp_def.

 Variable x y : Inverses_setoid.

 Definition Inv_comp_elt_l := Inv_elt_l x +_M Inv_elt_l y.

 Definition Inv_comp_elt_r := Inv_elt_r y +_M Inv_elt_r x.

 Lemma Inv_comp_invs1 : Inverses_rel Inv_comp_elt_l Inv_comp_elt_r.
 Proof.
 exact (Eq_abb'a' (Prf_invs1 x) (Prf_invs1 y)).
 Qed.

 Lemma Inv_comp_invs2 : Inverses_rel Inv_comp_elt_r Inv_comp_elt_l.
 Proof.
 exact (Eq_abb'a' (Prf_invs2 y) (Prf_invs2 x)).
 Qed.

 Canonical Structure Inverses_comp : Inverses_setoid :=
   Build_Inverses Inv_comp_invs1 Inv_comp_invs2.

 End inverses_comp_def.

Lemma Inverses_congl : Map2_congl_law Inverses_comp.
Proof.
unfold Map2_congl_law in |- *.
intros x y z.
elim x; elim y; elim z; simpl in |- *.
intros a a' p p' a0 a0' p0 p0' a1 a1' p1 p1' H.
unfold Inv_comp_elt_l, Inv_comp_elt_r in |- *; simpl in |- *.
apply (Prf_map2_congl (Mop A) (b1:=a1) (b2:=a0) a); trivial.
Qed.

Lemma Inverses_congr : Map2_congr_law Inverses_comp.
Proof.
unfold Map2_congr_law in |- *; simple induction a1; simple induction a2;
 simpl in |- *.
intros b0 b0' p0 p0' z; elim z.
intros b1 b1' p1 p1' H.
unfold Inv_comp_elt_l, Inv_comp_elt_r in |- *; simpl in |- *.
apply (Prf_map2_congr (Mop A) (a1:=Inv_elt_l0) (a2:=b0) b1); trivial.
Qed.

Definition Inverses_op := Build_Map2 Inverses_congl Inverses_congr.

(* The Monoid of inverse pairs *)

Lemma Mass_Inverses : Monoid_ass Inverses_op.
Proof.
red in |- *.
simple induction x; simple induction y; simple induction z; simpl in |- *;
 intros.
unfold Inverses_comp, Inv_comp_elt_l, Inv_comp_elt_r in |- *; simpl in |- *.
apply (Prf_monoid_ass Inv_elt_l0 Inv_elt_l1 Inv_elt_l2).
Qed.

Lemma Inverses_unit_invs : Inverses_rel (Munit A) (Munit A).
Proof.
apply (Prf_monoid_idl (Munit A)).
Qed.

Canonical Structure Inverses_unit :=
  Build_Inverses Inverses_unit_invs Inverses_unit_invs.

Lemma Midl_Inverses : Monoid_idl Inverses_op Inverses_unit.
Proof.
red in |- *.
simple induction x; simpl in |- *; intros.
unfold Inverses_eq, Inv_comp_elt_l in |- *; simpl in |- *.
apply (Prf_monoid_idl Inv_elt_l0).
Qed.

Lemma Midr_Inverses : Monoid_idr Inverses_op Inverses_unit.
Proof.
red in |- *.
simple induction x; simpl in |- *; intros.
apply (Prf_monoid_idr Inv_elt_l0).
Qed.

Canonical Structure Inverses_Monoid :=
  Build_Monoid Mass_Inverses Midl_Inverses Midr_Inverses.

(* opposite operation *)

Definition Opposite (x : Inverses_setoid) : Inverses_setoid :=
  Build_Inverses (Prf_invs2 x) (Prf_invs1 x).

Lemma Opposite_map_law : Map_law Opposite.
Proof.
red in |- *; intros x y.
elim x; elim y; simpl in |- *; unfold Inverses_eq in |- *; simpl in |- *.
intros a a' aa' a'a b b' bb' b'b ba.
(* *) apply Trans with (b' +_M Munit A).
apply Midr.
(* *) apply Trans with (b' +_M (a +_M a')).
unfold ApMop in |- *; apply Map2_l.
apply Sym; trivial.
(* *) apply Trans with (y := b' +_M a +_M a').
apply Mass.
(* *) apply Trans with (Munit A +_M a').
2: apply Midl.
unfold ApMop in |- *; apply Map2_r.
(* *) apply Trans with (b' +_M b).
2: assumption.
unfold ApMop in |- *; apply Map2_l.
apply Sym; trivial.
Qed.

Canonical Structure Opposite_map := Build_Map Opposite_map_law.

Lemma Inverses_invl : Group_invl Opposite_map.
Proof.
red in |- *; simple induction x; trivial.
Qed.

Lemma Inverses_invr : Group_invr Opposite_map.
Proof.
red in |- *; simple induction x; trivial.
Qed.

Canonical Structure Inverses_group := Build_Group Inverses_invl Inverses_invr.

End inv_def.
