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


(*****************************************************************************)
(*          Projet Formel - Calculus of Inductive Constructions V5.10        *)
(*****************************************************************************)
(*									     *)
(*	       Category Parallel Arrowd (used in Equalizers)		     *)
(*									     *)
(*****************************************************************************)
(*									     *)
(*                     A. SAIBI	  May 95                  		     *)
(*									     *)
(*****************************************************************************)


Require Export BasicTypes.
Require Export Category.

Set Implicit Arguments.
Unset Strict Implicit.

Section pa_def.

Variables (C : Category) (a b : C) (I : Type) (k : I -> (a --> b)).

Inductive PA_ob : Type :=
  | PA1 : PA_ob
  | PA2 : PA_ob.

Inductive PA_mor : PA_ob -> PA_ob -> Type :=
  | PA_I1 : PA_mor PA1 PA1
  | PA_I2 : PA_mor PA2 PA2
  | PA_f : I -> PA_mor PA1 PA2.

(* sche'mas d'e'limination pour PA_mor *)

Lemma PA_11_P :
 (PA_mor PA1 PA1 -> Prop) -> forall x y : PA_ob, PA_mor x y -> Prop.
Proof.
intros P x y; elim x; elim y.
exact P.
intro x'; exact True.
intro x'; exact True.
intro x'; exact True.
Defined.

Lemma PA_11_ind :
 forall P : PA_mor PA1 PA1 -> Prop, P PA_I1 -> forall x : PA_mor PA1 PA1, P x.
Proof.
intros P PP1 x.
change (PA_11_P P x) in |- *.
apply (PA_mor_ind (P:=fun (x y : PA_ob) (f : PA_mor x y) => PA_11_P P f));
 simpl in |- *.
exact PP1.
trivial.
trivial.
Qed.

Lemma PA_22_P :
 (PA_mor PA2 PA2 -> Prop) -> forall x y : PA_ob, PA_mor x y -> Prop.
Proof.
intros P x y; elim x; elim y.
intro x'; exact True.
intro x'; exact True.
intro x'; exact True.
exact P.
Defined.

Lemma PA_22_ind :
 forall P : PA_mor PA2 PA2 -> Prop, P PA_I2 -> forall x : PA_mor PA2 PA2, P x.
Proof.
intros P PP2 x.
change (PA_22_P P x) in |- *.
apply (PA_mor_ind (P:=fun (x y : PA_ob) (f : PA_mor x y) => PA_22_P P f));
 simpl in |- *.
trivial.
exact PP2.
trivial.
Qed.

Lemma PA_12_P :
 (PA_mor PA1 PA2 -> Prop) -> forall x y : PA_ob, PA_mor x y -> Prop.
Proof.
intros P x y; elim x; elim y.
intro x'; exact True.
exact P.
intro x'; exact True.
intro x'; exact True.
Defined.

Lemma PA_12_ind :
 forall P : PA_mor PA1 PA2 -> Prop,
 (forall i : I, P (PA_f i)) -> forall x : PA_mor PA1 PA2, P x.
Proof.
intros P Pf x.
change (PA_12_P P x) in |- *.
apply (PA_mor_ind (P:=fun (x y : PA_ob) (f : PA_mor x y) => PA_12_P P f));
 simpl in |- *.
trivial.
trivial.
exact Pf.
Qed.

Lemma PA_21_P :
 (PA_mor PA2 PA1 -> Prop) -> forall x y : PA_ob, PA_mor x y -> Prop.
Proof.
intros P x y; elim x; elim y.
intro x'; exact True.
intro x'; exact True.
exact P.
intro x'; exact True.
Defined.

Lemma PA_21_ind :
 forall (P : PA_mor PA2 PA1 -> Prop) (x : PA_mor PA2 PA1), P x.
Proof.
intros P x.
change (PA_21_P P x) in |- *.
apply (PA_mor_ind (P:=fun (x y : PA_ob) (f : PA_mor x y) => PA_21_P P f));
 simpl in |- *; auto.
Qed.

Lemma PA_21_T :
 (PA_mor PA2 PA1 -> Type) -> forall x y : PA_ob, PA_mor x y -> Type.
Proof.
intros P x y; elim x; elim y.
intro x'; exact UnitType.
intro x'; exact UnitType.
exact P.
intro x'; exact UnitType.
Defined.

Lemma PA_21_rect :
 forall (P : PA_mor PA2 PA1 -> Type) (x : PA_mor PA2 PA1), P x.
Proof.
intros P x.
change (PA_21_T P x) in |- *.
apply (PA_mor_rect (P:=fun (x y : PA_ob) (f : PA_mor x y) => PA_21_T P f));
 simpl in |- *; auto.
Qed.


(* egalite' *)

Definition Equal_PA_mor (x y : PA_ob) (f g : PA_mor x y) :=
  match f in (PA_mor x' y') return Prop with
  | PA_I1 => 
      (* PA_I1  *)  True
      (* PA_I2  *) 
  | PA_I2 => True
      (* PA_f i *) 
  | PA_f i =>
      match g in (PA_mor x' y') return Prop with
      | PA_I1 => 
          (* PA_I1  *)  False
          (* PA_I2  *) 
      | PA_I2 => False
          (* PA_f j *) 
      | PA_f j => k i =_S k j
      end
  end.

Lemma Equal_PA_mor_Equiv :
 forall x y : PA_ob, Equivalence (Equal_PA_mor (x:=x) (y:=y)).
Proof.
intros x y; apply Build_Equivalence;
 [ red in |- * | apply Build_Partial_equivalence; red in |- * ].
intro f; elim f.
simpl in |- *; trivial.
simpl in |- *; trivial.
intro i; simpl in |- *; apply Refl.
intros f; elim f.
intros g h e1 e2.
apply (PA_11_ind (P:=fun h : PA_mor PA1 PA1 => Equal_PA_mor PA_I1 h)).
simpl in |- *; trivial.
intros g h e1 e2.
apply (PA_22_ind (P:=fun h : PA_mor PA2 PA2 => Equal_PA_mor PA_I2 h)).
simpl in |- *; trivial.
intros i g h.
lapply
 (PA_12_ind
    (P:=fun x : PA_mor PA1 PA2 =>
        Equal_PA_mor (PA_f i) x ->
        Equal_PA_mor x h -> Equal_PA_mor (PA_f i) h)).
intros H H0 H1; apply (H g H0 H1).
intro j; unfold Equal_PA_mor at 1 in |- *; intro eqij.
lapply
 (PA_12_ind
    (P:=fun x : PA_mor PA1 PA2 =>
        Equal_PA_mor (PA_f j) x -> Equal_PA_mor (PA_f i) x)).
intros H H0; apply (H h H0).
simpl in |- *; intros l eqjl.
(* *) apply Trans with (k j); trivial.
intros f; elim f.
intros g e1.
apply (PA_11_ind (P:=fun g : PA_mor PA1 PA1 => Equal_PA_mor g PA_I1)).
simpl in |- *; trivial.
intros g e1.
apply (PA_22_ind (P:=fun g : PA_mor PA2 PA2 => Equal_PA_mor g PA_I2)).
simpl in |- *; trivial.
intros i g.
lapply
 (PA_12_ind
    (P:=fun g : PA_mor PA1 PA2 =>
        Equal_PA_mor (PA_f i) g -> Equal_PA_mor g (PA_f i))).
intros H H0; apply (H g H0).
intro j; simpl in |- *; intro eqij; apply Sym; trivial.
Qed.

Canonical Structure PA_mor_setoid (x y : PA_ob) :=
  Build_Setoid (Equal_PA_mor_Equiv x y).

(* composition *)

Definition Comp_PA_mor (x y z : PA_ob) (f : PA_mor x y) :=
  match f in (PA_mor p p0) return (PA_mor p0 z -> PA_mor p z) with
  | PA_I1 => 
      (* PA_I1 *) 
      match z as p return (PA_mor PA1 p -> PA_mor PA1 p) with
      | PA1 =>
          (* PA1 *)  fun _ => PA_I1 
                     (* PA2 *) 
      | PA2 => fun g => g
      end
      (* PA_I2 *) 
  | PA_I2 =>
      match z as p return (PA_mor PA2 p -> PA_mor PA2 p) with
      | PA1 =>
          (* PA1 *) 
          fun g => PA_21_rect (fun _ => PA_mor PA2 PA1) g
          (* PA2 *) 
      | PA2 => fun _ => PA_I2
      end
      (* PA_f  *) 
  | PA_f x =>
      match z as p return (I -> PA_mor PA2 p -> PA_mor PA1 p) with
      | PA1 =>
          (* PA1 *) 
          fun _ g => PA_21_rect (fun _ => PA_mor PA1 PA1) g
          (* PA2 *) 
      | PA2 => fun i _ => PA_f i
      end x
  end.
(* *)

(* code complique' pour contourner bug Generalize *)

Lemma Comp_PA_fact1 :
 forall (f : PA_mor PA1 PA1) (x : PA_ob) (g : PA_mor PA1 x),
 Comp_PA_mor f g =_S g.
Proof.
intros f x g;
 apply (PA_11_ind (P:=fun x' : PA_mor PA1 PA1 => Comp_PA_mor x' g =_S g)).
generalize g.
elim x.
simpl in |- *; auto.
intro g1; apply Refl.
Qed.

Lemma Comp_PA_fact2 :
 forall (f : PA_mor PA2 PA2) (x : PA_ob) (g : PA_mor PA2 x),
 Comp_PA_mor f g =_S g.
Proof.
intros f x g;
 apply (PA_22_ind (P:=fun x' : PA_mor PA2 PA2 => Comp_PA_mor x' g =_S g)).
generalize g.
elim x.
intro g1;
 apply
  (PA_21_ind
     (fun x' : PA_mor PA2 PA1 =>
      PA_21_rect (fun _ : PA_mor PA2 PA1 => PA_mor PA2 PA1) g1 =_S g1) g1).
simpl in |- *; auto.
Qed.

Lemma Comp_PA_fact3 :
 forall (i : I) (g : PA_mor PA2 PA2), Comp_PA_mor (PA_f i) g =_S PA_f i.
Proof.
intros i g;
 apply
  (PA_22_ind
     (P:=fun x' : PA_mor PA2 PA2 => Comp_PA_mor (PA_f i) x' =_S PA_f i)).
apply Refl.
Qed.

Lemma Comp_PA_fact4 :
 forall (i : I) (g : PA_mor PA2 PA1) (h : PA_mor PA1 PA1),
 Comp_PA_mor (PA_f i) g =_S h.
Proof.
intros i g h;
 apply
  (PA_21_ind (fun x' : PA_mor PA2 PA1 => Comp_PA_mor (PA_f i) g =_S h) g).
Qed.


(** **)

Lemma Comp_PA_congl : Congl_law Comp_PA_mor.
Proof.
unfold Congl_law in |- *.
intros x y z f g h.
generalize f; generalize g.
elim h; elim z.
(* cas 1*)
(* cas 1.1 *)
simpl in |- *; auto.
(* cas 1.2 *)
simpl in |- *; auto.
(* cas 2 *)
(* cas 2.1 *)
intros f0 g0 H.
apply
 (PA_21_ind
    (fun x : PA_mor PA2 PA1 => Comp_PA_mor PA_I2 g0 =_S Comp_PA_mor PA_I2 f0)
    g0).
(* cas 2.2 *)
simpl in |- *; auto.
(* cas 3 *)
(* cas 3.1 *)
intros i g0 f0 H.
apply
 (PA_21_ind
    (fun x : PA_mor PA2 PA1 =>
     Comp_PA_mor (PA_f i) f0 =_S Comp_PA_mor (PA_f i) g0) f0).
(* cas 3.2 *)
intros i g0 f0 H; apply Refl.
Qed.

Lemma Comp_PA_congr : Congr_law Comp_PA_mor.
Proof.
unfold Congr_law in |- *.
intros x y z f; elim f.
(* cas 1 *)
intro g;
 lapply
  (PA_11_ind
     (P:=fun x' : PA_mor PA1 PA1 =>
         forall h : PA_mor PA1 z,
         PA_I1 =_S x' -> Comp_PA_mor PA_I1 h =_S Comp_PA_mor x' h)).
intros H h H0; apply (H g h H0).
elim z.
(* cas 1.1 *)
simpl in |- *; auto.
(* cas 1.2 *)
intros h H; apply Refl.
(* cas 2 *)
intro g;
 lapply
  (PA_22_ind
     (P:=fun x' : PA_mor PA2 PA2 =>
         forall h : PA_mor PA2 z,
         Equal_PA_mor PA_I2 x' -> Comp_PA_mor PA_I2 h =_S Comp_PA_mor x' h)).
intros H h H0; apply (H g h H0).
elim z.
(* cas 2.1 *)
intros h H;
 apply
  (PA_21_ind
     (fun x' : PA_mor PA2 PA1 => Comp_PA_mor PA_I2 h =_S Comp_PA_mor PA_I2 h)
     h).
(* cas 2.2 *)
simpl in |- *; auto.
(* cas 3 *)
intros i g;
 lapply
  (PA_12_ind
     (P:=fun x' : PA_mor PA1 PA2 =>
         forall h : PA_mor PA2 z,
         Equal_PA_mor (PA_f i) x' ->
         Comp_PA_mor (PA_f i) h =_S Comp_PA_mor x' h)).
intros H h H0; apply (H g h H0).
elim z.
(* cas 3.1 *)
intros j h H;
 apply
  (PA_21_ind
     (fun x' : PA_mor PA2 PA1 =>
      Comp_PA_mor (PA_f i) h =_S Comp_PA_mor (PA_f j) h) h).
(* cas 3.2 *)
intros j h H; simpl in |- *; exact H.
Qed.

(** **)

Definition Comp_PA := Build_Comp Comp_PA_congl Comp_PA_congr.

Lemma Assoc_PA : Assoc_law Comp_PA.
Proof.
unfold Assoc_law in |- *.
intros x y z o4 f; elim f.
(* cas 1 *)
intros g h.
apply Trans with (Comp_PA_mor g h).
apply (Comp_PA_fact1 PA_I1 (Comp_PA_mor g h)).
apply (Comp_PA_congr (f:=g) (g:=Comp_PA_mor PA_I1 g) h).
apply Sym.
apply (Comp_PA_fact1 PA_I1 g).
(* cas 2 *)
intros g h.
apply Trans with (Comp_PA_mor g h).
apply (Comp_PA_fact2 PA_I2 (Comp_PA_mor g h)).
apply (Comp_PA_congr (f:=g) (g:=Comp_PA_mor PA_I2 g) h).
apply Sym.
apply (Comp_PA_fact2 PA_I2 g).
(* cas 3 *) 
intro i; elim z.
intros g h;
 apply
  (PA_21_ind
     (fun x : PA_mor PA2 PA1 =>
      Comp_PA_mor (PA_f i) (Comp_PA_mor g h) =_S
      Comp_PA_mor (Comp_PA_mor (PA_f i) g) h) g).
intros g h; apply Trans with (Comp_PA_mor (PA_f i) h).
apply (Comp_PA_congl (f:=Comp_PA_mor g h) (g:=h) (PA_f i)).
apply (Comp_PA_fact2 g h).
simpl in |- *.
apply (Comp_PA_congr (f:=PA_f i) (g:=Comp_PA_mor (PA_f i) g) h).
apply Sym.
apply (Comp_PA_fact3 i g).
Qed.

Definition Id_PA (x : PA_ob) :=
  match x as x' return (PA_mor x' x') with
  | PA1 => (* PA1 *)  PA_I1 
      (* PA2 *) 
  | PA2 => PA_I2
  end.

Lemma Idl_PA : Idl_law Comp_PA Id_PA.
Proof.
unfold Idl_law in |- *; simpl in |- *.
intros x y; elim x; intro f.
apply (Comp_PA_fact1 PA_I1 f).
apply (Comp_PA_fact2 PA_I2 f).
Qed.

Lemma Idr_PA : Idr_law Comp_PA Id_PA.
Proof.
unfold Idr_law in |- *; simpl in |- *.
intros x y f; elim f.
apply (Comp_PA_fact1 PA_I1 PA_I1).
apply (Comp_PA_fact2 PA_I2 PA_I2).
intro i; apply (Comp_PA_fact3 i PA_I2).
Qed.

Canonical Structure PA := Build_Category Assoc_PA Idl_PA Idr_PA.

End pa_def.