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
(*	         Category .->.<-. (used for Pullbacks)     		     *)
(*									     *)
(*****************************************************************************)
(*									     *)
(*                     A. SAIBI	  May 95                  		     *)
(*									     *)
(*****************************************************************************)


Require Export Category.
Require Export BasicTypes.

Set Implicit Arguments.
Unset Strict Implicit.

Inductive PULB_ob : Type :=
  | P1 : PULB_ob
  | P2 : PULB_ob
  | P3 : PULB_ob.

Inductive PULB_mor : PULB_ob -> PULB_ob -> Type :=
  | IP1 : PULB_mor P1 P1
  | IP2 : PULB_mor P2 P2
  | IP3 : PULB_mor P3 P3
  | F12 : PULB_mor P1 P2
  | F32 : PULB_mor P3 P2.

(* *)

Lemma PULB_11_P :
 (PULB_mor P1 P1 -> Prop) -> forall a b : PULB_ob, PULB_mor a b -> Prop.
Proof.
intros P a b; elim a; elim b.
exact P.
intro x; exact True.
intro x; exact True.
intro x; exact True.
intro x; exact True.
intro x; exact True.
intro x; exact True.
intro x; exact True.
intro x; exact True.
Defined.

Lemma PULB_11_ind :
 forall P : PULB_mor P1 P1 -> Prop, P IP1 -> forall x : PULB_mor P1 P1, P x.
Proof.
intros P Pi1 x.
change (PULB_11_P P x) in |- *.
apply
 (PULB_mor_ind (P:=fun (a b : PULB_ob) (f : PULB_mor a b) => PULB_11_P P f));
 simpl in |- *.
exact Pi1.
trivial.
trivial.
trivial.
trivial.
Qed.

Lemma PULB_22_P :
 (PULB_mor P2 P2 -> Prop) -> forall a b : PULB_ob, PULB_mor a b -> Prop.
Proof.
intros P a b; elim a; elim b.
intro x; exact True.
intro x; exact True.
intro x; exact True.
intro x; exact True.
exact P.
intro x; exact True.
intro x; exact True.
intro x; exact True.
intro x; exact True.
Defined.

Lemma PULB_22_ind :
 forall P : PULB_mor P2 P2 -> Prop, P IP2 -> forall x : PULB_mor P2 P2, P x.
Proof.
intros P Pi1 x.
change (PULB_22_P P x) in |- *.
apply
 (PULB_mor_ind (P:=fun (a b : PULB_ob) (f : PULB_mor a b) => PULB_22_P P f));
 simpl in |- *.
trivial.
exact Pi1.
trivial.
trivial.
trivial.
Qed.

Lemma PULB_33_P :
 (PULB_mor P3 P3 -> Prop) -> forall a b : PULB_ob, PULB_mor a b -> Prop.
Proof.
intros P a b; elim a; elim b.
intro x; exact True.
intro x; exact True.
intro x; exact True.
intro x; exact True.
intro x; exact True.
intro x; exact True.
intro x; exact True.
intro x; exact True.
exact P.
Defined.

Lemma PULB_33_ind :
 forall P : PULB_mor P3 P3 -> Prop, P IP3 -> forall x : PULB_mor P3 P3, P x.
Proof.
intros P Pi1 x.
change (PULB_33_P P x) in |- *.
apply
 (PULB_mor_ind (P:=fun (a b : PULB_ob) (f : PULB_mor a b) => PULB_33_P P f));
 simpl in |- *.
trivial.
trivial.
exact Pi1.
trivial.
trivial.
Qed.

Lemma PULB_12_P :
 (PULB_mor P1 P2 -> Prop) -> forall a b : PULB_ob, PULB_mor a b -> Prop.
Proof.
intros P a b; elim a; elim b.
intro x; exact True.
exact P.
intro x; exact True.
intro x; exact True.
intro x; exact True.
intro x; exact True.
intro x; exact True.
intro x; exact True.
intro x; exact True.
Defined.

Lemma PULB_12_ind :
 forall P : PULB_mor P1 P2 -> Prop, P F12 -> forall x : PULB_mor P1 P2, P x.
Proof.
intros P Pi1 x.
change (PULB_12_P P x) in |- *.
apply
 (PULB_mor_ind (P:=fun (a b : PULB_ob) (f : PULB_mor a b) => PULB_12_P P f));
 simpl in |- *.
trivial.
trivial.
trivial.
exact Pi1.
trivial.
Qed.

Lemma PULB_32_P :
 (PULB_mor P3 P2 -> Prop) -> forall a b : PULB_ob, PULB_mor a b -> Prop.
Proof.
intros P a b; elim a; elim b.
intro x; exact True.
intro x; exact True.
intro x; exact True.
intro x; exact True.
intro x; exact True.
intro x; exact True.
intro x; exact True.
exact P.
intro x; exact True.
Defined.

Lemma PULB_32_ind :
 forall P : PULB_mor P3 P2 -> Prop, P F32 -> forall x : PULB_mor P3 P2, P x.
Proof.
intros P Pi1 x.
change (PULB_32_P P x) in |- *.
apply
 (PULB_mor_ind (P:=fun (a b : PULB_ob) (f : PULB_mor a b) => PULB_32_P P f));
 simpl in |- *.
trivial.
trivial.
trivial.
trivial.
exact Pi1.
Qed.

Lemma PULB_21_P :
 (PULB_mor P2 P1 -> Prop) -> forall a b : PULB_ob, PULB_mor a b -> Prop.
Proof.
intros P a b; elim a; elim b.
intro x; exact True.
intro x; exact True.
intro x; exact True.
exact P.
intro x; exact True.
intro x; exact True.
intro x; exact True.
intro x; exact True.
intro x; exact True.
Defined.

Lemma PULB_21_ind :
 forall (P : PULB_mor P2 P1 -> Prop) (x : PULB_mor P2 P1), P x.
Proof.
intros P x.
change (PULB_21_P P x) in |- *.
apply
 (PULB_mor_ind (P:=fun (a b : PULB_ob) (f : PULB_mor a b) => PULB_21_P P f));
 simpl in |- *; auto.
Qed.

Lemma PULB_21_T :
 (PULB_mor P2 P1 -> Type) -> forall a b : PULB_ob, PULB_mor a b -> Type.
Proof.
intros P a b; elim a; elim b.
intro x; exact UnitType.
intro x; exact UnitType.
intro x; exact UnitType.
exact P.
intro x; exact UnitType.
intro x; exact UnitType.
intro x; exact UnitType.
intro x; exact UnitType.
intro x; exact UnitType.
Defined.

Lemma PULB_21_rect :
 forall (P : PULB_mor P2 P1 -> Type) (x : PULB_mor P2 P1), P x.
Proof.
intros P x.
change (PULB_21_T P x) in |- *.
apply
 (PULB_mor_rect (P:=fun (a b : PULB_ob) (f : PULB_mor a b) => PULB_21_T P f));
 simpl in |- *; auto.
Qed.

Lemma PULB_31_P :
 (PULB_mor P3 P1 -> Prop) -> forall a b : PULB_ob, PULB_mor a b -> Prop.
Proof.
intros P a b; elim a; elim b.
intro x; exact True.
intro x; exact True.
intro x; exact True.
intro x; exact True.
intro x; exact True.
intro x; exact True.
exact P.
intro x; exact True.
intro x; exact True.
Defined.

Lemma PULB_31_ind :
 forall (P : PULB_mor P3 P1 -> Prop) (x : PULB_mor P3 P1), P x.
Proof.
intros P x.
change (PULB_31_P P x) in |- *.
apply
 (PULB_mor_ind (P:=fun (a b : PULB_ob) (f : PULB_mor a b) => PULB_31_P P f));
 simpl in |- *; auto.
Qed.

Lemma PULB_31_T :
 (PULB_mor P3 P1 -> Type) -> forall a b : PULB_ob, PULB_mor a b -> Type.
Proof.
intros P a b; elim a; elim b.
intro x; exact UnitType.
intro x; exact UnitType.
intro x; exact UnitType.
intro x; exact UnitType.
intro x; exact UnitType.
intro x; exact UnitType.
exact P.
intro x; exact UnitType.
intro x; exact UnitType.
Defined.

Lemma PULB_31_rect :
 forall (P : PULB_mor P3 P1 -> Type) (x : PULB_mor P3 P1), P x.
Proof.
intros P x.
change (PULB_31_T P x) in |- *.
apply
 (PULB_mor_rect (P:=fun (a b : PULB_ob) (f : PULB_mor a b) => PULB_31_T P f));
 simpl in |- *; auto.
Qed.

Lemma PULB_13_P :
 (PULB_mor P1 P3 -> Prop) -> forall a b : PULB_ob, PULB_mor a b -> Prop.
Proof.
intros P a b; elim a; elim b.
intro x; exact True.
intro x; exact True.
exact P.
intro x; exact True.
intro x; exact True.
intro x; exact True.
intro x; exact True.
intro x; exact True.
intro x; exact True.
Defined.

Lemma PULB_13_ind :
 forall (P : PULB_mor P1 P3 -> Prop) (x : PULB_mor P1 P3), P x.
Proof.
intros P x.
change (PULB_13_P P x) in |- *.
apply
 (PULB_mor_ind (P:=fun (a b : PULB_ob) (f : PULB_mor a b) => PULB_13_P P f));
 simpl in |- *; auto.
Qed.

Lemma PULB_13_T :
 (PULB_mor P1 P3 -> Type) -> forall a b : PULB_ob, PULB_mor a b -> Type.
Proof.
intros P a b; elim a; elim b.
intro x; exact UnitType.
intro x; exact UnitType.
exact P.
intro x; exact UnitType.
intro x; exact UnitType.
intro x; exact UnitType.
intro x; exact UnitType.
intro x; exact UnitType.
intro x; exact UnitType.
Defined.

Lemma PULB_13_rect :
 forall (P : PULB_mor P1 P3 -> Type) (x : PULB_mor P1 P3), P x.
Proof.
intros P x.
change (PULB_13_T P x) in |- *.
apply
 (PULB_mor_rect (P:=fun (a b : PULB_ob) (f : PULB_mor a b) => PULB_13_T P f));
 simpl in |- *; auto.
Qed.

Lemma PULB_23_P :
 (PULB_mor P2 P3 -> Prop) -> forall a b : PULB_ob, PULB_mor a b -> Prop.
Proof.
intros P a b; elim a; elim b.
intro x; exact True.
intro x; exact True.
intro x; exact True.
intro x; exact True.
intro x; exact True.
exact P.
intro x; exact True.
intro x; exact True.
intro x; exact True.
Defined.

Lemma PULB_23_ind :
 forall (P : PULB_mor P2 P3 -> Prop) (x : PULB_mor P2 P3), P x.
Proof.
intros P x.
change (PULB_23_P P x) in |- *.
apply
 (PULB_mor_ind (P:=fun (a b : PULB_ob) (f : PULB_mor a b) => PULB_23_P P f));
 simpl in |- *; auto.
Qed.

Lemma PULB_23_T :
 (PULB_mor P2 P3 -> Type) -> forall a b : PULB_ob, PULB_mor a b -> Type.
Proof.
intros P a b; elim a; elim b.
intro x; exact UnitType.
intro x; exact UnitType.
intro x; exact UnitType.
intro x; exact UnitType.
intro x; exact UnitType.
exact P.
intro x; exact UnitType.
intro x; exact UnitType.
intro x; exact UnitType.
Defined.

Lemma PULB_23_rect :
 forall (P : PULB_mor P2 P3 -> Type) (x : PULB_mor P2 P3), P x.
Proof.
intros P x.
change (PULB_23_T P x) in |- *.
apply
 (PULB_mor_rect (P:=fun (a b : PULB_ob) (f : PULB_mor a b) => PULB_23_T P f));
 simpl in |- *; auto.
Qed.

(* equlaity *)

 Section pulb_setoid_def.

 Variable a b : PULB_ob.

 Definition Equal_PULB_mor (f g : PULB_mor a b) := True.
 
 Lemma Equal_PULB_mor_equiv : Equivalence Equal_PULB_mor.
 Proof.
 apply Build_Equivalence; [ trivial | apply Build_Partial_equivalence ];
  red in |- *; unfold Equal_PULB_mor in |- *; simpl in |- *; 
  auto.
 Qed.
 
 Canonical Structure PULB_mor_setoid := Build_Setoid Equal_PULB_mor_equiv.

 End pulb_setoid_def.

(* composition *)

Definition Comp_PULB_mor (a b c : PULB_ob) (f : PULB_mor_setoid a b) :=
  match
    f in (PULB_mor p p0) return (PULB_mor_setoid p0 c -> PULB_mor_setoid p c)
  with
  | IP1 => 
      (* IP1 *) 
      match c as p return (PULB_mor P1 p -> PULB_mor P1 p) with
      | P1 =>
          (* P1 *)  fun _ => IP1 
                    (* P2 *) 
      | P2 => fun _ => F12
              (* P3 *) 
      | P3 =>
          fun g => PULB_13_rect (fun _ : PULB_mor P1 P3 => PULB_mor P1 P3) g
      end
      (* IP1 *) 
  | IP2 =>
      match c as p return (PULB_mor P2 p -> PULB_mor P2 p) with
      | P1 => 
          (* P1 *) 
          fun g =>
          PULB_21_rect (fun _ : PULB_mor P2 P1 => PULB_mor P2 P1) g
          (* P2 *) 
      | P2 => fun _ => IP2
              (* P3 *) 
      | P3 =>
          fun g => PULB_23_rect (fun _ : PULB_mor P2 P3 => PULB_mor P2 P3) g
      end
      (* IP3 *) 
  | IP3 =>
      match c as p return (PULB_mor P3 p -> PULB_mor P3 p) with
      | P1 =>
          (* P1 *) 
          fun g =>
          PULB_31_rect (fun _ : PULB_mor P3 P1 => PULB_mor P3 P1) g 
          (* P2 *) 
      | P2 => fun _ => F32
              (* P3 *) 
      | P3 => fun _ => IP3
      end
      (* F12  *) 
  | F12 =>
      match c as p return (PULB_mor P2 p -> PULB_mor P1 p) with
      | P1 =>
          (* P1 *) 
          fun g =>
          PULB_21_rect (fun _ : PULB_mor P2 P1 => PULB_mor P1 P1) g
          (* P2 *) 
      | P2 => fun _ => F12
              (* P3 *) 
      | P3 =>
          fun g => PULB_23_rect (fun _ : PULB_mor P2 P3 => PULB_mor P1 P3) g
      end
      (* F32  *) 
  | F32 =>
      match c as p return (PULB_mor P2 p -> PULB_mor P3 p) with
      | P1 =>
          (* P1 *) 
          fun g =>
          PULB_21_rect (fun _ : PULB_mor P2 P1 => PULB_mor P3 P1) g
          (* P2 *) 
      | P2 => fun _ => F32
              (* P3 *) 
      | P3 =>
          fun g => PULB_23_rect (fun _ : PULB_mor P2 P3 => PULB_mor P3 P3) g
      end
  end.

Lemma Comp_PULB_congl : Congl_law Comp_PULB_mor.
Proof.
unfold Congl_law, Equal_PULB_mor in |- *; simpl in |- *; auto.
Qed.

Lemma Comp_PULB_congr : Congr_law Comp_PULB_mor.
Proof.
unfold Congr_law, Equal_PULB_mor in |- *; simpl in |- *; auto.
Qed.
 
Definition Comp_PULB := Build_Comp Comp_PULB_congl Comp_PULB_congr.

Lemma Assoc_PULB : Assoc_law Comp_PULB.
Proof.
unfold Assoc_law in |- *; simpl in |- *; unfold Equal_PULB_mor in |- *;
 simpl in |- *; auto.
Qed.

(* Id *)

Definition Id_PULB (a : PULB_ob) :=
  match a as a' return (PULB_mor a' a') with
  | P1 => (* P1 *)  IP1 
      (* P2 *) 
  | P2 => IP2 
      (* P3 *) 
  | P3 => IP3
  end.

Lemma Idl_PULB : Idl_law Comp_PULB Id_PULB.
Proof.
unfold Idl_law in |- *; simpl in |- *; unfold Equal_PULB_mor in |- *;
 simpl in |- *; auto.
Qed.

Lemma Idr_PULB : Idr_law Comp_PULB Id_PULB.
Proof.
unfold Idr_law in |- *; simpl in |- *; unfold Equal_PULB_mor in |- *;
 simpl in |- *; auto.
Qed.
 
(* Bug ds trad *)

Canonical Structure PULB := Build_Category Assoc_PULB Idl_PULB Idr_PULB.
