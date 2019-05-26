(*
Copyright 2018 IMDEA Software Institute
Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at
    http://www.apache.org/licenses/LICENSE-2.0
Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
*)

From Coq Require Import ssreflect ssrbool ssrfun.
From mathcomp Require Import ssrnat eqtype.
From fcsl Require Import prelude pcm.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(******************************************************************************)
(* This file contains an implementation of lift type adding an undef element  *)
(* a structure.                                                               *)
(* Lifting turns an unlifted structure into a PCM and preserves equality.     *)
(******************************************************************************)

Module Unlifted.

Record mixin_of (T : Type) := Mixin {
  ounit_op : T;
  ojoin_op : T -> T -> option T;
  ojoinC_op : forall x y, ojoin_op x y = ojoin_op y x;
  ojoinA_op : forall x y z, 
    obind (ojoin_op x) (ojoin_op y z) = obind (ojoin_op^~ z) (ojoin_op x y);
  ounitL_op : forall x, ojoin_op ounit_op x = Some x}.

Section ClassDef.

Notation class_of := mixin_of (only parsing).

Structure type : Type := Pack {sort : Type; _ : class_of sort}.
Local Coercion sort : type >-> Sortclass.

Variables (T : Type) (cT : type).
Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.
Definition pack c := @Pack T c.
Definition clone := fun c & cT -> T & phant_id (pack c) cT => pack c.

Definition ounit := ounit_op class.
Definition ojoin := ojoin_op class.

End ClassDef.

Module Exports.
Coercion sort : type >-> Sortclass.
Notation unlifted := type.
Notation UnliftedMixin := Mixin.
Notation Unlifted T m := (@pack T m).

Notation "[ 'unliftedMixin' 'of' T ]" := (class _ : mixin_of T)
  (at level 0, format "[ 'unliftedMixin'  'of'  T ]") : form_scope.
Notation "[ 'unlifted' 'of' T 'for' C ]" := (@clone T C _ idfun id)
  (at level 0, format "[ 'unlifted'  'of'  T  'for'  C ]") : form_scope.
Notation "[ 'unlifted' 'of' T ]" := (@clone T _ _ id id)
  (at level 0, format "[ 'unlifted'  'of'  T ]") : form_scope.

Notation ounit := ounit. 
Notation ojoin := ojoin.

Arguments ounit [cT].

Lemma ojoinC (U : unlifted) (x y : U) : ojoin x y = ojoin y x.
Proof. by case: U x y=>T [ou oj ojC]. Qed.

Lemma ojoinA (U : unlifted) (x y z : U) : 
        obind (ojoin x) (ojoin y z) = obind (@ojoin U^~ z) (ojoin x y).
Proof. by case: U x y z=>T [ou oj ojC ojA]. Qed.

Lemma ounitL (U : unlifted) (x : U) : ojoin ounit x = Some x.
Proof. by case: U x=>T [ou oj ojC ojA ojL]. Qed.

End Exports.

End Unlifted.

Export Unlifted.Exports.

(**************************************************)
(* Lifting turns an unlifted structure into a PCM *)
(**************************************************)

Inductive lift A := down | up of A.

Module Lift.  
Section Lift.  
Variable A : unlifted. 

Let unit := up (@ounit A).

Let valid := 
  [fun x : lift A => if x is up _ then true else false].

Let join := 
  [fun x y : lift A => 
     if (x, y) is (up v, up w) then 
       if ojoin v w is Some u then up u
       else @down A 
     else @down A].

Lemma joinC (x y : lift A) : join x y = join y x.
Proof. by case: x y=>[|x][|y] //=; rewrite ojoinC. Qed.

Lemma joinA (x y z : lift A) : join x (join y z) = join (join x y) z.
Proof. 
case: x y z =>[|x][|y][|z] //=; first by case: (ojoin x y).
case E1: (ojoin y z)=>[v1|].
- case E2: (ojoin x y)=>[v2|];
  by move: (ojoinA x y z); rewrite E1 E2 /=; move=>->.
case E2: (ojoin x y)=>[v2|] //.
by move: (ojoinA x y z); rewrite E1 E2 /= =><-.
Qed. 

Lemma unitL x : join unit x = x.
Proof. by case: x=>[|x] //=; rewrite ounitL. Qed.

Lemma validL x y : valid (join x y) -> valid x.
Proof. by case: x y=>[|x][|y]. Qed.

Lemma validU : valid unit.
Proof. by []. Qed.

End Lift.

(* Lifting preserves equality types *)
Section LiftEqType.
Variable A : eqType.

Definition lift_eq (u v : lift A) := 
  match u, v with
    up a, up b => a == b
  | down, down => true
  | _, _ => false
  end.

Lemma lift_eqP : Equality.axiom lift_eq.
Proof.
case=>[|x][|y] /=; try by constructor.
by apply: (iffP eqP)=>[->|[]].
Qed.

Definition liftEqMixin := EqMixin LiftEqType.lift_eqP.
Canonical liftEqType := Eval hnf in EqType _ liftEqMixin.

End LiftEqType.

Module Exports.
Arguments down [A].
Arguments up [A].
Canonical liftEqType.

Section Exports.
(* View for pattern-matching lifted pcm's *)

CoInductive lift_spec A (x : lift A) : lift A -> Type := 
| up_spec n of x = up n : lift_spec x (up n)
| undef_spec of x = down : lift_spec x down.

Lemma liftP A (x : lift A) : lift_spec x x.
Proof. by case: x=>[|a]; [apply: undef_spec | apply: up_spec]. Qed.

Variable A : unlifted.

Definition liftPCMMixin := 
  PCMMixin (@Lift.joinC A) (@Lift.joinA A) 
           (@Lift.unitL A) (@Lift.validL A) (@Lift.validU A).
Canonical liftPCM := Eval hnf in PCM (lift A) liftPCMMixin.

Lemma upE (a1 a2 : A) : 
        up a1 \+ up a2 = if ojoin a1 a2 is Some a then up a else down. 
Proof. by []. Qed.

Lemma valid_down : valid (@down A) = false.
Proof. by []. Qed.

Lemma down_join (x : lift A) : down \+ x = down.
Proof. by []. Qed.

Lemma join_down (x : lift A) : x \+ down = down.
Proof. by case: x. Qed.

Definition downE := (down_join, join_undef, valid_down).

CoInductive liftjoin_spec (x y : lift A) : _ -> _ -> _ -> Type := 
| upcase1 n1 n2 of x = up n1 & y = up n2 : 
    liftjoin_spec x y (if ojoin n1 n2 is Some u then up u else down) x y 
| invalid1 of ~~ valid (x \+ y) : liftjoin_spec x y down x y.

Lemma liftPJ (x y : lift A) : liftjoin_spec x y (x \+ y) x y.
Proof. by case: x y=>[|x][|y]; rewrite ?downE; constructor. Qed.

End Exports.
End Exports.
End Lift.

Export Lift.Exports.


Module NatUnlift.

Local Definition ojoin (x y : nat) := Some (x + y).
Local Definition ounit := 0.

Lemma ojoinC x y : ojoin x y = ojoin y x.
Proof. by rewrite /ojoin addnC. Qed.

Lemma ojoinA x y z : 
        obind (ojoin x) (ojoin y z) = obind (ojoin^~ z) (ojoin x y).
Proof. by rewrite /obind/ojoin /= addnA. Qed.

Lemma ounitL x : ojoin ounit x = Some x.
Proof. by case: x. Qed.

End NatUnlift.

Definition natUnliftedMix := 
  UnliftedMixin NatUnlift.ojoinC NatUnlift.ojoinA NatUnlift.ounitL.
Canonical natUnlifted := Eval hnf in Unlifted nat natUnliftedMix.

(* some lemmas for lifted nats *)

Lemma nxV (m1 m2 : lift natUnlifted) : 
        valid (m1 \+ m2) -> exists n1 n2, m1 = up n1 /\ m2 = up n2.
Proof. by case: m1=>// n1; case: m2=>// n2; exists n1, n2. Qed.


Lemma nxE0 (n1 n2 : lift natUnlifted) : 
        n1 \+ n2 = up 0 -> (n1 = up 0) * (n2 = up 0).
Proof.
case: n1 n2=>[|n1][|n2] //; rewrite upE /ojoin /=. 
by case=>/eqP; rewrite addn_eq0=>/andP [/eqP -> /eqP ->].
Qed.
