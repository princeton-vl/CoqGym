From mathcomp.ssreflect
Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq.
From mathcomp
Require Import path.
Require Import Eqdep.
Require Import Relation_Operators.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


(* We need a custom equality type, as the default one from
   ssreflect breaks constraint solving when defining worlds.

   TODO: figure out, why?
 *)

Module EqualityX.

Definition axiom T (e : rel T) := forall x y, reflect (x = y) (e x y).

Structure mixin_of T := Mixin {op : rel T; _ : axiom op}.
Notation class_of := mixin_of (only parsing).

Section ClassDef.

Structure type := Pack {sort; _ : class_of sort; _ : Type}.
Local Coercion sort : type >-> Sortclass.
Variables (T : Type) (cT : type).

Definition class := let: Pack _ c _ := cT return class_of cT in c.

Definition pack c := @Pack T c T.
Definition clone := fun c & cT -> T & phant_id (pack c) cT => pack c.

End ClassDef.

Module Exports.
Coercion sort : type >-> Sortclass.
Notation eqTypeX := type.
Notation EqMixinX := Mixin.
Notation EqTypeX T m := (@pack T m).
End Exports.

End EqualityX.
Export EqualityX.Exports.

Section EqualityConversion.

Variable U: eqTypeX.
Definition eq_opX T := EqualityX.op (EqualityX.class T).

Lemma eqxP : Equality.axiom (@eq_opX U).
Proof. by case: U=>s[op a ?]; apply: a. Qed.

Canonical eqMixinX := EqMixin eqxP.
Canonical eqTypeX' := EqType U eqMixinX.                                   

End EqualityConversion.

(* Section EqualityConversion2. *)

(* Variable U: eqType. *)
(* Local Definition eq_op T := Equality.op (Equality.class T). *)

(* Lemma eqP' : Equality.axiom (@eq_op U). *)
(* Proof. by case: U=>s[op a ?]; apply: a. Qed. *)

(* Canonical eqMixinX2 := EqMixinX eqP'. *)
(* Canonical eqTypeX2' := EqTypeX U eqMixinX2.                                    *)

(* End EqualityConversion2. *)

