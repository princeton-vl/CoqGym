From Coq Require Import ssreflect ssrbool ssrfun.
From mathcomp Require Import ssrnat eqtype seq path fintype.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Ordered. 

Section RawMixin.

Structure mixin_of (T : eqType) := 
  Mixin {ordering : rel T; 
         _ : irreflexive ordering;
         _ : transitive ordering;
        }.
End RawMixin.

Section ClassDef.

Record class_of (T : Type) := Class {
   base : Equality.class_of T; 
   mixin : mixin_of (Equality.Pack base T)}.

Local Coercion base : class_of >-> Equality.class_of.

Structure type : Type := Pack {sort : Type; _ : class_of sort;}.
Local Coercion sort : type >-> Sortclass.

Variables (T : Type) (cT : type).
Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.

Definition pack b (m0 : mixin_of (EqType T b)) := 
  fun m & phant_id m0 m => Pack (@Class T b m).

Definition eqType := Equality.Pack class cT.

End ClassDef.

Module Exports.
Coercion eqType : type >-> Equality.type.
Canonical Structure eqType.
Notation ordType := Ordered.type.
Definition ord T : rel (sort T) := (ordering (mixin (class T))).
End Exports.
End Ordered.
Export Ordered.Exports.

Definition oleq (T : ordType) (t1 t2 : T) := ord t1 t2 || (t1 == t2).

Prenex Implicits ord oleq.

Section Lemmas.
Variable T : ordType.
Implicit Types x y : T.

Variable trans : transitive (@ord T). 

Lemma otrans : transitive (@oleq T).
Proof.
move=>x y z /=. 
case/orP; last by move/eqP=>->.
rewrite /oleq; move=>T1.
case/orP; first by move/(trans T1)=>->.
by move/eqP=><-; rewrite T1. 
Qed.

End Lemmas.
