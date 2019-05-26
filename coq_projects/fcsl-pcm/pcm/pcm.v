(*
Copyright 2013 IMDEA Software Institute
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

(******************************************************************************)
(* This file defines pcm -- a type equipped with partial commutative          *)
(* monoid structure, several subclasses of PCMs, and important                *)
(* concrete instances.                                                        *)
(******************************************************************************)

From Coq Require Import ssreflect ssrbool ssrfun.
From mathcomp Require Import ssrnat bigop.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Delimit Scope pcm_scope with pcm.
Open Scope pcm_scope.

(*******************************)
(* Partial Commutative Monoids *)
(*******************************)

Module PCM.

Record mixin_of (T : Type) := Mixin {
    valid_op : T -> bool;
    join_op : T -> T -> T;
    unit_op : T;
    _ : commutative join_op;
    _ : associative join_op;
    _ : left_id unit_op join_op;
    (* monotonicity of valid *)
    _ : forall x y, valid_op (join_op x y) -> valid_op x; 
    (* unit is valid *)
    _ : valid_op unit_op}.

Section ClassDef.

Notation class_of := mixin_of (only parsing). 

Structure type : Type := Pack {sort : Type; _ : class_of sort}.
Local Coercion sort : type >-> Sortclass.

Variables (T : Type) (cT : type).
Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.

Definition pack c := @Pack T c.
Definition clone := fun c & cT -> T & phant_id (pack c) cT => pack c. 

Definition valid := valid_op class.
Definition join := join_op class.
Definition unit := unit_op class.

End ClassDef.

Arguments unit [cT].

Module Exports.
Coercion sort : type >-> Sortclass.
Notation pcm := type.
Notation PCMMixin := Mixin.
Notation PCM T m := (@pack T m).

Notation "[ 'pcmMixin' 'of' T ]" := (class _ : mixin_of T)
  (at level 0, format "[ 'pcmMixin'  'of'  T ]") : pcm_scope.
Notation "[ 'pcm' 'of' T 'for' C ]" := (@clone T C _ idfun id)
  (at level 0, format "[ 'pcm'  'of'  T  'for'  C ]") : pcm_scope.
Notation "[ 'pcm' 'of' T ]" := (@clone T _ _ id id)
  (at level 0, format "[ 'pcm'  'of'  T ]") : pcm_scope.

Notation "x \+ y" := (join x y) 
  (at level 43, left associativity) : pcm_scope.
Notation valid := valid.
Notation Unit := unit.

Arguments unit [cT].
Prenex Implicits valid join unit. 

(* Restating the laws, with the notation. *) 
(* Plus some additional derived lemmas.   *)

Section Laws.
Variable U V : pcm.

Lemma joinC (x y : U) : x \+ y = y \+ x.
Proof. by case: U x y=>tp [v j z Cj *]; apply: Cj. Qed.

Lemma joinA (x y z : U) : x \+ (y \+ z) = x \+ y \+ z.
Proof. by case: U x y z=>tp [v j z Cj Aj *]; apply: Aj. Qed.

Lemma joinAC (x y z : U) : x \+ y \+ z = x \+ z \+ y.
Proof. by rewrite -joinA (joinC y) joinA. Qed.

Lemma joinCA (x y z : U) : x \+ (y \+ z) = y \+ (x \+ z).
Proof. by rewrite joinA (joinC x) -joinA. Qed.

Lemma validL (x y : U) : valid (x \+ y) -> valid x.
Proof. case: U x y=>tp [v j z Cj Aj Uj /= Mj inv f ?]; apply: Mj. Qed.

Lemma validR (x y : U) : valid (x \+ y) -> valid y.
Proof. by rewrite joinC; apply: validL. Qed.

Lemma validE (x y : U) : valid (x \+ y) -> valid x * valid y.
Proof. by move=>X; rewrite (validL X) (validR X). Qed.

Lemma unitL (x : U) : Unit \+ x = x.
Proof. by case: U x=>tp [v j z Cj Aj Uj *]; apply: Uj. Qed.

Lemma unitR (x : U) : x \+ Unit = x.
Proof. by rewrite joinC unitL. Qed.

Lemma valid_unit : valid (@Unit U).
Proof. by case: U=>tp [v j z Cj Aj Uj Vm Vu *]. Qed.

(* some helper lemmas for easier extraction of validity claims *)
Lemma validAR (x y z : U) : valid (x \+ y \+ z) -> valid (y \+ z).
Proof. by rewrite -joinA; apply: validR. Qed.

Lemma validAL (x y z : U) : valid (x \+ (y \+ z)) -> valid (x \+ y).
Proof. by rewrite joinA; apply: validL. Qed.

End Laws.

Hint Resolve valid_unit : core.

Section UnfoldingRules.
Variable U : pcm.

Lemma pcm_joinE (x y : U) : x \+ y = join_op (class U) x y.
Proof. by []. Qed.

Lemma pcm_validE (x : U) : valid x = valid_op (class U) x.
Proof. by []. Qed.

Lemma pcm_unitE : unit = unit_op (class U).
Proof. by []. Qed.

Definition pcmE := (pcm_joinE, pcm_validE, pcm_unitE).

(* also a simple rearrangment equation *)
Definition pull (x y : U) := (joinC y x, joinCA y x).

End UnfoldingRules. 

End Exports.

End PCM.

Export PCM.Exports.

(*********************)
(* Cancellative PCMs *)
(*********************)

(* definition of precision for an arbitrary PCM U *)

Definition precise (U : pcm) (P : U -> Prop) := 
  forall s1 s2 t1 t2, 
    valid (s1 \+ t1) -> P s1 -> P s2 -> 
    s1 \+ t1 = s2 \+ t2 -> s1 = s2.

Module CancellativePCM.

Variant mixin_of (U : pcm) := Mixin of 
  forall x1 x2 x : U, valid (x1 \+ x) -> x1 \+ x = x2 \+ x -> x1 = x2.

Section ClassDef.

Record class_of (U : Type) := Class {
  base : PCM.mixin_of U; 
  mixin : mixin_of (PCM.Pack base)}.

Local Coercion base : class_of >-> PCM.mixin_of.

Structure type : Type := Pack {sort : Type; _ : class_of sort}.
Local Coercion sort : type >-> Sortclass.

Variables (T : Type) (cT : type).
Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.
Definition clone c of phant_id class c := @Pack T c.

(* produce a cancellative type out of the mixin *)
(* equalize m0 and m by means of a phantom *)
Definition pack b0 (m0 : mixin_of (PCM.Pack b0)) := 
  fun m & phant_id m0 m => Pack (@Class T b0 m).

Definition pcm := PCM.Pack class. 

End ClassDef.

Module Exports.
Coercion base : class_of >-> PCM.mixin_of.
Coercion sort : type >-> Sortclass.
Coercion pcm : type >-> PCM.type.
Canonical Structure pcm.

Notation cpcm := type.
Notation CPCMMixin := Mixin.
Notation CPCM T m := (@pack T _ _ m id).

Notation "[ 'cpcm' 'of' T 'for' cT ]" := (@clone T cT _ id)
  (at level 0, format "[ 'cpcm'  'of'  T  'for' cT ]") : pcm_scope.
Notation "[ 'cpcm' 'of' T ]" := (@clone T _ _ id)
  (at level 0, format "[ 'cpcm'  'of'  T ]") : pcm_scope.

Section Lemmas.
Variable U : cpcm.

Lemma joinKx (x1 x2 x : U) : valid (x1 \+ x) -> x1 \+ x = x2 \+ x -> x1 = x2. 
Proof. by case: U x1 x2 x=>V [b][K] T; apply: K. Qed.

Lemma joinxK (x x1 x2 : U) : valid (x \+ x1) -> x \+ x1 = x \+ x2 -> x1 = x2. 
Proof. by rewrite !(joinC x); apply: joinKx. Qed.

Lemma cancPL (P : U -> Prop) s1 s2 t1 t2 : 
        precise P -> valid (s1 \+ t1) -> P s1 -> P s2 -> 
        s1 \+ t1 = s2 \+ t2 -> (s1 = s2) * (t1 = t2).
Proof.
move=>H V H1 H2 E; move: (H _ _ _ _ V H1 H2 E)=>X.
by rewrite -X in E *; rewrite (joinxK V E).
Qed.

Lemma cancPR (P : U -> Prop) s1 s2 t1 t2 : 
        precise P -> valid (s1 \+ t1) -> P t1 -> P t2 -> 
        s1 \+ t1 = s2 \+ t2 -> (s1 = s2) * (t1 = t2).
Proof.
move=>H V H1 H2 E. rewrite (joinC s1) (joinC s2) in E V.
by rewrite !(cancPL H V H1 H2 E).
Qed.

End Lemmas.
End Exports.

End CancellativePCM.

Export CancellativePCM.Exports.

(***************)
(* Topped PCMs *)
(***************)

(* PCM with an explicit undef value *)
(* we will want these constants to be decidable *)
(* so we also add unitb, to test if an element is unit *)
(* for undefb, that should be valid, so we don't add anything special *)
(* OTOH, unit should not be decomposable *)

Module TPCM.

Record mixin_of (U : pcm) := Mixin {
  undef_op : U;
  unitb_op : U -> bool;
  _ : forall x, reflect (x = Unit) (unitb_op x);
  (* next one doesn't hold of max PCM, so remove eventually *)
  _ : forall x y : U, x \+ y = Unit -> x = Unit /\ y = Unit;
(* _ : forall x y z : U, valid (x \+ y \+ z) = 
        [&& valid (x \+ y), valid (y \+ z) & valid (x \+ z)]; *)
  _ : ~~ valid undef_op;
  _ : forall x, undef_op \+ x = undef_op}.

Section ClassDef.

Record class_of (U : Type) := Class {
  base : PCM.mixin_of U; 
  mixin : mixin_of (PCM.Pack base)}.

Local Coercion base : class_of >-> PCM.mixin_of.

Structure type : Type := Pack {sort : Type; _ : class_of sort}.
Local Coercion sort : type >-> Sortclass.

Variables (T : Type) (cT : type).
Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.
Definition clone c of phant_id class c := @Pack T c.

(* produce a topped pcm out of the mixin *)
(* equalize m0 and m by means of a phantom *)
Definition pack b0 (m0 : mixin_of (PCM.Pack b0)) := 
  fun m & phant_id m0 m => Pack (@Class T b0 m).

Definition pcm := PCM.Pack class.
Definition unitb := unitb_op (mixin class).
Definition undef : pcm := undef_op (mixin class).

End ClassDef.

Module Exports.
Coercion base : class_of >-> PCM.mixin_of.
Coercion sort : type >-> Sortclass.
Coercion pcm : type >-> PCM.type.
Canonical Structure pcm.
Notation tpcm := type.
Notation TPCMMixin := Mixin.
Notation TPCM T m := (@pack T _ _ m id).

Notation "[ 'tpcm' 'of' T 'for' cT ]" := (@clone T cT _ id)
  (at level 0, format "[ 'tpcm'  'of'  T  'for' cT ]") : pcm_scope.
Notation "[ 'tpcm' 'of' T ]" := (@clone T _ _ id)
  (at level 0, format "[ 'tpcm'  'of'  T ]") : pcm_scope.

Notation undef := undef.
Notation unitb := unitb. 
Arguments undef [cT].
Prenex Implicits undef.

Section Lemmas.
Variable U : tpcm.

Lemma unitbP (x : U) : reflect (x = Unit) (unitb x).
Proof. by case: U x=>V [b][u]. Qed.

Lemma unitbE : unitb (Unit : U).
Proof. by case: unitbP. Qed.

Lemma joinE0 (x y : U) : x \+ y = Unit <-> (x = Unit) * (y = Unit).
Proof. 
case: U x y=>V [b][u1 u2] H1 H2 H3 T x y; split; first by apply: H2. 
by case=>->->; rewrite unitL.
Qed.

Lemma valid_undefN : ~~ valid (@undef U).
Proof. by case: U=>V [b][u]. Qed.

Lemma valid_undef : valid (@undef U) = false. 
Proof. by rewrite (negbTE valid_undefN). Qed.

Lemma undef_join (x : U) : undef \+ x = undef.
Proof. by case: U x=>V [b][u]. Qed.

Lemma join_undef (x : U) : x \+ undef = undef.
Proof. by rewrite joinC undef_join. Qed.

Lemma undef0 : (undef : U) <> (Unit : U).
Proof. by move=>E; move: (@valid_unit U); rewrite -E valid_undef. Qed.

Definition undefE := (undef_join, join_undef, valid_undef). 

End Lemmas.
End Exports.

End TPCM.

Export TPCM.Exports.


(***************************************)
(* Support for big operators over PCMs *)
(***************************************)

Canonical pcm_monoid (U : pcm) := Monoid.Law (@joinA U) (@unitL U) (@unitR U).
Canonical pcm_comoid (U : pcm) := Monoid.ComLaw (@joinC U). 

Section BigPartialMorph.
Variables (R1 : Type) (R2 : pcm) (K : R1 -> R2 -> Type) (f : R2 -> R1).
Variables (id1 : R1) (op1 : R1 -> R1 -> R1).
Hypotheses
  (f_op : forall x y : R2, valid (x \+ y) -> f (x \+ y) = op1 (f x) (f y))
  (f_id : f Unit = id1).

Lemma big_pmorph I r (P : pred I) F :
        valid (\big[PCM.join/Unit]_(i <- r | P i) F i) ->
        f (\big[PCM.join/Unit]_(i <- r | P i) F i) = 
          \big[op1/id1]_(i <- r | P i) f (F i).
Proof. 
rewrite unlock; elim: r=>[|x r IH] //=; case: ifP=>// H V.
by rewrite f_op // IH //; apply: validR V.
Qed.

End BigPartialMorph.


(*********************)
(* PCM constructions *)
(*********************)


(* nats with addition are a pcm *)
Definition natPCMMix := 
  PCMMixin addnC addnA add0n (fun x y => @id true) (erefl _).
Canonical natPCM := Eval hnf in PCM nat natPCMMix.

(* also with multiplication, but we don't make that one canonical *)
Definition multPCMMix := 
  PCMMixin mulnC mulnA mul1n (fun x y => @id true) (erefl _).
Definition multPCM := Eval hnf in PCM nat multPCMMix.

(* with max too *)
Definition maxPCMMix := 
  PCMMixin maxnC maxnA max0n (fun x y => @id true) (erefl _).
Definition maxPCM := Eval hnf in PCM nat maxPCMMix.

(* bools with disjunction are a pcm *)
Definition bool_orPCMMix := 
  PCMMixin orbC orbA orFb (fun x y => @id true) (erefl _).
Definition bool_orPCM := Eval hnf in PCM bool bool_orPCMMix.

(* cartesian product of pcms is a pcm *)

Module ProdPCM.
Section ProdPCM.
Variables (U V : pcm).
Local Notation tp := (U * V)%type.

Definition pvalid := [fun x : tp => valid x.1 && valid x.2].
Definition pjoin := [fun x1 x2 : tp => (x1.1 \+ x2.1, x1.2 \+ x2.2)].
Definition punit : tp := (Unit, Unit).

Lemma joinC x y : pjoin x y = pjoin y x.
Proof. 
move: x y => [x1 x2][y1 y2] /=. 
by rewrite (joinC x1) (joinC x2). 
Qed.

Lemma joinA x y z : pjoin x (pjoin y z) = pjoin (pjoin x y) z.
Proof.
move: x y z => [x1 x2][y1 y2][z1 z2] /=. 
by rewrite (joinA x1) (joinA x2).
Qed.

Lemma validL x y : pvalid (pjoin x y) -> pvalid x.
Proof.
move: x y => [x1 x2][y1 y2] /=. 
by case/andP=>D1 D2; rewrite (validL D1) (validL D2).
Qed.

Lemma unitL x : pjoin punit x = x.
Proof. by case: x=>x1 x2; rewrite /= !unitL. Qed.

Lemma validU : pvalid punit.
Proof. by rewrite /pvalid /= !valid_unit. Qed.

End ProdPCM.
End ProdPCM.

Definition prodPCMMixin U V := 
  PCMMixin (@ProdPCM.joinC U V) (@ProdPCM.joinA U V)
           (@ProdPCM.unitL U V) (@ProdPCM.validL U V) 
           (@ProdPCM.validU U V).
Canonical prodPCM U V := Eval hnf in PCM (_ * _) (@prodPCMMixin U V).

(* product simplification *)

Section Simplification.
Variable U V : pcm.

Lemma pcmPJ (x1 y1 : U) (x2 y2 : V) : 
        (x1, x2) \+ (y1, y2) = (x1 \+ y1, x2 \+ y2).
Proof. by []. Qed.

Lemma pcm_peta (x : prodPCM U V) : x = (x.1, x.2).
Proof. by case: x. Qed.

Lemma pcmPV (x : prodPCM U V) : valid x = valid x.1 && valid x.2.
Proof. by rewrite pcmE. Qed.

Definition pcmPE := (pcmPJ, pcmPV).

End Simplification.

(* product of TPCMs is a TPCM *)
(* With TPCMs we could really remove the pairs *)
(* where one element is valid and the other is not *)
(* But let's not bother now *)

Section ProdTPCM.
Variables (U V : tpcm).

Lemma prod_unitb (x : prodPCM U V) : 
        reflect (x = Unit) (unitb x.1 && unitb x.2).
Proof.
case: x=>x1 x2; case: andP=>/= H; constructor.
- by case: H=>/unitbP -> /unitbP ->. 
by case=>X1 X2; elim: H; rewrite X1 X2 !unitbE.
Qed.

Lemma prod_join0E (x y : prodPCM U V) : x \+ y = Unit -> x = Unit /\ y = Unit.
Proof. by case: x y=>x1 x2 [y1 y2][] /joinE0 [->->] /joinE0 [->->]. Qed.

(*
Lemma prod_valid3 (x y z : prodPCM U V) : valid (x \+ y \+ z) = 
        [&& valid (x \+ y), valid (y \+ z) & valid (x \+ z)].
Proof. 
case: x y z=>x1 x2 [y1 y2][z1 z2]; rewrite pcmE /= !valid3 -!andbA.
by do !bool_congr. 
Qed.
*)

Lemma prod_valid_undef : ~~ valid (@undef U, @undef V).
Proof. by rewrite pcmPV negb_and !valid_undef. Qed.

Lemma prod_undef_join x : (@undef U, @undef V) \+ x = (@undef U, @undef V). 
Proof. by case: x=>x1 x2; rewrite pcmPE !undef_join. Qed.

Definition prodTPCMMix := TPCMMixin prod_unitb prod_join0E 
                                    prod_valid_undef prod_undef_join.
Canonical prodTPCM := Eval hnf in TPCM (U * V) prodTPCMMix.

End ProdTPCM.

(* unit is a pcm; just for kicks *)

Module UnitPCM.
Section UnitPCM.

Definition uvalid (x : unit) := true.
Definition ujoin (x y : unit) := tt.
Definition uunit := tt.

Lemma ujoinC x y : ujoin x y = ujoin y x.
Proof. by []. Qed.

Lemma ujoinA x y z : ujoin x (ujoin y z) = ujoin (ujoin x y) z.
Proof. by []. Qed.

Lemma uvalidL x y : uvalid (ujoin x y) -> uvalid x.
Proof. by []. Qed.

Lemma uunitL x : ujoin uunit x = x.
Proof. by case: x. Qed. 

Lemma uvalidU : uvalid uunit.
Proof. by []. Qed.

End UnitPCM.
End UnitPCM.

Definition unitPCMMixin := 
  PCMMixin UnitPCM.ujoinC UnitPCM.ujoinA 
           UnitPCM.uunitL UnitPCM.uvalidL UnitPCM.uvalidU.
Canonical unitPCM := Eval hnf in PCM unit unitPCMMixin.

(* but it's not a TPCM, as there is no undefined element *)
(* we have to lift for that *)


(* bools with conjunction are a pcm *)

Module BoolConjPCM.
Lemma unitL x : true && x = x. Proof. by []. Qed.
End BoolConjPCM.

Definition boolPCMMixin := PCMMixin andbC andbA BoolConjPCM.unitL
                           (fun x y => @id true) (erefl _).
Canonical boolConjPCM := Eval hnf in PCM bool boolPCMMixin.


(*************************)
(* PCM-induced pre-order *)
(*************************)

Definition pcm_preord (U : pcm) (x y : U) := exists z, y = x \+ z.

Notation "[ 'pcm' x '<=' y ]" := (@pcm_preord _ x y)
  (at level 0, x, y at level 69, 
   format "[ '[hv' 'pcm'  x '/   '  <=  y ']' ]") : type_scope.

Section PleqLemmas.
Variable U : pcm.
Implicit Types x y z : U.

Lemma pleq_unit x : [pcm Unit <= x].
Proof. by exists x; rewrite unitL. Qed.

(* preorder lemmas *)

(* We don't have antisymmetry in general, though for common PCMs *)
(* e.g., union maps, we do have it; but it is proved separately for them *)

Lemma pleq_refl x : [pcm x <= x].
Proof. by exists Unit; rewrite unitR. Qed.

Lemma pleq_trans x y z : [pcm x <= y] -> [pcm y <= z] -> [pcm x <= z].
Proof. by case=>a -> [b ->]; exists (a \+ b); rewrite joinA. Qed.

(* monotonicity lemmas *)

Lemma pleq_join2r x x1 x2 : [pcm x1 <= x2] -> [pcm x1 \+ x <= x2 \+ x].
Proof. by case=>a ->; exists a; rewrite joinAC. Qed.

Lemma pleq_join2l x x1 x2 : [pcm x1 <= x2] -> [pcm x \+ x1 <= x \+ x2].
Proof. by rewrite !(joinC x); apply: pleq_join2r. Qed.

Lemma pleq_joinr x1 x2 : [pcm x1 <= x1 \+ x2].
Proof. by exists x2. Qed.

Lemma pleq_joinl x1 x2 : [pcm x2 <= x1 \+ x2].
Proof. by rewrite joinC; apply: pleq_joinr. Qed.

(* validity lemmas *)

Lemma pleqV (x1 x2 : U) : [pcm x1 <= x2] -> valid x2 -> valid x1.
Proof. by case=>x -> /validL. Qed.

Lemma pleq_validL (x x1 x2 : U) : 
        [pcm x1 <= x2] -> valid (x \+ x2) -> valid (x \+ x1).
Proof. by case=>a ->; rewrite joinA; apply: validL. Qed.

Lemma pleq_validR (x x1 x2 : U) : 
        [pcm x1 <= x2] -> valid (x2 \+ x) -> valid (x1 \+ x).
Proof. by rewrite -!(joinC x); apply: pleq_validL. Qed.

(* the next two lemmas only hold for cancellative PCMs *)

Lemma pleq_joinxK (V : cpcm) (x x1 x2 : V) : 
        valid (x2 \+ x) -> [pcm x1 \+ x <= x2 \+ x] -> [pcm x1 <= x2].
Proof. by move=>W [a]; rewrite joinAC=>/(joinKx W) ->; exists a. Qed.

Lemma pleq_joinKx (V : cpcm) (x x1 x2 : V) : 
        valid (x \+ x2) -> [pcm x \+ x1 <= x \+ x2] -> [pcm x1 <= x2].
Proof. by rewrite !(joinC x); apply: pleq_joinxK. Qed.

End PleqLemmas.

Hint Resolve pleq_unit pleq_refl pleq_joinr pleq_joinl : core.

(*******************)
(* Local functions *)
(*******************)

Definition local (U : pcm) (f : U -> U -> option U) := 
  forall p x y r, valid (x \+ (p \+ y)) -> f x (p \+ y) = Some r -> 
                  valid (r \+ p \+ y) /\ f (x \+ p) y = Some (r \+ p). 

Lemma localV U f x y r : 
        @local U f -> valid (x \+ y) -> f x y = Some r -> valid (r \+ y).
Proof. by move=>H V E; move: (H Unit x y r); rewrite unitL !unitR; case. Qed.

Lemma idL (U : pcm) : @local U (fun x y => Some x).
Proof. by move=>p x y _ V [<-]; rewrite -joinA. Qed.

