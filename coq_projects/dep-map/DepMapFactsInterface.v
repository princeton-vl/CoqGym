(** DepMap: Maps with explicit domain contained in their type *)
Require Import Utf8.
Require Import Orders.
Require Import Coqlib.
Require Import DepMapInterface.


Set Implicit Arguments.


(************************************************************)
(** **  Derived properties on DepMap from their interface  **)
(************************************************************)

Module Type DepMapFacts (X : OrderedType).

Include DepMap(X).

(** ***  Comparisons of dependent maps  **)

Definition eq {A : Type} {dom₁ dom₂} (m₁ : t A dom₁) (m₂ : t A dom₂) := forall x, find x m₁ = find x m₂.
Definition incl {A : Type} {dom₁ dom₂} (m₁ : t A dom₁) (m₂ : t A dom₂) :=
  forall x v, find x m₁ = Some v -> find x m₂ = Some v.

Declare Instance eq_refl : forall A dom, Reflexive (@eq A dom dom).
Parameter eq_sym : forall A dom₁ dom₂ (m₁ : t A dom₁) (m₂ : t A dom₂), eq m₁ m₂ -> eq m₂ m₁.
Parameter eq_trans : forall A dom₁ dom₂ dom3 (m₁ : t A dom₁) (m₂ : t A dom₂) (m3 : t A dom3),
  eq m₁ m₂ -> eq m₂ m3 -> eq m₁ m3.
Declare Instance eq_equiv : forall A dom, Equivalence (@eq A dom dom).

Declare Instance incl_refl : forall A dom (m : t A dom), Reflexive (@incl A dom dom).
Parameter incl_trans : forall A dom₁ dom₂ dom3 (m₁ : t A dom₁) (m₂ : t A dom₂) (m3 : t A dom3),
  incl m₁ m₂ -> incl m₂ m3 -> incl m₁ m3.
Declare Instance incl_preorder : forall A dom, PreOrder (@incl A dom dom).
Declare Instance eq_incl_compat : forall A dom, PartialOrder (@eq A dom dom) (@incl A dom dom).

(** ***  Compatibility Instances  **)

Declare Instance mem_compat (A : Type) dom : Proper (X.eq ==> @eq A dom dom ==> Logic.eq) (@mem A dom).
Parameter find_compat : forall A x y dom₁ dom₂ (m₁ : t A dom₁) (m₂ : t A dom₂),
  X.eq x y -> eq m₁ m₂ -> find x m₁ = find y m₂.
Declare Instance find_compat2 (A : Type) dom : Proper (X.eq ==> @eq A dom dom ==> Logic.eq) (@find A dom).

Arguments set {A} {dom} x v m _.
Parameter set_compat :
  forall A x y v dom₁ dom₂ (m₁ : t A dom₁) (m₂ : t A dom₂) (Hin₁ : Dom.In x dom₁) (Hin₂ : Dom.In y dom₂),
  X.eq x y -> eq m₁ m₂ -> eq (set x v m₁ Hin₁) (set y v m₂ Hin₂).
Declare Instance set_compat2 (A : Type) x dom :
  Proper (Logic.eq ==> @eq A dom dom ==> full_relation ==> @eq A dom dom) (@set A dom x).

Parameter add_compat : forall A x y v dom₁ dom₂ (m₁ : t A dom₁) (m₂ : t A dom₂),
  X.eq x y -> eq m₁ m₂ -> eq (add x v m₁) (add y v m₂).
Declare Instance add_compat2 (A : Type) x dom :
  Proper (Logic.eq ==> @eq A dom dom ==> @eq A (Dom.add x dom) (Dom.add x dom)) (@add A dom x).

Parameter remove_compat : forall A x y dom₁ dom₂ (m₁ : t A dom₁) (m₂ : t A dom₂),
  X.eq x y -> eq m₁ m₂ -> eq (remove x m₁) (remove y m₂).
Declare Instance remove_compat2 (A : Type) x dom :
  Proper (@eq A dom dom ==> @eq A (Dom.remove x dom) (Dom.remove x dom)) (@remove A dom x).

(** ***  Simplification theorems  **)

Parameter find_None : forall A dom x (m : t A dom), find x m = None <-> ¬Dom.In x dom.
Parameter find_dom : forall A x v dom (m : t A dom), find x m = Some v -> Dom.In x dom.

Parameter set_Some : forall A x y v u dom (m : t A dom) (Hin : Dom.In x dom),
  find y (set x v m Hin) = Some u <-> X.eq y x ∧ u = v ∨ ¬X.eq y x ∧ find y m = Some u.
Parameter set_None : forall A x y v dom (m : t A dom) (Hin : Dom.In x dom),
  find y (set x v m Hin) = None <-> ¬X.eq y x ∧ find y m = None.

Parameter add_Some : forall A x y v u dom (m : t A dom),
  find y (add x v m) = Some u <-> X.eq y x ∧ u = v ∨ ¬X.eq y x ∧ find y m = Some u.
Parameter add_None : forall A x y v dom (m : t A dom),
  find y (add x v m) = None <-> ¬X.eq y x ∧ find y m = None.

Parameter remove_Some : forall A x y u dom (m : t A dom),
  find y (remove x m) = Some u <-> ¬X.eq y x ∧ find y m = Some u.
Parameter remove_None : forall A x y dom (m : t A dom),
  find y (remove x m) = None <-> X.eq y x ∨ find y m = None.

Parameter add_cancel : forall A x v dom (m : t A dom), find x m = Some v -> eq (add x v m) m.
Parameter remove_cancel : forall A x dom (m : t A dom), find x m = None -> eq (remove x m) m.

Parameter add_merge : forall A x v₁ v₂ dom (m : t A dom), eq (add x v₂ (add x v₁ m)) (add x v₂ m).
Parameter add_comm : forall A x y v₁ v₂ dom (m : t A dom),
  ¬X.eq x y -> eq (add y v₂ (add x v₁ m)) (add x v₁ (add y v₂ m)).

Parameter remove_add_cancel : forall A s v dom (m : t A dom), eq (remove s (add s v m)) (remove s m).

Parameter map_None : forall A B (f : A -> B) dom (m : t A dom) x, find x (map f m) = None <-> ¬Dom.In x dom.

Parameter combine_None : forall A B C (f : A -> B -> C) g₁ g₂ dom₁ dom₂ (m₁ : t A dom₁) (m₂ : t B dom₂) x,
  find x (combine f g₁ g₂ m₁ m₂) = None <-> find x m₁ = None ∧ find x m₂ = None.

Parameter add_incl : forall A x v dom (m : t A dom), ¬Dom.In x dom -> incl m (add x v m).
Parameter remove_incl : forall A x dom (m : t A dom), incl (remove x m) m.

Parameter cast_spec : forall A dom₁ dom₂ (Heq : Dom.eq dom₁ dom₂) (m : t A dom₁), eq (cast Heq m) m.

Parameter eq_dom : forall A dom₁ dom₂ (m₁ : t A dom₁) (m₂ : t A dom₂), eq m₁ m₂ -> Dom.eq dom₁ dom₂.

(** *** Additional operations and their specification **)

Parameter for_all : forall {A}, (key -> A -> bool) -> forall {dom}, t A dom -> bool.
(** [for_all f m] returns [true] iff all bindings (x, v) in [m] satisfy [f x v]. **)

Parameter for_all_spec : forall A f, Proper (X.eq ==> Logic.eq ==> Logic.eq) f -> forall dom (m : t A dom),
  for_all f m = true <-> forall x v, find x m = Some v -> f x v = true.

Parameter exists_ : forall {A}, (key -> A -> bool) -> forall {dom}, t A dom -> bool.
(** [exists_ f m] returns [true] iff at least one bindings (x, v) in [m] satisfy [f x v]. **)

Parameter exists_spec : forall A f, Proper (X.eq ==> Logic.eq ==> Logic.eq) f -> forall dom (m : t A dom),
  exists_ f m = true <-> exists x v, find x m = Some v ∧ f x v = true.
(*
Parameter filter : forall {A} (f : key -> A -> bool) {dom} (m : t A dom),
  t A (fold (fun x v acc => if f x v then Dom.add x acc else acc) m Dom.empty).

Parameter filter_spec : forall A f dom (m : t A dom) x v,
  find x (filter f m) = Some v <-> find x m = Some v ∧ f x v = true.
*)
End DepMapFacts.
