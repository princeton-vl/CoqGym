(** DepMap: Maps with explicit domain contained in their type *)
Require Import Utf8.
Require Import MSets.
Require Import Coqlib.


Set Implicit Arguments.


(**************************************************************************)
(** **  Interface for maps with explicit domain contained in their type  **)
(**************************************************************************)


Module Type DepMap (X : OrderedType).

(** The type of domains: sets over [X]. **)
Declare Module Dom : MSetInterface.SetsOn(X) with Definition elt := X.t.

(** The type of dependent maps. **)
Definition key := X.t.
Parameter t : forall (A : Type) (dom : Dom.t), Type.

(** ***  Operations over dependent maps  **)

Parameter empty : forall {A}, t A Dom.empty.
(** The empty map, of empty domain. **)

Parameter is_empty : forall {A} {dom}, t A dom -> bool.
(** A boolean test retuning [true] iff the argument is empty. **)

Parameter mem : forall {A} {dom}, key -> t A dom -> bool.
(** [mem x m] returns [true] iff the key [x] is bound in [m]. **)

Parameter find : forall {A} {dom}, key -> t A dom -> option A.
(** [find x m] returns the binding of [x] in [m], if present. **)

Parameter domain : forall {A} {dom}, t A dom -> Dom.t.
(** [domain m] returns the domain of [m]. **)

Parameter add : forall {A} {dom} (x : key) (v : A) (m : t A dom), t A (Dom.add x dom).
(** [add x v m] adds the binding (s, v) to [m], replacing any previous binding. **)

Parameter set : forall {A} {dom} (x : key) (v : A) (m : t A dom), Dom.In x dom -> t A dom.
(** [set x v m] replaces the binding of [x] in [m] by [v].
    The difference with [add] is that the domain in not changed, which requires a proof
    that [x] belongs to the domain of [m]. **)

Parameter remove : forall {A} {dom} x (m : t A dom), t A (Dom.remove x dom).
(** [remove x m] removes the binding of [x] in [m]. **)

Parameter singleton : forall {A} (x : key), A -> t A (Dom.singleton x).
(** [singleton x v] is the map containing only the binding (x, v). **)

Parameter constant : forall {A} dom, A -> t A dom.
(** [constant dom x v] is the map of domain [dom] where every key is mapped to [v]. **)

Parameter fold : forall {A B : Type}, (key -> A -> B -> B) -> forall {dom}, t A dom -> B -> B.
(** [fold f m i] iterates [f] over all bindings in [m] in increasing order, starting from [i]. **)

Parameter map : forall A B, (A -> B) -> forall dom, t A dom -> t B dom.
(** [map f m] replaces all bindings [(x,v)] in [m] by [(x, f v)]. **)

Parameter combine : forall A B C, (A -> B -> C) -> (A -> C) -> (B -> C) ->
  forall dom₁ dom₂, t A dom₁ -> t B dom₂ -> t C (Dom.union dom₁ dom₂).
(** [combine f g h m₁ m₂] merges the map [m₁] and [m₂] into one by applying [f], [g] or [h]:
    - if [x] is bound to [v₁] in [m₁] and to [v₂] in [m₂], it is bound to [f v₁ v₂];
    - if [x] is bound to [v] in [m₁] and unbound in [m₂], it is bound to [g v];
    - if [x] is unbound in [m₁] and bound to [v] in [m₂], it is bound to [h v]. **)

Parameter cast : forall {A} {dom₁} {dom₂}, Dom.eq dom₁ dom₂ -> t A dom₁ -> t A dom₂.
(** [cast Heq m] only changes the type of [m], according to the equality [Heq] of the domains [dom₁] and [dom₂]. **)

Parameter elements : forall {A} {dom}, t A dom -> list (key * A).
(** [elements m] returns the ordered list of bindings in [m]. **)

Parameter from_elements : forall {A} (l : list (key * A)),
  t A (List.fold_left (fun acc xv => Dom.add (fst xv) acc) l Dom.empty).
(** [from_elements l] builds a map from the list of bindings [l]. **)


(** ***  Specifications of these operations  **)

Parameter empty_spec : forall A x, find x (@empty A) = None.

Parameter is_empty_spec : forall A dom (m : t A dom), is_empty m = true <-> forall x, find x m = None.

Parameter mem_spec : forall A x dom (m : t A dom), mem x m = true <-> exists v, find x m = Some v.

Declare Instance find_elt_compat A dom (m : t A dom) : Proper (X.eq ==> Logic.eq) (fun x => find x m).
Parameter find_spec : forall A x dom (m : t A dom), (exists v, find x m = Some v) <-> Dom.In x dom.

Parameter domain_spec : forall A dom (m : t A dom), domain m = dom.

Parameter set_same : forall A x v dom (m : t A dom) Hin, find x (@set A dom x v m Hin) = Some v.
Parameter set_other : forall A x y v dom (m : t A dom) Hin, ¬X.eq y x -> find y (@set A dom x v m Hin) = find y m.

Parameter add_same : forall A x v dom (m : t A dom), find x (add x v m) = Some v.
Parameter add_other : forall A x y v dom (m : t A dom), ¬X.eq y x -> find y (add x v m) = find y m.

Parameter singleton_same : forall A x (v : A), find x (singleton x v) = Some v.
Parameter singleton_other : forall A x y (v : A), ¬X.eq y x -> find y (singleton x v) = None.

Parameter remove_same : forall A x dom (m : t A dom), find x (remove x m) = None.
Parameter remove_other : forall A x y dom (m : t A dom), ¬X.eq y x -> find y (remove x m) = find y m.

Parameter constant_Some : forall A dom (v : A) x u, find x (constant dom v) = Some u <-> Dom.In x dom ∧ u = v.
Parameter constant_None : forall A dom (v : A) x, find x (constant dom v) = None <-> ¬Dom.In x dom.

Parameter fold_spec : forall A B (f : key -> A -> B -> B) dom (m : t A dom) (i : B),
  fold f m i = List.fold_left (fun acc xv => f (fst xv) (snd xv) acc) (elements m) i.

Parameter map_spec : forall A B (f : A -> B) dom (m : t A dom) x v,
  find x (map f m) = Some v <-> exists u, find x m = Some u ∧ f u = v.

Parameter combine_spec : forall A B C (f : A -> B -> C) g₁ g₂ dom₁ dom₂ (m₁ : t A dom₁) (m₂ : t B dom₂) x v,
  find x (combine f g₁ g₂ m₁ m₂) = Some v <->
  (exists v₁ v₂, find x m₁ = Some v₁ ∧ find x m₂ = Some v₂ ∧ v = f v₁ v₂)
  ∨ (exists v₁, find x m₁ = Some v₁ ∧ find x m₂ = None ∧ v = g₁ v₁)
  ∨ (exists v₂, find x m₁ = None ∧ find x m₂ = Some v₂ ∧ v = g₂ v₂).

Parameter cast_spec_find : forall A dom₁ dom₂ (Heq : Dom.eq dom₁ dom₂) (m : t A dom₁) x,
  find x (cast Heq m) = find x m.

Parameter elements_spec : forall A dom (m : t A dom) xv,
  InA (X.eq * eq)%signature xv (elements m) <-> find (fst xv) m = Some (snd xv).

Parameter elements_Sorted : forall A dom (m : t A dom), Sorted (X.lt@@1)%signature (elements m).

Parameter from_elements_spec : forall A (l : list (key * A)), NoDupA (X.eq@@1)%signature l ->
  forall x v, find x (from_elements l) = Some v <-> InA (X.eq * eq)%signature (x, v) l.

End DepMap.
