Require Import ExtLib.Structures.Maps.
Require Import ExtLib.Structures.Sets.

Set Implicit Arguments.
Set Strict Implicit.

(** Canonical instance, a set is the same as a map where the values
 ** are unit
 **)
(*
Section SetFromMap.
  Variable T : Type.
  Variable R : T -> T -> Prop.

  Variable m : Type -> Type.
  Variable Map_T : Map T m.

  Global Instance CSet_map : @DSet (m unit) T R :=
  { empty := Maps.empty
  ; contains := fun k m => match lookup k m with
                             | None => false
                             | Some _ => true
                           end
  ; add := fun k m => Maps.add k tt m
  ; remove := fun k m => Maps.remove k m
  ; singleton := fun v => Maps.add v tt Maps.empty
  }.
End SetFromMap.
*)