Require Import RelationClasses.
Require Import ExtLib.Structures.Monad.
Require Import ExtLib.Structures.Reducible.

Set Implicit Arguments.
Set Strict Implicit.

(** First-class maps **)
Section Maps.
  Variables K V : Type.
  Variable map : Type.

  (** General Maps **)
  Class Map : Type :=
  { empty    : map
  ; add      : K -> V -> map -> map
  ; remove   : K -> map -> map
  ; lookup   : K -> map -> option V
  ; union    : map -> map -> map
  }.

  Variable R : K -> K -> Prop.

  Class MapOk (M : Map) : Type :=
  { mapsto : K -> V -> map -> Prop
  ; mapsto_empty : forall k v, ~mapsto k v empty
  ; mapsto_lookup : forall k v m, lookup k m = Some v <-> mapsto k v m
  ; mapsto_add_eq : forall m k v, mapsto k v (add k v m)
  ; mapsto_add_neq : forall m k v k',
                       ~R k k' ->
                       forall v', (mapsto k' v' m <-> mapsto k' v' (add k v m))
  }.

  Variable M : Map.

  Definition contains (k : K) (m : map) : bool :=
    match lookup k m with
      | None => false
      | Some _ => true
    end.

  Definition singleton (k : K) (v : V) : map :=
    add k v empty.

  (* Finite Maps *)
  Context {F : Foldable map (K * V)}.

  Definition combine (f : K -> V -> V -> V) (m1 m2 : map) : map :=
    fold (fun k_v acc =>
      let '(k,v) := k_v in
      match lookup k acc with
        | None => add k v acc
        | Some v' => add k (f k v v') acc
      end) m2 m1.

  Definition filter (f : K -> V -> bool) (m : map) : map :=
    fold (fun k_v acc =>
      let '(k,v) := k_v in
      if f k v
        then add k v acc
        else acc) empty m.

  Definition submap_with (le : V -> V -> bool) (m1 m2 : map) : bool :=
    fold (fun k_v (acc : bool) => 
      if acc then 
        let '(k,v) := k_v in
        match lookup k m2 with
          | None => false
          | Some v' => le v v'
        end
      else false) true m1.

(*
  Definition keys (s : Type) (_ : DMonad s K) : map T -> s :=
    fold (fun k_v (acc : s) =>
      djoin (dreturn (fst k_v)) acc) dzero.

  Definition values (s : Type) (_ : DMonad s T) : map T -> s :=
    fold (fun k_v (acc : s) =>
      djoin (dreturn (snd k_v)) acc) dzero.
*)

End Maps.

Arguments empty {_} {_} {_} {_} .
Arguments add {K V} {map} {Map} _ _ _.
Arguments remove {K V} {map} {Map} _ _.
Arguments lookup {K V} {map} {Map} _ _.
Arguments contains {K V} {map} {M} _ _.
Arguments singleton {K V} {map} {M} _ _.
Arguments combine {K V} {map} {M} _ _ _ _.
