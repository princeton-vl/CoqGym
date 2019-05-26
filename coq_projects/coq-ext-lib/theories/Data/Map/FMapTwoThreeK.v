Require Import Coq.Lists.List.
Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Structures.Maps.
Require Import ExtLib.Structures.Monads.
Require Import ExtLib.Structures.Reducible.

Set Implicit Arguments.
Set Strict Implicit.

Section keyed.
  Variable K : Type.
  Variable K_le : K -> K -> Prop.
  Variable RD_K : K -> K -> comparison.

  Inductive twothree (T : Type) : Type :=
  | Leaf
  | Two : twothree T -> K -> T -> twothree T -> twothree T
  | Three : twothree T -> K -> T -> twothree T -> K -> T -> twothree T -> twothree T.

  Arguments Leaf {T}.
  Arguments Two {T} _ _ _ _.
  Arguments Three {T} _ _ _ _ _ _ _.

  Section modify.
    Variable V : Type.
    Variable k : K.
    Variable upd : V -> option V.
    Variable def : option V.

    Fixpoint remove_greatest (m : twothree V) {T} (k_oops : unit -> T) (k_ok : K -> V -> twothree V -> T) : T :=
      match m with
        | Leaf => k_oops tt
        | Two l k v r =>
          remove_greatest r (fun _ => k_ok k v l) (fun k' v' r' => k_ok k' v' (Two l k v r'))
        | Three l k v m k' v' r =>
          remove_greatest r (fun _ => k_ok k' v' (Two l k v m)) (fun k'' v'' r'' => k_ok k'' v'' (Three l k v m k' v' r''))
      end.

    Fixpoint twothree_modify (m : twothree V) {T} (k_ok : twothree V -> T) (k_splice_up : twothree V -> K -> V -> twothree V -> T) {struct m} : T :=
      match m with
        | Leaf =>
          match def with
            | Some v => k_splice_up Leaf k v Leaf
            | None => k_ok Leaf
          end
        | Two l k' v' r =>
          match RD_K k k' with
            | Eq =>
              match upd v' with
                | Some v' => k_ok (Two l k v' r)
                | None => remove_greatest l (fun _ => k_ok r) (fun k v l => k_ok (Two l k v r))
              end
            | Lt =>
              twothree_modify l (fun l => k_ok (Two l k' v' r))
                                (fun l'' k'' v'' r'' => k_ok (Three l'' k'' v'' r'' k' v' r))
            | Gt =>
              twothree_modify r (fun r => k_ok (Two l k' v' r))
                                (fun l'' k'' v'' r'' => k_ok (Three l k' v' l'' k'' v'' r''))
          end
        | Three l k1 v1 m k2 v2 r =>
          match RD_K k k1 with
            | Eq =>
              match upd v1 with
                | Some v' => k_ok (Three l k v' m k2 v2 r)
                | None =>
                  remove_greatest l (fun _ => k_ok (Two m k2 v2 r)) (fun k1 v1 l => k_ok (Three l k1 v2 m k2 v2 r))
              end
            | Lt =>
              twothree_modify l (fun l' => k_ok (Three l' k1 v1 m k2 v2 r))
                                (fun l' k' v' r' => k_splice_up (Two l' k' v' r') k1 v1 (Two m k2 v2 r))
            | Gt =>
              match RD_K k k2 with
                | Eq =>
                  match upd v2 with
                    | Some v2 => k_ok (Three l k1 v1 m k v2 r)
                    | None =>
                      remove_greatest m (fun _ => k_ok (Two l k1 v1 r))
                                        (fun k' v' m' => k_ok (Three l k1 v1 m' k' v' r))
                  end
                | Lt =>
                  twothree_modify m (fun m' => k_ok (Three l k1 v1 m' k2 v2 r))
                                    (fun l' k' v' r' => k_splice_up (Two l k1 v1 l') k' v' (Two r' k2 v2 r))
                | Gt =>
                  twothree_modify r (fun r' => k_ok (Three l k1 v1 m k2 v2 r'))
                                    (fun l' k' v' r' => k_splice_up (Two l k1 v1 m) k2 v2 (Two l' k' v' r'))
              end
          end
      end.

  End modify.

  Definition twothree_add {V} (k : K) (v : V) (m : twothree V) : twothree V :=
    twothree_modify k (fun _ => Some v) (Some v) m (fun m => m) Two.

  Definition twothree_remove {V} (k : K) (m : twothree V) : twothree V :=
    twothree_modify k (fun _ => None) None m (fun m => m) Two.

  Fixpoint twothree_find {V} (k : K) (m : twothree V) : option V :=
    match m with
      | Leaf => None
      | Two l k' v' r =>
        match RD_K k k' with
          | Eq => Some v'
          | Lt => twothree_find k l
          | Gt => twothree_find k r
        end
      | Three l k1 v1 m k2 v2 r =>
        match RD_K k k1 with
          | Eq => Some v1
          | Lt => twothree_find k l
          | Gt => match RD_K k k2 with
                    | Eq => Some v2
                    | Lt => twothree_find k m
                    | Gt => twothree_find k r
                  end
        end
    end.

  Section fold.
    Import MonadNotation.
    Local Open Scope monad_scope.

    Variables V T : Type.
    Variable f : K -> V -> T -> T.

    Fixpoint twothree_fold (acc : T) (map : twothree V) : T :=
      match map with
        | Leaf => acc
        | Two l k v r =>
          let acc := twothree_fold acc l in
          let acc := f k v acc in
          twothree_fold acc r
        | Three l k1 v1 m k2 v2 r =>
          let acc := twothree_fold acc l in
          let acc := f k1 v1 acc in
          let acc := twothree_fold acc m in
          let acc := f k2 v2 acc in
          twothree_fold acc m
      end.

  End fold.

  Definition twothree_union {V} (m1 m2 : twothree V) : twothree V :=
    twothree_fold twothree_add m2 m1.

  Global Instance Map_twothree V : Map K V (twothree V) :=
  { empty  := Leaf
  ; add    := twothree_add
  ; remove := twothree_remove
  ; lookup := twothree_find
  ; union  := twothree_union
  }.

  Global Instance Foldable_twothree V : Foldable (twothree V) (K * V) :=
    fun _ f b x => twothree_fold (fun k v => f (k,v)) b x.

End keyed.

(** Performance Test **)
(*
Module TEST.
  Definition m := twothree nat nat.
  Instance Map_m : Map nat (twothree nat).
    apply Map_twothree.
    apply Compare_dec.nat_compare.
  Defined.

  Definition z : m :=
    (fix fill n acc : m :=
      let acc := add n n acc in
      match n with
        | 0 => acc
        | S n => fill n acc
      end) 500 empty.

  Time Eval vm_compute in
    let z := z in
    (fix find_all n : unit :=
      let _ := lookup n z in
      match n with
        | 0 => tt
        | S n => find_all n
      end) 500.
End TEST.
*)