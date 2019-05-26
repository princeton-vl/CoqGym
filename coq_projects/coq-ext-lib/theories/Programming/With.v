Require Import Coq.Lists.List.

Set Asymmetric Patterns.

Fixpoint Ctor {T : Type} (ls : list {x : Type & T -> x}) : Type :=
  match ls with
    | nil    => T
    | a :: b => (projT1 a) -> Ctor b
  end.

Class Struct (T : Type) : Type := {
  fields : list {x : Type & T -> x} ;
  ctor   : Ctor fields
}.

Section With.
  Variable T : Type.
  Variable strt : Struct T.
  Variable rec : T.

  Section Member.
    Variable U : Type.

    Inductive Mem : list {x : Type & T -> x} -> Type :=
    | Here : forall a b, Mem ((@existT _ _ U a) :: b)
    | Next : forall a b, Mem b -> Mem (a :: b).
  End Member.

  Fixpoint applyRest (f : list {x : Type & T -> x}) : Ctor f -> T :=
    match f as f return Ctor f -> T with
      | nil => fun x => x
      | a :: b => fun acc => applyRest b (acc ((projT2 a) rec))
    end.

  Section Until.
    Context {U : Type}.
    Variable (v : U).

    Fixpoint applyUntil (f : list {x : Type & T -> x}) (n : Mem U f) : Ctor f -> T :=
      match n in Mem _ f return Ctor f -> T with
        | Here a b => fun ctor => applyRest b (ctor v)
        | Next a b i => fun ctor => applyUntil b i (ctor ((projT2 a) rec))
      end.
  End Until.

  Definition structWith {U : Type} (v : U) (n : Mem U fields) : T :=
    applyUntil v fields n ctor.

End With.

Class Accessor {T U : Type} {strt : Struct T} (f : T -> U) : Type := {
  acc : Mem T U fields
}.

Definition wrapWith {T U : Type} (t : T) (f : T -> U) (v : U)
  (_strt : Struct T) (_acc : Accessor f) :=
  @structWith _ _ t _ v acc.

Delimit Scope struct_scope with record.

Notation "{$ x 'with' y ':=' v $}" := (@wrapWith _ _ x y v _ _) : struct_scope.

Arguments Next { T U a b }.
Arguments Here { T U a b }.
