Require Import Coq.Lists.List.
Require Import ExtLib.Data.Member.

Fixpoint asFunc (domain : list Type) (range : Type) : Type :=
  match domain with
    | nil => range
    | d :: ds => d -> asFunc ds range
  end.

Fixpoint asPi (ps : list Type) {struct ps} :
         ((forall U, asFunc ps U -> U) -> Type) -> Type :=
  match ps as ps return ((forall U, asFunc ps U -> U) -> Type) -> Type with
    | nil => fun f => f (fun _ x => x)
    | p :: ps => fun f => forall x : p, asPi ps (fun App => f (fun _ f' => App _ (f' x)))
  end.

Fixpoint asTuple (domain : list Type) : Type :=
  match domain with
    | nil => unit
    | d :: ds => prod d (asTuple ds)
  end.

Fixpoint applyF {domain : list Type} {range : Type}
  : asFunc domain range -> asTuple domain -> range :=
  match domain as domain
    return asFunc domain range -> asTuple domain -> range
    with
    | nil => fun x _ => x
    | d :: ds => fun f x_xs => applyF (f (fst x_xs)) (snd x_xs)
  end.

Fixpoint const {D R} (r : R) : asFunc D R :=
  match D with
    | nil => r
    | _ :: D => fun _ => const r
  end.

Fixpoint uncurry {D R} {struct D} : (asTuple D -> R) -> asFunc D R :=
  match D as D return (asTuple D -> R) -> asFunc D R with
    | nil => fun x => x tt
    | d :: D => fun f d => uncurry (fun x => f (d, x))
  end.

Fixpoint curry {D R} {struct D} : asFunc D R -> (asTuple D -> R) :=
  match D as D return asFunc D R -> (asTuple D -> R) with
    | nil => fun x _ => x
    | d :: D => fun f x => curry (f (fst x)) (snd x)
  end.

Fixpoint get (domain : list Type) (range : Type) T (m : member T domain)
: (T -> asFunc domain range) -> asFunc domain range :=
  match m in member _ domain
        return (T -> asFunc domain range) -> asFunc domain range
  with
    | MZ _ _ => fun F x => F x x
    | MN _ m => fun F x => @get _ _ _ m (fun y => F y x)
  end.

Fixpoint under (domain : list Type) (range : Type)
         {struct domain}
: ((forall U, asFunc domain U -> U) -> range)
  -> asFunc domain range :=
  match domain as domain
        return ((forall U, asFunc domain U -> U) -> range)
               -> asFunc domain range
  with
    | nil => fun F => F (fun _ x => x)
    | d :: ds => fun F x =>
                   under ds range (fun App => F (fun U f => App U (f x)))
  end%type.

Fixpoint replace {ps} {T U : Type} (m : member T ps) (v : T) {struct m}
: asFunc ps U -> asFunc ps U :=
  match m in member _ ps return asFunc ps U -> asFunc ps U with
    | MZ _ _ => fun f _ => f v
    | MN _ m => fun f x => replace m v (f x)
  end.

Section combine.
  Context {T U V : Type}.
  Variable (join : T -> U -> V).

  Definition combine (domain : list Type)
             (a : asFunc domain T) (b : asFunc domain U)
  : asFunc domain V :=
    under domain _ (fun App => join (App _ a) (App _ b)).

End combine.
