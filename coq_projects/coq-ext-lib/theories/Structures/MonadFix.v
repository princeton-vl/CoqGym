Require Import ExtLib.Structures.Monad.

Set Implicit Arguments.

Class MonadFix (m : Type -> Type) : Type :=
{ mfix : forall {T U}, ((T -> m U) -> T -> m U) -> T -> m U }.

Section MonadFix.

  Fixpoint ftype (ls : list Type) (r : Type) : Type :=
    match ls with
      | nil => r
      | cons l ls => l -> ftype ls r
    end.

  Fixpoint tuple (ls : list Type) : Type :=
    match ls with
      | nil => unit
      | cons l ls => l * tuple ls
    end%type.

  Fixpoint wrap (ls : list Type) R {struct ls} : (tuple ls -> R) -> ftype ls R :=
    match ls as ls return (tuple ls -> R) -> ftype ls R with
      | nil => fun f => f tt
      | cons l ls => fun f => fun x => wrap ls (fun g => f (x,g))
    end.

  Fixpoint apply (ls : list Type) R {struct ls} : ftype ls R -> tuple ls -> R :=
    match ls as ls return ftype ls R -> tuple ls -> R with
      | nil => fun f _ => f
      | cons l ls  => fun f t => @apply ls R (f (fst t)) (snd t)
    end.

  Context {m : Type -> Type} {MF : MonadFix m}.

  Definition mfix_multi (ls : list Type) (R : Type)
    (f : ftype ls (m R) -> ftype ls (m R))
    : ftype ls (m R) :=
    @wrap ls (m R) (@mfix _ MF (tuple ls) R
      (fun packed => apply ls (m R) (f (wrap ls packed)))).

  Context {mMonad:Monad m}.

  Definition mfix2 A B C
    (ff:(A -> B -> m C) -> (A -> B -> m C)) (a:A) (b:B) : m C :=
    let ff' fabp (abp:A*B) :=
      let (a,b) := abp in
      let fab a b := fabp (a,b) in
      ff fab a b
    in
    mfix ff' (a,b).

  Definition mfix3 A B C D
    (ff:(A -> B -> C -> m D) -> (A -> B -> C -> m D))
    (a:A) (b:B) (c:C) : m D :=
    let ff' fabcp (abcp:A*B*C) :=
      let (abp,c) := abcp in
      let (a,b) := abp in
      let fabc a b c := fabcp (a,b,c) in
      ff fabc a b c
    in
    mfix ff' (a,b,c).

End MonadFix.
Arguments mfix {m MonadFix T U} _ _.