Require Import ExtLib.Structures.Monads.
Require Import ExtLib.Structures.Monoid.

Set Implicit Arguments.
Set Strict Implicit.

Import MonadNotation.
Local Open Scope monad_scope.

Section except.
  Variable T : Type.

  Global Instance Monad_either : Monad (sum T) :=
  { ret  := fun _ v => inr v
  ; bind := fun _ _ c1 c2 => match c1 with
                               | inl v => inl v
                               | inr v => c2 v
                             end
  }.

  Global Instance Exception_either : MonadExc T (sum T) :=
  { raise := fun _ v => inl v
  ; catch := fun _ c h => match c with
                            | inl v => h v
                            | x => x
                          end
  }.

  Variable m : Type -> Type.

  Inductive eitherT A := mkEitherT { unEitherT : m (sum T A) }.

  Variable M : Monad m.

  Global Instance Monad_eitherT : Monad eitherT :=
  { ret := fun _ x => mkEitherT (ret (inr x))
  ; bind := fun _ _ c f => mkEitherT (
      xM <- unEitherT c ;;
      match xM with
      | inl x => ret (inl x)
      | inr x => unEitherT (f x)
      end
    )
  }.

  Global Instance Exception_eitherT : MonadExc T eitherT :=
  { raise := fun _ v => mkEitherT (ret (inl v))
  ; catch := fun _ c h => mkEitherT (
      xM <- unEitherT c ;;
      match xM with
        | inl x => unEitherT (h x)
        | inr x => ret (inr x)
      end
    )
  }.

  Global Instance MonadPlus_eitherT : MonadPlus eitherT :=
  { mplus _A _B mA mB := mkEitherT (
      x <- unEitherT mA ;;
      match x with
      | inl _ =>
          y <- unEitherT mB ;;
          match y with
          | inl t => ret (inl t)
          | inr b => ret (inr (inr b))
          end
      | inr a => ret (inr (inl a))
      end
    )
  }.

  Global Instance MonadT_eitherT : MonadT eitherT m :=
  { lift := fun _ c => mkEitherT (liftM ret c) }.

  Global Instance MonadState_eitherT {T} (MS : MonadState T m) : MonadState T eitherT :=
  { get := lift get
  ; put := fun v => lift (put v)
  }.

  Global Instance MonadReader_eitherT {T} (MR : MonadReader T m) : MonadReader T eitherT :=
  { ask := lift ask
  ; local := fun _ f cmd => mkEitherT (local f (unEitherT cmd))
  }.

  Global Instance MonadWriter_eitherT {T} (Mon : Monoid T) (MW : MonadWriter Mon m) : MonadWriter Mon eitherT :=
  { tell := fun x => lift (tell x)
  ; listen := fun _ c => mkEitherT (
    x <- listen (unEitherT c) ;;
    match x with
      | (inl l, _) => ret (inl l)
      | (inr a, t) => ret (inr (a, t))
    end)
  ; pass := fun _ c => mkEitherT (
    x <- unEitherT c ;;
    match x with
      | inl s => ret (inl s)
      | inr (a,f) => pass (ret (inr a, f))
    end)
  }.

  Global Instance MonadFix_eitherT (MF : MonadFix m) : MonadFix eitherT :=
  { mfix := fun _ _ r v =>
    mkEitherT (mfix (fun f x => unEitherT (r (fun x => mkEitherT (f x)) x)) v)
  }.

End except.
