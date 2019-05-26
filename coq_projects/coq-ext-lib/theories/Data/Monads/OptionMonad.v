Require Import ExtLib.Structures.Monads.

Set Implicit Arguments.
Set Strict Implicit.

Import MonadNotation.
Local Open Scope monad_scope.

Global Instance Monad_option : Monad option :=
{ ret  := @Some
; bind := fun _ _ c1 c2 => match c1 with
                             | None => None
                             | Some v => c2 v
                           end
}.

Global Instance Zero_option : MonadZero option :=
{ mzero := @None }.

Global Instance Plus_option : MonadPlus option :=
{ mplus _A _B aM bM :=
    match aM with
    | None => liftM inr bM
    | Some a => Some (inl a)
    end
}.

Section Trans.
  Variable m : Type -> Type.

  Inductive optionT a := mkOptionT { unOptionT : m (option a) }.

  Context {M : Monad m}.

  Global Instance Monad_optionT : Monad optionT :=
  { ret _A := fun x => mkOptionT (ret (Some x))
  ; bind _A _B aMM f := mkOptionT
      (aM <- unOptionT aMM ;;
       match aM with
       | None => ret None
       | Some a => unOptionT (f a)
       end)
  }.

  Global Instance Zero_optionT : MonadZero optionT :=
  { mzero _A := mkOptionT (ret None) }.

  Global Instance MonadT_optionT : MonadT optionT m :=
  { lift _A aM := mkOptionT (liftM ret aM) }.

  Global Instance State_optionT {T} (SM : MonadState T m) : MonadState T optionT :=
  { get := lift get
  ; put v := lift (put v)
  }.

  Instance Plus_optionT_right : MonadPlus optionT :=
  { mplus _A _B a b :=
      mkOptionT (bind (unOptionT b) (fun b =>
        match b with
          | None =>
            bind (unOptionT a) (fun a =>
                                  match a with
                                    | None => ret None
                                    | Some a => ret (Some (inl a))
                                  end)
          | Some b => ret (Some (inr b))
        end))
  }.

  Instance Plus_optionT_left : MonadPlus optionT :=
  { mplus _A _B a b :=
      mkOptionT (bind (unOptionT a) (fun a =>
        match a with
          | None =>
            bind (unOptionT b) (fun b =>
                                  match b with
                                    | None => ret None
                                    | Some b => ret (Some (inr b))
                                  end)
          | Some a => ret (Some (inl a))
        end))
  }.

  Global Instance Plus_optionT : MonadPlus optionT := Plus_optionT_left.

  Global Instance Reader_optionT {T} (SM : MonadReader T m) : MonadReader T optionT :=
  { ask := lift ask
  ; local _T v cmd := mkOptionT (local v (unOptionT cmd))
  }.

  Instance OptionTError : MonadExc unit optionT :=
  { raise _u _A := mzero
  ; catch _A aMM f := mkOptionT
      (aM <- unOptionT aMM ;;
       match aM with
       | None => unOptionT (f tt)
       | Some x => ret (Some x)
       end)
  }.

End Trans.
