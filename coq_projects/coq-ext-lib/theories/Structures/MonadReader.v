(** The Reader Monad Class
 **)
Require Import ExtLib.Structures.Monad.

Set Universe Polymorphism.
Set Printing Universes.

Class MonadReader@{d c} (T : Type@{d}) (m : Type@{d} -> Type@{c})
: Type :=
{ local : forall {t : Type@{d}}, (T -> T) -> m t -> m t
; ask : m T
}.

Arguments local {T} {m} {_} {t} _ _ : rename.
Arguments ask {T} {m} {_} : rename.

Definition asks@{d c}
           {m : Type@{d} -> Type@{c}}
           {M : Monad m}
           {T : Type@{d}}
           {MR : MonadReader@{d c} T m}
           {U : Type@{d}} (f : T -> U) : m U :=
  bind ask (fun x => ret (f x)).

Definition ReaderProd@{d c}
           {m : Type@{d} -> Type@{c}}
           {M : Monad m}
           {T S : Type@{d}}
           {MR : MonadReader T m}
           (f : T -> S)
           (g : S -> T -> T)
: MonadReader@{d c} S m :=
{| ask := @asks m M T MR S f
 ; local := fun _T up (c : m _T)  =>
              @local T m MR _ (fun s => g (up (f s)) s) c
 |}.
