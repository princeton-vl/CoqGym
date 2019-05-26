Require Import ExtLib.Structures.Monads.
Require Import BinPos.

Set Implicit Arguments.
Set Strict Implicit.

Inductive FixResult (T : Type) :=
| Term : T -> FixResult T
| Diverge : FixResult T.

Arguments Diverge {_}.
Arguments Term {_} _.

(** The GFix monad is like monad fix except that
 ** it encapsulates the "gas" that is used as the measure
 **)
Section gfix.
  (** This is essentially ReaderT (optionT m)) **)
  Inductive GFix (T : Type) : Type := mkGFix
  { runGFix : N -> FixResult T }.

  Global Instance MonadFix_GFix : MonadFix GFix :=
  { mfix := fun T U f v => mkGFix (fun n : N => 
    match n with
      | N0 => Diverge
      | Npos g => 
        let F := fix rec (acc : T -> FixResult U) (gas : positive) (x : T) 
          : FixResult U :=
          match gas return FixResult U with
            | xI p => 
              runGFix (f (fun x => mkGFix (fun n => rec (fun x => rec acc p x) p x)) x) n
            | xO p => 
              rec (fun x => rec acc p x) p x
            | xH => runGFix (f (fun x => mkGFix (fun _ => acc x)) x) n
          end
        in F (fun x => runGFix (f (fun _ => mkGFix (fun _ => Diverge)) x) n) g v
      end)
  }.

  Global Instance Monad_GFix : Monad GFix :=
  { ret := fun _ v => mkGFix (fun _ => Term v)
  ; bind := fun _ _ c1 c2 =>
    mkGFix (fun gas =>
      match runGFix c1 gas with
        | Diverge => Diverge
        | Term v => runGFix (c2 v) gas
      end)
  }.

End gfix.

(** Demo
Require Import ExtLib.Data.Monads.IdentityMonad.
Definition foo : nat -> GFix ident nat :=
  mfix (fun recur n => 
    match n with
      | 0 => ret 0
      | S n => recur n
    end).

Eval compute in runGFix (foo 10) 100000000000000000000000.
**)
