Require Import Coq.Strings.String.
(** Require the monad definitions **)
Require Import ExtLib.Structures.Monads.
(** Use the instances for exceptions **)
Require Import ExtLib.Data.Monads.EitherMonad.
(** Strings will be used for error messages **)
Require Import ExtLib.Data.String.

Set Implicit Arguments.
Set Strict Implicit.

(** Syntax and values of a simple language **)
Inductive value : Type :=
| Int : nat -> value
| Bool : bool -> value.

Inductive exp : Type :=
| ConstI : nat -> exp
| ConstB : bool -> exp
| Plus : exp -> exp -> exp
| If : exp -> exp -> exp -> exp.

Section monadic.
  (** Going to work over any monad [m] that is:
   ** 1) a Monad, i.e. [Monad m]
   ** 2) has string-valued exceptions, i.e. [MonadExc string m]
   **)
  Variable m : Type -> Type.
  Context {Monad_m : Monad m}.
  Context {MonadExc_m : MonadExc string m}.

  (** Use the notation for monads **)
  Import MonadNotation.
  Local Open Scope monad_scope.

  (** Functions that get [nat] or [bool] values from a [value] **)
  Definition asInt (v : value) : m nat :=
    match v with
      | Int n => ret n
      | _ =>
        (** if we don't have an integer, signal an error using
         ** [raise] from the MoandExc instance
         **)
        raise ("expected integer got bool")%string
    end.

  Definition asBool (v : value) : m bool :=
    match v with
      | Bool b => ret b
      | _ => raise ("expected bool got integer")%string
    end.

  (** The main evaluator routine returns a [value], but since we are
   ** working in the [m] monad, we return [m value]
   **)
  Fixpoint eval' (e : exp) : m value :=
    match e with
        (** when there is no error, we can just return (i.e. [ret])
         ** the answer
         **)
      | ConstI i => ret (Int i)
      | ConstB b => ret (Bool b)
      | Plus l r =>
        (** evaluate the sub-terms to numbers **)
        l <- eval' l ;;
        l <- asInt l ;;
        r <- eval' r ;;
        r <- asInt r ;;
        (** Combine the result **)
        ret (Int (l + r))
      | If t tr fa =>
        (** evaluate the test condition to a boolean **)
        t <- eval' t ;;
        t <- asBool t ;;
        (** case split and perform the appropriate recursion **)
        if (t : bool) then
          eval' tr
        else
          eval' fa
    end.

End monadic.

(** Wrap the [eval] function up with the monad instance that we
 ** want to use
 **)
Definition eval : exp -> string + value :=
  eval' (m := sum string).

(** Some tests **)
Eval compute in eval (Plus (ConstI 1) (ConstI 2)).
Eval compute in eval (Plus (ConstI 1) (ConstB false)).

(** Other useful monads:
 ** * Reader - for handling lexicographic environments
 ** * State - for handling non-lexical state, like a heap
 ** * MonadFix - for handling unbounded recursion
 **)
