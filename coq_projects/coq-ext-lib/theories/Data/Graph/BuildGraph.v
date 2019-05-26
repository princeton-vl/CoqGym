Require Import ExtLib.Structures.Monads.
Require Import ExtLib.Data.Monads.StateMonad.

Set Implicit Arguments.
Set Strict Implicit.

Section Graph.
  Variable V : Type.
  Variable G : Type.

  Class BuildGraph : Type :=
  { emptyGraph : G
  ; addVertex : V -> G -> G
  ; addEdge   : V -> V -> G -> G
  }.
End Graph.

Arguments emptyGraph {_} {_} {_}.
Arguments addVertex {_} {_} {_} _ _.
Arguments addEdge {_} {_} {_} _ _ _.

(** A State Monad simplifies things **)
Section Monadic.
  Variable m : Type -> Type.
  Context {Monad_m : Monad m}.

  Variable V : Type.
  Variable G : Type.
  Variable BuildGraph_VG : BuildGraph V G.

  Definition GraphBuilderT (T : Type) : Type := stateT G m T.

  Global Instance Monad_GraphBuilder : Monad GraphBuilderT :=
    Monad_stateT _ _.

  Global Instance MonadT_GraphBuilder : MonadT GraphBuilderT m :=
    MonadT_stateT _ _.

  Instance State_GraphBuilder : MonadState G GraphBuilderT :=
    MonadState_stateT _ _.

  Import MonadNotation.
  Local Open Scope monad_scope.

  Definition newEdge (f t : V) : GraphBuilderT unit :=
    g <- get ;;
    put (addEdge f t g).

  Definition newVertex (v : V) : GraphBuilderT unit :=
    g <- get ;;
    put (addVertex v g).

  Definition buildGraph {v} (c : GraphBuilderT v) (g : G) : m G :=
    execStateT c g.

End Monadic.

Arguments newEdge {_} {_} {_} {_} {_} (_) (_).
Arguments newVertex {_} {_} {_} {_} {_} (_).