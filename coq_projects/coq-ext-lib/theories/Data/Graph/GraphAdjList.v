Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Structures.Monads.
Require Import ExtLib.Structures.Monoid.
Require Import ExtLib.Structures.Reducible.
Require Import ExtLib.Structures.Maps.
Require Import ExtLib.Data.List.
Require Import ExtLib.Data.PPair.
Require Import ExtLib.Data.Monads.WriterMonad.
Require Import ExtLib.Data.Monads.IdentityMonad.
Require Import ExtLib.Data.Graph.Graph.
Require Import ExtLib.Data.Graph.BuildGraph.

Set Implicit Arguments.
Set Strict Implicit.

Section GraphImpl.
  Variable V : Type.
  Variable map : Type.
  Variable Map : Map V (list V) map.
  Variable FMap : Foldable map (V * (list V)).
  Variable RelDec_V : RelDec (@eq V).

  Definition adj_graph : Type := map.

  Definition verts (g : adj_graph) : list V :=
    let c := foldM (m := writerT (Monoid_list_app) ident)
      (fun k_v _ => let k := fst k_v in tell (k :: nil)) (ret tt) g
    in
    psnd (unIdent (runWriterT c)).

  Definition succs (g : adj_graph) (v : V) : list V :=
    match lookup v g with
      | None => nil
      | Some vs => vs
    end.

  Global Instance Graph_adj_graph : Graph V adj_graph :=
  { verticies := verts
  ; successors := succs
  }.

  Definition add_vertex (v : V) (g : adj_graph) : adj_graph :=
    if contains v g then g else add v nil g.

  (** TODO: Move this **)
  Fixpoint list_in_dec v (ls : list V) : bool :=
    match ls with
    | nil => false
    | l :: ls =>
      if eq_dec l v then true
      else list_in_dec v ls
    end.

  Definition add_edge (f t : V) (g : adj_graph) : adj_graph :=
    match lookup f g with
      | None =>
        add f (t :: nil) g
      | Some vs =>
        if list_in_dec t vs then g
        else add f (t :: vs) g
    end.

  Global Instance GraphBuilder_adj_graph : BuildGraph V adj_graph :=
  { emptyGraph := empty
  ; addVertex := add_vertex
  ; addEdge   := add_edge
  }.

End GraphImpl.
