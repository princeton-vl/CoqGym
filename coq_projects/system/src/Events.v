(** Events which define the API to the system. *)
Require Import Coq.Lists.List.
Require Import Coq.NArith.NArith.
Require Import Coq.PArith.PArith.
Require Import ListString.All.

Import ListNotations.
Local Open Scope type.

(** The id of a client socket. *)
Module ClientSocketId.
  (** A socket id is a natural number. *)
  Inductive t : Set :=
  | New : N -> t.
End ClientSocketId.

(** The kind of commands. *)
Module Command.
  (** The list of commands. *)
  Inductive t : Set :=
  | Log
  | FileRead
  | ServerSocketBind
  | ClientSocketRead | ClientSocketWrite | ClientSocketClose
  | Time.

  (** The type of the parameters of a request. *)
  Definition request (command : t) : Set :=
    match command with
    | Log => LString.t
    | FileRead => LString.t
    | ServerSocketBind => N
    | ClientSocketRead => ClientSocketId.t
    | ClientSocketWrite => ClientSocketId.t * LString.t
    | ClientSocketClose => ClientSocketId.t
    | Time => unit
    end.

  (** The type of the parameters of an answer. *)
  Definition answer (command : t) : Set :=
    match command with
    | Log => bool
    | FileRead => option LString.t
    | ServerSocketBind => option ClientSocketId.t
    | ClientSocketRead => option LString.t
    | ClientSocketWrite => bool
    | ClientSocketClose => bool
    | Time => N
    end.

  (** Decide the equality of commands. *)
  Definition eq_dec (command1 command2 : t) :
    {command1 = command2} + {command1 <> command2}.
    destruct command1; destruct command2;
      try (left; congruence);
      try (right; congruence).
  Defined.
End Command.

(** The type of an output. *)
Module Output.
  (** An output is a command, a channel id and an argument. *)
  Record t : Set := New {
    command : Command.t;
    id : positive;
    argument : Command.request command }.
End Output.

(** The type of an input. *)
Module Input.
  (** An input is a command, a channel id and an argument. *)
  Record t : Set := New {
    command : Command.t;
    id : positive;
    argument : Command.answer command }.
End Input.
