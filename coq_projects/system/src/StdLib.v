(** The standard library. *)
Require Import Coq.Lists.List.
Require Import Coq.NArith.NArith.
Require Import ListString.All.
Require Import Computation.
Require Import Events.

Import ListNotations.
Import C.Notations.

(** Log data. *)
Module Log.
  (** Log a message on the standard output. *)
  Definition write {sig : Signature.t} (message : LString.t)
    (handler : bool -> C.t sig unit) : C.t sig unit :=
    C.Send Command.Log message tt (fun _ is_success =>
      do! handler is_success in
      C.Ret None).
End Log.

(** Read a file. *)
Module File.
  (** Read all the content of a file. *)
  Definition read {sig : Signature.t} (file_name : LString.t)
    (handler : option LString.t -> C.t sig unit) : C.t sig unit :=
    C.Send Command.FileRead file_name tt (fun _ content =>
      do! handler content in
      C.Ret None).
End File.

(** TCP client socket. *)
Module ClientSocket.
  (** Read a message. *)
  Definition read {sig : Signature.t} {A : Type} (id : ClientSocketId.t) (a : A)
    (handler : A -> option LString.t -> C.t sig (option A)) : C.t sig unit :=
    C.Send Command.ClientSocketRead id a handler.

  (** Write a message. *)
  Definition write {sig : Signature.t} (id : ClientSocketId.t) (data : LString.t)
    (handler : bool -> C.t sig unit) : C.t sig unit :=
    C.Send Command.ClientSocketWrite (id, data) tt (fun _ is_success =>
      do! handler is_success in
      C.Ret None).

  (** Close the socket. *)
  Definition close {sig : Signature.t} (id : ClientSocketId.t)
    (handler : bool -> C.t sig unit) : C.t sig unit :=
    C.Send Command.ClientSocketClose id tt (fun _ is_success =>
      do! handler is_success in
      C.Ret None).
End ClientSocket.

(** TCP server socket. *)
Module ServerSocket.
  (** Bind a socket. *)
  Definition bind {sig : Signature.t} (port : N)
    (handler : option ClientSocketId.t -> C.t sig unit) : C.t sig unit :=
    C.Send Command.ServerSocketBind port tt (fun _ client =>
      do! handler client in
      C.Ret (Some tt)).
End ServerSocket.

(** Get the current time. *)
Module Time.
  (** Get the current time (the number of seconds since Unix epoch). *)
  Definition get {sig : Signature.t} (handler : N -> C.t sig unit)
    : C.t sig unit :=
    C.Send Command.Time tt tt (fun _ time =>
      do! handler time in
      C.Ret None).
End Time.
