(** Test the standard library. *)
Require Import Coq.Lists.List.
Require Import Coq.NArith.NArith.
Require Import Coq.Strings.String.
Require Import ListString.All.
Require Import Computation.
Require Import Events.
Require Import Extraction.
Require Import StdLib.

Import ListNotations.
Import C.Notations.
Local Open Scope string.

(** Do nothing. *)
Module DoNothing.
  Definition program (argv : list LString.t) : C.t [] unit :=
    C.Exit.

  Definition test1 :
    Run.run_on_inputs (program []) Memory.Nil [] = (true, []) :=
    eq_refl.
End DoNothing.

(** Say hello. *)
Module HelloWorld.
  Definition program (argv : list LString.t) : C.t [] unit :=
    Log.write (LString.s "Hello") (fun _ =>
    Log.write (LString.s "world!") (fun _ =>
    C.Exit)).

  Definition test1 : Run.run_on_inputs (program []) Memory.Nil [
    Input.New Command.Log 1 true;
    Input.New Command.Log 2 true ] =
    (true, [
      Output.New Command.Log 2 (LString.s "world!");
      Output.New Command.Log 1 (LString.s "Hello") ]) :=
    eq_refl.

  Definition test2 : Run.run_on_inputs (program []) Memory.Nil [
    Input.New Command.Log 2 true;
    Input.New Command.Log 1 true ] =
    (false, [
      Output.New Command.Log 2 (LString.s "world!");
      Output.New Command.Log 1 (LString.s "Hello") ]) :=
    eq_refl.
End HelloWorld.

(** Print the content of a file. *)
Module ReadFile.
  Definition program (argv : list LString.t) : C.t [] unit :=
    match argv with
    | [_; file_name] =>
      File.read file_name (fun content =>
      let message := match content with
        | None => (LString.s "Error: cannot read the file.")
        | Some content => content
        end in
      Log.write message (fun _ => C.Exit))
    | _ =>
      Log.write (LString.s "One parameter (the file to read) expected.") (fun _ =>
      C.Exit)
    end.
End ReadFile.

(** A server responding to all incoming messages. *)
Module EchoServer.
  Definition port : N := 5 % N.

  Definition program (argv : list LString.t) : C.t [] unit :=
    ServerSocket.bind port (fun client_id =>
      match client_id with
      | None =>
        do! Log.write (LString.s "Server socket failed.") (fun _ => C.Ret tt) in
        C.Exit
      | Some client_id =>
        ClientSocket.read client_id tt (fun _ content =>
        match content with
        | None => C.Ret None
        | Some content =>
          do! ClientSocket.write client_id content (fun _ =>
            Log.write content (fun _ => C.Ret tt)) in
          C.Ret None
        end)
      end).
End EchoServer.

(** * Extractions, made outside of any module. *)
Definition do_nothing := Extraction.run Memory.Nil DoNothing.program.
Extraction "extraction/doNothing" do_nothing.

Definition hello_world := Extraction.run Memory.Nil HelloWorld.program.
Extraction "extraction/helloWorld" hello_world.

Definition read_file := Extraction.run Memory.Nil ReadFile.program.
Extraction "extraction/readFile" read_file.

Definition echo_server := Extraction.run Memory.Nil EchoServer.program.
Extraction "extraction/echoServer" echo_server.
