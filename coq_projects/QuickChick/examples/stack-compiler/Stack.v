Set Warnings "-extraction-opaque-accessed,-extraction".
Set Warnings "-notation-overridden,-parsing".

From QuickChick Require Import QuickChick.
Require Import Arith List. Import ListNotations.

Require Import Stack.Exp.

(* Instructions for our stack machine *)
Inductive sinstr : Type :=
| SPush : nat -> sinstr
| SPlus : sinstr
| SMinus : sinstr
| SMult : sinstr.

(* Execution *)
Fixpoint execute (stack : list nat) (prog : list sinstr) : list nat :=
  match (prog, stack) with
  | (nil,             _           ) => stack
  | (SPush n::prog',  _           ) => execute (n::stack) prog'
  | (SPlus::prog',    m::n::stack') => execute ((m+n)::stack') prog'
  | (SMinus::prog',   m::n::stack') => execute ((m-n)::stack') prog'
  | (SMult::prog',    m::n::stack') => execute ((m*n)::stack') prog'
  | (_::prog',        _           ) => execute stack prog'
  end.

(* Compilation... *)
Fixpoint compile (e : exp) : list sinstr :=
  match e with
  (* TODO: WRITE DURING TUTORIAL! *)
  | _ => nil
  end.

Definition compile_correct (e : exp) := (execute [] (compile e)) = [eval e]?.
(*! QuickChick compile_correct. *)