Require Import ZArith.
Require Import List. Import ListNotations.

Inductive Instruction : Type :=
  | Nop
  | Push  (n : Z)
  | BCall (n : Z) (* How many things to pass as arguments *)
  | BRet
  | Add
  | Load
  | Store.

Inductive OpCode : Type :=
  | OpBCall
  | OpBRet
  | OpNop
  | OpPush
  | OpAdd
  | OpLoad
  | OpStore.

Definition opCodes := [
  OpBCall;
  OpBRet;
  OpNop;
  OpPush;
  OpAdd;
  OpLoad;
  OpStore].

Definition opCode_eq_dec : forall o1 o2 : OpCode,
  {o1 = o2} + {o1 <> o2}.
Proof. decide equality. Defined.

Definition opcode_of_instr (i : Instruction) : OpCode :=
  match i with
  | BCall _ => OpBCall
  | BRet    => OpBRet
  | Push  _ => OpPush
  | Nop     => OpNop
  | Add     => OpAdd
  | Load    => OpLoad
  | Store   => OpStore
end.

