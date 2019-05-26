From QuickChick Require Import QuickChick.

Require Import ZArith.
Require Import NPeano.
Require Import List.
Import ListNotations.
From QuickChick.ifcbasic Require Import Machine.

(* Overriding default instance to generate "in-bounds" things *)
Definition mem_length : Z := 10.

Definition gen_Z := choose (0,mem_length).

Definition gen_label := elements L [L; H].

Definition gen_atom := liftGen2 Atm gen_Z gen_label.

Definition gen_memory := vectorOf 10 gen_atom.

Definition is_atom_low (a : Atom) :=
  match a with
    | _ @ L => true
    | _     => false
  end.

Local Open Scope nat.

Definition ainstr (st : State) : G Instruction :=
  let '(St im m stk pc ) := st in
  let fix stack_length s :=
      match s with
        | _ :: s' => 1 + stack_length s'
        | _ => 0
      end in
  let sl := stack_length stk in
  let fix containsRet s :=
      match s with
        | _ ::: _ => true
        | _ :: s' => containsRet s'
        | _ => false
      end in
  let onLength len x := if leb x len then x else 0 in
  freq_ (returnGen Nop) [
              (1, returnGen Nop);
              (10, liftGen Push gen_Z);
              (if sl < 1 ? then 0 else 10, liftGen BCall (if beq_nat sl 0 then returnGen 0
                                  else choose (0, Z.of_nat sl-1))%Z);
              (if containsRet stk then 10 else 0, returnGen BRet);
              (if sl < 2 ? then 0 else 10, returnGen Add);
              (if sl < 1 ? then 0 else 10, returnGen Load);
              (if sl < 2 ? then 0 else 100, returnGen Store)].

Fixpoint gen_stack (n : nat) (onlyLow : bool) : G Stack :=
  (*
  let gen_atom :=
      if onlyLow then liftGen2 Atm gen_Z (returnGen L)
      else gen_atom
  in
   *)
  match n with
    | O => returnGen Mty
    | S n' =>
      freq_ (returnGen Mty) [
                  (10, liftGen2 Cons gen_atom (gen_stack n' onlyLow));
                  (4, bindGen gen_atom (fun pc =>
                       liftGen (RetCons pc) (gen_stack n' (is_atom_low pc))))]
  end.

Fixpoint gen_by_exec (t : table) (fuel : nat) (st : State) :=
  let '(St im m stk (Atm addr pcl)) := st in
  match fuel with
  | O => returnGen st
  | S fuel' =>
    match nth im addr with
    | Some Nop =>
      (* If it is a noop, generate *)
      bindGen (ainstr st) (fun i =>
      match upd im addr i with
      | Some im' =>
        let st' := St im' m stk (Atm addr pcl) in
        gen_by_exec t fuel' st'
      | None => returnGen st
      end)
    | Some i =>
      (* Existing instruction, execute *)
      match exec t st with
      | Some st' =>
        gen_by_exec t fuel' st'
      | None => returnGen st
      end
    | None =>
      (* Out of bounds, terminate *)
      returnGen st
    end
  end.

Require Import ExtLib.Structures.Monads.
Import MonadNotation.
Open Scope monad_scope.

Definition gen_state : G State :=
  let imem0 := replicate 10 Nop in
  pc <- gen_atom ;;
  mem <- gen_memory ;;
  stk <- gen_stack 10 (is_atom_low pc) ;;
  st' <- gen_by_exec default_table 20 (St imem0 mem stk pc) ;;
  ret st'.

From QuickChick.ifcbasic Require Import Generation.

Instance vary_atom' : Vary Atom :=
{|
  vary a :=
    let '(x @ l) := a in
    match l with
      | L => returnGen a
      | H => liftGen2 Atm gen_Z (returnGen H)
    end
|}.

Instance vary_mem' : Vary Mem :=
{|
  vary m := sequenceGen (map vary m)
|}.

Fixpoint vary_stack (s : Stack) (isLow : bool) : G Stack :=
  match s with
    | a :: s'  => if isLow then liftGen2 Cons (vary a) (vary_stack s' isLow)
                  else liftGen2 Cons gen_atom (vary_stack s' isLow)
    | (x@l) ::: s' =>
      match l with
        | L => liftGen (RetCons (x@l)) (vary_stack s' true)
        | H => liftGen2 RetCons (vary (x@l)) (vary_stack s' false)
      end
    | Mty => returnGen Mty
  end.

Import QcDefaultNotation.
Instance vary_state' : Vary State :=
{|
  vary st :=
    let '(St imem mem stk pc) := st in
    mem' <- vary mem ;;
    pc'  <- vary pc ;;
    let isLow := match pc with
                   | _ @ L => true
                   | _ @ H => false
                 end in
    if isLow then
      stk' <- vary_stack stk isLow ;;
      ret (St imem mem' stk' pc')
    else
      stk' <- vary_stack stk isLow ;;
      bindGen (@arbitrary bool _) (fun b : bool =>
      if b then
        extra_elem <- gen_atom ;;
        ret (St imem mem' (extra_elem :: stk') pc')
      else
        ret (St imem mem' stk' pc'))
|}.

Definition gen_variation_state' : G (@Variation State) :=
  bindGen gen_state (fun st =>
  bindGen (vary st) (fun st' =>
  returnGen (V st st'))).
