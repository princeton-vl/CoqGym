From QuickChick Require Import QuickChick.

Require Import ZArith.
Require Import NPeano.
Require Import List.
Import ListNotations.
From QuickChick.ifcbasic Require Import Machine Printing Generation.

Set Bullet Behavior "Strict Subproofs".

Local Open Scope nat.

(* Overriding default instance to generate "in-bounds" things *)
(* Definition gen_Z := choose (0,1). *)
Inductive good_Z : Z -> Prop := 
  | GoodZ0 : good_Z 0
  | GoodZ1 : good_Z 1.

Derive ArbitrarySizedSuchThat for (fun z => good_Z z).

(* Definition gen_label := elements L [L; H]. *)
Derive Arbitrary for Label.

(* Definition gen_atom := liftGen2 Atm gen_Z gen_label. *)
Inductive good_atom : Atom -> Prop :=
  | GoodAtom : forall z l, good_Z z -> good_atom (Atm z l).
Derive ArbitrarySizedSuchThat for (fun a => good_atom a).

(* Definition gen_memory := vectorOf 2 gen_atom. *)
Inductive good_mem : Mem -> Prop :=
  | GoodMem : forall a1 a2, good_atom a1 -> good_atom a2 -> good_mem [a1 ; a2].
Derive ArbitrarySizedSuchThat for (fun m => good_mem m).

Definition is_atom_low (a : Atom) :=
  match a with
    | _ @ L => true
    | _     => false
  end.

(*
Fixpoint gen_stack (n : nat) (onlyLow : bool) : G Stack :=
  (* There is no invariant that says this. Why is this here? *)
  (*
  let gen_atom :=
      if onlyLow then liftGen2 Atm gen_Z (returnGen L)
      else gen_atom
  in
   *)
  match n with
    | O => returnGen Mty
    | S n' =>
      frequency (returnGen Mty) [
                  (10, liftGen2 Cons gen_atom (gen_stack n' onlyLow));
                  (4, bindGen gen_atom (fun pc =>
                       liftGen (RetCons pc) (gen_stack n' (is_atom_low pc))))]
  end.
*)
(* I could write this without the nat to exploit the default size! *)
Inductive good_stack : nat -> Stack -> Prop :=
| GoodStackMty  : good_stack 0 Mty
| GoodStackCons : forall n a s , good_atom a  -> good_stack n s -> good_stack (S n) (a  :: s)
| GoodStackRet  : forall n pc s, good_atom pc -> good_stack n s -> good_stack (S n) (RetCons pc s).

QuickChickWeights [(GoodStackCons, 10); (GoodStackRet, 4)].
Derive ArbitrarySizedSuchThat for (fun s => good_stack n s).

(*
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
  frequency (returnGen Nop) [
              (1, returnGen Nop);
              (10, liftGen Push gen_Z);
              (10, liftGen BCall (if beq_nat sl 0 then returnGen 0
                                  else choose (0, Z.of_nat sl-1))%Z);
              (if containsRet stk then 10 else 0, returnGen BRet);
              (10, returnGen Add);
              (10, returnGen Load);
              (100, returnGen Store)].
*)
Inductive contains_ret : Stack -> Prop := 
  | RetHere  : forall pc s, contains_ret (RetCons pc s)
  | RetLater : forall a  s, contains_ret s -> contains_ret (a :: s).
Instance dec_contains_ret (s : Stack) : Dec (contains_ret s).
Proof.
  dec_eq.
  induction s.
  - right => H; inversion H.
  - destruct IHs.
    + left; constructor; auto.
    + right => H; inversion H; eauto.
  - left; constructor; auto.
Defined.

Inductive stack_length : Stack -> nat -> Prop :=
| LenMty  : stack_length Mty 0
| LenRet  : forall pc s, stack_length (pc :: s) 0
| LenCons : forall a s n, stack_length s n -> stack_length (a :: s) (S n).
Derive ArbitrarySizedSuchThat for (fun n => stack_length s n).

Inductive between (x y : Z) (z : nat) : Prop :=
| Bet : (x < y -> y < Z.of_nat z -> between x y z)%Z.
Instance genST_bet x z : GenSizedSuchThat Z (fun y => between x y z) := 
{|
  arbitrarySizeST n := liftGen Some (choose (x, Z.of_nat z))
|}.

Inductive good_instr (stk : Stack) : Instruction -> Prop :=
  | GoodNop   : good_instr stk Nop
  | GoodPush  : forall z, good_Z z -> good_instr stk (Push z)
  | GoodCall  : forall z n, 
      stack_length stk n ->
      between 0 z n ->
      good_instr stk (BCall z)
  | GoodRet   : contains_ret stk -> good_instr stk BRet 
  | GoodAdd   : good_instr stk Add 
  | GoodLoad  : good_instr stk Load
  | GoodStore : good_instr stk Store.

QuickChickWeights [ (GoodNop, 1)
                  ; (GoodPush, 10)
                  ; (GoodCall, 10)
                  ; (GoodRet, 10)
                  ; (GoodAdd, 10)
                  ; (GoodLoad, 10)
                  ; (GoodStore, 100) ].
Derive ArbitrarySizedSuchThat for (fun i => good_instr stk i). 

(*
Definition gen_state : G State :=
  let imem0 := [Nop; Nop] in
  bindGen gen_atom (fun pc =>
  bindGen gen_memory (fun mem =>
  bindGen (gen_stack 4 (is_atom_low pc)) (fun stk =>
  bindGen (ainstr (St imem0 mem stk pc)) (fun i =>
  returnGen (St [i;i] mem stk pc))))).
*)
Inductive good_state : State -> Prop :=
  | GoodState : 
      forall i m stk pc, 
        good_atom pc ->
        good_mem m ->
        good_stack 4 stk ->
        good_instr stk i ->
        good_state (St [i;i] m stk pc).
Derive ArbitrarySizedSuchThat for (fun st => good_state st).        

(* Sample (@arbitrarySizeST _ (fun st => good_state st) _ 10).*)

(*
Class Vary (A : Type) := {
  vary : A -> G A
}.
*)

(*
Instance vary_atom : Vary Atom :=
{|
  vary a :=
    let '(x @ l) := a in
    match l with
      | L => returnGen a
      | H => liftGen2 Atm gen_Z (returnGen H)
    end
|}.
*)
Inductive variation_atom : Atom -> Atom -> Prop :=
| VaryAtomL : forall x  , variation_atom (x @ L) (x @ L)
| VaryAtomH : forall x y, good_Z y -> variation_atom (x @ H) (y @ H).
Derive ArbitrarySizedSuchThat for (fun y => variation_atom x y).

(*
Instance vary_mem : Vary Mem :=
{|
  vary m := sequenceGen (map vary m)
|}.
*)
Inductive variation_mem : Mem -> Mem -> Prop :=
| VaryMemNil  : variation_mem [] []
| VaryMemCons : forall a a' m m', variation_atom a a' ->
                                   variation_mem m m'  ->
                                   variation_mem (cons a m) (cons a' m').
Derive ArbitrarySizedSuchThat for (fun m2 => variation_mem m1 m2).    

(*
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
*)
Inductive variation_stack : Stack -> Stack -> Prop :=
  | VaryStkMty  : variation_stack Mty Mty
  | VaryStkCons : forall a a' s s', variation_atom a a' ->
                                    variation_stack s s' ->
                                    variation_stack (a :: s) (a' :: s')
  | VaryStkRet  : forall a a' s s', variation_atom a a' ->
                                    variation_stack s s' ->
                                    variation_stack (RetCons a s) (RetCons a' s').
Derive ArbitrarySizedSuchThat for (fun s2 => variation_stack s1 s2).

(*
Instance vary_state : Vary State :=
{|
  vary st :=
    let '(St imem mem stk pc) := st in
    bindGen (vary mem) (fun mem' =>
    bindGen (vary pc)  (fun pc' =>
    let isLow := match pc with
                   | _ @ L => true
                   | _ @ H => false
                 end in
    if isLow then
      bindGen (vary_stack stk isLow) (fun stk' =>
      returnGen (St imem mem' stk' pc'))
    else
      bindGen (vary_stack stk isLow) (fun stk' =>
      bindGen gen_atom (fun extra_elem =>
      returnGen (St imem mem' (extra_elem :: stk') pc')))))
|}.
*)

Inductive variation_high_stack : Atom -> Stack -> Stack -> Prop :=
| VaryStkAny : forall pc stk stk', variation_stack stk stk' ->
                                  variation_high_stack pc stk stk'
| VarystkHigh : forall pcx stk stk' a,
                       variation_stack stk stk' ->
                       good_atom a ->
                       variation_high_stack (pcx @ H) stk (a :: stk').
Derive ArbitrarySizedSuchThat for (fun stk' => variation_high_stack pc stk stk').

Inductive variation_state : State -> State -> Prop :=
  | VaryState : forall imem mem stk pc mem' stk' pc',
      variation_mem mem mem' ->
      variation_atom pc pc' ->
      variation_high_stack pc stk stk' ->
      variation_state (St imem mem stk pc) (St imem mem' stk' pc').
Derive ArbitrarySizedSuchThat for (fun st' => variation_state st st').

Definition gen_variation_state_derived : G (option (@Variation State)) :=
  bindGenOpt (genST (fun st => good_state st)) (fun st => 
  bindGenOpt (genST (fun st' => variation_state st st')) (fun st' =>
  returnGen (Some (V st st')))).                                                            
(*
  bindGen gen_state (fun st =>
  bindGen (vary st) (fun st' =>
  returnGen (V st st'))).
*)