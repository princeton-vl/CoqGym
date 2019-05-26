Require Import ZArith.
Require Import List. Import ListNotations.
Require Import MSetPositive.

From QuickChick.ifcbasic Require Export Rules Instructions.

Open Scope Z_scope.
Open Scope bool_scope.

(** * Basic List manipulation *)

(* [nth l n] returns the [n]th element of [l] if [0 <= n < Zlength l] *)
Definition nth {A:Type} (l:list A) (n:Z) : option A :=
  if Z_lt_dec n 0 then None
  else nth_error l (Z.to_nat n).

(* [upd_nat l n a] returns a list [l'] that is pointwise equal to [l], except the [n]th
    element that is now [a]. Only suceeds if [n < length l] *)
Fixpoint upd_nat {A:Type} (l:list A) (n:nat) (a:A) : option (list A) :=
  match l with
    | nil => None
    | x::q =>
      match n with
        | O => Some (a::q)
        | S p =>
          match upd_nat q p a with
            | None => None
            | Some q' => Some (x::q')
          end
      end
  end.

(* [upd l n a] returns a list [l'] that is pointwise equal to [l], except the [n]th
    element that is now [a]. Only suceeds if [0 <= n < Zlength l] *)
Definition upd {A:Type} (l:list A) (n:Z) (a:A) : option (list A) :=
  if Z_lt_dec n 0 then None
  else upd_nat l (Z.to_nat n) a.

Fixpoint replicate {A:Type} (n:nat) (a:A) : list A :=
  match n with
  | O => nil
  | S n' => a :: replicate n' a
  end.

Definition zreplicate {A:Type} (n:Z) (a:A) : option (list A) :=
  if Z_lt_dec n 0 then None
  else Some (replicate (Z.to_nat n) a).

(** * Machine definition *)

Inductive Atom : Type := Atm (x:Z) (l:Label).
Infix "@" := Atm (no associativity, at level 50).

Definition pc_lab (pc : Atom) : Label :=
  let (_,l) := pc in l.
Notation "'∂' pc" := (pc_lab pc) (at level 0).

Inductive Stack :=
  | Mty                         (* empty stack *)
  | Cons (a:Atom) (s:Stack)     (* stack atom cons *)
  | RetCons (pc:Atom) (s:Stack) (* stack frame marker cons *)
.
Infix "::"  := Cons (at level 60, right associativity).
Infix ":::" := RetCons (at level 60, right associativity).

Fixpoint app_stack (l:list Atom) (s:Stack) : Stack :=
  match l with
    | nil => s
    | cons a q => a::(app_stack q s)
  end.
Infix "$" := app_stack (at level 60, right associativity).

Definition IMem := list Instruction.
Definition Mem  := list Atom.
Record State := St {
  st_imem  : IMem ; (* instruction memory *)
  st_mem   : Mem  ; (* memory *)
  st_stack : Stack; (* operand stack *)
  st_pc    : Atom   (* program counter *)
}.

Definition labelCount (c:OpCode) : nat :=
  match c with
  | OpBCall   => 1
  | OpBRet    => 2
  | OpNop     => 0
  | OpPush    => 0
  | OpAdd     => 2
  | OpLoad    => 2
  | OpStore   => 3
end%nat.

Definition table := forall op, AllowModify (labelCount op).

Definition default_table : table := fun op =>
  match op with
  | OpBCall   =>  ≪ TRUE , LabPC , JOIN Lab1 LabPC≫
  | OpBRet    =>  ≪ TRUE , JOIN Lab2 LabPC , Lab1 ≫
  | OpNop     =>  ≪ TRUE , __ , LabPC ≫
  | OpPush    =>  ≪ TRUE , BOT , LabPC ≫
  | OpAdd     =>  ≪ TRUE , JOIN Lab1 Lab2, LabPC ≫
  | OpLoad    =>  ≪ TRUE , JOIN Lab1 Lab2 , LabPC ≫
  | OpStore   =>  ≪ LE (JOIN Lab1 LabPC) Lab3, JOIN LabPC (JOIN Lab1 Lab2) , LabPC ≫
end.

Definition run_tmr (t : table) (op: OpCode)
  (labs:Vector.t Label (labelCount op)) (pc: Label)
   : option (option Label * Label) :=
  let r := t op in
  apply_rule r labs pc.

Definition bind (A B:Type) (f:A->option B) (a:option A) : option B :=
    match a with
      | None => None
      | Some a => f a
    end.
Notation "'do' X <- A ; B" := (bind _ _ (fun X => B) A)
                    (at level 200, X ident, A at level 100, B at level 200).
Notation "'do' X : T <- A ; B" := (bind _ _ (fun X : T => B) A)
                    (at level 200, X ident, A at level 100, B at level 200).

Fixpoint insert_nat (s:Stack) (n:nat) (a:Atom) : option Stack :=
  match n,s with
    | O, _ => Some (a:::s)
    | S n', x :: xs =>
      do s' <- insert_nat xs n' a;
      Some (x :: s')
    | _, _ => None
  end.

Fixpoint findRet (s:Stack) : option (Atom * Stack) :=
  match s with
    | x ::: s' => Some (x,s')
    | x :: s'  => findRet s'
    | Mty      => None
  end.

Definition insert (s:Stack) (n:Z) (a:Atom) : option Stack :=
  if Z_lt_dec n 0 then None
  else insert_nat s (Z.to_nat n) a.

Definition lookupInstr (st : State) : option Instruction :=
  let '(St μ _ _ (pc@_)) := st in nth μ pc.

Definition exec (t : table) (st:State) : option State :=
  do instr <- lookupInstr st;
  match instr, st with
    | BCall n, St μ m (x @ l :: σ) (xpc@lpc) =>
      match run_tmr t OpBCall <|l|> lpc with
        | Some (Some rl, rpcl) =>
          let pc' := x @ rpcl in
          let ret_pc := (xpc + 1 @ rl) in
          do σ' <- insert σ n ret_pc;
          Some (St μ m σ' pc')
        | _ => None
      end
    | BRet, St μ m ((ax@al)::σ) (xpc@lpc) =>
      do tmp <- findRet σ;
      let '(xrpc @ lrpc, σ') := tmp in
      match run_tmr t OpBRet <|lrpc; al|> lpc with
        | Some (Some rl, rpcl) =>
          let pc' := xrpc @ rpcl in
          Some (St μ m ((ax@rl)::σ') pc')
        | _ => None
      end
    | Load, St μ m ((x @ l) :: σ) (xpc@lpc) =>
     do a <- nth m x;
     let '(ax @ al) := a in
     match run_tmr t OpLoad <|al; l|> lpc with
       | Some (Some rl, rpcl) =>
         Some (St μ m ((ax @ rl)::σ) ((xpc+1) @ rpcl))
       | _ => None
     end
    | Store, St μ m ((x @ lx) :: (a@la) :: σ) (xpc@lpc) =>
      do inMem <- nth m x;
      match run_tmr t OpStore <|lx; la; ∂inMem|> lpc with
        | Some (Some rl, rpcl) =>
          do m' <- upd m x (a@rl);
          Some (St μ m' σ ((xpc+1)@rpcl))
        | _ => None
      end
    | Push r, St μ m σ (xpc@lpc) =>
      match run_tmr t OpPush <||> lpc with
        | Some (Some rl, rpcl) =>
          Some (St μ m ((r@rl)::σ) ((xpc+1)@rpcl))
        | _ => None
      end
    | Nop, St μ m σ (xpc@lpc) =>
      match run_tmr t OpNop <||> lpc with
        | Some (_, rpcl) =>
          Some (St μ m σ ((xpc+1)@rpcl))
        | _ => None
      end
    | Add, St μ m ((x @ lx) :: (y @ ly) :: σ) (xpc@lpc) =>
      match run_tmr t OpAdd <|lx ; ly|> lpc with 
      | Some (Some rl, rpcl) =>
        Some (St μ m (((x + y) @ rl) :: σ) ((xpc+1)@rpcl))
      | _ => None
      end
    | _,_ => None
  end.

Fixpoint execN (t : table) (n : nat) (s : State) : list State :=
  match n with
    | O => [s]
    | S n' =>
      match exec t s with
        | Some s' => s :: execN t n' s'
        | None => s :: nil
      end
  end%list.


