From QuickChick Require Import QuickChick.
Require Import ZArith.
Require Import List.

From QuickChick.ifcbasic Require Import Machine.

Fixpoint forallb2 {A : Type} (f : A -> A -> bool) (l1 l2 :list A) : bool :=
  match l1, l2 with
    | nil, nil => true
    | cons h1 t1, cons h2 t2 => f h1 h2 && forallb2 f t1 t2
    | _, _ => false
  end.

(* Indistinguishability type class *)
Class Indist (A : Type) : Type :=
{
  indist : A -> A -> bool
}.

Instance indist_atom : Indist Atom :=
{|
  indist a1 a2 :=
    let '(x1@l1) := a1 in
    let '(x2@l2) := a2 in
    match l1, l2 with
      | L, L => Z.eqb x1 x2
      | H, H => true
      | _, _ => false
    end
|}.

Instance indist_mem : Indist Mem :=
{|
  indist m1 m2 := forallb2 indist m1 m2
|}.

Fixpoint cropTop (s:Stack) : Stack :=
  match s with
    | Mty        => Mty
    | x::s'      => cropTop s'
    | (x@H:::s') => cropTop s'
    | (_@L:::_)  => s
  end.

(* Assumes stacks have been cropTopped! *)
Instance indist_stack : Indist Stack :=
{|
  indist s1 s2 :=
    let fix aux s1 s2 :=
        match s1, s2 with
          | a1::s1', a2::s2' => indist a1 a2 && aux s1' s2'
          | a1:::s1', a2:::s2' => indist a1 a2 && aux s1' s2'
          | Mty, Mty => true
          | _, _ => false
        end
    in aux s1 s2
|}.

Instance indist_state : Indist State :=
{|
  indist st1 st2 :=
    let '(St imem1 mem1 stk1 pc1) := st1 in
    let '(St imem2 mem2 stk2 pc2) := st2 in
    if negb (indist mem1 mem2) then (* trace "Memory" *) false
    else if negb (indist pc1 pc2) then (* trace "PC" *) false
    else let (stk1',stk2') :=
           match pc1 with
             | _ @ H => (cropTop stk1, cropTop stk2)
             | _ => (stk1, stk2)
           end in
    if negb (indist stk1' stk2') then (* trace "Stack" *) false
    else true
|}.

