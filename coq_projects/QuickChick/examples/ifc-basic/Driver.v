From QuickChick Require Import QuickChick.
Import GenLow GenHigh.

Require Import List. Import ListNotations.

From QuickChick.ifcbasic Require Import Machine Printing Generation Indist DerivedGen.
From QuickChick.ifcbasic Require GenExec.

Require Import Coq.Strings.String.
Local Open Scope string.
Definition SSNI (t : table) (v : @Variation State) : Checker  :=
  let '(V st1 st2) := v in
  let '(St _ _ _ (_@l1)) := st1 in
  let '(St _ _ _ (_@l2)) := st2 in
  match lookupInstr st1 with
    | Some i =>     collect (show i) (  
  if indist st1 st2 then
    match l1, l2 with
      | L,L  =>
        match exec t st1, exec t st2 with
          | Some st1', Some st2' =>
(*
            whenFail ("Initial states: " ++ nl ++ show_pair st1 st2 ++ nl
                        ++ "Final states: " ++ nl ++ show_pair st1' st2' ++nl)
*)
            (* collect ("L -> L")*) (checker (indist st1' st2'))
          | _, _ => (* collect "L,L,FAIL" true *) checker rejected
        end
      | H, H =>
        match exec t st1, exec t st2 with
          | Some st1', Some st2' =>
            if is_atom_low (st_pc st1') && is_atom_low (st_pc st2') then
              (* whenFail ("Initial states: " ++ nl ++ show_pair st1 st2 ++ nl
                        ++ "Final states: " ++ nl ++ show_pair st1' st2' ++nl) *)
              (* collect ("H -> L")*) (checker (indist st1' st2') )
            else if is_atom_low (st_pc st1') then
                   (* whenFail ("States: " ++ nl ++ show_pair st2 st2' ++ nl )*)
              (* collect ("H -> H")*) (checker (indist st2 st2'))
            else
(*            whenFail ("States: " ++ nl ++ show_pair st1 st1' ++ nl )*)
              (* collect ("H -> H")*) (checker (indist st1 st1'))
          | _, _ => checker rejected
        end
      | H,_ =>
        match exec t st1 with
          | Some st1' =>
(*             whenFail ("States: " ++ nl ++ show_pair st1 st1' ++ nl )*)
                      (* collect "H -> H"*) (checker (indist st1 st1'))
          | _ => (*collect "H,_,FAIL" true *) checker rejected
        end
      | _,H =>
        match exec t st2 with
          | Some st2' =>
(*             whenFail ("States: " ++ nl ++ show_pair st2 st2' ++ nl )*)
                      (* collect "H -> H"*) (checker (indist st2 st2'))
          | _ => (*collect "L,H,FAIL" true *) checker rejected
        end
    end
  else (* collect "Not indist!" true*)  checker rejected
               )
    | _ => checker rejected
  end.

Definition prop_SSNI t : Checker :=
  forAllShrink gen_variation_state (fun _ => nil)
   (SSNI t : Variation -> G QProp).

Definition prop_SSNI_derived t : Checker :=
  forAllShrink gen_variation_state_derived (fun _ => nil)
               (fun mv => 
                  match mv with 
                  | Some v => SSNI t v
                  | _ => checker tt
                  end).

Definition prop_gen_indist :=
  forAllShrink gen_variation_state (fun _ => nil)
               (fun v => let '(V st1 st2) := v in indist st1 st2).

Definition prop_gen_indist_derived :=
  forAllShrink (gen_variation_state_derived) (fun _ => nil)
               (fun mv => 
                  match mv with 
                  | Some (V st1 st2) => indist st1 st2 
                  | _ => true
                  end).

Extract Constant defNumDiscards => "30000".
QuickCheck (prop_SSNI default_table).
QuickCheck (prop_SSNI_derived default_table).

Axiom numTests : nat.
Extract Constant numTests => "10000".

Fixpoint MSNI (fuel : nat) (t : table) (v : @Variation State) : Checker  :=
  let '(V st1 st2) := v in
  let '(St _ _ _ (_@l1)) := st1 in
  let '(St _ _ _ (_@l2)) := st2 in
  match fuel with
  | O => checker true
  | S fuel' => 
  match lookupInstr st1 with
    | Some i =>     collect (show i) (  
  if indist st1 st2 then
    match l1, l2 with
      | L,L  =>
        match exec t st1, exec t st2 with
          | Some st1', Some st2' =>
(*
            whenFail ("Initial states: " ++ nl ++ show_pair st1 st2 ++ nl
                        ++ "Final states: " ++ nl ++ show_pair st1' st2' ++nl)
*)
            (* collect ("L -> L")*)
            if indist st1' st2' then
              MSNI fuel' t (V st1' st2')
            else
              checker false
          | _, _ => (* collect "L,L,FAIL" true *) checker true
        end
      | H, H =>
        match exec t st1, exec t st2 with
          | Some st1', Some st2' =>
            if is_atom_low (st_pc st1') && is_atom_low (st_pc st2') then
              (* whenFail ("Initial states: " ++ nl ++ show_pair st1 st2 ++ nl
                        ++ "Final states: " ++ nl ++ show_pair st1' st2' ++nl) *)
              (* collect ("H -> L")*)
              if indist st1' st2' then
                MSNI fuel' t (V st1' st2')
              else
                checker false
            else if is_atom_low (st_pc st1') then
                   (* whenFail ("States: " ++ nl ++ show_pair st2 st2' ++ nl )*)
                   (* collect ("H -> H")*)
              if indist st2 st2' then
                (* Ensure still a variation by not executing st1 *)
                MSNI fuel' t (V st1 st2') 
              else checker false
            else
              if indist st1 st1' then
                MSNI fuel' t (V st1' st2)
              else checker false
              (*            whenFail ("States: " ++ nl ++ show_pair st1 st1' ++ nl )*)
              (* collect ("H -> H")*) 
          | _, _ => checker true
        end
      | H,_ =>
        match exec t st1 with
        | Some st1' =>
          if indist st1 st1' then
            MSNI fuel' t (V st1' st2)
          else
            checker false
          | _ => (*collect "H,_,FAIL" true *) checker true
        end
      | _,H =>
        match exec t st2 with
        | Some st2' =>
          if indist st2 st2' then
            MSNI fuel' t (V st1 st2')
          else checker false
        | _ => (*collect "L,H,FAIL" true *) checker true
        end
    end
  else checker rejected
(*    whenFail ("Indist with states: " ++ nl ++ show_pair st1 st2 ++ nl ++ " after steps: " ++ show fuel ++ nl) (checker false) *)
    )         
    | _ => checker rejected
  end
  end.

Definition prop_MSNI t : Checker :=
  forAllShrink GenExec.gen_variation_state' (fun _ => nil)
   (MSNI 20 t : Variation -> G QProp).

QuickCheck (prop_MSNI default_table).
(* QuickCheck (prop_SSNI_derived default_table).*)


(*
Definition prop_SSNI_derived t : Checker :=
  forAllShrink gen_variation_state_derived (fun _ => nil)
               (fun mv => 
                  match mv with 
                  | Some v => SSNI t v
                  | _ => checker tt
                  end).
*)


Definition myArgs : Args :=
  let '(MkArgs rp mSuc md mSh mSz c) := stdArgs in
  MkArgs rp numTests md mSh mSz c.

From QuickChick Require Import Mutate MutateCheck.

Instance mutateable_table : Mutateable table :=
{|
  mutate := mutate_table
|}.

Require Import ZArith.




Definition testMutantX n :=
  match nth (mutate_table default_table) n with
    | Some t => prop_SSNI t
    | _ => checker tt 
  end.

MutateCheckWith myArgs default_table
    (fun t => (forAllShrinkShow
      gen_variation_state (fun _ => nil) (fun _ => "")
      (SSNI t ))).

MutateCheckWith myArgs default_table
    (fun t => (forAllShrinkShow
      GenExec.gen_variation_state' (fun _ => nil) (fun _ => "")
      (MSNI 20 t ))).

MutateCheckWith myArgs default_table
    (fun t => (forAllShrinkShow
      (gen_variation_state_derived) (fun _ => nil) (fun _ => "")
      (fun mv => 
         match mv with 
         | Some v => SSNI t v 
         | None => checker tt
         end
    ))).

(*
Eval lazy -[labelCount helper] in
  nth (mutate_table default_table) 2. *)

(*
Definition st1 :=
  St [Store; Store] [0 @ L] (0 @ L :: 0 @ H :: Mty) (0 @ L).
Definition st2 :=
  St [Store; Store] [0 @ L] (0 @ L :: 1 @ H :: Mty) (0 @ L).
Definition ex_indist : indist st1 st2 = true. auto. Qed.

Definition st1' :=
  St [Add; Add] [0 @ L] (0 @ L :: 0 @ H :: Mty) (0 @ L).
Definition st2' :=
  St [Add; Add] [0 @ L] (0 @ L :: 1 @ H :: Mty) (0 @ L).
Definition ex_indist' : indist st1' st2' = true. auto. Qed.

Definition ex_test :=
  match nth (mutate_table default_table) 8 with
    | Some t => SSNI t (V st1' st2')
    | _ => checker tt
  end.

Eval compute in exec default_table st1'.
QuickCheck ex_test.
QuickCheck (testMutantX 18).
*)