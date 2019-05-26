Set Warnings "-extraction-opaque-accessed,-extraction".
Set Warnings "-notation-overridden,-parsing".

Require Import Omega.
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssrnat ssrbool eqtype div.

From ExtLib Require Import
     Structures.Monad.
Import MonadNotation.
Local Open Scope monad_scope.

From SimpleIO Require Import SimpleIO.

From QuickChick Require Import RoseTrees RandomQC GenLow GenHigh SemChecker.
From QuickChick Require Import Show Checker State Classes.

Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import List.
Import ListNotations.

Require Import Recdef.

Require Import Arith.EqNat.

Import GenLow GenHigh.

Definition gte n m := Nat.leb m n.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Bullet Behavior "Strict Subproofs".

Record Args := MkArgs {
  replay     : option (RandomSeed * nat);
  maxSuccess : nat;
  maxDiscard : nat;
  maxShrinks : nat;
  maxSize    : nat;
  chatty     : bool
}.

Definition updMaxSize (a : Args) (x : nat) : Args := 
  let '(MkArgs r msc md msh msz c) := a in 
  MkArgs r msc md msh x c.

Definition updMaxSuccess (a : Args) (x : nat) : Args := 
  let '(MkArgs r msc md msh msz c) := a in 
  MkArgs r x md msh msz c.

Inductive Result :=
  | Success : nat -> nat -> list (string * nat) -> string -> Result
  | GaveUp  : nat -> list (string * nat) -> string -> Result
  | Failure : nat -> nat -> nat -> RandomSeed -> nat -> string ->
              list (string * nat) -> string -> Result
  | NoExpectedFailure : nat -> list (string * nat) -> string -> Result.

Definition isSuccess (r : Result) : bool :=
  match r with
    | Success _ _ _ _ => true
    | _         => false
  end.

(* Representing large constants in Coq is not a good idea... :) *)
Axiom defNumTests    : nat.
Extract Constant defNumTests    => "10000".
Axiom defNumDiscards : nat.
Extract Constant defNumDiscards => "(2 * defNumTests)".
Axiom defNumShrinks  : nat.
Extract Constant defNumShrinks  => "1000".
Axiom defSize        : nat.
Extract Constant defSize        => "7".

Definition stdArgs := MkArgs None defNumTests defNumDiscards
                             defNumShrinks defSize true.

Definition roundTo n m := mult (Nat.div n m) m.

Definition computeSize' (a : Args) (n : nat) (d : nat) : nat :=
  if (roundTo n (maxSize a) <= maxSuccess a) || (n >= maxSuccess a)
     || (maxSuccess a %| (maxSize a))
  then
    minn (n %% (maxSize a) + d %/ 10) (maxSize a)
  else
    minn ((n %% (maxSize a)) * maxSize a %/
      ((maxSuccess a) %% (maxSize a) + d %/ 10)) (maxSize a).

 Definition at0 (f : nat -> nat -> nat) (s : nat) (n d : nat) :=
  if andb (beq_nat n 0) (beq_nat d 0) then s
  else f n d.

Fixpoint prependToAll {A : Type} (sep : A) (ls : list A) : list A :=
  match ls with
    | nil => nil
    | h :: t => sep :: h :: prependToAll sep t
  end.

Definition intersperse {A : Type} (sep : A) (ls : list A) : list A :=
  match ls with
    | nil => nil
    | h :: t => h :: prependToAll sep t
  end.

Definition notNull (ls : list string) : bool :=
  match ls with
    | nil => false
    | _ => true
  end.

Fixpoint insertBy A (compare : A -> A -> bool) (x : A) (l : list A) : list A :=
  match l with
    | nil => x :: nil
    | h :: t => if compare x h then x :: l else h :: insertBy compare x t
  end.

Fixpoint insSortBy A (compare : A -> A -> bool) (l : list A) : list A :=
  match l with
    | nil => nil
    | h :: t => insertBy compare h (insSortBy compare t)
  end.

Local Open Scope string.
Fixpoint concatStr (l : list string) : string :=
  match l with
    | nil => ""
    | (h :: t) => h ++ concatStr t
  end.

Definition summary (st : State) : list (string * nat) :=
  let res := Map.fold (fun key elem acc => (key,elem) :: acc) (labels st) nil
  in insSortBy (fun x y => snd y <= snd x) res .

Definition doneTesting (st : State) (f : nat -> RandomSeed -> QProp) : Result :=
 if expectedFailure st then
    Success (numSuccessTests st + 1) (numDiscardedTests st) (summary st)
            ("+++ Passed " ++ (show (numSuccessTests st)) ++ " tests (" ++ (show (numDiscardedTests st)) ++ " discards)")
  else
    NoExpectedFailure (numSuccessTests st) (summary st)
                      ("*** Failed! Passed " ++ (show (numSuccessTests st))
                                             ++ " tests (expected Failure)").
  (* TODO: success st - labels *)

Definition giveUp (st : State) (_ : nat -> RandomSeed -> QProp) : Result :=
  GaveUp (numSuccessTests st) (summary st)
         ("*** Gave up! Passed only " ++ (show (numSuccessTests st)) ++ " tests"
          ++  newline ++ "Discarded: " ++ (show (numDiscardedTests st))).

Definition callbackPostTest (st : State) (res : Checker.Result) : nat :=
  match res with
  | MkResult o e r i s c t =>
    fold_left (fun acc callback =>
                 match callback with
                 | PostTest _ call =>
                   (call st (MkSmallResult o e r i s t)) + acc
                 | _ => acc
                 end) c 0
  end.
  

Definition callbackPostFinalFailure (st : State) (res : Checker.Result)
: nat :=
match res with
  | MkResult o e r i s c t =>
  fold_left (fun acc callback =>
               match callback with
                 | PostFinalFailure _ call =>
                   (call st (MkSmallResult o e r i s t)) + acc
                 | _ => acc
               end) c 0
end.

Fixpoint localMin (st : State) (r : Rose Checker.Result)
         {struct r} : (nat * Checker.Result) :=
  match r with
  | MkRose res ts =>
    let fix localMin' st ts {struct ts} :=
        match ts return (nat * Checker.Result) with
        | nil =>
          let zero := callbackPostFinalFailure st res in
          (numSuccessShrinks st + zero, res)
        | cons ((MkRose res' _) as r') ts' =>
          let zero := callbackPostTest st res in 
          match ok res' with
            | Some x =>
              let consistent_tags := 
                match result_tag res, result_tag res' with 
                | Some t1, Some t2 => if string_dec t1 t2 then true else false
                | None, None => true
                | _, _ => false
                end in
              if andb (negb x) consistent_tags then
                localMin (updSuccessShrinks st (fun x => x + 1 + zero))
                         r'
              else
                localMin' (updTryShrinks st (fun x => x + 1)) ts'
            | None =>
              localMin' (updTryShrinks st (fun x => x + 1)) ts'
          end
        end in
    localMin' st (force ts)
  end.

Fixpoint runATest (st : State) (f : nat -> RandomSeed -> QProp) (maxSteps : nat) :=
  if maxSteps is maxSteps'.+1 then
    let size := (computeSize st) (numSuccessTests st) (numDiscardedTests st) in
    let (rnd1, rnd2) := randomSplit (randomSeed st) in
    let test (st : State) :=
        if (gte (numSuccessTests st) (maxSuccessTests st)) then
          doneTesting st f
        else if (gte (numDiscardedTests st) (maxDiscardedTests st)) then
               giveUp st f
             else runATest st f maxSteps'
    in
    match st with
    | MkState mst mdt ms cs nst ndt ls e r nss nts =>
      match f size rnd1 with
      | MkProp (MkRose res ts) =>
        (* TODO: CallbackPostTest *)
        let res_cb := callbackPostTest st res in
        match res with
        | MkResult (Some x) e reas _ s _ t =>
          if x then (* Success *)
            let ls' := 
                match s with 
                | nil => ls 
                | _ => 
                  let s_to_add := 
                      ShowFunctions.string_concat 
                        (ShowFunctions.intersperse " , "%string s) in
                  match Map.find s_to_add ls with 
                    | None   => Map.add s_to_add (res_cb + 1) ls
                    | Some k => Map.add s_to_add (k+1) ls
                  end 
                end in
(*                  
            let ls' := fold_left (fun stamps stamp =>
                                    let oldBind := Map.find stamp stamps in
                                    match oldBind with
                                    | None   => Map.add stamp 1 stamps
                                    | Some k => Map.add stamp (k+1) stamps
                                    end
                                 ) s ls in*)
            test (MkState mst mdt ms cs (nst + 1) ndt ls' e rnd2 nss nts)
          else (* Failure *)
            let tag_text := 
                match t with 
                | Some s => "Tag: " ++ s ++ nl
                | _ => "" 
                end in 
            let pre : string := (if expect res then "*** Failed "
                                 else "+++ Failed (as expected) ")%string in
            let (numShrinks, res') := localMin st (MkRose res ts) in
            let suf := ("after " ++ (show (S nst)) ++ " tests and "
                                 ++ (show numShrinks) ++ " shrinks. ("
                                 ++ (show ndt) ++ " discards)")%string in
            (* TODO: Output *)
            if (negb (expect res)) then
              Success (nst + 1) ndt (summary st) (tag_text ++ pre ++ suf)
            else
              Failure (nst + 1) numShrinks ndt r size (tag_text ++ pre ++ suf) (summary st) reas
        | MkResult None e reas _ s _ t =>
          (* Ignore labels of discarded tests? *)
          let ls' :=
              match s with
              | nil => ls
              | _ =>
                let s_to_add :=
                    "(Discarded) " ++ ShowFunctions.string_concat
                                    (ShowFunctions.intersperse " , "%string s) in
                match Map.find s_to_add ls with
                | None   => Map.add s_to_add (res_cb + 1) ls
                | Some k => Map.add s_to_add (k+1) ls
                end
              end in
          test (MkState mst mdt ms cs nst ndt.+1 ls' e rnd2 nss nts)
        end
      end
    end
  else giveUp st f.

Definition test (st : State) (f : nat -> RandomSeed -> QProp) : Result :=
  if (gte (numSuccessTests st) (maxSuccessTests st)) then
    doneTesting st f
  else if (gte (numDiscardedTests st) (maxDiscardedTests st)) then
         giveUp st f
  else
    let maxSteps := maxSuccessTests st + maxDiscardedTests st in
    runATest st f maxSteps.

Require Import ZArith.

(* ZP: This was quickCheckResult before but since we always return result
       return result there is no reason for such distinction *)
Definition quickCheckWith {prop : Type} {_ : Checkable prop}
           (a : Args) (p : prop) : Result :=
  (* ignore terminal - always use trace :D *)
  let (rnd, computeFun) :=
      match replay a with
        | Some (rnd, s) => (rnd, at0 (computeSize' a) s)
        | None          => (newRandomSeed, computeSize' a)
        (* make it more random...? need IO action *)
      end in
  test (MkState (maxSuccess a)  (* maxSuccessTests   *)
                (maxDiscard a)  (* maxDiscardTests   *)
                (maxShrinks a)  (* maxShrinks        *)
                computeFun      (* computeSize       *)
                0               (* numSuccessTests   *)
                0               (* numDiscardTests   *)
                (Map.empty nat) (* labels            *)
                false           (* expectedFailure   *)
                rnd             (* randomSeed        *)
                0               (* numSuccessShrinks *)
                0               (* numTryShrinks     *)
       ) (run (checker p)).

Fixpoint showCollectStatistics (l : list (string * nat)) :=
  match l with
    | nil => ""
    | cons (s,n) l' =>
      show n ++ " : " ++ s ++ newline ++ showCollectStatistics l'
  end.

Instance showResult : Show Result := Build_Show _ (fun r =>
  match r with
  | Success _ _ l s => showCollectStatistics l ++ s
  | GaveUp _ l s => showCollectStatistics l ++ s
  | Failure _ _ _ _ _ s l _ => showCollectStatistics l ++ s
  | NoExpectedFailure _ l s => showCollectStatistics l ++ s
  end ++ newline).

Definition quickCheck {prop : Type} {_ : Checkable prop}
           (p : prop) : Result :=
  quickCheckWith stdArgs p.

(* A named test property with parameters. *)
Inductive Test : Type :=
| QuickChickTest : string -> Args -> Checker -> Test.

(* Make a named test property with explicit parameters. *)
Definition qc_ {prop : Type} {_ : Checkable prop}
           (name : string) (a : Args) (p : prop) : Test :=
  QuickChickTest name a (checker p).

(* Make a named test property with implicit default parameters. *)
Definition qc {prop : Type} {_ : Checkable prop}
           (name : string) (p : prop) : Test :=
  qc_ name stdArgs (checker p).

(* IO action that runs the tests. *)
Fixpoint testRunner (tests : list Test) : IO unit :=
  match tests with
  | [] => ret tt
  | QuickChickTest name args test :: tests =>
    print_endline ("Checking " ++ name ++ "...");;
    print_endline (show (quickCheckWith args test));;
    testRunner tests
  end.

(* Actually run the tests. (Only meant for extraction.) *)
Definition runTests (tests : list Test) : io_unit :=
  IO.unsafe_run (testRunner tests).
