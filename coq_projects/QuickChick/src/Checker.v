Set Implicit Arguments.

Require Import List.
Require Import Coq.Strings.String.

Require Import RoseTrees.
Require Import Show.
Require Import State.
Require Import GenLow GenHigh.
Require Import Classes.
Require Import DependentClasses.

Import GenLow GenHigh.

(* Note : Simple Callbacks fall under strict positivity of result... *)
Inductive CallbackKind :=
| Counterexample
| NotCounterexample.

Inductive SmallResult :=
  MkSmallResult : option bool -> bool -> string -> bool ->
                  list string -> option string -> SmallResult.

Inductive Callback : Type :=
| PostTest :
    CallbackKind -> (State -> SmallResult -> nat) -> Callback
| PostFinalFailure :
    CallbackKind -> (State -> SmallResult -> nat) -> Callback.

Record Result :=
  MkResult {
      ok          : option bool; (* Test case result - maybe == discard *)
      expect      : bool;        (* If false, property should fail *)
      reason      : string;      (* Error message *)
      interrupted : bool;        (* ? *)
      stamp       : list string; (* Collected values for this test case *)
      callbacks   : list Callback; 
      result_tag  : option string (* Tag - for better shrinking *)
    }.

Definition debug_stamps s {A : Type} (r : Result) (x : A) :=
  trace (s ++ (ShowFunctions.string_concat (
             (ShowFunctions.intersperse " @ "%string (stamp r)))) ++ nl) x.

(* I WANT RECORD UPDATES :'( *)
Definition succeeded := MkResult (Some true ) true "" false nil nil None.
Definition failed    := MkResult (Some false) true "" false nil nil None.
Definition rejected  := MkResult (   None   ) true "" false nil nil None.

Definition updExpect (res : Result) (e' : bool) : Result :=
  match res with
    | MkResult o e r i s c t => MkResult o e' r i s c t
  end.

Definition updReason (r : Result) (s' : string) : Result :=
  match r with
    | MkResult o e _ i s c t => MkResult o e s' i s c t
  end.

Definition updOk (r : Result) o' : Result :=
  match r with
    | MkResult _ e r i s c t => MkResult o' e r i s c t
  end.

Definition addCallback (res : Result) (c : Callback) : Result :=
  match res with
    | MkResult o e r i s cs t => MkResult o e r i s (cons c cs) t
  end.

Definition addCallbacks (res : Result) (cs : list Callback) : Result :=
  match res with
    | MkResult o e r i s cs' t => MkResult o e r i s (cs ++ cs') t
  end.

Definition addStamps res ss :=
  match res with
    | MkResult o e r i s cs t => MkResult o e r i (ss ++ s) cs t
  end.

(* LEO: Should we check if there already exists a tag? *)
Definition setTag (r : Result) (t' : string) : Result :=
  match r with 
    | MkResult o e r i s cs _ => MkResult o e r i s cs (Some t')
  end.

(* CH: The name of this should change; we no longer call checkers props *)
Record QProp : Type :=
  MkProp
    {
      unProp : Rose Result
    }.

Definition Checker : Type := G QProp.

Class Checkable (A : Type) : Type :=
  {
    checker : A -> Checker
  }.

(* mapping and lifting functions *)

Definition liftBool (b : bool) : Result :=
  if b then succeeded else updReason failed "Falsifiable".

Definition mapProp {P : Type} {_ : Checkable P}
           (f : QProp -> QProp) (prop : P) : Checker :=
  fmap f (checker prop).

Definition mapRoseResult {P : Type} {_ : Checkable P}
           (f : Rose Result -> Rose Result) (prop : P) : Checker :=
  mapProp (fun p => match p with MkProp t => MkProp (f t) end) prop.

Definition mapTotalResult {prop : Type} {_ : Checkable prop}
           (f : Result -> Result) : prop -> Checker :=
  mapRoseResult (fmapRose f).

Global Instance testResult : Checkable Result :=
  {|
    (* Left a protectResults out! *)
    checker r := returnGen (MkProp (returnRose r))
  |}.

Global Instance testBool : Checkable bool :=
  {|
    checker b := checker (liftBool b)
  |}.

(* ZP/CH: what's the relation between unit and discards? *)
Global Instance testUnit : Checkable unit :=
  {|
    checker := fun _ => checker rejected
  |}.

Global Instance testProp : Checkable QProp :=
  {|
    checker p := returnGen p
  |}.

Global Instance testGenProp (P : Type) `{Checkable P} : Checkable (G P) :=
  {|
    checker p := bindGen p checker
  |}.

Global Instance testChecker : Checkable Checker :=
  {|
      checker x := x
  |}.

(* Checker Combinators *)

(* The following function on its own does not have a decreasing argument...

     Fixpoint props {prop A : Type} {t : Checkable prop}
                    (pf : A -> prop) (shrinker : A -> list A) (x : A) :=
       MkRose (checker (pf x)) (List.map (props pf shrinker) (shrinker x)).
 *)
Fixpoint props' {prop A : Type} {t : Checkable prop} (n : nat)
         (pf : A -> prop) (shrinker : A -> list A) (x : A) :=
  match n with
    | O =>
      MkRose (checker (pf x)) (lazy nil)
    | S n' =>
      MkRose (checker (pf x)) (lazy (List.map (props' n' pf shrinker) (shrinker x)))
  end.

(* Arbitrary choice for number of shrinks.. *)
Definition props {prop A : Type} `{Checkable prop}
           (pf : A -> prop) (shrinker : A -> list A) (x : A) : Rose Checker :=
  props' 1000 pf shrinker x.

Definition shrinking {prop A : Type} `{Checkable prop}
           (shrinker : A -> list A) (x0 : A) (pf : A -> prop) : Checker :=
  fmap (fun x => MkProp (joinRose (fmapRose unProp x)))
       (promote (props pf shrinker x0)).

Definition shrinkingNondet {prop A : Type} `{Checkable prop} (n : nat)
          (shrinker : A -> list A) (x0 : A) (pf : A -> prop) : Checker :=
  fmap (fun x => MkProp (repeatRose n (joinRose (fmapRose unProp x))))
       (promote (props pf shrinker x0)).
  
Definition callback {prop : Type} `{Checkable prop}
           (cb : Callback) : prop -> Checker :=
  mapTotalResult (fun r => addCallback r cb).

Definition printTestCase {prop : Type} `{Checkable prop}
           (s : string) (p : prop) : Checker :=
  (* The following newline was causing an unwanted extra new line *)
  callback (PostFinalFailure Counterexample (fun _st _res => trace (s (* ++ nl*)) 0)) p.

Definition whenFail {prop : Type} `{Checkable prop}
           (str : string) : prop -> Checker :=
  callback (PostFinalFailure Counterexample (fun _st _sr => trace (str ++ nl) 0)).

Definition whenFail' {prop : Type} `{Checkable prop}
           (str : unit -> string) : prop -> Checker :=
  callback (PostFinalFailure Counterexample (fun _st _sr => trace (str tt ++ nl) 0)).

Notation "x 'WHENFAIL' y" := (whenFail' (fun _ => x) y) (at level 55).

Definition expectFailure {prop: Type} `{Checkable prop} (p: prop) :=
  mapTotalResult (fun res => updExpect res false) p.

(* NOTE: Ignoring the nat argument. Use label or collect ONLY *)
Definition cover {prop : Type} {_ : Checkable prop}
           (b : bool) (n : nat) (s : string) : prop -> Checker :=
  if b then
    mapTotalResult (fun res =>
                      let '(MkResult o e r i st c t) := res in
                      MkResult o e r i (s :: st) c t)
  else checker.

Definition classify {prop : Type} {_ : Checkable prop}
           (b : bool) (s : string) : prop -> Checker :=
  cover b 0 s.

Definition label {prop : Type} {_ : Checkable prop}
           (s : string) : prop -> Checker :=
  classify true s.

Definition collect {A prop : Type} `{_ : Show A} {_ : Checkable prop}
           (x : A) : prop -> Checker :=
  label (show x).

Definition tag {prop : Type} {_ : Checkable prop} (t : string) : prop -> Checker :=
  mapTotalResult (fun res => setTag res t).

Definition implication {prop : Type} `{Checkable prop} (b : bool) (p : prop) : Checker :=
  if b then checker p else (returnGen (MkProp (returnRose rejected))).

Definition forAll {A prop : Type} {_ : Checkable prop} `{Show A}
           (gen : G A)  (pf : A -> prop) : Checker :=
  bindGen gen (fun x =>
                 printTestCase (show x ++ newline) (pf x)).

Definition forAllMaybe {A prop : Type} {_ : Checkable prop} `{Show A}
           (gen : G (option A))  (pf : A -> prop) : Checker :=
  bindGen gen (fun mx =>
                 match mx with
                 | Some x => printTestCase (show x ++ newline) (pf x)
                 | None => checker tt
                 end
              ).


Definition forAllProof {A prop : Type} {C : Checkable prop} `{S : Show A}
           (gen : G A)  (pf : forall (x : A), semGen gen x -> prop) : Checker :=
  bindGen' gen (fun x H => printTestCase (show x ++ newline) (pf x H)).
Arguments forAllProof {A} {prop} {C} {S} _ _.

Definition forAllShrink {A prop : Type} {_ : Checkable prop} `{Show A}
           (gen : G A) (shrinker : A -> list A) (pf : A -> prop) : Checker :=

  bindGen gen (fun x : A =>
                 shrinking shrinker x (fun x' =>
                                         printTestCase (show x' ++ newline) (pf x'))).

Definition forAllShrinkNonDet {A prop : Type} {_ : Checkable prop} `{Show A}
           (n : nat) (gen : G A) (shrinker : A -> list A) (pf : A -> prop) : Checker :=

  bindGen gen (fun x : A =>
                 shrinkingNondet n shrinker x (fun x' =>
                                         printTestCase (show x' ++ newline) (pf x'))).

Definition forAllShrinkShow {A prop : Type} {_ : Checkable prop}
           (gen : G A) (shrinker : A -> list A) (show' : A -> string) (pf : A -> prop) : Checker :=
  bindGen gen (fun x =>
                 shrinking shrinker x (fun x' =>
                                         printTestCase (show' x') (pf x'))).

Global Instance testFun {A prop : Type} `{Show A}
       `{Arbitrary A} `{_ : Checkable prop} : Checkable (A -> prop) :=
  {
    checker f := forAllShrink arbitrary shrink f
  }.

Global Instance testProd {A : Type} {prop : A -> Type} `{Show A} `{Arbitrary A} 
       `{forall x : A, Checkable (prop x)} :
  Checkable (forall (x : A), prop x) := 
  {| checker f := forAllShrink arbitrary shrink (fun x => checker (f x)) |}.

Global Instance testPolyFun {prop : Type -> Type} {_ : Checkable (prop nat)} : Checkable (forall T, prop T) :=
  {
    checker f := printTestCase "" (f nat)
  }.

Global Instance testPolyFunSet {prop : Set -> Type} {_ : Checkable (prop nat)} : Checkable (forall T, prop T) :=
  {
    checker f := printTestCase "" (f nat)
  }.

(* LEO: TODO: Prove conjoin checker *)
Definition addCallbacks' r result := 
  addCallbacks result (callbacks r).
Definition addStamps' r result := 
(*   debug_stamps "Before_adding: " result (
  debug_stamps "Adding_stamps: " r ( *)
  let res := addStamps result (stamp r) in
(*   debug_stamps "After_adding: " res  *)
  res.

Fixpoint conjAux (f : Result -> Result) 
         l := 
  match l with 
    | nil => (MkRose (f succeeded) (lazy nil))
    | cons res rs => 
      let '(MkRose r _) := res in
      match ok r with 
        | Some true =>
           (conjAux (fun r' => addStamps' r (addCallbacks' r (f r'))
                    ) rs)
        | Some false => res
        | None =>
          let res' := conjAux (fun r' => (addCallbacks' r (f r'))) rs in
          let '(MkRose r' rs) := res' in
          match ok r' with 
            | Some true => MkRose (updOk r' None) (lazy nil)
            | Some false => res'
            | None => res'
          end
      end
  end.

Definition mapGen {A B} (f : A -> G B) (l : list A) : G (list B) :=
  bindGen (foldGen (fun acc a => 
             bindGen (f a) (fun b => returnGen (cons b acc)))
          l nil) (fun l => returnGen (rev l)).

Fixpoint conjoin (l : list Checker) : Checker :=
(*   trace ("Beginnning conjoin" ++ nl) ( *)
  bindGen (mapGen (liftGen unProp) l) (fun rs =>
          (returnGen (MkProp (let res := conjAux (fun x => x) rs in
                              let '(MkRose r _) := res in 
                              (* debug_stamps "Conjoin result: " r *) res
                             )))).

Definition fmapRose' A B (r : Rose A) (f : A -> B) := fmapRose f r.

Definition expectFailureError := 
  updReason failed "Expect failure cannot occur inside a disjunction".

Definition disjAux (p q : Rose Result) : Rose Result :=
  joinRose (fmapRose' p (fun result1 =>
  if expect result1 then
    match ok result1 with 
    | Some true => returnRose result1
    | Some false => 
      joinRose (fmapRose' q (fun result2 =>
      if expect result2 then
        match ok result2 with 
        | Some true => returnRose result2
        | Some false => 
          returnRose (MkResult (ok result2)
                               (expect result2)
                               (if string_dec (reason result2) EmptyString 
                                then reason result1
                                else reason result2)
                               (orb (interrupted result1) (interrupted result2))
                               (stamp result1 ++ stamp result2)
                               (callbacks result1 ++ 
                                    cons (PostFinalFailure Counterexample
                                                      (fun _ _ => trace newline 0)) nil ++
                                    callbacks result2 )
                               (result_tag result2))
        | None => returnRose result2 (* Leo: What to do here? *)
        end
      else returnRose expectFailureError))
    | None => 
      joinRose (fmapRose' p (fun result2 => 
      if expect result2 then 
        match ok result2 with
        | Some true => returnRose result2
        | _ => returnRose result1 (* Not sure here as well *)
        end
      else returnRose expectFailureError))
    end
  else returnRose expectFailureError)).

Definition disjoin (l : list Checker) : Checker := 
  bindGen (mapGen (liftGen unProp) l) (fun rs =>
          (returnGen (MkProp (
                          fold_right disjAux (returnRose failed) rs
                        )))).

Module QcNotation.
  Export QcDefaultNotation.

  Notation "x ==> y" := (implication x y) (at level 55, right associativity)
                           : Checker_scope.

  (* TODO: Figure out pretty printing too *)
  Notation "'FORALL' x : T , c" :=
    (forAllShrink (@arbitrary T _) shrink (fun x => c))
    (at level 200, x ident, T at level 200, c at level 200, right associativity
     (* , format "'[' 'exists' '/ ' x .. y , '/ ' p ']'" *) )
    : type_scope.

  Notation "'FORALL' x | P , c" :=
    (forAllShrink (genST (fun x => P)) shrink (fun y => match y with
                                                    | Some x => c
                                                    | _ => checker tt
                                                    end))
      (at level 200, x ident, P at level 200, c at level 200, right associativity)
     : type_scope.
End QcNotation.

