(* We hide the implementation of generators behind this interface. The
   rest of the framework and user code are agnostic to the internal
   representation of generators. The proof organization/abstraction
   tries to follow this code organization/abstraction. We need to
   expose quite a bit on the proof side for this to work though. *)

Set Warnings "-extraction-opaque-accessed,-extraction".
Set Warnings "-notation-overridden,-parsing".

Require Import ZArith List.
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssrfun ssrbool ssrnat.

From ExtLib.Structures Require Export
     Functor Applicative Monads.
Import MonadNotation.
Open Scope monad_scope.

From QuickChick Require Import
     RandomQC RoseTrees Sets.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Bullet Behavior "Strict Subproofs".

Import ListNotations.

Definition isNone {T : Type} (u : option T) :=
  match u with
    | Some _ => false
    | None => true
  end.

Lemma randomSplit_codom : codom randomSplit <--> setT.
Proof.
by apply/subset_eqP; split=> // [[s1 s2]] _; apply: randomSplitAssumption.
Qed.

Module Type Sig.

  (** * Type of generators *)

  Parameter G : Type -> Type.

  (** * Primitive generator combinators *)

  Parameter returnGen  : forall {A : Type}, A -> G A.
  (* TODO: Add dependent combinator *)
  Parameter bindGen :  forall {A B : Type}, G A -> (A -> G B) -> G B.
  Parameter run  : forall {A : Type}, G A -> nat -> RandomSeed -> A.
  Parameter fmap : forall {A B : Type}, (A -> B) -> G A -> G B.
  Parameter apGen : forall {A B : Type}, G (A -> B) -> G A -> G B.
  Parameter sized : forall {A: Type}, (nat -> G A) -> G A.
  Parameter resize : forall {A: Type}, nat -> G A -> G A.
  Parameter promote : forall {A : Type}, Rose (G A) -> G (Rose A).
  Parameter choose : forall {A : Type} `{ChoosableFromInterval A}, (A * A) -> G A.
  Parameter sample : forall {A : Type}, G A -> list A.


  (* LL: The abstraction barrier is annoying :D *)
  Parameter variant : forall {A : Type}, SplitPath -> G A -> G A.
  Parameter reallyUnsafePromote : forall {r A:Type}, (r -> G A) -> G (r -> A).

  Parameter promoteVariant : forall {A B : Type} (a : A) (f : A -> SplitPath) (g : G B) size 
                               (r r1 r2 : RandomSeed),
                               randomSplit r = (r1,r2) ->                              
                               run (reallyUnsafePromote (fun a => variant (f a) g)) size r a = 
                               run g size (varySeed (f a) r1).

  (** * Semantics of generators *)

  (* Set of outcomes semantics definitions (repeated below) *)
  Definition semGenSize {A : Type} (g : G A) (size : nat) : set A :=
    codom (run g size).
  Definition semGen {A : Type} (g : G A) : set A :=
    \bigcup_size semGenSize g size.

  (* Set of outcomes semantics for generators that can fail
     (ignoring [None] as a value). *)
  Definition semGenSizeOpt {A : Type} (g : G (option A)) (s : nat) : set A :=
    somes (semGenSize g s).

  Definition semGenOpt {A : Type} (g : G (option A)) : set A :=
    somes (semGen g).

  Parameter semGenOpt_equiv : forall {A} (g : G (option A)),
    semGenOpt g <--> \bigcup_s semGenSizeOpt g s.

  Parameter bindGen' : forall {A B : Type} (g : G A), 
                       (forall (a : A), (a \in semGen g) -> G B) -> G B. 

  Arguments bindGen' [A] [B] _ _.

  (** * Properties of generators *)

  (** A generator is [Unsized] if its semantics does not depend on the runtime size *)
  (* begin Unsized *)
  Class Unsized {A} (g : G A) :=
    unsized : forall s1 s2, semGenSize g s1 <--> semGenSize g s2.
  (* end Unsized *)
  
  (** Sized generators monotonic in the size parameter *)
  Class SizedMonotonic {A} (g : nat -> G A) :=
    sizeMonotonic : forall s s1 s2,
      s1 <= s2 ->
      semGenSize (g s1) s \subset semGenSize (g s2) s.

  (** Sized generators of option type monotonic in the size parameter *)
  Class SizedMonotonicOpt {A} (g : nat -> G (option A)) :=
    sizeMonotonicOpt : forall s s1 s2,
      s1 <= s2 ->
      semGenSizeOpt (g s1) s \subset semGenSizeOpt (g s2) s.
  
  (** Generators monotonic in the runtime size parameter *)
  Class SizeMonotonic {A} (g : G A) :=
    monotonic : forall s1 s2,
      s1 <= s2 ->
      semGenSize g s1 \subset semGenSize g s2.

  (** Generators monotonic in the runtime size parameter *)
  Class SizeMonotonicOpt {A} (g : G (option A)) :=
    monotonicOpt : forall s1 s2,
      s1 <= s2 ->
      semGenSizeOpt g s1 \subset semGenSizeOpt g s2.
  
  (** Generators monotonic in the runtime size parameter *)
  Class SizeAntiMonotonicNone {A} (g : G (option A)) :=
    monotonicNone : forall s1 s2,
      s1 <= s2 ->
      isNone :&: semGenSize g s2 \subset isNone :&: semGenSize g s1.
  
  (* CH: Why does Unsized need a _ when A is marked as implict! *)
  Parameter unsized_alt_def :
    forall A (g : G A) `{Unsized _ g},
    forall s, semGenSize g s <--> semGen g.

  (* begin unsizedMonotonic *)
  Declare Instance unsizedMonotonic : forall {A} (g : G A), Unsized g -> SizeMonotonic g.
  (* end unsizedMonotonic *)
  

  (** *  Semantics of combinators *)
  
  Parameter semReturn :
    forall A (x : A), semGen (returnGen x) <--> [set x].
  Parameter semReturnSize :
    forall A (x : A) size, semGenSize (returnGen x) size <--> [set x].
  
  Declare Instance unsizedReturn {A} (x : A) : Unsized (returnGen x).
  Declare Instance returnGenSizeMonotonic {A} (x : A) : SizeMonotonic (returnGen x).
  Declare Instance returnGenSizeMonotonicOpt {A} (x : option A) : SizeMonotonicOpt (returnGen x).

  Parameter semBindSize :
    forall A B (g : G A) (f : A -> G B) (size : nat),
      semGenSize (bindGen g f) size <-->
                 \bigcup_(a in semGenSize g size) semGenSize (f a) size.

  Parameter semBindSize_subset_compat :
    forall {A B : Type} (g g' : G A) (f f' : A -> G B),
      (forall s, semGenSize g s \subset semGenSize g' s) ->
      (forall x s, semGenSize (f x) s \subset semGenSize (f' x) s) ->
      (forall s, semGenSize (bindGen g f) s \subset semGenSize (bindGen g' f') s).

  Parameter semBindSizeOpt_subset_compat :
    forall {A B : Type} (g g' : G A) (f f' : A -> G (option B)),
      (forall s, semGenSize g s \subset semGenSize g' s) ->
      (forall x s, isSome :&: semGenSize (f x) s \subset isSome :&: semGenSize (f' x) s) ->
      (forall s, isSome :&: semGenSize (bindGen g f) s \subset isSome :&: semGenSize (bindGen g' f') s) .

  Parameter monad_leftid : 
    forall {A B : Type} (a: A) (f : A -> G B),
      semGen (bindGen (returnGen a) f) <--> semGen (f a).
  Parameter monad_rightid : 
    forall {A : Type} (g : G A),
      semGen (bindGen g returnGen) <--> semGen g.
  Parameter monad_assoc: 
    forall {A B C : Type} (ga : G A) (fb : A -> G B) (fc : B -> G C),
      semGen (bindGen (bindGen ga fb) fc) <--> 
             semGen (bindGen ga (fun a => bindGen (fb a) fc)).
  
  (* I'm not sure how this universal quantifier will behave *)
  (* begin bindUnsized *)
  Declare Instance bindUnsized {A B} (g : G A) (f : A -> G B)
          `{Unsized _ g} `{forall x, Unsized (f x)} : Unsized (bindGen g f).
  (* end bindUnsized *)

  (* XXX these will always succeed and they have the same priority *)
  Declare Instance bindMonotonic
          {A B} (g : G A) (f : A -> G B)
          `{SizeMonotonic _ g} `{forall x, SizeMonotonic (f x)} : 
    SizeMonotonic (bindGen g f).

  Declare Instance bindMonotonicOpt
          {A B} (g : G A) (f : A -> G (option B))
          `{SizeMonotonic _ g} `{forall x, SizeMonotonicOpt (f x)} : 
    SizeMonotonicOpt (bindGen g f).

  Declare Instance bindMonotonicStrong
          {A B} (g : G A) (f : A -> G B)
          `{SizeMonotonic _ g} `{forall x, semGen g x -> SizeMonotonic (f x)} : 
    SizeMonotonic (bindGen g f).

  Declare Instance bindMonotonicOptStrong
          {A B} (g : G A) (f : A -> G (option B)) `{SizeMonotonic _ g}
          `{forall x, semGen g x -> SizeMonotonicOpt (f x)} :
    SizeMonotonicOpt (bindGen g f).
  
  Parameter semBindUnsized1 :
    forall A B (g : G A) (f : A -> G B) `{Unsized _ g},
      semGen (bindGen g f) <--> \bigcup_(a in semGen g) semGen (f a).
  
  Parameter semBindUnsized2 :
    forall A B (g : G A) (f : A -> G B) `{forall a, Unsized (f a)},
      semGen (bindGen g f) <--> \bigcup_(a in semGen g) semGen (f a).
  
  Parameter semBindSizeMonotonic :
  forall {A B} (g : G A) (f : A -> G B)
         `{SizeMonotonic _ g} `{forall a, SizeMonotonic (f a)},
    semGen (bindGen g f) <--> \bigcup_(a in semGen g) semGen (f a).

  Parameter semBindSizeMonotonicIncl_r :
    forall {A B} (g : G A) (f : A -> G (option B)) (s1 : set A) (s2 : A -> set B),
      semGen g \subset s1 ->
      (forall x, semGen (f x) \subset Some @: (s2 x) :|: [set None]) -> 
      semGen (bindGen g f) \subset Some @: (\bigcup_(a in s1) s2 a)  :|: [set None].

  Parameter semBindSizeMonotonicIncl_l :
    forall {A B} (g : G A) (f : A -> G (option B)) (s1 : set A) (fs : A -> set B) 
      `{Hg : SizeMonotonic _ g}
      `{Hf : forall a, SizeMonotonicOpt (f a)},
    s1 \subset semGen g ->
    (forall x, Some @: (fs x) \subset semGen (f x)) ->
    (Some @: \bigcup_(a in s1) (fs a)) \subset semGen (bindGen g f).

  Parameter semFmap :
    forall A B (f : A -> B) (g : G A),
      semGen (fmap f g) <--> f @: semGen g.

  Parameter semFmapSize :
    forall A B (f : A -> B) (g : G A) (size : nat),
      semGenSize (fmap f g) size <--> f @: semGenSize g size.

  Declare Instance fmapUnsized {A B} (f : A -> B) (g : G A) `{Unsized _ g} : 
    Unsized (fmap f g).

  Declare Instance fmapMonotonic
          {A B} (f : A -> B) (g : G A) `{SizeMonotonic _ g} : 
    SizeMonotonic (fmap f g).

  Parameter semChoose :
    forall A `{RandomQC.ChoosableFromInterval A} (a1 a2 : A),
      RandomQC.leq a1 a2 ->
      (semGen (choose (a1,a2)) <--> [set a | RandomQC.leq a1 a && RandomQC.leq a a2]).

  Parameter semChooseSize :
    forall A `{RandomQC.ChoosableFromInterval A} (a1 a2 : A),
      RandomQC.leq a1 a2 ->
      forall size, (semGenSize (choose (a1,a2)) size <-->
              [set a | RandomQC.leq a1 a && RandomQC.leq a a2]).

  Declare Instance chooseUnsized A `{RandomQC.ChoosableFromInterval A} (a1 a2 : A) :
    Unsized (choose (a1, a2)).

  Parameter semSized :
    forall A (f : nat -> G A),
      semGen (sized f) <--> \bigcup_s semGenSize (f s) s.

  Parameter semSizedSize :
    forall A (f : nat -> G A) s,
      semGenSize (sized f) s <--> semGenSize (f s) s.

  (* TODO change name *)

  Parameter semSized_alt :
    forall A (f : nat -> G A) `{forall n, SizeMonotonic (f n)},
      (forall n m s,  n <= m -> semGenSize (f n) s \subset semGenSize (f m) s) ->
      semGen (sized f) <--> \bigcup_n (semGen (f n)).

  Parameter semSized_opt :
    forall A (f : nat -> G (option A)) (H : forall n, SizeMonotonicOpt (f n)) (H' : SizedMonotonicOpt f),
      isSome :&: semGen (sized f) <--> isSome :&: \bigcup_n (semGen (f n)).

  Declare Instance sizedSizeMonotonic
          A (gen : nat -> G A) `{forall n, SizeMonotonic (gen n)} `{SizedMonotonic A gen} :
    SizeMonotonic (sized gen).

  Declare Instance sizedSizeMonotonicOpt
          A (gen : nat -> G (option A)) `{forall n, SizeMonotonic (gen n)} `{SizedMonotonicOpt A gen} :
    SizeMonotonicOpt (sized gen).
  
  Parameter semResize :
    forall A (n : nat) (g : G A),
      semGen (resize n g) <--> semGenSize g n.

  Parameter semSizeResize :
    forall A (s n : nat) (g : G A),
      semGenSize (resize n g) s <--> semGenSize g n.

  Declare Instance unsizedResize {A} (g : G A) n : 
    Unsized (resize n g).

  (* This (very concrete) spec is needed to prove shrinking *)
  Parameter semPromote :
    forall A (m : Rose (G A)),
      semGen (promote m) <-->
      codom2 (fun size seed => fmapRose (fun g => run g size seed) m).

  Parameter semPromoteSize :
    forall (A : Type) (m : Rose (G A)) n,
      semGenSize (promote m) n <-->
      (fun t : Rose A =>
         exists (seed : RandomSeed),
           fmapRose (fun g : G A => run g n seed) m = t).

  (* Those are too concrete, but I need them to prove shrinking.
   Does this reveal a weakness in our framework?
   Should we try to get rid of this?
   This is expected since the spec of promote is too concrete. *)

  Parameter runFmap :
    forall (A B : Type) (f : A -> B) (g : G A) seed size,
      run (fmap f g) seed size = f (run g seed size).

  Parameter runPromote :
    forall A (m : Rose (G A)) seed size,
      run (promote m) seed size = fmapRose (fun (g : G A) => run g seed size) m.
  
  Parameter semFmapBind :
    forall A B C (g : G A) (f1 : B -> C) (f2 : A -> G B),
      semGen (fmap f1 (bindGen g f2)) <-->
      semGen (bindGen g (fun x => fmap f1 (f2 x))).

  Instance Functor_G : Functor G := {
    fmap A B := fmap;
  }.

  Instance Applicative_G : Applicative G := {
    pure A := returnGen;
    ap A B := apGen;
  }.

  Instance Monad_G : Monad G := {
    ret A := returnGen;
    bind A B := bindGen;
  }.

  (** Delay evaluation of a generator in a CBV language. *)
  Parameter thunkGen : forall {A}, (unit -> G A) -> G A.

  (** [thunkGen] doesn't change semantics. *)
  Parameter semThunkGenSize : forall A (f : unit -> G A) s,
      semGenSize (thunkGen f) s <--> semGenSize (f tt) s.

  Parameter semThunkGen : forall A (f : unit -> G A),
      semGen (thunkGen f) <--> semGen (f tt).

  Declare Instance thunkGenUnsized {A} (f : unit -> G A)
          `{Unsized _ (f tt)} : Unsized (thunkGen f).

  Declare Instance thunkGenSizeMonotonic {A} (f : unit -> G A)
          `{SizeMonotonic _ (f tt)} : SizeMonotonic (thunkGen f).

  Declare Instance thunkGenSizeMonotonicOpt {A} (f : unit -> G (option A))
          `{SizeMonotonicOpt _ (f tt)} : SizeMonotonicOpt (thunkGen f).

  Declare Instance thunkGenSizeAntiMonotonicNone {A} (f : unit -> G (option A))
          `{SizeAntiMonotonicNone _ (f tt)} : SizeAntiMonotonicNone (thunkGen f).

  (** A notation around [thunkGen] for convenience. *)
  Notation etaG g := (thunkGen (fun _ => g)).

End Sig.
