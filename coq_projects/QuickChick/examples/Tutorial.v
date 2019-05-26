(** * Tutorial for QuickChick *)

(** QuickChick is a clone of Haskell's QuickCheck, slightly on
    steroids.  This tutorial explores basic aspects of random
    property-based testing and details the majority of features of
    QuickChick. *)

(* begin hide *)
From QuickChick Require Import QuickChick.
Import QcDefaultNotation. Open Scope qc_scope.
Import GenLow GenHigh.
Set Warnings "-extraction-opaque-accessed,-extraction".

Require Import List ZArith.
Import ListNotations.

Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import seq ssreflect ssrbool ssrnat eqtype.

(* end hide *)

(** ** Introduction *)
     
(** It is not uncommon during a verification effort to spend many
    hours attempting to prove a slightly false theorem, only to result
    in frustration when the mistake is realized and one needs to start
    over. Other theorem provers have testing tools to quickly raise
    one's confidence before embarking on the body of the proof;
    Isabelle has its own QuickCheck clone, as well as Nitpick,
    Sledgehammer and a variety of other tools; ACL2 has gone a step
    further using random testing to facilitate its
    automation. QuickChick is meant to fill this void for Coq.

    Consider the following short function [remove] that takes a
    natural number [x] and a list of nats [l] and proceeds to remove
    [x] from the list. While one might be tempted to pose the question
    "Is there a bug in this definition?", such a question has little
    meaning without an explicit specification. Here, [removeP]
    requires that after removing [x] from [l], the resulting list does
    not contain any occurences of [x]. *)

Fixpoint remove (x : nat) (l : list nat) : list nat :=
  match l with
    | []   => []
    | h::t => if beq_nat h x then t else h :: remove x t
  end.

Definition removeP (x : nat) (l : list nat) := 
  (~~ (existsb (fun y => beq_nat y x) (remove x l))).

(** For this simple example, it is not hard to "spot" the bug by
    inspection. We will use QuickChick to find out what is wrong.

    QuickChick provides a toplevel command [QuickChick] that receives
    as input an executable property and attempts to falsify it. *)

QuickChick removeP.

(** Internally, the code is extracted to OCaml, compiled and ran to
obtain the output:
<<
    0

    [ 0, 0 ]

    Failed! After 17 tests and 12 shrinks
>>
    The output signifies that if we use an input where [x] is [0] and
    [l] is the two element list containing two zeros, then our
    property fails. Indeed, we can now identify that the [then] branch
    of [remove] fails to make a recursive call, which means that only
    one occurence of each element will be deleted. The last line of
    the output states that it took 17 tests to identify some fault
    inducing input and 12 shrinks to reduce it to a minimal
    counterexample.

    Before we begin to explain exactly how QuickChick magically comes
    up with this result, it is important to point out the first (and
    arguably most important) limitation of this tool: it requires an
    *executable* specification. QuickChick needs to be able to "run" a
    property and decide whether it is true or not; a definition like
    [remove_spec] can't be QuickChecked! *)

Definition remove_spec :=
  forall x l, ~ In x (remove x l).

(** QuickChick requires either a functional spec (like [removeP]) or a
    decidability procedure for an inductive spec. *)

(** ** Property Based Random Testing Ingredients 

    There are four basic ingredients in property based random testing:

    - An executable property, as discussed above
    - A printer, to report counterexamples found
    - A generator, to produce random inputs 
    - A shrinker, to reduce counterexamples.

    We will now review the latter three in order. *)

(** *** Printing 

    For printing, QuickChick uses a [Show] typeclass, like Haskell. *)

Print Show.
(**  ==> Record Show (A : Type) : Type 
            := Build_Show { show : A -> String.string }   *)

(** The [Show] typeclass contains a single function [show] from some
    type [A] to Coq's [string]. QuickChick provides default instances
    for [string]s (the identity function), [nat], [bool], [Z],
    etc. (via extraction to appropriate OCaml functions for
    efficiency), as well as some common compound datatypes: lists,
    pairs and options.

    Writing your own show instance is easy! Let's define a simple
    [Color] datatype. *)

Inductive Color := Red | Green | Blue | Yellow.

(** After ensuring we have opened the [string] scope, we can declare
    an instance of [Show Color] by encoding [show] as a simple pattern
    matching on colors. *)

Require Import String. Open Scope string.
Instance show_color : Show Color :=
  {| show c :=
       match c with
         | Red    => "Red"
         | Green  => "Green"
         | Blue   => "Blue"
         | Yellow => "Yellow"
       end
  |}.

Eval compute in (show Green).
(** ==> "Green" : string *)

(** While writing show instances is relatively straightforward, it can
    get tedious.  The QuickChick provides a lot of automation, which
    will be discussed at the end of this Tutorial. *)

(** *** Generators *)

(** **** The [G] Monad *)

(** The heart of property based random testing is the random
    generation of inputs.  In QuickChick, a generator for elements of
    some type [A] is a monadic object with type [G A]. The monad [G]
    serves as an abstraction over random seed plumbing. Consider
    writing a program that given a random seed generates many
    integers: one needs to use the given seed to produce an integer
    while at the same time obtain a new, altered seed to use for
    future draws. This [State]-monad like behavior is hidden behind
    [G].

    Standard monadic functions have the [Gen] suffix. *)

Check bindGen.
(** ==> bindGen : G ?A -> (?A -> G ?B) -> G ?B *) 

Check returnGen.
(** ==> returnGen : ?A -> G ?A *)

(** For those familiar with Haskell's monadic interface, QuickChick
    also provides variants of [liftM] (as [liftGen]) with arities 1 to
    5, [sequence] (as [sequenceGen]) and [foldM] (as [foldGen]). *)

(** **** Primitive generators *)

(** Primitive generators for booleans, natural numbers and integers
    are provided via extraction to OCaml. They can be accessed via the
    [choose] combinator.
 *)

Check choose.
(** ==> choose : Z * Z -> G Z *)

(** While here [choose] is monomorphised to [Z], it actually takes an
    interval of any type [A] that satisfies a [ChoosableFromInterval]
    typeclass (with default standard numeric instances) and produces
    an object of type [A] within that interval.

    We can see that in action using [Sample]. This is another toplevel
    command by QuickChick that runs a generator a number of times and
    prints whatever was generated in the form of a list. *)

Sample (choose(0, 10)).
(** ==> [ 1, 2, 1, 9, 8, 1, 3, 6, 2, 1, 8, 0, 1, 1, 3, 5, 4, 10, 4, 6 ] *)


(** **** Lists *)

(** Due to being the most commonly used compound datatype, lists have
    special combinators in Haskell's QuickCheck. The same is true in
    QuickChick; there are two combinators, [listOf] and [vectorOf]. *)

Check listOf.
(** ==> listOf : G ?A -> G (list ?A) *)

(** [listOf] takes as input a generator for elements of type [A] and returns a
    generator for lists of the same type. *)

Sample (listOf (choose (0,4))).
(** ==> [ [ 0, 3, 2, 0 ], 
         [ 1, 3, 4, 1, 0, 3, 0, 2, 2, 3, 2, 2, 2, 0, 4, 2, 3, 0, 1 ], 
         [ 3, 4, 3, 1, 2, 4, 4, 1, 0, 3, 4, 3, 2, 2, 4, 4, 1 ], 
         [ 0 ], 
         [ 4, 2, 3 ], 
         [ 3, 3, 4, 0, 1, 4, 3, 2, 4, 1 ], 
         [ 0, 4 ], 
         [  ], 
         [ 1, 0, 1, 3, 1 ], 
         [ 0, 0 ], 
         [ 1, 4 ], 
         [ 4, 3, 2, 0, 2, 2, 4, 0 ], 
         [ 1, 1, 0, 0, 1, 4 ], 
         [ 2, 0, 2, 1, 3, 3 ], 
         [ 4, 3, 3, 0, 1 ], 
         [ 3, 3, 3 ], 
         [ 3, 2, 4 ], 
         [ 1, 2 ], 
         [  ], 
         [  ] 
       ]
*)

(** The second combinator, [vectorOf], receives an additional numeric
    argument [n], the length of the list to be generated. *)

Check vectorOf.
(** ==> vectorOf : nat -> G ?A -> G (list ?A) *)

(** This raises a question: how does [listOf] decide how big of a list
    to generate? The answer is hidden inside the [G] monad.
  
    In addition to handling random seed plumbing, the [G] monad also
    provides a [Reader]-like environment with size information: a
    natural number [n] that nominally serves as the upper bound on the
    depth of the generated objects.  QuickChick progressively tries
    larger and larger values for [n], in order to explore larger and
    deeper part of the search space. Note that each generator can
    choose to interpret this input size however it wants and there is
    no guarantee that all generators comply to this standard - it is
    more of a "good practice" when writing one to respect this
    bound. *)

(** **** Custom Datatypes *)

(** Naturally, a lot of the time one needs to write generators involving
    user-defined datatypes. Let's revisit our color datatype; to generate a
    color, we only need to pick one of its four constructors, [Red], [Green],
    [Blue] and [Yellow]. This is done using [elements]. *)

Check elements.
(** ==> elements : ?A -> list ?A -> G ?A *)

(** This is the first place where the totality checker of Coq raises a
    design question. While Haskell's QuickCheck can simply fail
    raising an [error] whenever the input list is empty, Coq does not
    allow that behavior. Instead of increasing the burden to the user
    by requiring a proof that the list is not empty or by making the
    return type an option, QuickChick requires an additional element
    of type [A] as input to serve as a "default" object.  If the list
    is not empty, [elements] returns a generator that picks an element
    of that list; otherwise the generator always returns the default
    object.

    Moreover, QuickChick provides convenient notation to hide this
    default if it is apparent from the structure. *)

(*
Notation            Scope     
" 'elems' [ x ] " := elements x (cons x nil)
                      : qc_scope
                      (default interpretation)
" 'elems' [ x ; y ] " := elements x (cons x (cons y nil))
                      : qc_scope
                      (default interpretation)
" 'elems' [ x ; y ; .. ; z ] " := elements x
                                    (cons x (cons y .. (cons z nil) ..))
                      : qc_scope
                      (default interpretation)
" 'elems' ( x ;; l ) " := elements x (cons x l)
                      : qc_scope
                      (default interpretation)
*)

(** Armed with [elems], we can write the following simple [Color]
    generator. *)

Definition genColor : G Color :=
  elems [ Red ; Green ; Blue ; Yellow ].

Sample genColor.
(** ==> [ Blue, Red, Yellow, Red, Blue, Yellow, Yellow, Blue, Green, Red, Green,
         Blue, Blue, Red, Yellow, Blue, Red, Blue, Blue, Red ] *)

(** For more complicated ADTs, QuickChick provides more
    combinators. We will showcase them using everyone's favorite
    datatype: Trees!

    Our trees are standard binary trees; either [Leaf]s or [Node]s
    containing some payload of type [A] and two subtrees. *)

Inductive Tree A :=
| Leaf : Tree A
| Node : A -> Tree A -> Tree A -> Tree A.

Arguments Leaf {A}.
Arguments Node {A} _ _ _.

(** Before getting to generators for trees, we give a simple [Show]
    instance.  The rather inconvenient need for a local [let fix]
    declaration stems from the fact that Coq's typeclasses (unlike
    Haskell's) are not automatically recursive. *) 

Instance showTree {A} `{_ : Show A} : Show (Tree A) :=
  {| show := 
       let fix aux t :=
         match t with
           | Leaf => "Leaf"
           | Node x l r => "Node (" ++ show x ++ ") (" ++ aux l ++ ") (" ++ aux r ++ ")"
         end
       in aux
  |}.

(** The first combinator that actually combines different generators
    is [oneof]. *)

Check oneof.
(** ==> oneof : G ?A -> list (G ?A) -> G ?A *)

(** [oneof] takes a default generator and a list of generators, and
    picks one of the generators from the list uniformly at random, as
    long as the list is not empty.  Just like before, QuickChick
    introduces the notation [oneOf] to hide this default element.

    At this point, Coq's termination checker saves us from shooting
    ourselves in the foot. The "obvious" first generator that one
    might write is the following [genTree]: either generate a [Leaf]
    or a [Node] whose subtrees are generated recursively and whose
    payload is produced by a generator for elements of type [A].*)

(*
Fixpoint genTree {A} (g : G A) : G (Tree A) :=
  oneOf [ returnGen Leaf ;
          liftGen3 Node  g (genTree g) (genTree g) ].*)

(** Of course, this fixpoint will not pass Coq's termination
    check. Attempting to justify this fixpoint to oneself, one might
    say that at some point the random generation will pick a [Leaf] so
    it will eventually terminate. Sadly, in this case the expected
    size of the generated Tree is infinite...

    The solution is the standard "fuel" solution Coq users are so
    familiar with: we add an additional natural number [sz] as a
    parameter; when that parameter is [O] we only generate
    non-recursive branches, while we decrease this size in each
    recursive call. Thus, [sz] serves as a bound on the depth of the
    tree.

 *)

Fixpoint genTreeSized {A} (sz : nat) (g : G A) : G (Tree A) :=
  match sz with
    | O => returnGen Leaf
    | S sz' => oneOf [ returnGen Leaf ;
                       liftGen3  Node g (genTreeSized sz' g) (genTreeSized sz' g)
                     ]
  end.

Sample (genTreeSized 3 (choose(0,3))).
(** ==> [ Leaf,
         Leaf,
         Node (3) (Node (0) (Leaf) (Leaf)) (Node (2) (Leaf) (Node (3) (Leaf) (Leaf))),
         Leaf,
         Leaf,
         Leaf,
         Node (1) (Leaf) (Node (1) (Leaf) (Node (0) (Leaf) (Leaf))),
         Leaf,
         Node (3) (Leaf) (Leaf),
         Node (1) (Leaf) (Leaf),
         Leaf,
         Leaf,
         Node (0) (Leaf) (Node (0) (Leaf) (Node (2) (Leaf) (Leaf))),
         Node (0) (Node (2) (Node (3) (Leaf) (Leaf)) (Leaf)) (Leaf),
         Node (0) (Leaf) (Leaf),
         Leaf,
         Leaf,
         Leaf,
         Leaf,
         Leaf ]
*)

(** While this generator succesfully generated trees, just by
    observing [Sample] above there is a problem: [genTreeSized]
    produces way too many [Leaf]s! That is to be expected, 50% of the
    time we generate a [Leaf]. The solution is to skew the
    distribution towards [Node]s, using the most expressive QuickChick
    combinator, [frequency] and its associated default-lifting
    notation [freq].
 *)
Check frequency.
(** ==> frequency : G ?A -> seq (nat * G ?A) -> G ?A *)

(** [freq] takes a list of generators, each one tagged with a natural
    number that serves as the weight of that generator. In the
    following example, a [Leaf] will be generated 1 / (sz + 1) of the
    time, while a [Node] the remaining sz / (sz + 1) of the time.*)

Fixpoint genTreeSized' {A} (sz : nat) (g : G A) : G (Tree A) :=
  match sz with
    | O => returnGen Leaf 
    | S sz' => freq [ (1,  returnGen Leaf) ;
                      (sz, liftGen3  Node g (genTreeSized' sz' g) (genTreeSized' sz' g))
                    ]
  end.

Sample (genTreeSized' 3 (choose(0,3))).
(** ==> [ Node (3) (Node (1) (Node (3) (Leaf) (Leaf)) (Leaf)) (Node (0) (Leaf) (Node (3) (Leaf) (Leaf))),
         Leaf,
         Node (2) (Node (1) (Leaf) (Leaf)) (Leaf),
         Node (0) (Leaf) (Node (0) (Node (2) (Leaf) (Leaf)) (Node (0) (Leaf) (Leaf))),
         Node (1) (Node (2) (Leaf) (Node (0) (Leaf) (Leaf))) (Leaf),
         Node (0) (Node (0) (Leaf) (Node (3) (Leaf) (Leaf))) (Node (2) (Leaf) (Leaf)),
         Node (1) (Node (3) (Node (2) (Leaf) (Leaf)) (Node (3) (Leaf) (Leaf))) (Node (1) (Leaf) (Node (2) (Leaf) (Leaf))),
         Node (0) (Node (0) (Node (0) (Leaf) (Leaf)) (Node (1) (Leaf) (Leaf))) (Node (2) (Node (3) (Leaf) (Leaf)) (Node (0) (Leaf) (Leaf))),
         Node (2) (Node (2) (Leaf) (Leaf)) (Node (1) (Node (2) (Leaf) (Leaf)) (Node (2) (Leaf) (Leaf))),
         Node (2) (Node (3) (Node (2) (Leaf) (Leaf)) (Leaf)) (Node (0) (Node (2) (Leaf) (Leaf)) (Leaf)),
         Leaf,
         Node (2) (Node (3) (Node (3) (Leaf) (Leaf)) (Leaf)) (Leaf),
         Leaf,
         Node (1) (Leaf) (Leaf),
         Leaf,
         Node (1) (Node (2) (Leaf) (Node (3) (Leaf) (Leaf))) (Node (0) (Leaf) (Node (1) (Leaf) (Leaf))),
         Leaf,
         Node (3) (Node (0) (Node (0) (Leaf) (Leaf)) (Leaf)) (Node (0) (Leaf) (Node (2) (Leaf) (Leaf))),
         Node (2) (Node (2) (Node (0) (Leaf) (Leaf)) (Leaf)) (Node (1) (Leaf) (Node (2) (Leaf) (Leaf))),
         Leaf ]
 *)

(** To showcase this generator, we will use the notion of mirroring a
    tree: swapping its left and right subtrees recursively. *)
   
Fixpoint mirror {A : Type} (t : Tree A) : Tree A :=
  match t with
    | Leaf => Leaf
    | Node x l r => Node x (mirror r) (mirror l)
  end.

(** We also need a simple structural equality on trees *)
Fixpoint eq_tree (t1 t2 : Tree nat) : bool :=
  match t1, t2 with
    | Leaf, Leaf => true
    | Node x1 l1 r1, Node x2 l2 r2 =>
      beq_nat x1 x2 && eq_tree l1 l2 && eq_tree r1 r2
    | _, _ => false
  end.

(** One expects that [mirror] should be unipotent; mirroring a tree
    twice yields the original tree.  *)

Definition mirrorP (t : Tree nat) := eq_tree (mirror (mirror t)) t.

(** To test this assumption, we can use the [forAll] property
    combinator that receives a generator [g] for elements of type [A]
    and an executable property with argument [A] and tests the
    property on random inputs of [g]. *)

QuickChick (forAll (genTreeSized' 5 (choose (0,5))) mirrorP).

(** QuickChick quickly responds that this property passed 10000 tests,
    so we gain some confidence in its truth. But what would happend if
    we had the *wrong* property? *)

Definition faultyMirrorP (t : Tree nat) := eq_tree (mirror t) t.

QuickChick (forAll (genTreeSized' 5 (choose (0,5))) faultyMirrorP).
(** ==> Node (3) (Node (0) (Leaf) (Node (0) (Node (1) (Leaf) (Leaf)) (Leaf)))
(Node (5) (Node (0) (Node (1) (Leaf) (Node (4) (Leaf) (Leaf))) (Node (4) (Leaf)
(Node (0) (Leaf) (Leaf)))) (Node (5) (Node (4) (Node (0) (Leaf) (Leaf)) (Leaf))
(Node (3) (Leaf) (Leaf))))

*** Failed! After 1 tests and 0 shrinks
*)

(** The bug is found immediately and reported. However, is this counterexample
    really helpful? What is the important part of it? The reported bug is too
    big and noisy to identify the root cause of the problem. That is where
    shrinking comes in. *)

(** **** Shrinking *)

(** Shrinking, also known as delta debugging, is a greedy process by
    which we can find a smaller counterexample given a relatively
    large one. Given a shrinking function [s] of type [A -> list A]
    and a counterexample [x] of type [A] that is known to falsify some
    property [p], QuickChick (lazily) tries [p] on all members of [s
    x] until it finds another counterexample; then it repeats this
    process.

    This greedy algorithm can only work if all elements of [s x] are
    strictly "smaller" that [x] for all [x]. Most of the time, a
    shrinking function for some type only returns elements that are
    "one step" smaller. For example, consider the default shrinking
    function for lists provided by QuickChick. *)

Print shrinkList.
(** ==> shrinkList = 
     fix shrinkList (A : Type) (shr : A -> seq A) (l : seq A) {struct l} :
       seq (seq A) :=
       match l with
       | [::] => [::]
       | x :: xs =>
           ((xs :: List.map (fun xs' : seq A => x :: xs') (shrinkList A shr xs))%SEQ ++
            List.map (fun x' : A => (x' :: xs)%SEQ) (shr x))%list
       end
          : forall A : Type, (A -> seq A) -> seq A -> seq (seq A)
*)

(** An empty list can not be shrunk - there is no smaller list.  A
    cons cell can be shrunk in three ways: by returning the tail of
    the list, by shrinking the tail of the list and consing the head,
    or by shrinking the head and consing its tail. By induction, this
    process can generate all smaller lists.

    Writing a shrinking instance for trees is equally straightforward:
    we don't shrink [Leaf]s while for [Node]s we can return the left
    or right subtrees, shrink the payload or one of the subtrees.*)

Open Scope list.
Fixpoint shrinkTree {A} (s : A -> list A) (t : Tree A) : seq (Tree A) :=
  match t with
    | Leaf => []
    | Node x l r => [l] ++ [r] ++
                    map (fun x' => Node x' l r) (s x) ++
                    map (fun l' => Node x l' r) (shrinkTree s l) ++
                    map (fun r' => Node x l r') (shrinkTree s r)
  end.

(** Armed with [shrinkTree], we use the [forAllShrink] property
    combinator that takes an additional argument, a shrinker *)

QuickChick (forAllShrink (genTreeSized' 5 (choose (0,5))) (shrinkTree shrink) faultyMirrorP).

(** ==> Node (0) (Leaf) (Node (0) (Leaf) (Leaf))

*** Failed! After 1 tests and 8 shrinks *)

(** We now got a much simpler counterexample (in fact, this is one of
    the two minimal ones) and can tell that the real problem occurs
    when the subtrees of a [Node] are different. *)

(** **** Putting it all Together *)

(** QuickChick, just like QuickCheck, provides an [Arbitrary]
    typeclass parameterized over some type [A] with two objects:
    [arbitrary] and [shrink].

    The [arbitrary] object is a generator for elements of type [A]. If
    we were to encode an [Arbitrary] instance for trees we would like
    to use [genTreeSized']; however that generator takes an additional
    size argument.  The [G] monad will provide that argument through
    the combinator [sized].*)
    
Check sized.
(** ==> sized : (nat -> G ?A) -> G ?A *)

(** [sized] receives a function that given a number produces a
    generator, just like [genTreeSized'], and returns a generator that
    uses the size information inside the [G] monad.

    The [shrink] function is simply a shrinker like [shrinkTree]. *)

Instance genTree {A} `{Gen A} : GenSized (Tree A) := 
  {| arbitrarySized n := genTreeSized n arbitrary |}.

Instance shrTree {A} `{Shrink A} : Shrink (Tree A) := 
  {| shrink x := shrinkTree shrink x |}.

(** With this [Arbitrary] instance we can once again use the toplevel
    [QuickChick] command with just the property.  *)

QuickChick faultyMirrorP.

(** [QuickChick] internally calls the function [quickCheck] with type
    [forall prop. Checkable prop => prop -> Result]. But what _is_
    [Checkable]? It is easy to see how a boolean is [Checkable]; we
    can always tell if it is true or not and then return a [Result],
    [Success]/[Failure] as appropriate.
    
    To see how executable properties are [Checkable], consider a
    single argument function [p : A -> Bool] that returns a
    boolean. If we know that [A] has [Show] and [Arbitrary] instances,
    we can just call [forAllShrink] with [arbitrary] and
    [shrink]. Going a step further, the result type doesn't really
    need to be [Bool], it can be a [Checkable]! Thus, we can provide a
    [Checkable] instance for arbitrary functions.*)

Print testFun.

(** **** Collecting Statistics *)

(** Earlier in this tutorial we claimed that [genTreeSized] produced
    "too many" [Leaf]s. But how can we justify that? Just looking at
    the result of [Sample] gives us an idea that something is going
    wrong but just observing a handful of samples cannot realistically
    provide statistical guarantees. That is where [collect], another
    property combinator, comes in. In Haskell notation, [collect]
    would have the type [collect : Show A, Checkable prop => A -> prop
    -> prop]; it takes some value of type [A] that can be shown and a
    property, and returns the property itself. Whenever the resulting
    property is exercised, the [A] object is captured and statistics
    are collected.

    For example, consider a [size] function on [Tree]s.
 *)

Fixpoint size {A} (t : Tree A) : nat :=
  match t with
    | Leaf => O
    | Node _ l r => 1 + size l + size r
  end.

(** If we were to write a dummy property to check our generators and
    measure the size of generated trees, we could use [treeProp]
    below. *)

Definition treeProp (g : nat -> G nat -> G (Tree nat)) n :=
  forAll (g n (choose (0,n))) (fun t => 
  collect (size t) true).

QuickChick (treeProp genTreeSized  5).

(** ==> 
4947 : 0
1258 : 1
673 : 2
464 : 6
427 : 5
393 : 3
361 : 7
302 : 4
296 : 8
220 : 9
181 : 10
127 : 11
104 : 12
83 : 13
64 : 14
32 : 15
25 : 16
16 : 17
13 : 18
6 : 19
5 : 20
2 : 21
1 : 23
+++ OK, passed 10000 tests

We see that 62.5% of the tests are either [Leaf]s or empty [Nodes], while too
few tests have larger sizes. Compare that with [genTreeSized'] below.  *)

QuickChick (treeProp genTreeSized' 5).
(** ==> 
1624 : 0
571 : 10
564 : 12
562 : 11
559 : 9
545 : 8
539 : 14
534 : 13
487 : 7
487 : 15
437 : 16
413 : 6
390 : 17
337 : 5
334 : 1
332 : 18
286 : 19
185 : 4
179 : 20
179 : 2
138 : 21
132 : 3
87 : 22
62 : 23
19 : 24
10 : 25
6 : 26
2 : 27
+++ OK, passed 10000 tests

A lot fewer terms have small sizes, allowing us to explore larger terms*)

(** ** Avoiding Work  :) *)

(** While a lot of time putting a bit of time and effort in a
    generator and a shrinker, the examples shown here are fairly
    straightforward. After writing a couple of [Show] and [Arbitrary]
    instances, it can get tedious and boring. That is precisely why
    [QuickChick] provides some automation in deriving such instances
    for _plain_ datatypes automatically. *)

Derive Arbitrary for Tree.
(* GenSizedTree is defined *)
(* ShrinkTree is defined *)
Print GenSizedTree.
Print ShrinkTree.

Derive Show for Tree.
(* ShowTree is defined *)
Print ShowTree.

