(* QuickChick Prelude *)
Set Warnings "-extraction-opaque-accessed,-extraction".
Set Warnings "-notation-overridden,-parsing".

Require Import String List. Open Scope string.

From QuickChick Require Import QuickChick Tactics.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype seq.
Import QcDefaultNotation. Open Scope qc_scope.

Set Bullet Behavior "Strict Subproofs".

(* End prelude *)

Require Export Lists.

Inductive list (X:Type) : Type :=
  | nil : list X
  | cons : X -> list X -> list X.

Instance dec_list' {A} (p q : list A) 
         (D : forall (x y : A), Dec (x = y)) : Dec (p = q).
Proof. constructor; unfold decidable.
       decide equality. apply D.
Defined.

Derive (Arbitrary, Show) for list.
Derive (Sized, CanonicalSized) for list.
Derive SizeMonotonic for list using genSlist.
Derive SizedMonotonic for list.
Derive SizedCorrect for list using genSlist and SizeMonotoniclist.

Fixpoint repeat (X : Type) (x : X) (count : nat) : list X :=
  match count with
  | 0 => nil X
  | S count' => cons X x (repeat X x count')
  end.

Module MumbleGrumble.

Inductive mumble : Type :=
  | a : mumble
  | b : mumble -> nat -> mumble
  | c : mumble.

Instance dec_mumble (p q : mumble) : Dec (p = q).
Proof. constructor; unfold decidable; repeat decide equality. Defined.

Derive (Arbitrary, Show) for mumble.
Derive (Sized, CanonicalSized) for mumble.
Derive SizeMonotonic for mumble using genSmumble.
Derive SizedMonotonic for mumble.
Derive SizedCorrect for mumble using genSmumble and SizeMonotonicmumble.

Inductive grumble (X:Type) : Type :=
  | d : mumble -> grumble X
  | e : X -> grumble X.

Instance dec_grumble' {A} (p q : grumble A) 
         (D : forall (x y : A), Dec (x = y)) : Dec (p = q).
Proof. constructor; unfold decidable.
       repeat decide equality. 
       apply D.
Defined.

Derive (Arbitrary, Show) for grumble.
Derive (Sized, CanonicalSized) for grumble.
Derive SizeMonotonic for grumble using genSgrumble.
Derive SizedMonotonic for grumble.
Derive SizedCorrect for grumble using genSgrumble and SizeMonotonicgrumble.

End MumbleGrumble.

Fixpoint repeat' X x count : list X :=
  match count with
  | 0        => nil X
  | S count' => cons X x (repeat' X x count')
  end.

Fixpoint repeat'' X x count : list X :=
  match count with
  | 0        => nil _
  | S count' => cons _ x (repeat'' _ x count')
  end.

Arguments nil {X}.
Arguments cons {X} _ _.
Arguments repeat {X} x count.


Fixpoint repeat''' {X : Type} (x : X) (count : nat) : list X :=
  match count with
  | 0        => nil
  | S count' => cons x (repeat''' x count')
  end.

Inductive list' {X:Type} : Type :=
  | nil' : list'
  | cons' : X -> list' -> list'.

Instance dec_list'' {A} (p q : @list' A) 
         (D : forall (x y : A), Dec (x = y)) : Dec (p = q).
Proof. constructor; unfold decidable.
       decide equality. apply D.
Defined.

Derive (Arbitrary, Show) for list'.
Derive (Sized, CanonicalSized) for list'.
Derive SizeMonotonic for list' using genSlist'.
Derive SizedMonotonic for list'.
Derive SizedCorrect for list' using genSlist' and SizeMonotoniclist'.

Fixpoint app {X : Type} (l1 l2 : list X)
             : (list X) :=
  match l1 with
  | nil      => l2
  | cons h t => cons h (app t l2)
  end.

Fixpoint rev {X:Type} (l:list X) : list X :=
  match l with
  | nil      => nil
  | cons h t => app (rev t) (cons h nil)
  end.

Fixpoint length {X : Type} (l : list X) : nat :=
  match l with
  | nil => 0
  | cons _ l' => S (length l')
  end.

Notation "x :: y" := (cons x y)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y []) ..).
Notation "x ++ y" := (app x y)
                     (at level 60, right associativity).

Theorem app_nil_r : forall (X:Type), forall l:list X,
  l ++ [] = l.
Admitted. (* QuickChick app_nil_r. *)

Theorem app_assoc : forall A (l m n:list A),
  l ++ m ++ n = (l ++ m) ++ n.
Admitted. (* QuickChick app_assoc. *)

Lemma app_length : forall (X:Type) (l1 l2 : list X),
  length (l1 ++ l2) = length l1 + length l2.
Admitted. (* QuickChick app_length. *)

Theorem rev_app_distr: forall X (l1 l2 : list X),
  rev (l1 ++ l2) = rev l1 ++ rev l2.
Admitted. (* QuickChick rev_app_distr. *)

Theorem rev_involutive : forall X : Type, forall l : list X,
  rev (rev l) = l.
Admitted. (* QuickChick rev_involutive. *)

Inductive prod (X Y : Type) : Type :=
| pair : X -> Y -> prod X Y.

Arguments pair {X} {Y} _ _.

Notation "( x , y )" := (pair x y).

Notation "X * Y" := (prod X Y) : type_scope.

Instance dec_prod' {A} {B} (p q : prod A B) 
         (DA : forall (x y : A), Dec (x = y)) 
         (DB : forall (x y : B), Dec (x = y)) : Dec (p = q).
Proof. constructor; unfold decidable.
       decide equality;
         try solve [apply DA];
         try solve [apply DB].         
Defined.

Derive Arbitrary for prod.
Derive Show for prod.
Derive Sized for prod.
Derive CanonicalSized for prod.
Derive SizeMonotonic for prod using genSprod.
Derive SizedMonotonic for prod.

Definition fst {X Y : Type} (p : X * Y) : X :=
  match p with
  | (x, y) => x
  end.

Definition snd {X Y : Type} (p : X * Y) : Y :=
  match p with
  | (x, y) => y
  end.

Fixpoint combine {X Y : Type} (lx : list X) (ly : list Y)
           : list (X*Y) :=
  match lx, ly with
  | [], _ => []
  | _, [] => []
  | x :: tx, y :: ty => (x, y) :: (combine tx ty)
  end.

(*
Fixpoint split {X Y : Type} (l : list (X*Y))
               : (list X) * (list Y)
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.
*)

Inductive option (X:Type) : Type :=
  | Some : X -> option X
  | None : option X.

Arguments Some {X} _.
Arguments None {X}.

Instance dec_option' {A} (p q : option A) 
         (D : forall (x y : A), Dec (x = y)) : Dec (p = q).
Proof. constructor; unfold decidable.
       decide equality. apply D.
Defined.

Derive Arbitrary for option.
Derive Show for option.
Derive Sized for option.
Derive CanonicalSized for option.
Derive SizeMonotonic for option using genSoption.
Derive SizedMonotonic for option.
Derive SizedCorrect for option using genSoption and SizeMonotonicoption.

Fixpoint nth_error {X : Type} (l : list X) (n : nat)
                   : option X :=
  match l with
  | [] => None
  | a :: l' => if beq_nat n O then Some a else nth_error l' (pred n)
  end.

Fixpoint filter {X:Type} (test: X->bool) (l:list X)
                : (list X) :=
  match l with
  | []     => []
  | h :: t => if test h then h :: (filter test t)
                        else       filter test t
  end.

Fixpoint map {X Y:Type} (f:X->Y) (l:list X) : (list Y) :=
  match l with
  | []     => []
  | h :: t => (f h) :: (map f t)
  end.

From QuickChick Require Import CoArbitrary.
Theorem map_rev : forall (X Y : Type) (f : X -> Y) (l : list X),
  map f (rev l) = rev (map f l).
Admitted. (* LEO: CoArbitrary *)

Definition option_map {X Y : Type} (f : X -> Y) (xo : option X)
                      : option Y :=
  match xo with
    | None => None
    | Some x => Some (f x)
  end.

Fixpoint fold {X Y:Type} (f: X->Y->Y) (l:list X) (b:Y)
                         : Y :=
  match l with
  | nil => b
  | h :: t => f h (fold f t b)
  end.

Definition constfun {X: Type} (x: X) : nat->X :=
  fun (k:nat) => x.

(** **** Exercise: 2 stars (fold_length)  *)
(** Many common functions on lists can be implemented in terms of
   [fold].  For example, here is an alternative definition of [length]: *)

Definition fold_length {X : Type} (l : list X) : nat :=
  fold (fun _ n => S n) l 0.

Theorem fold_length_correct : forall X (l : list X),
  fold_length l = length l.
Admitted. (* QuickChick fold_length_correct. *)

Definition prod_curry {X Y Z : Type}
  (f : X * Y -> Z) (x : X) (y : Y) : Z := f (x, y).

Definition prod_uncurry {X Y Z : Type}
  (f : X -> Y -> Z) (p : X * Y) : Z
  := let (x,y) := p in f x y. 

Theorem uncurry_curry : forall (X Y Z : Type)
                        (f : X -> Y -> Z)
                        x y,
  prod_curry (prod_uncurry f) x y = f x y.
Admitted. (* QuickChick uncurry_curry. *)

Theorem curry_uncurry : forall (X Y Z : Type)
                        (f : (X * Y) -> Z) (p : X * Y),
  prod_uncurry (prod_curry f) p = f p.
Admitted. (* CoArbitrary *)



