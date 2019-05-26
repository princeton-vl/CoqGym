(* QuickChick Prelude *)
Set Warnings "-extraction-opaque-accessed,-extraction".
Set Warnings "-notation-overridden,-parsing".

Require Import String List. Open Scope string.

From QuickChick Require Import QuickChick Tactics.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype seq.
Import QcDefaultNotation. Open Scope qc_scope.

Set Bullet Behavior "Strict Subproofs".

(* End prelude *)

Inductive day : Type :=
  | monday : day
  | tuesday : day
  | wednesday : day
  | thursday : day
  | friday : day
  | saturday : day
  | sunday : day.

Derive (Arbitrary, Show) for day.
Derive (Sized, CanonicalSized) for day.
Derive SizeMonotonic for day using genSday.
Derive SizedMonotonic for day.
Derive SizedCorrect for day using genSday and SizeMonotonicday.

Definition next_weekday (d:day) : day :=
  match d with
  | monday    => tuesday
  | tuesday   => wednesday
  | wednesday => thursday
  | thursday  => friday
  | friday    => monday
  | saturday  => monday
  | sunday    => monday
  end.

Module BoolPlayground.
Inductive bool : Type :=
  | true : bool
  | false : bool.

Derive (Arbitrary, Show) for bool.
Derive (Sized, CanonicalSized) for bool.
Derive SizeMonotonic for bool using genSbool.
Derive SizedMonotonic for bool.
Derive SizedCorrect for bool using genSbool and SizeMonotonicbool.

Definition negb (b:bool) : bool :=
  match b with
  | true => false
  | false => true
  end.

Definition andb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => b2
  | false => false
  end.

Definition orb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => true
  | false => b2
  end.
End BoolPlayground.

Module NatPlayground.

(* Note: nat already exists *)
(* 
Inductive nat : Type :=
  | O : nat
  | S : nat -> nat.
*)

Derive (Arbitrary, Show) for nat.
Derive (Sized, CanonicalSized) for nat.
(* XXX these do not work because there's already an instance for nat. *)
(*
Derive SizeMonotonic for nat using genSnat.
Derive SizedMonotonic for nat.
Derive SizedCorrect for nat using genSnat and SizeMonotonicnat.
*)

Inductive nat' : Type :=
  | stop : nat'
  | tick : nat' -> nat'.

(* Not sure why this works but the above doesn't. If it's nat-specific I don't really care *)
(* Yes it was nat specific. It breaks because there are two instances for nat -- one of them handwritten. *)
Derive (Arbitrary, Show) for nat'.
Derive (Sized, CanonicalSized) for nat'.
Derive SizeMonotonic for nat' using genSnat'.
Derive SizedMonotonic for nat'.
Derive SizedCorrect for nat' using genSnat' and SizeMonotonicnat'.


(** The second branch can be read: "if [n] has the form [S n']
    for some [n'], then return [n']."  *)

End NatPlayground.

Definition pred (n : nat) : nat :=
  match n with
    | O => O
    | S n' => n'
  end.


Definition minustwo (n : nat) : nat :=
  match n with
    | O => O
    | S O => O
    | S (S n') => n'
  end.

Fixpoint evenb (n:nat) : bool :=
  match n with
  | O        => true
  | S O      => false
  | S (S n') => evenb n'
  end.

Definition oddb (n:nat) : bool   :=   negb (evenb n).

Module NatPlayground2.

Fixpoint plus (n : nat) (m : nat) : nat :=
  match n with
    | O => m
    | S n' => S (plus n' m)
  end.

Fixpoint mult (n m : nat) : nat :=
  match n with
    | O => O
    | S n' => plus m (mult n' m)
  end.

Fixpoint minus (n m:nat) : nat :=
  match n, m with
  | O   , _    => O
  | S _ , O    => n
  | S n', S m' => minus n' m'
  end.

End NatPlayground2.

Fixpoint beq_nat (n m : nat) : bool :=
  match n with
  | O => match m with
         | O => true
         | S m' => false
         end
  | S n' => match m with
            | O => false
            | S m' => beq_nat n' m'
            end
  end.

Fixpoint leb (n m : nat) : bool :=
  match n with
  | O => true
  | S n' =>
      match m with
      | O => false
      | S m' => leb n' m'
      end
  end.

Theorem plus_O_n : forall n : nat, 0 + n = n.
Admitted. (* QuickChick plus_O_n. *)

Theorem plus_O_n' : forall n : nat, 0 + n = n.
Admitted. (* QuickChick plus_O_n'. *)

Theorem plus_1_l : forall n:nat, 1 + n = S n.
Admitted. (* QuickChick plus_1_l. *)

Theorem mult_0_l : forall n:nat, 0 * n = 0.
Admitted. (* QuickChick mult_0_l. *)

Theorem plus_0_example: forall n, n = 17 -> n = 42.
Admitted. (* QuickChick plus_0_example. *)

Conjecture plus_id_example : forall n m : nat, n = m -> n + n = m + 0.
QuickChick plus_id_example.

(*
Derive ArbitrarySizedSuchThat for (fun x => eq x a).

QuickChickDebug Debug On.

Derive SizeMonotonicSuchThatOpt for (fun x => eq x a).

Derive SizedProofEqs for (fun x => eq x a).
Proof.
refine (fun x => conj 
   (fun Hin =>
    match Hin with
    | ex_intro s Hc =>
        match Hc with
        | conj Hl Hin =>
            nat_ind
              (fun n =>
               forall x (input0_ : A),
               Basics.impl
                 ((let
                     fix aux_iter size0 (input0_ : A) :=
                       match size0 with
                       | O => setU (set1 input0_) set0
                       | S size' => setU (set1 input0_) set0
                       end in
                   aux_iter n input0_) x) ((@eq A) x input0_))
              (fun x (input0_ : A) hin =>
               match hin with
               | or_introl Hr0 => _ (* eq_ind _ _ (eq_refl _) _ Hr0*)
               | or_intror Hl0 => False_ind _ Hl0
               end)
              (fun size0 IHs x (input0_ : A) hin =>
               match hin with
               | or_introl Hr1 => _ (* eq_ind _ _ (eq_refl _) _ Hr1 *)
               | or_intror Hl1 => False_ind _ Hl1
               end)
              s x input0_ Hin

        end
    end)
   _).
- inversion Hr0; auto.
- inversion Hr1; auto.
- intros H; symmetry in H; move: H.
  apply eq_ind.
  eapply (ex_intro input0_).
Defined.
Defined.
  admit.
Admitted.


  refine ((fun x' => ex_intro _ _) _).
  refine (ex_intro _).
  refine (eq_ind
      (fun _gen (input0_ : A) =>
       bigcup setT
         (fun n =>
          let
            fix aux_iter size0 (input0_ : A) :=
              match size0 with
              | O => setU (set1 input0_) set0
              | S size' => setU (set1 input0_) set0
              end in
          aux_iter n input0_) _gen)
      _ x input0_).
      (fun x => ex_intro _ (Coq.Init.Datatypes.S 0) (conj I (or_introl (Logic.eq_refl _)))) x
      input0_).


Definition s A (input0_ : A) := 
(fun x =>
 conj
   (fun Hin =>
    match Hin with
    | ex_intro s Hc =>
        match Hc with
        | conj Hl Hin =>
            nat_ind
              (fun n =>
               forall x (input0_ : A),
               Basics.impl
                 ((let
                     fix aux_iter size0 (input0_ : A) :=
                       match size0 with
                       | O => setU (set1 input0_) set0
                       | S size' => setU (set1 input0_) set0
                       end in
                   aux_iter n input0_) x) ((@eq A) x input0_))
              (fun x (input0_ : A) hin =>
               match hin with
               | or_introl Hr0 => eq_ind _ _ (eq_refl _) _ Hr0
               | or_intror Hl0 => False_ind _ Hl0
               end)
              (fun size0 IHs x (input0_ : A) hin =>
               match hin with
               | or_introl Hr1 => eq_ind _ _ (eq_refl _) _ Hr1
               | or_intror Hl1 => False_ind _ Hl1
               end) s x input0_ Hin
        end
    end)
   (eq_ind
      (fun _gen (input0_ : A) =>
       bigcup setT
         (fun n =>
          let
            fix aux_iter size0 (input0_ : A) :=
              match size0 with
              | O => setU (set1 input0_) set0
              | S size' => setU (set1 input0_) set0
              end in
          aux_iter n input0_) _gen)
      (fun x => ex_intro _ (Coq.Init.Datatypes.S 0) (conj I (or_introl (Logic.eq_refl _)))) x
      input0_)).


(* TODO: Replace these with derived versions *)
(*

QuickChickDebug Debug On.



Derive GenSizedSuchThatCorrect for (fun eq => eq x a).

Derive GenSizedSuchThatSizeMonotonicOpt for (fun foo => goodFooUnif n foo).
*)
*)


Theorem plus_id_exercise : forall n m o : nat,
  n = m -> m = o -> n + m = m + o.
Admitted.  QuickChick plus_id_exercise.

Theorem mult_0_plus : forall n m : nat,
  (0 + n) * m = n * m. Admitted. (* QuickChick mult_0_plus. *)

Theorem mult_S_1 : forall n m : nat,
  m = S n ->
  m * (1 + n) = m * m.
Admitted. (* QuickChick mult_S_1. *)

Theorem plus_1_neq_0_firsttry : forall n : nat,
  beq_nat (n + 1) 0 = false.
Admitted. (* QuickChick plus_1_neq_0_firsttry. *)

Theorem negb_involutive : forall b : bool,
  negb (negb b) = b. Admitted. (* QuickChick negb_involutive. *)

Theorem andb_commutative : forall b c, andb b c = andb c b.
Admitted. (* QuickChick andb_commutative. *)

Theorem andb_true_elim2 : forall b c : bool,
  andb b c = true -> c = true.
Admitted. (* Leo: OUT-OF-SCOPE *)

Theorem zero_nbeq_plus_1 : forall n : nat,
  beq_nat 0 (n + 1) = false. 
Admitted. (* QuickChick zero_nbeq_plus_1 *)

Theorem identity_fn_applied_twice :
  forall (f : bool -> bool),
  (forall (x : bool), f x = x) ->
  forall (b : bool), f (f b) = b.
Admitted. (* Leo: FUNCTION *)

Theorem andb_eq_orb :
  forall (b c : bool),
  (andb b c = orb b c) ->
  b = c.
Admitted. (* Leo: OUT-OF-SCOPE *)
