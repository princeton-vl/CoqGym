(** * Lists: Working with Structured Data *)

From QuickChick Require Import QuickChick.
Import QcDefaultNotation. Open Scope qc_scope.
Import GenLow GenHigh.
Set Warnings "-extraction-opaque-accessed,-extraction".
Require Import List ZArith.
Import ListNotations.
(* 
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import seq ssreflect ssrbool ssrnat eqtype.
*)

Require Export Induction.
Module NatList.

Inductive natprod : Type :=
| pair : nat -> nat -> natprod.
Derive Arbitrary for natprod.
Derive Show for natprod.
Instance natprod_eq (x y : natprod) : Dec (x = y).
constructor. unfold ssrbool.decidable. repeat (decide equality). Defined.

Definition fst (p : natprod) : nat :=
  match p with
  | pair x y => x
  end.

Definition snd (p : natprod) : nat :=
  match p with
  | pair x y => y
  end.

Notation "( x , y )" := (pair x y).

Definition swap_pair (p : natprod) : natprod :=
  match p with
  | (x,y) => (y,x)
  end.

(* BCP: boring! *)
Definition equal_pair (p : natprod) (q : natprod) : bool :=
  match p,q with
  | (p1,p2),(q1,q2) => andb (p1 =? q1) (p2 =? q2)
  end.

Definition surjective_pairing (p : natprod) :=
  equal_pair p (fst p, snd p).
(*! QuickCheck surjective_pairing. *)

Inductive natlist : Type :=
  | nil  : natlist
  | cons : nat -> natlist -> natlist.
Derive Arbitrary for natlist.
Derive Show for natlist.
Instance natlist_eq (x y : natlist) : Dec (x = y).
constructor. unfold ssrbool.decidable. repeat (decide equality). Defined.

Notation "x :: l" := (cons x l)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

Fixpoint repeat (n count : nat) : natlist :=
  match count with
  | O => nil
  | S count' => n :: (repeat n count')
  end.

Fixpoint length (l:natlist) : nat :=
  match l with
  | nil => O
  | h :: t => S (length t)
  end.

Fixpoint app (l1 l2 : natlist) : natlist :=
  match l1 with
  | nil    => l2
  | h :: t => h :: (app t l2)
  end.

Notation "x ++ y" := (app x y)
                     (right associativity, at level 60).

Example test_app1:             [1;2;3] ++ [4;5] = [1;2;3;4;5].
Proof. reflexivity.  Qed.
Example test_app2:             nil ++ [4;5] = [4;5].
Proof. reflexivity.  Qed.
Example test_app3:             [1;2;3] ++ nil = [1;2;3].
Proof. reflexivity.  Qed.

Definition hd (default:nat) (l:natlist) : nat :=
  match l with
  | nil => default
  | h :: t => h
  end.

Definition tl (l:natlist) : natlist :=
  match l with
  | nil => nil
  | h :: t => t
  end.

Definition test_hd1 := hd 0 [1;2;3] =? 1.
(*! QuickChick test_hd1. *)

Fixpoint equal_list l1 l2 :=
  match l1,l2 with
  | [],[] => true
  | h1::t1,h2::t2 => andb (h1=?h2) (equal_list t1 t2)
  | _,_ => false
  end.

Definition test_tl := equal_list (tl [1;2;3]) [2;3].
(*! QuickChick test_tl. *)

Fixpoint alternate (l1 l2 : natlist) : natlist
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *) := [].

Definition bag := natlist.

Definition nil_app := fun l:natlist =>
  equal_list ([] ++ l) l.
(* QuickChick nil_app. *)

Definition tl_length_pred := fun l:natlist =>
  pred (length l) =? length (tl l).

(* Ugh -- temporary hack *)
Definition tl_length_prop := 
  forAllShrink arbitrary shrink tl_length_pred.
(*! QuickChick tl_length_prop. *)

Definition app_assoc := fun l1 l2 l3 : natlist =>
  (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
Instance app_assoc_dec (l1 l2 l3 : natlist) : Dec (app_assoc l1 l2 l3).
unfold app_assoc. apply natlist_eq. Defined.

(* BCP: What do I need to write here?
QuickChick app_assoc.
*)

Fixpoint rev (l:natlist) : natlist :=
  match l with
  | nil    => nil
  | h :: t => rev t ++ [h]
  end.

Definition rev_length := fun l : natlist =>
  length (rev l) =? length l.
(*! QuickChick rev_length. *)

Fixpoint beq_natlist (l1 l2 : natlist) : bool
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *) := false.

(* BCP: Use this elsewhere *)
Definition beq_natlist_refl := fun l:natlist =>
  Bool.eqb true (beq_natlist l l).
QuickChick (expectFailure beq_natlist).

(* BCP: I wonder how best to do this...? *)
Definition rev_injective := fun (l1 l2 : natlist) =>
  (equal_list (rev l1) (rev l2)) ==> equal_list l1 l2.
(* BCP: Probably needs some mutations to be interesting... *)
(*! QuickChick beq_natlist. *)

(* Let's try with the dependent stuff... *)
Inductive eq_list : natlist -> natlist -> Prop :=
  | eq_nil : eq_list [] []
  | eq_cons : forall h l1 l2, eq_list l1 l2 -> eq_list (h::l1) (h::l2).

Inductive snoc_of : natlist -> nat -> natlist -> Prop :=
  | snoc_of_nil : forall x, snoc_of [] x [x]
  | snoc_of_cons : forall x h t t',
      snoc_of t x t' -> snoc_of (h::t) x (h::t').

Derive ArbitrarySizedSuchThat for (fun h  => snoc_of t h t').
Derive ArbitrarySizedSuchThat for (fun t' => snoc_of t h t').

Inductive reverse_of : natlist -> natlist -> Prop :=
  | reverse_of_nil : reverse_of [] []
  | reverse_of_cons : forall h t t' t'',
      reverse_of t t' ->
      snoc_of t' h t'' ->
      reverse_of (h::t) t''.

Derive ArbitrarySizedSuchThat for (fun l => reverse_of l l').
Derive ArbitrarySizedSuchThat for (fun l => reverse_of l' l).

Inductive equal_reverses : (natlist * natlist)%type -> Prop :=
  | eqrev : forall l1 l2 l,
      reverse_of l1 l -> reverse_of l2 l ->
      equal_reverses (Coq.Init.Datatypes.pair l1 l2).

Derive ArbitrarySizedSuchThat for (fun l1l2 => equal_reverses l1l2). 

(* Need to actual write decidability if we want to use it 
Instance equal_reverses_dec l1l2 : Dec (equal_reverses l1l2).
Proof. 
  constructor; unfold ssrbool.decidable. 
  destruct l1l2 as [l1 l2].
  (* ... *)
Admitted.
*)

Definition rev_injective_checker : Checker :=
  forAll (genST (fun l1l2 => equal_reverses l1l2))
         (fun l1l2 => match l1l2 with 
                        | Some (Coq.Init.Datatypes.pair l1 l2) => ((l1 = l2)?)
                        | None => true
                      end).

QuickChick rev_injective_checker.

Fixpoint nth_bad (l:natlist) (n:nat) : nat :=
  match l with
  | nil => 42  (* arbitrary! *)
  | a :: l' => match beq_nat n O with
               | true => a
               | false => nth_bad l' (pred n)
               end
  end.

Inductive natoption : Type :=
  | Some : nat -> natoption
  | None : natoption.
Derive Arbitrary for natoption.
Derive Show for natoption.
Instance natoption_eq (x y : natoption) : Dec (x = y).
constructor. unfold ssrbool.decidable. repeat (decide equality). Defined.

Fixpoint nth_error (l:natlist) (n:nat) : natoption :=
  match l with
  | nil => None
  | a :: l' => match beq_nat n O with
               | true => Some a
               | false => nth_error l' (pred n)
               end
  end.

(* BCP: Fix *)
Definition test_nth_error1 :=
  (nth_error [4;5;6;7] 0) = (Some 4)?.
(*! QuickChick test_nth_error1. *)

End NatList.

Inductive id : Type :=
  | Id : nat -> id.
Derive Arbitrary for id.
Derive Show for id.
Instance id_eq (x y : id) : Dec (x = y).
constructor. unfold ssrbool.decidable. repeat (decide equality). Defined.

Definition beq_id (x1 x2 : id) :=
  match x1, x2 with
  | Id n1, Id n2 => beq_nat n1 n2
  end.

(* BCP: Extraction inside modules is broken! *)
(*
Module PartialMap.
*)
Export NatList.
  
Inductive partial_map : Type :=
  | empty  : partial_map
  | record : id -> nat -> partial_map -> partial_map.
Derive Arbitrary for partial_map.
Derive Show for partial_map.
Instance partial_map_eq (x y : partial_map) : Dec (x = y).
constructor. unfold ssrbool.decidable. repeat (decide equality). Defined.

Definition update (d : partial_map)
                  (x : id) (value : nat)
                  : partial_map :=
  record x value d.

Fixpoint find (x : id) (d : partial_map) : natoption :=
  match d with
  | empty         => None
  | record y v d' => if beq_id x y
                     then Some v
                     else find x d'
  end.

Definition update_eq :=
  fun (d : partial_map) (x : id) (v: nat) =>
    (find x (update d x v) = Some v)?.
(*! QuickChick update_eq. *)

