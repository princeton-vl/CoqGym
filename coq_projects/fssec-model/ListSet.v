(****************************************************************************)
(*                 The Calculus of Inductive Constructions                  *)
(*                                                                          *)
(*                                Projet Coq                                *)
(*                                                                          *)
(*                     INRIA        LRI-CNRS        ENS-CNRS                *)
(*              Rocquencourt         Orsay          Lyon                    *)
(*                                                                          *)
(*                                 Coq V6.3                                 *)
(*                               July 1st 1999                              *)
(*                                                                          *)
(****************************************************************************)
(*                                ListSet.v                                 *)
(****************************************************************************)

(* A Library for finite sets, implemented as lists *)
(* A Library with similar interface will soon be available under
  the name TreeSet in the theories/TREES directory *)

(* PolyList is loaded, but not exported *)
(* This allow to "hide" the definitions, functions and theorems of PolyList
 and to see only the ones of ListSet *)
Require Import List.

Set Implicit Arguments.
Unset Strict Implicit.
Section first_definitions.


Variable A : Set.
Hypothesis Aeq_dec : forall x y : A, {x = y} + {x <> y}.

Definition set := list A.

Definition empty_set := nil (A:=A). 
 
  Fixpoint set_add (a : A) (x : set) {struct x} : set :=
    match x with
    | nil => a :: nil
    | a1 :: x1 =>
        match Aeq_dec a a1 with
        | left _ => a1 :: x1
        | right _ => a1 :: set_add a x1
        end
    end. 
 
 
  Fixpoint set_mem (a : A) (x : set) {struct x} : bool :=
    match x with
    | nil => false
    | a1 :: x1 =>
        match Aeq_dec a a1 with
        | left _ => true
        | right _ => set_mem a x1
        end
    end. 
  
  (* If a belongs to x, removes a from x. If not, does nothing *) 
  Fixpoint set_remove (a : A) (x : set) {struct x} : set :=
    match x with
    | nil => empty_set
    | a1 :: x1 =>
        match Aeq_dec a a1 with
        | left _ => set_remove a x1
        | right _ => a1 :: set_remove a x1
        end
    end.
 
  Fixpoint set_inter (x : set) : set -> set :=
    match x with
    | nil => fun y => nil (A:=A)
    | a1 :: x1 =>
        fun y =>
        if set_mem a1 y then a1 :: set_inter x1 y else set_inter x1 y
    end. 
 
  Fixpoint set_union (x y : set) {struct y} : set :=
    match y with
    | nil => x
    | a1 :: y1 => set_add a1 (set_union x y1)
    end. 
         
  (* returns the set of all els of x that does not belong to y *) 
  Fixpoint set_diff (x : set) : set -> set :=
    fun y =>
    match x with
    | nil => nil (A:=A)
    | a1 :: x1 =>
        if set_mem a1 y then set_diff x1 y else set_add a1 (set_diff x1 y)
    end. 
    
  (**  
  Inductive set_In : A -> set -> Prop := 
    set_In_singl : (a:A)(x:set)(set_In a (cons a (nil A)))  
  | set_In_add : (a,b:A)(x:set)(set_In a x)->(set_In a (set_add b x)) 
  . 
  **) 
 
  Definition set_In : A -> set -> Prop := In (A:=A). 
 
Lemma Set_remove1 : forall (B : set) (x : A), ~ set_In x (set_remove x B). 
intro; intro. 
induction  B as [| a B HrecB]. 
auto. 
 
simpl in |- *. 
elim (Aeq_dec x a). 
intro. 
unfold not in |- *. 
unfold not in HrecB. 
intro. 
apply HrecB; auto. 
 
intro. 
unfold not in |- *. 
unfold not in HrecB. 
simpl in |- *. 
intro. 
elim H. 
intro. 
cut (a = x /\ a <> x). 
intro. 
auto. 
 
split. 
auto. 
 
auto. 
 
auto. 
 
Qed. 
 
 
 
Lemma set_In_dec : forall (a : A) (x : set), {set_In a x} + {~ set_In a x}. 

unfold set_In in |- *.
simple induction x.
auto.

intros.
cut ({a = a0} + {a <> a0}).
intro Eq_dec; elim Eq_dec.
intro Eq; rewrite Eq; left; auto with datatypes.

elim H.
auto with datatypes.

unfold not in |- *; intros; right; intro.
elim H0; auto.

auto.

Qed.


  Lemma set_mem_ind :
   forall (B : Set) (P : B -> Prop) (y z : B) (a : A) (x : set),
   (set_In a x -> P y) -> P z -> P (if set_mem a x then y else z). 
 
  Proof. 
    simple induction x; simpl in |- *; intros. 
    assumption. 
    elim (Aeq_dec a a0); auto with datatypes. 
  Qed. 
 
  Lemma set_mem_correct1 :
   forall (a : A) (x : set), set_mem a x = true -> set_In a x. 
  Proof. 
    simple induction x; simpl in |- *. 
    discriminate. 
    intros a0 l; elim (Aeq_dec a a0); auto with datatypes. 
  Qed. 
 
  Lemma set_mem_correct2 :
   forall (a : A) (x : set), set_In a x -> set_mem a x = true. 
  Proof. 
    simple induction x; simpl in |- *. 
    intro Ha; elim Ha. 
    intros a0 l; elim (Aeq_dec a a0); auto with datatypes. 
    intros H1 H2 [H3| H4]. 
    absurd (a0 = a); auto with datatypes. 
    auto with datatypes. 
  Qed. 
 
  Lemma set_mem_complete1 :
   forall (a : A) (x : set), set_mem a x = false -> ~ set_In a x. 
  Proof. 
    simple induction x; simpl in |- *. 
    tauto. 
    intros a0 l; elim (Aeq_dec a a0). 
    intros; discriminate H0. 
    unfold not in |- *; intros; elim H1; auto with datatypes. 
  Qed. 
 
  Lemma set_mem_complete2 :
   forall (a : A) (x : set), ~ set_In a x -> set_mem a x = false. 
  Proof. 
    simple induction x; simpl in |- *. 
    tauto. 
    intros a0 l; elim (Aeq_dec a a0). 
    intros; elim H0; auto with datatypes. 
    tauto. 
  Qed. 
 
  Lemma set_add_intro1 :
   forall (a b : A) (x : set), set_In a x -> set_In a (set_add b x). 
 
  Proof. 
    unfold set_In in |- *; simple induction x; simpl in |- *. 
    auto with datatypes. 
    intros a0 l H [Ha0a| Hal]. 
    elim (Aeq_dec b a0); left; assumption. 
    elim (Aeq_dec b a0); right; [ assumption | auto with datatypes ]. 
  Qed. 
 
  Lemma set_add_intro2 :
   forall (a b : A) (x : set), a = b -> set_In a (set_add b x). 
 
  Proof. 
    unfold set_In in |- *; simple induction x; simpl in |- *. 
    auto with datatypes. 
    intros a0 l H Hab. 
    elim (Aeq_dec b a0);
     [ rewrite Hab; intro Hba0; rewrite Hba0; simpl in |- *;
        auto with datatypes
     | auto with datatypes ]. 
  Qed. 
 
  Hint Resolve set_add_intro1 set_add_intro2 Set_remove1. 
 
 
 
  Lemma set_add_intro :
   forall (a b : A) (x : set), a = b \/ set_In a x -> set_In a (set_add b x). 
   
  Proof. 
    intros a b x [H1| H2]; auto with datatypes. 
  Qed. 
  
  Lemma set_add_elim :
   forall (a b : A) (x : set), set_In a (set_add b x) -> a = b \/ set_In a x. 
 
  Proof. 
    unfold set_In in |- *. 
    simple induction x. 
    simpl in |- *; intros [H1| H2]; auto with datatypes. 
    simpl in |- *; do 3 intro. 
    elim (Aeq_dec b a0). 
    tauto. 
    simpl in |- *; intros; elim H0. 
    trivial with datatypes. 
    tauto. 
    tauto. 
  Qed. 
 
  Hint Resolve set_add_intro set_add_elim. 
 
  Lemma set_add_not_empty :
   forall (a : A) (x : set), set_add a x <> empty_set. 
  Proof. 
    simple induction x; simpl in |- *. 
    discriminate. 
    intros; elim (Aeq_dec a a0); intros; discriminate. 
  Qed.    
 
 
  Lemma set_union_intro1 :
   forall (a : A) (x y : set), set_In a x -> set_In a (set_union x y). 
  Proof. 
    simple induction y; simpl in |- *; auto with datatypes. 
  Qed. 
 
  Lemma set_union_intro2 :
   forall (a : A) (x y : set), set_In a y -> set_In a (set_union x y). 
  Proof. 
    simple induction y; simpl in |- *. 
    tauto. 
    intros; elim H0; auto with datatypes. 
  Qed. 
 
  Hint Resolve set_union_intro2 set_union_intro1. 
 
  Lemma set_union_intro :
   forall (a : A) (x y : set),
   set_In a x \/ set_In a y -> set_In a (set_union x y). 
  Proof. 
    intros; elim H; auto with datatypes. 
  Qed. 
 
  Lemma set_union_elim :
   forall (a : A) (x y : set),
   set_In a (set_union x y) -> set_In a x \/ set_In a y. 
  Proof. 
    simple induction y; simpl in |- *. 
    auto with datatypes. 
    intros. 
    generalize (set_add_elim H0). 
    intros [H1| H1]. 
    auto with datatypes. 
    tauto. 
  Qed. 
 
  Lemma set_inter_intro :
   forall (a : A) (x y : set),
   set_In a x -> set_In a y -> set_In a (set_inter x y). 
  Proof. 
    simple induction x. 
    auto with datatypes. 
    simpl in |- *; intros a0 l Hrec y [Ha0a| Hal] Hy. 
    simpl in |- *; rewrite Ha0a. 
    generalize (set_mem_correct1 (a:=a) (x:=y)). 
    generalize (set_mem_complete1 (a:=a) (x:=y)). 
    elim (set_mem a y); simpl in |- *; intros. 
    auto with datatypes. 
    absurd (set_In a y); auto with datatypes. 
    elim (set_mem a0 y); [ right; auto with datatypes | auto with datatypes ].      
  Qed. 
 
  Lemma set_inter_elim1 :
   forall (a : A) (x y : set), set_In a (set_inter x y) -> set_In a x. 
  Proof. 
    simple induction x. 
    auto with datatypes. 
    simpl in |- *; intros a0 l Hrec y. 
    generalize (set_mem_correct1 (a:=a0) (x:=y)). 
    elim (set_mem a0 y); simpl in |- *; intros. 
    elim H0; eauto with datatypes. 
    eauto with datatypes. 
  Qed. 

  Lemma set_inter_elim2 :
   forall (a : A) (x y : set), set_In a (set_inter x y) -> set_In a y. 
  Proof. 
    simple induction x. 
    unfold set_In, set_inter in |- *; unfold In in |- *; tauto.
    simpl in |- *; intros a0 l Hrec y. 
    generalize (set_mem_correct1 (a:=a0) (x:=y)). 
    elim (set_mem a0 y); simpl in |- *; intros. 
    elim H0;
     [ intro Hr; rewrite <- Hr; eauto with datatypes | eauto with datatypes ]. 
    eauto with datatypes. 
  Qed. 
 
  Hint Resolve set_inter_elim1 set_inter_elim2. 
 
  Lemma set_inter_elim :
   forall (a : A) (x y : set),
   set_In a (set_inter x y) -> set_In a x /\ set_In a y. 
  Proof. 
    eauto with datatypes. 
  Qed.  
 
  Lemma set_diff_intro :
   forall (a : A) (x y : set),
   set_In a x -> ~ set_In a y -> set_In a (set_diff x y). 
  Proof. 
    simple induction x. 
    tauto. 
    simpl in |- *; intros a0 l Hrec y [Ha0a| Hal] Hay. 
    rewrite Ha0a; generalize (set_mem_complete2 Hay). 
    elim (set_mem a y);
     [ intro Habs; discriminate Habs | auto with datatypes ]. 
    elim (set_mem a0 y); auto with datatypes. 
  Qed. 
 
  Lemma set_diff_elim1 :
   forall (a : A) (x y : set), set_In a (set_diff x y) -> set_In a x. 
  Proof. 
    simple induction x. 
    tauto. 
    simpl in |- *; intros a0 l Hrec y; elim (set_mem a0 y). 
    eauto with datatypes. 
    intro; generalize (set_add_elim H). 
    intros [H1| H2]; eauto with datatypes. 
  Qed. 
 
End first_definitions. 
 
Section other_definitions. 
 
  Variable A B : Set. 
 
  Definition set_prod : set A -> set B -> set (A * B) :=
    list_prod (A:=A) (B:=B). 
 
  (* B^A, set of applications from A to B *) 
  Definition set_power : set A -> set B -> set (set (A * B)) :=
    list_power (A:=A) (B:=B). 
 
  Definition set_map : (A -> B) -> set A -> set B := map (A:=A) (B:=B). 
 
  Definition set_fold_left : (B -> A -> B) -> set A -> B -> B :=
    fold_left (A:=B) (B:=A). 
 
  Definition set_fold_right (f : A -> B -> B) (x : set A) 
    (b : B) : B := fold_right f b x. 
 
  
End other_definitions. 
 
Set Strict Implicit.
Unset Implicit Arguments. 

 