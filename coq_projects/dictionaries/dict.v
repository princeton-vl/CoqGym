(* This program is free software; you can redistribute it and/or      *)
(* modify it under the terms of the GNU Lesser General Public License *)
(* as published by the Free Software Foundation; either version 2.1   *)
(* of the License, or (at your option) any later version.             *)
(*                                                                    *)
(* This program is distributed in the hope that it will be useful,    *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of     *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the      *)
(* GNU General Public License for more details.                       *)
(*                                                                    *)
(* You should have received a copy of the GNU Lesser General Public   *)
(* License along with this program; if not, write to the Free         *)
(* Software Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA *)
(* 02110-1301 USA                                                     *)


(* (C) Pierre Castéran , LaBRI, Universite Bordeaux 1,
                     Inria Futurs
Dictionaries (after Paulson : ML for the working programmer) *)

Require Import Relations.
Require Import List.

Set Asymmetric Patterns.
Unset Standard Proposition Elimination Names.

(* Dictionaries : a dictionary is roughly a partial maping from
   keys to values  *)

Module Type DICT.
 Parameter key : Set. 
 Parameter data : Set. (* data associated with keys *)
 Parameter dict : Set. (* the type associated with dictionaries *)
 Parameter empty : dict. (* dictionary without any entry *)
 Parameter add : key -> data -> dict -> dict. (* add an entry to a dictionary *)
 Parameter find : key -> dict -> option data. (* get the value from the key  *)

 (* relationships between find, add and empty *)        

 Axiom empty_def : forall k : key, find k empty = None.
 Axiom
   success :
     forall (d : dict) (k : key) (v : data), find k (add k v d) = Some v.
 Axiom
   diff_key :
     forall (d : dict) (k k' : key) (v : data),
     k <> k' -> find k (add k' v d) = find k d.
End DICT.





(* building a dictionary from a list of entries *)
Module Type DICT_PLUS.
 Declare Module Dict : DICT.
 Parameter build : list (Dict.key * Dict.data) -> Dict.dict.
End DICT_PLUS.


Module Dict_Plus (D: DICT) : DICT_PLUS with Module Dict := D.
 Module Dict := D.
 Definition key := D.key.
 Definition data := D.data. 
 Definition dict := D.dict.
 Definition add := D.add.
 Definition empty := D.empty.

 Fixpoint addlist (l : list (key * data)) : dict -> dict :=
   fun d : dict =>
   match l with
   | nil => d
   | p :: l' => match p with
                | (k, v) => addlist l' (add k v d)
                end
   end.

 Definition build (l : list (key * data)) := addlist l empty.
End Dict_Plus.




(* keys for dictionaries 
   We just need a data type on which Leibniz equality is decidable
*)

Module Type KEY.
 Parameter A : Set.
 Parameter eqdec : forall a b : A, {a = b} + {a <> b}.
End KEY.

Module LKey (K: KEY) : KEY with Definition A := list K.A.
 Definition A := list K.A.

 Definition eqdec : forall a b : A, {a = b} + {a <> b}.
  intro a; elim a.
  simple induction b; [ left; auto | right; red in |- *; discriminate 1 ].
  intros a0 k Ha; simple induction b.
  right; red in |- *; discriminate 1.
  intros a1 l0 s; case (K.eqdec a0 a1); intro H0.
  case (Ha l0); intro H1.
  left; rewrite H1; rewrite H0; auto.
  right; red in |- *; injection 1.
  intro H3; case (H1 H3).
  right; red in |- *; injection 1.
  intros H3 H4; case (H0 H4).
 Defined.
End LKey.

Require Import ZArith.
Module ZKey : KEY with Definition A := Z.
  Definition A := Z.
  Definition eqdec := Z_eq_dec.
End ZKey.


Module LZKey := LKey ZKey.

(* 
Check (LZKey.eqdec (cons `7` (nil ?)) (cons `3+4` (nil ?))).
*)

(* pairs of keys *)

Module PairKey (K1: KEY) (K2: KEY) : KEY with Definition
  A := (K1.A * K2.A)%type.
 Definition A := (K1.A * K2.A)%type.

 Definition eqdec : forall a b : A, {a = b} + {a <> b}.
    simple destruct a. 
    intros a0 a1; simple destruct b; intros b0 b1.
    case (K1.eqdec a0 b0); intro H; case (K2.eqdec a1 b1); intro H0;
     [ left | right | right | right ]; try (rewrite H; rewrite H0; trivial);
     red in |- *; intro H1; injection H1; tauto.
 Defined.
End PairKey.


(* Total decidable orders *)

Module Type DEC_ORDER.
 Parameter A : Set.
 Parameter le : A -> A -> Prop.
 Parameter lt : A -> A -> Prop.
 Axiom ordered : order A le.
 Axiom lt_le_weak : forall a b : A, lt a b -> le a b.
 Axiom lt_diff : forall a b : A, lt a b -> a <> b.
 Axiom le_lt_or_eq : forall a b : A, le a b -> lt a b \/ a = b.
 Parameter lt_eq_lt_dec : forall a b : A, {lt a b} + {a = b} + {lt b a}.
End DEC_ORDER.

(* some derived theorems on dec_orders *)

Module Type MORE_DEC_ORDERS.
  Parameter A : Set.
  Parameter le : A -> A -> Prop.
  Parameter lt : A -> A -> Prop.
  Axiom le_trans : transitive A le.
  Axiom le_refl : reflexive A le.
  Axiom le_antisym : antisymmetric A le.
  Axiom lt_irreflexive : forall a : A, ~ lt a a.
  Axiom lt_trans : transitive A lt.
  Axiom lt_not_le : forall a b : A, lt a b -> ~ le b a.
  Axiom le_not_lt : forall a b : A, le a b -> ~ lt b a.
  Axiom lt_intro : forall a b : A, le a b -> a <> b -> lt a b.
  Parameter le_lt_dec : forall a b : A, {le a b} + {lt b a}.
  Parameter le_lt_eq_dec : forall a b : A, le a b -> {lt a b} + {a = b}.
End MORE_DEC_ORDERS.


(* A functor for getting some useful derived properties on decidable
   orders *)

Module More_Dec_Orders (D: DEC_ORDER) : MORE_DEC_ORDERS with Definition
  A := D.A with Definition le := D.le with Definition lt := D.lt.
                                       
 Definition A := D.A.
 Definition le := D.le.
 Definition lt := D.lt.
 
 Theorem le_trans : transitive A le.
 Proof.
   case D.ordered; auto.
 Qed.

 Theorem le_refl : reflexive A le.
  Proof.
   case D.ordered; auto.
 Qed.
 
 Theorem le_antisym : antisymmetric A le.
 Proof.
   case D.ordered; auto.
 Qed.

 Theorem lt_intro : forall a b : A, le a b -> a <> b -> lt a b.
 Proof.
   intros a b H diff; case (D.le_lt_or_eq a b H); tauto.
 Qed.
 
 Theorem lt_irreflexive : forall a : A, ~ lt a a.  
 Proof.
  intros a H.
  case (D.lt_diff _ _ H); trivial.
 Qed.

 Theorem lt_not_le : forall a b : A, lt a b -> ~ le b a.
 Proof.
  intros a b H H0.
  absurd (a = b).
  apply D.lt_diff; trivial.
  apply le_antisym; auto; apply D.lt_le_weak; assumption.
 Qed.

 Theorem le_not_lt : forall a b : A, le a b -> ~ lt b a.
 Proof.
   intros a b H H0; apply (lt_not_le b a); auto.  
  Qed.

  Theorem lt_trans : transitive A lt.
  Proof.    
   unfold A, transitive in |- *.
   intros x y z H H0.
   apply (lt_intro x z).
   apply le_trans with y; apply D.lt_le_weak; assumption.
   intro e; rewrite e in H.
   absurd (y = z).
   intro e'; rewrite e' in H. 
   apply (lt_irreflexive _ H). 
   apply le_antisym; apply D.lt_le_weak; trivial.
  Qed.

  Definition le_lt_dec : forall a b : A, {le a b} + {lt b a}.
   intros a b; case (D.lt_eq_lt_dec a b).
   intro d; case d; auto.  
   left; apply D.lt_le_weak; trivial. 
   simple induction 1; left; apply le_refl.
   right; trivial.
  Defined.

  Definition le_lt_eq_dec : forall a b : A, le a b -> {lt a b} + {a = b}.
   intros a b H.
   case (D.lt_eq_lt_dec a b).
   trivial. 
   intro H0; case (le_not_lt a b H H0).
  Defined.

End More_Dec_Orders.

(* the forgetful functor ! *)
Module Forget_Order (D: DEC_ORDER) : KEY with Definition A := D.A.

 Module M := More_Dec_Orders D. 

 Definition A := D.A.

 Definition eqdec : forall a b : A, {a = b} + {a <> b}. 
  intros a b; case (D.lt_eq_lt_dec a b).
  intro H; case H.   
  right; apply D.lt_diff; auto.
  left; trivial.
  intro d; right. 
  intro e; rewrite e in d.
  apply (M.lt_irreflexive b); auto.
 Defined.
End Forget_Order.
 

(* Lexicographic ordering *)

Module Lexico (D1: DEC_ORDER) (D2: DEC_ORDER) <: DEC_ORDER with Definition
  A := (D1.A * D2.A)%type.

 Module M1 := More_Dec_Orders D1.
 Module M2 := More_Dec_Orders D2.

 Definition A := (D1.A * D2.A)%type.
 
 Definition le (a b : A) : Prop :=
   let (a1, a2) := a in
   let (b1, b2) := b in D1.lt a1 b1 \/ a1 = b1 /\ D2.le a2 b2.
 
 Definition lt (a b : A) : Prop :=
   let (a1, a2) := a in
   let (b1, b2) := b in D1.lt a1 b1 \/ a1 = b1 /\ D2.lt a2 b2.


 Theorem ordered : order A le.
 Proof.
  split.
  unfold reflexive in |- *; intros.
  unfold le in |- *; case x. 
  right.
  split; [ trivial | apply M2.le_refl; auto ].
  unfold le, transitive in |- *. 
  simple destruct x; simple destruct y; simple destruct z. 
  simple destruct 1; intro H1.
  simple destruct 1.
  left.
  eapply M1.lt_trans.
  eexact H1.
  assumption.
  simple destruct 1.
  simple destruct 1.
  auto.
  simple destruct 1.
  intro. 
  case H1; intros e H3; rewrite e; auto.
  case H1; intros e H3; rewrite e; auto.
  simple destruct 1.
  simple destruct 1.
  right.
  split; try auto. 
  eapply M2.le_trans; eauto.
  unfold antisymmetric, A, le in |- *.
  simple destruct x; simple destruct y.
  simple destruct 1; simple destruct 2.
  intro.
  absurd (D1.lt a1 a1).   
  apply M1.lt_irreflexive. 
  eapply M1.lt_trans; eauto.
  simple destruct 1; intros e H3.
  rewrite e in H0.
  case (M1.lt_irreflexive a H0).
  case H0; intros e H3.
  rewrite e; intro H2.
  case (M1.lt_irreflexive a1 H2).
  simple destruct 1; intros e H3; rewrite e.  
  case (M2.le_antisym a2 a0).
  auto.
  case H0; auto.
  auto.
 Qed.

 Theorem lt_le_weak : forall a b : A, lt a b -> le a b.
 Proof.
  unfold A, lt, le in |- *; intros a b; case a; case b. 
  simple destruct 1; intros; auto.
  right; case H0; split; auto.
  apply D2.lt_le_weak; trivial.   
 Qed.


 Theorem lt_diff : forall a b : A, lt a b -> a <> b.
 Proof.
  unfold A, lt, le in |- *; intros a b; case a; case b. 
  simple destruct 1.
  intro H0; red in |- *; injection 1.
  intros e1 e2; rewrite e2 in H0.
  case (M1.lt_irreflexive a0 H0).
  simple destruct 1.
  simple destruct 1.   
  intro H2; red in |- *; injection 1.
  intro e; rewrite e in H2; case (M2.lt_irreflexive _ H2).
 Qed.

 Theorem le_lt_or_eq : forall a b : A, le a b -> lt a b \/ a = b.
 Proof.
  unfold A, lt, le in |- *; intros a b; case a; case b. 
  simple destruct 1; auto.
  simple destruct 1.
  simple destruct 1.
  intro H2; case (D2.le_lt_or_eq _ _ H2).
  auto.
  simple destruct 1. 
  auto. 
 Qed.


 Definition lt_eq_lt_dec : forall a b : A, {lt a b} + {a = b} + {lt b a}.
  Proof.
   unfold A, lt in |- *; intros.
   case a; case b.
   intros a0 a1 a2 a3.  
   case (D1.lt_eq_lt_dec a0 a2).
   simple destruct 1.
   right.
   auto.
   simple destruct 1.
   case (D2.lt_eq_lt_dec a1 a3).
   simple destruct 1.
   right.
   auto.
   simple destruct 1.
   left; right; trivial.
   left; left; auto.
   left.
   left; auto.
  Defined.
End Lexico.


(* order on disjoint sums *)

Module Sum_Order (O1: DEC_ORDER) (O2: DEC_ORDER) <: DEC_ORDER with Definition
  A := (O1.A + O2.A)%type.

 Definition A := (O1.A + O2.A)%type.
 
 Definition le (a b : A) : Prop :=
   match a with
   | inl a' => match b with
               | inl b' => O1.le a' b'
               | _ => True
               end
   | inr a' => match b with
               | inr b' => O2.le a' b'
               | _ => False
               end
   end.

  Definition lt (a b : A) : Prop :=
    match a with
    | inl a' => match b with
                | inl b' => O1.lt a' b'
                | _ => True
                end
    | inr a' => match b with
                | inr b' => O2.lt a' b'
                | _ => False
                end
    end.


 Module M1 := More_Dec_Orders O1.
 Module M2 := More_Dec_Orders O2.
  
 Theorem ordered : order A le.
 Proof.
  split.
  unfold reflexive in |- *; intros.
  unfold le in |- *.
  case x. 
  exact M1.le_refl.
  exact M2.le_refl.
  unfold le in |- *.  
  unfold transitive in |- *. 
  simple destruct x; simple destruct y; simple destruct z. 
  intros; eapply M1.le_trans; eauto.
  auto.
  contradiction.
  auto.
  auto.  
  contradiction.
  auto.
  intros; eapply M2.le_trans; eauto.
  unfold antisymmetric, A, le in |- *.
  simple destruct x; simple destruct y.
  intros a0 H0 H1; rewrite (M1.le_antisym _ _ H0 H1).
  trivial.
  contradiction.
  contradiction.  
  intros a0 H0 H1; rewrite (M2.le_antisym _ _ H0 H1).
  trivial.
 Qed.


 Theorem lt_le_weak : forall a b : A, lt a b -> le a b.
 Proof.
   unfold A, lt, le in |- *; intros a b.
   case a; case b; auto. 
   intros; apply O1.lt_le_weak; trivial.
   intros; apply O2.lt_le_weak; trivial.
 Qed.

 Theorem lt_diff : forall a b : A, lt a b -> a <> b.
 Proof.
    unfold lt in |- *; simple destruct a; simple destruct b.
    intros a1 H e; injection e; intro e'.
    case (O1.lt_diff _ _ H e').
    intros a1 H e; discriminate e.
    contradiction.
    intros a1 H e; injection e; intro e'.
    case (O2.lt_diff _ _ H e').
 Qed.
 
 Theorem le_lt_or_eq : forall a b : A, le a b -> lt a b \/ a = b.
 Proof.
   unfold A, lt, le in |- *; intros a b; case a; case b. 
   intros a0 a1 H; case (O1.le_lt_or_eq a1 a0 H).
   auto.
   simple destruct 1; auto.
   auto.
   contradiction.
   intros a0 a1 H; case (O2.le_lt_or_eq a1 a0 H); auto.
   simple destruct 1; auto.
 Qed.

 Definition lt_eq_lt_dec : forall a b : A, {lt a b} + {a = b} + {lt b a}.
  unfold A, lt in |- *; intros.
  case a; case b.
  intros a0 a1.
  case (O1.lt_eq_lt_dec a0 a1).
  simple destruct 1.
  right.
  auto.
  simple destruct 1.
  left.
  right.
  trivial. 
  left.
  left.
  trivial.
  left; trivial.
  left; trivial.
  right. 
  auto. 
  intros a0 a1.
  case (O2.lt_eq_lt_dec a0 a1).
  simple destruct 1.
  right.
  auto.
  simple destruct 1.
  left.
  right.
  trivial. 
  left.
  left.
  trivial.
 Defined.

End Sum_Order. 

Require Import Arith.

Module Nat_Order : DEC_ORDER with Definition A := nat with Definition
  le := le with Definition lt := lt.
  Definition A := nat.
  Definition le := le.
  Definition lt := lt.
  Theorem ordered : order A le.
  Proof.
    split.   
    unfold A, le, reflexive in |- *; auto with arith. 
    unfold A, le, transitive in |- *; eauto with arith. 
    unfold A, le, antisymmetric in |- *; eauto with arith. 
  Qed.


  Theorem lt_le_weak : forall a b : A, lt a b -> le a b.
  Proof.
   unfold A in |- *; exact lt_le_weak.  
  Qed.
 
  Theorem lt_diff : forall a b : A, lt a b -> a <> b.
  Proof.
   unfold A, lt, le in |- *; intros a b H e. 
   rewrite e in H.
   case (lt_irrefl b H).
  Qed.

  Theorem le_lt_or_eq : forall a b : A, le a b -> lt a b \/ a = b.
  Proof.
   unfold A, le, lt in |- *.  
   exact le_lt_or_eq.
  Qed.
  
  Definition lt_eq_lt_dec : forall a b : A, {lt a b} + {a = b} + {lt b a} :=
    lt_eq_lt_dec.
  
End Nat_Order. 

 (* the natural order on booleans ( false < true ) *)

 Definition bool_le (b b' : bool) :=
   if b then if b' then True else False else True.
 Definition bool_lt (b b' : bool) :=
   if b then False else if b' then True else False.


 Module Bool_Order : DEC_ORDER with Definition A := bool with Definition
   le := bool_le with Definition lt := bool_lt.
  Definition A := bool.
  Definition le := bool_le.
  Definition lt := bool_lt.
  
  Theorem ordered : order A le.
  Proof.
    split.   
    unfold A, le, reflexive in |- *. 
    intro x; case x; simpl in |- *; auto.
    unfold A, le, transitive in |- *; simple destruct x; simple destruct y;
     auto; simple destruct z; auto. 
    unfold A, le, antisymmetric in |- *; simple destruct x; simple destruct y;
     simpl in |- *; auto; contradiction.
  Qed.

  Theorem lt_le_weak : forall a b : A, lt a b -> le a b.
  Proof.
   unfold A, lt, le in |- *; simple destruct a; simple destruct b;
    simpl in |- *; tauto. 
  Qed.

  Theorem lt_diff : forall a b : A, lt a b -> a <> b. 
  Proof.
    unfold A, lt, bool_lt in |- *; simple destruct a; simple destruct b; auto.
  Qed.

  Theorem le_lt_or_eq : forall a b : A, le a b -> lt a b \/ a = b.
  Proof.
   unfold A, le, lt, bool_lt in |- *; simple destruct a; simple destruct b;
    auto.
  Qed.

 Definition lt_eq_lt_dec : forall a b : A, {lt a b} + {a = b} + {lt b a}. 
    unfold A, le, lt, bool_lt in |- *; simple destruct a; simple destruct b;
     auto.                   
 Defined.
End Bool_Order.


(* This module type specifies the domain of values returned by
   consulting a dictionary ; it is supposed to be an argument of
   any functor building an implementation for dictionaries *)

Module Type DATA.
 Parameter data : Set.
End DATA.




(* A simple implementation of dictionaries : 
   the dictionary IS the (partial) function from keys to values 
   This implementation is clearly inefficient, but since it is
   trivially correct ; during the building  of a modular program,
   such trivial correct implementations of module types  may be
   very useful during the development steps of an application  *)



Module TrivialDict (Key: KEY) (Val: DATA) : DICT with Definition key := Key.A
  with Definition data := Val.data.
 Definition key := Key.A.
 Definition data := Val.data.
 Definition dict := key -> option data.

 Definition empty (k : key) := None (A:=data).
 Definition find (k : key) (d : dict) := d k.
 Definition add (k : key) (v : data) (d : dict) : dict :=
   fun k' : key =>
   match Key.eqdec k' k with
   | left _ => Some v
   | right _ => d k'
   end.

 Theorem empty_def : forall k : key, find k empty = None.
 Proof.
  unfold find, empty in |- *; auto.
 Qed. 

 Theorem success :
  forall (d : dict) (k : key) (v : data), find k (add k v d) = Some v.
 Proof. 
  unfold find, add in |- *; intros d k v. 
  case (Key.eqdec k k); simpl in |- *; tauto.
 Qed.
  
 Theorem diff_key :
  forall (d : dict) (k k' : key) (v : data),
  k <> k' -> find k (add k' v d) = find k d.
 Proof.
  unfold find, add in |- *; intros d k k' v. 
  case (Key.eqdec k k'); simpl in |- *; tauto.
 Qed.

End TrivialDict.



(* dictionaries based on searchtrees 
we require a total decidable order on keys *)

Module TDict (Key: DEC_ORDER) (Val: DATA) : DICT with Definition key := Key.A
  with Definition data := Val.data.
 Definition key := Key.A.
 Definition data := Val.data.

 Module M := More_Dec_Orders Key.

 (* search trees definitions and properties *)

 (* the underlying data structure : binary trees labeled 
    with keys and associated values *)

 Inductive btree : Set :=
   | leaf : btree
   | bnode : key -> data -> btree -> btree -> btree.

 (* The entry with key k and value v occurs in the binary tree t *)

 Inductive occ (v : data) (k : key) : btree -> Prop :=
   | occ_root : forall t1 t2 : btree, occ v k (bnode k v t1 t2)
   | occ_l :
       forall (k' : key) (v' : data) (t1 t2 : btree),
       occ v k t1 -> occ v k (bnode k' v' t1 t2)
   | occ_r :
       forall (k' : key) (v' : data) (t1 t2 : btree),
       occ v k t2 -> occ v k (bnode k' v' t1 t2).


(*  key k is less than every key in t  *)
 Inductive min (k : key) (t : btree) : Prop :=
     min_intro :
       (forall (k' : key) (v : data), occ v k' t -> Key.lt k k') -> min k t.

 Hint Resolve min_intro: searchtrees.


(*  key k is gretaer than every key in t  *)
 Inductive maj (k : key) (t : btree) : Prop :=
     maj_intro :
       (forall (k' : key) (v : data), occ v k' t -> Key.lt k' k) -> maj k t.

 Hint Resolve maj_intro: searchtrees.

(* searchness predicate on binary trees *)
 Inductive search_tree : btree -> Prop :=
   | leaf_search_tree : search_tree leaf
   | bnode_search_tree :
       forall (k : key) (v : data) (t1 t2 : btree),
       search_tree t1 ->
       search_tree t2 ->
       maj k t1 -> min k t2 -> search_tree (bnode k v t1 t2).

 Inductive is_bnode : btree -> Prop :=
     is_bnode_intro :
       forall (k : key) (v : data) (t1 t2 : btree),
       is_bnode (bnode k v t1 t2).

 Hint Resolve is_bnode_intro: searchtrees.

 Hint Resolve occ_root occ_l occ_r: searchtrees.

 Derive Inversion_clear OCC_INV with
  (forall (k k' : key) (v v' : data) (t1 t2 : btree),
   occ v' k' (bnode k v t1 t2)).


 Lemma occ_inv :
  forall (k k' : key) (v v' : data) (t1 t2 : btree),
  occ v' k' (bnode k v t1 t2) ->
  k = k' /\ v = v' \/ occ v' k' t1 \/ occ v' k' t2.
 Proof.
  intros k k' v v' t1 t2 H.
  inversion H using OCC_INV; auto with searchtrees.
 Qed.

 Hint Resolve occ_inv: searchtrees.

 Lemma not_occ_Leaf : forall (k : key) (v : data), ~ occ v k leaf.
 Proof.
  unfold not in |- *; intros k v H.
  inversion_clear H.
 Qed.

 Hint Resolve not_occ_Leaf: searchtrees.

 Hint Resolve leaf_search_tree bnode_search_tree: searchtrees.

 Lemma min_leaf : forall k : key, min k leaf.
 Proof.
  intro k; apply min_intro.
  inversion_clear 1.
 Qed.

 Hint Resolve min_leaf: searchtrees.

 Lemma maj_leaf : forall k : key, maj k leaf.
 Proof.
  intro k; apply maj_intro; inversion_clear 1.
 Qed.

 Hint Resolve maj_leaf: searchtrees.


 Lemma maj_not_occ :
  forall (k : key) (v : data) (t : btree), maj k t -> ~ occ v k t.
 Proof.
  unfold not in |- *; intros k v t H H'.
  elim H; intros; absurd (Key.lt k k); auto.
  apply M.lt_irreflexive. 
  eauto.
 Qed.

 Hint Resolve maj_not_occ: searchtrees.

 Lemma min_not_occ :
  forall (k : key) (v : data) (t : btree), min k t -> ~ occ v k t.
 Proof.
  unfold not in |- *; intros k v t H H'.
  elim H; intros; absurd (Key.lt k k); eauto.
  apply M.lt_irreflexive. 
 Qed.


 Hint Resolve min_not_occ: searchtrees.

(* technical lemmas about some non-leaf search tree *)

 Section search_tree_basic_properties.

 Variables (n : key) (v : data) (t1 t2 : btree).
 
 Hypothesis se : search_tree (bnode n v t1 t2).


 Lemma search_tree_l : search_tree t1.
 Proof.
  inversion_clear se; auto with searchtrees.
 Qed.

 Hint Resolve search_tree_l: searchtrees.

 Lemma search_tree_r : search_tree t2.
 Proof.
  inversion_clear se; auto with searchtrees.
 Qed.
 Hint Resolve search_tree_r: searchtrees.

 Lemma maj_l : maj n t1.
 Proof.
  inversion_clear se; auto with searchtrees.
 Qed.
 Hint Resolve maj_l: searchtrees.

 Lemma min_r : min n t2.
 Proof.
  inversion_clear se; auto with searchtrees.
 Qed.

 Hint Resolve min_r: searchtrees.

 Lemma not_right : forall (p : key) (v' : data), Key.le p n -> ~ occ v' p t2.
 Proof.
  intros p v' H; elim min_r.
  unfold not in |- *; intros; absurd (Key.lt n p); eauto with searchtrees.
  apply M.le_not_lt; assumption.
 Qed.

 Hint Resolve not_right: searchtrees.
 
 Lemma not_left : forall (p : key) (v' : data), Key.le n p -> ~ occ v' p t1.
 Proof.
  intros p v' H; elim maj_l.
  unfold not in |- *; intros; absurd (Key.lt p n); eauto with searchtrees.
  apply M.le_not_lt; assumption.
 Qed.

 Hint Resolve not_left: searchtrees.

 Lemma go_left :
  forall (p : key) (v' : data),
  occ v' p (bnode n v t1 t2) -> Key.lt p n -> occ v' p t1.
 Proof.
  intros p v' H H0.    
  case (occ_inv _ _ _ _ _ _ H).
  repeat simple destruct 1; absurd (Key.lt p n). 
  rewrite H2; apply M.lt_irreflexive. 
  assumption.
  simple destruct 1; trivial.
  intro H2; absurd (occ v' p t2).
  apply not_right.
  apply Key.lt_le_weak; assumption. 
  auto.
 Qed.

 Lemma go_right :
  forall (p : key) (v' : data),
  occ v' p (bnode n v t1 t2) -> Key.lt n p -> occ v' p t2.
 Proof.
  intros p v' H H0.    
  case (occ_inv _ _ _ _ _ _ H).
  repeat simple destruct 1; absurd (Key.lt n p). 
  rewrite H2; apply M.lt_irreflexive. 
  assumption.
  simple destruct 1; trivial.
  intro H2; absurd (occ v' p t1).
  apply not_left.
  apply Key.lt_le_weak; assumption. 
  auto.
 Qed.

 End search_tree_basic_properties.

 Hint Resolve go_left go_right not_left not_right search_tree_l search_tree_r
   maj_l min_r: searchtrees.

(* each key occurs at most once *)

 Lemma occ_unicity :
  forall t : btree,
  search_tree t ->
  forall (k : key) (v v' : data), occ v k t -> occ v' k t -> v = v'.
 Proof. (* too long, but proofs are irrelevant, are'nt they ? *)
  simple induction t.
  inversion 2.
  intros.
  case (occ_inv _ _ _ _ _ _ H2). 
  repeat simple destruct 1. 
  case (occ_inv _ _ _ _ _ _ H3). 
  tauto.
  simple destruct 1.
  intro.
  absurd (occ v' k0 b); auto.
  eapply not_left.  
  eauto.
  rewrite H5; apply M.le_refl.
  intro.
  absurd (occ v' k0 b0); auto.
  eapply not_right; eauto. 
  rewrite H5; apply M.le_refl.
  simple destruct 1; intro.
  case (occ_inv _ _ _ _ _ _ H3).
  repeat simple destruct 1.
  absurd (occ v k b); auto.
  eapply not_left; eauto. 
  apply M.le_refl.
  rewrite H7; auto.
  simple destruct 1; intro.
  eapply H.
  eauto with searchtrees.
  eauto.
  assumption.
  absurd (occ v' k0 b0); auto.
  eapply not_right; eauto with searchtrees.
  case (maj_l _ _ _ _ H1).
  intro; apply Key.lt_le_weak.
  eauto.
  case (occ_inv _ _ _ _ _ _ H3).
  repeat simple destruct 1.
  absurd (occ v k0 b0); auto.
  case H7.
  eapply not_right; eauto with searchtrees.
  apply M.le_refl.
  simple destruct 1.
  intro.
  absurd (occ v' k0 b); auto.
  eapply not_left; eauto with searchtrees.
  case (min_r _ _ _ _ H1).
  intros.
  apply Key.lt_le_weak.
  eauto.
  intro.
  eapply H0. 
  eauto with searchtrees.
  eauto.
  eauto. 
 Qed.
 
(* given a key and a search tree, we return either an associated value
   or the proof of its non-existence *)

 Definition occ_dec_spec (k : key) (t : btree) :=
   search_tree t -> {v : data | occ v k t} + {(forall v : data, ~ occ v k t)}.


 Definition occ_dec : forall (k : key) (t : btree), occ_dec_spec k t.
  intro p; simple induction t.
  right.
  auto with searchtrees.
  intros n v t1 R1 t2 R2 H.
  case (M.le_lt_dec p n).
  intro H0; case (M.le_lt_eq_dec p n H0).
  intro H1; case R1.
  eauto with searchtrees.
  simple destruct 1; intros v' H'.
  left.
  exists v'; eauto with searchtrees.
  right.
  intros v0 H3.
  apply (n0 v0); eauto with searchtrees.
  simple destruct 1; left.
  exists v; eauto with searchtrees.
  intro H2; case R2.
  eauto with searchtrees.
  simple destruct 1; intros v' H'.
  left.
  exists v'; eauto with searchtrees.
  right.
  intros v0 H3.
  apply (n0 v0); eauto with searchtrees.
 Defined.

(* t' is obtained by inserting (n,v) into t *)

 Inductive INSERT (n : key) (v : data) (t t' : btree) : Prop :=
     insert_intro :
       (forall (p : key) (v' : data), occ v' p t -> p = n \/ occ v' p t') ->
       occ v n t' ->
       (forall (p : key) (v' : data),
        occ v' p t' -> occ v' p t \/ n = p /\ v = v') ->
       search_tree t' -> INSERT n v t t'.

 Hint Resolve insert_intro: searchtrees.


 Definition insert_spec (n : key) (v : data) (t : btree) : Set :=
   search_tree t -> {t' : btree | INSERT n v t t'}.



 Lemma insert_leaf :
  forall (n : key) (v : data), INSERT n v leaf (bnode n v leaf leaf).
 Proof.
  intro n; split; auto with searchtrees.
  intros p k H; inversion_clear H; auto with searchtrees. 
 Qed.
 Hint Resolve insert_leaf: searchtrees.



(* Inserting in the left son *)

 Lemma insert_l :
  forall (n p : key) (v v' : data) (t1 t'1 t2 : btree),
  Key.lt n p ->
  search_tree (bnode p v' t1 t2) ->
  INSERT n v t1 t'1 -> INSERT n v (bnode p v' t1 t2) (bnode p v' t'1 t2).
 Proof.
  intros n p v v' t1 t'1 t2 H H0 H1; split.
  intros p0 v'0 H2; inversion_clear H2.
  auto with searchtrees.
  case H1; intros.    
  case (H2 _ _ H3).   
  auto.
  auto with searchtrees. 
  auto with searchtrees.
  case H1; intros.    
  eauto with searchtrees.
  intros p0 v'0 H2.
  inversion_clear H2.
  auto with searchtrees.
  case H1; intros. 
  elim (H5 p0 v'0); auto with searchtrees.
  auto with searchtrees.
  case H1; constructor 2; auto with searchtrees.
  eapply search_tree_r; eauto with searchtrees.
  split; intros.
  elim (H4 _ _ H6).
  intro.
  cut (maj p t1).
  inversion_clear 1; eauto with searchtrees.
  eauto with searchtrees.
  repeat simple destruct 1.
  assumption.
  eauto with searchtrees.
 Qed.

(* inserting in the right son *)

 Lemma insert_r :
  forall (n p : key) (v v' : data) (t1 t2 t'2 : btree),
  Key.lt p n ->
  search_tree (bnode p v' t1 t2) ->
  INSERT n v t2 t'2 -> INSERT n v (bnode p v' t1 t2) (bnode p v' t1 t'2).

 Proof.
  intros n p v v' t1 t2 t'2 H H0 H1; split.
  intros p0 v'0 H2; inversion_clear H2.
  auto with searchtrees.
  auto with searchtrees. 
  case H1; intros.    
  case (H2 _ _ H3).   
  auto.
  auto with searchtrees. 
  case H1; intros.
  auto with searchtrees.
  intros p0 v'0 H2.
  inversion_clear H2.
  auto with searchtrees.
  auto with searchtrees.
  case H1; intros. 
  elim (H5 p0 v'0 H3); auto with searchtrees.
  case H1; constructor 2; auto with searchtrees.
  eapply search_tree_l; eauto with searchtrees.
  eauto with searchtrees.
  split; intros.
  case (H4 _ _ H6).
  intro.
  cut (min p t2).
  inversion_clear 1; eauto with searchtrees.
  eauto with searchtrees.
  repeat simple destruct 1.
  assumption.
 Qed.


(* inserting at the root ;
  please notice that the most recent value is stored *)

 Lemma insert_eq :
  forall (n : key) (v v' : data) (t1 t2 : btree),
  search_tree (bnode n v t1 t2) ->
  INSERT n v' (bnode n v t1 t2) (bnode n v' t1 t2).
 Proof.
  split.
  inversion 1; eauto with searchtrees.
  eauto with searchtrees.
  inversion 1; eauto with searchtrees.
  inversion H; eauto with searchtrees.
 Qed.

 Hint Resolve insert_l insert_r insert_eq: searchtrees.




 Definition insert :
   forall (n : key) (v : data) (t : btree), insert_spec n v t.
  simple induction t. 
  exists (bnode n v leaf leaf).
  auto with searchtrees.
  unfold insert_spec at 3 in |- *; intros p b t1 H1 t2 H2 H0.
  case (M.le_lt_dec n p).
  intro H; case (M.le_lt_eq_dec n p H).
  intro H'.
  case (H1 (search_tree_l _ _ _ _ H0)). 
  intros t3; exists (bnode p b t3 t2). 
  auto with searchtrees.
  intro e; rewrite e; exists (bnode p v t1 t2); auto with searchtrees.
  case (H2 (search_tree_r _ _ _ _ H0)). 
  intros t3; exists (bnode p b t1 t3). 
  auto with searchtrees.
 Defined. 

(* realisation of the DICT  signature *)

(* dictionaries are represented as  certified binary search trees *)

 Definition dict : Set := sig search_tree. 

 Definition empty : dict.
  unfold dict in |- *; exists leaf.
  left.
 Defined.
 
 Definition find (k : key) (d : dict) : option data :=
   let (t, Ht) := d in
   match occ_dec k t Ht with
   | inleft s => let (v, _) := s in Some v
   | inright _ => None (A:=data)
   end.

 Definition add : key -> data -> dict -> dict.
  refine
   (fun (k : key) (v : data) (d : dict) =>
    let (t, Ht) := d in
    let (x, Hx) := insert k v t Ht in exist search_tree x _).
  case Hx; auto.
 Defined.           


  (* Now, we've got to prove the axioms *)

 Definition D_tree (d : dict) : btree := match d with
                                         | exist t Ht => t
                                         end.

 Lemma D_search : forall d : dict, search_tree (D_tree d).
 Proof.
   simple destruct d; simpl in |- *; auto.
 Qed.


 Lemma find_occ_dec :
  forall (k : key) (v : data) (d : dict),
  occ v k (D_tree d) -> find k d = Some v.

 Proof.
  unfold find in |- *; simple destruct d; simpl in |- *; intros.
  case (occ_dec k x s); simpl in |- *. 
  simple destruct s0; simpl in |- *.
  intros x0 H0; case (occ_unicity x s _ _ _ H H0).
  auto.
  intros.
  case (n v H). 
 Qed.

 Lemma not_find_occ_dec :
  forall (k : key) (d : dict),
  (forall v : data, ~ occ v k (D_tree d)) -> find k d = None.
 Proof.
  unfold find in |- *; simple destruct d; simpl in |- *; intros.
  case (occ_dec k x s); simpl in |- *. 
  simple destruct s0; simpl in |- *.
  intros.  
  case (H _ o). 
  auto.
 Qed.

 Theorem empty_def : forall k : key, find k empty = None.
 Proof.
  unfold find, empty in |- *. 
  intro k; case (occ_dec k leaf leaf_search_tree); simpl in |- *.
  simple destruct s.
  inversion 1.
  auto.
 Qed.

 Remark success2 :
  forall (d : dict) (k : key) (v : data), occ v k (D_tree (add k v d)).
 Proof.
  simple destruct d.
  simpl in |- *.
  intros x s k v; case (insert k v x s); simpl in |- *.
  simple destruct 1.
  eauto with searchtrees.
 Qed. 

 Theorem success :
  forall (d : dict) (k : key) (v : data), find k (add k v d) = Some v.
 Proof.
  intros; apply find_occ_dec.
  apply success2.
 Qed.

 Remark diff_key1 :
  forall (d : dict) (k k' : key) (v v' : data),
  k <> k' -> occ v k (D_tree (add k' v' d)) -> occ v k (D_tree d).
 Proof.
  simple destruct d.
  simpl in |- *.
  intros x s k k' v v'; case (insert k' v' x s); simpl in |- *.
  simple destruct 1; intros.   
  case (H1 _ _ H4). 
  auto.
  simple destruct 1; absurd (k' = k); auto.
  case H5; auto.
 Qed.

 Remark diff_key2 :
  forall (d : dict) (k k' : key) (v v' : data),
  k <> k' -> occ v k (D_tree d) -> occ v k (D_tree (add k' v' d)).
 Proof.
  simple destruct d; simpl in |- *.
  intros x s k k' v v'; case (insert k' v' x s); simpl in |- *.
  simple destruct 1; intros.   
  case (H _ _ H4).
  intro H5; case (H3 H5).
  auto.
 Qed.

 
 Theorem diff_key :
  forall (d : dict) (k k' : key) (v : data),
  k <> k' -> find k (add k' v d) = find k d.
 Proof.
  intros.
  case (occ_dec k (D_tree d)).
  apply D_search.
  simple destruct 1.
  intros x Hx.
  transitivity (Some x).
  apply find_occ_dec.
  apply diff_key2; auto.
  symmetry  in |- *; apply find_occ_dec; auto.
  intro; transitivity (None (A:=data)).
  apply not_find_occ_dec.
  intros v0 H0.
  apply (n v0).
  eapply diff_key1; eauto.
  symmetry  in |- *; apply not_find_occ_dec.
  auto.
 Qed.
 
End TDict.

(* Examples *)




Module BoolNat := Lexico Bool_Order Nat_Order.

Module MoreBoolNat := More_Dec_Orders BoolNat.

Module Nats <: DATA.
 Definition data := list nat.
End Nats.

Module NaiveDict := TrivialDict LZKey Nats.

Module MyDict : DICT := TDict BoolNat Nats.

Module Dict2 := Dict_Plus MyDict.



Module Dict1 := Dict_Plus NaiveDict.

(*
To get Ocaml code :

unix: coqc dict.

unix : coqtop

Coq < Require dict.
Coq < Recursive Extraction Library dict.

*)
