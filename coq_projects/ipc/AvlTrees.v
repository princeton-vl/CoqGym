(* File: AvlTrees.v  (last edited on 25/10/2000) (c) Klaus Weich  *)

Require Import ML_Int.
Require Import My_Arith.
Require Import List.

Global Set Asymmetric Patterns.

Section avl_trees.

Variable B : Set.


(*********************************************************)
(*		Definition bal and avl_tree	  	 *)

Inductive bal : Set :=
  | Left_Balanced : bal
  | Balanced : bal
  | Right_Balanced : bal.

Inductive avl_tree : Set :=
  | Avl_Nil : avl_tree
  | Avl_Node : Int -> B -> avl_tree -> avl_tree -> bal -> avl_tree.



(*********************************************************)
(*		Definition is_below		  	 *)


Inductive is_below : avl_tree -> Int -> Prop :=
  | Below_Nil : forall k0 : Int, is_below Avl_Nil k0
  | Below_Node :
      forall (k : Int) (d : B) (l r : avl_tree) (b : bal) (k0 : Int),
      Less k k0 ->
      is_below l k0 -> is_below r k0 -> is_below (Avl_Node k d l r b) k0.

Lemma inv_below_key :
 forall (k : Int) (d : B) (l r : avl_tree) (b : bal) (k0 : Int),
 is_below (Avl_Node k d l r b) k0 -> Less k k0.
intros.
inversion H; assumption.
Qed.

Lemma inv_below_left :
 forall (k : Int) (d : B) (l r : avl_tree) (b : bal) (k0 : Int),
 is_below (Avl_Node k d l r b) k0 -> is_below l k0.
intros.
inversion H; assumption.
Qed.

Lemma inv_below_right :
 forall (k : Int) (d : B) (l r : avl_tree) (b : bal) (k0 : Int),
 is_below (Avl_Node k d l r b) k0 -> is_below r k0.
intros.
inversion H; assumption.
Qed.


Lemma below_trans :
 forall (t : avl_tree) (k0 k1 : Int),
 is_below t k0 -> Less k0 k1 -> is_below t k1.
intros t; elim t; clear t.
intros.
apply Below_Nil.
intros k d l ih_l r ih_r b k0 k1 H0 H1.
apply Below_Node.
apply (less_trans k k0 k1).
apply (inv_below_key k d l r b k0 H0).
assumption.
apply (ih_l k0 k1 (inv_below_left k d l r b k0 H0) H1).
apply (ih_r k0 k1 (inv_below_right k d l r b k0 H0) H1).
Qed.



(*********************************************************)
(*		Definition is_above		  	 *)

Inductive is_above : avl_tree -> Int -> Prop :=
  | Above_Nil : forall k0 : Int, is_above Avl_Nil k0
  | Above_Node :
      forall (k : Int) (d : B) (l r : avl_tree) (b : bal) (k0 : Int),
      Less k0 k ->
      is_above l k0 -> is_above r k0 -> is_above (Avl_Node k d l r b) k0.

Lemma inv_above_key :
 forall (k : Int) (d : B) (l r : avl_tree) (b : bal) (k0 : Int),
 is_above (Avl_Node k d l r b) k0 -> Less k0 k.
intros.
inversion H; assumption.
Qed.

Lemma inv_above_left :
 forall (k : Int) (d : B) (l r : avl_tree) (b : bal) (k0 : Int),
 is_above (Avl_Node k d l r b) k0 -> is_above l k0.
intros.
inversion H; assumption.
Qed.

Lemma inv_above_right :
 forall (k : Int) (d : B) (l r : avl_tree) (b : bal) (k0 : Int),
 is_above (Avl_Node k d l r b) k0 -> is_above r k0.
intros.
inversion H; assumption.
Qed.


Lemma above_trans :
 forall (t : avl_tree) (k0 k1 : Int),
 is_above t k0 -> Less k1 k0 -> is_above t k1.
intros t; elim t; clear t.
intros.
apply Above_Nil.
intros k d l ih_l r ih_r b k0 k1 H0 H1.
apply Above_Node.
apply (less_trans k1 k0 k H1).
apply (inv_above_key k d l r b k0 H0).
apply (ih_l k0 k1 (inv_above_left k d l r b k0 H0) H1).
apply (ih_r k0 k1 (inv_above_right k d l r b k0 H0) H1).
Qed.



(*********************************************************)
(*		Definition height         	  	 *)

Fixpoint height (t : avl_tree) : nat :=
  match t with
  | Avl_Nil => 0
  | Avl_Node _ _ l r _ => S (max (height l) (height r))
  end.


Lemma height_O_nil : forall t : avl_tree, height t = 0 -> t = Avl_Nil.
intros t; elim t; clear t.
intros; trivial.
intros k d l ih_l r ih_r b.
simpl in |- *; intro u0;  discriminate u0.
Qed.


(*********************************************************)
(*		Definition is_balanced		  	 *)


Inductive is_balanced (l r : avl_tree) : bal -> Prop :=
  | Is_Left_Balanced :
      height l = S (height r) -> is_balanced l r Left_Balanced
  | Is_Fully_Balanced : height l = height r -> is_balanced l r Balanced
  | Is_Right_Balanced :
      S (height l) = height r -> is_balanced l r Right_Balanced.


Lemma inv_left_balanced :
 forall l r : avl_tree,
 is_balanced l r Left_Balanced -> height l = S (height r).
intros.
inversion H; assumption.
Qed.

Lemma inv_fully_balanced :
 forall l r : avl_tree, is_balanced l r Balanced -> height l = height r.
intros.
inversion H; assumption.
Qed.

Lemma inv_right_balanced :
 forall l r : avl_tree,
 is_balanced l r Right_Balanced -> S (height l) = height r.
intros.
inversion H; assumption.
Qed.


(************************************************************************)
(* lookup                                                               *)


Inductive lookup (key : Int) : avl_tree -> B -> Prop :=
  | Lookup_Equal :
      forall (d : B) (l r : avl_tree) (b : bal),
      lookup key (Avl_Node key d l r b) d
  | Lookup_Left :
      forall (k : Int) (d : B) (l r : avl_tree) (b : bal) (data : B),
      lookup key l data -> lookup key (Avl_Node k d l r b) data
  | Lookup_Right :
      forall (k : Int) (d : B) (l r : avl_tree) (b : bal) (data : B),
      lookup key r data -> lookup key (Avl_Node k d l r b) data.


Lemma inv_lookup_nil :
 forall (key : Int) (data : B), lookup key Avl_Nil data -> False.
intros.
inversion H.
Qed.

Lemma inv_lookup :
 forall (key k : Int) (d : B) (l r : avl_tree) (b : bal) (data : B),
 lookup key (Avl_Node k d l r b) data ->
 k = key /\ d = data \/ lookup key l data \/ lookup key r data.
intros.
inversion_clear H.
left; split; trivial.
right; left; assumption.
right; right; assumption.
Qed.

(*******************************************************)
(* Lemmata about Lookup and below/above                *)

Lemma lookup_below_less :
 forall (key : Int) (t : avl_tree) (data : B) (k0 : Int),
 lookup key t data -> is_below t k0 -> Less key k0.
intros key t; elim t; clear t.
intros data k0 lookup_t below_t.
elimtype False.
apply (inv_lookup_nil key data lookup_t).
intros k d l ih_l r ih_r b data k0 lookup_t below_t.
elim (inv_lookup key k d l r b data lookup_t); clear lookup_t; intro u0.
elim u0; clear u0; intros u0 u1.
 rewrite <- u0.
apply (inv_below_key k d l r b k0 below_t).

elim u0; clear u0; intro u0.
apply (ih_l data).
assumption.
apply (inv_below_left k d l r b k0 below_t).

apply (ih_r data).
assumption.
apply (inv_below_right k d l r b k0 below_t).
Qed.


Lemma lookup_above_greater :
 forall (key : Int) (t : avl_tree) (data : B) (k0 : Int),
 lookup key t data -> is_above t k0 -> Less k0 key.
intros key t; elim t; clear t.
intros data k0 lookup_t above_t.
elimtype False.
apply (inv_lookup_nil key data lookup_t).
intros k d l ih_l r ih_r b data k0 lookup_t above_t.
elim (inv_lookup key k d l r b data lookup_t); clear lookup_t; intro u0.
elim u0; clear u0; intros u0 u1.
 rewrite <- u0.
apply (inv_above_key k d l r b k0 above_t).

elim u0; clear u0; intro u0.
apply (ih_l data).
assumption.
apply (inv_above_left k d l r b k0 above_t).

apply (ih_r data).
assumption.
apply (inv_above_right k d l r b k0 above_t).
Qed.


Lemma lookup_less_below :
 forall (t : avl_tree) (k0 : Int),
 (forall (k : Int) (d : B), lookup k t d -> Less k k0) -> is_below t k0.
intros t; elim t; clear t.
intros.
apply Below_Nil.
intros k d l ih_l r ih_r b k0 H.
apply Below_Node.
apply (H k d).
apply Lookup_Equal.
apply ih_l.
intros k1 d0 lookup_l.
apply (H k1 d0).
apply Lookup_Left; assumption.
apply ih_r.
intros k1 d0 lookup_r.
apply (H k1 d0).
apply Lookup_Right; assumption.
Qed.


Lemma lookup_greater_above :
 forall (t : avl_tree) (k0 : Int),
 (forall (k : Int) (d : B), lookup k t d -> Less k0 k) -> is_above t k0.
intros t; elim t; clear t.
intros.
apply Above_Nil.
intros k d l ih_l r ih_r b k0 H.
apply Above_Node.
apply (H k d).
apply Lookup_Equal.
apply ih_l.
intros k1 d0 lookup_l.
apply (H k1 d0).
apply Lookup_Left; assumption.
apply ih_r.
intros k1 d0 lookup_r.
apply (H k1 d0).
apply Lookup_Right; assumption.
Qed.



Lemma lookup_above_lookup :
 forall (key k : Int) (d : B) (l r : avl_tree) (b : bal) (data : B),
 lookup key (Avl_Node k d l r b) data ->
 Less key k -> is_above r key -> lookup key l data.
intros key k d l r b data lookup_t less above_r.
elim (inv_lookup key k d l r b data lookup_t); clear lookup_t; intro u0.

elimtype False.
elim u0; clear u0; intros u0 u1.
apply less_irrefl with key.
 rewrite u0 in less.
assumption.

elim u0; clear u0; intro u0.

assumption.

elimtype False.
apply less_irrefl with key.
apply lookup_above_greater with r data; assumption.
Qed.




Lemma lookup_below_lookup :
 forall (key k : Int) (d : B) (l r : avl_tree) (b : bal) (data : B),
 lookup key (Avl_Node k d l r b) data ->
 Less k key -> is_below l key -> lookup key r data.
intros key k d l r b data lookup_t less below_l.
elim (inv_lookup key k d l r b data lookup_t); clear lookup_t; intro u0.

elimtype False.
elim u0; clear u0; intros u0 u1.
apply less_irrefl with key.
 rewrite u0 in less.
assumption.

elim u0; clear u0; intro u0.

elimtype False.
apply less_irrefl with key.
apply lookup_below_less with l data; assumption.

assumption.
Qed.

Lemma lookup_below_false :
 forall (key : Int) (t : avl_tree) (data : B),
 lookup key t data -> is_below t key -> False.
intros key t data lookup_t below_t.
apply less_irrefl with key.
apply lookup_below_less with t data; assumption.
Qed.



Lemma lookup_above_false :
 forall (key : Int) (t : avl_tree) (data : B),
 lookup key t data -> is_above t key -> False.
intros key t data lookup_t above_t.
apply less_irrefl with key.
apply lookup_above_greater with t data; assumption.
Qed.




(*********************************************************)
(*		Definition is_below_avl		  	 *)


Inductive is_below_avl : avl_tree -> Int -> Prop :=
  | Below_Avl_Nil : forall k0 : Int, is_below_avl Avl_Nil k0
  | Below_Avl_Node :
      forall (k : Int) (d : B) (l r : avl_tree) (b : bal) (k0 : Int),
      Less k k0 -> is_below_avl r k0 -> is_below_avl (Avl_Node k d l r b) k0.

Lemma inv_below_avl_key :
 forall (k : Int) (d : B) (l r : avl_tree) (b : bal) (k0 : Int),
 is_below_avl (Avl_Node k d l r b) k0 -> Less k k0.
intros.
inversion H; assumption.
Qed.

Lemma inv_below_avl_right :
 forall (k : Int) (d : B) (l r : avl_tree) (b : bal) (k0 : Int),
 is_below_avl (Avl_Node k d l r b) k0 -> is_below_avl r k0.
intros.
inversion H; assumption.
Qed.


Lemma below_avl_trans :
 forall (t : avl_tree) (k0 k1 : Int),
 is_below_avl t k0 -> Less k0 k1 -> is_below_avl t k1.
intros t; elim t; clear t.
intros.
apply Below_Avl_Nil.
intros k d l ih_l r ih_r b k0 k1 H0 H1.
apply Below_Avl_Node.
apply (less_trans k k0 k1).
apply (inv_below_avl_key k d l r b k0 H0).
assumption.
apply (ih_r k0 k1 (inv_below_avl_right k d l r b k0 H0) H1).
Qed.


Lemma below_below_avl :
 forall (t : avl_tree) (key : Int), is_below t key -> is_below_avl t key.
intros t key; elim t; clear t.

intros.
apply Below_Avl_Nil.

intros k d l ih_l r ih_r b below_t.
apply Below_Avl_Node.
apply (inv_below_key k d l r b key below_t).
apply ih_r.
apply (inv_below_right k d l r b key below_t).
Qed.



(*********************************************************)
(*		Definition is_above_avl		  	 *)

Inductive is_above_avl : avl_tree -> Int -> Prop :=
  | Above_Avl_Nil : forall k0 : Int, is_above_avl Avl_Nil k0
  | Above_Avl_Node :
      forall (k : Int) (d : B) (l r : avl_tree) (b : bal) (k0 : Int),
      Less k0 k -> is_above_avl l k0 -> is_above_avl (Avl_Node k d l r b) k0.

Lemma inv_above_avl_key :
 forall (k : Int) (d : B) (l r : avl_tree) (b : bal) (k0 : Int),
 is_above_avl (Avl_Node k d l r b) k0 -> Less k0 k.
intros.
inversion H; assumption.
Qed.

Lemma inv_above_avl_left :
 forall (k : Int) (d : B) (l r : avl_tree) (b : bal) (k0 : Int),
 is_above_avl (Avl_Node k d l r b) k0 -> is_above_avl l k0.
intros.
inversion H; assumption.
Qed.


Lemma above_avl_trans :
 forall (t : avl_tree) (k0 k1 : Int),
 is_above_avl t k0 -> Less k1 k0 -> is_above_avl t k1.
intros t; elim t; clear t.
intros.
apply Above_Avl_Nil.
intros k d l ih_l r ih_r b k0 k1 H0 H1.
apply Above_Avl_Node.
apply (less_trans k1 k0 k H1).
apply (inv_above_avl_key k d l r b k0 H0).
apply (ih_l k0 k1 (inv_above_avl_left k d l r b k0 H0) H1).
Qed.

Lemma above_above_avl :
 forall (t : avl_tree) (key : Int), is_above t key -> is_above_avl t key.
intros t key; elim t; clear t.

intros.
apply Above_Avl_Nil.

intros k d l ih_l r ih_r b above_t.
apply Above_Avl_Node.
apply (inv_above_key k d l r b key above_t).
apply ih_l.
apply (inv_above_left k d l r b key above_t).
Qed.


(*****************************************************************)
(*           height_avl                                          *)

Fixpoint height_avl (t : avl_tree) : nat :=
  match t with
  | Avl_Nil => 0
  | Avl_Node _ _ l _ Left_Balanced => S (height_avl l)
  | Avl_Node _ _ l _ Balanced => S (height_avl l)
  | Avl_Node _ _ _ r Right_Balanced => S (height_avl r)
  end.


Lemma height_avl_O_nil : forall t : avl_tree, height_avl t = 0 -> t = Avl_Nil.
intros t; elim t; clear t.
intros; trivial.
intros k d l ih_l r ih_r b.
elim b; simpl in |- *; intro u0;  discriminate u0.
Qed.


(*********************************************************)
(*		Definition is_balanced		  	 *)


Inductive is_balanced_avl (l r : avl_tree) : bal -> Prop :=
  | Is_Left_Balanced_Avl :
      height_avl l = S (height_avl r) -> is_balanced_avl l r Left_Balanced
  | Is_Fully_Balanced_Avl :
      height_avl l = height_avl r -> is_balanced_avl l r Balanced
  | Is_Right_Balanced_Avl :
      S (height_avl l) = height_avl r -> is_balanced_avl l r Right_Balanced.


Lemma inv_left_balanced_avl :
 forall l r : avl_tree,
 is_balanced_avl l r Left_Balanced -> height_avl l = S (height_avl r).
intros.
inversion H; assumption.
Qed.

Lemma inv_fully_balanced_avl :
 forall l r : avl_tree,
 is_balanced_avl l r Balanced -> height_avl l = height_avl r.
intros.
inversion H; assumption.
Qed.


Lemma inv_right_balanced_avl :
 forall l r : avl_tree,
 is_balanced_avl l r Right_Balanced -> S (height_avl l) = height_avl r.
intros.
inversion H; assumption.
Qed.


Lemma hasnot_grown_left__preserves_is_balanced_avl :
 forall (l l0 r0 : avl_tree) (b0 : bal),
 is_balanced_avl l0 r0 b0 ->
 height_avl l = height_avl l0 -> is_balanced_avl l r0 b0.
intros l l0 r0 b0 Balanced_l0 height_l.
inversion_clear Balanced_l0.
apply Is_Left_Balanced_Avl.
 rewrite height_l; assumption.
apply Is_Fully_Balanced_Avl.
 rewrite height_l; assumption.
apply Is_Right_Balanced_Avl.
 rewrite height_l; assumption.
Qed.


Lemma hasnot_grown_right__preserves_is_balanced_avl :
 forall (l0 r r0 : avl_tree) (b0 : bal),
 is_balanced_avl l0 r0 b0 ->
 height_avl r = height_avl r0 -> is_balanced_avl l0 r b0.
intros l0 r r0 b0 Balanced_l0 height_r.
inversion_clear Balanced_l0.
apply Is_Left_Balanced_Avl.
 rewrite height_r; assumption.
apply Is_Fully_Balanced_Avl.
 rewrite height_r; assumption.
apply Is_Right_Balanced_Avl.
 rewrite height_r; assumption.
Qed.


(*************************************************)
(*		Definition Avl		  	 *)
(*************************************************)

Inductive is_avl : avl_tree -> Prop :=
  | Nil_Is_Avl : is_avl Avl_Nil
  | Node_Is_Avl :
      forall (k : Int) (d : B) (l r : avl_tree) (b : bal),
      is_avl l ->
      is_avl r ->
      is_balanced_avl l r b ->
      is_below_avl l k -> is_above_avl r k -> is_avl (Avl_Node k d l r b).


Lemma is_avl_rec :
 forall P : avl_tree -> Set,
 P Avl_Nil ->
 (forall (k : Int) (d : B) (l r : avl_tree) (b : bal),
  is_avl l ->
  P l ->
  is_avl r ->
  P r ->
  is_balanced_avl l r b ->
  is_below_avl l k -> is_above_avl r k -> P (Avl_Node k d l r b)) ->
 forall t : avl_tree, is_avl t -> P t.
intros P base step t.
elim t; clear t.
intros; apply base.
intros k d l ih_l r ih_r b avl_t.
apply step.
inversion_clear avl_t; assumption.
apply ih_l.
inversion_clear avl_t; assumption.
inversion_clear avl_t; assumption.
apply ih_r.
inversion_clear avl_t; assumption.
inversion_clear avl_t; assumption.
inversion_clear avl_t; assumption.
inversion_clear avl_t; assumption.
Qed.



Lemma inv_is_avl_left :
 forall (k : Int) (d : B) (l r : avl_tree) (b : bal),
 is_avl (Avl_Node k d l r b) -> is_avl l.
intros.
inversion H; assumption.
Qed.


Lemma inv_is_avl_right :
 forall (k : Int) (d : B) (l r : avl_tree) (b : bal),
 is_avl (Avl_Node k d l r b) -> is_avl r.
intros.
inversion H; assumption.
Qed.

Lemma inv_is_avl_is_balanced_avl :
 forall (k : Int) (d : B) (l r : avl_tree) (b : bal),
 is_avl (Avl_Node k d l r b) -> is_balanced_avl l r b.
intros.
inversion H; assumption.
Qed.

Lemma inv_is_avl_is_is_below_avl :
 forall (k : Int) (d : B) (l r : avl_tree) (b : bal),
 is_avl (Avl_Node k d l r b) -> is_below_avl l k.
intros.
inversion H; assumption.
Qed.

Lemma inv_is_avl_is_is_above_avl :
 forall (k : Int) (d : B) (l r : avl_tree) (b : bal),
 is_avl (Avl_Node k d l r b) -> is_above_avl r k.
intros.
inversion H; assumption.
Qed.


Lemma avl_height_avl_height :
 forall t : avl_tree, is_avl t -> height_avl t = height t.
intros t avl_t.
elim avl_t.
simpl in |- *; trivial.
intros k d l r b avl_l ih_l avl_r ih_r Balanced_t below_l above_r.
clear avl_l avl_r below_l above_r. 
simpl in |- *.
 rewrite <- ih_l.
 rewrite <- ih_r.
clear ih_l ih_r.
inversion_clear Balanced_t.
 rewrite H.
 rewrite (max_Sn_n (height_avl r)).
trivial.
 rewrite H.
 rewrite (max_n_n (height_avl r)).
trivial.
 rewrite <- H.
 rewrite (max_n_Sn (height_avl l)).
trivial.
Qed.


Lemma is_balanced_avl_is_balanced :
 forall l r : avl_tree,
 is_avl l ->
 is_avl r -> forall b : bal, is_balanced_avl l r b -> is_balanced l r b.
intros l r avl_l avl_r.
intro b; elim b; clear b; intro bal0.
apply Is_Left_Balanced.
 rewrite <- (avl_height_avl_height r avl_r).
 rewrite <- (avl_height_avl_height l avl_l).
apply inv_left_balanced_avl; assumption.
apply Is_Fully_Balanced.
 rewrite <- (avl_height_avl_height r avl_r).
 rewrite <- (avl_height_avl_height l avl_l).
apply inv_fully_balanced_avl; assumption.

apply Is_Right_Balanced.
 rewrite <- (avl_height_avl_height r avl_r).
 rewrite <- (avl_height_avl_height l avl_l).
apply inv_right_balanced_avl; assumption.
Qed.



Lemma is_avl_is_balanced :
 forall (l r : avl_tree) (k : Int) (d : B) (b : bal),
 is_avl (Avl_Node k d l r b) -> is_balanced l r b.
intros l r k d b avl_t.
apply is_balanced_avl_is_balanced.
apply (inv_is_avl_left k d l r b avl_t).
apply (inv_is_avl_right k d l r b avl_t).
apply (inv_is_avl_is_balanced_avl k d l r b avl_t).
Qed.


Lemma is_below_avl_is_below :
 forall t : avl_tree,
 is_avl t -> forall k0 : Int, is_below_avl t k0 -> is_below t k0.
intros t avl_t.
elim avl_t; clear avl_t t.
intros; apply Below_Nil.
intros k d l r b avl_l ih_l avl_r ih_r Balanced_t below_l above_r k0
 below_avl.
inversion_clear below_avl.
apply Below_Node.
assumption.
apply ih_l. 
apply below_avl_trans with k.
assumption.
assumption.
apply ih_r; assumption.
Qed.


Lemma is_above_avl_is_above :
 forall t : avl_tree,
 is_avl t -> forall k0 : Int, is_above_avl t k0 -> is_above t k0.
intros t avl_t; elim avl_t; clear avl_t t.
intros; apply Above_Nil.
intros k d l r b avl_l ih_l avl_r ih_r Balanced_t below_l above_r k0
 above_avl.
clear avl_l avl_r Balanced_t.
inversion_clear above_avl.
apply Above_Node.
assumption.
apply ih_l; assumption.
apply ih_r.
apply above_avl_trans with k.
assumption.
assumption.
Qed.






(***************************************************************)
(*  lookup_avl                                                 *)


Lemma lookup_avl_inv_equal :
 forall (key k : Int) (d : B) (l r : avl_tree) (b : bal) (data : B),
 is_avl (Avl_Node k d l r b) ->
 Equal key k -> lookup key (Avl_Node k d l r b) data -> d = data.
intros key k d l r b data avl_t equal lookup_t.
elim (inv_lookup key k d l r b data lookup_t); intro u0.

elim u0; trivial.

elimtype False.
elim u0; clear u0; intro u0.

apply (lookup_below_false key l data u0).
apply is_below_avl_is_below.
apply (inv_is_avl_left k d l r b avl_t).
 rewrite (equal_eq key k equal).
apply (inv_is_avl_is_is_below_avl k d l r b avl_t).

apply (lookup_above_false key r data u0).
apply is_above_avl_is_above.
apply (inv_is_avl_right k d l r b avl_t).
 rewrite (equal_eq key k equal).
apply (inv_is_avl_is_is_above_avl k d l r b avl_t).
Qed.


Lemma lookup_avl_inv_less :
 forall (key k : Int) (d : B) (l r : avl_tree) (b : bal) (data : B),
 is_avl (Avl_Node k d l r b) ->
 Less key k -> lookup key (Avl_Node k d l r b) data -> lookup key l data.
intros key k d l r b data avl_t less lookup_t.
elim (inv_lookup key k d l r b data lookup_t); intro u0.
elimtype False.
apply (less_irrefl key).
elim u0; clear u0; intros u0 u1.
 rewrite u0 in less.
assumption.

elim u0; clear u0; intro u0.
assumption.

elimtype False.
apply (lookup_above_false key r data u0).
apply is_above_avl_is_above.
apply (inv_is_avl_right k d l r b avl_t).
apply (above_avl_trans r k key).
apply (inv_is_avl_is_is_above_avl k d l r b avl_t).
assumption.
Qed.


Lemma lookup_avl_inv_greater :
 forall (key k : Int) (d : B) (l r : avl_tree) (b : bal) (data : B),
 is_avl (Avl_Node k d l r b) ->
 Less k key -> lookup key (Avl_Node k d l r b) data -> lookup key r data.
intros key k d l r b data avl_t less lookup_t.
elim (inv_lookup key k d l r b data lookup_t); intro u0.
elimtype False.
apply (less_irrefl key).
elim u0; clear u0; intros u0 u1.
 rewrite u0 in less.
assumption.

elim u0; clear u0; intro u0.

elimtype False.
apply (lookup_below_false key l data u0).
apply (below_trans l k key).
apply is_below_avl_is_below.
apply (inv_is_avl_left k d l r b avl_t).
apply (inv_is_avl_is_is_below_avl k d l r b avl_t).
assumption.

assumption.
Qed.



Lemma lookup_avl_equal :
 forall (k1 k : Int) (t : avl_tree) (d1 d : B),
 is_avl t -> lookup k1 t d1 -> lookup k t d -> Equal k1 k -> d1 = d.
intros k1 k t d1 d avl_t.
generalize d; clear d.
generalize d1; clear d1.
generalize k; clear k.
generalize k1; clear k1.
elim avl_t; clear avl_t.

intros.
inversion_clear H.

intros k0 d0 l r b avl_l ih_l avl_r ih_r Balanced_l below_avl_r above_avl_r
 k1 k2 d1 d2 lookup_k1.
inversion_clear lookup_k1.
intros lookup_k0 equal_k1.
apply lookup_avl_inv_equal with k2 k0 l r b.
apply Node_Is_Avl; assumption.
apply equal_sym; assumption.
assumption.

intros lookup_k2 equal_k1.
apply ih_l with k1 k2; try assumption.
apply lookup_avl_inv_less with k0 d0 r b.
apply Node_Is_Avl; assumption.
 rewrite <- (equal_eq k1 k2 equal_k1).
apply lookup_below_less with l d1.
assumption.
apply is_below_avl_is_below; assumption.
assumption.
intros lookup_k2 equal_k1.
apply ih_r with k1 k2; try assumption.
apply lookup_avl_inv_greater with k0 d0 l b.
apply Node_Is_Avl; assumption.
 rewrite <- (equal_eq k1 k2 equal_k1).
apply lookup_above_greater with r d1.
assumption.
apply is_above_avl_is_above; assumption.
assumption.
Qed.


(****************************************************************************)

Inductive lookup_dec_spec (key : Int) (t : avl_tree) : Set :=
  | Lookup : forall d : B, lookup key t d -> lookup_dec_spec key t
  | Not_Lookup : (forall d : B, ~ lookup key t d) -> lookup_dec_spec key t.



Lemma lookup_dec :
 forall (key : Int) (t : avl_tree), is_avl t -> lookup_dec_spec key t.
intros key t avl_t; elim avl_t; clear avl_t t.
apply Not_Lookup.
unfold not in |- *; intros d lookup_nil.
apply (inv_lookup_nil key d); assumption.

intros k d l r b avl_l ih_l avl_r ih_r Balanced_t below_l above_r.
elim (equal_dec key k).

intro equal_key_k.
apply Lookup with d.
 rewrite (equal_eq key k equal_key_k).
apply Lookup_Equal.

intros not_equal_key_k.
elim (less_dec key k).

intro less_key_k.
elim ih_l; clear ih_r ih_l.
intros d0 lookup_d0.
apply Lookup with d0.
apply Lookup_Left; assumption.
intros not_lookup_d0.
apply Not_Lookup.
unfold not in |- *; intros d0 lookup_d0.
apply (not_lookup_d0 d0).
apply (lookup_avl_inv_less key k d l r b). 
apply Node_Is_Avl; assumption.
assumption.
assumption.

intros not_less.
generalize (notequal_notless_greater key k not_equal_key_k not_less).
clear not_equal_key_k not_less.
intros less_k_key.
elim ih_r; clear ih_r ih_l.
intros d0 lookup_d0.
apply Lookup with d0.
apply Lookup_Right; assumption.
intros not_lookup_d0.
apply Not_Lookup.
unfold not in |- *; intros d0 lookup_d0.
apply (not_lookup_d0 d0).
apply (lookup_avl_inv_greater key k d l r b); try assumption.
apply Node_Is_Avl; assumption.
Qed.


(***************************************************************************)
(*  equiv                                                                  *)


Fixpoint lin_avl (t : avl_tree) : list (Int * B) :=
  match t with
  | Avl_Nil => nil (A:=Int * B)
  | Avl_Node k d l r _ => lin_avl l ++ (k, d) :: lin_avl r
  end.

Inductive equiv : avl_tree -> avl_tree -> Prop :=
    equiv_intro :
      forall t0 t1 : avl_tree,
      (forall (key : Int) (data : B),
       lookup key t0 data -> lookup key t1 data) ->
      (forall (key : Int) (data : B),
       lookup key t1 data -> lookup key t0 data) -> 
      equiv t0 t1.

Lemma inv_equiv_t0_t1 :
 forall (t0 t1 : avl_tree) (key : Int) (data : B),
 equiv t0 t1 -> lookup key t0 data -> lookup key t1 data.
intros.
inversion_clear H.
apply H1.
assumption.
Qed.

Lemma inv_equiv_t1_t0 :
 forall (t0 t1 : avl_tree) (key : Int) (data : B),
 equiv t0 t1 -> lookup key t1 data -> lookup key t0 data.
intros.
inversion_clear H.
apply H2.
assumption.
Qed.


Lemma equiv_sym : forall t t0 : avl_tree, equiv t t0 -> equiv t0 t.
intros t t0 equiv_t_t0.
inversion_clear equiv_t_t0.
apply equiv_intro.
assumption.
assumption.
Qed.

Lemma equiv_refl :
 forall (k : Int) (d : B) (l r : avl_tree) (b b' : bal),
 equiv (Avl_Node k d l r b) (Avl_Node k d l r b').
intros k d l r b b'.
apply equiv_intro.
intros key data lookup_t.
inversion_clear lookup_t.
apply Lookup_Equal.
apply Lookup_Left; assumption.
apply Lookup_Right; assumption.

intros key data lookup_t.
inversion_clear lookup_t.
apply Lookup_Equal.
apply Lookup_Left; assumption.
apply Lookup_Right; assumption.
Qed.


(******************************************************************)

Definition rebalance_left_spec (k : Int) (d : B) (l r : avl_tree) 
(b : bal) : Set :=
  { t : avl_tree | 
      is_avl t /\
      lin_avl t = lin_avl (Avl_Node k d l r b) /\
      equiv t (Avl_Node k d l r b) /\
      match l with
      | Avl_Nil => True
      | Avl_Node _ _ _ _ Left_Balanced => height_avl t = height_avl l
      | Avl_Node _ _ _ _ Balanced => height_avl t = S (height_avl l)
      | Avl_Node _ _ _ _ Right_Balanced => height_avl t = height_avl l
      end }.



Lemma rebalance_left :
 forall (k : Int) (d : B) (l r : avl_tree) (b : bal),
 is_avl l ->
 is_below_avl l k ->
 is_avl r ->
 is_above_avl r k ->
 height_avl l = S (S (height_avl r)) -> rebalance_left_spec k d l r b.
intros k d l r b avl_l below_avl_l avl_r above_avl_r.
generalize below_avl_l; clear below_avl_l.
elim avl_l; clear avl_l l.

(* l=Avl_Nil *)
intros below_avl_l height_l.
 discriminate height_l.

(* l=(Avl_Node kl dl ll rl bl) *)
intros kl dl ll rl bl.
case bl; clear bl; simpl in |- *.



(* bl=Left_Balanced => single LL-rotation *)
intros avl_ll ih_ll avl_rl ih_rl Balanced_l below_ll above_rl below_avl_l
 height_l;  injection height_l; clear height_l ih_ll ih_rl; 
 intros height_l.
exists (Avl_Node kl dl ll (Avl_Node k d rl r Balanced) Balanced).
repeat apply conj.
inversion_clear below_avl_l.
inversion_clear Balanced_l.
apply Node_Is_Avl; try assumption.
apply Node_Is_Avl; try assumption.
apply Is_Fully_Balanced_Avl.
 rewrite height_l in H1.
symmetry  in |- *.
 injection H1; trivial.
apply Is_Fully_Balanced_Avl.
simpl in |- *.
assumption.
apply Above_Avl_Node; assumption.

simpl in |- *.
 rewrite
 (app_ass (lin_avl ll) ((kl, dl) :: lin_avl rl) ((k, d) :: lin_avl r))
 .
trivial.

apply equiv_intro; clear avl_ll avl_rl height_l Balanced_l.
intros key data lookup_t.
inversion_clear lookup_t.
apply Lookup_Left; apply Lookup_Equal.
apply Lookup_Left; apply Lookup_Left; assumption.
inversion_clear H.
apply Lookup_Equal.
apply Lookup_Left; apply Lookup_Right; assumption.
apply Lookup_Right; assumption.

intros key data lookup_t0.
inversion_clear lookup_t0.
apply Lookup_Right; apply Lookup_Equal.
inversion_clear H.
apply Lookup_Equal.
apply Lookup_Left; assumption.
apply Lookup_Right; apply Lookup_Left; assumption.
apply Lookup_Right; apply Lookup_Right; assumption.

simpl in |- *; trivial. 


(* bl=Balanced => single LL-rotation  *)
intros avl_ll ih_ll avl_rl ih_rl Balanced_l below_ll above_rl below_avl_l
 height_l;  injection height_l; clear height_l ih_ll ih_rl; 
 intros height_l.
exists (Avl_Node kl dl ll (Avl_Node k d rl r Left_Balanced) Right_Balanced).
repeat apply conj.
inversion_clear Balanced_l.
inversion_clear below_avl_l.
apply Node_Is_Avl; try assumption.
apply Node_Is_Avl; try assumption.
apply Is_Left_Balanced_Avl.
 rewrite <- height_l.
symmetry  in |- *.
assumption.
apply Is_Right_Balanced_Avl.
simpl in |- *.
 rewrite H; trivial.
apply Above_Avl_Node; assumption.

simpl in |- *.
 rewrite
 (app_ass (lin_avl ll) ((kl, dl) :: lin_avl rl) ((k, d) :: lin_avl r))
 .
trivial.

apply equiv_intro; clear avl_ll avl_rl below_avl_l height_l.
intros key data lookup_t.
inversion_clear lookup_t.
apply Lookup_Left; apply Lookup_Equal.
apply Lookup_Left; apply Lookup_Left; assumption.
inversion_clear H.
apply Lookup_Equal.
apply Lookup_Left; apply Lookup_Right; assumption.
apply Lookup_Right; assumption.

intros key data lookup_t0.
inversion_clear lookup_t0.
apply Lookup_Right; apply Lookup_Equal.
inversion_clear H.
apply Lookup_Equal.
apply Lookup_Left; assumption.
apply Lookup_Right; apply Lookup_Left; assumption.
apply Lookup_Right; apply Lookup_Right; assumption.

simpl in |- *.
inversion_clear Balanced_l.
 rewrite H; trivial.


(* bl=Right_Balanced => double LR-rotation *)
intros avl_ll ih_ll avl_rl ih_rl; clear ih_ll ih_rl.
elim avl_rl; clear avl_rl rl; simpl in |- *.

intros Balanced_l below_ll above_l below_avl_l height_l.
 discriminate height_l.
intros klr dlr llr rlr blr avl_llr ih_llr avl_rlr ih_rlr; clear ih_llr ih_rlr.
intros Balanced_rl below_llr above_rlr Balanced_l below_ll above_lr
 below_avl_l height_l.
 injection height_l; clear height_l; intros height_l.
exists 
    (Avl_Node klr dlr
       (Avl_Node kl dl ll llr
          match blr with
          | Left_Balanced => Balanced
          | Balanced => Balanced
          | Right_Balanced => Left_Balanced
          end)
       (Avl_Node k d rlr r
          match blr with
          | Left_Balanced => Right_Balanced
          | Balanced => Balanced
          | Right_Balanced => Balanced
          end) Balanced).
repeat apply conj.
inversion_clear Balanced_l.
inversion_clear above_lr.
inversion_clear below_avl_l.
inversion_clear H3.
apply Node_Is_Avl; try assumption.
apply Node_Is_Avl; try assumption.
clear height_l.
generalize H; clear H.
inversion_clear Balanced_rl; simpl in |- *; intros.
apply Is_Fully_Balanced_Avl.
 injection H3; trivial.
apply Is_Fully_Balanced_Avl.
 injection H3; trivial.
apply Is_Left_Balanced_Avl.
 rewrite <- H in H3.
 injection H3; trivial.

apply Node_Is_Avl; try assumption.
generalize height_l; clear height_l.
generalize H; clear H.
inversion_clear Balanced_rl; simpl in |- *; intros.
apply Is_Right_Balanced_Avl.
 rewrite <- H.
 injection height_l; trivial.
apply Is_Fully_Balanced_Avl.
 rewrite <- H.
 injection height_l; trivial.
apply Is_Fully_Balanced_Avl.
 injection height_l; trivial.

apply Is_Fully_Balanced_Avl.
generalize height_l; clear height_l.
generalize H; clear H.
inversion_clear Balanced_rl; clear blr; simpl in |- *; intros.
 rewrite H3.
assumption.
 rewrite <- H.
assumption.
assumption.

apply Below_Avl_Node; try assumption.
apply Above_Avl_Node; try assumption.

clear height_l.
simpl in |- *.

 rewrite
 (app_ass (lin_avl ll) ((kl, dl) :: lin_avl llr)
    ((klr, dlr) :: lin_avl rlr ++ (k, d) :: lin_avl r))
 .
 rewrite
 (app_ass (lin_avl ll) ((kl, dl) :: lin_avl llr ++ (klr, dlr) :: lin_avl rlr)
    ((k, d) :: lin_avl r)).
simpl in |- *.
 rewrite
 (app_ass (lin_avl llr) ((klr, dlr) :: lin_avl rlr) ((k, d) :: lin_avl r))
 .
trivial.

apply equiv_intro; clear avl_ll avl_llr avl_rlr below_avl_l height_l.
intros key data lookup_t.
inversion_clear lookup_t.
apply Lookup_Left; apply Lookup_Right; apply Lookup_Equal.
apply Lookup_Left.
inversion_clear H.
apply Lookup_Equal.
apply Lookup_Left; assumption.
apply Lookup_Right; apply Lookup_Left; assumption.
inversion_clear H.
apply Lookup_Equal.
apply Lookup_Left; apply Lookup_Right; apply Lookup_Right; assumption.
apply Lookup_Right; assumption.

intros key data lookup_t0.
inversion_clear lookup_t0.
apply Lookup_Right; apply Lookup_Equal.
inversion_clear H.
apply Lookup_Left; apply Lookup_Equal.
apply Lookup_Left; apply Lookup_Left; assumption.
inversion_clear H0.
apply Lookup_Equal.
apply Lookup_Left; apply Lookup_Right; assumption.
apply Lookup_Right; apply Lookup_Left; assumption.
apply Lookup_Right; apply Lookup_Right; assumption.

clear below_avl_l above_lr below_ll above_rlr below_llr avl_rlr avl_llr.
generalize height_l; clear height_l.
inversion_clear Balanced_l.
generalize H; clear H.
inversion_clear Balanced_rl; clear blr; simpl in |- *; intros.
 rewrite H0; trivial.
 rewrite H0; trivial.
 rewrite H0; trivial.
Qed.


(******************************************************************)



Definition rebalance_right_spec (k : Int) (d : B) (l r : avl_tree) 
(b : bal) : Set :=
  { t : avl_tree | 
      is_avl t /\
      lin_avl t = lin_avl (Avl_Node k d l r b) /\
      equiv t (Avl_Node k d l r b) /\
      match r with
      | Avl_Nil => True
      | Avl_Node _ _ _ _ Left_Balanced => height_avl t = height_avl r
      | Avl_Node _ _ _ _ Balanced => height_avl t = S (height_avl r)
      | Avl_Node _ _ _ _ Right_Balanced => height_avl t = height_avl r
      end }.


Lemma rebalance_right :
 forall (k : Int) (d : B) (l r : avl_tree) (b : bal),
 is_avl l ->
 is_below_avl l k ->
 is_avl r ->
 is_above_avl r k ->
 S (S (height_avl l)) = height_avl r -> rebalance_right_spec k d l r b.
intros k d l r b avl_l below_avl_l avl_r.
elim avl_r; clear avl_r.

(* r=Avl_Nil *)
intros above_avl_r height_r.
 discriminate height_r.

(* r=(Avl_Node kr dr lr rr br) *)
intros kr dr lr rr br avl_lr ih_lr avl_rr ih_rr.
clear ih_lr ih_rr.
case br; clear br.

(* br=Left_Balanced => double RL-rotation *)
elim avl_lr; clear avl_lr lr.
simpl in |- *.
intros Balanced_r below_lr above_rr above_avl_r height_r.
 discriminate height_r.
intros krl drl lrl rrl brl avl_lrl ih_lrl avl_rrl ih_rrl; clear ih_lrl ih_rrl.
intros Balanced_lr below_lrl above_rrl Balanced_r below_lr above_rr
 above_avl_r height_r.
exists
    (Avl_Node krl drl
       (Avl_Node k d l lrl
          match brl with
          | Left_Balanced => Balanced
          | Balanced => Balanced
          | Right_Balanced => Left_Balanced
          end)
       (Avl_Node kr dr rrl rr
          match brl with
          | Left_Balanced => Right_Balanced
          | Balanced => Balanced
          | Right_Balanced => Balanced
          end) Balanced).
repeat apply conj.
inversion_clear Balanced_r.
inversion_clear below_lr.
inversion_clear above_avl_r.
inversion_clear H3.
apply Node_Is_Avl; try assumption.
apply Node_Is_Avl; try assumption.
generalize height_r;
 clear height_r H5 H4 H2 H1 H0 above_rr above_rrl below_lrl.
generalize H; clear H.
inversion_clear Balanced_lr; clear brl; simpl in |- *; intros.
(* blr=Left_Balanced *)
apply Is_Fully_Balanced_Avl.
 injection height_r; trivial.
(* blr=Balanced *)
apply Is_Fully_Balanced_Avl.
 injection height_r; trivial.
(* blr=Right_Balanced *)
apply Is_Left_Balanced_Avl.
 rewrite H.
 injection height_r; trivial.

apply Node_Is_Avl; try assumption.
clear height_r H5 H4 H2 H1 H0 above_rr above_rrl below_lrl.
generalize H; clear H.
inversion_clear Balanced_lr; clear brl; simpl in |- *; intros.
(* brl=Left_Balanced *)
apply Is_Right_Balanced_Avl.
 rewrite <- H.
 injection H0; trivial.
(* brl=Balanced *)
apply Is_Fully_Balanced_Avl.
 rewrite <- H.
 injection H0; trivial.
(* brl=Right_Balanced *)
apply Is_Fully_Balanced_Avl.
 injection H0; trivial.

apply Is_Fully_Balanced_Avl.
generalize height_r;
 clear height_r H5 H4 H2 H1 H0 above_rr above_rrl below_lrl.
generalize H; clear H.
inversion_clear Balanced_lr; clear brl; simpl in |- *; intros.
(* brl=Left_Balanced *)
 rewrite <- H0.
 injection height_r; clear height_r; intro height_r.
 rewrite height_r; trivial.
(* brl=Balanced *)
 rewrite <- H.
 injection height_r; clear height_r; intro height_r.
 rewrite height_r; trivial.
(* brl=Right_Balanced *)
 injection height_r; clear height_r; intro height_r.
 rewrite height_r; trivial.

apply Below_Avl_Node; assumption.
apply Above_Avl_Node; assumption.

clear height_r above_avl_r above_rr below_lr Balanced_r above_rrl below_lrl
 Balanced_lr.
simpl in |- *.
 rewrite
 (app_ass (lin_avl l) ((k, d) :: lin_avl lrl)
    ((krl, drl) :: lin_avl rrl ++ (kr, dr) :: lin_avl rr))
 .
simpl in |- *.
 rewrite
 (app_ass (lin_avl lrl) ((krl, drl) :: lin_avl rrl) ((kr, dr) :: lin_avl rr))
 .
trivial.

clear height_r above_avl_r above_rr below_lr Balanced_r above_rrl below_lrl
 Balanced_lr.
apply equiv_intro.
intros key data lookup_t.
inversion_clear lookup_t.
apply Lookup_Right; apply Lookup_Left; apply Lookup_Equal.
inversion_clear H.
apply Lookup_Equal.
apply Lookup_Left; assumption.
apply Lookup_Right; apply Lookup_Left; apply Lookup_Left; assumption.
inversion_clear H.
apply Lookup_Right; apply Lookup_Equal.
apply Lookup_Right; apply Lookup_Left; apply Lookup_Right; assumption.
apply Lookup_Right; apply Lookup_Right; assumption.

intros key data lookup_t0.
inversion_clear lookup_t0.
apply Lookup_Left; apply Lookup_Equal.
apply Lookup_Left; apply Lookup_Left; assumption.
inversion_clear H.
apply Lookup_Right; apply Lookup_Equal.
inversion_clear H0.
apply Lookup_Equal.
apply Lookup_Left; apply Lookup_Right; assumption.
apply Lookup_Right; apply Lookup_Left; assumption.
apply Lookup_Right; apply Lookup_Right; assumption.

clear above_avl_r above_rr below_lr above_rrl below_lrl.
generalize height_r; clear height_r.
elim brl; simpl in |- *; trivial.

(* br=Balanced *)
simpl in |- *.
intros Balanced_r below_lr above_rr above_avl_r height_r.
exists (Avl_Node kr dr (Avl_Node k d l lr Right_Balanced) rr Left_Balanced).
repeat apply conj.
inversion_clear above_avl_r.
 injection height_r; clear height_r; intro height_r.
apply Node_Is_Avl; try assumption.
apply Node_Is_Avl; try assumption.
apply Is_Right_Balanced_Avl.
assumption.
apply Is_Left_Balanced_Avl.
simpl in |- *.
inversion_clear Balanced_r.
 rewrite H1; trivial.
apply Below_Avl_Node; assumption.

simpl in |- *.
 rewrite
 (app_ass (lin_avl l) ((k, d) :: lin_avl lr) ((kr, dr) :: lin_avl rr))
 .
trivial.

apply equiv_intro; clear above_avl_r height_r.
intros key data lookup_t.
inversion_clear lookup_t.
apply Lookup_Right; apply Lookup_Equal.
inversion_clear H.
apply Lookup_Equal.
apply Lookup_Left; assumption.
apply Lookup_Right; apply Lookup_Left; assumption.
apply Lookup_Right; apply Lookup_Right; assumption.

intros key data lookup_t0.
inversion_clear lookup_t0.
apply Lookup_Left; apply Lookup_Equal.
apply Lookup_Left; apply Lookup_Left; assumption.
inversion_clear H.
apply Lookup_Equal.
apply Lookup_Left; apply Lookup_Right; assumption.
apply Lookup_Right; assumption.

simpl in |- *.
trivial.

(* br=Right_Balanced *)
simpl in |- *.
intros Balanced_r below_lr above_rr above_avl_r height_r.
 injection height_r; clear height_r; intro height_r.
exists (Avl_Node kr dr (Avl_Node k d l lr Balanced) rr Balanced).
repeat apply conj.
inversion_clear above_avl_r.
inversion_clear Balanced_r.

apply Node_Is_Avl; try assumption.
apply Node_Is_Avl; try assumption.
apply Is_Fully_Balanced_Avl.
 rewrite <- height_r in H1.
symmetry  in |- *.
 injection H1; trivial.
apply Is_Fully_Balanced_Avl.
simpl in |- *.
assumption.
apply Below_Avl_Node; assumption.

simpl in |- *.
 rewrite
 (app_ass (lin_avl l) ((k, d) :: lin_avl lr) ((kr, dr) :: lin_avl rr))
 .
trivial.

apply equiv_intro; clear above_avl_r height_r.
intros key data lookup_t.
inversion_clear lookup_t.
apply Lookup_Right; apply Lookup_Equal.
inversion_clear H.
apply Lookup_Equal.
apply Lookup_Left; assumption.
apply Lookup_Right; apply Lookup_Left; assumption.
apply Lookup_Right; apply Lookup_Right; assumption.

intros key data lookup_t0.
inversion_clear lookup_t0.
apply Lookup_Left; apply Lookup_Equal.
apply Lookup_Left; apply Lookup_Left; assumption.
inversion_clear H.
apply Lookup_Equal.
apply Lookup_Left; apply Lookup_Right; assumption.
apply Lookup_Right; assumption.

simpl in |- *.
 rewrite height_r; trivial.
Qed.

(********************************************************************)

Inductive is_balanced_avl_left_shift (l r : avl_tree) : bal -> Prop :=
  | Is_Left_Balanced_Avl_Left_Shift :
      height_avl l = S (S (height_avl r)) ->
      is_balanced_avl_left_shift l r Left_Balanced
  | Is_Fully_Balanced_Avl_Left_Shift :
      height_avl l = S (height_avl r) ->
      is_balanced_avl_left_shift l r Balanced
  | Is_Right_Balanced_Avl_Left_Shift :
      height_avl l = height_avl r ->
      is_balanced_avl_left_shift l r Right_Balanced.



Lemma is_left_balanced_is_left_balanced_left_shift :
 forall (l0 l r0 : avl_tree) (b0 : bal),
 is_balanced_avl l0 r0 b0 ->
 height_avl l = S (height_avl l0) -> is_balanced_avl_left_shift l r0 b0.
intros l0 l r0 b0 Balanced_l0 height_l.
inversion_clear Balanced_l0.
apply Is_Left_Balanced_Avl_Left_Shift.
 rewrite <- H; assumption.
apply Is_Fully_Balanced_Avl_Left_Shift.
 rewrite <- H; assumption.
apply Is_Right_Balanced_Avl_Left_Shift.
 rewrite <- H; assumption.
Qed.


Lemma is_balanced_is_balanced_left_shift_false :
 forall (l r : avl_tree) (b : bal),
 is_balanced_avl l r b -> is_balanced_avl_left_shift l r b -> False.
intros l r b Balanced_l.
inversion_clear Balanced_l; intros Balanced_shift_l;
 inversion_clear Balanced_shift_l.
apply n_Sn_false with (S (height_avl r)).
 rewrite <- H0.
symmetry  in |- *; assumption.
apply n_Sn_false with (height_avl r).
 rewrite <- H0.
symmetry  in |- *; assumption.
apply n_Sn_false with (height_avl l).
 rewrite H.
assumption.
Qed.

(********************************************************************)

Inductive is_balanced_avl_right_shift (l r : avl_tree) : bal -> Prop :=
  | Is_Left_Balanced_Avl_Right_Shift :
      height_avl l = height_avl r ->
      is_balanced_avl_right_shift l r Left_Balanced
  | Is_Fully_Balanced_Avl_Right_Shift :
      S (height_avl l) = height_avl r ->
      is_balanced_avl_right_shift l r Balanced
  | Is_Right_Balanced_Avl_Right_Shift :
      S (S (height_avl l)) = height_avl r ->
      is_balanced_avl_right_shift l r Right_Balanced.



Lemma is_balanced_avl_is_balanced_avl_right_shift :
 forall (l0 r r0 : avl_tree) (b0 : bal),
 is_balanced_avl l0 r0 b0 ->
 height_avl r = S (height_avl r0) -> is_balanced_avl_right_shift l0 r b0.
intros l0 r r0 b0 Balanced_r0 height_l.
inversion_clear Balanced_r0.
apply Is_Left_Balanced_Avl_Right_Shift.
 rewrite H; symmetry  in |- *; assumption.
apply Is_Fully_Balanced_Avl_Right_Shift.
 rewrite H; symmetry  in |- *; assumption.
apply Is_Right_Balanced_Avl_Right_Shift.
 rewrite H; symmetry  in |- *; assumption.
Qed.


Lemma is_balanced_avl_is_balanced_avl_right_shift_false :
 forall (l r : avl_tree) (b : bal),
 is_balanced_avl l r b -> is_balanced_avl_right_shift l r b -> False.
intros l r b Balanced_l.
inversion_clear Balanced_l; intros Balanced_shift_l;
 inversion_clear Balanced_shift_l.
apply n_Sn_false with (height_avl r).
 rewrite <- H.
symmetry  in |- *; assumption.
apply n_Sn_false with (height_avl l).
 rewrite H0.
assumption.
apply n_Sn_false with (S (height_avl l)).
 rewrite H0.
assumption.
Qed.

(**********************************************************************)


Inductive hasnot_grown_left (t : avl_tree) (k : Int) 
(d : B) (l r : avl_tree) : bal -> Prop :=
  | Hasnot_Grown_Left_Bal :
      forall b : bal,
      is_balanced_avl l r b ->
      height_avl t = height_avl (Avl_Node k d l r b) ->
      hasnot_grown_left t k d l r b
  | Hasnot_Grown_Left_Shift_Left :
      is_balanced_avl_left_shift l r Left_Balanced ->
      height_avl t = height_avl l ->
      hasnot_grown_left t k d l r Left_Balanced
  | Hasnot_Grown_Left_Shift_Right :
      is_balanced_avl_left_shift l r Right_Balanced ->
      height_avl t = S (height_avl l) ->
      hasnot_grown_left t k d l r Right_Balanced.


Inductive has_grown_left (t : avl_tree) (k : Int) (d : B) 
(l r : avl_tree) : bal -> Prop :=
  | Has_Grown_Left_Shift_Left :
      is_balanced_avl_left_shift l r Left_Balanced ->
      height_avl t = S (height_avl l) ->
      has_grown_left t k d l r Left_Balanced
  | Has_Grown_Left_Shift_Balanced :
      is_balanced_avl_left_shift l r Balanced ->
      height_avl t = S (height_avl l) -> has_grown_left t k d l r Balanced.


Inductive bal_grow_left_spec (k : Int) (d : B) (l r : avl_tree) 
(b : bal) : Set :=
    Balance_Grow_Left_Spec_Intro :
      forall t : avl_tree,
      is_avl t ->
      lin_avl t = lin_avl (Avl_Node k d l r b) ->
      equiv t (Avl_Node k d l r b) ->
      {hasnot_grown_left t k d l r b} + {has_grown_left t k d l r b} ->
      bal_grow_left_spec k d l r b.


Lemma balance_left :
 forall (k : Int) (d : B) (l r : avl_tree) (b : bal),
 is_avl l ->
 is_below_avl l k ->
 is_avl r ->
 is_above_avl r k ->
 {is_balanced_avl l r b} + {is_balanced_avl_left_shift l r b} ->
 bal_grow_left_spec k d l r b.
intros k d l r b avl_l below_avl_l avl_r above_avl_r bal_or_shift.
elim bal_or_shift; clear bal_or_shift.
(* l and r is Balanced with respect to b *)
intro Balanced_l.
apply Balance_Grow_Left_Spec_Intro with (Avl_Node k d l r b). 
apply Node_Is_Avl; assumption.
trivial.
apply equiv_refl.
left.
apply Hasnot_Grown_Left_Bal. 
assumption.
trivial.

(* l and r is'nt Balanced with respect to b *)
elim b; clear b; intros Balanced_shift_l.
(* b=Left_Balanced *)
elim (rebalance_left k d l r Left_Balanced); try assumption.
intros t (avl_t,(lin,(equiv_t,height_t))).
apply Balance_Grow_Left_Spec_Intro with t.
assumption.
assumption.
assumption.
clear lin equiv_t avl_l below_avl_l.
generalize height_t; clear height_t.
generalize Balanced_shift_l; clear Balanced_shift_l.
case l; clear l.
intro u0. 
elimtype False.
inversion_clear u0.
 discriminate H.
intros kl dl ll rl bl.
elim bl; clear bl; simpl in |- *; intros Balanced_shift_l height_t.
(* bl=Left_Balanced *)
left.
apply Hasnot_Grown_Left_Shift_Left; assumption.
(* bl=Balanced *)
right.
apply Has_Grown_Left_Shift_Left; assumption.
(* bl=Right_Balanced *)
left.
apply Hasnot_Grown_Left_Shift_Left; assumption.
(* side premisses of (Elim (rebalance ... )) *)
inversion_clear Balanced_shift_l; assumption.

(* b=Balanced *)
apply Balance_Grow_Left_Spec_Intro with (Avl_Node k d l r Left_Balanced).
apply Node_Is_Avl; try assumption.
apply Is_Left_Balanced_Avl.
inversion_clear Balanced_shift_l; assumption.
trivial.
apply equiv_refl.
right.
apply Has_Grown_Left_Shift_Balanced. 
assumption.
trivial.

(* b=Right_Balanced *)
apply Balance_Grow_Left_Spec_Intro with (Avl_Node k d l r Balanced).
apply Node_Is_Avl; try assumption.
apply Is_Fully_Balanced_Avl.
inversion_clear Balanced_shift_l; assumption.
trivial.
apply equiv_refl.
simpl in |- *. 
left.
apply Hasnot_Grown_Left_Shift_Right. 
assumption.
trivial.
Qed.



(**********************************************************************)


Inductive hasnot_grown_right (t : avl_tree) (k : Int) 
(d : B) (l r : avl_tree) : bal -> Prop :=
  | Hasnot_Grown_Right_Bal :
      forall b : bal,
      is_balanced_avl l r b ->
      height_avl t = height_avl (Avl_Node k d l r b) ->
      hasnot_grown_right t k d l r b
  | Hasnot_Grown_Right_Shift_Left :
      is_balanced_avl_right_shift l r Left_Balanced ->
      height_avl t = S (height_avl r) ->
      hasnot_grown_right t k d l r Left_Balanced
  | Hasnot_Grown_Right_Shift_Right :
      is_balanced_avl_right_shift l r Right_Balanced ->
      height_avl t = height_avl r ->
      hasnot_grown_right t k d l r Right_Balanced.


Inductive has_grown_right (t : avl_tree) (k : Int) 
(d : B) (l r : avl_tree) : bal -> Prop :=
  | Has_Grown_Right_Shift_Balanced :
      is_balanced_avl_right_shift l r Balanced ->
      height_avl t = S (height_avl r) -> has_grown_right t k d l r Balanced
  | Has_Grown_Right_Shift_Right :
      is_balanced_avl_right_shift l r Right_Balanced ->
      height_avl t = S (height_avl r) ->
      has_grown_right t k d l r Right_Balanced.



Inductive bal_grow_right_spec (k : Int) (d : B) (l r : avl_tree) 
(b : bal) : Set :=
    Balance_Grow_Right_Spec_Intro :
      forall t : avl_tree,
      is_avl t ->
      lin_avl t = lin_avl (Avl_Node k d l r b) ->
      equiv t (Avl_Node k d l r b) ->
      {hasnot_grown_right t k d l r b} + {has_grown_right t k d l r b} ->
      bal_grow_right_spec k d l r b.


Lemma balance_right :
 forall (k : Int) (d : B) (l r : avl_tree) (b : bal),
 is_avl l ->
 is_below_avl l k ->
 is_avl r ->
 is_above_avl r k ->
 {is_balanced_avl l r b} + {is_balanced_avl_right_shift l r b} ->
 bal_grow_right_spec k d l r b.
intros k d l r b avl_l below_avl_l avl_r above_avl_r bal_or_shift.
elim bal_or_shift; clear bal_or_shift.
(* l and r is Balanced with respect to b *)
intro Balanced_l.
apply Balance_Grow_Right_Spec_Intro with (Avl_Node k d l r b). 
apply Node_Is_Avl; assumption.
trivial.
apply equiv_refl.
left.
apply Hasnot_Grown_Right_Bal. 
assumption.
trivial.

(* l and r is'nt Balanced with respect to b *)
elim b; clear b; intros Balanced_shift_l.
(* b=Left_Balanced *)
apply Balance_Grow_Right_Spec_Intro with (Avl_Node k d l r Balanced).
apply Node_Is_Avl; try assumption.
apply Is_Fully_Balanced_Avl.
inversion_clear Balanced_shift_l; assumption.
trivial.
apply equiv_refl.
left.
simpl in |- *. 
apply Hasnot_Grown_Right_Shift_Left. 
assumption.
simpl in |- *.
inversion_clear Balanced_shift_l.
 rewrite H; trivial.

(* b=Balanced *)
apply Balance_Grow_Right_Spec_Intro with (Avl_Node k d l r Right_Balanced).
apply Node_Is_Avl; try assumption.
apply Is_Right_Balanced_Avl.
inversion_clear Balanced_shift_l; assumption.
trivial.
apply equiv_refl.
right.
apply Has_Grown_Right_Shift_Balanced. 
assumption.
trivial.

(* b=Right_Balanced *)
elim (rebalance_right k d l r Right_Balanced); try assumption.
intros t (avl_t,(lin,(equiv_t,height_t))).
apply Balance_Grow_Right_Spec_Intro with t.
assumption.
assumption.
assumption.
clear lin equiv_t avl_l below_avl_l avl_r above_avl_r.
generalize height_t; clear height_t.
generalize Balanced_shift_l; clear Balanced_shift_l.
case r; clear r.
intro u0. 
elimtype False.
inversion_clear u0.
 discriminate H.
intros kr dr lr rr br.
elim br; clear br; simpl in |- *; intros Balanced_shift_l height_t.
(* br=Left_Balanced *)
left.
apply Hasnot_Grown_Right_Shift_Right; assumption.
(* br=Balanced *)
right.
apply Has_Grown_Right_Shift_Right; assumption.
(* br=Right_Balanced *)
left.
apply Hasnot_Grown_Right_Shift_Right; assumption.
(* side premisses of (Elim (rebalance ... )) *)
inversion_clear Balanced_shift_l; assumption.
Qed.


(*********************************************************************)
(*  equiv_ins                                                        *)

Inductive equiv_ins (key : Int) (update : B -> B) (init : B)
(t0 t : avl_tree) : Prop :=
    equiv_ins_intro :
      (forall (k : Int) (data : B),
       Equal k key -> lookup k t0 data -> lookup k t (update data)) ->
      (forall k : Int,
       Equal k key ->
       (forall data : B, lookup k t0 data -> False) ->
       lookup k t (update init)) ->
      (forall (k : Int) (data : B),
       ~ Equal k key -> lookup k t0 data -> lookup k t data) ->
      (forall (k : Int) (data : B),
       ~ Equal k key -> lookup k t data -> lookup k t0 data) ->
      equiv_ins key update init t0 t.

Lemma inv_equiv_ins_equal0 :
 forall (key : Int) (update : B -> B) (init : B) (t0 t : avl_tree) 
   (k : Int) (data : B),
 equiv_ins key update init t0 t ->
 Equal k key -> lookup k t0 data -> lookup k t (update data).
intros.
inversion_clear H.
apply H2; assumption.
Qed.


Lemma inv_equiv_ins_equal1 :
 forall (key : Int) (update : B -> B) (init : B) (t0 t : avl_tree) (k : Int),
 equiv_ins key update init t0 t ->
 Equal k key ->
 (forall data : B, lookup k t0 data -> False) -> lookup k t (update init).
intros.
inversion_clear H.
apply H3; assumption.
Qed.


Lemma inv_equiv_ins_notequal0 :
 forall (key : Int) (update : B -> B) (init : B) (t0 t : avl_tree) 
   (k : Int) (data : B),
 equiv_ins key update init t0 t ->
 ~ Equal k key -> lookup k t0 data -> lookup k t data.
intros.
inversion_clear H.
apply H4; assumption.
Qed.

Lemma inv_equiv_ins_notequal1 :
 forall (key : Int) (update : B -> B) (init : B) (t0 t : avl_tree) 
   (k : Int) (data : B),
 equiv_ins key update init t0 t ->
 ~ Equal k key -> lookup k t data -> lookup k t0 data.
intros.
inversion_clear H.
apply H5; assumption.
Qed.


Lemma equiv_ins_equiv_equiv_ins :
 forall (key : Int) (update : B -> B) (init : B) (t0 t1 t2 : avl_tree),
 equiv_ins key update init t0 t1 ->
 equiv t1 t2 -> equiv_ins key update init t0 t2.
intros key update init t0 t1 t2 equiv_ins0 equiv0.
apply equiv_ins_intro.

intros k data equal Lookup_t0.
apply (inv_equiv_t0_t1 t1 t2).
assumption.
apply (inv_equiv_ins_equal0 key update init t0 t1 k data); assumption.

intros k equal not_Lookup_t0.
apply (inv_equiv_t0_t1 t1 t2).
assumption.
apply (inv_equiv_ins_equal1 key update init t0 t1 k); assumption.

intros k data notequal Lookup_t0.
apply (inv_equiv_t0_t1 t1 t2).
assumption.
apply (inv_equiv_ins_notequal0 key update init t0 t1 k data); assumption.

intros k data notequal Lookup_t2.
apply (inv_equiv_ins_notequal1 key update init t0 t1 k data).
assumption.
assumption.
apply (inv_equiv_t1_t0 t1 t2); assumption.

Qed.




Lemma equiv_ins_below :
 forall (key : Int) (update : B -> B) (init : B) (t0 t : avl_tree) (k0 : Int),
 equiv_ins key update init t0 t ->
 Less key k0 -> is_below t0 k0 -> is_below t k0.
intros key update init t0 t k0 equiv_t0 less below_t0.
apply lookup_less_below.
intros k d lookup_t.
elim (equal_dec k key).

intro equal.
apply (equal_less_less k key k0); assumption.

intro notequal.
generalize
 (inv_equiv_ins_notequal1 key update init t0 t k d equiv_t0 notequal lookup_t).
intro lookup_t0.
apply (lookup_below_less k t0 d); assumption.
Qed.



Lemma equiv_ins_above :
 forall (key : Int) (update : B -> B) (init : B) (t0 t : avl_tree) (k0 : Int),
 equiv_ins key update init t0 t ->
 Less k0 key -> is_above t0 k0 -> is_above t k0.
intros key update init t0 t k0 equiv_t0 greater below_t0.
apply lookup_greater_above.
intros k d lookup_t.
elim (equal_dec k key).

intro equal.
apply (less_equal_less k0 key k).
assumption.
apply equal_sym; assumption.

intro notequal.
generalize
 (inv_equiv_ins_notequal1 key update init t0 t k d equiv_t0 notequal lookup_t).
intro lookup_t0.
apply (lookup_above_greater k t0 d); assumption.
Qed.

(***************************************************************************)

Lemma leave_is_avl :
 forall (k : Int) (d : B), is_avl (Avl_Node k d Avl_Nil Avl_Nil Balanced).
intros.
apply Node_Is_Avl.
apply Nil_Is_Avl.
apply Nil_Is_Avl.
apply Is_Fully_Balanced_Avl; trivial.
apply Below_Avl_Nil.
apply Above_Avl_Nil.
Qed.


Lemma equiv_ins_nil :
 forall (key : Int) (update : B -> B) (init : B),
 equiv_ins key update init Avl_Nil
   (Avl_Node key (update init) Avl_Nil Avl_Nil Balanced).
intros key update init.
apply equiv_ins_intro.
intros k data equal lookup_nil.
elimtype False.
apply (inv_lookup_nil k data lookup_nil).

intros k equal notlookup_nil.
 rewrite (equal_eq k key equal).
apply Lookup_Equal.

intros k data notequal lookup_nil.
elimtype False.
apply (inv_lookup_nil k data lookup_nil).

intros k data notequal lookup_nil.
elim
 (inv_lookup k key (update init) Avl_Nil Avl_Nil Balanced data lookup_nil).
intro u0.
elimtype False.
apply notequal.
elim u0; intros u00 u01.
 rewrite u00.
apply equal_refl.

 tauto.
Qed.


Lemma avl_ins_eq :
 forall (k : Int) (d : B) (l r : avl_tree) (b : bal) (d' : B),
 is_avl (Avl_Node k d l r b) -> is_avl (Avl_Node k d' l r b).
intros k d l r b d' avl_t.
apply Node_Is_Avl.
apply (inv_is_avl_left k d l r b avl_t).
apply (inv_is_avl_right k d l r b avl_t).
apply (inv_is_avl_is_balanced_avl k d l r b avl_t).
apply (inv_is_avl_is_is_below_avl k d l r b avl_t).
apply (inv_is_avl_is_is_above_avl k d l r b avl_t).
Qed.


Lemma equiv_ins_eq :
 forall (key : Int) (update : B -> B) (init : B) (k : Int) 
   (d : B) (l0 r0 : avl_tree) (b : bal),
 is_avl (Avl_Node k d l0 r0 b) ->
 Equal key k ->
 equiv_ins key update init (Avl_Node k d l0 r0 b)
   (Avl_Node k (update d) l0 r0 b).
intros key update init k d l0 r0 b avl_t0 equal.
generalize (avl_ins_eq k d l0 r0 b (update d) avl_t0).
intro avl_t.

apply equiv_ins_intro.

intros k0 data equal1.
generalize (equal_trans k0 key k equal1 equal).
intro equal2. 
intro lookup_t0.
 rewrite (lookup_avl_inv_equal k0 k d l0 r0 b data avl_t0 equal2 lookup_t0).
 rewrite (equal_eq k0 k equal2).
apply Lookup_Equal. 

intros k0 equal1.
generalize (equal_trans k0 key k equal1 equal).
intro equal2. 
intro not_lookup_t0.
elimtype False. 
apply (not_lookup_t0 d). 
 rewrite (equal_eq k0 k equal2).
apply Lookup_Equal. 

intros k0 data notequal0.
intro lookup_t0.
elim (inv_lookup k0 k d l0 r0 b data lookup_t0); intro u0.
elimtype False.
apply notequal0.
elim u0; clear u0; intros u0 u1.
 rewrite <- u0.
apply equal_sym; assumption.
elim u0; clear u0; intro u0.
apply Lookup_Left; assumption.
apply Lookup_Right; assumption.

intros k0 data notequal0.
intro lookup_t.
elim (inv_lookup k0 k (update d) l0 r0 b data lookup_t); intro u0.
elimtype False.
apply notequal0.
elim u0; clear u0; intros u0 u1.
 rewrite <- u0.
apply equal_sym; assumption.
elim u0; clear u0; intro u0.
apply Lookup_Left; assumption.
apply Lookup_Right; assumption.
Qed.


Lemma equiv_ins_left :
 forall (key : Int) (update : B -> B) (init : B) (k0 : Int) 
   (d0 : B) (l0 r0 : avl_tree) (b0 : bal) (l : avl_tree) 
   (b : bal),
 is_avl (Avl_Node k0 d0 l0 r0 b0) ->
 Less key k0 ->
 equiv_ins key update init l0 l ->
 equiv_ins key update init (Avl_Node k0 d0 l0 r0 b0) (Avl_Node k0 d0 l r0 b).
intros key update init k0 d0 l0 r0 b0 l b avl_t0 less equiv_ins_l0.
apply equiv_ins_intro.

intros k data equal.
generalize (equal_less_less k key k0 equal less); intro less1.
intro lookup_t0.
apply Lookup_Left.
apply (inv_equiv_ins_equal0 key update init l0 l).
assumption.
assumption.
apply (lookup_avl_inv_less k k0 d0 l0 r0 b0 data); assumption.

intros k equal.
intro not_lookup_t0.
apply Lookup_Left.
apply (inv_equiv_ins_equal1 key update init l0 l).
assumption.
assumption.
intros data lookup_l0.
apply (not_lookup_t0 data).
apply Lookup_Left; assumption.

intros k data notequal.
intro lookup_t0.
elim (inv_lookup k k0 d0 l0 r0 b0 data lookup_t0); intro u0.
elim u0; clear u0; intros u0 u1.
 rewrite u0.
 rewrite u1.
apply Lookup_Equal.

elim u0; clear u0; intros u0.
apply Lookup_Left.
apply (inv_equiv_ins_notequal0 key update init l0 l); assumption.

apply Lookup_Right; assumption.

intros k data notequal.
intro lookup_t.
elim (inv_lookup k k0 d0 l r0 b data lookup_t); intro u0.
elim u0; clear u0; intros u0 u1.
 rewrite u0.
 rewrite u1.
apply Lookup_Equal.

elim u0; clear u0; intros u0.
apply Lookup_Left.
apply (inv_equiv_ins_notequal1 key update init l0 l); assumption.

apply Lookup_Right; assumption.
Qed.




Lemma equiv_ins_right :
 forall (key : Int) (update : B -> B) (init : B) (k0 : Int) 
   (d0 : B) (l0 r0 : avl_tree) (b0 : bal) (r : avl_tree) 
   (b : bal),
 is_avl (Avl_Node k0 d0 l0 r0 b0) ->
 Less k0 key ->
 equiv_ins key update init r0 r ->
 equiv_ins key update init (Avl_Node k0 d0 l0 r0 b0) (Avl_Node k0 d0 l0 r b).
intros key update init k0 d0 l0 r0 b0 r b avl_t0 less equiv_r0.
inversion_clear equiv_r0.
apply equiv_ins_intro.

intros k data equal lookup_t0.
apply Lookup_Right.
apply H.
assumption.
apply (lookup_avl_inv_greater k k0 d0 l0 r0 b0 data); try assumption.
apply (less_equal_less k0 key k).
assumption.
apply equal_sym; assumption.

intros k equal not_lookup_t0.
apply Lookup_Right.
apply H0.
assumption.
intros data lookup_l0.
apply (not_lookup_t0 data).
apply Lookup_Right; assumption.

intros k data notequal lookup_t0.
inversion_clear lookup_t0.
apply Lookup_Equal.
apply Lookup_Left; assumption.
apply Lookup_Right.
apply H1; assumption.

intros k data notequal lookup_t.
inversion_clear lookup_t.
apply Lookup_Equal.
apply Lookup_Left; assumption.
apply Lookup_Right.
apply H2; assumption.
Qed.


(***************************************************************************)

Inductive lin_ins_spec (key : Int) (update : B -> B) 
(init : B) (t0 t : avl_tree) : Prop :=
  | Lin_Ins_New :
      forall l0 l1 : list (Int * B),
      lin_avl t0 = l0 ++ l1 ->
      lin_avl t = l0 ++ (key, update init) :: l1 ->
      lin_ins_spec key update init t0 t
  | Lin_Ins_Update :
      forall (d : B) (l0 l1 : list (Int * B)),
      lin_avl t0 = l0 ++ (key, d) :: l1 ->
      lin_avl t = l0 ++ (key, update d) :: l1 ->
      lin_ins_spec key update init t0 t.

            
Inductive avl_ins_spec (key : Int) (update : B -> B) 
(init : B) (t0 : avl_tree) : Set :=
    Avl_Ins_Spec_Intro :
      forall t : avl_tree,
      lookup_dec_spec key t0 ->
      is_avl t ->
      lin_ins_spec key update init t0 t ->
      equiv_ins key update init t0 t ->
      {height_avl t = height_avl t0} + {height_avl t = S (height_avl t0)} ->
      avl_ins_spec key update init t0.


(***************************************************************************)
(***************************************************************************)


Lemma insert_avl :
 forall (key : Int) (update : B -> B) (init : B) (t0 : avl_tree),
 is_avl t0 -> avl_ins_spec key update init t0.
intros key update init t0.
elim t0; clear t0.

(* t0=Avl_Nil *)
intros avl_t0.
apply
 Avl_Ins_Spec_Intro
  with (t := Avl_Node key (update init) Avl_Nil Avl_Nil Balanced).

apply Not_Lookup.
unfold not in |- *; intros d lookup0.
apply (inv_lookup_nil key d lookup0).

apply leave_is_avl.
apply Lin_Ins_New with (nil (A:=Int * B)) (nil (A:=Int * B)); trivial.
apply equiv_ins_nil.
right; simpl in |- *; trivial.

(* t0=(Avl_Node k0 d0 l0 r0 b0)  *)
intros k0 d0 l0 ih_l0 r0 ih_r0 b0 avl_t0.
elim (equal_dec key k0).

intro equal.
clear ih_l0 ih_r0.
apply Avl_Ins_Spec_Intro with (t := Avl_Node k0 (update d0) l0 r0 b0).
apply Lookup with d0.
 rewrite (equal_eq key k0 equal).
apply Lookup_Equal.

apply (avl_ins_eq k0 d0 l0 r0 b0); assumption.
 rewrite (equal_eq key k0 equal).
apply Lin_Ins_Update with d0 (lin_avl l0) (lin_avl r0); trivial.
apply equiv_ins_eq; assumption.
left.
elim b0; simpl in |- *; trivial.

intro notequal.
elim (less_dec key k0).
intro less.
elim (ih_l0 (inv_is_avl_left k0 d0 l0 r0 b0 avl_t0)); clear ih_l0 ih_r0.
intros l lookup_dec_spec0 avl_l lin_ins_l equiv_ins_l bal_or_shift.
elim (balance_left k0 d0 l r0 b0). 
intros t avl_t lin_t equiv_t growth_dec.
apply Avl_Ins_Spec_Intro with t.
elim lookup_dec_spec0; clear lookup_dec_spec0.
intros d lookup_d.
apply Lookup with d.
apply Lookup_Left; assumption.
intros not_lookup_d0.
apply Not_Lookup.
unfold not in |- *; intros d lookup_d0.
apply (not_lookup_d0 d).
apply (lookup_avl_inv_less key k0 d0 l0 r0 b0); assumption.

assumption.

elim lin_ins_l; clear lin_ins_l.
intros l1 l2 lin_l0 lin_l.
apply Lin_Ins_New with l1 (l2 ++ (k0, d0) :: lin_avl r0); simpl in |- *.
 rewrite lin_l0.
 rewrite (app_ass l1 l2 ((k0, d0) :: lin_avl r0)); trivial.
 rewrite lin_t; simpl in |- *.
 rewrite lin_l.
 rewrite (app_ass l1 ((key, update init) :: l2) ((k0, d0) :: lin_avl r0)).
trivial.
intros d' l1 l2 lin_l0 lin_l.
apply Lin_Ins_Update with d' l1 (l2 ++ (k0, d0) :: lin_avl r0); simpl in |- *.
 rewrite lin_l0.
 rewrite (app_ass l1 ((key, d') :: l2) ((k0, d0) :: lin_avl r0)); trivial.
 rewrite lin_t; simpl in |- *.
 rewrite lin_l.
 rewrite (app_ass l1 ((key, update d') :: l2) ((k0, d0) :: lin_avl r0)).
trivial.

apply equiv_ins_equiv_equiv_ins with (Avl_Node k0 d0 l r0 b0).
apply (equiv_ins_left key update init k0 d0 l0 r0 b0 l b0); assumption.
apply equiv_sym; assumption.
elim growth_dec; clear growth_dec.

intro has_not_grown.
left.
inversion_clear avl_t0.
generalize H1; clear H1.
clear equiv_t equiv_ins_l H3 H2 H0 H.
inversion_clear has_not_grown.
(* (is_balanced_avl l r0 b0) *)
 rewrite H0; clear H0.
inversion_clear H; simpl in |- *.
 rewrite H0; clear H0.
intros Balanced_l0; inversion_clear Balanced_l0.
 rewrite H; trivial.
 rewrite H0; clear H0.
intro Balanced_l0; inversion_clear Balanced_l0.
 rewrite H; trivial.
trivial.
(* (is_balanced_avl_left_shift l r0 Left_Balanced) *)
 rewrite H0; clear H0.
simpl in |- *.
inversion_clear H.
 rewrite H0; clear H0.
intros Balanced_l0; inversion_clear Balanced_l0.
 rewrite H; trivial.
(* (is_balanced_avl_left_shift l r0 Right_Balanced) *)
 rewrite H0; clear H0.
simpl in |- *.
inversion_clear H.
 rewrite H0; clear H0.
trivial.

intro has_grown.
right.
clear equiv_t equiv_ins_l.
inversion_clear avl_t0.
generalize H1; clear H H0 H1 H2 H3.
inversion_clear has_grown.
(*  (is_balanced_avl_left_shift l r0 Left_Balanced) *)
 rewrite H0; clear H0.
simpl in |- *.
inversion_clear H.
 rewrite H0; clear H0.
intros Balanced_l0; inversion_clear Balanced_l0.
 rewrite H; trivial.
(* (is_balanced_avl_left_shift l r0 Balanced) *)
 rewrite H0; clear H0.
simpl in |- *.
inversion_clear H.
 rewrite H0; clear H0.
intros Balanced_l0; inversion_clear Balanced_l0.
 rewrite H; trivial.

(* side premisses of Elim (balance...) *)
assumption.
apply below_below_avl.
apply equiv_ins_below with key update init l0.
assumption.
assumption.
inversion_clear avl_t0.
apply is_below_avl_is_below; assumption.
inversion_clear avl_t0; assumption.
inversion_clear avl_t0; assumption.
elim bal_or_shift; clear bal_or_shift; intro height_l.
left.
apply hasnot_grown_left__preserves_is_balanced_avl with l0.
inversion_clear avl_t0; assumption.
assumption.
right.
apply is_left_balanced_is_left_balanced_left_shift with l0.
inversion_clear avl_t0; assumption.
assumption.

(**********    greater   **********************************)

intro notless.
generalize (notequal_notless_greater key k0 notequal notless).
intro greater; clear notless.
elim (ih_r0 (inv_is_avl_right k0 d0 l0 r0 b0 avl_t0)); clear ih_l0 ih_r0.

intros r lookup_dec_spec0 avl_r lin_ins_r equiv_ins_r bal_or_shift.
elim (balance_right k0 d0 l0 r b0). 
intros t avl_t lin_t equiv_t growth_dec.
apply Avl_Ins_Spec_Intro with t.

elim lookup_dec_spec0; clear lookup_dec_spec0.
intros d lookup_d.
apply Lookup with d.
apply Lookup_Right; assumption.
intros not_lookup_d0.
apply Not_Lookup.
unfold not in |- *; intros d lookup_d.
apply (not_lookup_d0 d).
apply (lookup_avl_inv_greater key k0 d0 l0 r0 b0); assumption.

assumption.

elim lin_ins_r; clear lin_ins_r.
intros l1 l2 lin_r0 lin_r.
apply Lin_Ins_New with (lin_avl l0 ++ (k0, d0) :: l1) l2; simpl in |- *.
 rewrite lin_r0.
 rewrite (app_ass (lin_avl l0) ((k0, d0) :: l1) l2); trivial.
 rewrite lin_t; simpl in |- *.
 rewrite lin_r.
 rewrite (app_ass (lin_avl l0) ((k0, d0) :: l1) ((key, update init) :: l2)).
trivial.
intros d' l1 l2 lin_r0 lin_r.
apply Lin_Ins_Update with d' (lin_avl l0 ++ (k0, d0) :: l1) l2; simpl in |- *.
 rewrite lin_r0.
 rewrite (app_ass (lin_avl l0) ((k0, d0) :: l1) ((key, d') :: l2)); trivial.
 rewrite lin_t; simpl in |- *.
 rewrite lin_r.
 rewrite (app_ass (lin_avl l0) ((k0, d0) :: l1) ((key, update d') :: l2)).
trivial.

apply equiv_ins_equiv_equiv_ins with (Avl_Node k0 d0 l0 r b0).
apply (equiv_ins_right key update init k0 d0 l0 r0 b0 r b0); assumption.
apply equiv_sym; assumption.
clear equiv_t avl_t bal_or_shift equiv_ins_r.
elim growth_dec; clear growth_dec.

intro has_not_grown.
left.
inversion_clear avl_t0.
generalize H1; clear H H0 H1 H2 H3.
inversion_clear has_not_grown.
(* (is_balanced_avl l0 r b0) *)
 rewrite H0; clear H0.
inversion_clear H; simpl in |- *.
trivial.
trivial.
 rewrite <- H0; clear H0.
intros Balanced_l0; inversion_clear Balanced_l0.
 rewrite H; trivial.
(* (is_balanced_avl_right_shift l0 r Left_Balanced) *)
 rewrite H0; clear H0; simpl in |- *.
inversion_clear H.
 rewrite H0; trivial.
(* (is_balanced_avl_left_shift l0 r Right_Balanced) *)
 rewrite H0; clear H0; simpl in |- *.
inversion_clear H.
 rewrite <- H0; clear H0.
intro Balanced_l0; inversion_clear Balanced_l0.
 rewrite H; trivial.

intro has_grown.
right.
inversion_clear avl_t0.
generalize H1; clear H H0 H1 H2 H3.
inversion_clear has_grown; simpl in |- *.
(*  (is_balanced_avl_right_shift l0 r Balanced) *)
 rewrite H0; clear H0.
inversion_clear H.
 rewrite H0; trivial.
(* (is_balanced_avl_right_shift l0 r Right_Balanced) *)
 rewrite H0; clear H0.
inversion_clear H.
 rewrite <- H0; clear H0.
intros Balanced_l0; inversion_clear Balanced_l0.
 rewrite H; trivial.

(* side premisses of Elim (balance...) *)
inversion_clear avl_t0; assumption.
inversion_clear avl_t0; assumption.
assumption.
apply above_above_avl.
apply equiv_ins_above with key update init r0.
assumption.
assumption.
inversion_clear avl_t0.
apply is_above_avl_is_above; assumption.
elim bal_or_shift; clear bal_or_shift; intro height_r.
left.
apply hasnot_grown_right__preserves_is_balanced_avl with r0.
inversion_clear avl_t0; assumption.
assumption.
right.
apply is_balanced_avl_is_balanced_avl_right_shift with r0.
inversion_clear avl_t0; assumption.
assumption.
Qed.


(***********************************************************************)


Inductive equiv_del (key : Int) (t0 t : avl_tree) : Prop :=
    equiv_del_intro :
      (forall k : Int, Equal k key -> forall d : B, lookup k t d -> False) ->
      (forall (k : Int) (data : B),
       ~ Equal k key -> lookup k t0 data -> lookup k t data) ->
      (forall (k : Int) (data : B),
       ~ Equal k key -> lookup k t data -> lookup k t0 data) ->
      equiv_del key t0 t.


Lemma inv_equiv_del_equal :
 forall (key : Int) (t0 t : avl_tree) (k : Int) (d : B),
 equiv_del key t0 t -> Equal k key -> lookup k t d -> False.
intros.
inversion H.
apply H2 with (k := k) (d := d); assumption.
Qed.


Lemma inv_equiv_del_notequal0 :
 forall (key : Int) (t0 t : avl_tree) (k : Int) (d : B),
 equiv_del key t0 t -> ~ Equal k key -> lookup k t0 d -> lookup k t d.
intros.
inversion H.
apply H3; assumption.
Qed.

Lemma inv_equiv_del_notequal1 :
 forall (key : Int) (t0 t : avl_tree) (k : Int) (d : B),
 equiv_del key t0 t -> ~ Equal k key -> lookup k t d -> lookup k t0 d.
intros.
inversion H.
apply H4; assumption.
Qed.



Lemma equiv_del_equiv_equiv_del :
 forall (key : Int) (t0 t1 t2 : avl_tree),
 equiv_del key t0 t1 -> equiv t1 t2 -> equiv_del key t0 t2.
intros key t0 t1 t2 equiv_del0 equiv0.
inversion_clear equiv_del0.
inversion_clear equiv0.
apply equiv_del_intro.

intros k equal data lookup_t2.
apply H with k data.
assumption.
apply H3; assumption.

intros k data notequal lookup_t0.
apply H2.
apply H0; assumption.

intros k data notequal lookup_t2.
apply H1.
assumption.
apply H3; assumption.
Qed.


(*****************************************************************)

Lemma equiv_del_semi_leave :
 forall (k : Int) (d : B) (l : avl_tree) (b : bal),
 is_avl (Avl_Node k d l Avl_Nil b) ->
 equiv_del k (Avl_Node k d l Avl_Nil b) l.
intros k d l b avl_t.
apply equiv_del_intro.

intros k0 equal d0 lookup_l.
inversion_clear avl_t.
apply lookup_below_false with k0 l d0.
assumption.
 rewrite (equal_eq k0 k equal).
apply is_below_avl_is_below; assumption.

intros k0 data notequal lookup_t.
inversion lookup_t.
 rewrite H0 in notequal.
elimtype False.
apply notequal.
apply equal_refl.
assumption.
inversion_clear H5.

intros k0 data notequal lookup_l.
apply Lookup_Left; assumption.
Qed.

(*************************************************************************)

Lemma equiv_del_above :
 forall (key : Int) (t0 t : avl_tree) (k0 : Int),
 equiv_del key t0 t -> Less k0 key -> is_above t0 k0 -> is_above t k0.
intros key t0 t k0 equiv_t0 greater below_t0.
apply lookup_greater_above.
intros k d lookup_t.
elim (equal_dec k key).

intro equal.
apply (less_equal_less k0 key k).
assumption.
apply equal_sym; assumption.

intro notequal.
apply (lookup_above_greater k t0 d).
inversion_clear equiv_t0.
apply H1; assumption.
assumption.
Qed.


Lemma equiv_del_right :
 forall (key k0 : Int) (d0 : B) (l0 r0 : avl_tree) 
   (b0 : bal) (r : avl_tree) (b : bal),
 is_avl (Avl_Node k0 d0 l0 r0 b0) ->
 Less k0 key ->
 equiv_del key r0 r ->
 equiv_del key (Avl_Node k0 d0 l0 r0 b0) (Avl_Node k0 d0 l0 r b).
intros key k0 d0 l0 r0 b0 r b avl_t0 less equiv_r0.
inversion_clear equiv_r0.
apply equiv_del_intro.

intros k equal data lookup_t.
elim (inv_lookup k k0 d0 l0 r b data lookup_t); intro u0.
elim u0; clear u0; intros u0 u1.
 rewrite u0 in less.
 rewrite (equal_eq k key equal) in less.
apply less_irrefl with key; assumption.
elim u0; clear u0; intro u0.
 rewrite (equal_eq k key equal) in u0.
apply lookup_below_false with key l0 data.
assumption.
apply below_trans with k0.
inversion_clear avl_t0.
apply is_below_avl_is_below; assumption.
assumption.
apply H with k data; assumption.

intros k data notequal lookup_t0.
inversion_clear lookup_t0.
apply Lookup_Equal.
apply Lookup_Left; assumption.
apply Lookup_Right.
apply H0; assumption.

intros k data notequal lookup_t.
inversion_clear lookup_t.
apply Lookup_Equal.
apply Lookup_Left; assumption.
apply Lookup_Right.
apply H1; assumption.
Qed.



(**********************************************************************)

Lemma below_equiv_below :
 forall (k : Int) (t0 t : avl_tree),
 is_below t0 k -> equiv t t0 -> is_below t k.
intros k t0 t below_t0 equiv_t.
inversion_clear equiv_t.
apply lookup_less_below.
intros k0 d0 lookup_k0.
apply lookup_below_less with t0 d0.
apply H; assumption.
assumption.
Qed.

Lemma Balanced_shrunk_left_balanced_shift :
 forall (l0 r r0 : avl_tree) (b0 : bal),
 is_balanced_avl l0 r0 b0 ->
 height_avl r0 = S (height_avl r) -> is_balanced_avl_left_shift l0 r b0.
intros l0 r r0 b0 Balanced_l0 height_r.
inversion_clear Balanced_l0.
apply Is_Left_Balanced_Avl_Left_Shift.
 rewrite <- height_r; assumption.
apply Is_Fully_Balanced_Avl_Left_Shift.
 rewrite <- height_r; assumption.
apply Is_Right_Balanced_Avl_Left_Shift.
 rewrite <- H in height_r. 
 injection height_r; trivial.
Qed.


Lemma below_equiv_del_below :
 forall (t0 t : avl_tree) (k key : Int),
 is_below t0 k -> equiv_del key t0 t -> is_below t k.
intros t0 t k key below_t0 equiv_del_t0.
inversion_clear equiv_del_t0.
apply lookup_less_below.
intros k0 d0 lookup_k0.
apply lookup_below_less with t0 d0.
elim (equal_dec k0 key).
intros equal_k0.
elimtype False.
apply H with k0 d0; assumption.
intros not_equal_k0.
apply H1; assumption.
assumption.
Qed.


Lemma above_equiv_del_above :
 forall (t0 t : avl_tree) (k key : Int),
 is_above t0 k -> equiv_del key t0 t -> is_above t k.
intros t0 t k key above_t0 equiv_del_t0.
inversion_clear equiv_del_t0.
apply lookup_greater_above.
intros k0 d0 lookup_k0.
apply lookup_above_greater with t0 d0.
elim (equal_dec k0 key).
intros equal_k0.
elimtype False.
apply H with k0 d0; assumption.
intros not_equal_k0.
apply H1; assumption.
assumption.
Qed.



(**********************************************************************)


Inductive hasnot_shrunk_left (t : avl_tree) (k : Int) 
(d : B) (l r : avl_tree) : bal -> Prop :=
  | Hasnot_Shrunk_Left_Bal :
      forall b : bal,
      is_balanced_avl l r b ->
      height_avl t = height_avl (Avl_Node k d l r b) ->
      hasnot_shrunk_left t k d l r b
  | Hasnot_Shrunk_Left_Shift_Left :
      is_balanced_avl_left_shift l r Left_Balanced ->
      height_avl t = S (height_avl l) ->
      hasnot_shrunk_left t k d l r Left_Balanced
  | Hasnot_Shrunk_Left_Shift_Balanced :
      is_balanced_avl_left_shift l r Balanced ->
      height_avl t = S (height_avl l) ->
      hasnot_shrunk_left t k d l r Balanced.


Inductive has_shrunk_left (t : avl_tree) (k : Int) 
(d : B) (l r : avl_tree) : bal -> Prop :=
  | Has_Shrunk_Left_Shift_Left :
      is_balanced_avl_left_shift l r Left_Balanced ->
      height_avl t = height_avl l -> has_shrunk_left t k d l r Left_Balanced
  | Has_Shrunk_Left_Shift_Right :
      is_balanced_avl_left_shift l r Right_Balanced ->
      height_avl t = S (height_avl l) ->
      has_shrunk_left t k d l r Right_Balanced.




Inductive bal_shrunk_left_spec (k : Int) (d : B) (l r : avl_tree) 
(b : bal) : Set :=
    Balance_Shrunk_Left_Spec_Intro :
      forall t : avl_tree,
      is_avl t ->
      lin_avl t = lin_avl (Avl_Node k d l r b) ->
      equiv t (Avl_Node k d l r b) ->
      {hasnot_shrunk_left t k d l r b} + {has_shrunk_left t k d l r b} ->
      bal_shrunk_left_spec k d l r b.


Lemma balance_shrunk_left :
 forall (k : Int) (d : B) (l r : avl_tree) (b : bal),
 is_avl l ->
 is_below_avl l k ->
 is_avl r ->
 is_above_avl r k ->
 {is_balanced_avl l r b} + {is_balanced_avl_left_shift l r b} ->
 bal_shrunk_left_spec k d l r b.
intros k d l r b avl_l below_avl_l avl_r above_avl_r bal_or_shift.
elim bal_or_shift; clear bal_or_shift.
(* l and r is Balanced with respect to b *)
intro Balanced_l.
apply Balance_Shrunk_Left_Spec_Intro with (Avl_Node k d l r b). 
apply Node_Is_Avl; assumption.
trivial.
apply equiv_refl.
left.
apply Hasnot_Shrunk_Left_Bal. 
assumption.
trivial.

(* l and r is'nt Balanced with respect to b *)
elim b; clear b; intros Balanced_shift_l.
(* b=Left_Balanced *)
elim (rebalance_left k d l r Left_Balanced); try assumption.
intros t (avl_t,(lin_t,(equiv_t,height_t))).
apply Balance_Shrunk_Left_Spec_Intro with t.
assumption.
assumption.
assumption.
clear lin_t equiv_t avl_l below_avl_l.
generalize height_t; clear height_t.
generalize Balanced_shift_l; clear Balanced_shift_l.
case l; clear l.
intro u0. 
elimtype False.
inversion_clear u0.
 discriminate H.
intros kl dl ll rl bl.
elim bl; clear bl; simpl in |- *; intros Balanced_shift_l height_t.
(* bl=Left_Balanced *)
right.
apply Has_Shrunk_Left_Shift_Left; assumption.
(* bl=Balanced *)
left.
apply Hasnot_Shrunk_Left_Shift_Left; assumption.
(* bl=Right_Balanced *)
right.
apply Has_Shrunk_Left_Shift_Left; assumption.
(* side premisses of (Elim (rebalance ... )) *)
inversion_clear Balanced_shift_l; assumption.

(* b=Balanced *)
apply Balance_Shrunk_Left_Spec_Intro with (Avl_Node k d l r Left_Balanced).
apply Node_Is_Avl; try assumption.
apply Is_Left_Balanced_Avl.
inversion_clear Balanced_shift_l; assumption.
trivial.
apply equiv_refl.
left.
apply Hasnot_Shrunk_Left_Shift_Balanced. 
assumption.
trivial.

(* b=Right_Balanced *)
apply Balance_Shrunk_Left_Spec_Intro with (Avl_Node k d l r Balanced).
apply Node_Is_Avl; try assumption.
apply Is_Fully_Balanced_Avl.
inversion_clear Balanced_shift_l; assumption.
trivial.
apply equiv_refl.
right.
apply Has_Shrunk_Left_Shift_Right. 
assumption.
trivial.
Qed.

(*****************************************************************)

Inductive delete_max_spec (t0 : avl_tree) : Set :=
    Del_Max_Spec_Intro :
      forall (k : Int) (d : B) (t : avl_tree),
      lookup k t0 d ->
      is_avl t ->
      is_below_avl t k ->
      lin_avl t0 = lin_avl t ++ (k, d) :: nil ->
      equiv_del k t0 t ->
      {height_avl t0 = height_avl t} + {height_avl t0 = S (height_avl t)} ->
      delete_max_spec t0.


(*****************************************************************)

Lemma delete_max :
 forall (k0 : Int) (d0 : B) (l0 r0 : avl_tree) (b0 : bal),
 is_avl (Avl_Node k0 d0 l0 r0 b0) ->
 delete_max_spec (Avl_Node k0 d0 l0 r0 b0).
intros k0 d0 l0 r0.
generalize l0; clear l0.
generalize d0; clear d0.
generalize k0; clear k0.
elim r0; clear r0.

(* r0=Avl_Nil *)
intros k0 d0 l0 b0 avl_t0.
apply Del_Max_Spec_Intro with k0 d0 l0.
apply Lookup_Equal.
inversion_clear avl_t0; assumption.
inversion_clear avl_t0; assumption.
trivial.
apply equiv_del_semi_leave; assumption.
right.
inversion_clear avl_t0.
inversion_clear H1.
simpl in |- *; trivial.
simpl in |- *; trivial.
 discriminate H4.

(* r0=(Avl_Node kr0 dr0 lr0 rr0 br0) *)
intros kr0 dr0 lr0 ih_lr0 rr0 ih_rr0 br0 k0 d0 l0 b0 avl_t0.
elim (ih_rr0 kr0 dr0 lr0 br0); clear ih_lr0 ih_rr0.
intros k d r lookup_r avl_r below_avl_r lin_r equiv_del_r bal_or_shift.
elim (balance_shrunk_left k0 d0 l0 r b0). 
intros t avl_t lin_t equiv_t shrunk_dec.
apply Del_Max_Spec_Intro with k d t.

apply Lookup_Right; assumption.

assumption.

apply below_below_avl.
apply below_equiv_below with (Avl_Node k0 d0 l0 r b0).
cut (Less k0 k).
intro less_k0.
apply Below_Node.
assumption.
apply below_trans with k0.
inversion_clear avl_t0.
apply is_below_avl_is_below; assumption.
assumption.
apply is_below_avl_is_below; assumption.
apply lookup_above_greater with (Avl_Node kr0 dr0 lr0 rr0 br0) d.
assumption.
inversion_clear avl_t0.
apply is_above_avl_is_above; assumption.
assumption.

 rewrite lin_t.
simpl in |- *.
 rewrite (app_ass (lin_avl l0) ((k0, d0) :: lin_avl r) ((k, d) :: nil)).
simpl in |- *.
 rewrite <- lin_r.
trivial.

apply equiv_del_equiv_equiv_del with (Avl_Node k0 d0 l0 r b0).
apply equiv_del_right.
assumption.
apply lookup_above_greater with (Avl_Node kr0 dr0 lr0 rr0 br0) d.
assumption.
inversion_clear avl_t0.
apply is_above_avl_is_above; assumption.
assumption.
apply equiv_sym; assumption.


clear equiv_t avl_t lin_r equiv_del_r below_avl_r lookup_r bal_or_shift.
elim shrunk_dec; clear shrunk_dec.

intros has_notshrunk.
left.
inversion_clear avl_t0.
generalize H1; clear H H0 H1 H2 H3.
inversion_clear has_notshrunk.
 rewrite H0; clear H0.
inversion_clear H; simpl in |- *. 
trivial.
trivial.
 rewrite <- H0; clear H0.
intros Balanced_l; inversion_clear Balanced_l.
 rewrite H.
simpl in |- *; trivial.

 rewrite H0; simpl in |- *; trivial.
 rewrite H0; simpl in |- *; trivial.

intro has_shrunk.
right.
inversion_clear avl_t0.
generalize H1; clear H1 H H0 H2 H3.
inversion_clear has_shrunk; simpl in |- *.

 rewrite H0; clear H0.
trivial.

 rewrite H0; clear H0.
intros Balanced_l; inversion_clear Balanced_l.
 rewrite H0.
simpl in |- *; trivial.

(* side premisses (Elim (balance ...)) *)
inversion_clear avl_t0; assumption.
inversion_clear avl_t0; assumption.
assumption.
apply above_above_avl.
apply above_equiv_del_above with (Avl_Node kr0 dr0 lr0 rr0 br0) k. 
inversion_clear avl_t0.
apply is_above_avl_is_above; assumption.
assumption.
elim bal_or_shift; clear bal_or_shift; intros height_r.
left.
apply
 hasnot_grown_right__preserves_is_balanced_avl
  with (Avl_Node kr0 dr0 lr0 rr0 br0).
inversion_clear avl_t0; assumption.
symmetry  in |- *; assumption.
right.
apply Balanced_shrunk_left_balanced_shift with (Avl_Node kr0 dr0 lr0 rr0 br0).
inversion_clear avl_t0; assumption.
assumption.

(* Side premiss of (Elim ih_rr0) *)
inversion_clear avl_t0; assumption.
Qed.

(**********************************************************************)


Inductive hasnot_shrunk_right (t : avl_tree) (k : Int) 
(d : B) (l r : avl_tree) : bal -> Prop :=
  | Hasnot_Shrunk_Right_Bal :
      forall b : bal,
      is_balanced_avl l r b ->
      height_avl t = height_avl (Avl_Node k d l r b) ->
      hasnot_shrunk_right t k d l r b
  | Hasnot_Shrunk_Right_Shift_Balanced :
      is_balanced_avl_right_shift l r Balanced ->
      height_avl t = S (height_avl r) ->
      hasnot_shrunk_right t k d l r Balanced
  | Hasnot_Shrunk_Right_Shift_Right :
      is_balanced_avl_right_shift l r Right_Balanced ->
      height_avl t = S (height_avl r) ->
      hasnot_shrunk_right t k d l r Right_Balanced.

Inductive has_shrunk_right (t : avl_tree) (k : Int) 
(d : B) (l r : avl_tree) : bal -> Prop :=
  | Has_Shrunk_Right_Shift_Left :
      is_balanced_avl_right_shift l r Left_Balanced ->
      height_avl t = S (height_avl r) ->
      has_shrunk_right t k d l r Left_Balanced
  | Has_Shrunk_Right_Shift_Right :
      is_balanced_avl_right_shift l r Right_Balanced ->
      height_avl t = height_avl r ->
      has_shrunk_right t k d l r Right_Balanced.




Inductive bal_shrunk_right_spec (k : Int) (d : B) (l r : avl_tree) 
(b : bal) : Set :=
    Balance_Shrunk_Right_Spec_Intro :
      forall t : avl_tree,
      is_avl t ->
      lin_avl t = lin_avl (Avl_Node k d l r b) ->
      equiv t (Avl_Node k d l r b) ->
      {hasnot_shrunk_right t k d l r b} + {has_shrunk_right t k d l r b} ->
      bal_shrunk_right_spec k d l r b.


Lemma balance_shrunk_right :
 forall (k : Int) (d : B) (l r : avl_tree) (b : bal),
 is_avl l ->
 is_below_avl l k ->
 is_avl r ->
 is_above_avl r k ->
 {is_balanced_avl l r b} + {is_balanced_avl_right_shift l r b} ->
 bal_shrunk_right_spec k d l r b.
intros k d l r b avl_l below_avl_l avl_r above_avl_r bal_or_shift.
elim bal_or_shift; clear bal_or_shift.
(* l and r is Balanced with respect to b *)
intro Balanced_l.
apply Balance_Shrunk_Right_Spec_Intro with (Avl_Node k d l r b). 
apply Node_Is_Avl; assumption.
trivial.
apply equiv_refl.
left.
apply Hasnot_Shrunk_Right_Bal. 
assumption.
trivial.

(* l and r is'nt Balanced with respect to b *)
elim b; clear b; intros Balanced_shift_l.
(* b=Left_Balanced *)
apply Balance_Shrunk_Right_Spec_Intro with (Avl_Node k d l r Balanced).
apply Node_Is_Avl; try assumption.
apply Is_Fully_Balanced_Avl.
inversion_clear Balanced_shift_l; assumption.
trivial.
apply equiv_refl.
right.
apply Has_Shrunk_Right_Shift_Left. 
assumption.
simpl in |- *.
inversion_clear Balanced_shift_l.
 rewrite H; trivial.

(* b=Balanced *)
apply Balance_Shrunk_Right_Spec_Intro with (Avl_Node k d l r Right_Balanced).
apply Node_Is_Avl; try assumption.
apply Is_Right_Balanced_Avl.
inversion_clear Balanced_shift_l; assumption.
trivial.
apply equiv_refl.
left.
apply Hasnot_Shrunk_Right_Shift_Balanced. 
assumption.
trivial.

(* b=Right_Balanced *)
elim (rebalance_right k d l r Right_Balanced); try assumption.
intros t (avl_t,(lin_t,(equiv_t,height_t))).
apply Balance_Shrunk_Right_Spec_Intro with t.
assumption.
assumption.
assumption.
clear lin_t equiv_t avl_l below_avl_l avl_r above_avl_r.
generalize height_t; clear height_t.
generalize Balanced_shift_l; clear Balanced_shift_l.
case r; clear r.
intro u0. 
elimtype False.
inversion_clear u0.
 discriminate H.
intros kr dr lr rr br.
elim br; clear br; simpl in |- *; intros Balanced_shift_l height_t.
(* br=Left_Balanced *)
right.
apply Has_Shrunk_Right_Shift_Right; assumption.
(* br=Balanced *)
left.
apply Hasnot_Shrunk_Right_Shift_Right; assumption.
(* br=Right_Balanced *)
right.
apply Has_Shrunk_Right_Shift_Right; assumption.
(* side premisses of (Elim (rebalance ... )) *)
inversion_clear Balanced_shift_l; assumption.
Qed.

(*******************************************************************)


Inductive lin_del_spec (key : Int) (d : B) (t0 t : avl_tree) : Prop :=
    Lin_Del_Spec_Intro :
      forall l0 l1 : list (Int * B),
      lin_avl t0 = l0 ++ (key, d) :: l1 ->
      lin_avl t = l0 ++ l1 -> lin_del_spec key d t0 t.


Inductive delete_spec (key : Int) (t0 : avl_tree) : Set :=
    Delete_Spec_Intro :
      forall t : avl_tree,
      lookup_dec_spec key t0 ->
      is_avl t ->
      (forall d : B, lookup key t0 d -> lin_del_spec key d t0 t) ->
      equiv_del key t0 t ->
      {height_avl t0 = height_avl t} + {height_avl t0 = S (height_avl t)} ->
      delete_spec key t0.


Lemma equiv_del_nil : forall key : Int, equiv_del key Avl_Nil Avl_Nil.
intros key.
apply equiv_del_intro.

intros k equal d lookup_nil.
apply (inv_lookup_nil k d lookup_nil).

intros k d notequal lookup_nil.
apply lookup_nil.

intros k d notequal lookup_nil.
apply lookup_nil.
Qed.


Lemma equiv_del_right_semi_leave :
 forall (k : Int) (d : B) (r : avl_tree) (b : bal),
 is_avl (Avl_Node k d Avl_Nil r b) ->
 equiv_del k (Avl_Node k d Avl_Nil r b) r.
intros k d r b avl_t.
apply equiv_del_intro.

intros k0 equal d0 lookup_r.
apply (less_irrefl k).
apply (less_equal_less k k0 k).
apply (lookup_above_greater k0 r d0 k lookup_r).
inversion_clear avl_t. 
apply is_above_avl_is_above; assumption.
assumption.

intros k0 data notequal lookup_t.
generalize notequal; clear notequal.
inversion_clear lookup_t.
intro notequal.
elimtype False.
apply notequal.
apply equal_refl.
inversion_clear H.
intros; assumption.

intros k0 data notequal lookup_l.
apply Lookup_Right; assumption.
Qed.


Lemma equiv_del_equal :
 forall (key k0 k : Int) (l0 l r0 : avl_tree) (b0 : bal) (d d0 : B),
 Equal key k0 ->
 equiv_del k l0 l ->
 lookup k l0 d ->
 is_below l0 k0 ->
 is_above r0 k0 ->
 is_avl l0 -> equiv_del key (Avl_Node k0 d0 l0 r0 b0) (Avl_Node k d l r0 b0).
intros key k0 k l0 l r0 b0 d d0 equal_key equiv_del_l lookup_l below_l0
 above_r0 avl_l0.
 rewrite (equal_eq key k0 equal_key); clear equal_key key.
apply equiv_del_intro.

intros k1 equal_k1 d1 lookup_d1.
 rewrite (equal_eq k1 k0 equal_k1) in lookup_d1; clear equal_k1 k1.

inversion lookup_d1.
apply lookup_below_false with k l0 d.
assumption.
 rewrite <- H0.
assumption.
clear H0 H4 H3 H2 H1 H data b r l1 d2 k1 lookup_d1.
apply lookup_below_false with k0 l0 d1.
inversion_clear equiv_del_l.
apply H1.
unfold not in |- *; intro u0.
apply H with k0 d1; assumption.
assumption.
assumption.
clear H0 H4 H3 H2 H1 H data b r l1 d2 k1 lookup_d1.
apply lookup_above_false with k0 r0 d1.
assumption.
assumption.

intros k1 d1 notequal lookup_t0.

inversion lookup_t0; clear lookup_t0.
elimtype False.
apply notequal.
 rewrite H0.
apply equal_refl.
clear H0 H4 H3 H2 H1 H data b r l1 d2 k2.
elim (equal_dec k1 k).
intro equal_k1.
 rewrite (equal_eq k1 k equal_k1).
 rewrite <- (lookup_avl_equal k1 k l0 d1 d); try assumption.
apply Lookup_Equal.

intros notequal0.
apply Lookup_Left.
inversion_clear equiv_del_l.
apply H0; assumption.

clear H0 H4 H3 H2 H1 H data b r l1 d2 k2.
apply Lookup_Right.
assumption.

intros k1 d1 notequal lookup_k1.
inversion lookup_k1.
 rewrite <- H5.
apply Lookup_Left; assumption.
clear H0 H4 H3 H2 H1 H data b r l1 d2 k2.
apply Lookup_Left.
inversion_clear equiv_del_l.
elim (equal_dec k1 k).
intro equal_k1.
elimtype False.
apply H with k1 d1; assumption.
intro notequal_k1.
apply H1; assumption.

apply Lookup_Right; assumption.
Qed.


Lemma is_balanced_avl_is_balanced_avl_right_shift_left :
 forall (l l0 r0 : avl_tree) (b0 : bal),
 is_balanced_avl l0 r0 b0 ->
 S (height_avl l) = height_avl l0 -> is_balanced_avl_right_shift l r0 b0.
intros l l0 r0 b0 Balanced_r0 height_l.
inversion_clear Balanced_r0.
apply Is_Left_Balanced_Avl_Right_Shift.
 rewrite H in height_l.
 injection height_l; trivial.
apply Is_Fully_Balanced_Avl_Right_Shift.
 rewrite <- H; assumption.
apply Is_Right_Balanced_Avl_Right_Shift.
 rewrite height_l.
assumption.
Qed.


Lemma is_balanced_is_balanced_right_shift :
 forall (l l0 r0 : avl_tree) (b0 : bal),
 is_balanced_avl l0 r0 b0 ->
 height_avl l0 = S (height_avl l) -> is_balanced_avl_right_shift l r0 b0.
intros l l0 r0 b0 Balanced_l0 height_r.
inversion_clear Balanced_l0.
apply Is_Left_Balanced_Avl_Right_Shift.
 rewrite H in height_r.
symmetry  in |- *.
 injection height_r; trivial.
apply Is_Fully_Balanced_Avl_Right_Shift.
 rewrite <- height_r; assumption.
apply Is_Right_Balanced_Avl_Right_Shift.
 rewrite <- H.
 rewrite height_r; trivial.
Qed.

Lemma equiv_del_trans_left :
 forall (k k0 : Int) (d0 : B) (l0 r0 l : avl_tree) (b0 : bal),
 Less k k0 ->
 is_above r0 k0 ->
 equiv_del k l0 l ->
 equiv_del k (Avl_Node k0 d0 l0 r0 b0) (Avl_Node k0 d0 l r0 b0).
intros k k0 d0 l0 r0 l b0 less_k above_r0 equiv_del_l0.
inversion_clear equiv_del_l0.
apply equiv_del_intro.

intros k1 equal_k1 d1 lookup1.
apply H with k1 d1.
assumption.
 rewrite (equal_eq k1 k equal_k1).
 rewrite (equal_eq k1 k equal_k1) in lookup1; clear equal_k1 k1.
inversion lookup1.
elimtype False.
apply less_irrefl with k0.
 rewrite H3 in less_k.
assumption.
assumption.
elimtype False.
apply lookup_above_false with k r0 d1.
assumption.
apply above_trans with k0.
assumption.
assumption.

intros k1 d1 notequal lookup1.
inversion_clear lookup1.
apply Lookup_Equal.
apply Lookup_Left.
apply H0; assumption.
apply Lookup_Right; assumption.

intros k1 d1 notequal lookup1.
inversion_clear lookup1.
apply Lookup_Equal.
apply Lookup_Left.
apply H1; assumption.
apply Lookup_Right; assumption.
Qed.


Lemma equiv_del_trans_right :
 forall (k k0 : Int) (d0 : B) (l0 r r0 : avl_tree) (b0 : bal),
 Less k0 k ->
 is_below l0 k0 ->
 equiv_del k r0 r ->
 equiv_del k (Avl_Node k0 d0 l0 r0 b0) (Avl_Node k0 d0 l0 r b0).
intros k k0 d0 l0 r0 l b0 greater_k below_l0 equiv_del_r0.
inversion_clear equiv_del_r0.
apply equiv_del_intro.

intros k1 equal_k1 d1 lookup1.
apply H with k1 d1.
assumption.
 rewrite (equal_eq k1 k equal_k1).
 rewrite (equal_eq k1 k equal_k1) in lookup1; clear equal_k1 k1.
inversion lookup1.
elimtype False.
apply less_irrefl with k0.
 rewrite H3 in greater_k.
assumption.
elimtype False.
apply lookup_below_false with k l0 d1.
assumption.
apply below_trans with k0.
assumption.
assumption.
assumption.

intros k1 d1 notequal lookup1.
inversion_clear lookup1.
apply Lookup_Equal.
apply Lookup_Left; assumption.
apply Lookup_Right.
apply H0; assumption.


intros k1 d1 notequal lookup1.
inversion_clear lookup1.
apply Lookup_Equal.
apply Lookup_Left; assumption.
apply Lookup_Right.
apply H1; assumption.
Qed.


(*****************************************************************)

Lemma delete_avl :
 forall (key : Int) (t0 : avl_tree), is_avl t0 -> delete_spec key t0.
intros key t0; elim t0; clear t0.

(* t0=nil *)
intros avl_t0.
apply Delete_Spec_Intro with (t := Avl_Nil).

right.
unfold not in |- *; intros d lookup_t0.
inversion_clear lookup_t0.

assumption.

intros d lookup_t0.
elimtype False.
inversion_clear lookup_t0.

apply equiv_del_nil.

left; simpl in |- *; trivial.

(* t0=(Avl_Node k0 d0 l0 r0 b0) *)
intros k0 d0 l0 ih_l0 r0 ih_r0 b0 avl_t0.
elim (equal_dec key k0).

(* (Equal key=k0)  *)
intros equal.
clear ih_l0 ih_r0.
generalize avl_t0; clear avl_t0.
case l0; clear l0.
(* l0=nil *)
intro avl_t0.
apply Delete_Spec_Intro with (t := r0).

left with d0.
 rewrite (equal_eq key k0 equal).
simpl in |- *.
apply Lookup_Equal.

inversion_clear avl_t0; assumption.

intros d lookup0.
apply Lin_Del_Spec_Intro with (nil (A:=Int * B)) (lin_avl r0). 
 rewrite (equal_eq key k0 equal); trivial.
 rewrite (lookup_avl_equal key k0 (Avl_Node k0 d0 Avl_Nil r0 b0) d d0);
 try assumption.
trivial.
apply Lookup_Equal.
simpl in |- *; trivial.

 rewrite (equal_eq key k0 equal).
apply equiv_del_right_semi_leave; assumption.

right. 
inversion_clear avl_t0.
inversion_clear H1; simpl in |- *.
 discriminate H4.
 rewrite <- H4.
simpl in |- *; trivial.
trivial.

(* l0=(node kl0 dl0 ll0 rl0 bl0) *)
intros kl0 dl0 ll0 rl0 bl0 avl_t0.
elim (delete_max kl0 dl0 ll0 rl0 bl0).

intros k d l lookup_l0 avl_l below_l lin_l0 equiv_del_l0 bal_or_shift.
elim (balance_shrunk_right k d l r0 b0); try assumption.
intros t avl_t lin_t0 equiv_t0 shrunk_dec.
apply Delete_Spec_Intro with (t := t).

left with d0.
 rewrite (equal_eq key k0 equal).
simpl in |- *; apply Lookup_Equal.

assumption.

intros d1 lookup0.
apply
 Lin_Del_Spec_Intro
  with (lin_avl ll0 ++ (kl0, dl0) :: lin_avl rl0) (lin_avl r0).
 rewrite (equal_eq key k0 equal).
 rewrite
 (lookup_avl_equal key k0
    (Avl_Node k0 d0 (Avl_Node kl0 dl0 ll0 rl0 bl0) r0 b0) d1 d0)
 ; try assumption.
simpl in |- *; trivial.
apply Lookup_Equal.
generalize lin_l0; clear lin_l0; simpl in |- *; intro lin_l0.
 rewrite lin_l0.
 rewrite (app_ass (lin_avl l) ((k, d) :: nil) (lin_avl r0)).
trivial.

apply equiv_del_equiv_equiv_del with (t1 := Avl_Node k d l r0 b0).
apply equiv_del_equal; try assumption.
apply is_below_avl_is_below.
inversion_clear avl_t0; assumption.
inversion_clear avl_t0; assumption.
apply is_above_avl_is_above.
inversion_clear avl_t0; assumption.
inversion_clear avl_t0; assumption.
inversion_clear avl_t0; assumption.
apply equiv_sym; assumption.

clear lin_t0 equiv_t0 avl_t bal_or_shift equiv_del_l0 below_l avl_l lookup_l0.
elim shrunk_dec; clear shrunk_dec.

intros hasnot_shrunk.
left.
inversion_clear avl_t0.
generalize H1; clear H1 H3 H2 H0 H.
inversion_clear hasnot_shrunk.
 rewrite H0; clear H0.
inversion_clear H; simpl in |- *.
 rewrite H0; clear H0.
intros Balanced_l0; inversion_clear Balanced_l0.
 rewrite <- H.
simpl in |- *; trivial.
 rewrite H0.
intros Balanced_l0; inversion_clear Balanced_l0.
 rewrite <- H.
simpl in |- *; trivial.
trivial.

 rewrite H0; clear H0.
intros Balanced_l0; inversion_clear Balanced_l0.
 rewrite <- H0.
simpl in |- *; trivial.

 rewrite H0; clear H0.
simpl in |- *; trivial.

intros has_shrunk.
right.
inversion_clear avl_t0.
generalize H1; clear H H0 H1 H2 H3.
inversion_clear has_shrunk.
 rewrite H0; clear H0.
intros Balanced_l0; inversion_clear Balanced_l0.
 rewrite <- H0.
simpl in |- *; trivial.

 rewrite H0; clear H0.
simpl in |- *; trivial.

(* side premisses (Elim balance_shrunk_right ...) *)
inversion_clear avl_t0; assumption.
apply above_avl_trans with k0.
inversion_clear avl_t0; assumption.
apply lookup_below_less with (Avl_Node kl0 dl0 ll0 rl0 bl0) d.
assumption.
apply is_below_avl_is_below.
inversion_clear avl_t0; assumption.
inversion_clear avl_t0; assumption.

elim bal_or_shift; clear bal_or_shift; intros height_l0.
left.
apply
 hasnot_grown_left__preserves_is_balanced_avl
  with (Avl_Node kl0 dl0 ll0 rl0 bl0).
inversion_clear avl_t0; assumption.
symmetry  in |- *; assumption.
right.
apply
 is_balanced_avl_is_balanced_avl_right_shift_left
  with (Avl_Node kl0 dl0 ll0 rl0 bl0).
inversion_clear avl_t0; assumption.
symmetry  in |- *; assumption.
inversion_clear avl_t0; assumption.


(* ~(Equal key k0) *)
intro notequal.
elim (less_dec key k0).

(* (Less key k0) *)
intro less.
elim (ih_l0 (inv_is_avl_left k0 d0 l0 r0 b0 avl_t0)); clear ih_l0 ih_r0.
intros l lookup_l0 avl_l lin_l0 equiv_del_l0 bal_or_shift.
elim (balance_shrunk_right k0 d0 l r0 b0); try assumption.
intros t avl_t lin_t equiv_t shrunk_dec.
apply Delete_Spec_Intro with t; try assumption.

elim lookup_l0; clear lookup_l0.
intros d lookup_d.
left with d.
apply Lookup_Left; assumption.
intro not_lookup_l0.
right.
unfold not in |- *; intros d lookup_t.
apply (not_lookup_l0 d).
apply (lookup_avl_inv_less key k0 d0 l0 r0 b0 d); assumption.

clear shrunk_dec equiv_t avl_t bal_or_shift equiv_del_l0 lookup_l0.
intros d lookup0.
elim lin_l0 with d; clear lin_l0.
intros l1 l2 lin_l0 lin_l.
apply Lin_Del_Spec_Intro with l1 (l2 ++ (k0, d0) :: lin_avl r0).
simpl in |- *.
 rewrite lin_l0.
 rewrite (app_ass l1 ((key, d) :: l2) ((k0, d0) :: lin_avl r0)).
trivial.
 rewrite lin_t.
simpl in |- *.
 rewrite lin_l.
 rewrite (app_ass l1 l2 ((k0, d0) :: lin_avl r0)); trivial.
apply (lookup_avl_inv_less key k0 d0 l0 r0 b0 d); assumption.

clear shrunk_dec lin_t bal_or_shift lin_l0.
apply equiv_del_equiv_equiv_del with (t1 := Avl_Node k0 d0 l r0 b0);
 try assumption.
apply equiv_del_trans_left; try assumption.
inversion_clear avl_t0.
apply is_above_avl_is_above; assumption.
apply equiv_sym; assumption.

clear lin_t equiv_t avl_t bal_or_shift equiv_del_l0 lookup_l0.
elim shrunk_dec; clear shrunk_dec.

intro hasnot_shrunk.
left.
inversion_clear avl_t0.
generalize H1; clear H H0 H1 H2 H3.
inversion_clear hasnot_shrunk.

 rewrite H0; clear H0.
inversion_clear H; simpl in |- *.
 rewrite H0; clear H0.
intros Balanced_l0; inversion_clear Balanced_l0.
 rewrite H; trivial.
 rewrite H0; clear H0.
intros Balanced_l0; inversion_clear Balanced_l0.
 rewrite H; trivial.
trivial.

 rewrite H0; clear H0.
intros Balanced_l0; inversion_clear Balanced_l0; simpl in |- *.
 rewrite H0; trivial.

 rewrite H0; clear H0.
simpl in |- *; trivial.

intros has_shrunk.
right.
inversion_clear avl_t0.
generalize H1; clear H H0 H1 H2 H3.
inversion_clear has_shrunk.

 rewrite H0; clear H0.
intros Balanced_l0; inversion_clear Balanced_l0.
simpl in |- *.
 rewrite H0; trivial.

 rewrite H0; clear H0.
simpl in |- *; trivial.

(* side premisses (Elim (balance_shrunk_right ...) ) *)
inversion_clear avl_t0.
apply below_below_avl.
apply below_equiv_del_below with l0 key. 
apply is_below_avl_is_below; assumption.
assumption.
inversion_clear avl_t0; assumption.
inversion_clear avl_t0; assumption.
elim bal_or_shift; clear bal_or_shift; intros height_l0.
left.
apply hasnot_grown_left__preserves_is_balanced_avl with l0. 
inversion_clear avl_t0; assumption.
symmetry  in |- *; assumption.
right.
apply is_balanced_is_balanced_right_shift with l0. 
inversion_clear avl_t0; assumption.
assumption.

(* (Less k0 key) *)
intro notless.
generalize (notequal_notless_greater key k0 notequal notless); intro greater.
elim ih_r0; clear ih_r0 ih_l0 notless.
intros r lookup_r0 avl_r lin_r0 equiv_r0 bal_or_shift.
elim (balance_shrunk_left k0 d0 l0 r b0); try assumption.
intros t avl_t lin_t equiv_t shrunk_dec.
apply Delete_Spec_Intro with t; try assumption.

elim lookup_r0; clear lookup_r0.
intros d lookup_d.
left with d.
apply Lookup_Right; assumption.
intro not_lookup_r0.
right.
unfold not in |- *; intros d lookup_t.
apply (not_lookup_r0 d).
apply (lookup_avl_inv_greater key k0 d0 l0 r0 b0 d); assumption.

intros d lookup0.
elim lin_r0 with d; clear lin_r0.
intros l1 l2 lin_r0 lin_r.
apply Lin_Del_Spec_Intro with (lin_avl l0 ++ (k0, d0) :: l1) l2;
 simpl in |- *.
 rewrite (app_ass (lin_avl l0) ((k0, d0) :: l1) ((key, d) :: l2)).
 rewrite lin_r0; trivial.
 rewrite lin_t.
simpl in |- *.
 rewrite (app_ass (lin_avl l0) ((k0, d0) :: l1) l2).
 rewrite lin_r; trivial.
apply (lookup_avl_inv_greater key k0 d0 l0 r0 b0 d); assumption.

apply equiv_del_equiv_equiv_del with (t1 := Avl_Node k0 d0 l0 r b0);
 try assumption.
apply equiv_del_trans_right; try assumption.
inversion_clear avl_t0.
apply is_below_avl_is_below; assumption.
apply equiv_sym; assumption.

clear lin_t equiv_t avl_t bal_or_shift equiv_r0 lookup_r0.
elim shrunk_dec; clear shrunk_dec.

intro hasnot_shrunk.
left.
inversion_clear avl_t0.
generalize H1; clear H H0 H1 H2 H3.
inversion_clear hasnot_shrunk.

 rewrite H0; clear H0.
inversion_clear H; simpl in |- *.
trivial.
trivial.
 rewrite <- H0; clear H0.
intros Balanced_l0; inversion_clear Balanced_l0.
 rewrite H; trivial.
 rewrite H0; clear H0.
simpl in |- *.
trivial.

 rewrite H0; clear H0.
simpl in |- *.
trivial.

intros has_shrunk.
right.
inversion_clear avl_t0.
generalize H1; clear H H0 H1 H2 H3.
inversion_clear has_shrunk.

 rewrite H0; clear H0.
simpl in |- *; trivial.
 rewrite H0; clear H0.
intros Balanced_l0; inversion_clear Balanced_l0.
simpl in |- *.
 rewrite H0; trivial.

(* side premisses (Elim (balance_shrunk_right ...) ) *)
inversion_clear avl_t0; assumption.
inversion_clear avl_t0; assumption.
inversion_clear avl_t0.
apply above_above_avl.
apply above_equiv_del_above with r0 key. 
apply is_above_avl_is_above; assumption.
assumption.
elim bal_or_shift; clear bal_or_shift; intros height_l0.
left.
apply hasnot_grown_right__preserves_is_balanced_avl with r0. 
inversion_clear avl_t0; assumption.
symmetry  in |- *; assumption.
right.
apply Balanced_shrunk_left_balanced_shift with r0. 
inversion_clear avl_t0; assumption.
assumption.

inversion_clear avl_t0; assumption.
Qed.

(************************************************************************)
(************************************************************************)
(************************************************************************)

Inductive AVL : Set :=
    AVL_intro : forall t : avl_tree, is_avl t -> AVL.


Definition AVL_NIL := AVL_intro Avl_Nil Nil_Is_Avl.


Definition LOOKUP (key : Int) (T : AVL) (data : B) :=
  match T with
  | AVL_intro t _ => lookup key t data
  end.


Definition LOOKUP_Dec_Spec (key : Int) (T : AVL) :=
  match T with
  | AVL_intro t _ => lookup_dec_spec key t
  end.

Theorem LOOKUP_DEC : forall (key : Int) (T : AVL), LOOKUP_Dec_Spec key T.
intros key T.
elim T; clear T.
exact (lookup_dec key).
Qed.


(***************************************************************************)

Definition LIN_AVL (T : AVL) := match T with
                                | AVL_intro t _ => lin_avl t
                                end.


(***************************************************************************)

Definition LIN_INS (key : Int) (update : B -> B) (init : B) 
  (T0 T : AVL) :=
  match T0 with
  | AVL_intro t0 _ =>
      match T with
      | AVL_intro t _ => lin_ins_spec key update init t0 t
      end
  end.

Definition EQUIV_INS (key : Int) (update : B -> B) 
  (init : B) (T0 T : AVL) :=
  match T0 with
  | AVL_intro t0 _ =>
      match T with
      | AVL_intro t _ => equiv_ins key update init t0 t
      end
  end.


Definition INSRT_Spec (key : Int) (update : B -> B) 
  (init : B) (T0 : AVL) :=
  match T0 with
  | AVL_intro t0 _ => avl_ins_spec key update init t0
  end.

Theorem INSRT_AVL :
 forall (key : Int) (update : B -> B) (init : B) (T0 : AVL),
 INSRT_Spec key update init T0.
intros key update init T0.
elim T0; clear T0.
exact (insert_avl key update init).
Qed.

(***************************************************************************)


Definition LIN_DEL (key : Int) (d : B) (T0 T : AVL) :=
  match T0 with
  | AVL_intro t0 _ =>
      match T with
      | AVL_intro t _ => lin_del_spec key d t0 t
      end
  end.


Definition EQUIV_DEL (key : Int) (T0 T : AVL) :=
  match T0 with
  | AVL_intro t0 _ => match T with
                      | AVL_intro t _ => equiv_del key t0 t
                      end
  end.


Definition DELETE_Spec (key : Int) (T0 : AVL) :=
  match T0 with
  | AVL_intro t0 _ => delete_spec key t0
  end.


Theorem DELETE_AVL : forall (key : Int) (T0 : AVL), DELETE_Spec key T0.
intros key T0.
elim T0; clear T0.
exact (delete_avl key).
Qed.

End avl_trees.



(* In order to extract a ML program use:  *)

(*
Require Extraction.

Extract Constant Int => int.
Link Int := Int.
Extract Inductive sumbool => bool [ true false ].
Extract Constant equal_dec => "(=)".
Extract Constant less_dec => "(<)".

Write Caml File "avl_trees" [rebalance_left rebalance_right 
                            balance_left balance_right
                            balance_shrunk_left balance_shrunk_right
                            delete_max
                            lookup_dec insert_avl delete_avl lin_avl].
*)


