Set Implicit Arguments.
Unset Automatic Introduction.

Require Import Setoid.
Require Import util.
Require vec.
Require List.
Require Vector.

Section contents.

  Variable T: Set.

  Inductive L: Set := one: T -> L | cons: T -> L -> L.

  Fixpoint to_plain (l: L): List.list T :=
    match l with one x => List.cons x List.nil | cons x y => List.cons x (to_plain y) end.

  Coercion to_plain: L >-> List.list.

  Fixpoint from_plain (x: T) (l: List.list T): L:=
    match l with
    | List.nil => one x
    | List.cons h t => cons x (from_plain h t)
    end.

  Lemma round_trip l x: (to_plain (from_plain x l)) = List.cons x l.
  Proof with auto. induction l... simpl. rewrite IHl... Qed.

  Fixpoint app (a b: L) {struct a}: L :=
    match a with
    | one x => cons x b
    | cons x y => cons x (app y b)
    end.

  Variable l: L.

  Definition head := match l with one x => x | cons x _ => x end.
  Definition tail := match l with one _ => List.nil | cons _ x => to_plain x end.

  Lemma head_in_self: List.In head l.
  Proof with auto. unfold head. destruct l; left... Qed.

  Lemma In_sound x: List.In x l -> (head = x \/ List.In x tail).
  Proof with auto. unfold head. unfold tail. destruct l... Qed.

  Lemma In_cons_head (x: T) y: List.In x (cons x y). left; reflexivity. Qed.
  Lemma In_one (x: T): List.In x (one x). left; reflexivity. Qed.

  Lemma coerced_cons_eq (h: T): List.cons h l = cons h l.
  Proof. auto. Qed.

End contents.

Definition map (A B: Set) (f: A -> B): L A -> L B :=
  fix r (l: L A): L B :=
    match l with
    | one x => one (f x)
    | cons h t => cons (f h) (r t)
    end.

Lemma plain_map (A B: Set) (f: A -> B) (l: L A): to_plain (map f l) = List.map f (to_plain l).
Proof with auto.
  induction l...
  simpl.
  rewrite IHl...
Qed.

Add Parametric Morphism (A B: Set): (@map A B)
  with signature (@ext_eq A B) ==> (@ext_eq (L A) (L B))
  as ne_list_map_ext_eq_morph.
Proof with try reflexivity.
  unfold ext_eq.
  intros.
  induction x0; simpl; rewrite H...
  rewrite IHx0...
Qed.

Lemma map_ext (T U: Set) (f g: T -> U): ext_eq f g -> forall l, map f l = map g l.
Proof. intros T U f g e. fold (ext_eq (map f) (map g)). rewrite e. reflexivity. Qed.

Lemma In_map_inv (T U: Set) (f: T -> U) (l: L T) (y: U): List.In y (map f l) -> exists x, f x = y /\ List.In x l.
Proof. induction l; simpl; intros; destruct H; firstorder. Qed.

Lemma length_ne_0 (A: Set) (l: L A): List.length l <> 0.
Proof with auto with arith. destruct l; simpl... Qed.

Lemma map_length (A B: Set) (f: A -> B) (l: L A): List.length (map f l) = List.length l.
Proof with auto. induction l... simpl. rewrite IHl... Qed.

Lemma map_map (A B C: Set) (g: A -> B) (f: B -> C) (l: L A):
  map f (map g l) = map (f ∘ g) l.
Proof with auto. induction l... simpl. rewrite IHl... Qed.

Lemma In_round_tripped_head (T: Set) (x: T) l: List.In x (from_plain x l).
Proof with auto. intros. rewrite round_trip. left... Qed.

Hint Immediate In_one.
Hint Immediate In_cons_head.
Hint Immediate head_in_self.
Hint Immediate In_round_tripped_head.

Fixpoint from_vec (A: Set) n: Vector.t A (S n) -> L A :=
  match n return Vector.t A (S n) -> L A with
  | 0 => fun v => one (vec.head v)
  | _ => fun v => cons (vec.head v) (from_vec (vec.tail v))
  end.

Lemma from_vec_to_plain (A: Set) n (v: Vector.t A (S n)): to_plain (from_vec v) = vec.to_list v.
Proof with reflexivity.
  induction n; intros.
    rewrite (vec.eq_cons v).
    simpl.
    rewrite (vec.eq_nil (vec.tail v))...
  rewrite (vec.eq_cons v).
  simpl.
  rewrite IHn...
Qed.
