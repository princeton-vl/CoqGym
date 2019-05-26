From mathcomp Require Import ssreflect ssrnat ssrbool eqtype.

(* Formalization inspired from
   https://www.cs.princeton.edu/~appel/papers/redblack.pdf *)

(* An implementation of Red-Black Trees (insert only) *)

(* begin tree *)
Inductive color := Red | Black.
Inductive tree := Leaf : tree | Node : color -> tree -> nat -> tree -> tree.
(* end tree *)

(* insertion *)

Definition balance rb t1 k t2 :=
  match rb with
    | Red => Node Red t1 k t2
    | _ =>
      match t1 with
        | Node Red (Node Red a x b) y c =>
          Node Red (Node Black a x b) y (Node Black c k t2)
        | Node Red a x (Node Red b y c) =>
          Node Red (Node Black a x b) y (Node Black c k t2)
        | a => match t2 with
                 | Node Red (Node Red b y c) z d =>
                   Node Red (Node Black t1 k b) y (Node Black c z d)
                 | Node Red b y (Node Red c z d) =>
                   Node Red (Node Black t1 k b) y (Node Black c z d)
                 | _ => Node Black t1 k t2
               end
      end
  end.

Fixpoint ins x s :=
  match s with
    | Leaf => Node Red Leaf x Leaf
    | Node c a y b => if x < y then balance c (ins x a) y b
                      else if y < x then balance c a y (ins x b)
                           else Node c a x b
  end.

Definition makeBlack t :=
  match t with
    | Leaf => Leaf
    | Node _ a x b => Node Black a x b
  end.

Definition insert x s := makeBlack (ins x s).


(* Red-Black Tree invariant: declarative definition *)
(* begin is_redblack *)
Inductive is_redblack' : tree -> color -> nat -> Prop :=
| IsRB_leaf: forall c, is_redblack' Leaf c 0
| IsRB_r: forall n tl tr h, is_redblack' tl Red h -> is_redblack' tr Red h ->
                            is_redblack' (Node Red tl n tr) Black h
| IsRB_b: forall c n tl tr h, is_redblack' tl Black h -> is_redblack' tr Black h ->
                              is_redblack' (Node Black tl n tr) c (S h).
Definition is_redblack (t:tree) : Prop := exists h, is_redblack' t Red h.
(* end is_redblack *)

(* begin insert_preserves_redblack *)
Definition insert_preserves_redblack : Prop :=
  forall x s, is_redblack s -> is_redblack (insert x s).
(* end insert_preserves_redblack *)

(* Declarative Proposition *)
Lemma insert_preserves_redblack_correct : insert_preserves_redblack.
Abort. (* if this wasn't about testing, we would just prove this *)
