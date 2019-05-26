From QuickChick Require Import QuickChick.

Require Import List. Import ListNotations.
Require Import String. Open Scope string.

Inductive Tree :=
| Leaf : Tree
| Node : nat -> Tree -> Tree -> Tree.

Derive (Arbitrary, Show) for Tree. 

Inductive bst : nat -> nat -> Tree -> Prop :=
| bst_leaf : forall lo hi, bst lo hi Leaf
| bst_node : forall lo hi x l r,
    le (S lo) x ->  le (S x) hi ->
    bst lo x l -> bst x hi r ->
    bst lo hi (Node x l r).

Derive ArbitrarySizedSuchThat for (fun x => le y x).
Derive ArbitrarySizedSuchThat for (fun t => bst lo hi t).

Derive DecOpt for (bst lo hi t).

Eval simpl in (@decOpt (bst 0 2 (Node 1 Leaf (Node 2 Leaf Leaf))) _ 40).

Fixpoint is_bst (lo hi : nat) (t : Tree) :=
  match t with
  | Leaf => true
  | Node x l r =>
    andb ((lo < x /\ x < hi) ?)
         (andb (is_bst lo x l)
               (is_bst x hi r))
  end.

Definition bst_checker_prop :=
  forAllMaybe (genST (fun t => bst 0 17 t))
              (fun t => implication (is_bst 0 17 t)
                        (let d := @decOpt (bst 1 5 t) _ 40 in
                         let f := is_bst 1 5 t in
                         whenFail (show (d,f))
                                  ((@decOpt (bst 1 5 t) _ 40 = Some (is_bst 1 5 t))?))).

QuickChick bst_checker_prop. 



