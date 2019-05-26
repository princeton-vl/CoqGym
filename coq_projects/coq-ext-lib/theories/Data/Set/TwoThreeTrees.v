Require Import ExtLib.Structures.Monads.
Require Import ExtLib.Data.Monads.OptionMonad.
Require Import ExtLib.Programming.Extras.
Import FunNotation.

Set Implicit Arguments.
Set Maximal Implicit Insertion.

Import MonadNotation.
Import MonadPlusNotation.
Open Scope monad_scope.

Section tree.
  Variable E:Type.
  Variable comp : E -> E -> comparison.

  (* a two-three tree *)
  Inductive tree :=
  (* Null_t = _ *)
  | Null_t : tree
  (*                [a]
   * Two_t X a Y =  / \
   *               X   Y
   * Invariant: x in X => x < a; y in Y => y > a
   *)
  | Two_t : tree -> E -> tree -> tree
  (*                       [a][b]
   * Three_t X a Y b Z =  /  |  \
   *                     X   Y   Z
   * Invariant: x in X => x < a; y in Y => a < y < b; z in Z => z > b
   *)
  | Three_t : tree -> E -> tree -> E -> tree -> tree
  .

  Fixpoint height_t (t:tree) : nat :=
  match t with
  | Null_t => O
  | Two_t tl _ tr => max (height_t tl) (height_t tr)
  | Three_t tl _ tm _ tr => max (max (height_t tl) (height_t tm)) (height_t tr)
  end.



  (* a context of a two-three tree. this is the type of taking a tree and
   * replacing a sub-tree with a hole.
   *)
  Inductive context :=
  (* Top_c = _ *)
  | Top_c : context
  (*                         C
   * TwoLeftHole_c a Y C =   |
   *                        [a]
   *                        / \
   *                       ?   Y
   *)
  | TwoLeftHole_c : E -> tree -> context -> context
  (*                          C
   * TwoRightHole_c X a C =   |
   *                         [a]
   *                         / \
   *                        X   ?
   *)
  | TwoRightHole_c : tree -> E -> context -> context
  (*                             C
   * ThreeLeftHole a Y b Z C =   |
   *                           [a][b]
   *                          /  |  \
   *                         ?   Y   Z
   *)
  | ThreeLeftHole_c : E -> tree -> E -> tree -> context -> context
  (*                               C
   * ThreeMiddleHole X a b Z C =   |
   *                             [a][b]
   *                            /  |  \
   *                           X   ?   Z
   *)
  | ThreeMiddleHole_c : tree -> E -> E -> tree -> context -> context
  (*                                C
   * ThreeRightHole_c X a Y b C =   |
   *                              [a][b]
   *                             /  |  \
   *                            X   Y   ?
   *)
  | ThreeRightHole_c : tree -> E -> tree -> E -> context -> context
  .

  (* zip takes a context (which can be thought of as a tree with a hole), and a
   * subtree, and fills the hole with the subtree
   *)
  Fixpoint zip (t:tree) (c:context) : tree :=
  match c with
  | Top_c => t
  | TwoLeftHole_c em tr c' => zip (Two_t t em tr) c'
  | TwoRightHole_c tl em c' => zip (Two_t tl em t) c'
  | ThreeLeftHole_c el em er tr c' => zip (Three_t t el em er tr) c'
  | ThreeMiddleHole_c tl el er tr c' => zip (Three_t tl el t er tr) c'
  | ThreeRightHole_c tl el em er c' => zip (Three_t tl el em er t) c'
  end.

  Fixpoint fuse (c1:context) (c2:context) : context :=
  match c1 with
  | Top_c => c2
  | TwoLeftHole_c em tr c1' => TwoLeftHole_c em tr (fuse c1' c2)
  | TwoRightHole_c tl em c1' => TwoRightHole_c tl em (fuse c1' c2)
  | ThreeLeftHole_c el em er tr c1' => ThreeLeftHole_c el em er tr (fuse c1' c2)
  | ThreeMiddleHole_c tl el er tr c1' => ThreeMiddleHole_c tl el er tr (fuse c1' c2)
  | ThreeRightHole_c tl el em er c1' => ThreeRightHole_c tl el em er (fuse c1' c2)
  end.

  Inductive location :=
  (*                     C
   * TwoHole_l X Y C =   |
   *                    [?]
   *                    / \
   *                   X   Y
   *)
  | TwoHole_l : tree -> tree -> context -> location
  (*                         C
   * TwoHole_l X Y b Z C =   |
   *                       [?][b]
   *                       /  |  \
   *                      X   Y   Z
   *)
  | ThreeLeftHole_l : tree -> tree -> E -> tree -> context -> location
  (*                         C
   * TwoHole_l X a Y Z C =   |
   *                       [a][?]
   *                       /  |  \
   *                      X   Y   Z
   *)
  | ThreeRightHole_l : tree -> E -> tree -> tree -> context -> location
  .

  Definition fillLocation (e:E) (l:location) : tree :=
  match l with
  | TwoHole_l tl tr c => zip (Two_t tl e tr) c
  | ThreeLeftHole_l tl tm vr tr c => zip (Three_t tl e tm vr tr) c
  | ThreeRightHole_l tl el tm tr c => zip (Three_t tl el tm e tr) c
  end.

  Fixpoint locate (e:E) (t:tree) (c:context) : context + E * location :=
  match t with
  | Null_t => inl c
  | Two_t tl em tr =>
      match comp e em with
      | Lt => locate e tl $ TwoLeftHole_c em tr c
      | Eq => inr (em, TwoHole_l tl tr c)
      | Gt => locate e tr $ TwoRightHole_c tl em c
      end
  | Three_t tl el tm er tr =>
      match comp e el, comp e er with
      | Lt, _ => locate e tl $ ThreeLeftHole_c el tm er tr c
      | Eq, _ => inr (el, ThreeLeftHole_l tl tm er tr c)
      | Gt, Lt => locate e tm $ ThreeMiddleHole_c tl el er tr c
      | _, Eq => inr (er, ThreeRightHole_l tl el tm tr c)
      | _, Gt => locate e tr $ ThreeRightHole_c tl el tm er c
      end
  end.

  Fixpoint locateGreatest (t:tree) (c:context)
    : option (E * (context + E * context)) :=
  match t with
  | Null_t => None
  | Two_t tl em tr => liftM sum_tot $
      locateGreatest tr (TwoRightHole_c tl em c)
      <+>
      ret (em, inl c)
  | Three_t tl el tm er tr => liftM sum_tot $
      locateGreatest tr (ThreeRightHole_c tl el tm er c)
      <+>
      ret (er, inr (el, c))
  end.

  Definition single e := Two_t Null_t e Null_t.

  (* if insertion results in a subtree which is too tall, propegate it up into
   * its context.
   *)
  Fixpoint insertUp (tet:tree * E * tree) (c:context) : tree :=
  let '(tl,em,tr) := tet in
  match c with
  (*     _
   *     |
   *    [em]    =>   [em]
   *   //  \\        /  \
   *  tl    tr      tl   tr
   *)
  | Top_c => Two_t tl em tr
  (*        c'              c'
   *        |               |
   *      [em']    =>    [em][em']
   *      /   \          /  |   \
   *    [em]   tr'     tl  tr   tr'
   *   // \\
   *  tl   tr
   *)
  | TwoLeftHole_c em' tr' c' =>
      zip (Three_t tl em tr em' tr') c'
  (*     c'                c'
   *     |                 |
   *   [em']      =>    [em'][em]
   *   /   \            /  |   \
   *  tl'  [em]       tl'  tl   tr
   *      // \\
   *     tl   tr
   *)
  | TwoRightHole_c tl' em' c' =>
      zip (Three_t  tl' em' tl em tr ) c'
  (*         c'                  c'
   *         |                   |
   *      [el][er]     =>      [el]
   *      /  |   \            //  \\
   *    [em] tm   tr'       [em]   [er]
   *   // \\                /  \   /  \
   *  tl   tr              tl  tr tm  tr'
   *)
  | ThreeLeftHole_c el tm er tr' c' =>
      insertUp (Two_t tl em tr, el, Two_t tm er tr') c'
  (*      c'                 c'
   *      |                  |
   *   [el][er]     =>      [em]
   *   /   |  \            //  \\
   *  tl' [em] tr'       [el]   [er]
   *     // \\           /  \   /  \
   *    tl   tr         tl' tl tr  tr'
   *)
  | ThreeMiddleHole_c tl' el er tr' c' =>
      insertUp (Two_t tl' el tl, em, Two_t tr er tr') c'
  (*      c'                   c'
   *      |                    |
   *   [el][er]       =>      [er]
   *   /  |   \              //  \\
   *  tl' tm  [em]         [el]   [em]
   *          // \\        /  \   /  \
   *         tl   tr      tl' tm tl  tr
   *)
  | ThreeRightHole_c tl' el tm er c' =>
      insertUp (Two_t tl' el tm, er, Two_t tl em tr) c'
  end.

  (* insert an element into the two-three tree *)
  Definition insert (e:E) (t:tree) : tree :=
  match locate e t Top_c with
  | inl c => insertUp (Null_t, e, Null_t) c
  | inr (_, l) => fillLocation e l
  end.

  (* if remove results in a tree which is too short, propegate the gap into the
   * context *)
  Fixpoint removeUp (t:tree) (c:context) : tree :=
  match c with
  (*  _
   *  ||
   *  e  =>  e
   *)
  | Top_c => t
  (*    c'                    c'
   *    |                     |
   *   [em]           =>     [el']
   *  //  \                  /   \
   *  t  [el'][er']       [em]   [er']
   *     /   |   \        /  \    /  \
   *    tl'  tm'  tr'    t   tl' tm' tr'
   *)
  | TwoLeftHole_c em (Three_t tl' el' tm' er' tr') c' =>
      zip (Two_t (Two_t t em tl') el' (Two_t tm' er' tr')) c'
  (*    c'                c'
   *    |                 ||
   *   [em]       =>   [em][em']
   *  //  \            /   |   \
   *  t   [em']       t    tl'  tr'
   *     /    \
   *    tl'   tr'
   *)
  | TwoLeftHole_c em (Two_t tl' em' tr') c' =>
      removeUp (Three_t t em tl' em' tr') c'
  (*          c'             c'
   *          |              |
   *         [em]   =>      [er']
   *        /   \\          /   \
   *  [el'][er']  t     [el']   [em]
   *   /   |   \        /  \    /  \
   *  tl'  tm'  tr'    tl' tm' tr'  t
   *)
  | TwoRightHole_c (Three_t tl' el' tm' er' tr') em c' =>
      zip (Two_t (Two_t tl' el' tm') er' (Two_t tr' em t)) c'
  (*        c'            c'
   *        |             ||
   *       [em]   =>   [em'][em]
   *       /  \\       /   |   \
   *    [em']  t      tl'  tr'  t
   *   /    \
   *  tl'   tr'
   *)
  | TwoRightHole_c (Two_t tl' em' tr') em c' =>
      removeUp (Three_t tl' em' tr' em t) c'
  (*         c'                      c'
   *         |                       |
   *      [el][er]      =>        [el][er]
   *   //    |     \             /   |    \
   *  t  [el'][er'] tr       [el']  [er']  tr
   *    /    |    \          /  \    /  \
   *   tl'   tm'  tr'       t   tl' tm' tr'
   *)
  | ThreeLeftHole_c el (Three_t tl' el' tm' er' tr') er tr c' =>
      zip (Three_t (Two_t t el' tl') el (Two_t tm' er' tr') er tr) c'
  (*         c'                       c'
   *         |                        |
   *      [el][er]      =>           [er]
   *   //    |     \                /    \
   *  t    [em']    tr        [el][em']   tr
   *       /   \             /    |    \
   *     tl'   tr'          t    tl'    tr'
   *)
  | ThreeLeftHole_c el (Two_t tl' em' tr') er tr c' =>
      zip (Two_t (Three_t t el tl' em' tr') er tr) c'
  (*                c'                        c'
   *                |                         |
   *             [el][er]      =>         [er'][er]
   *           /     ||   \              /    |    \
   *     [el'][er']  t     tr        [el']   [el]   tr
   *    /    |    \                  /  \    /  \
   *  tl'   tm'   tr'              tl'  tm'  tr' t
   *)
  | ThreeMiddleHole_c (Three_t tl' el' tm' er' tr') el er tr c' =>
      zip (Three_t (Two_t tl' el' tm') er' (Two_t tr' el t) er tr) c'
  (*        c'                            c'
   *        |                             |
   *     [el][er]             =>      [el][el']
   *   /    ||   \                  /    |     \
   *  tl    t  [el'][er']         tl   [er]     [er']
   *           /    |    \              /  \     /  \
   *         tl'   tm'   tr'           t   tl'  tm'  tr'
   *)
  | ThreeMiddleHole_c tl el er (Three_t tl' el' tm' er' tr') c' =>
      zip (Three_t tl el (Two_t t er tl') el' (Two_t tm' er' tr')) c'
  (*            c'                        c'
   *            |                         |
   *         [el][er]      =>           [er]
   *       /     ||   \                /   \
   *    [em']    t     tr        [em'][el]  tr
   *    /  \                     /   |    \
   *  tl'  tr'                 tl'  tr'    t
   *)
  | ThreeMiddleHole_c (Two_t tl' em' tr') el er tr c' =>
      zip (Two_t (Three_t tl' em' tr' el t) er tr) c'
  (*        c'                   c'
   *        |                    |
   *     [el][er]        =>    [el]
   *   /    ||   \             /   \
   *  tl    t   [em']        tl   [er][em']
   *            /   \            /    |    \
   *          tl'   tr'         t     tl'   tr'
   *)
  | ThreeMiddleHole_c tl el er (Two_t tl' em' tr') c' =>
      zip (Two_t tl el (Three_t t er tl' em' tr')) c'
  (*         c'                  c'
   *         |                   |
   *      [el][er]      =>     [el][er']
   *   /      |    \\         /   |     \
   *  tl [el'][er']  t      tl  [el']   [er]
   *     /   |     \           /   \    /   \
   *   tl'   tm'    tr'      tl'   tm' tr'   t
   *)
  | ThreeRightHole_c tl el (Three_t tl' el' tm' er' tr') er c' =>
      zip (Three_t tl el (Two_t tl' el' tm') er' (Two_t tr' er t)) c'
  (*         c'                  c'
   *         |                   |
   *      [el][er]      =>      [el]
   *     /    |   \\            /   \
   *    tl  [em']  t          tl  [em'][er]
   *        /   \                  /   |   \
   *      tl'    tr'              tl'  tr   t
   *)
  | ThreeRightHole_c tl el (Two_t tl' em' tr') er c' =>
      zip (Two_t tl el (Three_t tl' em' tr' er t)) c'
  | TwoLeftHole_c _ Null_t _ => Null_t (* not wf *)
  | TwoRightHole_c Null_t _ _ => Null_t (* not wf *)
  | ThreeLeftHole_c _ Null_t _ _ _ => Null_t (* not wf *)
  | ThreeMiddleHole_c Null_t _ _ _ _ => Null_t (* not wf *)
  | ThreeRightHole_c _ _ Null_t _ _ => Null_t (* not wf *)
  end.


  Definition remove (e:E) (t:tree) : tree :=
  match locate e t Top_c with
  (* element doesn't exist *)
  | inl _ => t
  (* element found at location [loc] *)
  | inr (_, loc) =>
      match loc with
      (* element found at a two-node *)
      | TwoHole_l tl tr c =>
          let mkContext g c' := TwoLeftHole_c g tr c' in
          match locateGreatest tl Top_c with
          (* no children: turn into a hole and propagate *)
          | None => removeUp Null_t c
          (* greatest leaf is a two-node: replace it with a hole and propagate *)
          | Some (g, inl c') => removeUp Null_t $ fuse (mkContext g c') c
          (* greatest leaf is a three-node: turn it into a two-node *)
          | Some (g, inr (el, c')) => zip (single el) $ fuse (mkContext g c') c
          end
      (* element found on left side of three-node *)
      | ThreeLeftHole_l tl tm er tr c =>
          let mkContext g c' := ThreeLeftHole_c g tm er tr c' in
          match locateGreatest tl Top_c with
          (* no children: turn into a two-node *)
          | None => zip (single er) c
          (* greatest leaf is a two-node: replace it with a hole and propagate *)
          | Some (g, inl c') => removeUp Null_t $ fuse (mkContext g c') c
          (* greatest leaf is a three-node: turn it into a two-node *)
          | Some (g, inr (el, c')) => zip (single el) $ fuse (mkContext g c') c
          end
      (* element found on right side of three-node *)
      | ThreeRightHole_l tl el tm tr c =>
          let mkContext g c' := ThreeMiddleHole_c tl el g tr c' in
          match locateGreatest tm Top_c with
          (* no children: turn into a two-node *)
          | None => zip (single el) c
          (* greatest leaf is a two-node: replace it with a hole and propagate *)
          | Some (g, inl c') => removeUp Null_t $ fuse (mkContext g c') c
          (* greatest leaf is a three-node: turn it into a two-node *)
          | Some (g, inr (el, c')) => zip (single el) $ fuse (mkContext g c') c
          end
      end
  end.

End tree.
Arguments Null_t {E}.


(*
Section treeWfP.
  Context {E:Type} {TO:TotalOrder E} {TOP:TotalOrderP E}.
  Context {EP:EquivP E} {POEP:PreOrderEquivP _ EP}.

  Inductive tree_wf : tree E -> nat -> EtndTopBot E -> EtndTopBot E -> Prop :=
  | NullTreeWf : forall eLL eRR, tree_wf Null_t O eLL eRR
  | TwoTreeWf : forall tl em tr h eLL eRR,
         eLL << IncEtndTopBot em
      -> IncEtndTopBot em << eRR
      -> tree_wf tl h eLL (IncEtndTopBot em)
      -> tree_wf tr h (IncEtndTopBot em) eRR
      -> tree_wf (Two_t tl em tr) (S h) eLL eRR
  | ThreeTreWf : forall tl el tm er tr eLL eRR h,
         eLL << IncEtndTopBot el
      -> el << er
      -> IncEtndTopBot er << eRR
      -> tree_wf tl h eLL (IncEtndTopBot el)
      -> tree_wf tm h (IncEtndTopBot el) (IncEtndTopBot er)
      -> tree_wf tr h (IncEtndTopBot er) eRR
      -> tree_wf (Three_t tl el tm er tr) (S h) eLL eRR
  .

  Inductive tree_in : E -> tree E -> Prop :=
  | TwoTreeIn : forall e tl em tr,
         e ~= em
      \/ tree_in e tl
      \/ tree_in e tr
      -> tree_in e (Two_t tl em tr)
  | ThreeTreeIn : forall e tl el tm er tr,
         e ~= el
      \/ e ~= er
      \/ tree_in e tl
      \/ tree_in e tm
      \/ tree_in e tr
      -> tree_in e (Three_t tl el tm er tr)
  .

  (*
  Lemma swapTwoWf : forall tl em tr h eLL eRR em',
       tree_wf (Two_t tl em tr) h eLL eRR
    -> em ~= em'
    -> tree_wf (Two_t tl em' tr) h eLL eRR.
  Proof. intros ; induction h.
  inversion H.
  inversion H ; subst ; clear H. constructor. repeat (ohsnap ; girlforeal).
  unfold ltP in H5. destruct eLL ; repeat (ohsnap ; girlforeal).
  ...
  *)

End treeWfP.


(*
  Definition context_wf (c:context) (sth:nat) (sel:E+bool) (ser:E+bool) (th:nat) (eLL:E+bool) (eRR:E+bool) : Prop :=
  forall t:tree, tree_wf t sth sel ser -> tree_wf (zip t c) th eLL eRR.

  Lemma twoLeftHoleZipWf : forall tl em tr c h eLL eRR,
  tree_wf (zip (Two_t tl em tr) c) h eLL eRR -> tree_wf (zip tl (TwoLeftHole_c em tr c)) h eLL eRR.
  Proof. intros. induction tl ; intros ; simpl ; auto. Qed. Hint Immediate twoLeftHoleZipWf : twoThreeDb.
  Lemma twoRightHoleZipWf : forall tl em tr c h eLL eRR,
  tree_wf (zip (Two_t tl em tr) c) h eLL eRR -> tree_wf (zip tr (TwoRightHole_c tl em c)) h eLL eRR.
  Proof. intros. induction tl ; intros ; simpl ; auto. Qed. Hint Immediate twoRightHoleZipWf : twoThreeDb.
  Lemma threeLeftHoleZipWf : forall tl el tm er tr c h eLL eRR,
  tree_wf (zip (Three_t tl el tm er tr) c) h eLL eRR-> tree_wf (zip tl (ThreeLeftHole_c el tm er tr c)) h eLL eRR.
  Proof. intros. induction tl ; intros ; simpl ; auto. Qed. Hint Immediate threeLeftHoleZipWf : twoThreeDb.
  Lemma threeMiddleHoleZipWf : forall tl el tm er tr c h eLL eRR,
  tree_wf (zip (Three_t tl el tm er tr) c) h eLL eRR -> tree_wf (zip tm (ThreeMiddleHole_c tl el er tr c)) h eLL eRR.
  Proof. intros. induction tl ; intros ; simpl ; auto. Qed. Hint Immediate threeMiddleHoleZipWf : twoThreeDb.
  Lemma threeRightHoleZipWf : forall tl el tm er tr c h eLL eRR,
  tree_wf (zip (Three_t tl el tm er tr) c) h eLL eRR -> tree_wf (zip tr (ThreeRightHole_c tl el tm er c)) h eLL eRR.
  Proof. intros. induction tl ; intros ; simpl ; auto. Qed. Hint Immediate threeRightHoleZipWf : twoThreeDb.

  Definition location_wf (l:location) h eLL eRR : Prop := forall e:E, tree_wf (fillLocation e l) h eLL eRR.

  Lemma zipLocationWf : forall tl em tr c, tree_wf (zip (Two_t tl em tr) c) -> location_wf (TwoHole_l tl tr c).
  Proof. intros. unfold location_wf. intros. simpl.

    exists em. auto. Qed. Hint Immediate zipLocationWf : twoThreeDb.

  Lemma locate_wf : forall e t c, tree_wf (zip t c) -> match locate e t c with inl c => tree_wf (zip Null_t c) | inr (_,l) => location_wf l end.
  Proof. intros. gd c. gd e.
  induction t ; intros ; simpl ; auto. destruct (compareo e0 e).
  pose (twoLeftHoleZipWf _ _ _ _ H). specialize (IHt1 e0 _ t). apply IHt1.
  eauto with twoThreeDb.
  pose (twoRightHoleZipWf _ _ _ _ H). specialize (IHt2 e0 _ t). apply IHt2.

  Lemma single_wf : forall e, tree_wf (single e). Proof. intros. simpl. auto. Qed.

  Definition insert_wf : forall e t, tree_wf t -> tree_wf (insert e t).
  Proof. intros.
  destruct t. simpl. auto.
  unfold insert. simpl.
  destruct (compareo e e0).
  unfold insert.
  destruct (locate e t Top_c). simpl.
  *)

  *)
