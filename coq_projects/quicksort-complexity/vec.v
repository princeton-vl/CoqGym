Global Set Automatic Coercions Import.
Set Implicit Arguments.
Unset Standard Proposition Elimination Names.

(* Intended for use without Import. *)

Require Import nat_below.
Require Import util.
Require Import list_utils.
Require Import Le.
Require Import Plus.
Require Import Lt.
Require Import arith_lems.
Require Vector.
Require Import Relations.
Require List.
Require Import Omega.

Arguments Vector.cons [A] _ [n].
Arguments Vector.nil [A].


(* eliminators/inversion *)

Definition head A n (v: Vector.t A (S n)): A :=
  match v with
  | Vector.nil => I | Vector.cons h _ _ => h
  end.

Definition tail n A (v: Vector.t A (S n)): Vector.t A n :=
  match v with
  | Vector.nil => I | Vector.cons _ _ t => t
  end.

Lemma eq_nil A (v: Vector.t A 0): v = Vector.nil.
Proof.
  cut (forall n (v: Vector.t A n), match n return Vector.t A n -> Prop with 0 => fun v => v = Vector.nil | _ => fun _ => True end v).
    intros.
    apply (H 0 v).
  clear v; destruct v; auto.
Qed.

Lemma eq_cons A n (v: Vector.t A (S n)): v = Vector.cons (head v) (tail v).
Proof.
  cut (forall n (v: Vector.t A n),
      match n return Vector.t A n -> Prop with
      | 0 => fun _ => True
      | S m' => fun w => w = Vector.cons (head w) (tail w)
      end v).
    intros.
    apply (H (S n) v).
  clear v; destruct v; auto.
Qed.

Lemma Vcons_eq A (h h': A) n (t t': Vector.t A n): h = h' -> t = t' -> Vector.cons h t = Vector.cons h' t'.
Proof. intros. subst. reflexivity. Qed.

Lemma Vcons_eq_inv A (h h': A) n (t t': Vector.t A n): Vector.cons h t = Vector.cons h' t' -> h = h' /\ t = t'.
Proof with auto.
  intros.
  split...
    replace h with (head (Vector.cons h t))...
    replace h' with (head (Vector.cons h' t'))...
    rewrite H...
  replace t with (tail (Vector.cons h t))...
  replace t' with (tail (Vector.cons h' t'))...
  rewrite H...
Qed.

(* conversion to/from list *)

Fixpoint to_list X (n: nat) (v: Vector.t X n) {struct v}: List.list X :=
  match v with
  | Vector.nil => List.nil | Vector.cons x _ v' => List.cons x (to_list v')
  end.

Fixpoint from_list A (l: List.list A): Vector.t A (List.length l) :=
  match l return Vector.t A (List.length l) with
  | List.nil => Vector.nil | List.cons h t => Vector.cons h (from_list t)
  end.

Coercion to_list: Vector.t >-> List.list.
Coercion from_list: List.list >-> Vector.t.

Lemma list_round_trip A (l: List.list A): to_list (from_list l) = l.
Proof with try reflexivity. induction l... simpl. rewrite IHl... Qed.

Lemma vec_round_trip (X T: Set) (n : nat) (v : Vector.t X n) (f: forall n, Vector.t X n -> T):
  (f _ (from_list (to_list v))) = f _ v.
Proof with auto.
  revert f.
  induction v...
  intros.
  simpl.
  apply (IHv (fun (m: nat) (w: Vector.t X m) => f (S m) (Vector.cons h w))).
Qed.

Lemma eq_as_lists X n (x y: Vector.t X n): to_list x = to_list y -> x = y.
Proof with auto.
  induction n; intros.
    rewrite (eq_nil x), (eq_nil y)...
  rewrite (eq_cons x), (eq_cons y) in *...
  inversion H.
  rewrite (IHn (tail x) (tail y))...
Qed.

Lemma eq_list A (l: List.list A) (v: Vector.t A (List.length l)): from_list l = v -> l = to_list v.
Proof with auto.
  induction l; simpl; intros.
    rewrite (eq_nil v)...
  rewrite <- H...
  simpl.
  rewrite list_round_trip...
Qed.

(* simultaneous induction over two vectors *)

Lemma double_rect A B (P: forall n, Vector.t A n -> Vector.t B n -> Prop):
  P 0 Vector.nil Vector.nil ->
  (forall n (v: Vector.t A n) (w: Vector.t B n) (x: A) (y: B), P n v w -> P (S n) (Vector.cons x v) (Vector.cons y w)) ->
  forall n (v: Vector.t A n) (w: Vector.t B n), P n v w.
Proof.
  induction n; intros.
    rewrite (eq_nil v). rewrite (eq_nil w). auto.
  rewrite (eq_cons v). rewrite (eq_cons w). auto.
Qed.

(* misc *)

Lemma length A n (l: Vector.t A n): List.length l = n.
Proof with auto. induction l... simpl. apply eq_S... Qed.

Fixpoint app A n: Vector.t A n -> forall m, Vector.t A m -> Vector.t A (n + m) :=
  match n return Vector.t A n -> forall m, Vector.t A m -> Vector.t A (n + m) with
  | 0 => fun _ _ w => w
  | S n' => fun v _ w => Vector.cons (head v) (app (tail v) w)
  end.

(* vmap *)

Fixpoint map X Y (f: X -> Y) (n: nat) (v: Vector.t X n): Vector.t Y n :=
  match v with
  | Vector.nil => @Vector.nil Y
  | Vector.cons h _ t => Vector.cons (f h) (map f t)
  end.

(*Fixpoint map X Y (f: X -> Y) (n: nat): Vector.t X n -> Vector.t Y n :=
  match n with
  | 0 => fun _ => Vector.nil Y
  | S n' => fun v => Vector.cons (f (head v)) (map f (tail v))
  end.*)

Lemma map_map X Y Z (f: X -> Y) (g: Y -> Z) (n: nat) (v: Vector.t X n):
  map g (map f v) = map (g ∘ f) v.
Proof with auto.
  induction v...
  simpl.
  rewrite IHv...
Qed.

Lemma map_ext X Y (f g: X -> Y) (e: ext_eq f g) (n: nat) (v: Vector.t X n):
  map f v = map g v.
Proof with auto.
  induction v...
  simpl.
  rewrite IHv.
  rewrite (e h)...
Qed. (* todo: as a morphism *)

Lemma In_map A B (f: A -> B) (a: A) n (v: Vector.t A n): List.In a v -> List.In (f a) (map f v).
Proof. induction v; intros; inversion_clear H; [left; subst | right]; auto. Qed.

Lemma List_map A B n (l: Vector.t A n) (f: A -> B): List.map f l = to_list (map f l).
Proof with auto.
  induction l...
  simpl.
  intros.
  rewrite IHl...
Qed.

(* vnth *)

Lemma natBelow0_rect: natBelow 0 -> forall T, T.
Proof. intros. inversion H. Qed.

(*Definition pred (n: nat): nat := match n with 0 => 0 | S n' => n' end.*)
Definition nof (n: nat) (_: natBelow n): nat := n.

Section mine.

Variable P: forall n: nat, natBelow n -> Type.
Variable Pz: forall p, P (mkNatBelow 0 p).
Variable Ps: forall v p, P (mkNatBelow v p) -> P (mkNatBelow (S v) p).

Fixpoint natBelow_rect (n: nat): forall nb: natBelow n, P nb :=
  match n with
  | 0 => fun nb => natBelow0_rect nb _
  | S x => fun nb =>
    match nb return (forall nb: natBelow (pred (nof nb)), P nb) -> P nb with
    | mkNatBelow 0 y => fun _ => Pz y
    | mkNatBelow (S z) y => fun U => Ps (U (mkNatBelow z y))
    end (@natBelow_rect x)
  end.

End mine.

Section another.

Variable P: forall n: nat, natBelow (S n) -> Type.
Variable Pz: forall p, P (mkNatBelow 0 p).
Variable Ps: forall v p, P (mkNatBelow v p) -> P (mkNatBelow (S v) p).

Definition R (n: nat): natBelow n -> Type :=
  match n with
  | 0 => fun _ => False
  | S _ => @P _
  end.

Definition natBelow_rect_S (n: nat) (nb: natBelow (S n)): P nb := natBelow_rect R Pz Ps nb.

End another.


Lemma val_Snb n (x: natBelow n): nb_val (Snb x) = S (nb_val x).
Proof. destruct x. reflexivity. Qed.

Lemma val_nb0 n: nb_val (nb0 n) = 0.
Proof. reflexivity. Qed.

Lemma natBelow_S_inv (n: nat) (nb: natBelow (S n)): { nb': natBelow n | nb = Snb nb' } + { nb = nb0 n }.
Proof with reflexivity.
  pattern n, nb.
  apply natBelow_rect_S.
    simpl.
    right...
  intros.
  left.
  destruct H.
    destruct s.
    exists (Snb x).
    rewrite <- e...
  exists (nb0 (v + p)).
  rewrite <- e...
Qed.

Definition natBelow_S_bla (T: Type) (n: nat) (b: natBelow n): T -> (natBelow (pred n) -> T) -> T :=
  match b with
  | mkNatBelow 0 _ => fun z s => z
  | mkNatBelow (S i) p => fun z s => s (mkNatBelow i p)
  end.

Lemma natBelow_S_inv' (n: nat) (P: natBelow (S n) -> Type):
  P (nb0 n) -> (forall m, P (Snb m)) -> forall x, P x.
Proof. intros. destruct (natBelow_S_inv x); [destruct s | idtac]; subst; auto. Qed.
  (* maybe it would be nicer to have this one as the primitive, and natBelow_S_inv above as the derived one *)

Fixpoint nth X (n: nat) (v: Vector.t X n): natBelow n -> X :=
  match v with
  | Vector.nil => fun nb => natBelow0_rect nb _
  | Vector.cons h k t => fun nb => natBelow_S_bla nb h (nth t)
  end.

Lemma nth_0 A n (v: Vector.t A (S n)):
  nth v (nb0 n) = head v.
Proof. intros. rewrite (eq_cons v). reflexivity. Qed.

Lemma nth_S A p (v: Vector.t A (S p)) (n: natBelow p):
  nth v (Snb n) = nth (tail v) n.
Proof.
  intros.
  rewrite (eq_cons v).
  simpl.
  unfold Snb.
  destruct n.
  reflexivity.
Qed.

Lemma nth_map A B (f: A -> B) n i (v: Vector.t A n):
  nth (map f v) i = f (nth v i).
Proof with auto.
  induction v.
    inversion i.
  simpl.
  destruct (natBelow_S_inv i).
    destruct s.
    subst.
    simpl.
    unfold natBelow_S_bla.
    unfold Snb.
    simpl.
    destruct x.
    apply IHv.
  subst...
Qed.

Lemma nb1 (n: natBelow 1): n = mkNatBelow 0 0.
Proof.
  intros.
  apply natBelow_unique.
  simpl.
  dependent simple inversion n.
  simpl.
  omega.
Qed.

Lemma ext_nth A n (x y: Vector.t A n): ext_eq (nth x) (nth y) -> x = y.
Proof with auto.
  revert n x y.
  apply (double_rect (fun n (x y: Vector.t A n) => ext_eq (nth x) (nth y) -> x = y))...
  intros.
  cset (H0 (nb0 n)).
  simpl in H1.
  subst.
  rewrite H...
  intro.
  cset (H0 (Snb x)).
  repeat rewrite nth_S in H1...
Qed.

Lemma In_nth A n i (v: Vector.t A n): List.In (nth v i) v.
Proof with auto.
  induction i using natBelow_rect in v |- *.
    simpl.
    intros.
    rewrite (eq_cons v).
    simpl head.
    left...
  intros.
  rewrite (eq_cons v).
  right.
  simpl plus.
  fold (Snb (mkNatBelow v0 p)).
  rewrite nth_S...
Qed.

Lemma to_list_app A n (v: Vector.t A n) m (w: Vector.t A m):
  to_list (app v w) = List.app (to_list v) (to_list w).
Proof with auto.
  induction n.
    intros.
    rewrite (eq_nil v)...
  intros.
  rewrite (eq_cons v).
  simpl.
  rewrite IHn...
Qed.

Lemma In_vec_inv A a n (v: Vector.t A n): List.In a v -> exists i, a = nth v i.
Proof with auto.
  induction v.
    intros.
    inversion H.
  intros.
  inversion_clear H.
    exists (nb0 n).
    simpl...
  destruct (IHv H0).
  exists (Snb x).
  rewrite nth_S...
Qed.

Lemma nb_val_eq_rec_r (k u: nat) (n: natBelow u) (h: k = u):
  nb_val (eq_rec_r natBelow n h) = nb_val n.
Proof. intros. unfold eq_rec_r, eq_rec, eq_rect. case (sym_eq h). auto. Qed.

Fixpoint take A n: forall m, Vector.t A (n + m) -> Vector.t A n :=
  match n return forall m, Vector.t A (n + m) -> Vector.t A n with
  | 0 => fun _ _ => Vector.nil
  | S n' => fun m v => Vector.cons (head v) (take n' m (tail v))
  end.

Fixpoint drop A n: forall m, Vector.t A (n + m) -> Vector.t A m :=
  match n return forall m, Vector.t A (n + m) -> Vector.t A m with
  | 0 => fun m v => v
  | S n' => fun m v => drop n' m (tail v)
  end.

Lemma split A n m (v: Vector.t A (n + m)): v = app (take n m v) (drop n m v).
Proof with auto.
  induction n...
  intros.
  simpl.
  rewrite <- IHn.
  apply eq_cons.
Qed.

Lemma eq_app_inv A n m (a b: Vector.t A n) (c d: Vector.t A m): app a c = app b d -> a = b /\ c = d.
Proof with auto.
  induction n in m, a, b, c, d |- *; simpl; intros.
    rewrite (eq_nil a).
    rewrite (eq_nil b)...
  destruct (Vcons_eq_inv H).
  destruct (IHn _ _ _ _ _ H1).
  split...
  rewrite (eq_cons a).
  rewrite (eq_cons b).
  rewrite H0.
  rewrite H2...
Qed.

(* remove *)

Definition remove (T: Set) (n: nat) (v: Vector.t T (S n)) (nb: natBelow (S n)): Vector.t T n :=
  natBelow_rect_S
    (fun (n0: nat) (_: natBelow (S n0)) => Vector.t T (S n0) -> Vector.t T n0)
    (fun p => @tail p _)
    (fun v p H v0 => Vector.cons (head v0) (H (tail v0))) nb v.

(* permutations *)

Inductive Permutation (A: Type): forall n, Vector.t A n -> Vector.t A n -> Prop :=
  | perm_nil: Permutation Vector.nil Vector.nil
  | perm_skip (x: A) n (v v': Vector.t A n): Permutation v v' -> Permutation (Vector.cons x v) (Vector.cons x v')
  | perm_swap (x y: A) n (l: Vector.t A n): Permutation (Vector.cons y (Vector.cons x l)) (Vector.cons x (Vector.cons y l))
  | perm_trans n (l l' l'': Vector.t A n): Permutation l l' -> Permutation l' l'' -> Permutation l l''.

Hint Resolve perm_nil.
Hint Resolve perm_skip.
Hint Resolve perm_swap.

Lemma perm_sym (X: Set) n (a b: Vector.t X n): Permutation a b -> Permutation b a.
Proof with auto. intros p. induction p... apply perm_trans with l'... Qed.

Lemma perm_refl (X: Set) n (v: Vector.t X n): Permutation v v.
Proof. induction v; auto. Qed.

Lemma List_Permutation (X: Set) n (a b: Vector.t X n): Permutation a b -> Permutation.Permutation a b.
Proof with eauto.
  intros p.
  induction p; simpl...
Qed.

Lemma remove_head (T: Set) p (v: Vector.t T (S p)):
  remove v (mkNatBelow 0 p) = tail v.
Proof. reflexivity. Qed.

Lemma remove_tail (T: Set) n p (v: Vector.t T (S (S (n + p)))):
  remove v (mkNatBelow (S n) p) = Vector.cons (head v) (remove (tail v) (mkNatBelow n p)).
Proof. reflexivity. Qed.

Lemma in_remove (T: Set) x n (i: natBelow (S n)) (v: Vector.t T (S n)):
  List.In x v -> x <> nth v i -> List.In x (remove v i).
Proof with auto.
  revert v.
  pattern n, i.
  apply natBelow_rect_S.
    intros.
    rewrite remove_head.
    rewrite (eq_cons v) in H.
    simpl in H.
    destruct H...
    elimtype False.
    apply H0.
    fold (nb0 p).
    rewrite nth_0...
  intros.
  simpl plus.
  rewrite remove_tail.
  rewrite (eq_cons v0) in H0.
  destruct H0.
    left.
    assumption.
  right.
  apply H...
  clear H0.
  rewrite (eq_cons v0) in H1.
  simpl in H1...
Qed.

Lemma remove_map (A B: Set) (f: A -> B) n (i: natBelow (S n)) (v: Vector.t A (S n)):
  remove (map f v) i = map f (remove v i).
Proof with reflexivity.
  revert v.
  pattern n, i.
  apply natBelow_rect_S.
    simpl.
    intros.
    rewrite (eq_cons v).
    simpl.
    do 2 rewrite remove_head...
  intros.
  simpl plus.
  cset remove_tail.
  simpl plus in *.
  rewrite H0.
  rewrite H0.
  simpl.
  rewrite <- H.
  rewrite (eq_cons v0).
  reflexivity.
Qed.

Lemma remove_perm (T: Set) n (nb: natBelow (S n)) (v: Vector.t T (S n)):
  Permutation (Vector.cons (nth v nb) (remove v nb)) v.
Proof with auto.
  revert v.
  pattern n, nb.
  apply natBelow_rect_S.
    simpl.
    intros.
    rewrite remove_head.
    rewrite (eq_cons v).
    simpl.
    apply perm_refl.
  intros.
  simpl plus.
  rewrite remove_tail.
  cset (H (tail v0)).
  clear H.
  simpl plus in *.
  cset' (remove (tail v0) (mkNatBelow v p)).
  fold (Snb (mkNatBelow v p)).
  rewrite nth_S.
  cut (Permutation (Vector.cons (nth (tail v0) (mkNatBelow v p)) (Vector.cons (head v0) H)) (Vector.cons (head v0) (tail v0))).
    rewrite <- eq_cons.
    intros...
  apply perm_trans with (Vector.cons (head v0) (Vector.cons (nth (tail v0) (mkNatBelow v p)) H))...
Qed.

Require Import skip_list.

Lemma SkipList_tail (A: Set) n (v: Vector.t A (S n)): SkipList (tail v) v.
Proof.
  intros.
  rewrite (eq_cons v).
  simpl.
  apply SkipList_tail.
  apply SkipList_refl.
Qed.

Lemma SkipList_remove (A: Set) n (nb: natBelow (S n)) (l: Vector.t A (S n)):
  SkipList (remove l nb) l.
Proof.
  revert l.
  pattern n, nb.
  apply natBelow_rect_S.
    simpl.
    intros.
    rewrite remove_head.
    apply SkipList_tail.
  intros.
  destruct v.
    simpl.
    rewrite (eq_cons l).
    simpl.
    apply SkipList_head.
    apply SkipList_tail.
  cset (remove_tail (S v) p l).
  simpl plus in *.
  rewrite H0.
  cset (H (tail l)).
  apply SkipList_trans with (List.cons (head l) (tail l)).
    simpl.
    apply SkipList_head.
    assumption.
  rewrite (eq_cons l).
  simpl.
  apply SkipList_refl.
Qed.

Definition remove_In (X: Set) n (v: Vector.t X (S n)) x i (p: List.In x (remove v i)): List.In x v
  := incl_In x p (SkipList_incl (SkipList_remove i v)).

(* nats *)

Lemma trans_plus_n_Sm n m: n + S m = S (n + m).
Proof.
  induction n; simpl.
    reflexivity.
  intros.
  apply eq_S.
  apply IHn.
Defined.

Fixpoint nats (x n: nat) {struct n}: Vector.t (natBelow (x + n)) n :=
  match n as n0 return Vector.t (natBelow (x + n0)) n0 with
  | 0 => Vector.nil
  | S n0 => map (fun d => eq_rec_r natBelow d (trans_plus_n_Sm x n0))
    (Vector.cons (mkNatBelow x n0) (nats (S x) n0))
  end.

Definition nb_nats (x n: nat): Vector.t nat n := map nb_val (nats x n).

Lemma nats_S (x n: nat): nats x (S n) =
  map (fun d => eq_rec_r natBelow d (trans_plus_n_Sm x n)) (Vector.cons (mkNatBelow x n) (nats (S x) n)).
Proof. reflexivity. Qed.

Lemma nb_nats_S (x n: nat): nb_nats x (S n) = Vector.cons x (nb_nats (S x) n).
Proof with reflexivity.
  unfold nb_nats.
  intros.
  simpl.
  apply Vcons_eq.
    rewrite nb_val_eq_rec_r...
  rewrite map_map.
  apply map_ext.
  intro.
  unfold compose.
  rewrite nb_val_eq_rec_r...
Qed.

Lemma In_nats_S v u w: List.In w (nats u v) -> List.In (Snb w) (nats (S u) v).
Proof with auto. (* todo: rename *)
  induction v in u, w |- *...
  simpl.
  intros.
  destruct H.
    left.
    subst.
    apply natBelow_unique.
    rewrite val_Snb.
    rewrite nb_val_eq_rec_r.
    rewrite nb_val_eq_rec_r...
  right.
  rewrite <- List_map in H.
  destruct (In_map_inv H). clear H.
  destruct H0.
  subst.
  set (fun d: natBelow (S (S (u + v))) => eq_rec_r natBelow d (eq_S (u + S v) (S (u + v)) (trans_plus_n_Sm u v))).
  replace (Snb (eq_rec_r natBelow x (trans_plus_n_Sm u v))) with (n (Snb x)).
    rewrite <- List_map.
    apply List.in_map.
    apply (IHv (S u))...
  apply natBelow_unique.
  subst n.
  simpl.
  rewrite val_Snb.
  repeat rewrite nb_val_eq_rec_r.
  rewrite val_Snb...
Qed.

Lemma In_nb_nats v n m: List.In (v + m) (nb_nats m (S (v + n))).
Proof with auto.
  induction v in n, m |- *.
    simpl.
    intros.
    left.
    rewrite nb_val_eq_rec_r...
  simpl.
  intros.
  repeat rewrite nb_val_eq_rec_r.
  simpl.
  cset (IHv n m).
  simpl in H.
  rewrite nb_val_eq_rec_r in H.
  destruct H.
    right.
    left.
    simpl.
    simpl in H.
    apply eq_S...
  rewrite map_map in H.
  rewrite <- List_map in H.
  destruct (In_map_inv H). clear H.
  destruct H0.
  unfold compose in H.
  rewrite nb_val_eq_rec_r in H.
  simpl.
  right.
  right.
  rewrite map_map.
  rewrite map_map.
  unfold compose.
  assert (ext_eq (fun x1: natBelow (S (S (m + (v + n)))) => nb_val (eq_rec_r natBelow (eq_rec_r natBelow x1 (eq_S (m + S (v + n)) (S (m + (v + n))) (trans_plus_n_Sm m (v + n)))) (trans_plus_n_Sm m (S (v + n))))) nb_val).
    intro.
    repeat rewrite nb_val_eq_rec_r...
  rewrite (map_ext H1).
  replace (S (v + m)) with (nb_val (Snb x)).
    rewrite <- List_map.
    apply List.in_map.
    apply (In_nats_S (v + n) (S m))...
  clear H1 H0.
  destruct x.
  simpl in *.
  apply eq_S...
Qed.

Lemma In_nb_nats' x m n: m <= x -> x < m + n -> List.In x (nb_nats m n).
Proof with auto.
  intros.
  destruct (le_exists_plus H).
  subst.
  assert (x0 < n) by omega.
  destruct (lt_exists_plus H1).
  subst.
  rewrite plus_comm.
  apply In_nb_nats.
Qed.

Lemma In_as_nb_val n (x: natBelow n) m (l: Vector.t (natBelow n) m):
  List.In (nb_val x) (map nb_val l) -> List.In x l.
Proof with auto.
  intros.
  rewrite <- List_map in H.
  destruct (In_map_inv H). clear H.
  destruct H0.
  rewrite <- (natBelow_unique _ _ H)...
Qed.

Lemma In_nats_0 n x: List.In x (nats 0 n).
Proof.
  intros.
  apply In_as_nb_val.
  simpl in x.
  dependent inversion_clear x.
  simpl @nb_val.
  cset (In_nb_nats v p 0).
  rewrite plus_0_r in H.
  assumption.
Qed.

Lemma S_rect A n (P: Vector.t A (S n) -> Type):
  (forall h t, P (Vector.cons h t)) -> forall v, P v.
Proof. intros. rewrite (eq_cons v). apply X. Qed.

Lemma In_inv_perm (X: Set) (x: X) n (v: Vector.t X (S n)):
  List.In x v -> exists v': Vector.t X n, Permutation (Vector.cons x v') v.
Proof with auto.
  induction n in v |- *.
    rewrite (eq_cons v).
    rewrite (eq_nil (tail v)).
    intros.
    destruct H.
      subst.
      exists (tail v).
      rewrite (eq_nil (tail v)).
      apply perm_refl.
    elimtype False...
  pattern v. apply S_rect. clear v.
  intros h t. pattern t. apply S_rect. clear t.
  intros.
  simpl in H.
  destruct H.
    subst.
    exists (Vector.cons h0 t).
    apply perm_refl.
  destruct (IHn (Vector.cons h0 t) H).
  exists (Vector.cons h x0).
  apply perm_trans with (Vector.cons h (Vector.cons x x0)).
    apply perm_swap.
  apply perm_skip...
Qed.

Lemma NoDup_incl_Permutation (A: Set) n (a b: Vector.t A n):
  List.NoDup a -> List.incl a b -> Permutation a b.
Proof with auto.
  induction n.
    intros.
    rewrite (eq_nil a).
    rewrite (eq_nil b).
    apply perm_nil.
  pattern a. apply S_rect. clear a. intros ha ta.
  pattern b. apply S_rect. clear b. intros hb tb.
  intros.
  assert (List.In ha (Vector.cons hb tb)).
    apply H0.
    left...
  destruct (In_inv_perm ha (Vector.cons hb tb) H1).
  apply perm_trans with (Vector.cons ha x)...
  apply perm_skip.
  apply IHn.
    inversion_clear H...
  cut (List.incl ta (Vector.cons ha x)).
    intros.
    simpl in H3.
    do 2 intro.
    destruct (H3 _ H4)...
    subst.
    inversion_clear H.
    elimtype False...
  apply List.incl_tran with (to_list (Vector.cons hb tb)).
    do 2 intro.
    apply H0.
    right...
  apply Permutation_incl.
  apply Permutation.Permutation_sym.
  apply List_Permutation...
Qed.

Lemma In_nats_inv z y (x: natBelow (y + z)): List.In x (nats y z) -> y <= x < z + y.
Proof with auto.
  induction z in y, x |- *.
    intros.
    elimtype False...
  simpl.
  rewrite <- List_map.
  intro.
  destruct H.
    subst.
    rewrite nb_val_eq_rec_r.
    simpl.
    omega.
  destruct (In_map_inv H). clear H.
  destruct H0.
  subst.
  rewrite nb_val_eq_rec_r.
  destruct (IHz (S y) x0 H0).
  split.
    apply le_Sn_le...
  rewrite <- plus_n_Sm in H1...
Qed.

Lemma In_nb_nats_inv z y x: List.In x (nb_nats y z) -> y <= x < z + y.
Proof.
  unfold nb_nats.
  intros.
  rewrite <- List_map in H.
  destruct (In_map_inv H). clear H.
  destruct H0.
  subst.
  apply In_nats_inv.
  assumption.
Qed.

Lemma NoDup_nats y x: List.NoDup (nats x y).
Proof with auto. (* todo: proof way too long *)
  induction y in x |- *.
    simpl...
  simpl.
  intros.
  apply List.NoDup_cons.
    intro.
    rewrite <- List_map in H.
    destruct (In_map_inv H). clear H.
    destruct H0.
    destruct (In_nats_inv y (S x) x0 H0).
    assert (nb_val x0 = x).
      replace x with (nb_val (eq_rec_r natBelow (mkNatBelow x y) (trans_plus_n_Sm x y))).
        rewrite <- H.
        rewrite nb_val_eq_rec_r...
      rewrite nb_val_eq_rec_r...
    apply le_Sn_n with x.
    simpl in H1.
    rewrite H3 in H1...
  rewrite <- List_map.
  apply NoDup_map.
    intros.
    apply natBelow_unique.
    rewrite <- (nb_val_eq_rec_r x0 (trans_plus_n_Sm x y)).
    rewrite <- (nb_val_eq_rec_r y0 (trans_plus_n_Sm x y)).
    rewrite H1...
  apply (IHy (S x)).
Qed.

Lemma tail_map (A B: Set) (f: A -> B) n (l: Vector.t A (S n)):
  tail (map f l) = map f (tail l).
Proof. intros. rewrite (eq_cons l). reflexivity. Qed.

Lemma tail_cons (A: Set) (a: A) n (l: Vector.t A n): tail (Vector.cons a l) = l.
Proof. reflexivity. Qed.

Lemma nth_nats m (i: natBelow m) n: nb_val (nth (nats n m) i) = n + i.
Proof with auto.
  revert n.
  pattern m, i.
  apply natBelow_rect.
    simpl.
    intros.
    rewrite nb_val_eq_rec_r.
    simpl.
    symmetry.
    apply plus_0_r.
  intros.
  simpl plus in *.
  fold (Snb (mkNatBelow v p)).
  rewrite nth_S.
  rewrite nats_S.
  rewrite tail_map.
  rewrite tail_cons.
  rewrite nth_map.
  rewrite nb_val_eq_rec_r.
  rewrite <- plus_n_Sm.
  apply (H (S n)).
Qed.

Lemma nth_nats3 m i n: nth (nats (S n) m) i = Snb (nth (nats n m) i).
Proof with auto.
  revert n.
  pattern m, i.
  apply natBelow_rect.
    simpl.
    intros.
    (*Set Printing Coercions.*)
    apply natBelow_unique.
    rewrite val_Snb.
    do 2 rewrite nb_val_eq_rec_r...
  intros.
  apply natBelow_unique.
  simpl plus.
  rewrite (val_Snb (nth (nats n (S (S (v + p)))) (mkNatBelow (S v) p))).
  rewrite nth_nats.
  cset (nth_nats (mkNatBelow (S v) p) (S n)).
  simpl plus in H0.
  rewrite H0.
  simpl...
Qed. (* todo: hm, didn't need induction hypothesis *)

Lemma nth_nats_0 n i: nth (nats 0 n) i = i.
Proof. intros. apply natBelow_unique. rewrite nth_nats. reflexivity. Qed.

Definition plusnb (y x: nat) (nb: natBelow x): natBelow (x + y) :=
  match nb in natBelow x' return natBelow (x' + y) with
  | mkNatBelow a b => eq_rec_r natBelow (mkNatBelow a (b + y)) (eq_S _ _ (plus_assoc_reverse a b y))
  end.

Lemma val_plusnb y x (nb: natBelow x): nb_val (plusnb y nb) = nb_val nb.
Proof.
  intros.
  dependent inversion nb.
  simpl.
  rewrite nb_val_eq_rec_r.
  reflexivity.
Qed.

Lemma map_app (A B: Type) (f: A -> B) n (v: Vector.t A n) m (w: Vector.t A m):
  map f (app v w) = app (map f v) (map f w).
Proof with reflexivity.
  induction n; intros.
    rewrite (eq_nil v)...
  rewrite (eq_cons v).
  simpl.
  rewrite IHn...
Qed.


Lemma app_eq A m (x x': Vector.t A m) n (y y': Vector.t A n): x = x' -> y = y' -> app x y = app x' y'.
Proof. intros. subst. reflexivity. Qed.

Lemma nats_plus x n y:
  nats n (x + y) =
  map (fun nb => eq_rec_r natBelow nb (plus_assoc n x y)) (app (map (@plusnb y _) (nats n x)) (nats (n + x) y)).
Proof with auto.
  induction x in n, y |- *.
    simpl.
    intros.
    apply ext_nth.
    intro.
    rewrite nth_map.
    apply natBelow_unique.
    rewrite nth_nats.
    rewrite nb_val_eq_rec_r.
    rewrite nth_nats...
  simpl.
  intros.
  apply Vcons_eq.
    apply natBelow_unique.
    do 2 rewrite nb_val_eq_rec_r.
    rewrite val_plusnb.
    rewrite nb_val_eq_rec_r.
    simpl...
  rewrite IHx.
  repeat rewrite map_app.
  apply app_eq.
    repeat rewrite map_map.
    apply map_ext.
    intro.
    unfold compose.
    apply natBelow_unique.
    repeat rewrite nb_val_eq_rec_r.
    do 2 rewrite val_plusnb.
    rewrite nb_val_eq_rec_r...
  rewrite map_map.
  apply ext_nth.
  intro.
  do 2 rewrite nth_map.
  unfold compose.
  apply natBelow_unique.
  repeat rewrite nb_val_eq_rec_r.
  simpl.
  rewrite trans_plus_n_Sm...
Qed.

Lemma nb_nats_plus x n y: nb_nats n (x + y) = app (nb_nats n x) (nb_nats (n + x) y).
Proof with auto.
  unfold nb_nats.
  intros.
  rewrite nats_plus.
  rewrite map_map.
  rewrite (@map_ext _ _ (nb_val ∘ (fun nb => eq_rec_r natBelow nb (plus_assoc n x y))) nb_val).
    rewrite map_app.
    rewrite map_map.
    rewrite (@map_ext _ _ (nb_val ∘ plusnb y (x:=n + x)) nb_val)...
    intro. unfold compose.
    apply val_plusnb.
  intro. unfold compose.
  apply nb_val_eq_rec_r.
Qed.

(* misc *)

Lemma map_cons A B (f: A -> B) (h: A) n (t: Vector.t A n): map f (Vector.cons h t) = Vector.cons (f h) (map f t).
Proof. reflexivity. Qed.

Lemma Permutation_mapping (X: Set) n (a b: Vector.t X n): Permutation a b ->
  exists l: Vector.t (natBelow n) n, (forall x, List.In x l) /\ map (nth b) l = a.
Proof with auto with arith.
  intros p.
  induction p.
        exists Vector.nil.
        split...
        intros.
        inversion x.
      destruct IHp.
      destruct H.
      exists (Vector.cons (nb0 n) (map (@Snb _) x0)).
      split.
        intros.
        destruct (natBelow_S_inv x1).
          destruct s.
          subst.
          right.
          rewrite <- List_map.
          apply List.in_map...
        subst.
        left...
      subst.
      rewrite map_cons.
      f_equal.
      rewrite map_map.
      apply map_ext.
      intro.
      unfold compose.
      rewrite nth_S...
    exists (Vector.cons (Snb (nb0 n)) (Vector.cons (nb0 (S n)) (nats 2 n))).
    split.
      intros.
      simpl.
      destruct (natBelow_S_inv x0).
        destruct s.
        subst.
        destruct (natBelow_S_inv x1).
          destruct s.
          subst.
          right.
          right.
          apply (In_nats_S n 1).
          apply (In_nats_S n 0).
          apply In_nats_0.
        subst...
      subst...
    repeat rewrite map_cons.
    f_equal.
    apply (f_equal (@Vector.cons _ x n)).
    apply ext_nth.
    intro.
    rewrite nth_map.
    cset (nth_nats3 x0 1).
    simpl in H.
    rewrite H.
    cset (nth_nats3 x0 0).
    simpl in H0. rewrite H0.
    repeat rewrite nth_S.
    cset (nth_nats_0 x0).
    simpl in *.
    rewrite H1.
    reflexivity.
  destruct IHp1.
  destruct IHp2.
  destruct H.
  destruct H0.
  exists (map (nth x0) x).
  split.
    intros.
    destruct (In_vec_inv _ _ (H0 x1)).
    subst.
    rewrite <- List_map.
    apply List.in_map...
  apply ext_nth.
  intro.
  subst.
  repeat rewrite nth_map...
Qed. (* todo: still way too long *)

Section contents.

  Variable X: Set.
  Variable Xle: X -> X -> Prop.
  Hypothesis XO: preorder X Xle.

  Definition Xlt (x y: X): Prop := Xle x y /\ ~ Xle y x.

  Lemma Xle_nlt: forall x y, Xle x y -> ~ Xlt y x.
  Proof. firstorder. Qed.

  Lemma Xlt_irrefl x: ~ Xlt x x.
  Proof. intro. set (preord_refl _ _ XO x). firstorder. Qed.

  Lemma Xle_lt_trans x y: Xle x y -> forall z, Xlt y z -> Xlt x z.
  Proof with assumption.
    unfold Xlt.
    intros.
    destruct H0.
    split.
      apply (preord_trans _ _ XO) with y...
    intro.
    apply H1.
    apply (preord_trans _ _ XO) with x...
  Qed.

  (* Vsorted *)

  Inductive sorted: forall n, Vector.t X n -> Prop := (* Coq.Sorting's definition sucks *)
    | sorted_nil: sorted Vector.nil
    | sorted_one x: sorted (Vector.cons x Vector.nil)
    | sorted_more (a b: X) n (t: Vector.t X n):
        Xle a b -> sorted (Vector.cons b t) -> sorted (Vector.cons a (Vector.cons b t)).

  Hint Constructors sorted.

  Lemma sorted_cons x n (v: Vector.t X (S n)): Xle x (head v) -> sorted v -> sorted (Vector.cons x v).
  Proof with auto.
    intros.
    rewrite (eq_cons v).
    apply sorted_more...
    rewrite <- eq_cons...
  Qed.

  Lemma sorted_cons' x n (v: Vector.t X n): (forall y, List.In y v -> Xle x y) -> sorted v -> sorted (Vector.cons x v).
  Proof with auto.
    induction v; intros.
      apply sorted_one.
    apply sorted_more...
    apply H. left...
  Qed.

  Lemma sorted_cons_inv x n (v: Vector.t X (S n)): sorted (Vector.cons x v) -> Xle x (head v).
  Proof. intros. rewrite (eq_cons v) in H. inversion_clear H. assumption. Qed.

  Lemma sorted_tail x n (v: Vector.t X n): sorted (Vector.cons x v) -> sorted v.
  Proof. intros. inversion_clear H; auto. Qed.

  Lemma sorted_cons_inv' (x: X) n (xs: Vector.t X n): sorted (Vector.cons x xs) ->
    forall x', List.In x' xs -> Xle x x'.
  Proof with auto.
    induction xs.
      simpl.
      intros.
      elimtype False...
    simpl.
    intros.
    inversion_clear H0.
      subst.
      inversion_clear H...
    apply IHxs...
    clear IHxs H1.
    revert H.
    dependent inversion_clear xs.
      simpl.
      intros.
      apply sorted_one.
    intros.
    apply sorted_more.
      apply (preord_trans _ _ XO) with h...
        apply (sorted_cons_inv H).
      apply (sorted_cons_inv (sorted_tail H)).
    apply (sorted_tail (sorted_tail H)).
  Qed.

  Lemma sorted_app (v w: List.list X): sorted v -> sorted w ->
    (forall x y, List.In x v -> List.In y w -> Xle x y) -> sorted (List.app v w).
  Proof with auto.
    induction v...
    intros.
    simpl.
    apply sorted_cons'.
      intros.
      clear IHv.
      rewrite list_round_trip in H2.
      destruct (List.in_app_or v w y H2).
        simpl in H.
        apply (sorted_cons_inv' H).
        rewrite list_round_trip...
      apply H1...
      left...
    apply IHv...
      simpl in H.
      apply sorted_tail with a...
    intros.
    apply H1...
    simpl...
  Qed.

  Lemma sorted_le_indices_le_values n (v: Vector.t X n): sorted v ->
    forall (i j: natBelow n), i <= j -> Xle (nth v i) (nth v j).
  Proof with auto with arith.
    intros s.
    induction s.
        intros.
        inversion i.
      intros.
      rewrite (nb1 i).
      rewrite (nb1 j).
      simpl.
      apply preord_refl...
    intro i. pattern i. apply natBelow_S_inv'; [idtac | intro m]; intro j; pattern j; apply natBelow_S_inv'.
          rewrite nth_0.
          intros. apply preord_refl...
        rewrite nth_0.
        intros.
        rewrite nth_S.
        apply (preord_trans _ _ XO) with (nth (Vector.cons b t) (nb0 _))...
      rewrite val_Snb.
      simpl @nb_val.
      intros.
      inversion H0.
    intro.
    do 2 rewrite val_Snb.
    do 2 rewrite nth_S...
  Qed.

  Lemma sorted_lt_values_lt_indices n (v: Vector.t X n): sorted v ->
    forall i j, Xlt (nth v i) (nth v j) -> i < j.
  Proof with auto with arith.
    intros s.
    induction s.
        intros.
        inversion i.
      intros i j.
      rewrite (nb1 i).
      rewrite (nb1 j).
      simpl.
      intro.
      elimtype False.
      apply (Xlt_irrefl H).
    intro i. pattern i. apply natBelow_S_inv'; [idtac | intro m]; intro j; pattern j; apply natBelow_S_inv'.
          rewrite nth_0.
          intros.
          elimtype False.
          apply (Xlt_irrefl H0).
        intro.
        rewrite val_nb0.
        rewrite val_Snb...
      rewrite nth_S.
      rewrite nth_0.
      intros.
      elimtype False.
      apply (Xle_nlt H).
      apply Xle_lt_trans with (nth (Vector.cons b t) m)...
      apply (sorted_le_indices_le_values s (nb0 _) m)...
    intro.
    do 2 rewrite nth_S.
    do 2 rewrite val_Snb...
  Qed.

  (* insertion sort *)

  Variable XleDec: forall x y, { Xle x y } + { Xle y x }.

  Fixpoint insert_ordered (x: X) n: Vector.t X n -> Vector.t X (S n) :=
    match n return Vector.t X n -> Vector.t X (S n) with
    | 0 => fun _ => Vector.cons x Vector.nil
    | S n' => fun v => if XleDec x (head v)
        then Vector.cons x v
        else Vector.cons (head v) (insert_ordered x (tail v))
    end.

  Hint Immediate perm_refl.

  Lemma insert_ordered_permutes x n (v: Vector.t X n): Permutation (insert_ordered x v) (Vector.cons x v).
  Proof with auto.
    induction v; simpl...
    destruct (XleDec x h)...
    apply perm_trans with (Vector.cons h (Vector.cons x v))...
  Qed.

  Lemma insert_ordered_preserves_sorted n x (v: Vector.t X n): sorted v -> sorted (insert_ordered x v).
  Proof with auto.
    induction v.
      simpl...
    simpl.
    intros.
    destruct (XleDec x h).
      apply sorted_more...
    destruct n.
      rewrite (eq_nil v).
      simpl.
      apply sorted_more...
    cset (IHv (sorted_tail H)). clear IHv.
    cset (eq_cons v).
    revert H1.
    generalize (head v).
    generalize (tail v).
    intros.
    subst.
    simpl in *.
    destruct (XleDec x x1).
      apply sorted_more...
    apply sorted_more...
    apply (sorted_cons_inv H).
  Qed.

  Fixpoint insertion_sort n: Vector.t X n -> Vector.t X n :=
    match n return Vector.t X n -> Vector.t X n with
    | 0 => fun _ => Vector.nil
    | S n' => fun v => insert_ordered (head v) (insertion_sort (tail v))
    end.

  Lemma insertion_sort_sorts n (l: Vector.t X n): sorted (insertion_sort l).
  Proof with auto.
    induction n; intros.
      rewrite (eq_nil l)...
    rewrite (eq_cons l).
    simpl.
    apply insert_ordered_preserves_sorted...
  Qed.

  Lemma insertion_sort_permutes n (l: Vector.t X n): Permutation (insertion_sort l) l.
  Proof with auto.
    induction l...
    simpl.
    apply perm_trans with (Vector.cons h (insertion_sort l))...
    apply insert_ordered_permutes.
  Qed.

End contents.
