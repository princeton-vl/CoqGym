(** * Addendum to the standard library of Coq *)

Require Import Bool Arith Div2 List Permutation.
Require Export Omega.

Global Obligation Tactic := idtac.

Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) .. ).

Lemma length_nil : forall A (l : list A),
  length l = 0 -> l = nil.
Proof.
 intros; destruct l; trivial; intros.
 simpl in H; contradict H; omega.
Qed.

Lemma length_tail A l : length (@tail A l) = length l - 1.
Proof.
  destruct l; simpl; auto with arith.
Qed.

Lemma hd_nth_0 A (l : list A) d :
  hd d l = nth 0 l d.
Proof. intros; case l; simpl; trivial. Qed.

Lemma hd_nth_1 A (l : list A) d :
  hd d (tl l) = nth 1 l d.
Proof.
 intros; case l; simpl; intros; trivial.
 apply hd_nth_0.
Qed.

Lemma In_hd (A : Type)(d:A)(l : list A)(n : nat)(H : length l = S n) :
  In (hd d l) l.
Proof.
destruct l.
simpl in H.
discriminate H.
simpl; tauto.
Qed.

Lemma map_hd : forall A B (f:A->B) d l, f (hd d l) = hd (f d) (map f l).
Proof.
intros A B f d [ | x l]; trivial.
Qed.

Lemma map_tl : forall A B (f:A->B) l, map f (tl l) = tl (map f l).
Proof.
intros A B f [ | x l]; trivial.
Qed.

Lemma map_eq_hd :
  forall A B (f:A->B) d l1 l2,
  map f l1 = map f l2 -> f (hd d l1) = f (hd d l2).
Proof.
intros A B f d [ | a1 l1] [ | a2 l2]; simpl; congruence.
Qed.

Lemma firstn_nil {A} n : firstn n (@nil A) = nil.
Proof. case n; simpl; trivial. Qed.

Lemma skipn_nil : forall {A} n (x : list A),
  length x <= n -> skipn n x = nil.
Proof.
  induction n; simpl in *; trivial; intros.
  apply length_nil; auto; omega.
  destruct x; simpl in *; trivial.
  apply IHn; omega.
Qed.

Lemma nth_firstn : forall A i j (l:list A) d,
  i < j -> nth i (firstn j l) d = nth i l d.
Proof.
 intros A i j.
 revert i; induction j; simpl; intros.
 contradict H; omega.
 case l; simpl; destruct i; simpl; trivial; intros.
 apply IHj; omega.
Qed.

Lemma nth_skipn A i j (l:list A) d : 
  nth i (skipn j l) d = nth (j+i) l d.
Proof.
 intros; revert i l.
 induction j; simpl; intros; trivial.
 destruct l; simpl; trivial; case i; trivial.
Qed.

Lemma length_skipn : forall A n (y : list A),
  length (skipn n y) = length y - n.
Proof.
  induction n; simpl; intros; [ omega | ].
  destruct y; simpl; trivial.
Qed.

Lemma skipn_length : forall {A} n (l:list A), 
  length (skipn n l) = length l - n.
Proof.
  induction n; simpl; intros; auto with arith.
  destruct l; simpl; auto.
Qed.

Lemma cons_skipn :
  forall A d i (l:list A),
  i < length l ->
  nth i l d :: skipn (S i) l = skipn i l.
Proof.
 induction i as [ | i IH]; simpl; intros.
 destruct l as [ | x l]; trivial.
 contradict H; simpl; omega.
 destruct l as [ | x l].
 contradict H; simpl; omega.
 rewrite <- IH; trivial.
 simpl in H; omega.
Qed.

Lemma skipn_plus :
  forall A j i (l:list A), skipn (i+j) l = skipn i (skipn j l).
Proof.
 induction j as [ | j IH]; simpl; intros.
 rewrite plus_0_r; trivial.
 rewrite <- plus_Snm_nSm.
 case l.
 rewrite !skipn_nil; simpl; trivial; omega.
 simpl; trivial.
Qed.

Lemma skipn_hd : forall {A} n y (d:A), 
  n < length y -> 
  skipn n y = nth n y d :: skipn (S n) y.
Proof.
 induction n; simpl; intros.
 destruct y; simpl in *; trivial.
 contradict H; omega.
 destruct y; simpl in *.
 contradict H; omega.
 apply IHn.
 omega.
Qed.

Lemma firstn_app {A} (l l' : list A) : 
  firstn (length l) (l ++ l') = l.
Proof.
 induction l; intros; simpl; trivial.
 rewrite IHl; trivial.
Qed.

Lemma skipn_app {A} (l l' : list A) : 
  skipn (length l) (l ++ l') = l'.
Proof. induction l; intros; simpl; trivial. Qed.

Lemma map_cons : forall A B (f:A->B) a l, map f (a::l) = f a :: map f l.
Proof. trivial. Qed.

Lemma map_firstn : forall A B (f:A->B) n l,
  map f (firstn n l) = firstn n (map f l).
Proof.
 induction n; simpl; intros; trivial.
 case l; simpl; trivial; congruence.
Qed.

Lemma map_skipn : forall A B (f:A->B) n l,
  map f (skipn n l) = skipn n (map f l).
Proof.
 induction n; simpl; intros; trivial.
 case l; simpl; trivial; congruence.
Qed.

Lemma map_nth_seq : forall A (l:list A) len n d,
  length l = len + n ->
  map (fun x : nat => nth x l d) (seq n len) = (skipn n l).
Proof.
 intros A l len; revert l.
 induction len; simpl; intros.
 rewrite skipn_nil; trivial; omega.
 rewrite IHlen, <- skipn_hd; trivial; omega.
Qed.

Lemma skipn_nil_length : forall A n (l : list A),
  skipn n l = nil -> length l <= n.
Proof.
  induction n; simpl in *; intros.
  subst; simpl; trivial.
  destruct l; simpl; [ omega | ].
  generalize (IHn _ H); omega.
Qed.

Lemma firstn_map_nth :
  forall A d n m (l:list A),
  m+n <= length l ->
  firstn n (skipn m l) = map (fun i => nth i l d) (seq m n).
Proof.
 induction n as [ | n IH]; simpl; intros; trivial.
 rewrite <- IH by omega.
 replace (skipn (S m) l) with (tl (skipn m l)).
 case_eq (skipn m l).
 intro H0.
 contradict H0.
 contradict H.
 apply skipn_nil_length in H; omega.
 intros x l' H0; simpl; f_equal.
 erewrite skipn_hd in H0.
 injection H0.
 intros _ H1.
 symmetry; apply H1.
 omega.
 rewrite <- cons_skipn with (d:=d); trivial; omega.
Qed.

Lemma firstn_seq n start len :
  firstn n (seq start len) = seq start (min n len).
Proof.
 intros; revert n start.
 induction len; simpl; intros.
 rewrite min_r; simpl;[ | omega].
 apply firstn_nil.
 case n; simpl; trivial; congruence.
Qed.

Lemma skipn_seq n start len :
  skipn n (seq start len) = seq (start+n) (len-n).
Proof.
 intros; revert n start.
 induction len; simpl; intros.
 apply skipn_nil; simpl; omega.
 case n; simpl; intros.
 rewrite plus_0_r; trivial.
 rewrite <- plus_Snm_nSm; apply IHlen.
Qed.

Lemma in_seq_iff : forall x len start,
  In x (seq start len) <-> start <= x < start+len.
Proof.
intros x len.
induction len; simpl; intros;[ omega | ].
split.
intros [H | H]; subst; try omega.
assert (S start <= x < S start + len).
rewrite <- IHlen; trivial.
omega.
intro H; rewrite IHlen; omega.
Qed.

Lemma nth_map_cst :
  forall {A B} (l:list A) n (d:B), nth n (map (fun _ => d) l) d = d.
Proof.
intros A B l.
induction l as [ | a l IH]; intros [ | n] d; simpl; trivial.
Qed.

Lemma nth_S_tl A (l : list A) d n :
  nth n (tl l) d = nth (S n) l d.
Proof.
 intros; destruct l; simpl; intros; trivial.
 case n; trivial.
Qed.

Lemma map_ext2 : forall {A B} (f g : A -> B) l,
  (forall a : A, In a l -> f a = g a) -> map f l = map g l.
Proof.
 intros; induction l; simpl; trivial.
 f_equal.
 apply H; simpl; auto.
 apply IHl.
 intros; apply H; simpl; auto.
Qed.

Lemma map_nth2
  (A B : Type) (f : A -> B) (l : list A) b d n :
  (f d) = b ->
  nth n (map f l) b = f (nth n l d).
Proof. intros; rewrite <- H; apply map_nth. Qed.

Lemma length_plus_ex {A} n1 n2 (l : list A):
  length l = n1 + n2 ->
  exists l1, exists l2,
    length l1 = n1 /\ length l2 = n2 /\ l = l1 ++ l2.
Proof.
 intros.
 exists (firstn n1 l).
 exists (skipn n1 l).
 rewrite firstn_length, min_l, length_skipn, firstn_skipn; repeat split; omega.
Qed.

Lemma tl_app : forall A (l1 l2 : list A),
  l1 <> nil ->
  tl (l1 ++ l2) = tl l1 ++ l2.
Proof.
 intros; destruct l1; simpl; trivial.
 elim H; trivial.
Qed.

Lemma map_seq_nth : forall A B (l : list A) (g : A -> B) d, 
 map (fun n => g (nth n l d)) (seq 0 (length l)) = map g l.
Proof.
 intros A B l g d.
 change l with (skipn 0 l) at 3.
 rewrite <- map_nth_seq with (len := length l) (d := d).
 rewrite map_map.
 auto.
 auto.
Qed.

Lemma map_seq_shift : forall A m (f : nat -> A) n,
n <> 0 ->
map f (seq 0 m) = map (fun x => f (x - n)%nat) (seq n m).
Proof.
 induction m; simpl; intros; auto.
 f_equal.
 f_equal; omega.
 rewrite <- seq_shift with (start := 0).
 rewrite map_map.
 rewrite IHm with (n := S n). 
 apply map_ext2.
 intros; f_equal.
 rewrite in_seq_iff in H0.
 omega.
 omega.
Qed.

Lemma map_seq_nth_safe : forall A B (l : list A) (g : A -> B) d m, 
 map (fun n => g (nth (n - m) l d)) (seq m (length l)) = map g l.
Proof.
 intros A B l g d m.
 rewrite <- map_seq_nth with (d := d).
 destruct m; simpl.
 apply map_ext; intros.
 rewrite <- minus_n_O; trivial.
 rewrite map_seq_shift with (n := S m); auto.
Qed.

Lemma seq_app : forall x y z,
  seq x y ++ seq (x + y) z = seq x (y + z).
Proof.
 intros.
 rewrite <- firstn_skipn with (l := seq x (y + z)) (n := y).
 f_equal.
 rewrite firstn_seq.
 rewrite Min.min_l; auto.
 omega.
 rewrite skipn_seq.
 f_equal; omega.
Qed.

Definition andl {A} (P:A->Prop)(l:list A) : Prop :=
  fold_right (fun a res => P a /\ res) True l.

Lemma forall_andl A (P:A->Prop) l :
  (forall x, In x l -> P x) <-> andl P l.
Proof.
 induction l; simpl; intros;[ tauto | ].
 split; intro.
 rewrite <- IHl; auto.
 intros x [H1 | H2]; subst;[ tauto | ].
 apply IHl; tauto.
Qed.

Fixpoint fun_power {A:Type}(n:nat)(f:A->A)(x:A) : A :=
  match n with
  | 0 => x
  | S n' => f (fun_power n' f x)
  end.

Lemma fun_power_minus_S : forall A (f:A->A) x m n,
  m < n -> f (fun_power (n - S m) f x) = fun_power (n - m) f x.
Proof.
 intros A f x m n H.
 replace (n-m) with (S (n - S m)) by omega; trivial.
Qed.

Definition mod2 (n : nat) : nat :=
  n - 2 * div2 n.

Fixpoint power (m n:nat) : nat :=
 match n with
 | 0 => 1
 | S n' => m * power m n'
 end.

Lemma power_le_l : forall a b n, a <= b -> power a n <= power b n.
Proof.
 induction n; simpl; intros; trivial.
 apply mult_le_compat; tauto.
Qed.

Definition plusl (l:list nat) : nat :=
  fold_right plus 0 l.

Lemma plusl_cons : forall x l, plusl (x :: l) = x + plusl l.
Proof. trivial. Qed.

Lemma plusl_app l1 l2 :
  plusl (l1++l2) = plusl l1 + plusl l2.
Proof.
 induction l1; simpl; intros; trivial.
 rewrite IHl1; ring.
Qed.

Lemma plusl_compat : forall A (l : list A) f g,
  (forall x, In x l -> f x <= g x) ->
  plusl (map f l) <= plusl (map g l).
Proof.
 induction l; simpl; intros; auto.
 apply plus_le_compat; auto.
Qed. 

Definition multl (l:list nat) : nat :=
  fold_right mult 1 l.

Lemma multl_app l1 l2 :
  multl (l1++l2) = multl l1 * multl l2.
Proof.
 induction l1; simpl; intros; trivial.
 rewrite IHl1; ring.
Qed.

Lemma multl_plus_distr_l n l :
  n * plusl l = plusl (map (fun m => n * m) l).
Proof.
 induction l as [ | m l' IH]; simpl; intros; [ | rewrite <- IH]; ring.
Qed.

Fixpoint maxl l := 
  match l with
    | nil => 0
    | a :: l' => max a (maxl l')
  end.

Lemma in_le_maxl x l : In x l -> x <= maxl l.
Proof.
 induction l; simpl; intros.
 tauto.
 destruct H; subst.
 apply Nat.le_max_l.
 eapply le_trans; [ | apply Nat.le_max_r]; tauto.
Qed.

Lemma maxl_map A l (f : A -> nat) n :
  (forall x, In x l -> f x = n) ->
  maxl (map f l) <= n.
Proof.
 induction l; simpl; intros; trivial.
 omega.
 apply Nat.max_lub.
 rewrite H; auto.
 apply IHl.
 intros; apply H; auto.
Qed.

Lemma maxl_le l e :
  maxl l <= e ->
  (forall x, In x l -> x <= e).
Proof.
 induction l; simpl;[ tauto | intros].
 destruct H0; subst.
 apply Nat.max_lub_l with (maxl l); trivial.
 apply IHl; trivial.
 apply Nat.max_lub_r with a; trivial.
Qed.

Lemma maxl_eq_le l e :
  maxl l = e ->
  (forall x, In x l -> x <= e).
Proof.
 intros.
 apply maxl_le with l; auto.
 rewrite H; auto.
Qed.

Lemma maxl_eq_le3 e1 e2 e3 e :
  maxl [e1; e2; e3] = e ->
  e1 <= e /\ e2 <= e /\ e3 <= e.
Proof.
 intros.
 assert (Hl := maxl_eq_le _ _ H).
 repeat split; apply Hl; simpl; auto.
Qed.

Lemma maxl_le3 e1 e2 e3 e :
  maxl [e1; e2; e3] <= e ->
  e1 <= e /\ e2 <= e /\ e3 <= e.
Proof.
 intros.
 assert (Hl := maxl_le _ _ H).
 repeat split; apply Hl; simpl; auto.
Qed.

Lemma maxl_bound e1 e2 e3 e :
  e1 <= e -> e2 <= e -> e3 <= e ->
  maxl [e1; e2; e3] <= e.
Proof.
 intros.
 simpl.
 apply Nat.max_lub; trivial.
 apply Nat.max_lub; trivial.
 apply Nat.max_lub; trivial.
 omega.
Qed.

Lemma maxl_bound_in l e :
  (forall e', In e' l -> e' <= e) -> maxl l <= e.
Proof.
 induction l; simpl; intros;[ omega | ].
 apply Nat.max_lub.
 apply H; auto.
 apply IHl.
 intros; apply H; auto.
Qed.

Lemma maxl_cons l n : n <= maxl (n :: l).
Proof.
 destruct l; simpl; intros.
 auto with arith.
 apply Nat.le_max_l.
Qed.

Lemma le_maxl_cons l m n :
 n <= maxl l -> n <= maxl (m :: l).
Proof.
 induction l; simpl; intros;[ omega | ].
 eapply le_trans.
 apply Nat.le_max_r.
 apply Nat.max_le_compat_l; trivial.
Qed.

Lemma nth_maxl_bound : forall A (l : list A) (m:A->nat) d i,
  m d = 0 -> m (nth i l d) <= maxl (map m l).
Proof.
intros A l m d.
induction l as [ | a l IH]; intros [ | i] H; simpl.
omega.
omega.
auto with arith.
eapply le_trans.
apply IH.
exact H.
apply Nat.le_max_r.
Qed.

Lemma length_hd_app A (l1 l2 : list (list A)) :
  length (hd nil l1) <= length (hd nil (l1 ++ l2)).
Proof. intros; case l1; simpl; trivial; omega. Qed.

Lemma length_nth_app A (l1 l2 : list (list A)) i :
  length (nth i l1 nil) <= length (nth i (l1 ++ l2) nil).
Proof.
 intros; destruct (le_lt_dec (length l1) i).
 rewrite nth_overflow; simpl; trivial; omega.
 rewrite app_nth1; trivial.
Qed.

Lemma maxl_nth l :
  exists i, maxl l = nth i l 0.
Proof.
 induction l; simpl.
 exists 0; trivial.
 destruct IHl.
 destruct (le_lt_dec a (maxl l)).
 rewrite max_r; trivial.
 exists (S x); trivial.
 exists 0; rewrite max_l; trivial.
 omega.
Qed.

Lemma maxl_map_0 A l (f : A -> nat)  :
  (forall x, In x l -> (f x) = 0) ->
  maxl (map f l) = 0.
Proof.
 induction l; simpl; intros; trivial.
 rewrite H, IHl; simpl; trivial; intros; auto.
Qed.

Lemma maxl_le_plusl : forall l, maxl l <= plusl l.
Proof.
 induction l; trivial; simpl.
 apply Nat.max_lub; omega.
Qed.

Lemma forallb_forall_conv :
  forall A f (l:list A), forallb f l = false <-> (exists x, In x l /\ f x = false).
Proof.
 induction l as [ | x l IH]; simpl; split.
 congruence.
 intros [x H]; tauto.
 intro H.
 apply andb_false_elim in H.
 destruct H as [H | H].
 exists x; tauto.
 rewrite IH in H.
 destruct H as [y H]; exists y; tauto.
 intros [y H].
 apply andb_false_iff.
 destruct H as [ [H1 | H1] H2]; subst; auto.
 right; rewrite IH; exists y; tauto.
Qed.

Lemma forallb_nth : forall A (l : list A) (p : A -> bool) n d,
  p d = true ->
  forallb p l = true ->
  p (nth n l d) = true.
Proof.
 induction l; simpl; intros; case n; trivial; intros;
   rewrite andb_true_iff in H0; [ | apply IHl ]; tauto.
Qed.

Lemma forallb_hd : forall A (l : list A) (p : A -> bool) d,
  forallb p l = true ->
  p d = true ->
  p (hd d l) = true.
Proof.
 destruct l; simpl; intros; trivial.
 rewrite andb_true_iff in H; tauto.
Qed.

Lemma forallb_tl : forall A (l : list A) (p : A -> bool),
  forallb p l = true ->
  forallb p (tail l) = true.
Proof.
 induction l; simpl; intros; trivial.
 rewrite andb_true_iff in H; tauto.
Qed.

Lemma forallb_map : forall A B (l : list A) (p : B -> bool) (f : A -> B),
  (forall x, In x l -> p (f x) = true) ->
  forallb p (map f l) = true.
Proof.
 intros; apply forallb_forall.
 intros.
 apply in_map_iff in H0.
 destruct H0 as ( x' & H0 & H1); subst; auto.
Qed.

Fixpoint repeat {A:Type}(n:nat)(x:A) : list A :=
  match n with
  | 0 => nil
  | S n' => x :: repeat n' x
  end.

Lemma firstn_repeat_le :
  forall A (x:A) m n,
  m <= n ->
  firstn m (repeat n x) = repeat m x.
Proof.
intros A x m.
induction m as [ | m IH]; intros n H.
trivial.
destruct n as [ | n].
contradict H.
omega.
simpl.
f_equal.
apply IH.
omega.
Qed.

Lemma in_repeat_eq : forall A (x y:A) n, In x (repeat n y) -> x=y.
Proof.
 induction n as [ | n IH]; simpl; intro H; [ tauto | ].
 destruct H as [H | H].
 congruence.
 tauto.
Qed.

Lemma map_repeat : forall A B (f:A->B) n x, map f (repeat n x) = repeat n (f x).
Proof.
 induction n as [ | n IH].
 trivial.
 simpl; congruence.
Qed.

Lemma multl_repeat_power : forall n x, multl (repeat n x) = power x n.
Proof. induction n as [ | n IH]; trivial; simpl; congruence. Qed.

Lemma length_repeat : forall A n (x:A), length (repeat n x) = n.
Proof. induction n; simpl; intros; trivial; congruence. Qed.

Lemma nth_repeat :
  forall A n (x:A) d i, i < n ->
  nth i (repeat n x) d = x.
Proof.
 intros A n x d.
 induction n as [ | n IH]; simpl ; intros i H.
 contradict H.
 omega.
 destruct i as [ | i]; auto with arith.
Qed.

Definition move_forward {A}(i j:nat)(l:list A)(d:A) : list A :=
  firstn i l ++ firstn j (skipn (S i) l) ++ (nth i l d :: skipn (S (i+j)) l).

Lemma move_forward_map A B d1 d2 i j (f:A->B) l :
  f d1 = d2 ->
  move_forward i j (map f l) d2 = map f (move_forward i j l d1).
Proof.
 intros; unfold move_forward.
 rewrite !map_app; f_equal.
 rewrite map_firstn; trivial.
 f_equal.
 rewrite map_firstn, map_skipn; trivial.
 rewrite map_nth2 with (d:=d1); trivial.
 rewrite <- map_skipn; trivial.
Qed.

Lemma length_move_forward :
  forall A i j (l:list A) d, i+j < length l -> length (move_forward i j l d) = length l.
Proof.
unfold move_forward.
intros.
do 2 rewrite app_length.
do 2 rewrite firstn_length.
rewrite min_l.
rewrite min_l.
change (length (nth i l d :: skipn (S (i + j)) l)) with (1 + length (skipn (S (i + j)) l)).
rewrite length_skipn.
omega.
rewrite length_skipn.
omega.
omega.
Qed.

Lemma in_move_forward_iff :
  forall A x i j d (l:list A), i < length l -> (In x (move_forward i j l d) <-> In x l).
Proof.
unfold move_forward.
intros A x i j d l Hi.
transitivity (In x (firstn i l ++ nth i l d :: firstn j (skipn (S i) l) ++ skipn (S (i + j)) l)).
split.
apply Permutation_in.
apply Permutation_app_head.
apply Permutation_sym.
apply Permutation_middle.
apply Permutation_in.
apply Permutation_app_head.
apply Permutation_middle.
assert (l = firstn i l ++ nth i l d :: firstn j (skipn (S i) l) ++ skipn (S (i + j)) l) as H.
rewrite <- (firstn_skipn i l) at 1.
f_equal.
transitivity (nth i l d :: skipn (S i) l).
symmetry.
apply cons_skipn.
trivial.
f_equal.
transitivity (firstn j (skipn (S i) l) ++ skipn j (skipn (S i) l)).
rewrite firstn_skipn.
trivial.
f_equal.
rewrite <- skipn_plus.
f_equal.
ring.
rewrite H at 5.
tauto.
Qed.

Lemma firstn_simpl : forall A B (l : list A) (l2 : list B),
 length l2 = length l ->
 firstn (length l2) l = l.
Proof.
 intros.
 rewrite H.
 rewrite <- app_nil_r with (l := l) at 2 .
 rewrite firstn_app.
 trivial.
Qed.

Lemma firstn_app2 : forall (A : Type) (l l' : list A) n, 
 length l = n -> firstn n (l ++ l') = l .
Proof. intros; subst; apply firstn_app. Qed.

Lemma firstn_firstn : forall A n (l : list A),
 firstn n (firstn n l) = firstn n l.
Proof.
 induction n; simpl; auto.
 intros [ | a l]; try rewrite IHn; auto.
Qed.

Lemma In_firstn : forall A n a (l : list A),
  In a (firstn n l) -> In a l.
Proof.
 intros A; induction n; simpl; intros.
 elim H.
 destruct l; simpl in *.
 elim H.
 destruct H; subst; auto.
Qed.
