
Set Implicit Arguments.

Require Import Bool.
Require Import List.
Require Import Le.
Require Import Lt.
Require Import Arith.
Require Import Omega.
Require Import util.
Require Import arith_lems.
Require Import List.
Require Import monads.
Require Import monoid_monad_trans.
Require Import qs_definitions.
Import mon_det.
Require fix_measure_utils.

Set Shrink Obligations.

Variables (T: Set) (cmp: T -> T -> bool). (* "le" *)

Definition counted_cmp (x y: T): SimplyProfiled bool := (1, cmp x y). (* lift *)

Lemma filter_cost (p: T -> SimplyProfiled bool):
  (forall t, cost (p t) = 1) -> forall (l: list T), cost (filter _ p l) = length l.
Proof with auto with arith.
  intros pd.
  induction l...
  simpl.
  destruct (filter SimplyProfiled p l)...
  destruct s...
  set (pd a).
  clearbody e.
  destruct (p a)...
  simpl in *.
  subst.
  omega.
Qed.

Lemma exclusive_filtering (T: Set) (p q: T -> SimplyProfiled bool)
  (ex: forall x, result (p x) = false \/ result (q x) = false) (l: list T):
    length (proj1_sig (result (filter SimplyProfiled p l))) +
    length (proj1_sig (result (filter SimplyProfiled q l))) <= length l.
Proof with auto with arith.
  induction l...
  simpl.
  destruct (filter SimplyProfiled p l).
  destruct (filter SimplyProfiled q l).
  destruct s.
  destruct s0.
  simpl in *.
  destruct (ex a); [destruct (p a) | destruct (q a)]; simpl in H; subst; simpl; [destruct (q a) | destruct (p a)]; destruct b; simpl; omega.
Qed.

Lemma counted_cmp_excl (n x: T):
  result (counted_cmp n x) = false \/ result (gt _ counted_cmp n x) = false.
Proof. simpl. intros. destruct (cmp n x); auto. Qed.

Lemma common_arith
  (n n3 n0 n1 n2: nat)
  (l0: n3 + n0 <= n)
  (p: n1 <= sqrd n3)
  (p0: n2 <= sqrd n0):
   n + n2 + n + n1 <= sqrd n + n + n + 1.
Proof with auto with arith.
  intros.
  apply le_trans with (n2 + n1 + (n + n)); try omega.
  apply le_trans with (sqrd n + 1 + (n + n)); try omega.
  apply plus_le_compat_r.
  deep_le_trans p...
  deep_le_trans p0...
  rewrite plus_comm in l0.
  apply le_trans with (sqrd (n0 + n3))...
Qed.

Lemma bind_eqq (M: Monad) (e: extMonad M) (A B: Set) (m n: M A) (f g: A -> M B): m = n -> ext_eq f g -> (m >>= f) = (n >>= g).
Proof.
  intros.
  subst.
  apply e.
  assumption.
Qed.

Hint Resolve SimplyProfiled_ext.

Definition qs_body (l: list T) (qs0: {l': list T | length l' < length l} -> SimplyProfiled (list T)) :=
  match l as l1 return (l1 = l -> SimplyProfiled (list T)) with
  | nil => fun _ => ret (m:=SimplyProfiled) nil
  | pivot :: t => fun Heq_l =>
      lower <-
        x <- filter SimplyProfiled (gt SimplyProfiled counted_cmp pivot) t;
        qs0 (exist _ (proj1_sig x) (qs_definitions.mon_det.qs_obligation_1 SimplyProfiled (fun l H => qs0 (exist _ l H)) Heq_l x));
      upper <-
        x <- filter SimplyProfiled (counted_cmp pivot) t;
        qs0 (exist _ (proj1_sig x) (qs_definitions.mon_det.qs_obligation_2 SimplyProfiled (fun l H => qs0 (exist _ l H)) Heq_l x));
      ret (m:=SimplyProfiled) (lower ++ pivot :: upper)
  end refl_equal.

Theorem qs_quadratic (l: list T): cost (qs counted_cmp l) <= sqrd (length l).
Proof with auto with arith.
  intros.
  set (P := fun (l: list T) (r: SimplyProfiled (list T)) => cost r <= sqrd (length l)).
  cut (P l (qs counted_cmp l))...
  unfold qs.
  fold qs_body.
  apply fix_measure_utils.rect; subst P; intros.
    unfold qs_body.
    destruct x0...
    repeat (try apply bind_eqq; try intro; auto).
  simpl.
  unfold qs_body.
  simpl proj1_sig.
  destruct x...
  repeat rewrite bind_cost.
  repeat rewrite return_cost.
  repeat rewrite filter_cost...
  fold qs_body.
  cset (exclusive_filtering (counted_cmp t) (gt SimplyProfiled counted_cmp t) (counted_cmp_excl t) x).
  destruct (result (filter SimplyProfiled (gt SimplyProfiled counted_cmp t) x)).
  destruct (result (filter SimplyProfiled (counted_cmp t) x)).
  simpl proj1_sig in *.
  assert (fix_measure_utils.MR lt (fun l: list T => length l) x0 (t :: x)). unfold fix_measure_utils.MR. simpl...
  assert (fix_measure_utils.MR lt (fun l: list T => length l) x1 (t :: x)). unfold fix_measure_utils.MR. simpl...
  unfold SimplyProfiled in H.
  simpl mon in H.
  deep_le_trans (H x0 H1)...
  deep_le_trans (H x1 H2)...
  simpl in *.
  rewrite sqrd_S.
  autorewrite with arith_norm.
  apply common_arith with (length x1) (length x0)...
Qed.
