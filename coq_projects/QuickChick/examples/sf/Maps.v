(* QuickChick Prelude *)
Set Warnings "-extraction-opaque-accessed,-extraction".
Set Warnings "-notation-overridden,-parsing".

Require Import String List. Open Scope string.

From QuickChick Require Import QuickChick Tactics.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype seq.
Import QcDefaultNotation. Open Scope qc_scope.

Set Bullet Behavior "Strict Subproofs".

(* End prelude *)

Require Import Ascii String.

Derive (Arbitrary, Show) for ascii.
Derive (Sized, CanonicalSized) for ascii.
Derive SizeMonotonic for ascii using genSascii.
Derive SizedMonotonic for ascii using genSascii.
Derive SizedCorrect for ascii using genSascii and SizeMonotonicascii.

Derive (Arbitrary, Show) for string.
Derive (Sized, CanonicalSized) for string.
Derive SizeMonotonic for string using genSstring.
Derive SizedMonotonic for string.
Derive SizedCorrect for string using genSstring and SizeMonotonicstring.


Inductive id : Type :=
  | Id : string -> id.

Derive (Arbitrary, Show) for id.
Derive (Sized, CanonicalSized) for id.
Derive SizeMonotonic for id using genSid.
Derive SizedMonotonic for id.
Derive SizedCorrect for id using genSid and SizeMonotonicid.

Instance eq_dec_id (x y : id) : Dec (x = y).
constructor; unfold decidable. repeat decide equality. Defined.

Definition beq_id x y :=
  match x,y with
    | Id n1, Id n2 => if string_dec n1 n2 then true else false
  end.

Theorem beq_id_refl : forall id, true = beq_id id id.
Admitted. (* QuickChick beq_id_refl. *) 

Theorem beq_id_true_iff : forall x y : id,
  beq_id x y = true <-> x = y.
Admitted. (* Prop *)

Theorem beq_id_false_iff : forall x y : id,
  beq_id x y = false
  <-> x <> y.
Admitted. (* Prop *)

Theorem false_beq_id : forall x y : id,
   x <> y
   -> beq_id x y = false.
Admitted. (* QuickChick false_beq_id. *)

(* Maps as functions are bad, explicit maps instead *)

Definition partial_map := list (id * nat).

Definition empty : partial_map := nil.

Definition update := @cons (id * nat).

Inductive bind : partial_map -> id -> nat -> Prop :=
  | BindNow   : forall x a m, bind (cons (x, a) m) x a
  | BindLater : forall x x' a a' m',
                  ~ (x = x') ->
                  bind m' x a -> 
                  bind (cons (x',a') m') x a.

Derive ArbitrarySizedSuchThat for (fun x => bind m x a).
Derive SizeMonotonicSuchThatOpt for (fun x => bind m x a).
Derive GenSizedSuchThatSizeMonotonicOpt for (fun x => bind m x a).
(* KNOWN DUG. The derivation of SizedProofEqs for bind fails. *)
(* Derive SizedProofEqs for (fun x => bind m x a). *)
(* Derive GenSizedSuchThatCorrect for (fun x => bind m x a). *)

Instance adm_st m a : SuchThatCorrect (fun x => bind m x a) (genST (fun x => bind m x a)).
Admitted.

Instance checkFalse : Checkable False := {| checker := fun _ => checker false |}.

Instance bind_dec m x v : Dec (bind m x v) :=
  {| dec := _ |}.
Proof.
  move: x v.
  induction m => x v.
  - right => contra. inversion contra.
  - destruct a as [x' v'].
    destruct (eq_dec_id x x') as [[Eq | Neq]].
    + destruct (Dec_eq_nat v v') as [[EqV | NeqV]].
      * subst; left ; constructor; eauto.
      * subst; right => Contra.
        inversion Contra; subst; eauto.
    + subst; specialize (IHm x v).
      destruct IHm as [L | R].
      * left; constructor; eauto.
      * right => Contra; inversion Contra; subst; eauto.
Defined.

(* TODO: Correct equivalence of maps *)
Definition equiv_map m1 m2 :=
  forall x v , bind m1 x v <-> bind m2 x v.

Conjecture apply_empty : forall x a, ~ (bind empty x a).
(* QuickChick apply_empty. *)
(* Gave Up! - QuickChick apply_empty_unfolded. *)

Conjecture update_eq : forall (m: partial_map) x v,
    bind (update (x,v) m) x v.
(* QuickChick update_eq. *)

Theorem update_neq : forall v x1 x2
                       (m : partial_map),
  x2 <> x1 ->
    forall v' v'', bind (cons (x2, v) m) x1 v' ->
                   bind m x1 v'' ->
                   v' = v''.
Admitted. (* Leo: TODO QuickChick update_neq. *)

Lemma update_shadow : forall (m: partial_map) v1 v2 x,
  update (x, v2) (update (x, v1) m)  = update (x, v2) m.
Admitted. (* QuickChick update_shadow. *)

Theorem update_same : forall v x (m : partial_map),
  bind m x v ->
  update (x, v) m = m.
Admitted. (* QuickChick update_same. *)

Theorem update_permute : forall v1 v2 x1 x2
                                (m : partial_map),
  x2 <> x1 ->
    (update (x1,v1) (update (x2,v2) m))
  = (update (x2,v2) (update (x1,v1) m)).
Admitted. (* QuickChick update_permute. *)

Definition total_map := (partial_map * nat)%type.

Definition t_empty v : total_map := (empty, v).

Definition t_update (m : total_map) (x : id) (v : nat) :=
  let (pm,d) := m in
  (update (x, v) pm, d).

Inductive t_bind : partial_map -> nat -> id -> nat -> Prop :=
  | T_BindDef   : forall x v, t_bind nil v x v
  | T_BindNow   : forall x a m d, t_bind (cons (x, a) m) d x a
  | T_BindLater : forall x x' a a' m' d,
                  ~ (x = x') ->
                  t_bind m' d x a -> 
                  t_bind (cons (x',a') m') d x a.

Derive ArbitrarySizedSuchThat for (fun x => t_bind m d x a).
Derive SizeMonotonicSuchThatOpt for (fun x => t_bind m d x a).

Instance adm_st' d m a : SuchThatCorrect (fun x => t_bind m d x a) (genST (fun x => t_bind m d x a)).
Admitted.

Lemma t_apply_empty:  forall x v v', t_bind empty v x v' -> v = v'.
Admitted. (* Leo TODO: suchtat4_2  QuickChick t_apply_empty. *)

Fixpoint lookup m x : option nat :=
  match m with 
  | nil => None
  | (x',v)::t => if (x = x') ? then Some v else lookup t x
  end.

Definition t_lookup (m : total_map) x := 
  let (m, d) := m in
  match lookup m x with
  | Some v => v
  | None => d
  end.

Lemma t_update_eq : forall (m: total_map) x v,
  t_lookup (t_update m x v) x = v.
Admitted. (* QuickChick t_update_eq. *)

Theorem t_update_neq : forall v x1 x2
                         (m : total_map),
  x1 <> x2 ->
  t_lookup (t_update m x1 v) x2 = t_lookup m x2.
Admitted. (* QuickChick t_update_neq. *)

Lemma t_update_shadow : forall  (m: total_map) v1 v2 x,
    t_update (t_update m x v1) x v2
  = t_update m x v2.
Admitted. (* QuickChick t_update_shadow. *)

Lemma beq_idP : forall x y, reflect (x = y) (beq_id x y).
Admitted. (* Undecidable *)

Theorem t_update_same : forall x (m : total_map),
  t_update m x (t_lookup m x) = m.
Admitted. (* QuickChick t_update_same *)

Theorem t_update_permute : forall v1 v2 x1 x2
                             (m : total_map),
  x2 <> x1 ->
    (t_update (t_update m x2 v2) x1 v1)
  = (t_update (t_update m x1 v1) x2 v2).
Admitted. (* QuickChick t_update_permute *)
