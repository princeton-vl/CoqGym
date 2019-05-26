(* QuickChick Prelude *)
Set Warnings "-extraction-opaque-accessed,-extraction".
Set Warnings "-notation-overridden,-parsing".

Require Import String List. Open Scope string.

From QuickChick Require Import QuickChick Tactics.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype seq.
Import QcDefaultNotation. Open Scope qc_scope.

Set Bullet Behavior "Strict Subproofs".

(* End prelude *)

Require Import Smallstep.
Require Import Types.

Inductive ty : Type :=
  | TBool  : ty
  | TArrow : ty -> ty -> ty.

Derive (Arbitrary, Show) for ty.
Derive (Sized, CanonicalSized) for ty.
Derive SizeMonotonic for ty using genSty.
Derive SizedMonotonic for ty.
Derive SizedCorrect for ty using genSty and SizeMonotonicty.

Instance eq_dec_ty (t1 t2 : ty) : Dec (t1 = t2).
constructor; unfold decidable; decide equality; auto. Defined.

Require Import Ascii String.

Derive (Arbitrary, Show) for ascii.
Derive (Sized, CanonicalSized) for ascii.
Derive SizeMonotonic for ascii using genSascii.
Derive SizedMonotonic for ascii.
Derive SizedCorrect for ascii using genSascii and SizeMonotonicascii.

Derive (Arbitrary, Show) for string.
Derive (Sized, CanonicalSized) for string.
Derive SizeMonotonic for string using genSstring.
Derive SizedMonotonic for string.


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


Inductive trm : Type :=
  | tvar : id -> trm
  | tapp : trm -> trm -> trm
  | tabs : id -> ty -> trm -> trm
  | ttrue : trm
  | tfalse : trm
  | tif : trm -> trm -> trm -> trm.

Derive (Arbitrary, Show) for trm.
Derive (Sized, CanonicalSized) for trm.
Derive SizeMonotonic for trm using genStrm.
Derive SizedMonotonic for trm.
Derive SizedCorrect for trm using genStrm and SizeMonotonictrm.


Instance eq_dec_tm (t1 t2 : trm) : Dec (t1 = t2).
constructor; unfold decidable; repeat decide equality. Defined.

(* Leo: TODO: lowercase x - name clash *)
Inductive value : trm -> Prop :=
  | v_abs : forall X T t,
      value (tabs X T t)
  | v_true :
      value ttrue
  | v_false :
      value tfalse.

Derive ArbitrarySizedSuchThat for (fun tm => value tm).
Derive SizedProofEqs for (fun tm => value tm).
Derive SizeMonotonicSuchThatOpt for (fun tm => value tm).
Derive GenSizedSuchThatCorrect for (fun tm => value tm).
Derive GenSizedSuchThatSizeMonotonicOpt for (fun tm => value tm).

Instance dec_value t : Dec (value t).
constructor; unfold decidable; induction t;
try solve [left; constructor; auto];
try solve [right => contra; inversion contra; eauto].
Defined.

Hint Constructors value.

Reserved Notation "'[' x ':=' s ']' t" (at level 20).

Fixpoint subst (x:id) (s:trm) (t:trm) : trm :=
  match t with
  | tvar x' =>
      if beq_id x x' then s else t
  | tabs x' T t1 =>
      tabs x' T (if beq_id x x' then t1 else ([x:=s] t1))
  | tapp t1 t2 =>
      tapp ([x:=s] t1) ([x:=s] t2)
  | ttrue =>
      ttrue
  | tfalse =>
      tfalse
  | tif t1 t2 t3 =>
      tif ([x:=s] t1) ([x:=s] t2) ([x:=s] t3)
  end

where "'[' x ':=' s ']' t" := (subst x s t).

(*
Inductive substi (s:trm) (x:id) : trm -> trm -> Prop :=
  | s_var1 :
      substi s x (tvar x) s
  (* FILL IN HERE *)
.

Hint Constructors substi.

Theorem substi_correct : forall s x t t',
  [x:=s]t = t' <-> substi s x t t'.
Proof.
  (* FILL IN HERE *) Admitted.
*)

Reserved Notation "t1 '===>' t2" (at level 40).

Inductive step : trm -> trm -> Prop :=
  | ST_AppAbs : forall x T t12 v2,
         value v2 ->
         (tapp (tabs x T t12) v2) ===> [x:=v2]t12
  | ST_App1 : forall t1 t1' t2,
         t1 ===> t1' ->
         tapp t1 t2 ===> tapp t1' t2
  | ST_App2 : forall v1 t2 t2',
         value v1 ->
         t2 ===> t2' ->
         tapp v1 t2 ===> tapp v1  t2'
  | ST_IfTrue : forall t1 t2,
      (tif ttrue t1 t2) ===> t1
  | ST_IfFalse : forall t1 t2,
      (tif tfalse t1 t2) ===> t2
  | ST_If : forall t1 t1' t2 t3,
      t1 ===> t1' ->
      (tif t1 t2 t3) ===> (tif t1' t2 t3)

where "t1 '===>' t2" := (step t1 t2).

Hint Constructors step.

Notation multistep := (multi step).
Notation "t1 '===>*' t2" := (multistep t1 t2) (at level 40).

Definition context := list (id * ty).

Definition empty : context := nil.

Inductive bind : context -> id -> ty -> Prop :=
  | BindNow   : forall i a m, bind (cons (i, a) m) i a
  | BindLater : forall i i' a a' m',
                  ~ (i = i') ->
                  bind m' i a -> 
                  bind (cons (i',a') m') i a.

Derive ArbitrarySizedSuchThat for (fun i => bind m i a).
Derive SizeMonotonicSuchThatOpt for (fun i => bind m i a).
Derive GenSizedSuchThatSizeMonotonicOpt for (fun x => bind m x a).
(* KNOWN DUG. The derivation of SizedProofEqs for bind fails. *)
(* Derive SizedProofEqs for (fun x => bind m x a). *)
(* Derive GenSizedSuchThatCorrect for (fun x => bind m x a). *)

Instance adm_st m a : SuchThatCorrect (fun x => bind m x a) (genST (fun x => bind m x a)).
Admitted.

Instance bind_dec m x v : Dec (bind m x v) :=
  {| dec := _ |}.
Proof.
  move: x v.
  induction m => x v.
  - right => contra. inversion contra.
  - destruct a as [x' v'].
    destruct (eq_dec_id x x') as [[Eq | Neq]].
    + destruct (eq_dec_ty v v') as [[EqV | NeqV]].
      * subst; left ; constructor; eauto.
      * subst; right => Contra.
        inversion Contra; subst; eauto.
    + subst; specialize (IHm x v).
      destruct IHm as [L | R].
      * left; constructor; eauto.
      * right => Contra; inversion Contra; subst; eauto.
Defined.

Reserved Notation "Gamma '|-' t '\typ' T" (at level 40).

Inductive has_type : context -> trm -> ty -> Prop :=
  | T_Var : forall Gamma i T,
      bind Gamma i T ->
      Gamma |- tvar i \typ T
  | T_Abs : forall Gamma i T11 T12 t12,
      cons (i, T11) Gamma |- t12 \typ T12 ->
      Gamma |- tabs i T11 t12 \typ TArrow T11 T12
  | T_App : forall T11 T12 Gamma t1 t2,
      Gamma |- t1 \typ TArrow T11 T12 ->
      Gamma |- t2 \typ T11 ->
      Gamma |- tapp t1 t2 \typ T12
  | T_True : forall Gamma,
       Gamma |- ttrue \typ TBool
  | T_False : forall Gamma,
       Gamma |- tfalse \typ TBool
  | T_If : forall t1 t2 t3 T Gamma,
       Gamma |- t1 \typ TBool ->
       Gamma |- t2 \typ T ->
       Gamma |- t3 \typ T ->
       Gamma |- tif t1 t2 t3 \typ T

where "Gamma '|-' t '\typ' T" := (has_type Gamma t T).

Hint Constructors has_type.

Derive ArbitrarySizedSuchThat for (fun tm => has_type Gamma tm ty).
Derive SizedProofEqs for (fun tm => value tm).
Derive SizeMonotonicSuchThatOpt for (fun tm => value tm).
Derive GenSizedSuchThatCorrect for (fun tm => value tm).
Derive GenSizedSuchThatSizeMonotonicOpt for (fun tm => value tm).

Instance has_type_gen_correct0 Gamma T : SuchThatCorrect (fun t => has_type Gamma t T) 
                                                         (@arbitraryST _ (fun t => has_type Gamma t T) _).
Admitted.

Fixpoint lookup (Gamma : context) (i : id) : option ty :=
  match Gamma with 
  | nil => None
  | cons (i',T) Gamma' => 
    if beq_id i i' then Some T
    else lookup Gamma' i
  end.


Theorem beq_id_true_iff : forall x y : id,
  beq_id x y = true <-> x = y.
Admitted. (* Prop *)

Theorem beq_id_false_iff : forall x y : id,
  beq_id x y = false
  <-> x <> y.
Admitted. (* Prop *)

Lemma lookup_bind : forall Gamma i T, lookup Gamma i = Some T <-> bind Gamma i T.
induction Gamma => i T; split; intros; eauto.
- inversion H.
- inversion H.
- destruct a; simpl in *.
  destruct (beq_id i i0) eqn:HeqI; eauto.
  + inversion H.
    apply (beq_id_true_iff) in HeqI.
    subst; constructor.
  + apply beq_id_false_iff in HeqI; constructor; eauto.
    eapply IHGamma in H; auto.
- destruct a; inversion H; subst; eauto.
  + simpl.
    destruct (beq_id i i) eqn:B; auto.
    apply beq_id_false_iff in B; congruence.
  + simpl.
    destruct (beq_id i i0) eqn:B; auto.
    * eapply beq_id_true_iff in B; subst; congruence.
    * eapply IHGamma in H6; auto.
Qed.    

Fixpoint get_type (Gamma : context) (t : trm) : option ty.
Admitted.

Instance dec_has_type Gamma t T : Dec (has_type Gamma t T).
constructor; unfold decidable.
move: Gamma T; induction t => Gamma T.
- destruct (bind_dec Gamma i T) as [[In | NotIn]].
  + left; constructor; auto.
  + right => contra; inversion contra; eauto.
Admitted.
