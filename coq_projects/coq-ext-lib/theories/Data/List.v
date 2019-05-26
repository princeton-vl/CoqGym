Require Import Coq.Lists.List.
Require Coq.Classes.EquivDec.
Require Import ExtLib.Core.Type.
Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Structures.Monoid.
Require Import ExtLib.Structures.Reducible.
Require ExtLib.Data.Nat.
Require Import ExtLib.Tactics.Consider.
Require Import ExtLib.Tactics.Injection.

Set Implicit Arguments.
Set Strict Implicit.

Section type.
  Variable T : Type.
  Context {type_T : type T}.

  Inductive list_eq : list T -> list T -> Prop :=
  | nil_eq : list_eq nil nil
  | cons_eq : forall x xs y ys, equal x y -> list_eq xs ys -> list_eq (x :: xs) (y :: ys).

  Instance type_list : type (list T) :=
  { equal := list_eq
  ; proper := Forall proper
  }.

  Context {typeOk_T : typeOk type_T}.

  Instance typeOk_list : typeOk type_list.
  Proof.
    constructor.
    { intros. induction H.
      { intuition; constructor. }
      { apply only_proper in H; auto. intuition; constructor; intuition. } }
    { intro. induction x; intros.
      { constructor. }
      { inversion H; clear H; subst.
        constructor; auto.
        apply equiv_prefl; auto. apply IHx. apply H3. } }
    { intro. induction 1; constructor; auto.
      apply equiv_sym; auto. }
    { intro. do 3 intro.  revert z. induction H.
      { remember nil. destruct 1; try congruence. constructor. }
      { remember (y :: ys). destruct 1; try congruence. inversion Heql; clear Heql; subst.
        constructor. eapply equiv_trans; eauto. eapply IHlist_eq. apply H2. } }
  Qed.
End type.

Section EqDec.
  Variable T : Type.
  Variable EqDec_T : EquivDec.EqDec _ (@eq T).

  Global Instance EqDec_list : EquivDec.EqDec _ (@eq (list T)).
  Proof.
    red. unfold Equivalence.equiv, RelationClasses.complement.
    intros.
    change (x = y -> False) with (x <> y).
    decide equality. eapply EqDec_T.
  Qed.
End EqDec.

(* Specialized induction rules *)
Lemma list_ind_singleton
: forall {T : Type} (P : list T -> Prop)
         (Hnil : P nil)
         (Hsingle : forall t, P (t :: nil))
         (Hcons : forall t u us, P (u :: us) -> P (t :: u :: us)),
    forall ls, P ls.
Proof.
  induction ls; eauto.
  destruct ls. eauto. eauto.
Qed.

Lemma list_rev_ind
  : forall T (P : list T -> Prop),
    P nil ->
    (forall l ls, P ls -> P (ls ++ l :: nil)) ->
    forall ls, P ls.
Proof.
  clear. intros. rewrite <- rev_involutive.
  induction (rev ls).
  apply H.
  simpl. auto.
Qed.

Section AllB.
  Variable T : Type.
  Variable p : T -> bool.

  Fixpoint allb (ls : list T) : bool :=
    match ls with
      | nil => true
      | l :: ls =>
        if p l then allb ls else false
    end.

  Fixpoint anyb (ls : list T) : bool :=
    match ls with
      | nil => false
      | l :: ls =>
        if p l then true else anyb ls
    end.
End AllB.

Lemma Forall_map
: forall T U (f : T -> U) P ls,
    Forall P (List.map f ls) <-> Forall (fun x => P (f x)) ls.
Proof.
  induction ls; simpl.
  { split; intros; constructor. }
  { split; inversion 1; intros; subst; constructor; auto.
    apply IHls. auto. apply IHls. auto. }
Qed.

Lemma Forall_cons_iff : forall (T : Type) (P : T -> Prop) a b,
    Forall P (a :: b) <-> (P a /\ Forall P b).
Proof. clear. split.
       inversion 1; auto.
       destruct 1; constructor; auto.
Qed.

Lemma Forall_nil_iff : forall (T : Type) (P : T -> Prop),
    Forall P nil <-> True.
Proof.
  clear. split; auto.
Qed.


Global Instance Foldable_list {T} : Foldable (list T) T :=
  fun _ f x ls => fold_right f x ls.

Require Import ExtLib.Structures.Traversable.
Require Import ExtLib.Structures.Functor.
Require Import ExtLib.Structures.Monad.
Require Import ExtLib.Structures.Applicative.

Section traversable.
  Polymorphic Context {F : Type -> Type}.
  Polymorphic Context {Applicative_F : Applicative F}.
  Polymorphic Context {A B : Type}.
  Polymorphic Variable f : A -> F B.

  Polymorphic Fixpoint mapT_list (ls : list A) : F (list B) :=
    match ls with
      | nil => pure nil
      | l :: ls => ap (ap (pure (@cons B)) (f l)) (mapT_list ls)
    end.
End traversable.

Global Instance Traversable_list : Traversable list :=
{ mapT := @mapT_list }.

Global Instance Monad_list : Monad list :=
{ ret  := fun _ x => x :: nil
; bind := fun _ _ x f =>
  List.fold_right (fun x acc => f x ++ acc) nil x
}.



Section list.
  Inductive R_list_len {T} : list T -> list T -> Prop :=
  | R_l_len : forall n m, length n < length m -> R_list_len n m.

  Theorem wf_R_list_len T : well_founded (@R_list_len T).
  Proof.
    constructor. intros.
    refine (@Fix _ _ Nat.wf_R_lt (fun n : nat => forall ls : list T, n = length ls -> Acc R_list_len ls)
      (fun x rec ls pfls => Acc_intro _ _)
      _ _ refl_equal).
    refine (
      match ls as ls return x = length ls -> forall z : list T, R_list_len z ls -> Acc R_list_len z with
        | nil => fun (pfls : x = 0) z pf => _
        | cons l ls => fun pfls z pf =>
          rec _ (match pf in R_list_len xs ys return x = length ys -> Nat.R_nat_lt (length xs) x with
                   | R_l_len n m pf' => fun pf_eq => match eq_sym pf_eq in _ = x return Nat.R_nat_lt (length n) x with
                                                     | refl_equal => Nat.R_lt pf'
                                                   end
                 end pfls) _ eq_refl
      end pfls).
    clear - pf; abstract (inversion pf; subst; simpl in *; inversion H).
  Defined.
End list.

Definition Monoid_list_app {T} : Monoid (list T) :=
{| monoid_plus := @List.app _
 ; monoid_unit := @nil _
 |}.

Section ListEq.
  Variable T : Type.
  Variable EDT : RelDec (@eq T).

  Fixpoint list_eqb (ls rs : list T) : bool :=
    match ls , rs with
      | nil , nil => true
      | cons l ls , cons r rs =>
        if l ?[ eq ] r then list_eqb ls rs else false
      | _ , _ => false
    end.

  (** Specialization for equality **)
  Global Instance RelDec_eq_list : RelDec (@eq (list T)) :=
  { rel_dec := list_eqb }.

  Variable EDCT : RelDec_Correct EDT.

  Global Instance RelDec_Correct_eq_list : RelDec_Correct RelDec_eq_list.
  Proof.
    constructor; induction x; destruct y; split; simpl in *; intros;
      repeat match goal with
               | [ H : context [ rel_dec ?X ?Y ] |- _ ] =>
                 consider (rel_dec X Y); intros; subst
               | [ |- context [ rel_dec ?X ?Y ] ] =>
                 consider (rel_dec X Y); intros; subst
             end; try solve [ auto | exfalso; clear - H; inversion H ].
    - f_equal. eapply IHx. eapply H0.
    - inversion H. subst. eapply IHx. reflexivity.
    - inversion H. exfalso. eapply H0. assumption.
  Qed.

End ListEq.

Global Instance Injective_cons T (a : T) b c d : Injective (a :: b = c :: d).
refine {| result := a = c /\ b = d |}.
inversion 1; auto.
Defined.

Global Instance Injective_cons_nil T (a : T) b : Injective (a :: b = nil).
refine {| result := False |}.
inversion 1; auto.
Defined.

Global Instance Injective_nil_cons T (a : T) b : Injective (nil = a :: b).
refine {| result := False |}.
inversion 1; auto.
Defined.

Global Instance Injective_nil_nil T : Injective (nil = @nil T).
refine {| result := True |}.
auto.
Defined.

Global Instance Injective_app_cons {T} (a : list T) b c d
: Injective (a ++ b :: nil = (c ++ d :: nil)).
Proof.
refine {| result := a = c /\ b = d |}.
eapply app_inj_tail.
Defined.

Global Instance Injective_app_same_L {T} (a : list T) b c
: Injective (b ++ a = b ++ c).
Proof.
refine {| result := a = c |}.
apply app_inv_head.
Defined.

Global Instance Injective_app_same_R {T} (a : list T) b c
: Injective (a ++ b = c ++ b).
Proof.
refine {| result := a = c |}.
apply app_inv_tail.
Defined.


Lemma eq_list_eq
: forall T (a b : T) (pf : a = b) (F : _ -> Type) val,
    match pf in _ = x return list (F x) with
      | eq_refl => val
    end = map (fun val => match pf in _ = x return F x with
                            | eq_refl => val
                          end) val.
Proof.
  destruct pf. intros. rewrite map_id. reflexivity.
Qed.
Hint Rewrite eq_list_eq : eq_rw.

Export Coq.Lists.List.
