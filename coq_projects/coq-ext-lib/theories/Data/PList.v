Require Import ExtLib.Structures.Functor.
Require Import ExtLib.Structures.Applicative.
Require Import ExtLib.Data.POption.
Require Import ExtLib.Data.PPair.
Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Tactics.Consider.
Require Import ExtLib.Tactics.Injection.

Require Import Coq.Bool.Bool.

Set Universe Polymorphism.
Set Primitive Projections.

Section plist.
  Polymorphic Universe i.
  Variable T : Type@{i}.

  Polymorphic Inductive plist : Type@{i} :=
  | pnil
  | pcons : T -> plist -> plist.

  Polymorphic Fixpoint length (ls : plist) : nat :=
    match ls with
    | pnil => 0
    | pcons _ ls' => S (length ls')
    end.

  Polymorphic Fixpoint app (ls ls' : plist) : plist :=
    match ls with
    | pnil => ls'
    | pcons l ls => pcons l (app ls ls')
    end.

  Polymorphic Definition hd (ls : plist) : poption T :=
    match ls with
    | pnil => pNone
    | pcons x _ => pSome x
    end.

  Polymorphic Definition tl (ls : plist) : plist :=
    match ls with
    | pnil => ls
    | pcons _ ls => ls
    end.

  Polymorphic Fixpoint pIn (a : T) (l : plist) : Prop :=
    match l with
    | pnil => False
    | pcons b m => b = a \/ pIn a m
    end.

  Polymorphic Inductive pNoDup : plist -> Prop :=
    pNoDup_nil : pNoDup pnil
  | pNoDup_cons : forall (x : T) (l : plist),
                 ~ pIn x l -> pNoDup l -> pNoDup (pcons x l).

  Polymorphic Fixpoint inb {RelDecA : RelDec (@eq T)} (x : T) (lst : plist) :=
    match lst with
    | pnil => false
    | pcons l ls => if x ?[ eq ] l then true else inb x ls
    end.

  Polymorphic Fixpoint anyb (p : T -> bool) (ls : plist) : bool :=
    match ls with
    | pnil => false
    | pcons l ls0 => if p l then true else anyb p ls0
    end.

  Polymorphic Fixpoint allb (p : T -> bool) (lst : plist) : bool :=
    match lst with
    | pnil => true
    | pcons l ls => if p l then allb p ls else false
    end.

  Polymorphic Fixpoint nodup {RelDecA : RelDec (@eq T)} (lst : plist) :=
    match lst with
    | pnil => true
    | pcons l ls => andb (negb (inb l ls)) (nodup ls)
    end.

  Polymorphic Fixpoint nth_error (ls : plist) (n : nat) : poption T :=
    match n , ls with
    | 0 , pcons l _ => pSome l
    | S n , pcons _ ls => nth_error ls n
    | _ , _ => pNone
    end.

  Section folds.
    Polymorphic Universe j.
    Context {U : Type@{j}}.
    Variable f : T -> U -> U.

    Polymorphic Fixpoint fold_left (acc : U) (ls : plist) : U :=
      match ls with
      | pnil => acc
      | pcons l ls => fold_left (f l acc) ls
      end.

    Polymorphic Fixpoint fold_right (ls : plist) (rr : U) : U :=
      match ls with
      | pnil => rr
      | pcons l ls => f l (fold_right ls rr)
      end.
  End folds.

End plist.

Arguments pnil {_}.
Arguments pcons {_} _ _.
Arguments app {_} _ _.
Arguments pIn {_} _ _.
Arguments pNoDup {_} _.
Arguments anyb {_} _ _.
Arguments allb {_} _ _.
Arguments inb {_ _} _ _.
Arguments nodup {_ _} _.
Arguments fold_left {_ _} _ _ _.
Arguments fold_right {_ _} _ _ _.
Arguments nth_error {_} _ _.


Section plistFun.
  Polymorphic Fixpoint split {A B : Type} (lst : plist (pprod A B)) :=
    match lst with
    | pnil => (pnil, pnil)
    | pcons (ppair x y) tl => let (left, right) := split tl in (pcons x left, pcons y right)
    end.

  Lemma pIn_split_l {A B : Type} (lst : plist (pprod A B)) (p : pprod A B) (H : pIn p lst) :
    (pIn (pfst p) (fst (split lst))).
  Proof.
    destruct p; simpl.
    induction lst; simpl in *.
    + destruct H.
    + destruct t; simpl.
      destruct (split lst); simpl.
      destruct H as [H | H].
      { inv_all. tauto. }
      { tauto. }
  Qed.

  Lemma pIn_split_r {A B : Type} (lst : plist (pprod A B)) (p : pprod A B) (H : pIn p lst) :
    (pIn (psnd p) (snd (split lst))).
  Proof.
    destruct p; simpl.
    induction lst; simpl in *.
    + destruct H.
    + destruct t; simpl.
      destruct (split lst); simpl.
      destruct H.
      { inv_all; tauto. }
      { tauto. }
  Qed.

  Lemma pIn_app_iff (A : Type) (l l' : plist A) (a : A) :
    pIn a (app l l') <-> pIn a l \/ pIn a l'.
  Proof.
    induction l; simpl; intuition congruence.
  Qed.

End plistFun.

Section plistOk.
  Context {A : Type}.
  Context {RelDecA : RelDec (@eq A)}.
  Context {RelDecA_Correct : RelDec_Correct RelDecA}.

  Lemma inb_sound (x : A) (lst : plist A) (H : inb x lst = true) : pIn x lst.
  Proof.
    induction lst; simpl in *; try congruence.
    consider (x ?[ eq ] t); intros; subst.
    + left; reflexivity.
    + right; apply IHlst; assumption.
  Qed.

  Lemma inb_complete (x : A) (lst : plist A) (H : pIn x lst) : inb x lst = true.
  Proof.
    induction lst; simpl in *; try intuition congruence.
    consider (x ?[ eq ] t); intros; destruct H as [H | H]; try congruence.
    apply IHlst; assumption.
  Qed.

  Lemma nodup_sound (lst : plist A) (H : nodup lst = true) : pNoDup lst.
  Proof.
    induction lst.
    + constructor.
    + simpl in *. rewrite andb_true_iff in H; destruct H as [H1 H2].
      rewrite negb_true_iff in H1. constructor.
      * intro H. apply inb_complete in H. intuition congruence.
      * apply IHlst; assumption.
  Qed.

  Lemma nodup_complete (lst : plist A) (H : pNoDup lst) : nodup lst = true.
  Proof.
    induction lst.
    + constructor.
    + simpl in *. rewrite andb_true_iff. inversion H; subst; split; clear H.
      * apply eq_true_not_negb. intros H; apply H2. apply inb_sound; assumption.
      * apply IHlst; assumption.
  Qed.

End plistOk.

Section pmap.
  Polymorphic Universe i j.
  Context {T : Type@{i}}.
  Context {U : Type@{j}}.
  Variable f : T -> U.

  Polymorphic Fixpoint fmap_plist (ls : plist@{i} T) : plist@{j} U :=
    match ls with
    | pnil => pnil
    | pcons l ls => pcons (f l) (fmap_plist ls)
    end.
End pmap.

Polymorphic Definition Functor_plist@{i} : Functor@{i i} plist@{i} :=
{| fmap := @fmap_plist@{i i} |}.
Existing Instance Functor_plist.


Section applicative.
  Polymorphic Universe i j.

  Context {T : Type@{i}} {U : Type@{j}}.
  Polymorphic Fixpoint ap_plist
              (fs : plist@{i} (T -> U)) (xs : plist@{i} T)
    : plist@{j} U :=
    match fs with
    | pnil => pnil
    | pcons f fs => app@{j} (fmap_plist@{i j} f xs) (ap_plist fs xs)
    end.
End applicative.

Polymorphic Definition Applicative_plist@{i} : Applicative@{i i} plist@{i} :=
{| pure := fun _ val => pcons val pnil
 ; ap := @ap_plist
 |}.

Section PListEq.
  Polymorphic Universe i.
  Variable T : Type@{i}.
  Variable EDT : RelDec (@eq T).

  Polymorphic Fixpoint plist_eqb (ls rs : plist T) : bool :=
    match ls , rs with
      | pnil , pnil => true
      | pcons l ls , pcons r rs =>
        if l ?[ eq ] r then plist_eqb ls rs else false
      | _ , _ => false
    end.

  (** Specialization for equality **)
  Global Polymorphic Instance RelDec_eq_plist : RelDec (@eq (plist T)) :=
  { rel_dec := plist_eqb }.

  Variable EDCT : RelDec_Correct EDT.

  Global Polymorphic Instance RelDec_Correct_eq_plist : RelDec_Correct RelDec_eq_plist.
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

End PListEq.
