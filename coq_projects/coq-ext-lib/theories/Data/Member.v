(** [member] is the proof relevant version of [In] **)
Require Import Coq.Lists.List.
Require Import Relations RelationClasses.
Require Import ExtLib.Core.Type.
Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Data.SigT.
Require Import ExtLib.Data.ListNth.
Require Import ExtLib.Data.Option.
Require Import ExtLib.Structures.Proper.
Require Import ExtLib.Tactics.Injection.
Require Import ExtLib.Tactics.EqDep.

Set Implicit Arguments.
Set Strict Implicit.
Set Asymmetric Patterns.

Section member.
  Context {T : Type}.

  Inductive member (a : T) : list T -> Type :=
  | MZ : forall ls, member a (a :: ls)
  | MN : forall l ls, member a ls -> member a (l :: ls).

  Section to_nat.
    Variable a : T.

    Fixpoint to_nat {ls} (m : member a ls) : nat :=
      match m with
        | MZ _ => 0
        | MN _ _ m => S (to_nat m)
      end.
  End to_nat.

  Lemma member_eta
  : forall x ls (m : member x ls),
      m = match m in member _ ls
                return member x ls
          with
            | MZ ls => MZ x ls
            | MN _ _ n => MN _ n
          end.
  Proof.
    destruct m; auto.
  Qed.

  Lemma member_case
  : forall x ls (m : member x ls),
      match ls as ls return member x ls -> Prop with
        | nil => fun _ => False
        | l :: ls' => fun m =>
                        (exists (pf : l = x),
                           m = match pf in _ = z return member z (l :: ls') with
                                 | eq_refl => MZ _ ls'
                               end)
                        \/ exists m' : member x ls',
                             m = MN _ m'
      end m.
  Proof.
    induction m.
    { left. exists eq_refl. reflexivity. }
    { right. eauto. }
  Qed.

  Lemma to_nat_eq_member_eq
  : forall {_ : EqDec T (@eq T)} x ls (a b : member x ls),
      to_nat a = to_nat b ->
      a = b.
  Proof.
    induction a; intros.
    { destruct (member_case b).
      { destruct H0. subst.
        rewrite (UIP_refl x0). reflexivity. }
      { destruct H0. subst.
        simpl in *. congruence. } }
    { destruct (member_case b).
      { exfalso. destruct H0. subst. simpl in *. congruence. }
      { destruct H0. subst. simpl in *.
        inversion H; clear H; subst.
        eapply IHa in H1. f_equal. assumption. } }
  Qed.

  Fixpoint nth_member (ls : list T) (n : nat) {struct n}
  : option { x : T & member x ls } :=
    match ls as ls return option { x : T & member x ls } with
      | nil => None
      | l :: ls =>
        match n with
          | 0 => Some (@existT _ (fun x => member x (l :: ls)) l (MZ _ _))
          | S n =>
            match nth_member ls n with
              | Some (existT v m) => Some (@existT _ _ v (MN _ m))
              | None => None
            end
        end
    end.

  Definition get_next ls y x (m : member x (y :: ls))
  : option (member x ls) :=
    match m in member _ ls'
          return match ls' with
                   | nil => unit
                   | l' :: ls' => option (member x ls')
                 end
    with
      | MZ _ => None
      | MN _ _ m => Some m
    end.

  Instance Injective_MN x y ls m m' : Injective (@MN x y ls m = @MN x y ls m').
  Proof.
  refine {| result := m = m' |}.
    intro.
    assert (get_next (MN y m) = get_next (MN y m')).
    { rewrite H. reflexivity. }
    { simpl in *. inversion H0. reflexivity. }
  Defined.

  Lemma nth_member_nth_error
  : forall ls p,
      nth_member ls (to_nat (projT2 p)) = Some p <->
      nth_error ls (to_nat (projT2 p)) = Some (projT1 p).
  Proof.
    destruct p. simpl in *.
    induction m.
    { simpl. split; auto. }
    { simpl. split.
      { intros. destruct (nth_member ls (to_nat m)); try congruence.
        { destruct s.
          inv_all. subst. inv_all. subst.
          apply IHm. reflexivity. } }
      { intros.
        eapply IHm in H. rewrite H. reflexivity. } }
  Qed.

  Lemma member_In : forall ls (t : T), member t ls -> List.In t ls.
  Proof.
    induction 1; simpl; auto.
  Qed.

End member.