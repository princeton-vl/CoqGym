Require Import RelationClasses.
Require Import Setoid.
Require Import ExtLib.Core.Type.
Require Import ExtLib.Data.Fun.
Require Import ExtLib.Structures.Monads.
Require Import ExtLib.Structures.Proper.
Require Import ExtLib.Structures.MonadLaws.
Require Import ExtLib.Data.Option.
Require Import ExtLib.Data.Monads.OptionMonad.
Require Import ExtLib.Tactics.TypeTac.

Set Implicit Arguments.
Set Strict Implicit.

(*
Section Laws.
  Variable m : Type -> Type.
  Variable Monad_m : Monad m.
  Variable mtype : forall T, type T -> type (m T).
  Variable mtypeOk : forall T (tT : type T), typeOk tT -> typeOk (mtype tT).
  Variable ML_m : MonadLaws Monad_m mtype.

  Section parametric.
    Variable T : Type.
    Variable tT : type T.

    Definition optionT_eq (a b : optionT m T) : Prop :=
      equal (unOptionT a) (unOptionT b).

    Global Instance type_optionT : type (optionT m T) :=
      type_from_equal optionT_eq.

    Variable tokT : typeOk tT.

    Global Instance typeOk_readerT : typeOk type_optionT.
    Proof.
      eapply typeOk_from_equal.
      { simpl. unfold optionT_eq. intros.
        generalize (only_proper _ _ _ H); intros.
        split; solve_equal. }
      { red. unfold equal; simpl. unfold optionT_eq; simpl.
        unfold Morphisms.respectful; simpl. symmetry. auto. }
      { red. unfold equal; simpl. unfold optionT_eq; simpl.
        unfold Morphisms.respectful; simpl. intros.
        etransitivity; eauto. }
    Qed.

    Global Instance proper_unOptionT : proper (@unOptionT m T).
    Proof. do 3 red; eauto. Qed.

    Global Instance proper_mkOptionT : proper (@mkOptionT m T).
    Proof. do 5 red; eauto. Qed.
  End parametric.

  Theorem equal_match : forall (A B : Type) (eA : type A) (eB : type B),
    typeOk eA -> typeOk eB ->
    forall (x y : option A) (a b : B) (f g : A -> B),
      equal x y ->
      equal a b ->
      equal f g ->
      equal match x with
              | Some a => f a
              | None => a
            end
            match y with
              | Some a => g a
              | None => b
            end.
  Proof.
    destruct x; destruct y; intros; eauto with typeclass_instances; type_tac.
    { inversion H1. assumption. }
    { inversion H1. }
    { inversion H1. }
  Qed.

  Instance proper_match : forall (A B : Type) (eA : type A) (eB : type B),
    typeOk eA -> typeOk eB ->
    forall (x : option A),
    proper x ->
    forall f : A -> optionT m B,
      proper f ->
      proper match x with
               | Some a => unOptionT (f a)
               | None => ret None
             end.
  Proof.
    destruct x; intros; eauto with typeclass_instances; type_tac.
  Qed.

  Global Instance MonadLaws_optionT : MonadLaws (@Monad_optionT _ Monad_m) type_optionT.
  Proof.
    constructor.
    { (* bind_of_return *)
      intros. do 3 red. unfold bind, optionT_eq; simpl.
      rewrite bind_of_return; eauto with typeclass_instances; type_tac.
      eapply equal_match; eauto with typeclass_instances; type_tac. }
    { (* return_of_bind *)
      simpl; unfold optionT_eq; simpl; intros.
      rewrite return_of_bind; eauto with typeclass_instances; intros; type_tac.
      destruct x; type_tac. }
    { (* bind_associativity *)
      simpl; unfold optionT_eq; simpl; intros.
      rewrite bind_associativity; eauto with typeclass_instances; intros; type_tac.
      destruct x; destruct y; try solve [ inversion H5 ]; type_tac.
      inversion H5; assumption.
      eapply equal_match; eauto with typeclass_instances; type_tac.
      rewrite bind_of_return; eauto with typeclass_instances; type_tac.
      eapply equal_match; eauto with typeclass_instances; type_tac.
      eapply equal_match; eauto with typeclass_instances; type_tac.
      eapply equal_match; eauto with typeclass_instances; type_tac. }
    { simpl; unfold optionT_eq; simpl; intros. red; simpl; intros. type_tac. }
    { simpl; unfold optionT_eq; simpl; intros. red; simpl; intros.
      red; simpl; intros. type_tac.
      eapply equal_match; eauto with typeclass_instances; type_tac. }
  Qed.

(*  Theorem equal_match_option : forall T U (tT : type T) (tU : type U),
    typeOk tT -> typeOk tU ->
    forall (a b : option T) (f g : T -> U) (x y : U),
      equal a b -> equal f g -> equal x y ->
      equal match a with
              | Some a => f a
              | None => x
            end
            match b with
              | Some b => g b
              | None => y
            end.
  Proof.
    clear. destruct a; destruct b; simpl; intros; try contradiction; auto.
  Qed.
*)

  Global Instance MonadTLaws_optionT : MonadTLaws _ _ _ _ (@MonadT_optionT _ Monad_m).
  Proof.
    constructor.
    { simpl. unfold optionT_eq; simpl; intros.
      unfold liftM. rewrite bind_of_return; eauto with typeclass_instances; type_tac. }
    { simpl; unfold lift, optionT_eq; simpl; intros.
      unfold liftM.
      rewrite bind_associativity; eauto with typeclass_instances; type_tac.
      rewrite bind_associativity; eauto with typeclass_instances; type_tac.
      rewrite bind_of_return; eauto with typeclass_instances; type_tac.
      eapply equal_match; eauto with typeclass_instances; type_tac.
      eapply equal_match; eauto with typeclass_instances; type_tac. }
    { unfold lift, liftM; simpl; intros. unfold liftM. red; simpl; intros.
      unfold optionT_eq; simpl. type_tac. }
  Qed.

  Global Instance MonadReaderLaws_optionT (s : Type) (t : type s) (tT : typeOk t) (Mr : MonadReader s m) (MLr : MonadReaderLaws Monad_m _ _ Mr) : MonadReaderLaws _ _ _ (@Reader_optionT _ _ _ Mr).
  Proof.
    constructor.
    { simpl. unfold optionT_eq; simpl; intros; unfold liftM.
      rewrite local_bind; eauto with typeclass_instances.
      (erewrite bind_proper; [ | | | | eapply ask_local | ]); eauto with typeclass_instances.
      rewrite bind_associativity; eauto with typeclass_instances.
      rewrite bind_associativity; eauto with typeclass_instances.
      type_tac. 6: eapply preflexive.
      repeat rewrite bind_of_return; eauto with typeclass_instances.
      rewrite local_ret; eauto with typeclass_instances. type_tac.
      type_tac. eapply equal_match; eauto with typeclass_instances; type_tac.
      apply proper_fun; intros. repeat rewrite local_ret; eauto with typeclass_instances.
      type_tac; eauto with typeclass_instances. type_tac.
      type_tac. eapply equal_match; eauto with typeclass_instances; type_tac.
      type_tac.
      apply proper_fun; intros. repeat rewrite local_ret; eauto with typeclass_instances.
      type_tac. eauto with typeclass_instances.
      type_tac. type_tac. }
    { simpl. unfold optionT_eq; simpl; intros; unfold liftM.
      rewrite local_bind; eauto with typeclass_instances.
      type_tac.
      destruct x; destruct y; try solve [ inversion H4 ]; type_tac.
      inversion H4; assumption.
      rewrite local_ret; eauto with typeclass_instances; type_tac.
      type_tac. eapply equal_match; eauto with typeclass_instances; type_tac. }
    { simpl. unfold optionT_eq; simpl; intros; unfold liftM.
      rewrite local_ret; eauto with typeclass_instances; type_tac. }
    { simpl. unfold optionT_eq; simpl; intros; unfold liftM.
      rewrite local_local; eauto with typeclass_instances; type_tac. }
    { unfold local; simpl; intros. red. red. intros. red in H0.
      red; simpl. type_tac. }
    { Opaque lift. unfold ask; simpl; intros. red. type_tac.
      eapply lift_proper; eauto with typeclass_instances. Transparent lift. }
  Qed.

(*
  Global Instance MonadStateLaws_optionT (s : Type) (t : type s) (tT : typeOk t) (Ms : MonadState s m) (MLs : MonadStateLaws Monad_m _ _ Ms) : MonadStateLaws _ _ _ (@State_optionT _ _ _ Ms).
  Proof.
    constructor.
    { simpl; unfold optionT_eq; simpl; intros; unfold liftM; simpl.
      rewrite bind_associativity; eauto with typeclass_instances; type_tac.
      erewrite bind_proper; eauto with typeclass_instances.
      2: instantiate (1 := get); type_tac.
      instantiate (1 := fun a => bind (put a) (fun x : unit => ret (Some x))).
      { rewrite <- bind_associativity; eauto with typeclass_instances; type_tac.
        erewrite bind_proper; eauto with typeclass_instances.
        2: eapply get_put; eauto with typeclass_instances.
        rewrite bind_of_return; eauto with typeclass_instances.
        instantiate (1 := fun x => ret (Some x)). simpl. type_tac.
        type_tac. type_tac. }
      { type_tac. rewrite bind_of_return; eauto with typeclass_instances.
        type_tac. type_tac.
        eapply equal_match_option; eauto with typeclass_instances; type_tac. }
      { eapply equal_match_option; eauto with typeclass_instances; type_tac. } }
    { simpl; unfold optionT_eq; simpl; intros; unfold liftM; simpl.
      repeat rewrite bind_associativity; eauto with typeclass_instances;
        try solve [ type_tac; eapply equal_match_option; eauto with typeclass_instances; type_tac ].
      rewrite bind_proper; eauto with typeclass_instances.
      2: eapply preflexive; eauto with typeclass_instances; type_tac.
      instantiate (1 := fun a : unit => bind get (fun x0 : s => ret (Some x0))).
      { rewrite <- bind_associativity; eauto with typeclass_instances.
        Require Import MonadTac.
        {
          Ltac cl := eauto with typeclass_instances.
          Ltac tcl := solve [ cl ].
Ltac monad_rewrite t :=
          first [ t
                | rewrite bind_rw_0; [ | tcl | tcl | tcl | t | type_tac ]
                | rewrite bind_rw_1 ].
monad_rewrite ltac:(eapply put_get; eauto with typeclass_instances).
rewrite bind_associativity; cl; try solve_proper.
rewrite bind_rw_1; [ | tcl | tcl | tcl | intros | type_tac ].
Focus 2.
etransitivity. eapply bind_of_return; cl; type_tac.
instantiate (1 := fun _ => ret (Some x)). simpl. type_tac.
Add Parametric Morphism (T : Type) (tT : type T) (tokT : typeOk tT) : (@equal _ tT)
  with signature (equal ==> equal ==> iff)
  as equal_mor.
Proof.
  clear - tokT. intros. split; intros.
  { etransitivity. symmetry; eassumption. etransitivity; eassumption. }
  { etransitivity; eauto. etransitivity; eauto. symmetry; auto. }
Qed.
Add Parametric Morphism (T : Type) (tT : type T) (tokT : typeOk tT) : (@equal _ tT)
  with signature (equal ==> eq ==> iff)
  as equal_left_mor.
Proof.
  clear - tokT. intros. split; intros.
  { etransitivity. symmetry; eassumption. eassumption. }
  { etransitivity; eauto. }
Qed.
Add Parametric Morphism (T : Type) (tT : type T) (tokT : typeOk tT) : (@equal _ tT)
  with signature (eq ==> equal ==> iff)
  as equal_right_mor.
Proof.
  clear - tokT. intros. split; intros.
  { etransitivity. eassumption. eassumption. }
  { etransitivity; eauto. symmetry; auto. }
Qed.
assert (Morphisms.Proper (equal ==> Basics.flip Basics.impl)
                (equal (bind (put x) (fun _ : unit => ret (Some x))))) by cl.
assert (Morphisms.Proper
                (Morphisms.pointwise_relation unit equal ==> equal)
                (bind (@put _ _ Ms x))).
{ red. red. intros. eapply bind_proper; cl. solve_proper.
  red; simpl. red in H1. red.

assert bind_proper.
debug eauto with typeclass_instances.


setoid_rewrite bind_of_return.
2: rewrite bind_of_return; eauto with typeclass_instances; type_tac.

        rewrite bind_rw_0
        3: instantiate (1 := (bind (put x) (fun _ : unit => get))).




        Theorem bind_rw_0 : forall A B (tA : type A) (tB : type B),
          typeOk tA -> typeOk tB ->
          forall (x z : m A) (y : A -> m B)z,
            equal x z ->
            proper y ->
            equal (bind x y) (bind z y).
        Proof.


 }
      { type_tac. rewrite bind_of_return; eauto with typeclass_instances; type_tac.
        eapply equal_match_option; eauto with typeclass_instances; type_tac. } }


      Print MonadStateLaws.
*)

  Global Instance MonadZeroLaws_optionT : MonadZeroLaws (@Monad_optionT _ Monad_m) type_optionT _.
  Proof.
    constructor.
    { simpl; unfold optionT_eq; simpl; intros.
      rewrite bind_of_return; eauto with typeclass_instances; type_tac.
      eapply equal_match; eauto with typeclass_instances; type_tac. }
    { unfold mzero; simpl; intros. red; simpl. type_tac. }
  Qed.

End Laws.
*)