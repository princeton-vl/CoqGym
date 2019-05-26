Require Import Relations.
Require Import ExtLib.Data.Fun.
Require Import ExtLib.Structures.Proper.
Require Import ExtLib.Structures.Monad.
Require Import ExtLib.Structures.FunctorRelations.
Require Import ExtLib.Structures.MonadLaws.

Set Implicit Arguments.
Set Strict Implicit.

Section stuff.

  Variable m : Type -> Type.
  Variable Monad_m : Monad m.
  Variable mleq : forall T, (T -> T -> Prop) -> m T -> m T -> Prop.
  Variable mproper : forall T (rT : relation T), Proper rT -> Proper (mleq rT).
  Variable FunctorOrder_mleq : FunctorOrder m mleq mproper.
  Variable MonadLaws_mleq : MonadLaws Monad_m mleq mproper.

  Definition compose (A B C : Type) (f : A -> B) (g : B -> C) : A -> C :=
    fun x => g (f x).

  Definition pure (T : Type) : T -> m T := @ret _ _ _.
  Definition fapply (T U : Type) (f : m (T -> U)) (x : m T) : m U :=
    bind f (fun f => bind x (fun x => ret (f x))).

  Existing Instance fun_trans.
  Existing Instance fun_refl.

  Variables A B C : Type.
  Context (rA : relation A) (rB : relation B) (rC : relation C)
          (pA : Proper rA) (pB : Proper rB) (pC : Proper rC).
  Context (Ra : PReflexive rA) (Rb : PReflexive rB) (Rc : PReflexive rC).
  Context (Ta : PTransitive rA) (Tb : PTransitive rB) (Tc : PTransitive rC).

  Instance fun_app_proper (A B : Type) (rA : relation A) (rB : relation B) (pA : Proper rA) (pB : Proper rB) (f : A -> B) x :
    proper f -> proper x ->
    proper (f x).
  Proof.
    intros. apply H. auto.
  Qed.

  Instance fun_abs (A B : Type) (rA : relation A) (rB : relation B) (pA : Proper rA) (pB : Proper rB) (f : A -> B) :
    (forall x, proper x -> proper (f x)) ->
    (forall x y, proper x -> proper y -> rA x y -> rB (f x) (f y)) ->
    proper (fun x => f x).
  Proof.
    intros. split; auto; eapply H.
  Qed.

  Ltac prove_proper x k :=
    match x with
      | _ => match goal with
               | [ H : proper x |- _ ] => k H
             end
      | bind ?A ?B => 
        prove_proper A ltac:(fun a => prove_proper B ltac:(fun b =>
          let H := fresh in
            assert (H : proper x); [ eapply bind_proper; eauto with typeclass_instances | k H ]))
      | ret ?A => 
        prove_proper A ltac:(fun a => 
          let H := fresh in
            assert (H : proper x); [ eapply ret_proper; eauto with typeclass_instances | k H ])
      | (fun x => _) =>
        let H := fresh in 
        assert (H : proper x); [ eapply fun_abs; intros; [ propers | repeat red; intros; prove_mleq ] | k H ]
      | _ => 
        let H := fresh in
          assert (H : proper x); [ eauto with typeclass_instances | k H ]
    end
  with prove_mleq :=
    try match goal with
          | |- proper (fun x => _) =>
            eapply fun_abs; intros; [ propers | repeat red; intros; prove_mleq ]
          | [ R : _ , H' : pfun_ext ?R _ ?F ?G |- ?R (?F _) (?G _) ] =>
            eapply H'; [ propers | propers | prove_mleq ]
          | [ H' : proper ?F |- ?R (?F _) (?F _) ] =>
            eapply H'; [ propers | propers | try assumption; prove_mleq ]
          | [ |- mleq _ (bind _ _) (bind _ _) ] =>
            eapply bind_respectful_leq; [ eauto with typeclass_instances | eauto with typeclass_instances | prove_mleq | intros; prove_mleq ]
          | [ |- mleq _ (ret _) (ret _) ] =>
            eapply ret_respectful_leq; [ eauto with typeclass_instances | eauto with typeclass_instances | prove_mleq ]
          | [ H : proper ?f |- pfun_ext _ _ ?f ?f ] => apply H
          | [ H : proper ?f |- pfun_ext _ _ (fun x => _) (fun y => _) ] => red; intros; prove_mleq
          | _ => eassumption
        end
  with propers :=
    match goal with 
      | |- proper ?X => prove_proper X ltac:(fun x => eapply x)
      | |- mleq _ ?X ?Y =>
        prove_proper X ltac:(fun x => prove_proper Y ltac:(fun x => idtac))
    end.

  Instance PReflexive_stuff : PReflexive 
     (pfun_ext (pfun_ext (pfun_ext rC pA) (Proper_pfun pB pC))
        (Proper_pfun pA pB)).
  Proof. intuition. Qed.

  Theorem bind_law : forall (f : A -> B) (g : B -> C),
    proper f -> proper g ->
    mleq (pfun_ext rC pA)
         (fapply (fapply (pure (@compose A B C)) (pure f)) (pure g))
         (pure (compose f g)).
  Proof.
    unfold fapply, pure, compose; simpl; intros.
    propers. 
    (eapply ptransitive; [ | | | | eapply (@bind_associativity _ _ _ _ MonadLaws_mleq) | ]); eauto with typeclass_instances; propers.
    (eapply ptransitive; [ | | | | eapply (@bind_of_return _ _ _ _ MonadLaws_mleq) | ]); eauto with typeclass_instances; propers.
    (eapply ptransitive; [ | | | | eapply (@bind_associativity _ _ _ _ MonadLaws_mleq) | ]); eauto with typeclass_instances; propers.
    (eapply ptransitive; [ | | | | eapply (@bind_of_return _ _ _ _ MonadLaws_mleq) | ]); eauto with typeclass_instances; propers.
    (eapply ptransitive; [ | | | | eapply (@bind_of_return _ _ _ _ MonadLaws_mleq) | ]); eauto with typeclass_instances; propers.
    (eapply ptransitive; [ | | | | eapply (@bind_of_return _ _ _ _ MonadLaws_mleq) | ]); eauto with typeclass_instances; propers.
    eapply preflexive; eauto with typeclass_instances.
  Qed.

End stuff.

Print Assumptions bind_law.
