Set Implicit Arguments.

Require Import util.
Require list_utils.
Require Import List.
Require Import monads.

Record Monoid: Type :=
  { monoid_type:> Set
  ; monoid_zero: monoid_type
  ; monoid_mult: monoid_type -> monoid_type -> monoid_type
  ; monoid_lunit: forall x, monoid_mult monoid_zero x = x
  ; monoid_runit: forall x, monoid_mult x monoid_zero = x
  ; monoid_assoc: forall x y z, monoid_mult (monoid_mult x y) z = monoid_mult x (monoid_mult y z)
  }.

Record monoidHomo (m n: Monoid) (f: m -> n): Prop :=
  { monoidHomo_zero: f (monoid_zero m) = (monoid_zero n)
  ; monoidHomo_mult: forall x y, f (monoid_mult m x y) = monoid_mult n (f x) (f y)
  }.

Lemma monoidHomo_refl (m: Monoid): monoidHomo m m (fun x => x).
Proof. intros. apply Build_monoidHomo; auto. Qed.

Module MonoidMonadTrans.
Section MonoidMonadTrans.

  Variable monoid: Monoid.

  Section NewMonad.

    Variable monad: Monad.
    Hypothesis ext: extMonad monad.

    Let C_MMT (T: Set): Set := monad (prod monoid T).

    Let bind_MMT (A B: Set) (a: C_MMT A) (ab: A -> C_MMT B): C_MMT B :=
      x <- a ; y <- ab (snd x) ;
      ret (monoid_mult monoid (fst x) (fst y), snd y).

    Let ret_MMT (T: Set): T -> C_MMT T := ret ∘ pair (monoid_zero monoid).

    Definition M: Monad.
    Proof with simpl; auto.
      apply (Build_Monad C_MMT bind_MMT ret_MMT); intros.
          (* one unit *)
          unfold ret_MMT, bind_MMT, compose.
          simpl.
          rewrite mon_lunit.
          simpl.
          assert (ext_eq (fun y: prod monoid b => monads.ret (m:=monad) (monoid_mult monoid (monoid_zero monoid) (fst y), snd y)) ret).
            intro.
            rewrite monoid_lunit.
            destruct x0...
          rewrite (ext _ H (f x)).
          rewrite mon_runit...
        (* the other unit *)
        unfold ret_MMT, bind_MMT, compose.
        simpl.
        rewrite mon_lunit_under_bind...
        assert (ext_eq (fun x => monads.ret (m:=monad) (monoid_mult monoid (fst x) (monoid_zero monoid), snd x)) (@monads.ret monad (prod monoid a))).
          intro.
          rewrite monoid_runit.
          destruct x...
        rewrite (ext _ H f).
        rewrite mon_runit...
      (* assoc *)
      unfold bind_MMT.
      rewrite mon_assoc.
      apply (extFlipped ext n (prod monoid c)). intro.
      rewrite mon_assoc.
      rewrite mon_assoc.
      apply (extFlipped ext (f (snd x)) (prod monoid c)). intro.
      rewrite mon_assoc.
      rewrite mon_lunit...
      apply (extFlipped ext (g (snd x0)) (prod monoid c)). intro.
      rewrite mon_lunit.
      rewrite monoid_assoc...
    Defined.

    Lemma bind_toLower' (X V: Set) (f: M V) (g: V -> M X):
      f >>= g =
        x <- f: monad (prod monoid V);
        ((g (snd x): monad (prod monoid X)) >>=
          (ret ∘ (fun q => (monoid_mult monoid (fst x) (fst q), snd q)))).
    Proof. auto. Qed.

    Lemma bind_toLower (X V: Set) (f: M V) (g: V -> M X):
      f >>= g =
        x <- f: monad (prod monoid V);
        y <- g (snd x): monad (prod monoid X);
        ret (m:=monad) (monoid_mult monoid (fst x) (fst y), snd y).
    Proof. auto. Qed.

    Definition ret_toLower (X: Set) (x: X): @ret M X x = ret (m:=monad) (monoid_zero monoid, x).
    Proof. auto. Qed.

    Lemma mon_toLower: forall X, M X = monad (prod monoid X).
    Proof. auto. Qed.

    Lemma Mext: extMonad M.
    Proof with auto.
      unfold extMonad.
      intros.
      simpl.
      unfold bind_MMT.
      simpl in x.
      unfold C_MMT in x.
      set ext.
      unfold extMonad in e.
      apply (e (prod monoid A) (prod monoid B)).
      intro.
      unfold ext_eq in H.
      rewrite H...
    Qed.

    Definition lift (A: Set) (a: monad A): M A := a >>= (ret ∘ pair (monoid_zero monoid)).

  End NewMonad.

  Definition T: MonadTrans := Build_MonadTrans M lift.

End MonoidMonadTrans.
End MonoidMonadTrans.

Definition NatAddMonoid: Monoid.
Proof with auto with arith.
  apply (Build_Monoid 0 plus)...
Defined.

Definition SimplyProfiled: Monad := MonoidMonadTrans.M NatAddMonoid IdMonad.ext.

Definition cost {X: Set}: prod nat X -> nat := @fst _ _.
Definition result X: SimplyProfiled X -> X := @snd _ _.

Lemma bind_cost (T U: Set) (a: SimplyProfiled T) (b: T -> SimplyProfiled U):
  cost (bind a b) = cost a + cost (b (result a)).
Proof with auto.
  intros.
  destruct a.
  simpl.
  destruct (b t)...
Qed.

Lemma return_cost (T: Set) (x: T): cost (@ret SimplyProfiled T x) = 0.
Proof. auto. Qed.

Lemma SimplyProfiled_ext: extMonad SimplyProfiled.
  unfold SimplyProfiled.
  intro.
  simpl.
  unfold IdMonad.C.
  unfold IdMonad.bind.
  unfold IdMonad.ret.
  intros.
  rewrite (H (snd x)).
  reflexivity.
Qed.

Module ListMonoid.
Section ListMonoid.

  Variable T: Set.

  Definition M: Monoid :=
    Build_Monoid (@nil T) (@app T) (@refl_equal (list T)) (@list_utils.app_nil_r T) (@app_ass T).

End ListMonoid.
End ListMonoid.

