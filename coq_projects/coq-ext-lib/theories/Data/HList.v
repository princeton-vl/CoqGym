Require Import Coq.Lists.List.
Require Import Relations RelationClasses.
Require Import ExtLib.Core.Type.
Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Structures.Proper.
Require Import ExtLib.Data.SigT.
Require Import ExtLib.Data.Member.
Require Import ExtLib.Data.ListNth.
Require Import ExtLib.Data.Option.
Require Import ExtLib.Tactics.
Require Import Coq.Classes.Morphisms.

Set Implicit Arguments.
Set Strict Implicit.
Set Asymmetric Patterns.
Set Universe Polymorphism.
Set Printing Universes.

Lemma app_ass_trans@{X}
: forall {T : Type@{X} } (a b c : list T), (a ++ b) ++ c = a ++ b ++ c.
Proof.
  induction a; simpl.
  reflexivity.
  intros. destruct (IHa b c). reflexivity.
Defined.

Lemma app_nil_r_trans : forall {T : Type} (a : list T), a ++ nil = a.
Proof.
  induction a; simpl.
  reflexivity.
  refine match IHa in _ = X return _ = _ :: X with
         | eq_refl => eq_refl
         end.
Defined.

Monomorphic Universe hlist_large.

(** Core Type and Functions **)
Section hlist.
  Polymorphic Universe Ui Uv.

  Context {iT : Type@{Ui}}.
  Variable F : iT -> Type@{Uv}.

  Inductive hlist : list iT -> Type :=
  | Hnil  : hlist nil
  | Hcons : forall l ls, F l -> hlist ls -> hlist (l :: ls).

  Definition hlist_hd {a b} (hl : hlist (a :: b)) : F a :=
    match hl in hlist x return match x return Type@{Uv} with
                               | nil => unit
                               | l :: _ => F l
                               end with
    | Hnil => tt
    | Hcons _ _ x _ => x
    end.

  Definition hlist_tl {a b} (hl : hlist (a :: b)) : hlist b :=
    match hl in hlist x return match x return Type@{hlist_large} with
                                 | nil => unit
                                 | _ :: ls => hlist ls
                               end with
      | Hnil => tt
      | Hcons _ _ _ x => x
    end.

  Lemma hlist_eta : forall ls (h : hlist ls),
    h = match ls as ls return hlist ls -> hlist ls with
        | nil => fun _ => Hnil
        | a :: b => fun h => Hcons (hlist_hd h) (hlist_tl h)
        end h.
  Proof.
    intros. destruct h; auto.
  Qed.

  Fixpoint hlist_app ll lr (h : hlist ll) : hlist lr -> hlist (ll ++ lr) :=
    match h in hlist ll return hlist lr -> hlist (ll ++ lr) with
    | Hnil => fun x => x
    | Hcons _ _ hd tl => fun r => Hcons hd (hlist_app tl r)
    end.

  Lemma hlist_app_nil_r
  : forall ls (h : hlist ls),
      hlist_app h Hnil =
      match eq_sym (app_nil_r_trans ls) in _ = t return hlist t with
      | eq_refl => h
      end.
  Proof.
    induction h; simpl; intros; auto.
    rewrite IHh at 1.
    unfold eq_trans. unfold f_equal. unfold eq_sym.
    clear. revert h.
    generalize dependent (app_nil_r_trans ls).
    destruct e. reflexivity.
  Qed.

  Fixpoint hlist_rev' ls ls' (h : hlist ls) : hlist ls' -> hlist (rev ls ++ ls') :=
    match h in hlist ls return hlist ls' -> hlist (rev ls ++ ls') with
    | Hnil => fun h => h
    | Hcons l ls0 x h' => fun hacc =>
      match app_ass_trans (rev ls0) (l :: nil) ls' in _ = t
            return hlist t -> hlist _
      with
      | eq_refl => fun x => x
      end (@hlist_rev' _ (l :: ls') h' (Hcons x hacc))
    end.

  Definition hlist_rev ls (h : hlist ls) : hlist (rev ls) :=
    match app_nil_r_trans (rev ls) in _ = t return hlist t with
      | eq_refl => hlist_rev' h Hnil
    end.

  Lemma hlist_rev_nil : hlist_rev Hnil = Hnil.
  Proof.
    reflexivity.
  Qed.

  (** TODO: I need hlist_rev_cons **)

  (** Equivalence **)
  (** TODO: This should change to relations **)
  Section equiv.
    Variable eqv : forall x, relation (F x).

    Inductive equiv_hlist : forall ls, hlist ls -> hlist ls -> Prop :=
    | hlist_eqv_nil : equiv_hlist Hnil Hnil
    | hlist_eqv_cons : forall l ls x y h1 h2, eqv x y -> equiv_hlist h1 h2 ->
      @equiv_hlist (l :: ls) (Hcons x h1) (Hcons y h2).

    Global Instance Reflexive_equiv_hlist (R : forall t, Reflexive (@eqv t)) ls
    : Reflexive (@equiv_hlist ls).
    Proof.
      red. induction x; constructor; auto. reflexivity.
    Qed.

    Global Instance Symmetric_equiv_hlist (R : forall t, Symmetric (@eqv t)) ls
    : Symmetric (@equiv_hlist ls).
    Proof.
      red. induction 1.
      { constructor. }
      { constructor. symmetry. assumption. auto. }
    Qed.

    Global Instance Transitive_equiv_hlist (R : forall t, Transitive (@eqv t)) ls
    : Transitive (@equiv_hlist ls).
    Proof.
      red. induction 1.
      { intro; assumption. }
      { rewrite (hlist_eta z).
        refine
          (fun H' =>
             match H' in @equiv_hlist ls X Y
                   return
                   match ls as ls return hlist ls -> hlist ls -> Prop with
                     | nil => fun _ _ : hlist nil => True
                     | l :: ls => fun (X Y : hlist (l :: ls)) =>
                                    forall Z x xs,
                                      eqv (hlist_hd Z) (hlist_hd X) ->
                                      equiv_hlist xs (hlist_tl X) ->
                                      (forall z : hlist ls,
                                         equiv_hlist (hlist_tl X) z ->
                                         equiv_hlist (hlist_tl Z) z) ->
                                      @equiv_hlist (l :: ls) Z Y
                   end X Y
             with
               | hlist_eqv_nil => I
               | hlist_eqv_cons l ls x y h1 h2 pf pf' => _
             end (Hcons x h1) x _ H H0 (@IHequiv_hlist)).
        intros. rewrite (hlist_eta Z).
        constructor. simpl in *. etransitivity. eassumption. eassumption.
        eapply H3. simpl in *. eassumption. }
    Qed.

    Lemma equiv_hlist_Hcons
    : forall ls i a b (c : hlist ls) d,
        equiv_hlist (Hcons a c) (@Hcons i ls b d) ->
        (@eqv i a b /\ equiv_hlist c d).
    Proof.
      clear. intros.
      refine
        match H in @equiv_hlist ls' l r
              return match ls' as ls' return hlist ls' -> hlist ls' -> _ with
                       | nil => fun _ _ => True
                       | l :: ls => fun l r =>
                                      eqv (hlist_hd l) (hlist_hd r) /\
                                      equiv_hlist (hlist_tl l) (hlist_tl r)
                     end l r
        with
          | hlist_eqv_nil => I
          | hlist_eqv_cons _ _ _ _ _ _ pf pf' => conj pf pf'
        end.
    Defined.

    Lemma equiv_hlist_app
    : forall a b (c c' : hlist a)  (d d' : hlist b),
        (equiv_hlist c c' /\ equiv_hlist d d')
        <->
        equiv_hlist (hlist_app c d) (hlist_app c' d').
    Proof.
      clear. split.
      - destruct 1.
        induction H.
        + assumption.
        + simpl. constructor; auto.
      - induction c.
        + rewrite (hlist_eta c').
          simpl; intros; split; auto. constructor.
        + rewrite (hlist_eta c'); simpl.
          specialize (IHc (hlist_tl c')).
          intro.
          eapply equiv_hlist_Hcons in H. intuition.
          constructor; auto.
    Qed.

    Global Instance Injection_equiv_hlist_cons ls i a b (c : hlist ls) d
    : Injective (equiv_hlist (Hcons a c) (@Hcons i ls b d)) :=
    { result := @eqv i a b /\ equiv_hlist c d
    ; injection := @equiv_hlist_Hcons _ _ _ _ _ _ }.

    Global Instance Injection_equiv_hlist_app a b (c c' : hlist a) (d d' : hlist b)
    : Injective (equiv_hlist (hlist_app c d) (hlist_app c' d')) :=
    { result := equiv_hlist c c' /\ equiv_hlist d d'
    ; injection := fun x => proj2 (@equiv_hlist_app _ _ _ _ _ _) x }.

  End equiv.

  Lemma hlist_nil_eta : forall (h : hlist nil), h = Hnil.
  Proof.
    intros; rewrite (hlist_eta h); reflexivity.
  Qed.

  Lemma hlist_cons_eta : forall a b (h : hlist (a :: b)),
    h = Hcons (hlist_hd h) (hlist_tl h).
  Proof.
    intros; rewrite (hlist_eta h); reflexivity.
  Qed.

  Lemma Hcons_inv
  : forall l ls a b c d,
      @eq (hlist (l :: ls)) (Hcons a b) (Hcons c d) ->
      a = c /\ b = d.
  Proof.
    intros.
    refine (
        match H as K in _ = Z
              return match Z in hlist LS
                           return match LS with
                                    | nil => Prop
                                    | l :: ls => F l -> hlist ls -> Prop
                                  end
                     with
                       | Hcons X Y x y => fun a b => a = x /\ b = y
                       | Hnil => True
                     end a b
        with
          | eq_refl => conj eq_refl eq_refl
        end).
  Qed.

  Global Instance Injection_hlist_cons ls t (a : F t) (b : hlist ls) c d
  : Injective (Hcons a b = Hcons c d) :=
    { result := a = c /\ b = d
    ; injection := @Hcons_inv t ls a b c d
    }.


  Theorem equiv_eq_eq : forall ls (x y : hlist ls),
                          equiv_hlist (fun x => @eq _) x y <-> x = y.
  Proof.
    induction x; simpl; intros.
    { split. inversion 1. rewrite hlist_nil_eta. reflexivity.
      intros; subst; constructor. }
    { split.
      { intro. rewrite (hlist_eta y).
        specialize (IHx (hlist_tl y)).
        refine (match H in @equiv_hlist _ LS X Y
                      return match X in hlist LS
                                   return F match LS with
                                              | nil => l
                                              | l :: _ => l
                                            end ->
                                          hlist match LS with
                                                  | nil => ls
                                                  | _ :: ls => ls
                                                end ->
                                          Prop
                             with
                               | Hnil => fun _ _ => True
                               | Hcons a b c d => fun x y =>
                                                    (equiv_hlist (fun x0 : iT => eq) d y <-> d = y) ->
                                                    @Hcons a b c d = Hcons x y
                             end (match LS as LS return hlist LS -> F match LS with
                                                                        | nil => l
                                                                        | l :: _ => l
                                                                      end
                                  with
                                    | nil => fun _ => f
                                    | l :: ls => hlist_hd
                                  end Y)
                                 (match LS as LS return hlist LS -> hlist match LS with
                                                                            | nil => ls
                                                                            | _ :: ls => ls
                                                                          end
                                  with
                                    | nil => fun _ => x
                                    | l :: ls => hlist_tl
                                  end Y)
                with
                  | hlist_eqv_nil => I
                  | hlist_eqv_cons l ls x y h1 h2 pf1 pf2 => _
                end IHx).
        simpl.
        subst. intros.
        f_equal. apply H0. assumption. }
      { intros; subst. constructor; auto.
        reflexivity. } }
  Qed.

  Fixpoint hlist_get ls a (m : member a ls) : hlist ls -> F a :=
    match m in member _ ls return hlist ls -> F a with
      | MZ _ => hlist_hd
      | MN _ _ r => fun hl => hlist_get r (hlist_tl hl)
    end.

  Fixpoint hlist_nth_error {ls} (hs : hlist ls) (n : nat)
    : option (match nth_error ls n with
                | None => unit
                | Some x => F x
              end) :=
    match hs in hlist ls return option (match nth_error ls n with
                                          | None => unit
                                          | Some x => F x
                                        end)
      with
      | Hnil => None
      | Hcons l ls h hs =>
        match n as n return option (match nth_error (l :: ls) n with
                                      | None => unit
                                      | Some x => F x
                                    end)
          with
          | 0 => Some h
          | S n => hlist_nth_error hs n
        end
    end.

  Polymorphic Fixpoint hlist_nth ls (h : hlist ls) (n : nat) :
    match nth_error ls n return Type with
      | None => unit
      | Some t => F t
    end :=
    match h in hlist ls , n as n
      return match nth_error ls n with
               | None => unit
               | Some t => F t
             end
      with
      | Hnil , 0 => tt
      | Hnil , S _ => tt
      | Hcons _ _ x _ , 0 => x
      | Hcons _ _ _ h , S n => hlist_nth h n
    end.

  Fixpoint nth_error_hlist_nth ls (n : nat)
  : option (hlist ls -> match nth_error ls n with
                          | None => Empty_set
                          | Some x => F x
                        end) :=
    match ls as ls
          return option (hlist ls -> match nth_error ls n with
                                       | None => Empty_set
                                       | Some x => F x
                                     end)
    with
      | nil => None
      | l :: ls =>
        match n as n
              return option (hlist (l :: ls) -> match nth_error (l :: ls) n with
                                                  | None => Empty_set
                                                  | Some x => F x
                                                end)
        with
          | 0 => Some hlist_hd
          | S n =>
            match nth_error_hlist_nth ls n with
              | None => None
              | Some f => Some (fun h => f (hlist_tl h))
            end
        end
    end.

  Definition cast1 T l
  : forall (l' : list T) n v,
      nth_error l n = Some v -> Some v = nth_error (l ++ l') n.
  Proof.
    induction l. intros.
    { exfalso. destruct n; inversion H. }
    { destruct n; simpl; intros; auto. }
  Defined.

  Definition cast2 T l
  : forall (l' : list T) n,
      nth_error l n = None ->
      nth_error l' (n - length l) = nth_error (l ++ l') n.
  Proof.
    induction l; simpl.
    { destruct n; simpl; auto. }
    { destruct n; simpl; auto.
      inversion 1. }
  Defined.

  Theorem hlist_nth_hlist_app
  : forall l l' (h : hlist l) (h' : hlist l') n,
    hlist_nth (hlist_app h h') n =
    match nth_error l n as k
      return nth_error l n = k ->
      match nth_error (l ++ l') n return Type with
        | None => unit
        | Some t => F t
      end
    with
      | Some _ => fun pf =>
        match
          cast1 _ _ _ pf in _ = z ,
          eq_sym pf in _ = w
          return match w return Type with
                   | None => unit
                   | Some t => F t
                 end ->
                 match z return Type with
                   | None => unit
                   | Some t => F t
                 end
        with
          | eq_refl , eq_refl => fun x => x
        end (hlist_nth h n)
      | None => fun pf =>
        match cast2 _ _ _ pf in _ = z
          return match z with
                   | Some t => F t
                   | None => unit
                 end
        with
          | eq_refl => hlist_nth h' (n - length l)
        end
    end eq_refl.
  Proof.
    induction h; simpl; intros.
    { destruct n; simpl in *; reflexivity. }
    { destruct n; simpl.
      { reflexivity. }
      { rewrite IHh. reflexivity. } }
  Qed.

  Section type.
    Variable eqv : forall x, type (F x).

    Global Instance type_hlist (ls : list iT): type (hlist ls) :=
    { equal := @equiv_hlist (fun x => @equal _ (eqv x)) ls
    ; proper :=
      (fix recur ls (h : hlist ls) : Prop :=
        match h with
          | Hnil => True
          | Hcons _ _ x y => proper x /\ recur _ y
        end) ls
    }.

    Variable eqvOk : forall x, typeOk (eqv x).

    Global Instance typeOk_hlist (ls : list iT): typeOk (type_hlist ls).
    Proof.
      constructor.
      { induction ls; intros.
        { rewrite (hlist_eta x) in *. rewrite (hlist_eta y) in *.
          clear. compute; auto. }
        { rewrite (hlist_eta x) in *. rewrite (hlist_eta y) in *.
          simpl in H.
          inv_all. eapply IHls in H1.
          eapply only_proper in H0; eauto.
          simpl; tauto. } }
      { intro. induction ls; simpl.
        { rewrite (hlist_eta x); intros; constructor. }
        { rewrite (hlist_eta x); intros; intuition; constructor.
          eapply preflexive; [ | eauto with typeclass_instances ].
          eauto with typeclass_instances.
          eapply IHls; eauto. } }
      { red. induction 1.
        { constructor. }
        { constructor. symmetry. assumption. assumption. } }
      { red. induction 1.
        { auto. }
        { intro H1.
          etransitivity; [ | eassumption ].
          constructor; eauto. } }
    Qed.

    Global Instance proper_hlist_app l l' : proper (@hlist_app l l').
    Proof.
      do 6 red. induction 1; simpl; auto.
      { intros. constructor; eauto.
        eapply IHequiv_hlist. exact H1. }
    Qed.

    Lemma hlist_app_assoc : forall ls ls' ls''
                                 (a : hlist ls) (b : hlist ls') (c : hlist ls''),
      hlist_app (hlist_app a b) c =
      match eq_sym (app_ass_trans ls ls' ls'') in _ = t return hlist t with
        | eq_refl => hlist_app a (hlist_app b c)
      end.
    Proof.
      intros ls ls' ls''.
      generalize (eq_sym (app_assoc_reverse ls ls' ls'')).
      induction ls; simpl; intros.
      { rewrite (hlist_eta a); simpl.
        reflexivity. }
      { rewrite (hlist_eta a0). simpl.
        inversion H.
        erewrite (IHls H1).
        unfold f_equal. unfold eq_trans. unfold eq_sym.
        generalize (app_ass_trans ls ls' ls'').
        rewrite <- H1.
        clear. intro.
        generalize dependent (hlist_app (hlist_tl a0) (hlist_app b c)).
        destruct e. reflexivity. }
    Qed.

    Lemma hlist_app_assoc'
      : forall (ls ls' ls'' : list iT)
               (a : hlist ls) (b : hlist ls') (c : hlist ls''),
        hlist_app a (hlist_app b c) =
        match
          app_ass_trans ls ls' ls'' in (_ = t) return (hlist t)
        with
        | eq_refl => hlist_app (hlist_app a b) c
        end.
    Proof.
      clear. intros.
      generalize (hlist_app_assoc a b c).
      generalize (hlist_app (hlist_app a b) c).
      generalize (hlist_app a (hlist_app b c)).
      destruct (app_ass_trans ls ls' ls'').
      simpl. auto.
    Qed.

    Fixpoint hlist_split ls ls' : hlist (ls ++ ls') -> hlist ls * hlist ls' :=
      match ls as ls return hlist (ls ++ ls') -> hlist ls * hlist ls' with
        | nil => fun h => (Hnil, h)
        | l :: ls => fun h =>
                       let (a,b) := @hlist_split ls ls' (hlist_tl h) in
                       (Hcons (hlist_hd h) a, b)
      end.

    Lemma hlist_app_hlist_split : forall ls' ls (h : hlist (ls ++ ls')),
      hlist_app (fst (hlist_split ls ls' h)) (snd (hlist_split ls ls' h)) = h.
    Proof.
      induction ls; simpl; intros; auto.
      rewrite (hlist_eta h); simpl.
      specialize (IHls (hlist_tl h)).
      destruct (hlist_split ls ls' (hlist_tl h)); simpl in *; auto.
      f_equal. auto.
    Qed.

    Lemma hlist_split_hlist_app : forall ls' ls (h : hlist ls) (h' : hlist ls'),
      hlist_split _ _ (hlist_app h h') = (h,h').
    Proof.
      induction ls; simpl; intros.
      { rewrite (hlist_eta h); simpl; auto. }
      { rewrite (hlist_eta h); simpl.
        rewrite IHls. reflexivity. }
    Qed.

  End type.

  Lemma hlist_hd_fst_hlist_split
  : forall t (xs ys : list _) (h : hlist (t :: xs ++ ys)),
      hlist_hd (fst (hlist_split (t :: xs) ys h)) = hlist_hd h.
  Proof.
    simpl. intros.
    match goal with
    | |- context [ match ?X with _ => _ end ] =>
      destruct X
    end. reflexivity.
  Qed.

  Lemma hlist_tl_fst_hlist_split
  : forall t (xs ys : list _) (h : hlist (t :: xs ++ ys)),
      hlist_tl (fst (hlist_split (t :: xs) ys h)) =
      fst (hlist_split xs ys (hlist_tl h)).
  Proof.
    simpl. intros.
    match goal with
    | |- context [ match ?X with _ => _ end ] =>
      remember X
    end. destruct p. simpl.
    change h0 with (fst (h0, h1)).
    f_equal; trivial.
  Qed.

  Lemma hlist_tl_snd_hlist_split
  : forall t (xs ys : list _) (h : hlist (t :: xs ++ ys)),
      snd (hlist_split xs ys (hlist_tl h)) =
      snd (hlist_split (t :: xs) ys h).
  Proof.
    simpl. intros.
    match goal with
    | |- context [ match ?X with _ => _ end ] =>
      remember X
    end. destruct p.
    simpl.
    change h1 with (snd (h0, h1)).
    rewrite Heqp. reflexivity.
  Qed.

  Polymorphic Fixpoint nth_error_get_hlist_nth (ls : list iT) (n : nat) {struct ls} :
    option {t : iT & hlist ls -> F t} :=
    match
      ls as ls0
      return option {t : iT & hlist ls0 -> F t}
    with
      | nil => None
      | l :: ls0 =>
        match
          n as n0
          return option {t : iT & hlist (l :: ls0) -> F t}
        with
          | 0 =>
            Some (@existT _ (fun t => hlist (l :: ls0) -> F t)
                          l (@hlist_hd _ _))
          | S n0 =>
            match nth_error_get_hlist_nth ls0 n0 with
              | Some (existT x f) =>
                Some (@existT _ (fun t => hlist _ -> F t)
                              x (fun h : hlist (l :: ls0) => f (hlist_tl h)))
              | None => None
            end
        end
    end.

  Theorem nth_error_get_hlist_nth_Some
    : forall ls n s,
      nth_error_get_hlist_nth ls n = Some s ->
      exists pf : nth_error ls n = Some (projT1 s),
      forall h, projT2 s h = match pf in _ = t
                                   return match t return Type with
                                            | Some t => F t
                                            | None => unit
                                          end
                             with
                               | eq_refl => hlist_nth h n
                             end.
  Proof.
    induction ls; simpl; intros; try congruence.
    { destruct n.
      { inv_all; subst; simpl.
        exists (eq_refl).
        intros. rewrite (hlist_eta h). reflexivity. }
      { forward. inv_all; subst.
        destruct (IHls _ _ H0); clear IHls.
        simpl in *. exists x0.
        intros.
        rewrite (hlist_eta h). simpl. auto. } }
  Qed.

  Theorem nth_error_get_hlist_nth_None
  : forall ls n,
      nth_error_get_hlist_nth ls n = None <->
      nth_error ls n = None.
  Proof.
    induction ls; simpl; intros; try congruence.
    { destruct n; intuition. }
    { destruct n; simpl; try solve [ intuition congruence ].
      specialize (IHls n). forward. }
  Qed.

  Lemma nth_error_get_hlist_nth_weaken
  : forall ls ls' n x,
      nth_error_get_hlist_nth ls n = Some x ->
      exists z,
        nth_error_get_hlist_nth (ls ++ ls') n =
        Some (@existT iT (fun t => hlist (ls ++ ls') -> F t) (projT1 x) z)
        /\ forall h h', projT2 x h = z (hlist_app h h').
  Proof.
    intros ls ls'. revert ls.
    induction ls; simpl; intros; try congruence.
    { destruct n; inv_all; subst.
      { simpl. eexists; split; eauto.
        intros. rewrite (hlist_eta h). reflexivity. }
      { forward. inv_all; subst. simpl.
        apply IHls in H0. forward_reason.
        rewrite H. eexists; split; eauto.
        intros. rewrite (hlist_eta h). simpl in *.
        auto. } }
  Qed.

  Lemma nth_error_get_hlist_nth_appL
  : forall tvs' tvs n,
      n < length tvs ->
      exists x,
        nth_error_get_hlist_nth (tvs ++ tvs') n = Some x /\
        exists y,
          nth_error_get_hlist_nth tvs n = Some (@existT _ _ (projT1 x) y) /\
          forall vs vs',
            (projT2 x) (hlist_app vs vs') = y vs.
  Proof.
    clear. induction tvs; simpl; intros.
    { exfalso; inversion H. }
    { destruct n.
      { clear H IHtvs.
        eexists; split; eauto. eexists; split; eauto.
        simpl. intros. rewrite (hlist_eta vs). reflexivity. }
      { apply Lt.lt_S_n in H.
        { specialize (IHtvs _ H).
          forward_reason.
          rewrite H0. rewrite H1.
          forward. subst. simpl in *.
          eexists; split; eauto.
          eexists; split; eauto. simpl.
          intros. rewrite (hlist_eta vs). simpl. auto. } } }
  Qed.

  Lemma nth_error_get_hlist_nth_appR
  : forall tvs' tvs n x,
      n >= length tvs ->
      nth_error_get_hlist_nth (tvs ++ tvs') n = Some x ->
      exists y,
        nth_error_get_hlist_nth tvs' (n - length tvs) = Some (@existT _ _ (projT1 x) y) /\
        forall vs vs',
          (projT2 x) (hlist_app vs vs') = y vs'.
  Proof.
    clear. induction tvs; simpl; intros.
    { rewrite <- Minus.minus_n_O.
      rewrite H0. destruct x. simpl.
      eexists; split; eauto. intros.
      rewrite (hlist_eta vs). reflexivity. }
    { destruct n.
      { inversion H. }
      { assert (n >= length tvs) by (eapply le_S_n; eassumption). clear H.
        { forward. inv_all; subst. simpl in *.
          specialize (IHtvs _ _ H1 H0).
          simpl in *.
          forward_reason.
          rewrite H.
          eexists; split; eauto.
          intros. rewrite (hlist_eta vs). simpl. auto. } } }
  Qed.

End hlist.

Arguments Hnil {_ _}.
Arguments Hcons {_ _ _ _} _ _.
Arguments equiv_hlist {_ F} R {_} _ _ : rename.

(** Weak Map
 ** This is weak because it does not change the key type
 **)
Section hlist_map.
  Variable A : Type.
  Variables F G : A -> Type.
  Variable ff : forall x, F x -> G x.

  Fixpoint hlist_map (ls : list A) (hl : hlist F ls) {struct hl} : hlist G ls :=
    match hl in @hlist _ _ ls return hlist G ls with
      | Hnil => Hnil
      | Hcons _ _ hd tl =>
        Hcons (ff hd) (hlist_map tl)
    end.

  Theorem hlist_app_hlist_map
    : forall ls ls' (a : hlist F ls) (b : hlist F ls'),
      hlist_map (hlist_app a b) =
      hlist_app (hlist_map a) (hlist_map b).
  Proof.
    induction a. simpl; auto.
    simpl. intros. f_equal. auto.
  Qed.

End hlist_map.

Arguments hlist_map {_ _ _} _ {_} _.


Section hlist_map_rules.
  Variable A : Type.
  Variables F G G' : A -> Type.
  Variable ff : forall x, F x -> G x.
  Variable gg : forall x, G x -> G' x.

  Theorem hlist_map_hlist_map : forall ls (hl : hlist F ls),
      hlist_map gg (hlist_map ff hl) = hlist_map (fun _ x => gg (ff x)) hl.
  Proof.
    induction hl; simpl; f_equal. assumption.
  Defined.

  Theorem hlist_get_hlist_map : forall ls t (hl : hlist F ls) (m : member t ls),
      hlist_get m (hlist_map ff hl) = ff (hlist_get m hl).
  Proof.
    induction m; simpl.
    { rewrite (hlist_eta hl). reflexivity. }
    { rewrite (hlist_eta hl). simpl. auto. }
  Defined.

  Lemma hlist_map_ext : forall (ff gg : forall x, F x -> G x),
      (forall x t, ff x t = gg x t) ->
      forall ls (hl : hlist F ls),
        hlist_map ff hl = hlist_map gg hl.
  Proof.
    induction hl; simpl; auto.
    intros. f_equal; auto.
  Defined.

End hlist_map_rules.

Lemma equiv_hlist_map
: forall T U (F : T -> Type) (R : forall t, F t -> F t -> Prop)
         (R' : forall t, U t -> U t -> Prop)
         (f g : forall t, F t -> U t),
    (forall t (x y : F t), R t x y -> R' t (f t x) (g t y)) ->
    forall  ls (a b : hlist F ls),
      equiv_hlist R a b ->
      equiv_hlist R' (hlist_map f a) (hlist_map g b).
Proof.
  clear. induction 2; simpl; intros.
  - constructor.
  - constructor; eauto.
Qed.


(** Linking Heterogeneous Lists and Lists **)

Section hlist_gen.
  Variable A : Type.
  Variable F : A -> Type.
  Variable f : forall a, F a.

  Fixpoint hlist_gen ls : hlist F ls :=
    match ls with
    | nil => Hnil
    | cons x ls' => Hcons (f x) (hlist_gen ls')
    end.

  Lemma hlist_get_hlist_gen : forall ls t (m : member t ls),
    hlist_get m (hlist_gen ls) = f t.
  Proof.
    induction m; simpl; auto.
  Qed.

  (** This function is a generalisation of [hlist_gen] in which the function [f]
    takes the additional parameter [member a ls]. **)
  Fixpoint hlist_gen_member ls : (forall a, member a ls -> F a) -> hlist F ls :=
    match ls as ls return ((forall a : A, member a ls -> F a) -> hlist F ls) with
    | nil => fun _ => Hnil
    | a :: ls' => fun fm =>
        Hcons (fm a (MZ a ls'))
          (hlist_gen_member (fun a' (M : member a' ls') => fm a' (MN a M)))
    end.

  Lemma hlist_gen_member_hlist_gen : forall ls,
    hlist_gen_member (fun a _ => f a) = hlist_gen ls.
  Proof.
    induction ls; simpl; f_equal; auto.
  Qed.

  Lemma hlist_gen_member_ext : forall ls (f g : forall a, member a ls -> F a),
    (forall x M, f x M = g x M) ->
    hlist_gen_member f = hlist_gen_member g.
  Proof.
    intros. induction ls; simpl; f_equal; auto.
  Qed.

End hlist_gen.

Arguments hlist_gen {A F} f ls.

Lemma hlist_gen_member_hlist_map : forall A (F G : A -> Type) (ff : forall t, F t -> G t) ls f,
  hlist_map ff (hlist_gen_member F (ls := ls) f) = hlist_gen_member G (fun a M => ff _ (f _ M)).
Proof.
  intros. induction ls; simpl; f_equal; auto.
Qed.

Lemma hlist_gen_hlist_map : forall A (F G : A -> Type) (ff : forall t, F t -> G t) f ls,
  hlist_map ff (hlist_gen f ls) = hlist_gen (fun a => ff _ (f a)) ls.
Proof.
  intros. do 2 rewrite <- hlist_gen_member_hlist_gen. apply hlist_gen_member_hlist_map.
Qed.

Lemma hlist_gen_ext : forall A F (f g : forall a, F a),
  (forall x, f x = g x) ->
  forall ls : list A, hlist_gen f ls = hlist_gen g ls.
Proof.
  intros. do 2 rewrite <- hlist_gen_member_hlist_gen. apply hlist_gen_member_ext. auto.
Qed.

Global Instance Proper_hlist_gen : forall A F,
  Proper (forall_relation (fun _ => eq) ==> forall_relation (fun _ => eq))
         (@hlist_gen A F).
Proof.
  repeat intro. apply hlist_gen_ext. auto.
Qed.

Lemma equiv_hlist_gen : forall T (F : T -> Type) (f : forall t, F t) f'
    (R : forall t, F t -> F t -> Prop),
  (forall t, R t (f t) (f' t)) ->
  forall ls,
    equiv_hlist R (hlist_gen f ls) (hlist_gen f' ls).
Proof.
  induction ls; simpl; constructor; auto.
Qed.

Global Instance Proper_equiv_hlist_gen : forall A (F : A -> Type) R,
  Proper (forall_relation R ==> forall_relation (@equiv_hlist _ _ R))
         (@hlist_gen A F).
Proof.
  repeat intro. apply equiv_hlist_gen. auto.
Qed.

Fixpoint hlist_erase {A B} {ls : list A} (hs : hlist (fun _ => B) ls) : list B :=
  match hs with
  | Hnil => nil
  | Hcons _ _ x hs' => cons x (hlist_erase hs')
  end.

Lemma hlist_erase_hlist_gen : forall A B ls (f : A -> B),
  hlist_erase (hlist_gen f ls) = map f ls.
Proof.
  induction ls; simpl; intros; f_equal; auto.
Qed.


(** Linking Heterogeneous Lists and Predicates **)

Section hlist_Forall.
  Variable A : Type.
  Variable P : A -> Prop.

  Fixpoint hlist_Forall ls (hs : hlist P ls) : Forall P ls :=
    match hs with
    | Hnil => Forall_nil _
    | Hcons _ _ H hs' => Forall_cons _ H (hlist_Forall hs')
    end.

End hlist_Forall.


(** Heterogeneous Relations **)
Section hlist_rel.
  Variable A : Type.
  Variables F G : A -> Type.
  Variable R : forall x : A, F x -> G x -> Prop.

  Inductive hlist_hrel : forall ls, hlist F ls -> hlist G ls -> Prop :=
  | hrel_Hnil : hlist_hrel Hnil Hnil
  | hrel_Hcons : forall t ts x y xs ys, @R t x y -> @hlist_hrel ts xs ys ->
                                        @hlist_hrel (t :: ts) (Hcons x xs) (Hcons y ys).

End hlist_rel.

Section hlist_rel_map.
  Variable A : Type.
  Variables F G F' G' : A -> Type.
  Variable R : forall x : A, F x -> G x -> Prop.
  Variable R' : forall x : A, F' x -> G' x -> Prop.
  Variable ff : forall x : A, F x -> F' x.
  Variable gg : forall x : A, G x -> G' x.

  Hypothesis R_ff_R' :
    forall t x y, @R t x y ->
                  @R' t (ff x) (gg y).

  Theorem hlist_hrel_map
  : forall ls xs ys,
      @hlist_hrel A F G R ls xs ys ->
      @hlist_hrel A F' G' R' ls (hlist_map ff xs) (hlist_map gg ys).
  Proof.
    induction 1; simpl; constructor; eauto.
  Qed.

  Theorem hlist_hrel_cons
  : forall l ls x xs y ys,
      @hlist_hrel A F G R (l :: ls) (Hcons x xs) (Hcons y ys) ->
      @R l x y /\ @hlist_hrel A F G R ls xs ys.
  Proof.
    intros.
    refine
      match H in @hlist_hrel _ _ _ _ ls' xs' ys'
            return
            match ls' as ls' return hlist F ls' -> hlist G ls' -> Prop with
              | nil => fun _ _ => True
              | l' :: ls' => fun x y =>
                   R (hlist_hd x) (hlist_hd y)
                /\ hlist_hrel R (hlist_tl x) (hlist_tl y)
            end xs' ys'
      with
        | hrel_Hnil => I
        | hrel_Hcons _ _ _ _ _ _ pf pf' => conj pf pf'
      end.
  Qed.

  Theorem hlist_hrel_app
  : forall l ls x xs y ys,
      @hlist_hrel A F G R (l ++ ls) (hlist_app x xs) (hlist_app y ys) ->
      @hlist_hrel A F G R l x y /\ @hlist_hrel A F G R ls xs ys.
  Proof.
    induction x.
    + intros xs y ys. rewrite (hlist_eta y).
      simpl; intros; split; auto. constructor.
    + intros xs y ys. rewrite (hlist_eta y).
      intros. eapply hlist_hrel_cons in H.
      destruct H.
      apply IHx in H0.
      intuition. constructor; auto.
  Qed.

End hlist_rel_map.

Theorem hlist_hrel_equiv
: forall T (F : T -> Type) (R : forall t, F t -> F t -> Prop) ls (h h' : hlist F ls),
    hlist_hrel R h h' ->
    equiv_hlist R h h'.
Proof.
  induction 1; constructor; auto.
Qed.

Theorem hlist_hrel_flip
: forall T (F G : T -> Type) (R : forall t, F t -> G t -> Prop) ls
         (h : hlist F ls) (h' : hlist G ls),
    hlist_hrel R h h' ->
    hlist_hrel (fun t a b => R t b a) h' h.
Proof.
  induction 1; constructor; auto.
Qed.
