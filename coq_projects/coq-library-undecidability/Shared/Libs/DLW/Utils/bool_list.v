(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

(** ** Bitwise operations on nat as list bool *)

Require Import List Omega Bool Setoid.
Require Import utils_tac.

Set Implicit Arguments.

(* Section lb. *)

  Local Reserved Notation "x ⪯ y" (at level 70, no associativity).
  Local Reserved Notation "x ⟂ y" (at level 70, no associativity).
  Local Reserved Notation "x ↓ y" (at level 40, left associativity).
  Local Reserved Notation "x ↑ y" (at level 41, left associativity).

  Local Notation lb := (list bool).
  Local Notation "⟘" := false.
  Local Notation "⟙" := true.
  Local Infix "⪦" := leb (at level 70, no associativity).

  Fact leb_refl : forall x, x ⪦ x.
  Proof. intros []; simpl; auto. Qed.

  Fact leb_trans : forall x y z, x ⪦ y -> y ⪦ z -> x ⪦ z.
  Proof. intros [] [] []; simpl; auto. Qed.

  Fact leb_strict : ⟘ ⪦ ⟙.
  Proof. exact I. Qed. 

  Hint Resolve leb_refl leb_trans leb_strict.

  (** We develop the Boolean algebra of lists of Booleans *)

  (* The masking relation *)

  Inductive lb_mask : lb -> lb -> Prop :=
    | in_lb_mask_0 : forall l,                            nil ⪯ l
    | in_lb_mask_1 : forall l,                l ⪯ nil -> ⟘::l ⪯  nil 
    | in_lb_mask_2 : forall x y l m, x ⪦ y -> l ⪯ m   -> x::l ⪯  y::m
  where "l ⪯ m" := (lb_mask l m).

  Fact lb_mask_inv_nil l : ⟘::l ⪯  nil -> l ⪯  nil.
  Proof. inversion 1; auto. Qed. 

  Fact lb_mask_inv_left x l : x::l ⪯  nil -> x = ⟘ /\ l ⪯  nil.
  Proof. inversion 1; auto. Qed. 

  Fact lb_mask_inv_cons x y l m : x::l ⪯ y::m -> leb x y /\ l ⪯  m.
  Proof. inversion 1; tauto. Qed.

  Fact lb_mask_inv_cons_nil l : ⟙::l ⪯ nil -> False.
  Proof. inversion 1. Qed.

  Fact lb_mask_inv_cons_cons l m : ⟙::l ⪯ ⟘::m -> False.
  Proof.
    intros H; apply lb_mask_inv_cons, proj1 in H; discriminate.
  Qed.
 
  Definition lb_mask_leb := in_lb_mask_2.

  Fact lb_mask_refl l : l ⪯ l.
  Proof. induction l as [ | [] ]; constructor; simpl; auto. Qed.

  Fact lb_mask_trans l m k : l ⪯ m -> m ⪯ k -> l ⪯ k.
  Proof.
    intros H1; revert H1 k.
    induction 1 as [ l | l H1 IH1 | x y l m H1 IH1 ].
    + intros; constructor.
    + intros [ | z k ] Hk.
      * constructor; auto.
      * constructor; simpl; auto; apply IH1; constructor.
    + intros [ | z k ] Hk.
      * apply lb_mask_inv_left in Hk; destruct Hk as (? & Hk); subst y.
        destruct x; simpl in H1; try discriminate.
        constructor; auto.
      * apply lb_mask_inv_cons in Hk. 
        destruct Hk as (H2 & Hk).
        constructor; auto.
        revert x y z H1 H2.
        intros [] [] []; simpl; auto.
  Qed.

  Hint Resolve lb_mask_refl lb_mask_trans.

  Definition lb_mask_equiv l m := l ⪯ m /\ m ⪯ l.

  Local Infix "≂" := lb_mask_equiv (at level 70, no associativity).

  Fact lb_mask_equiv_refl l : l ≂ l.
  Proof. split; auto. Qed.

  Fact lb_mask_equiv_sym l m : l ≂ m -> m ≂ l.
  Proof. intros []; split; auto. Qed.

  Fact lb_mask_equiv_trans l m k : l ≂ m -> m ≂ k -> l ≂ k.
  Proof. intros [] []; split; eauto. Qed.

  Hint Resolve in_lb_mask_0 lb_mask_refl lb_mask_equiv_refl.

  Add Parametric Relation: (lb) (lb_mask_equiv)
      reflexivity proved by  lb_mask_equiv_refl
      symmetry proved by     lb_mask_equiv_sym
      transitivity proved by lb_mask_equiv_trans
    as lb_mask_equiv_rst.

  Local Notation lbeq := lb_mask_equiv (only parsing).

  Add Parametric Morphism: (lb_mask) with signature (lbeq) ==> (lbeq) ==> (iff) as lb_mask_le_iff.
  Proof. 
    intros x1 y1 (H1 & H2) x2 y2 (H3 & H4); split; intros H5.
    + apply lb_mask_trans with (1 := H2), lb_mask_trans with (1 := H5); auto.
    + apply lb_mask_trans with (1 := H1), lb_mask_trans with (1 := H5); auto.
  Qed.

  Add Parametric Morphism: (@cons bool) with signature (eq) ==> (lbeq) ==> (lbeq) as lb_mask_equiv_cons.
  Proof.
    intros [] ? ? []; split; apply lb_mask_leb; simpl; auto.
  Qed.

  Fact lb_mask_app l m a b : length l = length m -> l ⪯ m -> a ⪯ b -> l++a ⪯ m++b.
  Proof.
    revert m; induction l as [ | x l IHl ]; intros [ | y m ]; try discriminate; auto;
      simpl; intros H H1 H2.
    apply lb_mask_inv_cons in H1; destruct H1 as (H1 & H3).
    constructor 3; auto.
  Qed.

  Fact lb_mask_equiv_app l m a b : length l = length m -> l ≂ m -> a ≂ b -> l++a ≂ m++b.
  Proof.
    intros H (? & ?) (? & ?); split; apply lb_mask_app; auto.
  Qed.

  Inductive lb_ortho : lb -> lb -> Prop :=
    | in_lb_ortho_0 : forall l, nil ⟂ l
    | in_lb_ortho_1 : forall l, l ⟂ nil
    | in_lb_ortho_2 : forall x y l m, (x = ⟘ \/ y = ⟘) -> l ⟂ m -> x::l ⟂ y::m
  where "x ⟂ y" := (lb_ortho x y).

  Hint Constructors lb_ortho.

  Fact lb_ortho_cons_inv x y l m : x::l ⟂ y::m -> (x = ⟘ \/ y = ⟘) /\ l ⟂ m.
  Proof. inversion 1; auto. Qed.

  Fact lb_ortho_anti_left a b x : a ⪯ b -> b ⟂ x -> a ⟂ x.
  Proof.
    intros H; revert H x.
    induction 1 as [ l | m H1 IH1 | x y l m H1 H2 IH2  ]; intros z H3; try (constructor; fail);
      destruct z as [ | v z ]; try (constructor; fail).
    + constructor; auto; apply IH1; constructor.
    + apply lb_ortho_cons_inv in H3.
      destruct H3 as (H3 & H4).
      constructor; auto. 
      revert x y v H1 H3.
      intros [] [] []; simpl; auto.
  Qed.

  Fact lb_ortho_sym a b : a ⟂ b -> b ⟂ a.
  Proof. induction 1; constructor; tauto. Qed.

  Fact lb_ortho_anti a b x y : a ⪯ b -> x ⪯ y -> b ⟂ y -> a ⟂ x.
  Proof. 
    intros H1 H2 H3.
    apply lb_ortho_anti_left with (1 := H1), lb_ortho_sym,
          lb_ortho_anti_left with (1 := H2), lb_ortho_sym.
    trivial.
  Qed.

  Add Parametric Morphism: (lb_ortho) with signature (lbeq) ==> (lbeq) ==> (iff) as lb_ortho_iff.
  Proof. intros ? ? [] ? ? []; split; apply lb_ortho_anti; auto. Qed.

  Section lb_pointwise.

    Variable (f : bool -> bool -> bool).

    Fixpoint lb_pointwise l m := 
      match l, m with
        | nil,   nil  => nil
        |  _,    nil  => map (fun x => f x ⟘) l
        | nil,     _  => map (f ⟘) m
        | x::l, y::m  => f x y :: lb_pointwise l m
      end.

    Fact lb_pointwise_nil : lb_pointwise nil nil = nil.
    Proof. trivial. Qed.

    Fact lb_pointwise_left l : lb_pointwise l nil = map (fun x => f x ⟘) l.
    Proof. destruct l; trivial. Qed.

    Fact lb_pointwise_right l : lb_pointwise nil l = map (f ⟘) l.
    Proof. destruct l; trivial. Qed.
 
    Fact lb_pointwise_cons x l y m : lb_pointwise (x::l) (y::m) = f x y :: lb_pointwise l m.
    Proof. trivial. Qed.

    Fact lb_pointwise_length n l m : length l <= n -> length m <= n -> length (lb_pointwise l m) <= n.
    Proof.
      revert l m; induction n as [ | n IHn ].
      + intros [] []; simpl; omega.
      + intros [ | x l ] [ | y m ]; simpl; try rewrite map_length; auto.
        intros; apply le_n_S, IHn; omega.
    Qed.

    Fact lb_pointwise_sym l m : (forall x y, f x y = f y x) -> lb_pointwise l m = lb_pointwise m l.
    Proof.
      intros H; revert l m; induction l as [ | x l IHl ]; intros m.
      + rewrite lb_pointwise_left, lb_pointwise_right.
        apply map_ext; intro; auto.
      + destruct m as [ | y m ].
        * rewrite lb_pointwise_left, lb_pointwise_right.
          apply map_ext; intro; auto.
        * do 2 rewrite lb_pointwise_cons; f_equal; auto.
    Qed.

    Variable (Hf1 : forall x a b, leb a b -> leb (f x a) (f x b)) 
             (Hf2 : f ⟘ ⟘ = ⟘).

    Let lbpw_mono_1 l m :  lb_pointwise l nil ⪯   lb_pointwise l m.
    Proof.
      rewrite lb_pointwise_left.
      revert m; induction l as [ | x l IHl ]; intros m.
      + simpl; constructor.
      + destruct m as [ | y m ]; simpl.
        * apply lb_mask_refl.
        * apply lb_mask_leb; auto.
    Qed.

    Let lbpw_mono_f_0 g l m : g ⟘ = ⟘ -> leb (g ⟘) (g ⟙) -> l ⪯ m -> map g l ⪯  map g m.
    Proof.
      intros H1 H2.
      assert (Hg : forall x y, x ⪦ y -> g x ⪦ g y).
      { intros [] []; simpl; auto; discriminate. }
      induction 1; simpl; try rewrite H1; constructor; auto.
    Qed.

    Let lbpw_mono_2 l m : m ⪯ nil -> lb_pointwise l m ⪯   lb_pointwise l nil.
    Proof.
      revert m; induction l as [ | x l IHl ]; intros [ | y m ] H.
      + constructor.
      + rewrite lb_pointwise_right.
        apply lbpw_mono_f_0 with (g := f ⟘) in H; auto.
      + apply lb_mask_refl.
      + rewrite lb_pointwise_cons, lb_pointwise_left.
        apply lb_mask_inv_left in H.
        destruct H as (E & H); subst y.
        simpl.
        apply lb_mask_leb.
        1: destruct (f x ⟘); simpl; auto.
        apply lb_mask_trans with (1 := IHl _ H).
        rewrite lb_pointwise_left.
        apply lb_mask_refl.
    Qed.

    Fact lb_pointwise_mono_left l m k : l ⪯  m -> lb_pointwise k l ⪯   lb_pointwise k m.
    Proof.
      intros H; revert m H k.
      induction l as [ | x l IHl ]; intros m H k; auto.
      destruct m as [ | y m ].
      * apply lbpw_mono_2; auto.
      * destruct k as [ | u k ].
        - apply lbpw_mono_f_0; auto.
        - do 2 rewrite lb_pointwise_cons.
          apply lb_mask_inv_cons in H; destruct H.
          apply lb_mask_leb; auto.
    Qed.
  
  End lb_pointwise.

  Definition lb_meet := (lb_pointwise andb).
  Definition lb_join := (lb_pointwise orb).

  Local Infix "↓" := lb_meet.
  Local Infix "↑" := lb_join.

  Fact lb_meet_left x : x↓nil ≂ nil.
  Proof.
    unfold lb_meet.
    split; try (constructor; fail).
    rewrite lb_pointwise_left.
    induction x as [ | [] x ]; simpl; constructor; auto.
  Qed.

  Fact lb_meet_comm l m : l↓m = m↓l.
  Proof.
    apply lb_pointwise_sym.
    destruct x; destruct y; auto.
  Qed.

  Fact lb_meet_right x : nil↓x ≂ nil.
  Proof.
    rewrite lb_meet_comm; apply lb_meet_left.
  Qed.

  Fact lb_meet_cons x y l m : (x::l) ↓ (y::m) = x && y :: l↓m.
  Proof. auto. Qed.

  Fact lb_meet_mono l m a b : l ⪯ m -> a ⪯ b -> l↓a ⪯  m↓b.
  Proof.
    intros H1 H2.
    apply lb_mask_trans with (l↓b).
    + apply lb_pointwise_mono_left;auto.
      intros [] [] []; simpl; auto; discriminate.
    + do 2 rewrite (lb_meet_comm _ b).
      apply lb_pointwise_mono_left;auto.
      intros [] [] []; simpl; auto; discriminate.
  Qed.

  Add Parametric Morphism: (lb_meet) with signature (lbeq) ==> (lbeq) ==> (lbeq) as lb_meet_eq.
  Proof. intros ? ? [] ? ? []; split; apply lb_meet_mono; auto. Qed.

  Fact lb_meet_length_le n l m : length l <= n -> length m <= n -> length (l↓m) <= n.
  Proof. apply lb_pointwise_length. Qed.

  Fact lb_meet_length a b : length a = length b -> length (a↓b) = length a.
  Proof.
    revert b; induction a as [ | x a IHa ]; intros [ | y b ]; try discriminate; auto;
      intros H.
    rewrite lb_meet_cons; simpl; f_equal; auto.
  Qed.

  Fact lb_meet_app l m a b : length l = length m -> (l++a)↓(m++b) = l↓m++a↓b.   
  Proof.
    revert m; induction l as [ | x l IHl ]; intros [ | y m ]; try discriminate; intros H.
    + simpl; auto.
    + simpl app.
      rewrite lb_meet_cons; f_equal.
      apply IHl.
      simpl in H; inversion H; auto.
  Qed.

  Fact lb_join_left x : x↑nil = x.
  Proof.
    unfold lb_join.
    rewrite lb_pointwise_left.
    induction x as [ | [] ]; simpl; f_equal; auto.
  Qed.

  Fact lb_join_comm l m : l↑m = m↑l.
  Proof.
    apply lb_pointwise_sym.
    destruct x; destruct y; auto.
  Qed.

  Fact lb_join_right x : nil↑x = x.
  Proof.
    rewrite lb_join_comm; apply lb_join_left.
  Qed.
 
  Fact lb_join_cons x y l m : (x::l) ↑ (y::m) = x || y :: l↑m.
  Proof. auto. Qed.

  Fact lb_join_length_le n l m : length l <= n -> length m <= n -> length (l↑m) <= n.
  Proof. apply lb_pointwise_length. Qed.

  Fact lb_join_mono l m a b : l ⪯ m -> a ⪯ b -> l↑a ⪯  m↑b.
  Proof.
    intros H1 H2.
    apply lb_mask_trans with (l↑b).
    + apply lb_pointwise_mono_left;auto.
      intros [] [] []; simpl; auto; discriminate.
    + do 2 rewrite (lb_join_comm _ b).
      apply lb_pointwise_mono_left;auto.
      intros [] [] []; simpl; auto; discriminate.
  Qed.

  Add Parametric Morphism: (lb_join) with signature (lbeq) ==> (lbeq) ==> (lbeq) as lb_join_eq.
  Proof. intros ? ? [] ? ? []; split; apply lb_join_mono; auto. Qed.

  Fact lb_ortho_meet_nil x y : x ⟂ y <-> x↓y ≂ nil.
  Proof.
    split.
    + intros H; split; try constructor; revert H.
      induction 1 as [ m | l | x y l m ].
      - rewrite lb_meet_right; constructor.
      - rewrite lb_meet_left; constructor.
      - rewrite lb_meet_cons.
        simpl; destruct H; [ destruct y | destruct x ]; try discriminate; subst; simpl; constructor; auto.
    + intros [ H1 _ ]; revert H1.
      revert y; induction x as [ | x l IHl ]; intros [ | y m ]; simpl; intros H; try (constructor; fail).
      destruct x; destruct y; simpl in H |- *; try (inversion H; fail);
        apply lb_mask_inv_nil in H; constructor; auto.
  Qed.

  Hint Resolve lb_mask_equiv_refl.

  Fact lb_join_inc_left a b : a ⪯  a↑b.
  Proof.
    revert b; induction a as [ | x a IHa ]; intros b.
    + constructor.
    + destruct b as [ | y b ].
      * rewrite lb_join_left; auto.
      * rewrite lb_join_cons.
        apply lb_mask_leb; auto.
        destruct x; destruct y; simpl; auto.
  Qed.

  Fact lb_meet_dec_left a b : a↓b ⪯  a.
  Proof.
    revert b; induction a as [ | x a IHa ]; intros b.
    + rewrite lb_meet_right; constructor.
    + destruct b as [ | y b ].
      * rewrite lb_meet_left; constructor. 
      * rewrite lb_meet_cons.
        apply lb_mask_leb; auto.
        destruct x; destruct y; simpl; auto.
  Qed.

  Fact lb_join_inc_right a b : b ⪯  a↑b.
  Proof. rewrite lb_join_comm; apply lb_join_inc_left. Qed.

  Fact lb_meet_dec_right a b : a↓b ⪯  b.
  Proof. rewrite lb_meet_comm; apply lb_meet_dec_left. Qed.
  
  Hint Resolve lb_join_inc_left lb_join_inc_right lb_meet_dec_left lb_meet_dec_right.

  Fact lb_mask_join a b : a ⪯  b <-> a↑b ≂ b.
  Proof.
    split.
    + intros H; split.
      2: rewrite lb_join_comm; auto.
      induction H as [ | | x y ? ? H ].
      * rewrite lb_join_right; auto.
      * rewrite lb_join_left; constructor; auto.
      * rewrite lb_join_cons; constructor; auto.
        revert x y H; intros [] []; simpl; auto.
    + intros (H1 & _).
      apply lb_mask_trans with (2 := H1); auto.
  Qed.

  Fact lb_mask_meet a b : a ⪯  b <-> a↓b ≂ a.
  Proof.
    split.
    + intros H; split; auto.
      induction H as [ | | x y ? ? H ].
      * constructor.
      * rewrite lb_meet_left; constructor; auto.
      * rewrite lb_meet_cons; constructor; auto.
        revert x y H; intros [] []; simpl; auto.
    + intros (H1 & H2).
      apply lb_mask_trans with (1 := H2).
      rewrite lb_meet_comm; auto.
  Qed.

  Fact lb_meet_idem a : a↓a = a.
  Proof.
    induction a as [ | x a ]; auto.
    rewrite lb_meet_cons; f_equal; auto.
    destruct x; simpl; auto.
  Qed.

  Fact lb_join_idem a : a↑a = a.
  Proof.
    induction a as [ | x a ]; auto.
    rewrite lb_join_cons; f_equal; auto.
    destruct x; simpl; auto.
  Qed.

  Tactic Notation "rew" "lb"  :=
       repeat (  rewrite lb_meet_left || rewrite lb_meet_right
              || rewrite lb_join_left || rewrite lb_join_right); auto.

  Fact lb_join_meet_distr a b c : a↑(b↓c) ≂ (a↑b)↓(a↑c).
  Proof.
    revert b c; induction a as [ | x a IHa ]; intros b c.
    + rew lb.
    + destruct b as [ | y b ].
      * rew lb.
        rewrite (proj1 (lb_mask_meet _ _)); auto.
      * destruct c as [ | z c ].
        - rew lb.
          rewrite lb_meet_comm. 
          rewrite (proj1 (lb_mask_meet _ _)); auto.
        - repeat rewrite lb_meet_cons.
          repeat rewrite lb_join_cons.
          repeat rewrite lb_meet_cons.
          apply lb_mask_equiv_cons; auto.
          destruct x; destruct y; destruct z; simpl; auto.
  Qed.

  Fact lb_meet_join_distr a b c : a↓(b↑c) ≂ (a↓b)↑(a↓c).
  Proof.
    revert b c; induction a as [ | x a IHa ]; intros b c.
    + rew lb.
    + destruct b as [ | y b ].
      * rew lb.
      * destruct c as [ | z c ].
        - rew lb.
        - repeat rewrite lb_meet_cons.
          repeat rewrite lb_join_cons.
          repeat rewrite lb_meet_cons.
          apply lb_mask_equiv_cons; auto.
          destruct x; destruct y; destruct z; simpl; auto.
  Qed.

  Fact lb_meet_assoc a b c : a↓(b↓c) ≂ a↓b↓c.
  Proof.
    revert b c; induction a as [ | x a IHa ]; intros b c.
    + rew lb.
    + destruct b as [ | y b ].
      * rew lb.
      * destruct c as [ | z c ].
        - rew lb.
        - repeat rewrite lb_meet_cons.
          apply lb_mask_equiv_cons; auto.
          destruct x; destruct y; destruct z; simpl; auto.
  Qed.

  Fact lb_join_assoc a b c : a↑(b↑c) ≂ a↑b↑c.
  Proof.
    revert b c; induction a as [ | x a IHa ]; intros b c.
    + rew lb.
    + destruct b as [ | y b ].
      * rew lb.
      * destruct c as [ | z c ].
        - rew lb.
        - repeat rewrite lb_join_cons.
          apply lb_mask_equiv_cons; auto.
          destruct x; destruct y; destruct z; simpl; auto.
  Qed.

  Hint Resolve lb_meet_mono lb_join_mono.
  
  Fact lb_join_spec a b c : a ⪯  c -> b ⪯  c -> a↑b ⪯  c.
  Proof. intros; rewrite <- (lb_join_idem c); auto. Qed.

  Fact lb_meet_spec a b c : c ⪯  a -> c ⪯  b -> c ⪯  a↓b.
  Proof. intros; rewrite <- (lb_meet_idem c); auto. Qed.

  Fact lb_meet_join_idem a b : a↓(a↑b) ≂ a.
  Proof. rewrite <- lb_mask_meet; auto. Qed.

  Fact lb_join_meet_idem a b : a↑(a↓b) ≂ a.
  Proof. rewrite lb_join_comm, <- lb_mask_join; auto. Qed.

  Fact lb_join_nil_eq a b : a↑b ≂ nil -> a ≂ nil /\ b ≂ nil.
  Proof.
    intros H; split.
    rewrite <- (lb_meet_left a), <- H, lb_meet_join_idem; auto.
    rewrite <- (lb_meet_left b), <- H, lb_join_comm, lb_meet_join_idem; auto.
  Qed.

  Fact lb_ortho_join a x y : a ⟂ x↑y <-> a ⟂ x /\ a ⟂ y.
  Proof.
    do 3 rewrite lb_ortho_meet_nil; split.
    + intros H; apply lb_join_nil_eq.
      rewrite <- lb_meet_join_distr, H; auto.
    + intros (H1 & H2).
      rewrite lb_meet_join_distr, H1, H2; auto.
  Qed.

  Fact lb_ortho_mask_nil a x : a ⟂ x -> x ⪯  a -> x ≂ nil.
  Proof. 
    induction 1 as [ | | x y l m H1 H2 IH2 ]; auto.
    + split; auto.
    + intros H.
      apply lb_mask_inv_cons in H; destruct H as (H3 & H4).
      rewrite IH2; auto; split; auto.
      revert x y H1 H3.
      intros [] []; simpl; intros [] ?; try discriminate; constructor; auto.
  Qed.

  (* c = a - b *)

  Section lb_complement.

    Let bin_comp a b :=
      match a, b with
        | ⟘, ⟘  => ⟘ 
        | ⟘, ⟙  => ⟘
        | ⟙, ⟘  => ⟙
        | ⟙, ⟙  => ⟘ 
    end.

    Definition lb_complement a b : { c | b ⟂ c /\ a↑b ≂ c↑b }.
    Proof.
       revert b; induction a as [ | x a IHa ]; intros b.
       + exists nil; split; auto.
       + destruct b as [ | y b ].
         - exists (x :: a); split; auto.
         - destruct (IHa b) as (c & H1 & H2).
           exists (bin_comp x y::c).
           revert x y; intros [] []; simpl; split; auto; 
             rewrite H2; simpl; auto.
    Qed.

  End lb_complement.

  Definition lb_minus a b : a ⪯ b -> { c | a ⟂ c /\ b ≂ a↑c }.
  Proof.
    intros H.
    destruct (lb_complement b a) as (c & H1 & H2).
    exists c; split; auto.
    rewrite lb_mask_join in H.
    rewrite <- H, (lb_join_comm a), (lb_join_comm a); auto.
  Qed.

(* End lb.

Hint Resolve leb_refl leb_trans leb_strict.
Hint Resolve lb_mask_refl lb_mask_trans.
Hint Resolve in_lb_mask_0 lb_mask_refl lb_mask_equiv_refl.
Hint Constructors lb_mask lb_ortho.
Hint Resolve lb_mask_equiv_refl.
Hint Resolve lb_join_inc lb_meet_dec_left lb_meet_dec_right.
*)
