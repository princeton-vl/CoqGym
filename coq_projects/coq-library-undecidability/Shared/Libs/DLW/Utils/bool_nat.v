(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

(** ** Bitwise operations on nat *)

Require Import Arith Nat Omega List Bool Setoid.
Require Import utils_tac utils_list utils_nat bool_list gcd sums power_decomp.

Set Implicit Arguments.

Local Notation power := (mscal mult 1).
Local Notation "∑" := (msum plus 0).

Local Reserved Notation "x ≲ y" (at level 70, no associativity).

(* if n and m are written in binary, LSB first:
       n = n0 n1 n2 ...
       m = m0 m1 m2 ...
    then n ≲ m means forall any i, n[i] <= m[i] *)

Inductive binary_le : nat -> nat -> Prop :=
 | in_ble_0 : forall n, 0 ≲ n
 | in_ble_1 : forall n m, rem n 2 <= rem m 2 -> div n 2 ≲ div m 2 -> n ≲ m
where "x ≲ y" := (binary_le x y).

Local Infix "≲" := binary_le (at level 70, no associativity).

Fact binary_le_inv n m : n ≲ m -> n = 0 \/ div n 2 ≲ div m 2 /\ rem n 2 <= rem m 2.
Proof. inversion 1; auto. Qed.

Fact binary_le_refl x : x ≲ x.
Proof.
  induction on x as IH with measure x.
  destruct (eq_nat_dec x 0).
  + subst; constructor.
  + constructor 2; auto.
    apply IH, div_by_p_lt; auto.
Qed.

Fact binary_le_le x y : x ≲ y -> x <= y.
Proof.
  induction 1 as [ n | n m H1 H2 IH2 ]; try omega.
  rewrite (div_rem_spec1 n 2), (div_rem_spec1 m 2); omega.
Qed.

Fact binary_le_zero_inv n : n ≲ 0 -> n = 0.
Proof. intros H; apply binary_le_le in H; omega. Qed.

Fact binary_le_zero n : 0 ≲ n.
Proof. constructor. Qed.

Hint Resolve binary_le_zero binary_le_refl.

Local Notation "⟘" := false.
Local Notation "⟙" := true.

Definition bool2nat x := 
  match x with 
    | ⟘ => 0 
    | ⟙ => 1 
  end.
 
Fact rem_2_bool2nat b n : rem (bool2nat b+2*n) 2 = bool2nat b.
Proof. 
  destruct b; unfold bool2nat.
  + apply rem_2_fix_2.
  + apply rem_2_fix_1.
Qed.

Fact div_2_bool2nat b n : div (bool2nat b+2*n) 2 = n.
Proof. 
  destruct b; unfold bool2nat.
  + apply div_2_fix_2.
  + apply div_2_fix_1.
Qed.

Definition nat2bool x := 
  match x with 
    | 0 => ⟘ 
    | _ => ⟙ 
  end.

Fact bool2nat2bool : forall x, x < 2 -> bool2nat (nat2bool x) = x.
Proof. intros [ | [ | ] ] ?; simpl; omega. Qed.

Fact nat2bool2nat : forall x, nat2bool (bool2nat x) = x.
Proof. intros []; auto. Qed.

Local Hint Resolve power2_gt_0.

Local Notation lb := (list bool).

Local Infix "⪦" := leb (at level 70, no associativity).
Local Infix "⪯" := lb_mask (at level 70, no associativity).
Local Infix "≂" := lb_mask_equiv (at level 70, no associativity).
Local Infix "⟂" := lb_ortho (at level 70, no associativity).
Local Infix "↓" := lb_meet (at level 40, left associativity).
Local Infix "↑" := lb_join (at level 41, left associativity).

Local Reserved Notation "'⟦' l '⟧'".
Local Reserved Notation "'⟬' x '⟭'".

(* Section lb_nat. *)

  Fixpoint lb_nat (l : lb) :=
    match l with
      | nil    => 0
      | x :: l => bool2nat x + 2*⟦l⟧
    end
  where "⟦ l ⟧" := (lb_nat l).

  Fact lb_nat_fix_0 : ⟦nil⟧ = 0.                      Proof. trivial. Qed.
  Fact lb_nat_fix_1 l : ⟦⟘::l⟧ = 2*⟦l⟧.               Proof. trivial. Qed.
  Fact lb_nat_fix_2 l : ⟦⟙::l⟧ = 1+2*⟦l⟧.             Proof. trivial. Qed.
  Fact lb_nat_fix_3 x l : ⟦x::l⟧ = bool2nat x+2*⟦l⟧.  Proof. trivial. Qed.

  Fact lb_nat_app l m : lb_nat (l++m) = lb_nat l + (power (length l) 2)*(lb_nat m).
  Proof.
    induction l as [ | x l IHl ].
    + rewrite lb_nat_fix_0; simpl; omega.
    + simpl app; do 2 rewrite lb_nat_fix_3.
      simpl length; rewrite power_S.
      rewrite IHl; ring.
  Qed.

  Fact lb_mask_binary_le l m : l ⪯ m -> ⟦l⟧ ≲ ⟦m⟧.
  Proof.
    induction 1 as [ l | l H1 IH1 | x y l m H1 H2 IH2 ].
    - constructor 1.
    - apply binary_le_zero_inv in IH1.
      simpl; rewrite IH1; constructor.
    - do 2 rewrite lb_nat_fix_3.
      constructor 2.
      * do 2 rewrite rem_2_bool2nat.
        revert x y H1; intros [] []; simpl; auto; discriminate.
      * do 2 rewrite div_2_bool2nat; auto.
  Qed.

  Section nat_lb_def.

    Inductive g_nlb : nat -> lb -> Prop :=
      | in_gnlb_0 : g_nlb 0 nil
      | in_gnlb_1 : forall n l, n <> 0 -> rem n 2 = 0 -> g_nlb (div n 2) l -> g_nlb n (⟘::l)
      | in_gnlb_2 : forall n l, n <> 0 -> rem n 2 = 1 -> g_nlb (div n 2) l -> g_nlb n (⟙::l).
   
    Fact g_nlb_fun n l1 l2 : g_nlb n l1 -> g_nlb n l2 -> l1 = l2.
    Proof.
      intros H1 H2; revert H1 l2 H2.
      induction 1; inversion 1; auto; try omega; f_equal; auto.
    Qed.

    Let nat_lb_full n : { l | g_nlb n l }.
    Proof.
      induction on n as IHn with measure n.
      destruct (eq_nat_dec n 0) as [ | Hn ].
      + exists nil; subst; constructor.
      + destruct (IHn (div n 2)) as (l & Hl).
        * apply div_by_p_lt; omega.
        * case_eq (rem n 2).
          - intro; exists (⟘::l); constructor; auto.
          - intro; exists (⟙::l); constructor; auto.
            generalize (rem_2_lt n); omega.
    Qed.

    Definition nat_lb n := proj1_sig (nat_lb_full n).
  
    Fact nat_lb_spec n : g_nlb n (nat_lb n).
    Proof. apply (proj2_sig (nat_lb_full _)). Qed.

  End nat_lb_def.

  Local Notation "⟬ n ⟭" := (nat_lb n).

  Hint Resolve nat_lb_spec.

  Fact nat_lb_fix_0 : ⟬ 0⟭ = nil.
  Proof. apply g_nlb_fun with 0; auto; constructor. Qed.

  Fact nat_lb_fix_1 n : n <> 0 -> ⟬ 2*n⟭ = ⟘::⟬ n⟭ .
  Proof.
    intros Hn. 
    apply g_nlb_fun with (2*n); auto.
    constructor; auto; try omega.
    + apply rem_2_fix_1.
    + rewrite div_2_fix_1; auto.
  Qed.

  Fact nat_lb_fix_2 n : ⟬1+2*n⟭ = ⟙::⟬ n⟭ .
  Proof.
    apply g_nlb_fun with (1+2*n); auto.
    constructor; auto; try omega.
    + apply rem_2_fix_2.
    + rewrite div_2_fix_2; auto.
  Qed.

  Fact nat_lb_1 : ⟬ 1⟭ = ⟙::nil.
  Proof.
    change 1 with (1+2*0).
    rewrite nat_lb_fix_2, nat_lb_fix_0.
    trivial.
  Qed.

  Fact lb_nat_lb n : ⟦⟬ n ⟭⟧ = n.
  Proof.
    induction on n as IHn with measure n.
    destruct (eq_nat_dec n 0) as [ | Hn ].
    + subst; rewrite nat_lb_fix_0; auto.
    + destruct (euclid_2 n) as (q & [ Hq | Hq ]); subst n.
      * rewrite nat_lb_fix_1; try omega.
        rewrite lb_nat_fix_1; f_equal.
        apply IHn; omega.
      * rewrite nat_lb_fix_2; try omega.
        rewrite lb_nat_fix_2; do 2 f_equal.
        apply IHn; omega.
  Qed.

  Fact nat_lb_length x n : x < power n 2 -> length ⟬ x ⟭ <= n.
  Proof.
    revert x; induction n as [ | n IHn ]; intros x.
    + rewrite power_0; intro; cutrewrite (x=0); try omega.
      rewrite nat_lb_fix_0; simpl; omega.
    + rewrite power_S.
      destruct (euclid_2 x) as (y & [ H | H ]); intros Hx; subst.
      * destruct y.
        - simpl; rewrite nat_lb_fix_0;simpl; omega.
        - rewrite nat_lb_fix_1; try omega.
          simpl; apply le_n_S, IHn; omega.
      * rewrite nat_lb_fix_2; simpl.
        apply le_n_S, IHn; omega.
  Qed.

  Fact binary_le_lb_mask x y : x ≲ y -> ⟬ x ⟭ ⪯ ⟬ y ⟭ . 
  Proof.
    induction 1 as [ n | n m H1 H2 IH2 ].
    + rewrite nat_lb_fix_0; constructor.
    + destruct (eq_nat_dec n 0) as [ Hn | Hn ].
      - subst; rewrite nat_lb_fix_0; constructor.
      - assert (n <= m) as Hmn.
        { apply binary_le_le; constructor; auto. }
        destruct (euclid_2_div n) as (G1 & [ G2 | G2 ] );
        destruct (euclid_2_div m) as (G3 & [ G4 | G4 ] ); try omega.
        * rewrite G1, G2, G3, G4, Nat.add_0_l, Nat.add_0_l.
          do 2 (rewrite nat_lb_fix_1; [ | omega ]).
          constructor; auto.
        * rewrite G1, G2, G3, G4, Nat.add_0_l, nat_lb_fix_2.
          rewrite nat_lb_fix_1; [ | omega ].
          constructor; auto.
        * rewrite G1, G2, G3, G4.
          do 2 rewrite nat_lb_fix_2.
          constructor; auto.
  Qed.

  Hint Resolve lb_mask_binary_le binary_le_lb_mask.

  Section lb_mask_nat.

    Let lb_mask_nat_1 l : ⟬ ⟦l⟧⟭  ⪯  l.
    Proof.
      induction l as [ | [|] l IHl ].
      + rewrite lb_nat_fix_0, nat_lb_fix_0; constructor.
      + rewrite lb_nat_fix_2, nat_lb_fix_2; constructor; auto.
      + rewrite lb_nat_fix_1.
        destruct (eq_nat_dec ⟦l⟧ 0) as [ Hl | Hl ]. 
        - rewrite Hl; simpl; rewrite nat_lb_fix_0; constructor.
        - rewrite nat_lb_fix_1; auto; constructor; auto.
    Qed.

    Let lb_mask_nat_2 l : l ⪯  ⟬ ⟦l⟧⟭  .
    Proof.
      induction l as [ | [|] l IHl ].
      + constructor.
      + rewrite lb_nat_fix_2, nat_lb_fix_2; constructor; auto.
      + rewrite lb_nat_fix_1.
        destruct (eq_nat_dec ⟦l⟧ 0) as [ Hl | Hl ]. 
        - rewrite Hl; simpl; rewrite nat_lb_fix_0; constructor.
          rewrite Hl, nat_lb_fix_0 in IHl; auto.
        - rewrite nat_lb_fix_1; auto; constructor; auto.
    Qed.

    Fact lb_mask_nat l : ⟬ ⟦l⟧⟭ ≂ l.
    Proof. split; auto. Qed.

  End lb_mask_nat.

  Definition nat_lb_nat := lb_mask_nat.

  (* We have a correspondance *)

  Lemma lb_mask_eq_binary_le l m : l ⪯ m <-> ⟦l⟧ ≲ ⟦m⟧.
  Proof.
    split; auto; intro.
    rewrite <- (lb_mask_nat l), <- (lb_mask_nat m); auto.
  Qed.

  Lemma binary_le_eq_lb_mask x y : x ≲ y <-> ⟬ x⟭  ⪯ ⟬ y⟭ .
  Proof.
    split; auto.
    intro; rewrite <- (lb_nat_lb x), <- (lb_nat_lb y); auto.
  Qed.

  Hint Resolve lb_mask_eq_binary_le binary_le_eq_lb_mask.

  Fact binary_le_trans x y z : x ≲ y -> y ≲ z -> x ≲ z.
  Proof.
    do 3 rewrite binary_le_eq_lb_mask; apply lb_mask_trans.
  Qed.

  Fact lb_mask_equiv_equal l m : l ≂ m <-> ⟦l⟧ = ⟦m⟧.
  Proof.
    unfold lb_mask_equiv.
    do 2 rewrite lb_mask_eq_binary_le; split.
    + intros (? & ?); apply le_antisym; apply binary_le_le; auto.
    + intros H; rewrite H; split; auto. 
  Qed.

  Fact equal_lb_mask_equiv x y : x = y <-> ⟬ x⟭ ≂⟬ y⟭.
  Proof.
    rewrite lb_mask_equiv_equal, lb_nat_lb, lb_nat_lb; tauto.
  Qed.

  Local Notation lbeq := lb_mask_equiv (only parsing).

  Add Parametric Morphism: (lb_nat) with signature (lbeq) ==> (eq) as lb_nat_eq.
  Proof. apply lb_mask_equiv_equal. Qed.

(*
  Hint Resolve dio_rel_binomial dio_rel_remainder.

  Section binary_le_dio.

    Let ble_equiv x y : x ≲ y <-> exists b, b = binomial y x /\ 1 = rem b 2.
    Proof.
      rewrite binary_le_binomial; split; eauto.
      intros (? & ? & ?); subst; auto.
    Qed.

    Theorem binary_le_diophatine x y : 
             dio_expression x
          -> dio_expression y
          -> dio_rel (fun v => x v ≲ y v).
    Proof.
      intros. 
      apply dio_rel_equiv with (1 := fun v => ble_equiv (x v) (y v)).
      dio_rel_auto.
    Qed.

  End binary_le_dio.

  Definition lb_dio (R : (nat -> lb) -> Prop) := { f | forall v, df_pred f (fun n => ⟦v n⟧) <-> R v }.

  Theorem lb_mask_diophantine x y : lb_dio (fun v => v x ⪯  v y).
  Proof.
    destruct (binary_le_diophatine (dio_expr_var x) (dio_expr_var y)) as (f & Hf).
    exists f; intros v; rewrite Hf, lb_mask_eq_binary_le; tauto.
  Qed.

*)

  Definition bool_add_with_rem a b c : bool * bool :=
    match a, b, c with 
     | ⟘, ⟘, ⟘ => (⟘,⟘)
     | ⟘, ⟘, ⟙ => (⟘,⟙)
     | ⟘, ⟙, ⟘ => (⟘,⟙)
     | ⟘, ⟙, ⟙ => (⟙,⟘)
     | ⟙, ⟘, ⟘ => (⟘,⟙)
     | ⟙, ⟘, ⟙ => (⟙,⟘)
     | ⟙, ⟙, ⟘ => (⟙,⟘)
     | ⟙, ⟙, ⟙ => (⟙,⟙)
    end.

  Notation bin_add := bool_add_with_rem.
  
  Fact bin_add_eq_00x x : bin_add ⟘ ⟘  x = (⟘,x).
  Proof. destruct x; auto. Qed.

  Fact bin_add_eq_0x0 x : bin_add ⟘ x ⟘  = (⟘,x).
  Proof. destruct x; auto. Qed.

  Fixpoint lb_succ a l :=
    match l with
      | nil  => a::nil
      | x::l => let (r,z) := bin_add ⟘ a x in z::lb_succ r l
    end.

  Fact lb_succ_spec_0 l : ⟦lb_succ ⟘ l⟧ = ⟦l⟧.
  Proof.
    induction l as [ | [] ]; simpl; auto.
  Qed.

  Fact lb_succ_spec_1 l : ⟦lb_succ ⟙ l⟧ = S ⟦l⟧.
  Proof.
    induction l as [ | [] ]; auto.
    + simpl lb_succ; rewrite lb_nat_fix_2.
      rewrite lb_nat_fix_1, IHl; omega.
    + simpl lb_succ; rewrite lb_nat_fix_2.
      rewrite lb_nat_fix_1, lb_succ_spec_0; omega.
  Qed.

  Fact lb_succ_spec a l : ⟦lb_succ a l⟧ = bool2nat a + ⟦l⟧.
  Proof.
    destruct a.
    + rewrite lb_succ_spec_1; auto.
    + rewrite lb_succ_spec_0; auto.
  Qed.

  Fact lb_succ_bot l : lb_succ ⟘ l ≂ l.
  Proof.
    induction l as [ | x ]; simpl; auto.
    + split; repeat constructor.
    + destruct x; rewrite IHl; auto.
  Qed.

  Fixpoint lb_plus a l m :=
    match l, m with
      | nil,   m   => lb_succ a m
      | l,    nil  => lb_succ a l
      | x::l, y::m => let (r,z) := bin_add a x y in z::lb_plus r l m
    end.

  Fact lb_plus_fix_0 a l : lb_plus a nil l = lb_succ a l.
  Proof. auto. Qed.

  Fact lb_plus_fix_1 a l : lb_plus a l nil = lb_succ a l.
  Proof. destruct l; auto. Qed.

  Fact lb_plus_fix_2 a x y l m : lb_plus a (x::l) (y::m) = let (r,z) := bin_add a x y in z::lb_plus r l m.
  Proof. auto. Qed.

  Fact lb_plus_spec a l m : ⟦lb_plus a l m⟧ = bool2nat a + ⟦l⟧ + ⟦m⟧.
  Proof.
    revert a m; induction l as [ | x l IHl ]; intros a m.
    + rewrite lb_plus_fix_0, lb_succ_spec, lb_nat_fix_0; omega.
    + destruct m as [ | y m ].
      * rewrite lb_plus_fix_1, lb_succ_spec, lb_nat_fix_0; omega.
      * rewrite lb_plus_fix_2, lb_nat_fix_3, lb_nat_fix_3.
        destruct a; destruct x; destruct y; simpl; rewrite IHl; simpl; omega.
  Qed.

  Local Infix "⊕" := (lb_plus ⟘ ) (at level 41, left associativity). 

  Fact lb_plus_spec_0 l m : ⟦l⊕m⟧ = ⟦l⟧ + ⟦m⟧.
  Proof. rewrite lb_plus_spec; simpl; auto. Qed.

  Add Parametric Morphism a: (lb_plus a) with signature (lbeq) ==> (lbeq) ==> (lbeq) as lb_plus_eq.
  Proof.
    intros x1 y1 E1 x2 y2 E2; revert E1 E2.
    do 3 rewrite lb_mask_equiv_equal.
    do 2 rewrite lb_plus_spec.
    intros; f_equal; auto.
  Qed.

  Fact lb_ortho_plus l m : l ⟂ m <-> l ⪯ l⊕m.
  Proof.
    split.
    + induction 1 as [ l | l | x y l m [ H1 | H1 ] H2 IH2 ].
      * constructor. 
      * rewrite lb_plus_fix_1.
        rewrite lb_mask_eq_binary_le, lb_succ_spec; simpl.
        rewrite <- lb_mask_eq_binary_le; apply lb_mask_refl.
      * rewrite lb_plus_fix_2.
        subst x; rewrite bin_add_eq_00x.
        destruct y; constructor; auto.
      * rewrite lb_plus_fix_2.
        subst y; rewrite bin_add_eq_0x0.
        destruct x; constructor; auto.
    + revert m; induction l as [ | x l IHl ].
      * intros; constructor.
      * intros [ | y m ] H.
        - constructor.
        - rewrite lb_plus_fix_2 in H.
          destruct x; destruct y; simpl in H; try (apply lb_mask_inv_cons_cons in H; tauto);
            apply lb_mask_inv_cons, proj2 in H; constructor; auto.
  Qed.

(*

  Theorem lb_ortho_diophantine x y : lb_dio (fun v => v x ⟂ v y).
  Proof.
    destruct (@lb_mask_diophantine 0 1) as (f & Hf).
    exists (df_subst (fun n => match n with 0 => de_var x | _ => de_add (de_var x) (de_var y) end) f).
    intros v; rewrite df_pred_subst.
    set (w z := match z with 0 => v x | _ => lb_plus ⟘  (v x) (v y) end).
    rewrite df_pred_ext with (ω := fun n => ⟦ w n ⟧).
    + rewrite Hf; unfold w; symmetry; apply lb_ortho_plus.
    + intros [ | ]; simpl; auto.
      rewrite lb_plus_spec_0; auto.
  Qed.

*)

  Fact lb_ortho_plus_join x y : x ⟂ y -> x⊕y ≂ x↑y.
  Proof.
    induction 1 as [ m | l | x y l m H1 H2 IH2 ].
    + rewrite lb_plus_fix_0, lb_join_right; apply lb_succ_bot.
    + rewrite lb_plus_fix_1, lb_join_left; apply lb_succ_bot.
    + rewrite lb_join_cons.
      apply lb_mask_equiv_equal.
      rewrite lb_plus_spec_0.
      do 3 rewrite lb_nat_fix_3.
      rewrite lb_mask_equiv_equal in IH2.
      rewrite <- IH2.
      rewrite lb_plus_spec_0.
      destruct x; destruct y; simpl; try ring.
      destruct H1; discriminate.
  Qed.

  Fact lb_ortho_plus_id a x y : a ⟂ x -> a ⟂ y -> x ⟂ y <-> (a⊕x)↓(a⊕y) ≂ a.
  Proof.
    intros H1 H2. 
    do 2 (rewrite lb_ortho_plus_join; auto). 
    rewrite <- lb_join_meet_distr, lb_ortho_meet_nil.
    split.
    + intros H3; rewrite H3, lb_join_left; auto.
    + intros H3; apply lb_ortho_mask_nil with a.
      * revert H1; apply lb_ortho_anti; auto.
      * rewrite <- H3, lb_join_comm; auto.
  Qed.

  (* A purely Boolean algebraic proof *)

  Fact lb_minus_plus a b : a ⪯ b -> exists x, b ≂ a⊕x /\ a ⪯  a⊕x.
  Proof.
    intros H.
    destruct lb_minus with (1 := H) as (x & H1 & H2).
    exists x; rewrite lb_ortho_plus_join; auto.
  Qed.

  (* A diophantine representation of bitwise and *)
 
  Theorem lb_meet_dio a b c : a ≂ b↓c <-> exists x y, b ≂ a⊕x /\ c ≂ a⊕y /\ a ⪯  a⊕x /\ a ⪯  a⊕y /\ x ⪯  x⊕y.
  Proof.
    split.
    + intros H.
      destruct (@lb_minus_plus a b) as (x & H1 & H2).
      { rewrite H; auto. }
      destruct (@lb_minus_plus a c) as (y & H3 & H4).
      { rewrite H; auto. }
      exists x, y; repeat (split; auto).
      rewrite <- lb_ortho_plus in H2, H4 |- *.
      rewrite lb_ortho_plus_join in H1, H3; auto.
      apply lb_ortho_meet_nil. 
      apply lb_ortho_mask_nil with (a := a).
      - revert H4; apply lb_ortho_anti; auto.
      - rewrite H, H1, H3.
        apply lb_meet_mono; auto.
    + intros (x & y & H1 & H2 & H3 & H4 & H5).
      rewrite <- lb_ortho_plus in H3, H4, H5.
      rewrite H1, H2.
      do 2 (rewrite lb_ortho_plus_join; auto).
      rewrite <- lb_join_meet_distr. 
      rewrite lb_ortho_meet_nil in H5.
      rewrite H5; rew lb.
  Qed.

  (* A diophantine representation of bitwise or *)

  Fact lb_join_dio a b c : a ≂ b↑c <-> exists x, a ≂ b⊕x /\ b ⪯  b⊕x /\ x ⪯ c /\ c ⪯ a.
  Proof.
    split. 
    + intros H. 
      destruct (@lb_minus_plus b a) as (x & H1 & H2).
      { rewrite H; auto. }
      exists x; repeat (split; auto).
      2: rewrite H; auto.
      rewrite <- lb_ortho_plus in H2.
      rewrite  lb_ortho_plus_join in H1; auto.
      rewrite lb_ortho_meet_nil in H2.
      rewrite <- (lb_meet_join_idem x b), lb_join_comm.
      rewrite <- H1, H, lb_meet_join_distr, (lb_meet_comm _ b), H2.
      rew lb.
    + intros (x & H1 & H2 & H3 & H4).
      rewrite <- lb_ortho_plus in H2.
      rewrite lb_ortho_plus_join in H1; auto.
      rewrite lb_ortho_meet_nil in H2.
      split.
      * rewrite H1; apply lb_join_mono; auto.
      * apply lb_join_spec; auto; rewrite H1; auto.
  Qed.

(* End lb_nat. *)

  Fixpoint lb_bots n :=
    match n with 
      | 0   => nil
      | S n => ⟘ :: lb_bots n
    end.
      
  Definition lb_shift n l := lb_bots n ++ l.

  Fact lb_shift_0 l : lb_shift 0 l = l.
  Proof. auto. Qed.

  Fact lb_shift_S n l : lb_shift (S n) l = ⟘ :: lb_shift n l.
  Proof. auto. Qed.

  Fact lb_nat_shift n l : ⟦lb_shift n l⟧ = ⟦l⟧*power n 2.
  Proof.
    unfold lb_shift.
    induction n as [ | n IHn ]; simpl lb_bots.
    + rewrite power_0; simpl; ring.
    + simpl app; rewrite lb_nat_fix_1, IHn, power_S; ring.
  Qed.

  Fact lb_shift_meet n l m : lb_shift n (l↓m) = (lb_shift n l)↓(lb_shift n m).
  Proof.
    induction n as [ | n IHn ].
    + repeat rewrite lb_shift_0; auto.
    + do 3 rewrite lb_shift_S.
      rewrite lb_meet_cons; f_equal; auto.
  Qed.

  Fact lb_shift_join n l m : lb_shift n (l↑m) = (lb_shift n l)↑(lb_shift n m).
  Proof.
    induction n as [ | n IHn ].
    + repeat rewrite lb_shift_0; auto.
    + do 3 rewrite lb_shift_S.
      rewrite lb_join_cons; f_equal; auto.
  Qed.

  Fact lb_shift_ortho n l m : length l <= n -> l ⟂ lb_shift n m.
  Proof.
    revert n.
    induction l as [ | x l IHl ]; intros [ | n ]; simpl; auto; try omega.
    intro; rewrite lb_shift_S; constructor; auto; apply IHl; omega.
  Qed.

  Fact lb_shift_ortho_meet n l m : length l <= n -> l ↓ lb_shift n m ≂ nil.
  Proof.
    intros; apply lb_ortho_meet_nil, lb_shift_ortho; auto.
  Qed.

  Fact nat_pow2_lb_shift n q : ⟬q*power n 2⟭ ≂ lb_shift n ⟬q⟭ .
  Proof.  
    apply lb_mask_equiv_equal.
    rewrite lb_nat_lb, lb_nat_shift, lb_nat_lb; auto.
  Qed.

  Fact nat_euclid_pow2_lb n r q : r < power n 2 -> ⟬r+q*power n 2⟭ ≂ ⟬r⟭ ↑lb_shift n ⟬q⟭ .
  Proof.
    intros H.
    apply lb_mask_equiv_equal.
    rewrite lb_nat_lb.
    rewrite <- lb_ortho_plus_join.
    2: apply lb_shift_ortho, nat_lb_length; auto.
    rewrite lb_plus_spec_0; f_equal.
    + rewrite lb_nat_lb; auto.
    + rewrite lb_nat_shift, lb_nat_lb; auto.
  Qed.

  Definition nat_meet n m := ⟦ ⟬n⟭↓⟬m⟭ ⟧.
  Local Infix "⇣" := nat_meet (at level 40, left associativity).

  Fact nat_meet_comm n m : n⇣m = m⇣n.
  Proof.
    apply lb_mask_equiv_equal.
    rewrite lb_meet_comm; auto.
  Qed.

  Fact nat_meet_left n m : n⇣m ≲ n.
  Proof.
    apply binary_le_eq_lb_mask.
    unfold nat_meet.
    rewrite lb_mask_nat; auto.
  Qed.

  Fact nat_meet_right n m : n⇣m ≲ m.
  Proof.
    apply binary_le_eq_lb_mask.
    unfold nat_meet.
    rewrite lb_mask_nat; auto.
  Qed.

  Hint Resolve nat_meet_left nat_meet_right.

  Fact binary_le_nat_meet n m : n ≲ m <-> n⇣m = n.
  Proof.
    rewrite equal_lb_mask_equiv.
    rewrite binary_le_eq_lb_mask.
    unfold nat_meet.
    rewrite nat_lb_nat.
    apply lb_mask_meet.
  Qed.
  
  Theorem nat_meet_dio a b c : a = b⇣c <-> exists x y,  b = a+x
                                                     /\ c = a+y
                                                     /\ a ≲ a+x
                                                     /\ a ≲ a+y
                                                     /\ x ≲ x+y.
  Proof.
    unfold nat_meet.
    rewrite equal_lb_mask_equiv, nat_lb_nat.
    rewrite lb_meet_dio.
    split; intros (x & y & H1 & H2 & H3 & H4 & H5).
    + exists ⟦x⟧, ⟦y⟧.
      revert H1 H2 H3 H4 H5.
      repeat rewrite lb_mask_equiv_equal.
      repeat rewrite lb_mask_eq_binary_le.
      repeat rewrite lb_plus_spec_0.
      repeat rewrite lb_nat_lb; auto.
    + exists ⟬ x⟭, ⟬ y⟭ .
      repeat rewrite lb_mask_equiv_equal.
      repeat rewrite lb_mask_eq_binary_le.
      rewrite H1, H2.
      repeat rewrite lb_plus_spec_0.
      repeat rewrite lb_nat_lb.
      auto.
  Qed.

  (* This is how we compute the meet by division by powers of 2 *)

  Lemma nat_meet_mult_power2 q x y : (x*power q 2) ⇣ (y*power q 2) 
                                    = (x⇣y)*power q 2.
  Proof.
    unfold nat_meet.
    rewrite <- lb_nat_shift, lb_shift_meet.
    apply lb_mask_equiv_equal.
    do 2 rewrite nat_pow2_lb_shift; auto.
  Qed.

  Lemma nat_meet_euclid_power_2 q r1 d1 r2 d2 : 
           r1 < power q 2 
        -> r2 < power q 2 
        -> (r1+d1*power q 2) ⇣ (r2+d2*power q 2) 
         = (r1⇣r2) + (d1⇣d2)*power q 2.
  Proof.
    unfold nat_meet.
    intros H1 H2.
    do 2 (rewrite nat_euclid_pow2_lb; auto).
    rewrite <- lb_nat_shift, <- lb_plus_spec_0.
    apply lb_mask_equiv_equal.
    rewrite lb_ortho_plus_join.
    2: apply lb_shift_ortho, lb_meet_length_le; apply nat_lb_length; auto.
    rewrite lb_shift_meet.
    rewrite lb_meet_join_distr.
    do 2 rewrite (lb_meet_comm (_↑_)).
    do 2 rewrite lb_meet_join_distr.
    rewrite lb_shift_ortho_meet; try (apply nat_lb_length; auto; fail).
    rew lb. 
    rewrite (lb_meet_comm (lb_shift _ _)).
    rewrite lb_shift_ortho_meet; try (apply nat_lb_length; auto; fail).
    rew lb.
    rewrite lb_meet_comm.
    rewrite (lb_meet_comm (lb_shift _ _)); auto.
  Qed.

  Lemma nat_meet_euclid_2 r1 d1 r2 d2 : 
           r1 < 2 
        -> r2 < 2 
        -> (r1+2*d1) ⇣ (r2+2*d2) 
         = (r1⇣r2) + 2*(d1⇣d2).
  Proof.
    intros H1 H2.
    do 3 rewrite (mult_comm 2).
    apply nat_meet_euclid_power_2 with (q := 1); auto.
  Qed.
  
  Fact nat_meet_0n n : 0⇣n = 0.
  Proof.
    apply equal_lb_mask_equiv.
    unfold nat_meet.
    rewrite nat_lb_fix_0; rew lb.
    apply nat_lb_nat.
  Qed.

  Fact nat_meet_n0 n : n⇣0 = 0.
  Proof. rewrite nat_meet_comm, nat_meet_0n; auto. Qed.

  Fact nat_meet_idem n : n⇣n = n.
  Proof. 
    apply equal_lb_mask_equiv.
    unfold nat_meet.
    rewrite nat_lb_nat, lb_meet_idem; auto.
  Qed.

  Hint Resolve nat_meet_0n nat_meet_n0 nat_meet_idem.

  Fact nat_meet_assoc n m k : n⇣(m⇣k) = n⇣m⇣k.
  Proof.
    apply equal_lb_mask_equiv; unfold nat_meet.
    repeat rewrite nat_lb_nat.
    rewrite lb_meet_assoc; auto.
  Qed.

  Section nat_meet_power2_neq.

    Let nat_meet_power2_lt x y : x < y -> (power x 2) ⇣ (power y 2) = 0. 
    Proof.
      intros H.
      replace (power x 2) with (power x 2 + 0*power y 2) by ring.
      replace (power y 2) with (0 + 1*power y 2) at 2 by ring.
      rewrite nat_meet_euclid_power_2.
      + rewrite nat_meet_n0, nat_meet_0n; ring.
      + apply power_smono_l; omega.
      + apply power_ge_1; omega.
    Qed.

    Fact nat_meet_power2_neq x y : x <> y -> (power x 2) ⇣ (power y 2) = 0. 
    Proof.
      intros H.
      destruct (lt_eq_lt_dec x y) as [[]|]; try omega.
      + apply nat_meet_power2_lt; auto.
      + rewrite nat_meet_comm; apply nat_meet_power2_lt; auto.
    Qed.

  End nat_meet_power2_neq.

  Fact nat_meet_12n n : 1⇣(2*n) = 0.
  Proof.
    replace 1 with (1+0*power 1 2) at 1 by auto.
    replace (2*n) with (0+n*power 1 2) by (rewrite power_1; ring).
    rewrite nat_meet_euclid_power_2; rewrite power_1; try omega.
    rewrite nat_meet_0n, nat_meet_n0; auto.
  Qed.

  Fact nat_meet_12 : 1⇣2 = 0.
  Proof. apply (nat_meet_12n 1). Qed.

  Fact power_2_minus_1 n : power (S n) 2 - 1 = 1 + 2*(power n 2 - 1).
  Proof.
    rewrite power_S.
    generalize (@power_ge_1 n 2); intros; omega.
  Qed.

  Fact power_2_minus_1_gt n x : x < power n 2 <-> x ≲ power n 2 - 1.
  Proof.
    split.
    2: { intro Hx.
         apply binary_le_le in Hx.
         generalize (@power_ge_1 n 2); intros; omega. }
    intros H1.
    assert (x <= power n 2 -1) as H by omega; clear H1. 
    rewrite binary_le_nat_meet.
    revert x H; induction n as [ | n IHn ]; intros x Hx.
    + rewrite power_0 in Hx; cutrewrite (x=0); auto; omega.
    + destruct (eq_nat_dec x 0) as [ H | H ].
      - rewrite H; auto.
      - destruct (euclid_2_div x) as (H1 & H2).
        rewrite H1, power_2_minus_1.
        rewrite nat_meet_euclid_2; try omega.
        rewrite IHn.
        * f_equal; destruct H2 as [ H2 | H2 ]; rewrite H2; auto.
        * rewrite power_2_minus_1 in Hx; omega.
  Qed.

  Definition nat_join n m := ⟦ ⟬n⟭↑⟬m⟭ ⟧.
  Local Infix "⇡" := nat_join (at level 50, left associativity).

  Fact nat_join_comm n m : n⇡m = m⇡n.
  Proof.
    apply lb_mask_equiv_equal.
    rewrite lb_join_comm; auto.
  Qed.

  Fact nat_join_left n m : n ≲ n⇡m.
  Proof.
    apply binary_le_eq_lb_mask.
    unfold nat_join.
    rewrite lb_mask_nat; auto.
  Qed.

  Fact nat_join_right n m : m ≲ n⇡m.
  Proof.
    apply binary_le_eq_lb_mask.
    unfold nat_join.
    rewrite lb_mask_nat; auto.
  Qed.

  Hint Resolve nat_join_left nat_join_right.

  Fact nat_join_0n n : 0⇡n = n.
  Proof.
    apply equal_lb_mask_equiv.
    unfold nat_join.
    rewrite nat_lb_fix_0; rew lb.
    apply nat_lb_nat.
  Qed.

  Fact nat_join_n0 n : n⇡0 = n.
  Proof. rewrite nat_join_comm, nat_join_0n; auto. Qed.

  Fact nat_join_idem n : n⇡n = n.
  Proof. 
    apply equal_lb_mask_equiv.
    unfold nat_join.
    rewrite nat_lb_nat, lb_join_idem; auto.
  Qed.

  Fact nat_join_mono a b u v : a ≲ b -> u ≲ v -> a⇡u ≲ b⇡v.
  Proof.
    do 3 rewrite binary_le_eq_lb_mask; unfold nat_join.
    do 2 rewrite nat_lb_nat.
    apply lb_join_mono.
  Qed.

  Fact nat_join_assoc n m k : n⇡(m⇡k) = n⇡m⇡k.
  Proof.
    apply equal_lb_mask_equiv; unfold nat_join.
    repeat rewrite nat_lb_nat.
    rewrite lb_join_assoc; auto.
  Qed.

  Fact nat_join_meet_distr_l n m k : n⇡(m⇣k) = (n⇡m)⇣(n⇡k).
  Proof.
    apply equal_lb_mask_equiv.
    unfold nat_join, nat_meet.
    repeat rewrite nat_lb_nat.
    rewrite lb_join_meet_distr; auto.
  Qed.

  Fact nat_meet_join_distr_l n m k : n⇣(m⇡k) = (n⇣m)⇡(n⇣k).
  Proof.
    apply equal_lb_mask_equiv.
    unfold nat_join, nat_meet.
    repeat rewrite nat_lb_nat.
    rewrite lb_meet_join_distr; auto.
  Qed.
  
  Hint Resolve nat_join_0n nat_join_n0 nat_join_assoc.

  Lemma nat_join_monoid : monoid_theory nat_join 0.
  Proof. split; auto. Qed.
 
  Hint Resolve nat_join_monoid nat_join_mono.

  Fact nat_meet_joins_distr_l m n f : m ⇣ msum nat_join 0 n f = msum nat_join 0 n (fun i => m ⇣ f i).
  Proof.
    revert m f; induction n as [ | n IHn ]; intros m f.
    + do 2 rewrite msum_0; auto.
    + do 2 rewrite msum_S.
      rewrite nat_meet_join_distr_l, IHn; auto.
  Qed.

  Fact nat_join_binary_le n m k : n⇡m ≲ k <-> n ≲ k /\ m ≲ k.
  Proof.
    split.
    + intros H; split; apply binary_le_trans with (2 := H); auto.
    + intros (H1 & H2). rewrite <- (nat_join_idem k); auto.
  Qed. 

  Fact nat_joins_binary_le_left n f m : msum nat_join 0 n f ≲ m <-> forall i, i < n -> f i ≲ m.
  Proof.
    revert f; induction n as [ | n IHn ]; intros f.
    + rewrite msum_0; split; auto; intros; omega.
    + rewrite msum_S, nat_join_binary_le, IHn.
      split.
      * intros [H1 H2] [] ?; auto; apply H2; omega.
      * intros H; split; intros; apply H; omega.
  Qed.

  Fact nat_joins_binary_le_right m n f : (exists i, i < n /\ m ≲ f i) -> m ≲ msum nat_join 0 n f.
  Proof.
    intros (i & H1 & H2).
    apply binary_le_trans with (1 := H2).
    clear m H2.
    revert f i H1; induction n as [ | n IHn ]; intros f [ | i ] Hi; try omega; rewrite msum_S; auto.
    apply binary_le_trans with (2 := nat_join_right _ _).
    apply (IHn (fun i => f (S i))); omega.
  Qed.

  Fact nat_joins_binary_le n m f g :
           (forall i, i < n -> exists j, j < m /\ f i ≲ g j)
        -> msum nat_join 0 n f ≲ msum nat_join 0 m g.
  Proof.
    intros H.
    rewrite nat_joins_binary_le_left.
    intros i Hi; apply nat_joins_binary_le_right; auto.
  Qed.

  Fact nat_double_joins_binary_le n m f g : 
           (forall i j, j < i < n -> exists k, k < m /\ f i j ≲ g k)
        -> msum nat_join 0 n (fun i => msum nat_join 0 i (f i)) ≲ msum nat_join 0 m g.
  Proof.
    intros H.
    rewrite nat_joins_binary_le_left.
    intros; apply nat_joins_binary_le; auto.
  Qed.

  Fact binary_le_join_inv m a b : m ≲ a⇡b -> m = (m⇣a)⇡(m⇣b).
  Proof.
    rewrite binary_le_nat_meet, nat_meet_join_distr_l; auto.
  Qed.

  Fact binary_le_joins_inv m n f : m ≲ msum nat_join 0 n f
                              -> { k : nat & { g : nat -> nat & { h | m = msum nat_join 0 k g
                                                                   /\ k <= n 
                                                                   /\ (forall i, i < k -> g i <> 0 /\ g i ≲ f (h i))  
                                                                   /\ (forall i, i < k -> h i < n)
                                                                   /\ (forall i j, i < j < k -> h i < h j) } } }.
  Proof.
    revert m f; induction n as [ | n IHn ]; intros m f H.
    + rewrite msum_0 in H; apply binary_le_zero_inv in H.
      subst; exists 0, (fun _ => 0), (fun _ => 0); split.
      - rewrite msum_0; auto.
      - split; [ | split; [ | split ] ]; intros; omega.
    + rewrite msum_S in H.
      apply binary_le_join_inv in H.
      destruct (@IHn (m ⇣ msum nat_join 0 n (fun n => f (S n))) (fun n => f (S n)))
        as (k & g & h & H1 & H0 & H2 & H3 & H4); auto.
      rewrite H1 in H.
      case_eq (m ⇣ f 0).
      * intros E.
        rewrite E, nat_join_0n in H.
        exists k, g, (fun i => S (h i)); repeat (split; auto).
        - intros i Hi; specialize (H3 _ Hi); omega.
        - intros i j Hij; specialize (H4 _ _ Hij); omega.
      * intros u Hu.
        exists (S k), (fun i => match i with 0 => S u | S i => g i end),
                      (fun i => match i with 0 => 0   | S i => S (h i) end); split; [  | split; [ | split; [ | split ] ] ].
        - rewrite H, msum_S, <- Hu; auto.
        - omega.
        - intros [ | i ]; split; try omega. 
          ++ rewrite <- Hu; auto.
          ++ apply H2; omega.
          ++ apply H2; omega.
        - intros [ | i ] Hi; try omega.
          apply lt_S_n, H3 in Hi; omega.
        - intros [ | i ] [ | j ] (G1 & G2); simpl; try omega.
          apply lt_n_S, H4; omega.
  Qed.

  Fact binary_le_joins_inv' m n f : m ≲ msum nat_join 0 n f
                              -> { g | m = msum nat_join 0 n g /\ forall i, i < n -> g i ≲ f i }.  
  Proof.
    intros H; exists (fun i => m⇣f i); split.
    2: intros; auto.
    apply binary_le_nat_meet in H.
    rewrite <- H at 1.
    apply nat_meet_joins_distr_l.
  Qed.

  (* This is how we compute the meet by division by powers of 2 *)

  Lemma nat_join_mult_power2 q x y : (x*power q 2) ⇡ (y*power q 2) 
                                    = (x⇡y)*power q 2.
  Proof.
    unfold nat_join.
    rewrite <- lb_nat_shift, lb_shift_join.
    apply lb_mask_equiv_equal.
    do 2 rewrite nat_pow2_lb_shift; auto.
  Qed.

  Lemma binary_le_mult_power2_inv m x q : m ≲ x * power q 2 -> m <> 0 -> { y | m = y * power q 2 /\ y <> 0 /\ y ≲ x }.
  Proof.
    intros H1 H2.
    destruct (@euclid m (power q 2)) as (d & r & H3 & H4).
    + generalize (@power_ge_1 q 2); intros; omega.
    + apply binary_le_nat_meet in H1.
      rewrite plus_comm in H3.
      rewrite H3, <- (Nat.add_0_l (x*_)) in H1.
      rewrite nat_meet_euclid_power_2 in H1; auto.
      rewrite nat_meet_n0 in H1.
      rewrite (plus_comm r), (plus_comm 0) in H1.
      apply div_rem_uniq in H1; auto.
      2: generalize (@power_ge_1 q 2); intros; omega.
      destruct H1 as (H0 & H1).
      subst r; simpl in H3.
      exists d; split; auto.
      split.
      - contradict H2; subst; auto.
      - rewrite <- H0; auto.
  Qed.
 
  Lemma nat_join_euclid2 q r1 d1 r2 d2 : 
           r1 < power q 2 
        -> r2 < power q 2 
        -> (r1+d1*power q 2) ⇡ (r2+d2*power q 2) 
         = (r1⇡r2) + (d1⇡d2)*power q 2.
  Proof.
    unfold nat_join.
    intros H1 H2.
    do 2 (rewrite nat_euclid_pow2_lb; auto).
    rewrite <- lb_nat_shift, <- lb_plus_spec_0.
    apply lb_mask_equiv_equal.
    rewrite lb_ortho_plus_join.
    2: apply lb_shift_ortho, lb_join_length_le; apply nat_lb_length; auto.
    rewrite lb_shift_join.
    rewrite  lb_join_assoc, <- (lb_join_assoc ⟬ r1 ⟭).
    rewrite (lb_join_comm _ ⟬ r2 ⟭).
    repeat rewrite lb_join_assoc; auto.
  Qed.

  Fact nat_lb_plus n m : ⟬n+m⟭ ≂ ⟬n⟭⊕⟬m⟭.
  Proof.
    rewrite lb_mask_equiv_equal, lb_nat_lb, lb_plus_spec_0. 
    f_equal; symmetry; apply lb_nat_lb.
  Qed.

  Fact nat_ortho_plus_join n m : n⇣m = 0 -> n+m = n⇡m.
  Proof.
    do 2 rewrite equal_lb_mask_equiv.
    unfold nat_meet, nat_join.
    do 2 rewrite nat_lb_nat.
    rewrite nat_lb_plus, nat_lb_fix_0.
    rewrite <- lb_ortho_meet_nil.
    apply lb_ortho_plus_join.
  Qed.

  Local Notation sum_powers := (fun r n f e => ∑ n (fun i => f i * power (e i) r)).

  Fact sum_powers_bound r n f e :
                 r <> 0
              -> (forall i, i < n -> f i < r) 
              -> (forall i j, i < j -> e i < e j)
              -> sum_powers r n f e < power (e n) r.
  Proof.
    intros Hr; revert f e.
    induction n as [ | n IHn ]; intros f e Hf He.
    + rewrite msum_0; apply power_ge_1; auto.
    + rewrite msum_plus1; auto.
      apply lt_le_trans with (power (S (e n)) r).
      2: apply power_mono_l; try omega; apply He; auto.
      rewrite power_S.
      apply lt_le_trans with (1*power (e n) r + f n * power (e n) r).
      * rewrite Nat.mul_1_l; apply plus_lt_le_compat; auto.
      * rewrite <- Nat.mul_add_distr_r; apply mult_le_compat; auto.
        apply Hf; auto.
  Qed.

  Fact sum_powers_euclid r n f e : (forall j, j < n -> e 1 <= e (S j))
        -> sum_powers r (S n) f e = f 0 * power (e 0) r 
                                  + sum_powers r n (fun i => f (S i)) (fun i => e (S i) - e 1) * power (e 1) r.
  Proof.
    intros Hf; simpl; f_equal.
    rewrite <- sum_0n_scal_r.
    apply msum_ext.
    intros i Hi.
    rewrite <- mult_assoc; f_equal.
    rewrite <- power_plus; f_equal.
    generalize (Hf _ Hi); omega.
  Qed.

  Fact nat_meet_joins m n f : m⇣msum nat_join 0 n f = msum nat_join 0 n (fun i => m⇣f i).
  Proof.
    revert f; induction n as [ | n IHn ]; intros f.
    + rewrite msum_0, msum_0, nat_meet_n0; auto.
    + do 2 rewrite msum_S.
      rewrite nat_meet_join_distr_l, IHn; auto.
  Qed.

  Fact nat_join_eq_0 n m : n⇡m = 0 <-> n = 0 /\ m = 0.
  Proof.
    split.
    + do 3 rewrite equal_lb_mask_equiv. 
      unfold nat_join; rewrite nat_lb_nat.
      repeat rewrite nat_lb_fix_0.
      apply lb_join_nil_eq.
    + intros []; subst; apply nat_join_0n.
  Qed.

  Fact nat_ortho_joins_left m n f : m⇣msum nat_join 0 n f = 0 
                           <-> forall i, i < n -> m⇣f i = 0.
  Proof.
    rewrite nat_meet_joins.
    revert f; induction n as [ | n IHn ]; intros f.
    + rewrite msum_0; split; auto; intros; omega.
    + rewrite msum_S, nat_join_eq_0, IHn.
      split.
      * intros [ H1 H2 ] [ | i ] ?; auto; apply H2; omega.
      * intros H; split; intros; apply H; omega.
  Qed.

  Fact nat_ortho_sum_join n f : (forall i j, i <> j -> i < n -> j < n -> f i ⇣ f j = 0)
                             -> ∑ n f = msum nat_join 0 n f.
  Proof.
    revert f; induction n as [ | n IHn ]; intros f Hf.
    + do 2 rewrite msum_0; auto.
    + do 2 rewrite msum_S.
      rewrite IHn.
      apply nat_ortho_plus_join, nat_ortho_joins_left.
      * intros; apply Hf; omega.
      * intros; apply Hf; omega.
  Qed.

  Fact nat_ortho_joins m n f g : msum nat_join 0 m f ⇣ msum nat_join 0 n g = 0 
                             <-> forall i j, i < m -> j < n -> f i ⇣ g j = 0.
  Proof.
    rewrite nat_ortho_joins_left.
    split; intros H.
    + intros i j H1 H2; specialize (H _ H2).
      rewrite nat_meet_comm in H |- *.
      rewrite nat_ortho_joins_left in H; auto.
    + intros i Hi; rewrite nat_meet_comm, nat_ortho_joins_left.
      intros j Hj; rewrite nat_meet_comm; auto.
  Qed.

  Local Notation "⇧" := (fun r n f e => msum nat_join 0 n (fun i => f i * power (e i) r)).

  Section nat_meet_digits.

    Variable (q : nat) (Hq : 0 < q) (r : nat) (Hr : r = power q 2).
          
    Implicit Types (f g : nat -> nat).

    Let Hr' : 2 <= r.
    Proof. rewrite Hr; apply (@power_mono_l 1 _ 2); omega. Qed.

    Fact nat_meet_powers_eq i a b : (a*power i r)⇣(b*power i r) = (a⇣b)*power i r.
    Proof. rewrite Hr, <- power_mult, nat_meet_mult_power2; auto. Qed.

    Fact binary_power_split i a : { u : nat & { v | a = u⇡(v*power i r) /\ forall k, u⇣(k*power i r) = 0 } }.
    Proof.
      destruct (@euclid a (power i r)) as (u & v & H1 & H2).
      + generalize (@power_ge_1 i r); intros; omega.
      + exists v, u.
        assert (forall k, v ⇣ (k*power i r) = 0) as E.
        { intros k; replace v with (v+0*power i r) by ring.
          replace (k*power i r) with (0+k*power i r) by ring.
          rewrite Hr, <- power_mult.
          rewrite nat_meet_euclid_power_2, nat_meet_0n, nat_meet_n0; auto.
          rewrite power_mult, <- Hr; auto. }
        split; auto.
        rewrite H1, plus_comm, nat_ortho_plus_join; auto.
    Qed.
        

    Fact binary_le_power_inv i a b : a ≲ b * power i r -> { a' | a = a' * power i r /\ a' ≲ b }.
    Proof.
      intros H.
      destruct (binary_power_split i a) as (u & v & H1 & H2).
      exists (v⇣b).
      rewrite binary_le_nat_meet in H.
      rewrite H1 in H at 1.
      rewrite nat_meet_comm, nat_meet_join_distr_l in H.
      rewrite (nat_meet_comm _ u), H2, nat_join_0n, nat_meet_comm in H.
      rewrite Hr, <- power_mult,  nat_meet_mult_power2, power_mult, <- Hr in H.
      split; auto.
    Qed.
  
    Section nat_meet_powers_neq.

      Let nat_meet_neq_powers i j a b : i < j -> a < r -> b < r -> (a*power i r)⇣(b*power j r) = 0.
      Proof.
        intros H1 Ha Hb.
        replace (a*power i r) with (a*power i r + 0*power j r) by ring.
        replace (b*power j r) with (0+b*power j r) by ring.
        rewrite Hr, <- power_mult, <- power_mult.
        rewrite  nat_meet_euclid_power_2.
        + rewrite nat_meet_n0, nat_meet_0n; ring.
        + do 2 rewrite power_mult; rewrite <- Hr.
          apply lt_le_trans with (power (S i) r).
          - rewrite power_S; apply mult_lt_compat_r; auto.
            apply power_ge_1; omega.
          - apply power_mono_l; omega.
        + rewrite power_mult, <- Hr.
          apply power_ge_1; omega.
      Qed.

      Fact nat_meet_powers_neq i j a b : i <> j -> a < r -> b < r -> (a*power i r)⇣(b*power j r) = 0.
      Proof.
        intros Hij Ha Hb.
        destruct (lt_eq_lt_dec i j) as [ [] | ]; try omega.
        + apply nat_meet_neq_powers; auto.
        + rewrite nat_meet_comm.
          apply nat_meet_neq_powers; auto.
      Qed.
 
    End nat_meet_powers_neq.

    Fact sum_powers_ortho n f e : 
                 (forall i, i < n -> f i < r) 
              -> (forall i j, i < n -> j < n -> e i = e j -> i = j)
              -> sum_powers r n f e = ⇧ r n f e.
    Proof.
      revert f e; induction n as [ | n IHn ]; intros f e H1 H2.
      + do 2 rewrite msum_0; auto.
      + rewrite msum_S.
        rewrite IHn.
        2: intros; apply H1; omega.
        2: intros i j Hi Hj E; apply H2 in E; omega.
        rewrite nat_ortho_plus_join.
        * rewrite msum_S; auto.
        * apply nat_ortho_joins_left.
          intros i Hi.
          apply nat_meet_powers_neq.
          - intros E; apply H2 in E; omega.
          - apply H1; omega.
          - apply H1; omega.
    Qed.

    Section double_sum_powers_ortho.
 
      Variable (n : nat) (f e : nat -> nat -> nat)
               (Hf : forall i j, j < i < n -> f i j < r)
               (He : forall i1 j1 i2 j2, j1 < i1 < n -> j2 < i2 < n -> e i1 j1 = e i2 j2 -> i1 = i2 /\ j1 = j2).

      Let dsmpo_1 i : i < n -> sum_powers r i (f i) (e i) = ⇧ r i (f i) (e i).
      Proof.
        intros Hi; apply sum_powers_ortho.
        + intros; apply Hf; omega.
        + intros ? ? ? ?; apply He; omega.
      Qed.

      Fact double_sum_powers_ortho : ∑ n (fun i => sum_powers r i (f i) (e i)) = msum nat_join 0 n (fun i => ⇧ r i (f i) (e i)).
      Proof.
        rewrite nat_ortho_sum_join.
        + apply msum_ext; intros; apply dsmpo_1; auto.
        + intros; do 2 (rewrite dsmpo_1; auto).
          apply nat_ortho_joins.
          intros; apply nat_meet_powers_neq; auto.
          intros E; apply He in E; omega.
      Qed.

    End double_sum_powers_ortho.

    Fact sinc_injective n f : (forall i j, i < j < n -> f i < f j) -> forall i j, i < n -> j < n -> f i = f j -> i = j.
    Proof.
      intros Hf i j Hi Hj E.
      destruct (lt_eq_lt_dec i j) as [ [] | ]; auto.
      + generalize (Hf i j); intros; omega.
      + generalize (Hf j i); intros; omega.
    Qed.

    Hint Resolve sinc_injective.

    Section binary_le_meet_sum_powers.

      Variable (n : nat) (f g e : nat -> nat)
               (Hf : forall i, i < n -> f i < r) 
               (Hg : forall i, i < n -> g i < r)
               (He : forall i j, i < j < n -> e i < e j).

      Fact meet_sum_powers : (sum_powers r n f e)⇣(sum_powers r n g e) 
                           = sum_powers r n (fun i => f i ⇣ g i) e.
      Proof.
        generalize (sinc_injective _ He); intros H0.
        simpl; do 3 (rewrite sum_powers_ortho; auto).
        rewrite nat_meet_joins.
        + apply msum_ext.
          intros i Hi; rewrite nat_meet_comm.
          rewrite nat_meet_joins.
          rewrite msum_only_one with (i := i); auto.
          * rewrite nat_meet_comm, Hr, <- power_mult.
            apply nat_meet_mult_power2.
          * intros j G1 G2; apply nat_meet_powers_neq; auto.
        + intros i Hi.
          apply le_lt_trans with (2 := Hf Hi).
          apply binary_le_le; auto.
      Qed.

      Fact binary_le_sum_powers : sum_powers r n f e ≲ sum_powers r n g e <-> forall i, i < n -> f i ≲ g i.
      Proof.
        rewrite binary_le_nat_meet, meet_sum_powers.
        split. 
        + intros E i Hi.
          apply binary_le_nat_meet.
          apply power_decomp_unique with (5 := E); auto.
          intros j Hj; apply le_lt_trans with (2 := Hf Hj).
          apply binary_le_le; auto.
        + intros H; apply msum_ext.
          intros; f_equal; apply binary_le_nat_meet; auto.
      Qed.
          
    End binary_le_meet_sum_powers.

    Fact sum_power_binary_lt p n f a : 
            0 < p <= q
         -> (forall i j, i < j < n -> f i < f j)
         -> (forall i, i < n -> a i < power p 2)  -> ∑ n (fun i => a i * power (f i) r) 
                                                   ≲ (power p 2-1) * ∑ n (fun i => power (f i) r).
    Proof.
      intros H1 H2 H3.
      generalize (sinc_injective _ H2); intros H4.
      rewrite <- sum_0n_scal_l.
      apply binary_le_nat_meet.
      rewrite meet_sum_powers; auto.
      2: intros i Hi; rewrite Hr; apply lt_le_trans with (1 := H3 _ Hi), power_mono_l; omega. 
      2: { rewrite Hr.
           intros i Hi. 
           generalize (@power_ge_1 p 2); intro.
           unfold lt.
           cutrewrite (S (power p 2 -1) = power p 2); try omega. 
           apply power_mono_l; omega. }
      apply msum_ext; intros i Hi; f_equal.
      apply binary_le_nat_meet, power_2_minus_1_gt.
      assert (a i < power p 2); try omega.
      apply lt_le_trans with (1 := H3 _ Hi), power_mono_l; omega.
    Qed.

    Fact sum_powers_binary_le_inv n f e m :
                 (forall i, i < n -> f i < r) 
              -> (forall i j, i < j < n -> e i < e j)
              -> m ≲ sum_powers r n f e
              -> { k : nat &
                 { g : nat -> nat & 
                 { h |  m = sum_powers r k g (fun i => e (h i)) 
                     /\ k <= n
                     /\ (forall i, i < k -> g i <> 0 /\ g i ≲ f (h i))
                     /\ (forall i, i < k -> h i < n)
                     /\ (forall i j, i < j < k -> h i < h j) } } }.
    Proof.
      intros H1 H2 H3.
      generalize (sinc_injective _ H2); intros H0.
      simpl in H3; rewrite sum_powers_ortho in H3; auto.
      apply binary_le_joins_inv in H3.
      destruct H3 as (k & g & h & H4 & H10 & H5 & H6 & H7).
      generalize (sinc_injective _ H7); intros H8.
      assert (forall i, { a | i < k -> g i = a * power (e (h i)) r /\ a <> 0 /\ a ≲ f (h i) }) as H.
      { intros i.
        destruct (le_lt_dec k i) as [ H | H ].
        * exists 0; intros; omega.
        * destruct (H5 _ H) as (G1 & G2).
          rewrite Hr, <- power_mult in G2.
          apply binary_le_mult_power2_inv in G2; auto.
          destruct G2 as (a & G2 & G3 & G4).
          rewrite power_mult, <- Hr in G2.
          exists a; auto. }
      set (g' := fun i => proj1_sig (H i)).
      assert (Hg' : forall i, i < k -> g i = g' i * power (e (h i)) r /\ g' i <> 0 /\ g' i ≲ f (h i)).
      { intro i; apply (proj2_sig (H i)). }
      generalize g' Hg'; clear H g' Hg'; intros g' Hg'.

      exists k, g', h; split; [ | split; [ | split ] ]; auto.
      - rewrite sum_powers_ortho, H4.
        * apply msum_ext. intros; apply Hg'; auto.
        * intros i Hi; apply le_lt_trans with (f (h i)).
          + apply binary_le_le, Hg'; auto.
          + apply H1, H6; auto.
        * intros ? ? ? ? E; apply H0 in E; auto.
      - intros; apply Hg'; auto.
    Qed.

    Fact binary_le_sum_powers_inv n f e m :
                 (forall i, i < n -> f i < r) 
              -> (forall i j, i < j < n -> e i < e j)
              -> m ≲ sum_powers r n f e
              -> { g | m = sum_powers r n g e /\ forall i, i < n -> g i ≲ f i }.
    Proof.
      intros H1 H2 H3.
      generalize (sinc_injective _ H2); intros H0.
      simpl in H3; rewrite sum_powers_ortho in H3; auto.
      apply binary_le_joins_inv' in H3.
      destruct H3 as (g & H3 & H4).
      assert (forall i, i < n -> { h | g i = h * power (e i) r /\ h ≲ f i }) as h_full.
      { intros i Hi; apply binary_le_power_inv; auto. }
      set (h := fun i => match le_lt_dec n i with left _ => 0 | right H => proj1_sig (h_full _ H) end).
      assert (Hh : forall i, i < n ->  g i = h i * power (e i) r /\ h i ≲ f i).
      { intros i Hi; unfold h; destruct (le_lt_dec n i) as [ | H' ]; try omega.
        apply (proj2_sig (h_full _ H')). }
      generalize h Hh; clear h_full h Hh; intros h Hh.
      exists h; split; auto.
      + rewrite H3.
        rewrite sum_powers_ortho; auto.
        * apply msum_ext; intros; apply Hh; auto.
        * intros i Hi; apply le_lt_trans with (2 := H1 _ Hi), binary_le_le, Hh; auto.
      + intros; apply Hh; auto.
    Qed.

    Fact sum_power_binary_lt_inv p n f e m :
            0 < p <= q
         -> (forall i j, i < j < n -> f i < f j)
         -> (forall i j, i < j < n -> e i < e j)
         -> m ≲ (power p 2-1) * ∑ n (fun i => power (f i) r)
         -> exists a, m = ∑ n (fun i => a i * power (f i) r) 
                   /\ forall i, i < n -> a i < power p 2.
    Proof.
      intros H1 H2 H3 H4.
      rewrite <- sum_0n_scal_l in H4.
      apply binary_le_sum_powers_inv in H4; auto.
      + destruct H4 as (a & H5 & H6).
        exists a; split; auto.
        intros i Hi; apply power_2_minus_1_gt; auto.
      + intros i Hi.
        apply lt_le_trans with (power p 2).
        - generalize (@power_ge_1 p 2); intros; omega.
        - rewrite Hr; apply power_mono_l; omega.
    Qed.

  End nat_meet_digits.

    
        
       
 
      


