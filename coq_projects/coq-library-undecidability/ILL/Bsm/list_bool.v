(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import List Arith Max Omega Wellfounded Bool.

Require Import utils.

Set Implicit Arguments.

Notation Zero := false.
Notation One  := true.

Fact list_bool_dec (l m : list bool) : { l = m } + { l <> m }.
Proof.  apply list_eq_dec, bool_dec. Qed.

(* {0,1}* = 0*1{0,1}* + 0* *)

Fact list_bool_choose lb : { k : _ & { tl | lb = list_repeat Zero k ++ One :: tl } }
                         + { k            | lb = list_repeat Zero k }.
Proof.
  induction lb as [ | [] lb IHlb ].
  * right; exists 0; auto.
  * left; exists 0, lb; auto.
  * destruct IHlb as [ (k & lc & H) | (k & H) ].
    - left; exists (S k), lc; subst; auto.
    - right; exists (S k); subst; auto.
Qed.

(* {0,1}* = 1*0{0,1}* + 1* *)

Fact list_bool_choose_sym lb : { k : _ & { tl | lb = list_repeat One k ++ Zero :: tl } }
                             + { k            | lb = list_repeat One k }.
Proof.
  induction lb as [ | [] lb IHlb ].
  * right; exists 0; auto.
  * destruct IHlb as [ (k & lc & H) | (k & H) ].
    - left; exists (S k), lc; subst; auto.
    - right; exists (S k); subst; auto.
  * left; exists 0, lb; auto.
Qed.

(* [n1,...,nk] ---> 0...{n1}...01 0{n2}1 ... 0{nk}1 *) 

Fixpoint list_nat_bool ln :=
  match ln with
    | nil   => nil
    | x::ll => list_repeat Zero x ++ One :: list_nat_bool ll
  end.

Lemma list_bool_decomp k lb : { ln : _ & { lc | lb = list_nat_bool ln ++ lc 
                                             /\ Exists (fun x => k <= x) ln } }
                            + { ln : _ & { r  | lb = list_nat_bool ln ++ list_repeat Zero r 
                                             /\ Forall (fun x => x < k) ln } }.
Proof.
  induction lb as [ lb IH ] using (measure_rect (@length _)).
  destruct (list_bool_choose lb) as [ (x & lr & Hlb) | (x & Hlb) ].
  * destruct (le_lt_dec k x) as [ Hk | Hk ].
    + left; exists (x::nil), lr; split; simpl.
      - subst; solve list eq.
      - constructor 1; auto.
    + destruct (IH lr) as [ (ln & ld & H2 & H3) | (ln & r & H2 & H3) ].
      - subst; rew length; omega.
      - left; exists (x::ln), ld; split.
        ** subst; solve list eq.
        ** constructor 2; auto.
      - right; exists (x::ln), r; split.
        ** subst; solve list eq.
        ** constructor; auto.
  * right; exists nil, x; split.
     - subst; solve list eq.
     - constructor.
Qed.

Definition list_bool_valid   k lb ln := lb = list_nat_bool ln /\ Forall (fun x => x < k) ln.
Definition list_bool_invalid k lb ln := exists lc, lb = list_nat_bool ln ++ lc
                                            /\ (   Exists (fun x => k <= x) ln
                                               \/  Forall (fun x => x < k) ln 
                                                /\ exists p, lc = list_repeat Zero (S p)).

Fact list_bool_valid_dec k lb : { ln | list_bool_valid k lb ln } + { ln | list_bool_invalid k lb ln }.
Proof.
  destruct (list_bool_decomp k lb) as [ (ln & lc & H1 & H2) | (ln & [|p] & H1 & H2) ].
  * right; exists ln, lc; tauto.
  * left; exists ln; split; auto; subst; solve list eq.
  * right; exists ln, (list_repeat Zero (S p)); split; auto.
    right; split; auto; exists p; auto.
Qed.

Fixpoint list_bool_nat l :=
  match l with 
    | nil     => 1
    | Zero::l => 0 + 2*list_bool_nat l
    | One::l  => 1 + 2*list_bool_nat l
  end.

Fact list_bool_nat_ge_1 l : 1 <= list_bool_nat l.
Proof. induction l as [ | [] ]; simpl in *; omega. Qed.

Unset Elimination Schemes.

Inductive list_bool_succ : list bool -> list bool -> Prop :=
  | in_lbs_0 : forall k l, list_bool_succ (list_repeat One k ++ Zero :: l) (list_repeat Zero k ++ One :: l)
  | in_lbs_1 : forall k,   list_bool_succ (list_repeat One k)              (list_repeat Zero (S k)).

Set Elimination Schemes.

Section list_bool_succ_props.

  Fact list_One_Zero_inj a b l m : list_repeat One a ++ Zero :: l = list_repeat One b ++ Zero :: m -> a = b /\ l = m.
  Proof.
    revert b l m; induction a as [ | a IHa ]; intros [ | b ] l m; simpl; try discriminate.
    inversion 1; auto.
    intros H.
    inversion H as [ H1 ].
    apply IHa in H1.
    destruct H1; subst; auto.
  Qed.

  Fact list_One_Zero_not a b l : list_repeat One a ++ Zero :: l <> list_repeat One b.
  Proof.
    revert b l; induction a as [ | a IHa ]; intros [ | b ] l; simpl; try discriminate.
    intros H.
    inversion H as [ H1 ].
    apply IHa in H1; auto.
  Qed.

  Fact list_One_inj a b : list_repeat One a = list_repeat One b -> a = b.
  Proof.
    intros H; apply f_equal with (f := @length _) in H; revert H.
    do 2 rewrite list_repeat_length; auto.
  Qed.

  Fact list_bool_succ_fun l m1 m2 : list_bool_succ l m1 -> list_bool_succ l m2 -> m1 = m2.
  Proof.
    intros H; revert l m1 H m2.
    intros ? ? [ k l | k ]; inversion 1.
    apply list_One_Zero_inj in H1; destruct H1; subst k0 l1; auto.
    symmetry in H1; apply list_One_Zero_not in H1; tauto.
    apply list_One_Zero_not in H1; tauto.
    apply list_One_inj in H1; subst; auto.
  Qed.

  Fact list_bool_succ_nil l : list_bool_succ nil l -> l = Zero::nil.
  Proof.
    intros H; symmetry; revert H; apply list_bool_succ_fun.
    constructor 2 with (k := 0).
  Qed.

  Fact list_bool_succ_neq : forall l m, list_bool_succ l m -> l <> m.
  Proof.
    intros ? ? [ [|k] l | [|k] ]; discriminate.
  Qed.

  Fact list_bool_succ_neq_nil l : ~ list_bool_succ l nil.
  Proof.
    inversion 1.
    destruct k; discriminate.
  Qed.

End list_bool_succ_props.

Section list_bool_next.

  Let list_bool_next_def l : { m | list_bool_succ l m }.
  Proof.
    destruct (list_bool_choose_sym l) as [ (k & tl & H) | (k & H) ]; subst l.
    * exists (list_repeat Zero k ++ One :: tl); constructor.
    * exists (list_repeat Zero (S k)); constructor.
  Qed.

  Definition list_bool_next l := proj1_sig (list_bool_next_def l).
  Definition list_bool_next_spec l : list_bool_succ l (list_bool_next l). 
  Proof. apply (@proj2_sig _ _). Qed.

  Fact list_bool_next_neq_nil l : list_bool_next l <> nil.
  Proof.
    intros H.
    generalize (list_bool_next_spec l).
    rewrite H.
    apply list_bool_succ_neq_nil.
  Qed.

  Fact iter_list_bool_next_nil l n : iter list_bool_next l n = nil -> n = 0 /\ l = nil.
  Proof.
    destruct n as [ | n ].
    simpl; auto.
    replace (S n) with (n+1) by omega.
    rewrite iter_plus; simpl.
    intros H.
    apply list_bool_next_neq_nil in H.
    destruct H.
  Qed.

End list_bool_next.

Fact list_bool_succ_nat l m : list_bool_succ l m -> 1 + list_bool_nat l = list_bool_nat m.
Proof.
  revert l m; intros ? ? [ k l | k ]; induction k; simpl in *; omega.
Qed.
 
Section list_bool_succ_rect.

  Variable (P : list bool -> Type)
           (HP0 : P nil)
           (HPS : forall l m, list_bool_succ l m -> P l -> P m).

  Let list_bool_succ_rec n : forall l, list_bool_nat l = n -> P l.
  Proof.
    induction n as [ | n IHn ]; intros l Hl.
    * generalize (list_bool_nat_ge_1 l); omega.
    * destruct (list_bool_choose l) as [ (k & tl & H) | ([ | k] & H) ]; subst l;
      [ generalize (in_lbs_0 k tl) | apply HP0 | generalize (in_lbs_1 k) ];
        intros E; apply HPS with (1 := E), IHn;
        apply list_bool_succ_nat in E; omega.
  Qed.

  Theorem list_bool_succ_rect : forall l, P l.
  Proof. intro; apply list_bool_succ_rec with (1 := eq_refl). Qed.

End list_bool_succ_rect.


(* The iteration of list_bool_next from Zero::nil visits every non-empty list of booleans *)

Theorem list_bool_next_total l : l <> nil -> { n | l = iter list_bool_next (Zero::nil) n }.
Proof.
  induction l as [ | l m Hlm IH ] using list_bool_succ_rect.
  intros []; auto.
  intros Hm.
  destruct (list_bool_choose_sym l) as [ (k & tl & H) | ([|k] & H) ].
  * destruct IH as (n & Hn).
    { subst; destruct k; discriminate. }
    exists (n+1); rewrite iter_plus; simpl.
    rewrite <- Hn.
    generalize (list_bool_next_spec l).
    apply list_bool_succ_fun; auto.
  * exists 0; simpl.
    apply list_bool_succ_fun with (1 := Hlm).
    subst; simpl; constructor 2 with (k := 0).
  * destruct IH as (n & Hn).
    { subst; simpl; discriminate. }
    exists (n+1); rewrite iter_plus; simpl.
    rewrite <- Hn.
    generalize (list_bool_next_spec l).
    apply list_bool_succ_fun; auto.
Qed.

