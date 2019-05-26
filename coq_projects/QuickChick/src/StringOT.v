(* Ordering code by Antal :) *)

(* CH: We already have a similar class in RandomQC.v, why not use that
   one instead (maybe after moving it to separate file)? *)
Require Import OrderedType.

Require Import Bool.
Module BoolOT <: OrderedType.

Definition t := bool.

Definition eq       := @Logic.eq       bool.
Definition eq_refl  := @Logic.eq_refl  bool.
Definition eq_sym   := @Logic.eq_sym   bool.
Definition eq_trans := @Logic.eq_trans bool.
Definition eq_dec   := bool_dec.

Definition lt (b1 b2 : bool) : Prop := b1 = false /\ b2 = true.

Theorem lt_trans : forall x y z : bool, lt x y -> lt y z -> lt x z.
Proof. unfold lt; tauto. Qed.

Theorem lt_not_eq : forall x y : bool, lt x y -> ~ eq x y.
Proof. unfold lt, eq; intuition; congruence. Qed.

Theorem compare : forall x y : bool, Compare lt eq x y.
Proof.
  unfold lt, eq; repeat (let b := fresh in intros b; destruct b);
  [apply EQ | apply GT | apply LT | apply EQ]; auto.
Qed.

End BoolOT.

Require Import Ascii NArith.
Module AsciiOT <: OrderedType.

Definition t := ascii.

Definition eq       := @Logic.eq       ascii.
Definition eq_refl  := @Logic.eq_refl  ascii.
Definition eq_sym   := @Logic.eq_sym   ascii.
Definition eq_trans := @Logic.eq_trans ascii.
Definition eq_dec   := ascii_dec.

Definition lt (c d : ascii) : Prop := (N_of_ascii c < N_of_ascii d)%N.

Theorem lt_trans : forall c d e : ascii, lt c d -> lt d e -> lt c e.
Proof. intros until 0; unfold lt; apply N.lt_trans. Qed.

Theorem lt_not_eq : forall c d : ascii, lt c d -> ~ eq c d.
Proof.
  unfold lt, eq; red; intros;
  assert (N_of_ascii c = N_of_ascii d) as eq' by (f_equal; assumption);
  generalize dependent eq'; apply N.lt_neq; assumption.
Qed.

Theorem compare : forall c d : t, Compare lt eq c d.
Proof.
  unfold lt, eq; intros;
  remember (N_of_ascii c ?= N_of_ascii d)%N as C; symmetry in HeqC; destruct C;
  [ apply EQ; replace c with (ascii_of_N (N_of_ascii c))
                        by apply ascii_N_embedding;
              replace d with (ascii_of_N (N_of_ascii d))
                        by apply ascii_N_embedding;
              f_equal; apply N.compare_eq
  | apply LT
  | apply GT; apply N.gt_lt];
  assumption.
Qed.

End AsciiOT.

Require Import Coq.Strings.String.
Module StringOT <: OrderedType.

Definition t := string.

Definition eq       := @Logic.eq       string.
Definition eq_refl  := @Logic.eq_refl  string.
Definition eq_sym   := @Logic.eq_sym   string.
Definition eq_trans := @Logic.eq_trans string.
Definition eq_dec   := string_dec.

Inductive SOrdering := SLT | SEQ | SGT.

Fixpoint strcmp (s1 s2 : string) : SOrdering :=
  match s1, s2 with
    | EmptyString,    EmptyString    => SEQ
    | EmptyString,    String _ _     => SLT
    | String _   _,   EmptyString    => SGT
    | String ch1 s1', String ch2 s2' =>
        match AsciiOT.compare ch1 ch2 with
          | LT _ => SLT
          | EQ _ => strcmp s1' s2'
          | GT _ => SGT
        end
  end.

Definition lt (s1 s2 : string) := strcmp s1 s2 = SLT.

Local Ltac do_ascii_lt_trans :=
  match goal with
    | [  _ : AsciiOT.lt ?c1 ?c2
      ,  _ : AsciiOT.lt ?c2 ?c3
      |- _ ]
      => assert (AsciiOT.lt c1 c3) by (eapply AsciiOT.lt_trans; eauto)
  end.

Local Ltac not_ascii_lt_refl :=
  match goal with
    | [ _ : AsciiOT.lt ?c ?c |- _ ]
      => assert (c <> c) by (apply AsciiOT.lt_not_eq; assumption);
         congruence
  end.

Theorem lt_trans : forall s1 s2 s3 : string, lt s1 s2 -> lt s2 s3 -> lt s1 s3.
Proof.
  unfold lt; intros s1 s2; generalize dependent s1; induction s2 as [| c2 s2'].
  (* s2 = "" *)
    destruct s1; [trivial | simpl; congruence].
  (* s2 <> "" *)
    destruct s1 as [| c1 s1']; simpl.
    (* s1 = "" *)
      destruct s3; [congruence | trivial].
    (* s1 <> "" *)
      destruct s3 as [| c3 s3']; [congruence |].
      (* s3 <> "" *)
        destruct (AsciiOT.compare c1 c2) as [? | ? | ?] eqn:?;
        destruct (AsciiOT.compare c2 c3) as [? | ? | ?] eqn:?;
        destruct (AsciiOT.compare c1 c3) as [? | ? | ?] eqn:?;
        unfold AsciiOT.eq in *; subst;
        solve [ apply IHs2'
              | congruence
              | repeat (try not_ascii_lt_refl; do_ascii_lt_trans) ].
Qed.

Theorem lt_not_eq : forall s1 s2 : string, lt s1 s2 -> ~ eq s1 s2.
Proof.
  unfold lt, eq; induction s1 as [| c1 s1'].
  (* s1 = "" *)
    destruct s2; simpl; congruence.
  (* s1 <> "" *)
    destruct s2 as [| c2 s2']; simpl.
    (* s2 = "" *)
      congruence.
    (* s2 <> "" *)
        destruct (AsciiOT.compare c1 c2) as [? | ? | ?] eqn:?;
        intros Hc Heq; inversion Heq.
        (* c1 < c2 *)
          subst; not_ascii_lt_refl.
        (* c1 = c2 *)
          apply IHs1' in Hc; apply Hc; assumption.
        (* c1 > c2 *)
          congruence.
Qed.

Theorem compare : forall s1 s2 : t, Compare lt eq s1 s2.
Proof.
  unfold lt, eq; induction s1 as [| c1 s1'].
  (* s1 = "" *)
    destruct s2; [apply EQ | apply LT]; auto.
  (* s1 <> "" *)
    destruct s2 as [| c2 s2']; [apply GT; auto | ].
    destruct (AsciiOT.compare c1 c2) as [? | ? | ?] eqn:Hcmp.
    (* c1 < c2 *)
      apply LT; simpl; rewrite Hcmp; auto.
    (* c1 = c2 *)
      unfold AsciiOT.eq in *; subst.
      destruct (IHs1' s2'); [apply LT | apply EQ | apply GT];
      first [ simpl; rewrite Hcmp; assumption | subst; reflexivity ].
    (* c1 > c2 *)
      apply GT; simpl.
      destruct (AsciiOT.compare c2 c1) as [? | ? | ?] eqn:Hcmp'.
        reflexivity.
        unfold AsciiOT.eq in *; subst; not_ascii_lt_refl.
        do_ascii_lt_trans; not_ascii_lt_refl.
Qed.

End StringOT.
