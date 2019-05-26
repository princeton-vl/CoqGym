Require Import Coq.Strings.String.
Require Import Coq.Program.Program. 
Require Import Coq.Numbers.Natural.Peano.NPeano.
Require Import Coq.Arith.Arith.

Require Import ExtLib.Tactics.Consider.
Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Structures.Reducible.
Require Import ExtLib.Structures.Monoid.
Require Import ExtLib.Data.Char.
Require Import ExtLib.Data.Nat.

Set Implicit Arguments.
Set Strict Implicit.

Local Notation "x >> y" := (match x with
                              | Eq => y
                              | z => z
                            end) (only parsing, at level 30).

Definition bool_cmp (l r : bool) : comparison :=
  match l , r with
    | true , false => Gt
    | false , true => Lt
    | true , true
    | false , false => Eq
  end.

Definition ascii_cmp (l r : Ascii.ascii) : comparison :=
  match l , r with
    | Ascii.Ascii l1 l2 l3 l4 l5 l6 l7 l8 ,
      Ascii.Ascii r1 r2 r3 r4 r5 r6 r7 r8 =>
      bool_cmp l8 r8 >> bool_cmp l7 r7 >> bool_cmp l6 r6 >> bool_cmp l5 r5 >>
      bool_cmp l4 r4 >> bool_cmp l3 r3 >> bool_cmp l2 r2 >> bool_cmp l1 r1
  end.

Fixpoint string_dec (l r : string) : bool :=
  match l , r with
    | EmptyString , EmptyString => true
    | String l ls , String r rs =>
      if ascii_dec l r then string_dec ls rs
      else false
    | _ , _ => false
  end.

Theorem string_dec_sound : forall l r,
  string_dec l r = true <-> l = r.
Proof.
  induction l; destruct r; simpl; split; try solve [ intuition ; congruence ];
  consider (ascii_dec a a0); intros; subst. f_equal. eapply IHl; auto.
  apply IHl. congruence.
  inversion H. congruence.
Qed.

Global Instance RelDec_string : RelDec (@eq string) :=
{| rel_dec := string_dec |}.

Global Instance RelDec_Correct_string : RelDec_Correct RelDec_string.
Proof.
  constructor; auto using string_dec_sound.
Qed.

Global Instance Reflect_string_dec a b : Reflect (string_dec a b) (a = b) (a <> b).
Proof.
  apply iff_to_reflect; auto using string_dec_sound.
Qed.

Fixpoint string_cmp (l r : string) : comparison :=
  match l , r with
    | EmptyString , EmptyString => Eq
    | EmptyString , _ => Lt
    | _ , EmptyString => Gt
    | String l ls , String r rs =>
      ascii_cmp l r >> string_cmp ls rs
  end.

Section Program_Scope.
  Variable modulus : nat.
  Hypothesis one_lt_mod : 1 < modulus.

  Lemma _xxx : forall m n,
                 1 < m -> ~ n < m -> 0 < n.
  Proof.
    destruct n; destruct m; intros.
    inversion H. exfalso. apply H0. etransitivity. 2: eassumption. repeat constructor.
    inversion H.
    eapply neq_0_lt. congruence.
  Qed.

  Program Fixpoint nat2string (n:nat) {measure n}: string :=
    match NPeano.Nat.ltb n modulus as x return NPeano.Nat.ltb n modulus = x -> string with
      | true => fun _ => String (digit2ascii n) EmptyString
      | false => fun pf =>
        let m := NPeano.Nat.div n modulus in
        append (nat2string m) (String (digit2ascii (n - modulus * m)) EmptyString)
    end (@Logic.eq_refl _ (NPeano.Nat.ltb n modulus)).
  Next Obligation.
    eapply NPeano.Nat.div_lt; auto.
    consider (NPeano.Nat.ltb n modulus); try congruence. intros.
    eapply _xxx; eassumption.
  Defined.

End Program_Scope.

Definition nat2string10 : nat -> string.
refine (@nat2string 10 _).
repeat constructor.
Defined.

Definition nat2string2 : nat -> string.
refine (@nat2string 2 _).
repeat constructor.
Defined.

Definition nat2string8 : nat -> string.
refine (@nat2string 8 _).
repeat constructor.
Defined.

Definition nat2string16 : nat -> string.
refine (@nat2string 16 _).
repeat constructor.
Defined.

Global Instance Foldable_string : Foldable string ascii :=
  fun _ f base =>
    fix go ls :=
    match ls with
    | EmptyString => base
    | String l ls =>
      f l (go ls)
    end.

Section string.
  Inductive R_string_len : string -> string -> Prop :=
  | R_s_len : forall n m, length n < length m -> R_string_len n m.

  Theorem wf_R_string_len : well_founded R_string_len.
  Proof.
    constructor. intros.
    refine (@Fix _ _ wf_R_lt (fun n : nat => forall ls : string, n = length ls -> Acc R_string_len ls)
      (fun x rec ls pfls => Acc_intro _ _)
      _ _ refl_equal).
    refine (
      match ls as ls return x = length ls -> forall z : string, R_string_len z ls -> Acc R_string_len z with
        | EmptyString => fun (pfls : x = 0) z pf => _
        | String l ls => fun pfls z pf =>
          rec _ (match pf in R_string_len xs ys return x = length ys -> R_nat_lt (length xs) x with
                   | R_s_len n m pf' => fun pf_eq => match eq_sym pf_eq in _ = x return R_nat_lt (length n) x with
                                                     | refl_equal => R_lt pf'
                                                   end
                 end pfls) _ eq_refl
      end pfls).
    clear - pf; abstract (inversion pf; subst; simpl in *; inversion H).
  Defined.
End string.


Definition Monoid_string_append : Monoid string :=
{| monoid_plus := append
 ; monoid_unit := EmptyString
|}.
