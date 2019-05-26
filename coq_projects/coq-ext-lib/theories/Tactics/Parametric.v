Require Import Setoid.
Require Import RelationClasses.
Require Import Morphisms.

Set Implicit Arguments.
Set Strict Implicit.

(** The purpose of this tactic is to try to automatically derive morphisms
 ** for functions
 **)

Theorem Proper_red : forall T U (rT : relation T) (rU : relation U) (f : T -> U),
  (forall x x', rT x x' -> rU (f x) (f x')) ->
  Proper (rT ==> rU) f.
intuition.
Qed.

Theorem respectful_red : forall T U (rT : relation T) (rU : relation U) (f g : T -> U),
  (forall x x', rT x x' -> rU (f x) (g x')) ->
  respectful rT rU f g.
intuition.
Qed.
Theorem respectful_if_bool T : forall (x x' : bool) (t t' f f' : T) eqT,
  x = x' ->
  eqT t t' -> eqT f f' ->
  eqT (if x then t else f) (if x' then t' else f') .
intros; subst; auto; destruct x'; auto.
Qed.

Ltac derive_morph :=
repeat
  first [ lazymatch goal with
          | |- Proper _ _ => red; intros
          | |- (_ ==> _)%signature _ _ => red; intros
          end
        | apply respectful_red; intros
        | apply respectful_if_bool; intros
        | match goal with
          | [ H : (_ ==> ?EQ)%signature ?F ?F' |- ?EQ (?F _) (?F' _) ] =>
            apply H
          | [ |- ?EQ (?F _) (?F _) ] =>
            let inst := constr:(_ : Proper (_ ==> EQ) F) in
            apply inst
          | [ H : (_ ==> _ ==> ?EQ)%signature ?F ?F' |- ?EQ (?F _ _) (?F' _ _) ] =>
            apply H
          | [ |- ?EQ (?F _ _) (?F' _ _) ] =>
            let inst := constr:(_ : Proper (_ ==> _ ==> EQ) F) in
            apply inst
          | [ |- ?EQ (?F _ _ _) (?F _ _ _) ] =>
            let inst := constr:(_ : Proper (_ ==> _ ==> _ ==> EQ) F) in
            apply inst
          | [ |- ?EQ (?F _) (?F _) ] => unfold F
          | [ |- ?EQ (?F _ _) (?F _ _) ] => unfold F
          | [ |- ?EQ (?F _ _ _) (?F _ _ _) ] => unfold F
          end ].


Global Instance Proper_andb : Proper (@eq bool ==> @eq bool ==> @eq bool) andb.
derive_morph; auto.
Qed.

Section K.
  Variable F : bool -> bool -> bool.
  Hypothesis Fproper : Proper (@eq bool ==> @eq bool ==> @eq bool) F.
  Existing Instance Fproper.

  Definition food (x y z : bool) : bool :=
    F x (F y z).

  Global Instance Proper_food : Proper (@eq bool ==> @eq bool ==> @eq bool ==> @eq bool) food.
  Proof.
    derive_morph; auto.
  Qed.

  Global Instance Proper_S : Proper (@eq nat ==> @eq nat) S.
  Proof.
    derive_morph; auto.
  Qed.
End K.

Require Import List.

Section Map.
  Variable T : Type.
  Variable eqT : relation T.
  Inductive listEq {T} (eqT : relation T) : relation (list T) :=
  | listEq_nil : listEq eqT nil nil
  | listEq_cons : forall x x' y y', eqT x x' -> listEq eqT y y' ->listEq eqT (x :: y) (x' :: y').

  Theorem listEq_match V U (eqV : relation V) (eqU : relation U) : forall x x' : list V,
    forall X X' Y Y',
    eqU X X' ->
    (eqV ==> listEq eqV ==> eqU)%signature Y Y' ->
    listEq eqV x x' ->
    eqU (match x with
           | nil => X
           | x :: xs => Y x xs
         end)
        (match x' with
           | nil => X'
           | x :: xs => Y' x xs
         end).
  Proof.
    intros. induction H1; auto. derive_morph; auto.
  Qed.

  Variable U : Type.
  Variable eqU : relation U.
  Variable f : T -> U.
  Variable fproper : Proper (eqT ==> eqU) f.

  Definition hd (l : list T) : option T :=
    match l with
      | nil => None
      | l :: _ => Some l
    end.

(*
  Global Instance Proper_hd : Proper (listEq eqT ==> optionEq eqT) hd.
  Proof.
    foo. (** This has binders in the match... **)

  Abort.
*)

  Fixpoint map' (l : list T) : list U :=
    match l with
      | nil => nil
      | l :: ls => f l :: map' ls
    end.

  Global Instance Proper_map' : Proper (listEq eqT ==> listEq eqU) map'.
  Proof.
    derive_morph. induction H; econstructor; derive_morph; auto.
  Qed.
End Map.