(** This file gives some equational properties for manipulating matches.
 **)

Set Implicit Arguments.
Set Strict Implicit.

Create HintDb eq_rw discriminated.

Lemma eq_sym_eq
: forall T (a b : T) (pf : a = b) (F : T -> Type) val,
    match eq_sym pf in _ = x return F x with
      | eq_refl => val
    end =
    match pf in _ = x return F x -> F a with
      | eq_refl => fun x => x
    end val.
Proof.
  destruct pf. reflexivity.
Defined.

Lemma match_eq_sym_eq
: forall T (a b : T) (pf : a = b) F X,
    match pf in _ = t return F t with
      | eq_refl => match eq_sym pf in _ = t return F t with
                     | eq_refl => X
                   end
    end = X.
Proof.
  destruct pf. reflexivity.
Defined.
Hint Rewrite match_eq_sym_eq : eq_rw.

Lemma match_eq_sym_eq'
: forall T (a b : T) (pf : a = b) F X,
    match eq_sym pf in _ = t return F t with
      | eq_refl => match pf in _ = t return F t with
                     | eq_refl => X
                   end
    end = X.
Proof.
  destruct pf. reflexivity.
Defined.
Hint Rewrite match_eq_sym_eq' : eq_rw.


Lemma match_eq_match_eq
: forall T F (a b : T) (pf : a = b) X Y,
    X = Y ->
    match pf in _ = T return F T with
      | eq_refl => X
    end =
    match pf in _ = T return F T with
      | eq_refl => Y
    end.
Proof.
  intros. subst. auto.
Defined.

Lemma eq_sym_eq_trans
: forall T (a b c : T) (pf : a = b) (pf' : b = c),
    eq_sym (eq_trans pf pf') =
    eq_trans (eq_sym pf') (eq_sym pf).
Proof.
  clear. destruct pf. destruct pf'. reflexivity.
Defined.

(** Particular Instances **)
Lemma eq_Const_eq
: forall T (a b : T) (pf : a = b) (R : Type) val,
    match pf in _ = x return R with
      | eq_refl => val
    end = val.
Proof.
  destruct pf. reflexivity.
Defined.
Hint Rewrite eq_Const_eq : eq_rw.

Lemma eq_Arr_eq
: forall T (a b : T) (pf : a = b) (F G : T -> Type) val x,
    match pf in _ = x return F x -> G x with
      | eq_refl => val
    end x =
    match pf in _ = x return G x with
      | eq_refl => val match eq_sym pf in _ = x return F x with
                         | eq_refl => x
                       end
    end.
Proof.
  destruct pf. reflexivity.
Defined.
Hint Rewrite eq_Arr_eq : eq_rw.

Lemma eq_sym_eq_sym : forall (T : Type) (a b : T) (pf : a = b),
                        eq_sym (eq_sym pf) = pf.
Proof. destruct pf. reflexivity. Defined.
Hint Rewrite eq_sym_eq_sym : eq_rw.

Ltac autorewrite_eq_rw :=
  repeat progress (autorewrite with eq_rw;
                   repeat match goal with
                            | |- context [ match ?X in @eq _ _ _ return _ -> _ with
                                             | eq_refl => _
                                           end ] => rewrite (eq_Arr_eq X)
                          end).

Require Export ExtLib.Data.Eq.UIP_trans.
