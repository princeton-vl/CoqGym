(* This program is free software; you can redistribute it and/or      *)
(* modify it under the terms of the GNU Lesser General Public License *)
(* as published by the Free Software Foundation; either version 2.1   *)
(* of the License, or (at your option) any later version.             *)
(*                                                                    *)
(* This program is distributed in the hope that it will be useful,    *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of     *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the      *)
(* GNU General Public License for more details.                       *)
(*                                                                    *)
(* You should have received a copy of the GNU Lesser General Public   *)
(* License along with this program; if not, write to the Free         *)
(* Software Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA *)
(* 02110-1301 USA                                                     *)


Require Import IZF_logic.

(** To define the type of natural numbers, we introduce an extra
    universe Typ0 *below* the universe Typ1 (so that we are now
    working in the PTS lambda-omega.3).

    Another possibility would be to consider an axiomatized type
    of natural numbers (as in the author's LICS submission). *)

Definition Typ0 : Typ1 := Type.

(*******************************************)
(** * The type of Church numerals in Typ1  *)
(*******************************************)

(** ** Definition of natural numbers **)

(** Notice that the following definition is *predicative*, and the
    dependent product ranging over all X:Typ0 builds a type in the
    next universe Typ1.  In practice, this "predicativisation" of
    the type of natural numbers induces some minor changes in the
    implementation of the predecessor function. *)

Definition nat : Typ1 := forall X : Typ0, X -> (X -> X) -> X.
Definition O : nat := fun X x f => x.
Definition S (n : nat) : nat := fun X x f => f (n X x f).

(** A natural number is `well-formed' if it is in the smallest class
    containing zero and closed under the successor function. *)

Definition wf_nat (n : nat) : Prop :=
  forall P : nat -> Prop, P O -> (forall p : nat, P p -> P (S p)) -> P n.

(** ** The predecessor function **)

(** For any type X : Typ0, we define the pseudo-square (sqr X) : Typ0
    and the constructor (pair X) : X->X->(sqr X) by setting: *)

Definition sqr (X : Typ0) : Typ0 := (X -> X -> X) -> X.
Definition pair (X : Typ0) (x y : X) : sqr X := fun f => f x y.

(** The corresponding projections *)

Definition fst (X : Typ0) (p : sqr X) : X := p (fun x _ => x).
Definition snd (X : Typ0) (p : sqr X) : X := p (fun _ y => y).

(** enjoy the expected definitional equalities:

    (fst X (pair X x y)) = x   and   (snd X (pair X x y)) = y. *)

(** Now, consider an arbitrary function f : X->X.  From this function, we
    define a function  (step X f) : (sqr X)->(sqr X)  that maps the pair
    (x, y) to the pair (y, (f y)) by setting: *)

Definition step (X : Typ0) (f : X -> X) (p : sqr X) : 
  sqr X := pair X (snd X p) (f (snd X p)).

(** If we iterate the function (step X f) from an arbitrary pair of the
    form (x, x), we obtain

    (step X f)^0 (x, x) = (x, x)
    (step X f)^1 (x, x) = (x, (f x))
    (step X f)^2 (x, x) = ((f x), (f (f x))
    ...
    (step X f)^n (x, x) = ((f ... (f x) ...), (f ... (f x) ...))
                            ^^^^^^^^           ^^^^^^^^
                            n-1 times          n times

    By extracting the first component of the result and abstracting it
    w.r.t. the variables X:Typ0, x:X and f:X->X, we thus obtain the
    predecessor of Church numeral n.  This is how the predecessor
    function is implemented: *)

Definition pred (n : nat) : nat :=
  fun X x f => fst X (n (sqr X) (pair X x x) (step X f)).

(** We easily check the following definitional equalities: *)

Lemma pred_O : eq nat (pred O) O.
Proof eq_refl nat O.

Lemma pred_SO : eq nat (pred (S O)) O.
Proof eq_refl nat O.

(** The following equality is really definitional!
    "I can see it, but I don't believe it"... *)

Lemma pred_SSn : forall n : nat, eq nat (pred (S (S n))) (S (pred (S n))).
Proof fun n => eq_refl nat (pred (S (S n))).

(** From this, we prove that the predecessor cancels a previous
    application of the successor function (by induction) *)

Lemma pred_S : forall n : nat, wf_nat n -> eq nat (pred (S n)) n.

Proof.
intros n Hn; apply Hn; clear Hn n.
(* Base case *)
apply pred_O.
(* Inductive case *)
intros n H; pattern n at 2 in |- *.
apply H; apply pred_SSn.
Qed.

(*******************************)
(** * Deriving Peano's axioms  *)
(*******************************)

(** ** First axiom of Peano **)

Lemma wf_nat_O : wf_nat O.

Proof fun P HO HS => HO.

(** ** Second axiom of Peano **)

Lemma wf_nat_S : forall n : nat, wf_nat n -> wf_nat (S n).

Proof fun n H P HO HS => HS n (H P HO HS).

(** ** Third axiom of Peano **)

Lemma eq_S_O : forall n : nat, wf_nat n -> eq nat (S n) O -> bot.

Proof fun n _ H => H (fun p => p Prop bot (fun _ => top)) top_intro.

Lemma eq_O_S : forall n : nat, wf_nat n -> eq nat O (S n) -> bot.

Proof fun n _ H => H (fun p => p Prop top (fun _ => bot)) top_intro.

(** Note that in the proofs of the two lemmas above, the assumption
    (wf_nat n) is not used. *)

(** ** Fourth axiom of Peano **)

Lemma eq_S_S :
 forall n : nat,
 wf_nat n -> forall p : nat, wf_nat p -> eq nat (S n) (S p) -> eq nat n p.

Proof.
intros n Hn p Hp H.
apply (pred_S n Hn).
apply (pred_S p Hp).
apply H; apply eq_refl.
Qed.

(** ** Fifth axiom of Peano **)

Lemma nat_ind :
 forall P : nat -> Prop,
 P O ->
 (forall p : nat, wf_nat p -> P p -> P (S p)) ->
 forall n : nat, wf_nat n -> P n.

Proof.
intros P HO HS n Hn.
apply (and_snd (wf_nat n) (P n)).
apply Hn; clear Hn n.
(* Base case *)
apply and_intro; [ exact wf_nat_O | assumption ].
(* Inductive case *)
intros n H; apply H; clear H.
intros H1 H2; apply and_intro.
apply wf_nat_S; assumption.
apply HS; assumption.
Qed.

Lemma nat_ind' :
 forall n : nat,
 wf_nat n ->
 forall P : nat -> Prop,
 P O -> (forall p : nat, wf_nat p -> P p -> P (S p)) -> P n.

Proof fun n Hn P HO HS => nat_ind P HO HS n Hn.

(****************)
(** * Ordering  *)
(****************)

Definition le (n m : nat) : Prop :=
  forall P : nat -> Prop, P n -> (forall p : nat, P p -> P (S p)) -> P m.

(** This relation is reflexive and transitive, and closed under the
    successor function.  Notice that these lemmas do not rely on the
    well-formedness assumption: *)

Lemma le_refl : forall n : nat, le n n.

Proof fun n P H _ => H.

Lemma le_trans : forall n1 n2 n3 : nat, le n1 n2 -> le n2 n3 -> le n1 n3.

Proof fun n1 n2 n3 H1 H2 P Hn1 HS => H2 P (H1 P Hn1 HS) HS.

Lemma le_S : forall n m : nat, le n m -> le n (S m).

Proof fun n m H P Hn HS => HS m (H P Hn HS).

(** The successor of a natural number cannot be less than or equal
    to zero: *)

Lemma le_Sn_O : forall n : nat, le (S n) O -> bot.

Proof
  fun n H =>
  H (fun k => k Prop bot (fun _ => top)) top_intro (fun _ _ => top_intro).

(** Inversion lemma for (le n m): *)

Lemma le_inv :
 forall n m : nat,
 le n m -> or (eq nat n m) (ex nat (fun k => and (le n k) (eq nat m (S k)))).

Proof.
intros n m H; apply H; clear H m.
apply or_inl; apply eq_refl.
intros m H; apply H; clear H; intro H.
apply or_inr; apply ex_intro with m; apply and_intro.
apply H; apply le_refl. apply H; apply eq_refl.
apply H; clear H; intros k H; apply H; clear H; intros H1 H2.
apply or_inr; apply ex_intro with (S k); apply and_intro.
apply le_S; assumption. apply H2; apply eq_refl.
Qed.

Lemma le_n_Sm :
 forall n : nat,
 wf_nat n ->
 forall m : nat, wf_nat m -> le n (S m) -> or (le n m) (eq nat n (S m)).

Proof.
intros n Hn m Hm H.
apply (le_inv n (S m) H); clear H; intro H.
apply or_inr; assumption.
apply H; clear H; intros k H.
apply H; clear H; intros H1 H2.
generalize (le_trans _ _ _ Hn H1).
intro Hk; change (wf_nat k) in Hk.
apply (eq_sym _ _ _ (eq_S_S m Hm k Hk H2)).
apply or_inl; assumption.
Qed.

(** ** Strict ordering **)

Definition lt (n m : nat) : Prop := le (S n) m.

Lemma lt_n_Sn : forall n : nat, lt n (S n).

Proof fun n => le_refl (S n).

Lemma lt_S : forall n m : nat, lt n m -> lt n (S m).

Proof fun n m => le_S (S n) m.

Lemma lt_n_O : forall n : nat, lt n O -> bot.

Proof le_Sn_O.

Lemma lt_n_Sm :
 forall n : nat,
 wf_nat n ->
 forall m : nat, wf_nat m -> lt n (S m) -> or (lt n m) (eq nat n m).

Proof.
intros n Hn m Hm H.
apply (le_n_Sm (S n) (wf_nat_S n Hn) m Hm H); clear H; intro H.
apply or_inl; assumption. apply or_inr; apply eq_S_S; assumption.
Qed.
