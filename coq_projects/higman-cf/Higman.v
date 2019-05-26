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


Require Import List.
Require Extraction.

Inductive letter : Set :=
  | A : letter
  | B : letter.

Definition word := list letter.

Inductive emb : word -> word -> Prop :=
  | emb0 : forall ys : word, emb nil ys
  | emb1 :
      forall (xs ys : list letter) (y : letter),
      emb xs ys -> emb xs (y :: ys)
  | emb2 :
      forall (xs ys : list letter) (x : letter),
      emb xs ys -> emb (x :: xs) (x :: ys).

Inductive L (v : word) : list word -> Prop :=
  | L0 : forall (w : word) (ws : list word), emb w v -> L v (w :: ws)
  | L1 : forall (w : word) (ws : list word), L v ws -> L v (w :: ws).

Inductive good : list word -> Prop :=
  | good0 : forall (ws : list word) (w : word), L w ws -> good (w :: ws)
  | good1 : forall (ws : list word) (w : word), good ws -> good (w :: ws).

Inductive R (a : letter) : list word -> list word -> Prop :=
  | R0 : R a nil nil
  | R1 :
      forall (vs ws : list word) (w : word),
      R a vs ws -> R a (w :: vs) ((a :: w) :: ws).

Inductive T (a : letter) : list word -> list word -> Prop :=
  | T0 :
      forall (b : letter) (w : word) (ws zs : list word),
      a <> b -> R b ws zs -> T a (w :: zs) ((a :: w) :: zs)
  | T1 :
      forall (w : word) (ws zs : list word),
      T a ws zs -> T a (w :: ws) ((a :: w) :: zs)
  | T2 :
      forall (b : letter) (w : word) (ws zs : list word),
      a <> b -> T a ws zs -> T a ws ((b :: w) :: zs).

Inductive bar : list word -> Set :=
  | bar1 : forall ws : list word, good ws -> bar ws
  | bar2 : forall ws : list word, (forall w : word, bar (w :: ws)) -> bar ws.

Hint Constructors emb.
Hint Constructors L.
Hint Constructors good.
Hint Constructors R.
Hint Constructors T. 
Hint Constructors bar.
Hint Extern 5 (?X1 <> ?X2) => intro; discriminate.

Theorem prop1 : forall ws : list word, bar (nil :: ws).
auto.
Defined.
Hint Resolve prop1.

Theorem lemma1 :
 forall (ws : list word) (xs : word) (x : letter), L xs ws -> L (x :: xs) ws.
simple induction 1; auto.
Defined.
Hint Resolve lemma1.

Theorem lemma2' :
 forall (vs ws : list word) (x : letter) (xs : word),
 R x vs ws -> L xs vs -> L (x :: xs) ws.
simple induction 1.
inversion 1.
inversion 3; auto.
Defined.
Hint Resolve lemma2'.

Theorem lemma2 :
 forall (vs ws : list word) (a : letter), R a vs ws -> good vs -> good ws.
simple induction 1; auto.
inversion 3; eauto.
Defined.
Hint Resolve lemma2.

Theorem lemma3' :
 forall (vs ws : list word) (x : letter) (xs : word),
 T x vs ws -> L xs vs -> L (x :: xs) ws.
simple induction 1; auto; inversion 3; auto.
Qed.
Hint Resolve lemma3'.

Theorem lemma3 :
 forall (ws zs : list word) (a : letter), T a ws zs -> good ws -> good zs.
simple induction 1; auto; inversion 3; eauto.
Defined.
Hint Resolve lemma3.

Theorem lemma4 :
 forall (ws zs : list word) (a : letter), R a ws zs -> ws <> nil -> T a ws zs.
simple induction 1.
tauto.
intro.
case vs.
inversion 1.
intros.
case a.
apply (T0 A B w nil); auto.
apply (T0 B A w nil); auto.
auto.
Defined.
Hint Resolve lemma4.

Theorem letter_neq : forall a b c : letter, a <> b -> c <> a -> c = b.
intros a b c; case a; case b; case c; tauto.
Qed.

Theorem letter_eq_dec : forall a b : letter, {a = b} + {a <> b}.
intros.
decide equality.
Defined.

Theorem prop2 :
 forall (a b : letter) (xs : list word),
 a <> b ->
 bar xs ->
 forall ys : list word,
 bar ys -> forall zs : list word, T a xs zs -> T b ys zs -> bar zs.
intros a b xs neq.
simple induction 1.
eauto.
simple induction 3.
eauto.
intros.
apply bar2.
intro.
case w.
apply prop1.
intros.
elim (letter_eq_dec l a).
intro; rewrite a0; eauto.
intro; rewrite (letter_neq a b l neq b2); eauto.
Defined.
Hint Resolve prop2.

Theorem prop3 :
 forall (a : letter) (xs : list word),
 bar xs -> forall zs : list word, xs <> nil -> R a xs zs -> bar zs.
simple induction 1.
eauto.
intros.
apply bar2.
simple induction w.
auto.
intros.
elim (letter_eq_dec a0 a).
intro. 
rewrite a1; eauto.
intro.
apply (prop2 a0 a (l :: zs) b0 H3 ws); eauto.
Defined.
Hint Resolve prop3.

Theorem higman : bar nil.
apply bar2.
simple induction w; eauto.
Defined.
Hint Resolve higman.

Inductive is_prefix (A : Set) : list A -> (nat -> A) -> Prop :=
  | is_prefix_nil : forall f : nat -> A, is_prefix A nil f
  | is_prefix_cons :
      forall (f : nat -> A) (x : A) (xs : list A),
      x = f (length xs) -> is_prefix A xs f -> is_prefix A (x :: xs) f.
Hint Constructors is_prefix.

Theorem good_prefix_lemma :
 forall (ws : list word) (f : nat -> word),
 bar ws ->
 is_prefix word ws f -> {vs : list word | is_prefix word vs f /\ good vs}.
simple induction 1.
intros.
exists ws0; auto.
eauto.
Defined.
Hint Resolve good_prefix_lemma.

Theorem good_prefix :
 forall f : nat -> word, {vs : list word | is_prefix word vs f /\ good vs}.
eauto.
Defined.

Extraction "higman.ml" good_prefix.
