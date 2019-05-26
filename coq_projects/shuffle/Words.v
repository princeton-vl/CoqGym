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


(* Contribution to the Coq Library   V6.3 (July 1999)                    *)

(****************************************************************************)
(*                 The Calculus of Inductive Constructions                  *)
(*                                                                          *)
(*                                Projet Coq                                *)
(*                                                                          *)
(*                     INRIA                        ENS-CNRS                *)
(*              Rocquencourt                        Lyon                    *)
(*                                                                          *)
(*                                Coq V5.10                                 *)
(*                                                                          *)
(****************************************************************************)
(*                                 Words.v                                  *)
(****************************************************************************)
(* G. Huet - V5.8  Nov. 1994 *)
(*    ported V5.10 June 1995 *)

Require Import Bool.

(*****************)
(* Boolean words *)
(*****************)

Inductive word : Set :=
  | empty : word
  | bit : bool -> word -> word.

(* Remark : word ~ bool list *)

(* word concatenation : logical definition *)
Inductive conc : word -> word -> word -> Prop :=
  | conc_empty : forall v : word, conc empty v v
  | conc_bit :
      forall (u v w : word) (b : bool),
      conc u v w -> conc (bit b u) v (bit b w).

(* word concatenation : functional definition *)

Fixpoint append (u : word) : word -> word :=
  fun v : word =>
  match u with
  | empty => v
  | bit b w => bit b (append w v)
  end. 


(* Relating the two definitions; unused below *)
Lemma conc_append : forall u v w : word, conc u v w -> w = append u v.
Proof.
simple induction 1; simpl in |- *; trivial.
simple induction 2; trivial.
Qed.

(* Associativity of append; unused below *)
Lemma assoc_append :
 forall u v w : word, append u (append v w) = append (append u v) w.
Proof.
simple induction u; simpl in |- *; intros; auto.
rewrite H; trivial.
Qed.


(**************)
(* Singletons *)
(**************)

Definition single (b : bool) := bit b empty.


(*********************)
(* Parities of words *)
(*********************)

Inductive odd : word -> Prop :=
    even_odd : forall w : word, even w -> forall b : bool, odd (bit b w)
with even : word -> Prop :=
  | even_empty : even empty
  | odd_even : forall w : word, odd w -> forall b : bool, even (bit b w).

Hint Resolve odd_even even_empty even_odd.

Lemma not_odd_empty : ~ odd empty.
Proof.
unfold not in |- *; intro od.
inversion od.
Qed.

Hint Resolve not_odd_empty.

Lemma inv_odd : forall (w : word) (b : bool), odd (bit b w) -> even w.
Proof.
intros w b od.
inversion od; trivial.
Qed.

Lemma inv_even : forall (w : word) (b : bool), even (bit b w) -> odd w.
Proof.
intros w b ev.
inversion ev; trivial.
Qed.

(**********************)
(* (odd w) + (even w) *)
(**********************)

Lemma odd_or_even : forall w : word, odd w \/ even w.
Proof.
simple induction w; auto.
simple induction 1; intros.
right; auto.
left; auto.
Qed.

Lemma not_odd_and_even : forall w : word, odd w -> even w -> False.
Proof.
simple induction w; intros.
elim not_odd_empty; trivial.
apply H.
apply inv_even with b; trivial.
apply inv_odd with b; trivial.
Qed.

(************************)
(* Parities of subwords *)
(************************)

Lemma odd_even_conc :
 forall u v w : word,
 conc u v w ->
 odd w /\ (odd u /\ even v \/ even u /\ odd v) \/
 even w /\ (odd u /\ odd v \/ even u /\ even v).
Proof.
simple induction 1; intros.
elim (odd_or_even v0); auto.
elim H1; [ right | left ]; intuition.
Qed.

Lemma even_conc :
 forall u v w : word,
 conc u v w -> even w -> odd u /\ odd v \/ even u /\ even v.
Proof.
intros u v w c e; elim odd_even_conc with u v w; intros.
elim H; intro o; elim not_odd_and_even with w; auto.
elim H; intros; trivial.
trivial.
Qed.
