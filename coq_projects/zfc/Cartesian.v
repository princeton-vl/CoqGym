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

(* The cartesian product and its properties *)

Require Import Sets.
Require Import Axioms.


(* This definition of the ordered pair is slightly different from *)
(* the usual one, since we want it to work in an intuisionistic   *)
(* setting. Works the same, neitherless. The soundness proofs are *)
(* unpleasant.                                                    *)


Definition Couple (E E' : Ens) := Paire (Sing E) (Paire Vide (Sing E')).

Theorem Couple_inj_left :
 forall A A' B B' : Ens, EQ (Couple A A') (Couple B B') -> EQ A B.
unfold Couple in |- *; simpl in |- *.
simple induction 1.
intros HA HB; elim (HA true).
intros x; elim x; simpl in |- *; simple induction 1; intros H3 H4;
 elim (H3 true); simpl in |- *; intros xx; elim xx; 
 simpl in |- *; auto with zfc.
elim (H4 false); simpl in |- *.
simple induction x0; simpl in |- *.
intros.
cut (EQ (Sing B') Vide).
simpl in |- *.
simple induction 1.
intros yy; elim (yy true).
simple induction x1.

apply EQ_tran with A; auto with zfc.

intros; cut (EQ (Sing B') Vide).
simpl in |- *.
simple induction 1.
intros yy; elim (yy true).
simple induction x1.

apply EQ_tran with A; auto with zfc.

intros yy.
elim (HB true); simpl in |- *.
simple induction x0.
change (EQ (Sing A) (Sing B) -> EQ A B) in |- *; intros EE.
apply IN_Sing_EQ.
apply IN_sound_right with (Sing A); auto with zfc.
change (EQ (Paire Vide (Sing A')) (Sing B) -> EQ A B) in |- *.
intros zz.
elimtype F.
apply (not_EQ_Sing_Vide A').
apply EQ_tran with B.
apply IN_Sing_EQ.
apply IN_sound_right with (Paire Vide (Sing A')); auto with zfc.
apply EQ_sym; apply IN_Sing_EQ;
 apply IN_sound_right with (Paire Vide (Sing A')); 
 auto with zfc.

Qed.



Theorem Couple_inj_right :
 forall A A' B B' : Ens, EQ (Couple A A') (Couple B B') -> EQ A' B'.
unfold Couple in |- *; simpl in |- *.
simple induction 1; intros H1 H2.
elim (H1 false).
intros bb1; elim bb1.
intros HF.
change (EQ (Paire Vide (Sing A')) (Sing B)) in HF.
cut F.
simple induction 1.
apply (not_EQ_Vide_Sing A').
apply EQ_tran with B.
apply IN_Sing_EQ; apply IN_sound_right with (Paire Vide (Sing A'));
 auto with zfc.
apply EQ_sym; apply IN_Sing_EQ;
 apply IN_sound_right with (Paire Vide (Sing A')); 
 auto with zfc.
change (EQ (Paire Vide (Sing A')) (Paire Vide (Sing B')) -> EQ A' B') in |- *.
intros HP; cut (EQ (Sing A') (Sing B')).
intros; auto with zfc.
cut (IN (Sing A') (Paire Vide (Sing B'))).
intros HI; elim (Paire_IN Vide (Sing B') (Sing A') HI).
intros; cut F.
simple induction 1.
apply not_EQ_Sing_Vide with A'; assumption.
trivial with zfc.
apply IN_sound_right with (Paire Vide (Sing A')); auto with zfc.

Qed.






(* Here we cheat. It is easier to define the cartesian product using    *)
(* the type theoretical product, i.e. we here use non set-theoretical   *)
(* constructions. We could however use the usual definitions.           *)


Definition Prod (E E' : Ens) : Ens :=
  match E, E' with
  | sup A f, sup A' f' =>
      sup _
        (fun c : prod_t A A' =>
         match c with
         | pair_t a a' => Couple (f a) (f' a')
         end)
  end.


Hint Resolve Paire_sound_left Paire_sound_right: zfc.


Theorem Couple_sound_left :
 forall A A' B : Ens, EQ A A' -> EQ (Couple A B) (Couple A' B).
 unfold Couple in |- *; intros; auto with zfc.
Qed.

Theorem Couple_sound_right :
 forall A B B' : Ens, EQ B B' -> EQ (Couple A B) (Couple A B').
 unfold Couple in |- *; intros; auto with zfc.
Qed.


Theorem Couple_IN_Prod :
 forall E1 E2 E1' E2' : Ens,
 IN E1' E1 -> IN E2' E2 -> IN (Couple E1' E2') (Prod E1 E2).
simple induction E1; intros A1 f1 r1; simple induction E2; intros A2 f2 r2.
intros E1' E2' i1 i2.
elim (IN_EXType (sup A1 f1) E1').
intros x e1; simpl in x.
elim (IN_EXType (sup A2 f2) E2').
intros x0 e2; simpl in x.
apply IN_sound_left with (Couple (pi2 (sup A1 f1) x) (pi2 (sup A2 f2) x0));
 auto with zfc.
apply EQ_tran with (Couple (pi2 (sup A1 f1) x) E2'); auto with zfc.
apply Couple_sound_right.
auto with zfc.

apply Couple_sound_left; auto with zfc.

simpl in |- *.
simpl in |- *.
exists (pair_t _ _ x x0).
simpl in |- *.
split.
simple induction x1; simpl in |- *.
exists true; simpl in |- *.
split.
simple induction x2; simpl in |- *.
exists true; auto with zfc.

exists true; auto with zfc.

simple induction y; exists true; auto with zfc.

exists false; simpl in |- *.
split.
simple induction x2.
exists true; simpl in |- *; auto with zfc.
split.
simple induction x3.

simple induction y.

exists false; auto with zfc.

simple induction y; simpl in |- *.
exists true; auto with zfc.

exists false; auto with zfc.

simple induction y; simpl in |- *.
exists true; auto with zfc.

exists false; auto with zfc.

auto with zfc.

auto with zfc.
Qed.


Theorem Couple_Prod_IN :
 forall E1 E2 E1' E2' : Ens,
 IN (Couple E1' E2') (Prod E1 E2) -> IN E1' E1 /\ IN E2' E2.
simple induction E1; intros A1 f1 r1; simple induction E2; intros A2 f2 r2.
intros E1' E2' i.
elim (IN_EXType (Prod (sup A1 f1) (sup A2 f2)) (Couple E1' E2') i).
intros xx; elim xx; intros a1 a2 e.
change (EQ (Couple E1' E2') (Couple (f1 a1) (f2 a2))) in e.
cut (EQ E1' (f1 a1)).
cut (EQ E2' (f2 a2)).
intros e1 e2.
split.
apply IN_sound_left with (f1 a1); auto with zfc; simpl in |- *; exists a1;
 auto with zfc.
apply IN_sound_left with (f2 a2); auto with zfc; simpl in |- *; exists a2;
 auto with zfc.
apply Couple_inj_right with (A := E1') (B := f1 a1); auto with zfc.
apply Couple_inj_left with E2' (f2 a2); auto with zfc.
Qed.



Theorem IN_Prod_EXType :
 forall E E' E'' : Ens,
 IN E'' (Prod E E') ->
 EXType _ (fun A : Ens => EXType _ (fun B : Ens => EQ (Couple A B) E'')).
simple induction E; intros A f r; simple induction E'; intros A' f' r'.
intros; elim (IN_EXType (Prod (sup A f) (sup A' f')) E'').
simple induction x.
intros; exists (f a); exists (f' b); auto with zfc.
auto with zfc.
Qed.
