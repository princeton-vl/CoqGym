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

(*-- Tactics Tauto & Intuition --*)

(*-- Tauto: Tactic for automating proof in Intuionnistic Propositional 
            Caulculus, based on the contraction-free LJT of Dickhoff 
     Ref:   Roy Dyckhoff, The Journal of Symbolic Logic Volume 57,
            Number 3, Sept. 1992                                      --*) 

Parameter A B C : Prop.
Parameter even : nat -> Prop.
Parameter P : nat -> Prop.

(*-- Examples of intuitionistics tautologies 
     Ref: Lincoln Wallen, Automated Deduction in Nonclassical Logics, 1990 
          Sthephen Klenne, Introduction to Metamathematics,1952. --*)

Theorem Ex_Wallen : (A -> B /\ C) -> (A -> B) \/ (A -> C).
tauto.
Qed.

Theorem Ex_Klenne : ~ ~ (A \/ ~ A).
tauto.
Qed.

(*-- Example with a first ordre formula --*)  
Theorem Ex_Klenne' : forall n : nat, ~ ~ (even n \/ ~ even n).
intro.
tauto.
Qed.

(*-- Example with a first ordre tautologic formula --*)
Theorem Ex_Klenne'' :
 ~ ~ ((forall n : nat, even n) \/ ~ (forall m : nat, even m)).
tauto.
Qed.

(*-- Intuition: Tactics for simplifications of buts, based on LJT calcul.
     Ref      : Cesar Munoz, Rapport de stage de DEA 1993. --*)

Theorem Intu :
 (forall x : nat, P x) /\ B -> (forall y : nat, P y) /\ P 0 \/ B /\ P 0.
intuition.
Qed.

(*  A private club has the following rules :
 *
 *  . rule 1 : Every non-scottish member wears red socks
 *  . rule 2 : Every member wears a kilt or doesn't wear red socks
 *  . rule 3 : The married members don't go out on sunday
 *  . rule 4 : A member goes out on sunday if and only if he is scottish
 *  . rule 5 : Every member who wears a kilt is scottish and married
 *  . rule 6 : Every scottish member wears a kilt
 *
 *  Actually, no one can be accepted !
 *)

Section club.

Variable Scottish RedSocks WearKilt Married GoOutSunday : Prop.

Hypothesis rule1 : ~ Scottish -> RedSocks.
Hypothesis rule2 : WearKilt \/ ~ RedSocks.
Hypothesis rule3 : Married -> ~ GoOutSunday.
Hypothesis rule4 : GoOutSunday <-> Scottish.
Hypothesis rule5 : WearKilt -> Scottish /\ Married.
Hypothesis rule6 : Scottish -> WearKilt.

Lemma NoMember : False.
tauto.
Qed.

End club.

Theorem tauto : (forall x : nat, P x) -> forall y : nat, P y.
tauto.
Qed.

Theorem tauto1 : A -> A.
tauto.
Qed.

Theorem tauto2 : (A -> B -> C) -> (A -> B) -> A -> C.
tauto.
Qed.

Theorem a : forall (x0 : A \/ B) (x1 : B /\ C), A -> B.
tauto.
Qed.

Theorem a2 : (A -> B /\ C) -> (A -> B) \/ (A -> C).
tauto.
Qed.

Theorem a4 : ~ A -> ~ A.
tauto.
Qed.

Theorem e2 : ~ ~ (A \/ ~ A).
tauto.
Qed.

Theorem e4 : ~ ~ (A \/ B -> A \/ B).
tauto.
Qed.

Theorem y0 :
 forall (x0 : A) (x1 : ~ A) (x2 : A -> B) (x3 : A \/ B) (x4 : A /\ B),
 A -> False.
tauto.
Qed.

Theorem y1 : forall x0 : (A /\ B) /\ C, B.
tauto.
Qed.

Theorem y2 : forall (x0 : A) (x1 : B), C \/ B.
tauto.
Qed.

Theorem y3 : forall x0 : A /\ B, B /\ A.
tauto.
Qed.

Theorem y5 : forall x0 : A \/ B, B \/ A.
tauto.
Qed.

Theorem y6 : forall (x0 : A -> B) (x1 : A), B.
tauto.
Qed.

Theorem y7 : forall (x0 : A /\ B -> C) (x1 : B) (x2 : A), C.
tauto.
Qed.

Theorem y8 : forall (x0 : A \/ B -> C) (x1 : A), C.
tauto.
Qed.

Theorem y9 : forall (x0 : A \/ B -> C) (x1 : B), C.
tauto.
Qed.

Theorem y10 : forall (x0 : (A -> B) -> C) (x1 : B), C.
tauto.
Qed.
