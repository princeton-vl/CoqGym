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

(* Just for fun : a proof that there is no set of all sets, using       *)
(* Russell's paradox construction                                       *)
(* There, of course, are other proofs (foundation, etc)                 *)

Require Import Sets.
Require Import Axioms.


Theorem Russell : forall E : Ens, (forall E' : Ens, IN E' E) -> False.
intros U HU.
cut
 ((fun x : Ens => IN x x -> False) (Comp U (fun x : Ens => IN x x -> False))).
intros HR.
apply HR.
apply IN_P_Comp; auto with zfc.
intros w1 w2 HF e i; apply HF; apply IN_sound_left with w2; auto with zfc;
 apply IN_sound_right with w2; auto with zfc.
intros H.
cut
 (IN (Comp U (fun x : Ens => IN x x -> False))
    (Comp U (fun x : Ens => IN x x -> False))).
change
  ((fun x : Ens => IN x x -> False) (Comp U (fun x : Ens => IN x x -> False)))
 in |- *.
cut
 (forall w1 w2 : Ens, (IN w1 w1 -> False) -> EQ w1 w2 -> IN w2 w2 -> False).
intros ww.
exact
 (IN_Comp_P U (Comp U (fun x : Ens => IN x x -> False))
    (fun x : Ens => IN x x -> False) ww H).
intros w1 w2 HF e i; apply HF; apply IN_sound_left with w2; auto with zfc;
 apply IN_sound_right with w2; auto with zfc.
assumption.

Qed.
