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


(* definit un tableau a deux dimensions *)

Require Export table.

Unset Standard Proposition Elimination Names.

Section TABLE2.

Variable E F G : Set.
Hypothesis eq_E_dec : eq_dec E.
Hypothesis eq_F_dec : eq_dec F.
Variable t : E -> F -> G.
Variable x0 : E.
Variable y0 : F.
Variable z0 : G.

Definition change_x0y0 :=
  change_x0 E (F -> G) eq_E_dec t x0 (change_x0 F G eq_F_dec (t x0) y0 z0).
                     
Lemma elsewhere2_x : forall x : E, x <> x0 -> change_x0y0 x = t x.
Proof.
 intros; unfold change_x0y0 in |- *; simpl in |- *.
 rewrite elsewhere; auto.
Qed.

Lemma elsewhere2_y :
 forall y : F,
 y <> y0 -> (fun x : E => change_x0y0 x y) = (fun x : E => t x y).
Proof.
 intros; apply funct_eq.
 intros; unfold change_x0y0 in |- *.
 case (eq_E_dec e x0); intros.
 rewrite e0. rewrite
  (here E (F -> G) eq_E_dec t x0 (change_x0 F G eq_F_dec (t x0) y0 z0))
  .
 rewrite elsewhere; auto.
	
 rewrite
  (elsewhere E (F -> G) eq_E_dec t x0 (change_x0 F G eq_F_dec (t x0) y0 z0) e)
  ; auto.
Qed.

Lemma elsewhere2 :
 forall (x : E) (y : F), x <> x0 \/ y <> y0 -> change_x0y0 x y = t x y. 
Proof.
 intros; elim H; intros.
 rewrite (elsewhere2_x x); auto.

 apply
  f_equal
   with
     (f := fun g : E -> G => g x)
     (x := fun x' : E => change_x0y0 x' y)
     (y := fun x' : E => t x' y). 
 apply elsewhere2_y; auto.
Qed.

Lemma here2 : change_x0y0 x0 y0 = z0.
Proof.
 intros; unfold change_x0y0 in |- *; simpl in |- *.
 rewrite
  (here E (F -> G) eq_E_dec t x0 (change_x0 F G eq_F_dec (t x0) y0 z0))
  .
 rewrite here; auto.
Qed.
	
End TABLE2.
