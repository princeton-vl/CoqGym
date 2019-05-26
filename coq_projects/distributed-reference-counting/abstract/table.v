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


(* definit une table a une ou deux dimensions puis la sommation sur la
table *)

Require Import List.
Require Export finite.

Unset Standard Proposition Elimination Names.

Section TABLE1.

(* une table a lements dans F indexee par E est une fonction de E dans
F dans laquelle on ne modifie qu'un terme a la fois *)

Variable E F : Set.
Hypothesis eq_E_dec : eq_dec E.
Variable t : E -> F.
Variable x0 : E.
Variable y0 : F.

Definition change_x0 (x : E) :=
  if eq_E_dec x0 x then y0 else t x.

Lemma here : change_x0 x0 = y0.
Proof.
 unfold change_x0 in |- *; rewrite case_eq; trivial.
Qed.
	
Lemma elsewhere : forall x : E, x0 <> x -> change_x0 x = t x.
Proof.
 intros; unfold change_x0 in |- *.
 rewrite case_ineq; trivial.
Qed.

End TABLE1.

Section TABLE2.

(* une table a deux dimensions est indexee par deux ensembles *)

Variable E F G : Set.
Hypothesis eq_E_dec : eq_dec E.
Hypothesis eq_F_dec : eq_dec F.
Variable t : E -> F -> G.
Variable x0 : E.
Variable y0 : F.
Variable z0 : G.

Definition change_x0y0 :=
  change_x0 E (F -> G) eq_E_dec t x0 (change_x0 F G eq_F_dec (t x0) y0 z0).

Lemma here2 : change_x0y0 x0 y0 = z0.
Proof.
 intros; unfold change_x0y0 in |- *; simpl in |- *.
 do 2 rewrite here; auto.
Qed.
                     
Remark elsewhere2_x : forall x : E, x <> x0 -> change_x0y0 x = t x.
Proof.
 intros; unfold change_x0y0 in |- *; simpl in |- *.
 rewrite elsewhere; auto.
Qed.

Remark elsewhere2_y :
 forall y : F,
 y <> y0 -> (fun x : E => change_x0y0 x y) = (fun x : E => t x y).
Proof.
 intros; apply funct_eq.
 intros; unfold change_x0y0 in |- *.
 case (eq_E_dec e x0); intros.
 rewrite e0; rewrite here.
 rewrite elsewhere; auto.
	
 rewrite elsewhere; auto.
Qed.

Lemma elsewhere2 :
 forall (x : E) (y : F), x <> x0 \/ y <> y0 -> change_x0y0 x y = t x y. 
Proof.
 intros; elim H; intros.
 rewrite elsewhere2_x; auto.

 apply
  f_equal
   with
     (f := fun g : E -> G => g x)
     (x := fun x' : E => change_x0y0 x' y)
     (y := fun x' : E => t x' y). 
 apply elsewhere2_y; auto.
Qed.
	
End TABLE2.
 
Section CHANGE_SUM1.

(* la table est a elements dans Z, il est alors possible de sommer sur
une liste d'index *)

Variable E : Set.
Hypothesis eq_E_dec : eq_dec E.
Variable f : E -> Z.
Variable x0 : E.
Variable y0 : Z.

Lemma sigma_nowhere :
 forall l : list E,
 ~ In x0 l -> sigma E l (change_x0 E Z eq_E_dec f x0 y0) = sigma E l f. 
Proof.
 intros; apply sigma_simpl.
 intros; apply elsewhere.
 apply sym_not_eq; apply in_not_in with (l := l); auto.
Qed.

Lemma sigma_change :
 forall l : list E,
 only_once E eq_E_dec x0 l ->
 sigma E l (change_x0 E Z eq_E_dec f x0 y0) = (sigma E l f - f x0 + y0)%Z.
Proof.
 simple induction l; simpl in |- *.
 contradiction.

 intros a l0 hrec; case (eq_E_dec x0 a); intros.
 rewrite <- e; rewrite here.
 rewrite sigma_nowhere.
 omega.
	
 trivial.
	
 rewrite elsewhere.
 rewrite hrec.
 omega.
	
 trivial.

 trivial.
Qed.
 	
End CHANGE_SUM1.

Section SUM1_S.

(* l'ensemble d'index etant un ensemble fini, il est possible de
sommer sur cet ensemble, donc d'apres la definition choisie d'ensemble
fini, sur la liste de tout ses elements. On ne s'interesse qu'aux
incrementation ou decrementation d'un element de la table *)

Variable E : Set.
Hypothesis eq_E_dec : eq_dec E.
Variable L : list E.
Hypothesis finite_E : list_of_elements E eq_E_dec L.
Variable f : E -> Z.
Variable x0 : E.

Remark sigma_change_S :
 sigma E L (change_x0 E Z eq_E_dec f x0 (f x0 + 1)%Z) = (sigma E L f + 1)%Z.    
Proof.
 rewrite sigma_change.
 omega. 
	
 auto.
Qed.

Lemma sigma__S :
 forall g : E -> Z,
 g x0 = (f x0 + 1)%Z ->
 (forall x : E, x <> x0 -> g x = f x) -> sigma E L g = (sigma E L f + 1)%Z.    
Proof.
 intros; rewrite <- sigma_change_S.
 apply sigma_simpl.
 intros; unfold change_x0 in |- *.
 case (eq_E_dec x0 x); simpl in |- *; intro.
 rewrite <- e; auto.

 auto.
Qed.
   
Remark sigma_change_pred :
 sigma E L (change_x0 E Z eq_E_dec f x0 (f x0 - 1)%Z) = (sigma E L f - 1)%Z.    
Proof.
 rewrite sigma_change.
 omega.
		
 auto.
Qed.
   
Lemma sigma__pred :
 forall g : E -> Z,
 g x0 = (f x0 - 1)%Z ->
 (forall x : E, x <> x0 -> g x = f x) -> sigma E L g = (sigma E L f - 1)%Z.    
Proof.
 intros; rewrite <- sigma_change_pred.
 apply sigma_simpl.
 intros; unfold change_x0 in |- *.
 case (eq_E_dec x0 x); simpl in |- *; intro.
 rewrite <- e; auto.

 auto.
Qed.
 
End SUM1_S.
