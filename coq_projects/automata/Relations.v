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
(*                              Nov 25th 1994                               *)
(*                                                                          *)
(****************************************************************************)
(*                               Relations.v                                *)
(****************************************************************************)
(*              Formal Language Theory                                      *)
(*                                                                          *)
(*              Judicael Courant - Jean-Christophe Filliatre                *)
(*                                                                          *)
(*              Developped in V5.8  June-July 1993                          *)
(*              Ported     to V5.10 October 1994                            *)
(****************************************************************************)
 
(*Resultats sur les relations sur un Set,*)
(*copie de THEORIES/RELATIONS/Relations.v*)
(*ou l'on a remplace Type par Set et ou l'on definit le predicat Rstar_inv *)


Section Relations.

(* Properties of a binary relation R on type A *)

  Variable A : Set.  
  Variable R : A -> A -> Prop.  

(* Definition of the reflexive-transitive closure R* of R *)
(* Smallest reflexive P containing R o P *)

Definition Rstar (x y : A) :=
  forall P : A -> A -> Prop,
  (forall u : A, P u u) ->
  (forall u v w : A, R u v -> P v w -> P u w) -> P x y.  

Theorem Rstar_reflexive : forall x : A, Rstar x x.
 Proof
   fun (x : A) (P : A -> A -> Prop) (h1 : forall u : A, P u u)
     (h2 : forall u v w : A, R u v -> P v w -> P u w) => 
   h1 x.  

  
Theorem Rstar_R : forall x y z : A, R x y -> Rstar y z -> Rstar x z.
 Proof
   fun (x y z : A) (t1 : R x y) (t2 : Rstar y z) (P : A -> A -> Prop)
     (h1 : forall u : A, P u u)
     (h2 : forall u v w : A, R u v -> P v w -> P u w) =>
   h2 x y z t1 (t2 P h1 h2).  

(* We conclude with transitivity of Rstar : *)

Theorem Rstar_transitive :
 forall x y z : A, Rstar x y -> Rstar y z -> Rstar x z.
 Proof
   fun (x y z : A) (h : Rstar x y) =>
   h (fun u v : A => Rstar v z -> Rstar u z)
     (fun (u : A) (t : Rstar u z) => t)
     (fun (u v w : A) (t1 : R u v) (t2 : Rstar w z -> Rstar v z)
        (t3 : Rstar w z) => Rstar_R u v z t1 (t2 t3)).  

(* Another characterization of R* *)
(* Smallest reflexive P containing R o R* *)

Definition Rstar' (x y : A) :=
  forall P : A -> A -> Prop,
  P x x -> (forall u : A, R x u -> Rstar u y -> P x y) -> P x y.  

Theorem Rstar'_reflexive : forall x : A, Rstar' x x.
 Proof
   fun (x : A) (P : A -> A -> Prop) (h : P x x)
     (h' : forall u : A, R x u -> Rstar u x -> P x x) => h.
  
Theorem Rstar'_R : forall x y z : A, R x z -> Rstar z y -> Rstar' x y.
 Proof
   fun (x y z : A) (t1 : R x z) (t2 : Rstar z y) (P : A -> A -> Prop)
     (h1 : P x x) (h2 : forall u : A, R x u -> Rstar u y -> P x y) =>
   h2 z t1 t2.  

(* Equivalence of the two definitions: *)

Theorem Rstar'_Rstar : forall x y : A, Rstar' x y -> Rstar x y.
 Proof
   fun (x y : A) (h : Rstar' x y) =>
   h Rstar (Rstar_reflexive x) (fun u : A => Rstar_R x u y).  
  
Theorem Rstar_Rstar' : forall x y : A, Rstar x y -> Rstar' x y.
 Proof
   fun (x y : A) (h : Rstar x y) =>
   h Rstar' (fun u : A => Rstar'_reflexive u)
     (fun (u v w : A) (h1 : R u v) (h2 : Rstar' v w) =>
      Rstar'_R u w v h1 (Rstar'_Rstar v w h2)).  


(* inversion de Rstar*)

Lemma Rstar_inv :
 forall x y : A,
 Rstar x y -> x = y \/ ex2 (fun z : A => R x z) (fun z : A => Rstar z y).
intros x y Rstar_x_y.
pattern x, y in |- *.
apply Rstar_x_y.
	auto.

	intros u v w R_u_v Hyp.
	apply or_intror.
	exists v.
		assumption.
		elim Hyp.
			intro Rew.
			rewrite Rew.
			apply Rstar_reflexive.

			intro temp; elim temp; clear temp.
			intros z R_v_z Rstar_z_w.
			apply Rstar_R with z; assumption.
Qed.

End Relations.

Hint Resolve Rstar_reflexive.