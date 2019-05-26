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
(*     A development written by Pierre Castéran for Coq V6.1
     
Coq : A product of inria : "http://pauillac.inria.fr/coq/coq-eng.html"

Pierre Castéran : A product of LaBRI : 


LaBRI, Universite Bordeaux-I      |    12 place Puy Paulin
351 Cours de la Liberation        |    33000 Bordeaux
F-33405 TALENCE Cedex             |    France
France                            |    (+ 33) 5 56 81 15 80
tel : (+ 33) 5 56 84 69 31
fax : (+ 33) 5 56 84 66 69
email: casteran@labri.u-bordeaux.fr       
www: http://dept-info.labri.u-bordeaux.fr/~casteran

"Les rêves sont aussi beaux que la réalité, mais ils ne sont pas mieux".
( J.L.Borges )



*)

Require Export nat_trees.
Require Import Lt.

(* Definitions 
**************)

(* p is less than every member of t *)

Inductive min (p : nat) (t : nat_tree) : Prop :=
    min_intro : (forall q : nat, occ t q -> p < q) -> min p t.

Hint Resolve min_intro: searchtrees.

(* p is greater than every member of t *)

Inductive maj (p : nat) (t : nat_tree) : Prop :=
    maj_intro : (forall q : nat, occ t q -> q < p) -> maj p t.

Hint Resolve maj_intro: searchtrees.

Inductive search : nat_tree -> Prop :=
  | nil_search : search NIL
  | bin_search :
      forall (n : nat) (t1 t2 : nat_tree),
      search t1 -> search t2 -> maj n t1 -> min n t2 -> search (bin n t1 t2).

Hint Resolve nil_search bin_search: searchtrees.



(* technical lemmas about maj and min *)

Lemma min_nil : forall p : nat, min p NIL.
(*********************************)
Proof.
 intro p; apply min_intro.
 intros q H; inversion_clear H.
Qed.

Hint Resolve min_nil: searchtrees.


Lemma maj_nil : forall p : nat, maj p NIL.
(*********************************)
Proof.
 intro p; apply maj_intro.
 intros q H; inversion_clear H.
Qed.

Hint Resolve maj_nil: searchtrees.



Lemma maj_not_occ : forall (p : nat) (t : nat_tree), maj p t -> ~ occ t p.
(**********************************************************)
Proof.
 unfold not in |- *; intros p t H H'.
 elim H; intros; absurd (p < p); auto with searchtrees arith.
Qed.

Hint Resolve maj_not_occ: searchtrees.


Lemma min_not_occ : forall (p : nat) (t : nat_tree), min p t -> ~ occ t p.
(**********************************************************)
Proof. 
 unfold not in |- *; intros p t H H'.
 elim H; intros; absurd (p < p); auto with searchtrees arith.
Qed.

Hint Resolve min_not_occ: searchtrees.
 



(* Some properties of  search trees *)
Section search_tree_basic_properties.

     Variable n : nat.
     Variable t1 t2 : nat_tree.
     Hypothesis se : search (bin n t1 t2).

   (* inversion lemmas *)
   (********************)


     Lemma search_l : search t1.
     (**************************)
     Proof.
      inversion_clear se; auto with searchtrees arith.
     Qed.

     Hint Resolve search_l: searchtrees.


    Lemma search_r : search t2.
     (***************************)
     Proof.
      inversion_clear se; auto with searchtrees arith.
     Qed.
     Hint Resolve search_r: searchtrees.

   
     Lemma maj_l : maj n t1.
     (***********************)
     Proof.
      inversion_clear se; auto with searchtrees arith.
     Qed.
     Hint Resolve maj_l: searchtrees.

     Lemma min_r : min n t2.
     (***********************)
     Proof.
     inversion_clear se; auto with searchtrees arith.
     Qed.
     Hint Resolve min_r: searchtrees.

        (* Exclusion lemmas *)

     Lemma not_right : forall p : nat, p <= n -> ~ occ t2 p.
     (*********************************************)
     Proof.
      intros p H; elim min_r.
      unfold not in |- *; intros; absurd (n < p); auto with searchtrees arith.
     Qed.
     Hint Resolve not_right: searchtrees.
 
     Lemma not_left : forall p : nat, n <= p -> ~ occ t1 p.
     (*********************************************)
     Proof.
      intros p H; elim maj_l.
      unfold not in |- *; intros; absurd (p < n); auto with searchtrees arith.
     Qed.
     Hint Resolve not_left: searchtrees.

     (* directive lemmas *)
     Lemma go_left : forall p : nat, occ (bin n t1 t2) p -> p < n -> occ t1 p.
     (*****************************************************************)
     Proof.
      intros p H H0; elim (occ_inv _ _ _ _ H).
       (* is p at the root ? *)
        simple induction 1; absurd (p < n);
         [ rewrite H1; auto with searchtrees arith
         | auto with searchtrees arith ].
        simple induction 1; auto with searchtrees arith.
       (* is p in the right son (t2) ? *)
       intro H2; absurd (occ t2 p); auto with searchtrees arith.
      Qed.

     Lemma go_right :
      forall p : nat, occ (bin n t1 t2) p -> n < p -> occ t2 p.
     (******************************************************************)
     Proof.
      intros p H H0; elim (occ_inv _ _ _ _ H).
      (* is p at the root ? *)
        simple induction 1; absurd (n < p);
         [ rewrite H1; auto with searchtrees arith
         | auto with searchtrees arith ].
        simple induction 1; auto with searchtrees arith.
       (* is p in the left son (t1) ? *)
      intro H2; absurd (occ t1 p); auto with searchtrees arith.
     Qed.


     (* A general inversion lemma *)

     Lemma search_inv :
      forall P : Prop,
      (search t1 -> search t2 -> maj n t1 -> min n t2 -> P) -> P.
     Proof.
      auto with searchtrees arith.
     Qed.

End search_tree_basic_properties.