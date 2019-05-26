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

(****************************************************************)
(*           The Calculus of Inductive Constructions            *)
(*                       COQ v5.10                              *)
(*                                                              *)
(* Laurent Arditi.  Laboratoire I3S. CNRS ura 1376.             *)
(* Universite de Nice - Sophia Antipolis                        *)
(* arditi@unice.fr, http://wwwi3s.unice.fr/~arditi/lolo.html    *)
(*                                                              *)
(* date: may 1995                                               *)
(* file: Adder.v                                                *)
(* contents: Definition of an adder for two BVs and a carry     *)
(*                                                              *)
(****************************************************************)

Require Export BV.
Require Export FullAdder.

(****************************************************************)

(* Pourquoi ne peut-on ecrire ceci: ? *)
(*Recursive Definition BV_full_adder_sum : BV -> BV -> bool -> BV :=
utiliser le type BV en parties gauches ????????? UN BUG DE COQ ??????????
*)
(*Recursive Definition BV_full_adder_sum: (list bool)->(list bool)->bool->BV :=
    (nil bool) (nil bool) b => nilbv
  | (nil bool) (cons bool vh vt) b =>
	   (consbv (half_adder_sum vh b)
		   (BV_full_adder_sum (nil bool) vt (half_adder_carry vh b)))
  | (cons bool vh vt) (nil bool) b =>
	   (consbv (half_adder_sum vh b)
		   (BV_full_adder_sum vt (nil bool) (half_adder_carry vh b)))
  | (cons bool vh vt) (cons bool wh wt) b =>
	    (consbv (full_adder_sum vh wh b)
		    (BV_full_adder_sum vt wt (full_adder_carry vh wh b))).
*)

Definition BV_full_adder_sum :=
  (fix F (l : list bool) : list bool -> bool -> BV :=
     match l with
     | nil =>
         (fix F0 (l0 : list bool) : bool -> BV :=
            match l0 with
            | nil => fun _ : bool => nilbv
            | b :: l1 =>
                fun z : bool =>
                consbv (half_adder_sum b z) (F0 l1 (half_adder_carry b z))
            end)
     | b :: l0 =>
         fun x2 : list bool =>
         match x2 with
         | nil =>
             fun y z : bool =>
             consbv (half_adder_sum y z) (F l0 nil (half_adder_carry y z))
         | b0 :: l1 =>
             fun y z : bool =>
             consbv (full_adder_sum y b0 z)
               (F l0 l1 (full_adder_carry y b0 z))
         end b
     end).
    

Lemma BV_full_adder_sum_eq1 :
 forall b : bool, BV_full_adder_sum nil nil b = nilbv.
Proof.
 auto.
Qed.

Lemma BV_full_adder_sum_eq2 :
 forall (vh : bool) (vt : list bool) (b : bool),
 BV_full_adder_sum nil (vh :: vt) b =
 consbv (half_adder_sum vh b)
   (BV_full_adder_sum nil vt (half_adder_carry vh b)).
Proof.
 auto.
Qed.

Lemma BV_full_adder_sum_eq3 :
 forall (vh : bool) (vt : list bool) (b : bool),
 BV_full_adder_sum (vh :: vt) nil b =
 consbv (half_adder_sum vh b)
   (BV_full_adder_sum vt nil (half_adder_carry vh b)).
Proof.
 auto.
Qed.

Lemma BV_full_adder_sum_eq4 :
 forall (vh : bool) (vt : list bool) (wh : bool) (wt : list bool) (b : bool),
 BV_full_adder_sum (vh :: vt) (wh :: wt) b =
 consbv (full_adder_sum vh wh b)
   (BV_full_adder_sum vt wt (full_adder_carry vh wh b)).
Proof.
 auto.
Qed.


(*Recursive Definition BV_full_adder_carry: (list bool)->(list bool)->bool->bool
									   :=
     (nil bool) (nil bool) b => b
   | (nil bool) (cons vh vt) b => 
	(BV_full_adder_carry (nil bool) vt (half_adder_carry vh b))
   | (cons vh vt) (nil bool) b =>
	(BV_full_adder_carry vt (nil bool) (half_adder_carry vh b))
   | (cons vh vt) (cons wh wt) b => 
	(BV_full_adder_carry vt wt (full_adder_carry vh wh b)).
*)



Definition BV_full_adder_carry :=
  (fix F (l : list bool) : list bool -> bool -> bool :=
     match l with
     | nil =>
         (fix F0 (l0 : list bool) : bool -> bool :=
            match l0 with
            | nil => fun z : bool => z
            | b :: l1 => fun z : bool => F0 l1 (half_adder_carry b z)
            end)
     | b :: l0 =>
         fun x2 : list bool =>
         match x2 with
         | nil => fun y z : bool => F l0 nil (half_adder_carry y z)
         | b0 :: l1 => fun y z : bool => F l0 l1 (full_adder_carry y b0 z)
         end b
     end).


Lemma BV_full_adder_carry_eq1 :
 forall b : bool, BV_full_adder_carry nil nil b = b.

Proof.
 auto.
Qed.

Lemma BV_full_adder_carry_eq2 :
 forall (vh : bool) (vt : list bool) (b : bool),
 BV_full_adder_carry nil (vh :: vt) b =
 BV_full_adder_carry nil vt (half_adder_carry vh b).
Proof.
 auto.
Qed.


Lemma BV_full_adder_carry_eq3 :
 forall (vh : bool) (vt : list bool) (b : bool),
 BV_full_adder_carry (vh :: vt) nil b =
 BV_full_adder_carry vt nil (half_adder_carry vh b).

Proof.
 auto.
Qed.

Lemma BV_full_adder_carry_eq4 :
 forall (vh : bool) (vt : list bool) (wh : bool) (wt : list bool) (b : bool),
 BV_full_adder_carry (vh :: vt) (wh :: wt) b =
 BV_full_adder_carry vt wt (full_adder_carry vh wh b).

Proof.
 auto.
Qed.


Definition BV_full_adder (v w : BV) (cin : bool) : BV :=
  appbv (BV_full_adder_sum v w cin)
    (consbv (BV_full_adder_carry v w cin) nilbv).


Hint Unfold BV_full_adder.

(****************************************************************)

Lemma BV_full_adder_sum_v_nil_false :
 forall v : BV, BV_full_adder_sum v nilbv false = v.
unfold nilbv in |- *. simple induction v. trivial. intros.
rewrite BV_full_adder_sum_eq3. rewrite half_adder_carry_false.
rewrite half_adder_sum_false. rewrite H; auto.
Qed. Hint Resolve BV_full_adder_sum_v_nil_false.

Lemma BV_full_adder_carry_v_nil_false :
 forall v : BV, BV_full_adder_carry v nilbv false = false.
unfold nilbv in |- *.
simple induction v. trivial. intros.
rewrite BV_full_adder_carry_eq3. rewrite half_adder_carry_false.
trivial.
Qed. Hint Resolve BV_full_adder_carry_v_nil_false.

Lemma BV_full_adder_sum_sym :
 forall (v w : BV) (cin : bool),
 BV_full_adder_sum v w cin = BV_full_adder_sum w v cin.
simple induction v. simple induction w. auto. intros.
rewrite BV_full_adder_sum_eq2. rewrite BV_full_adder_sum_eq3.
rewrite H. auto. simple induction w. intro.
rewrite BV_full_adder_sum_eq2. rewrite BV_full_adder_sum_eq3. rewrite H.
auto. intros. repeat rewrite BV_full_adder_sum_eq4. rewrite H.
do 2 rewrite full_adder_carry_sym1. do 2 rewrite full_adder_sum_sym1. auto.
Qed.
				       
Lemma length_BV_full_adder_sum :
 forall (v w : BV) (cin : bool),
 lengthbv v = lengthbv w -> lengthbv (BV_full_adder_sum v w cin) = lengthbv v.
unfold lengthbv in |- *. simple induction v. simple induction w. intros. case cin. simpl in |- *. trivial.
simpl in |- *. trivial.
intros. absurd (length (nil:list bool) = length (a :: l)).
simpl in |- *. discriminate. exact H0. simple induction w. simpl in |- *. intros. discriminate H0.
intros. simpl in |- *. rewrite H. trivial. generalize H1. simpl in |- *. auto.
Qed.

Lemma BV_full_adder_carry_sym :
 forall (v w : BV) (cin : bool),
 BV_full_adder_carry v w cin = BV_full_adder_carry w v cin.
simple induction v. simple induction w. auto. intros.
rewrite BV_full_adder_carry_eq2. rewrite BV_full_adder_carry_eq3.
rewrite H; auto. simple induction w. intros. rewrite BV_full_adder_carry_eq2.
rewrite BV_full_adder_carry_eq3.
rewrite H. auto. intros. do 2 rewrite BV_full_adder_carry_eq4.
rewrite H. rewrite full_adder_carry_sym1. auto.
Qed.

Lemma BV_full_adder_sym :
 forall (v w : BV) (cin : bool),
 BV_full_adder v w cin = BV_full_adder w v cin.
unfold BV_full_adder in |- *.
intros.
rewrite BV_full_adder_sum_sym. rewrite BV_full_adder_carry_sym. auto.
Qed.
