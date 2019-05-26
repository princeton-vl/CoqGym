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

Set Asymmetric Patterns.

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
(*                                Sorting.v                                 *)
(****************************************************************************)

(* These sorting examples have first been compiled by P. Manoury using the  *)
(* ProPre tool to build recursive functions by cases                        *)

(* == Quelques fonctions utiles == *)

(* Inductive Set bool := true : bool | false : bool. *)

Definition si (X : Set) (b : bool) (x y : X) :=
  match b with
  | true => x
  | _ => y
  end.

Lemma si_eq1 : forall (X : Set) (x y : X), si X true x y = x.
Proof.
 auto.
Qed.

Lemma si_eq2 : forall (X : Set) (x y : X), si X false x y = y.
Proof.
 auto.
Qed.


(* Inductive Set nat : O:nat | S:nat->nat. *)

Fixpoint egal_nat (n : nat) : nat -> bool :=
  fun m : nat =>
  match n, m with
  | O, O => true
  | S n, S m => egal_nat n m
  | _, _ => false
  end.


Fixpoint inf_egal (n : nat) : nat -> bool :=
  fun m : nat =>
  match n, m with
  | O, m => true
  | S n, O => false
  | S n, S m => inf_egal n m
  end.


Lemma inf_egal_eq1 : forall m : nat, inf_egal 0 m = true.
Proof.
 auto.
Qed.

Lemma inf_egal_eq2 : forall n : nat, inf_egal (S n) 0 = false.
Proof.
 auto.
Qed. 

Lemma inf_egal_eq3 : forall n m : nat, inf_egal (S n) (S m) = inf_egal n m.
Proof.
 auto.
Qed. 

Inductive list (X : Set) : Set :=
  | Nil : list X
  | Cons : X -> list X -> list X.

Definition cdr (X : Set) (l : list X) :=
  match l with
  | Nil => Nil X
  | Cons _ xs => xs
  end.

Fixpoint length (X : Set) (l : list X) {struct l} : nat :=
  match l with
  | Nil => 0
  | Cons _ xs => S (length X xs)
  end.

(* append x y = yx *)
Fixpoint append (X : Set) (ys xs : list X) {struct xs} : 
 list X :=
  match xs with
  | Nil => ys
  | Cons x xs' => Cons X x (append X ys xs')
  end.

(* == Proprietes d'un tri == *)

Fixpoint sorted (l : list nat) : Prop :=
  match l with
  | Cons n (Cons m x as l) => inf_egal n m = true /\ sorted l
  | _ => True
  end.

Lemma sorted_eq1 : sorted (Nil nat) = True.
Proof.
 auto.
Qed.

Lemma sorted_eq2 : forall n : nat, sorted (Cons nat n (Nil nat)) = True.
Proof.
 auto.
Qed.

Lemma sorted_eq3 :
 forall (n m : nat) (x : list nat),
 sorted (Cons nat n (Cons nat m x)) =
 (inf_egal n m = true /\ sorted (Cons nat m x)).
Proof.
 auto.
Qed.

Fixpoint nocc (n : nat) (l : list nat) {struct l} : nat :=
  match l with
  | Nil => 0
  | Cons m x => si nat (egal_nat n m) (S (nocc n x)) (nocc n x)
  end.

Lemma nocc_eq1 : forall n : nat, nocc n (Nil nat) = 0.
Proof.
 auto.
Qed.

Lemma nocc_eq2 :
 forall (n m : nat) (x : list nat),
 nocc n (Cons nat m x) = si nat (egal_nat n m) (S (nocc n x)) (nocc n x).
Proof.
 auto.
Qed.

(* == Un lemme utile == *)
(* -- Sur les booleens *)

Theorem diff_true_false : true <> false.
Proof.
discriminate.
Qed.

(* -- Sur la conditionnelle *)
Theorem si_intro :
 forall (X : Set) (P : X -> Prop) (x y : X) (b : bool),
 (b = true :>bool -> P x) -> (b = false :>bool -> P y) -> P (si X b x y).
Proof.
simple induction b.

 intros.
 rewrite si_eq1.
 apply H.
 trivial.

 intros.
 rewrite si_eq2.
 apply H0.
 trivial.

Qed.

(* -- Sur la comparaison des entiers *)
Theorem inf_false_true :
 forall n m : nat, inf_egal n m = false -> inf_egal m n = true.
Proof.
simple induction n.
 intros.
 apply False_ind.
 apply diff_true_false.
 assumption.
 simple induction m.
  intro.
  trivial.
  intros.
  rewrite inf_egal_eq3.
  apply H.
  assumption.
Qed.

(* -- Sur le predicat "sorted" *)

Theorem sorted_cdr :
 forall (n : nat) (x : list nat), sorted (Cons nat n x) -> sorted x.
Proof.
simple induction x.
 intro. unfold sorted in |- *. trivial.
 intro. intro. intro. 
 rewrite sorted_eq3.
 tauto.
Qed.
 
Theorem sorted_inf :
 forall (n m : nat) (x : list nat),
 sorted (Cons nat n (Cons nat m x)) -> inf_egal n m = true.
Proof.
intro. intro. intro.
rewrite sorted_eq3.
tauto.
Qed.

(* == Tri par insertion *)

Fixpoint ins (n : nat) (l : list nat) {struct l} : 
 list nat :=
  match l with
  | Nil => Cons nat n (Nil nat)
  | Cons m x =>
      si (list nat) (inf_egal n m) (Cons nat n (Cons nat m x))
        (Cons nat m (ins n x))
  end.


Lemma ins_eq1 : forall n : nat, ins n (Nil nat) = Cons nat n (Nil nat).      
Proof.
 auto.
Qed.

Lemma ins_eq2 :
 forall (n m : nat) (x : list nat),
 ins n (Cons nat m x) =
 si (list nat) (inf_egal n m) (Cons nat n (Cons nat m x))
   (Cons nat m (ins n x)).
Proof.
 auto.
Qed.


Fixpoint tri_ins (l : list nat) : list nat :=
  match l with
  | Nil => Nil nat
  | Cons n x => ins n (tri_ins x)
  end.

Lemma tri_ins_eq1 : tri_ins (Nil nat) = Nil nat.
Proof.
 auto.
Qed.

Lemma tri_ins_eq2 :
 forall (n : nat) (x : list nat), tri_ins (Cons nat n x) = ins n (tri_ins x).
Proof.
 auto.
Qed.


(* -- Preuve de correction *)
(* -- 1 : Le resultat de "tri_ins" est une liste sorted *)

Theorem sorted_ins_Cons :
 forall (x : list nat) (n m : nat),
 inf_egal n m = false ->
 sorted (Cons nat m x) -> sorted (Cons nat m (ins n x)).
Proof.
simple induction x.
 intros.
 rewrite ins_eq1.
 rewrite sorted_eq3.
 split.
  apply inf_false_true. assumption.
  trivial.
 intros.
 rewrite ins_eq2.
 apply (si_intro (list nat) (fun x : list nat => sorted (Cons nat m x))).
  intro. 
  rewrite sorted_eq3.
  split.
   apply inf_false_true. assumption.
   rewrite sorted_eq3.
   split.
    apply H2.
    apply (sorted_cdr m). assumption.
  intro.
  rewrite sorted_eq3.
  split.
   apply (sorted_inf m x0 l). assumption.
   apply H.
    assumption.
    apply (sorted_cdr m). assumption.
Qed.

Theorem sorted_ins :
 forall (n : nat) (x : list nat), sorted x -> sorted (ins n x).
Proof.
simple induction x.
 trivial.
 intros.
 rewrite ins_eq2.
 apply si_intro.
  intros.
  rewrite sorted_eq3.
  split. assumption. assumption.
  intro.
  apply sorted_ins_Cons. assumption. assumption.
Qed.

(* -- 2 : Le resultat de "tri_ins" est une permutation de son entree *)
(*   ie : meme nombre d'occurrences de chaque element                *)

Theorem nocc_Cons_Cons :
 forall (n m p : nat) (x : list nat),
 nocc n (Cons nat m (Cons nat p x)) = nocc n (Cons nat p (Cons nat m x)).
Proof.
intros.
rewrite (nocc_eq2 n p (Cons nat m x)).
apply si_intro.
 intro.
 rewrite nocc_eq2.
 apply (si_intro nat (fun p : nat => p = S (nocc n (Cons nat m x)))).
  intro.
  rewrite nocc_eq2.
  rewrite H.
  rewrite si_eq1.
  rewrite nocc_eq2.
  rewrite H0.
  rewrite si_eq1.
  apply refl_equal.
  intro.
  rewrite nocc_eq2.
  rewrite H.
  rewrite si_eq1.
  rewrite nocc_eq2.
  rewrite H0.
  rewrite si_eq2.
  apply refl_equal.
 intro.
 rewrite (nocc_eq2 n m x).
 apply si_intro.
  intro.
  rewrite nocc_eq2.
  rewrite H0.
  rewrite si_eq1.
  rewrite nocc_eq2.
  rewrite H.
  rewrite si_eq2.
  apply refl_equal.
  intro.
  rewrite nocc_eq2.
  rewrite H0.
  rewrite si_eq2.
  rewrite nocc_eq2.
  rewrite H.
  rewrite si_eq2.
  apply refl_equal.
Qed.

Theorem nocc_Cons :
 forall (n m : nat) (x y : list nat),
 nocc n x = nocc n y -> nocc n (Cons nat m x) = nocc n (Cons nat m y).
Proof.
intros.
unfold nocc in |- *.
apply si_intro.
 intro.
 rewrite H0.
 simpl in |- *.
 apply eq_S.
 assumption.
 intro.
 rewrite H0.
 simpl in |- *.
 assumption.
Qed.

Theorem nocc_ins :
 forall (x : list nat) (n m : nat), nocc n (ins m x) = nocc n (Cons nat m x).
Proof.
simple induction x.
 trivial.
 intros.
 rewrite ins_eq2.
 apply
  (si_intro (list nat)
     (fun t : list nat => nocc n t = nocc n (Cons nat m (Cons nat x0 l)))).
  trivial.
  intro.
  rewrite nocc_Cons_Cons.
  apply nocc_Cons.
  apply H.
Qed.

Theorem nocc_tri_ins :
 forall (x : list nat) (n : nat), nocc n x = nocc n (tri_ins x).
Proof.
simple induction x.
 trivial.
 intros.
 rewrite tri_ins_eq2.
 rewrite nocc_ins.
 apply nocc_Cons.
 apply H.
Qed.

(* == Tri bubble *)

Fixpoint bubble_aux (x : list nat) : nat -> list nat :=
  fun n : nat =>
  match x with
  | Nil => Cons nat n (Nil nat)
  | Cons n0 l =>
      si (list nat) (inf_egal n n0) (Cons nat n (bubble_aux l n0))
        (Cons nat n0 (bubble_aux l n))
  end.

Definition bubble (x : list nat) : list nat :=
  match x with
  | Nil => Nil nat
  | Cons n l => bubble_aux l n
  end.

Lemma bubble_eq1 : bubble (Nil nat) = Nil nat. 
Proof.
  auto.
Qed.

Lemma bubble_eq2 :
 forall n : nat, bubble (Cons nat n (Nil nat)) = Cons nat n (Nil nat).
Proof.
  auto.
Qed.
Lemma bubble_eq3 :
 forall (n m : nat) (x : list nat),
 bubble (Cons nat n (Cons nat m x)) =
 si (list nat) (inf_egal n m) (Cons nat n (bubble (Cons nat m x)))
   (Cons nat m (bubble (Cons nat n x))).
Proof.
  auto.
Qed.



Fixpoint bubble_sort0 (n : nat) : list nat -> list nat :=
  fun x : list nat =>
  match n with
  | O => x
  | S n0 => bubble_sort0 n0 (bubble x)
  end.

Definition bubble_sort (x : list nat) : list nat :=
  bubble_sort0 (length nat x) x.



(* == Tri fusion *)

Fixpoint fusion (x : list nat) : list nat -> list nat :=
  fun y : list nat =>
  match x with
  | Nil => y
  | Cons n l0 =>
      (fix fusion_r (y : list nat) : list nat :=
         match y with
         | Nil => x
         | Cons n0 l2 =>
             si (list nat) (inf_egal n n0)
               (Cons nat n (fusion l0 (Cons nat n0 l2)))
               (Cons nat n0 (fusion_r l2))
         end) y
  end.


Lemma fusion_eq1 : forall ms : list nat, fusion (Nil nat) ms = ms.
Proof.
 auto.
Qed.

Lemma fusion_eq2 :
 forall (n : nat) (ns : list nat),
 fusion (Cons nat n ns) (Nil nat) = Cons nat n ns.
Proof.
 auto.
Qed.

Lemma fusion_eq3 :
 forall (n : nat) (ns : list nat) (m : nat) (ms : list nat),
 fusion (Cons nat n ns) (Cons nat m ms) =
 si (list nat) (inf_egal n m) (Cons nat n (fusion ns (Cons nat m ms)))
   (Cons nat m (fusion (Cons nat n ns) ms)).

Proof.
 auto.
Qed.


Fixpoint tri_merge0 (n : nat) : list (list nat) -> list nat :=
  fun ll : list (list nat) =>
  match n, ll with
  | S l, Cons ns Nil => ns
  | S l, Cons ns (Cons ms xss) => fusion (fusion ns ms) (tri_merge0 l xss)
  | _, _ => Nil nat
  end.


Fixpoint l2ll (X : Set) (l : list X) {struct l} : list (list X) :=
  match l with
  | Nil => Nil (list X)
  | Cons x xs => Cons (list X) (Cons X x (Nil X)) (l2ll X xs)
  end.

Definition tri_merge (l : list nat) : list nat :=
  tri_merge0 (length nat l) (l2ll nat l).



(* == Tri par abrbre binaire de recherche *)

Inductive arbin : Set :=
  | Fe : arbin
  | Br : nat -> arbin -> arbin -> arbin.


Fixpoint abr2Ln (a : arbin) : list nat :=
  match a with
  | Fe => Nil nat
  | Br n a1 a2 => append nat (Cons nat n (abr2Ln a2)) (abr2Ln a1)
  end.

Fixpoint insabr (n : nat) (a : arbin) {struct a} : arbin :=
  match a with
  | Fe => Br n Fe Fe
  | Br m a1 a2 =>
      si arbin (inf_egal n m) (Br m (insabr n a1) a2) (Br m a1 (insabr n a2))
  end.

Fixpoint Ln2abr (l : list nat) : arbin :=
  match l with
  | Nil => Fe
  | Cons n ns => insabr n (Ln2abr ns)
  end.

Definition tri_abr (ns : list nat) : list nat := abr2Ln (Ln2abr ns).


(* == Tri par tas *)

Fixpoint Tas2Ln (a : arbin) : list nat :=
  match a with
  | Fe => Nil nat
  | Br n a1 a2 => Cons nat n (fusion (Tas2Ln a1) (Tas2Ln a2))
  end.

Fixpoint insTas (n : nat) (a : arbin) {struct a} : arbin :=
  match a with
  | Fe => Br n Fe Fe
  | Br m a1 a2 =>
      si arbin (inf_egal n m) (Br n a2 (insTas m a1)) (Br m a2 (insTas n a1))
  end. 

Fixpoint Ln2Tas (l : list nat) : arbin :=
  match l with
  | Nil => Fe
  | Cons n ns => insTas n (Ln2Tas ns)
  end.

Definition tri_heap (l : list nat) : list nat := Tas2Ln (Ln2Tas l).
