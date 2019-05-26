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


(* BIBLI *)

(* fichier de bibliotheque*)

Require Export Arith.
Require Export Omega.
Require Import List.

Global Set Asymmetric Patterns.

Section SEPAR.

(* lorsque l'egalite est decidable sur un ensemble *)

Lemma eq_bool_dec : forall b : bool, {b = true} + {b = false}.
Proof.
 simple induction b; auto.
Defined.

Definition eq_dec (E : Set) := forall a b : E, {a = b} + {a <> b}.

Lemma case_eq :
 forall (E F : Set) (eq_E_dec : eq_dec E) (x : E) (y z : F),
 match eq_E_dec x x with
 | left _ => y
 | right _ => z
 end = y. 
Proof.
 intros; case (eq_E_dec x x).
 auto.

 intros; absurd (x = x); auto.
Qed.

Lemma case_ineq :
 forall (E F : Set) (eq_E_dec : eq_dec E) (x x' : E) (y z : F),
 x <> x' -> match eq_E_dec x x' with
            | left _ => y
            | right _ => z
            end = z. 
Proof.
 intros; case (eq_E_dec x x').
 intros; absurd (x = x'); auto.

 trivial.
Qed.

Lemma eq_couple_dec :
 forall (E F : Set) (eq_E_dec : eq_dec E) (eq_F_dec : eq_dec F) 
   (x1 x2 : E) (y1 y2 : F), {x1 = x2 /\ y1 = y2} + {x1 <> x2 \/ y1 <> y2}.
Proof.
 intros; case (eq_E_dec x1 x2); case (eq_F_dec y1 y2); intros; auto. 
Qed.

End SEPAR.

Section OTHER.

(* codage booleen en entier *)

Definition Int (b : bool) := if b then 1%Z else 0%Z.

Lemma true_not_false : forall b : bool, b = true -> false <> b.
Proof.
 intros; rewrite H; discriminate.
Qed.

(* axiome utilise frequement disant que l'egalite fonctionnelle est la
meme que l'egalite denotationnelle, il est possible que cet axiome ne
soit utilise que sur des ensembles finis sur lequel il pourrait etre
demontre. Il est possible aussi que l'on puisse s'en passer mais il
simplifie bien la vie *)

Axiom
  funct_eq :
    forall (E F : Set) (g h : E -> F), (forall e : E, g e = h e) -> g = h. 

(* trivialite inclassable *)

Lemma in_not_in :
 forall (E : Set) (a b : E) (l : list E), In a l -> ~ In b l -> a <> b. 
Proof.
 intros; red in |- *; intros.
 elim H0; rewrite <- H1; auto.
Qed.

End OTHER.

Section PointFixe.

(* cadeau de Christine Paulin, pour definir un point fixe avec une
relation bien fondee *)

Variable A : Set.
Variable P : A -> Set.
Variable R : A -> A -> Prop.
Hypothesis Rwf : well_founded R.
Variable F : forall x : A, (forall y : A, R y x -> P y) -> P x.

Hypothesis
  F_ext :
    forall (x : A) (f g : forall y : A, R y x -> P y),
    (forall (y : A) (p : R y x), f y p = g y p) -> F x f = F x g.

Fixpoint Fix_F (x : A) (r : Acc R x) {struct r} : P x :=
  F x (fun (y : A) (p : R y x) => Fix_F y (Acc_inv r y p)).

Scheme Acc_inv_dep := Induction for Acc Sort Prop.

Lemma Fix_F_eq :
 forall (x : A) (r : Acc R x),
 Fix_F x r = F x (fun (y : A) (p : R y x) => Fix_F y (Acc_inv r y p)).
intros x r; elim r using Acc_inv_dep; auto.
Qed.
                                     
Lemma Fix_F_inv : forall (x : A) (r s : Acc R x), Fix_F x r = Fix_F x s.
intro x; elim (Rwf x); intros.
rewrite (Fix_F_eq x0 r); rewrite (Fix_F_eq x0 s); intros.
apply F_ext; auto.
Qed.

Definition Fix (x : A) := Fix_F x (Rwf x).

Lemma fix_eq : forall x : A, Fix x = F x (fun (y : A) (p : R y x) => Fix y).
intro; unfold Fix in |- *.
rewrite (Fix_F_eq x).
apply F_ext; intros.
apply Fix_F_inv.
Qed.

End PointFixe.

Section WF_ROOT.

(* application au cas qui nous preoccupe, la relation est bien fondee
car il existe une fonction f de E dans nat strictement croissante, la
relation est decidable en ce sens qu'il existe une preuve qu'un
element a ou non des antecedents et un algorithme permettant de
choisir un antecedent quand il en a, il est alors possible de definir
par point fixe une fonction root qui a tout element associe
l'antecedent sans parent accessible par l'algorithme *)

Variable E : Set.

Variable f : E -> nat.

Variable R : E -> E -> Prop.

Hypothesis R_dec : forall x : E, {y : E | R y x} + {(forall y : E, ~ R y x)}.

Hypothesis strict : forall x y : E, R x y -> f x < f y.


Lemma lt_acc : forall (n : nat) (y : E), f y < n -> Acc R y.
Proof.
 simple induction n.
 intros; absurd (f y < 0); auto with arith.
 intros; apply Acc_intro.
 intros; apply H.
 apply lt_le_trans with (m := f y); auto with arith.
Qed.

Lemma wf_R : well_founded R.
Proof.
 unfold well_founded in |- *; intro.
 apply Acc_intro; intros.
 apply (lt_acc (f a)); auto.
Qed.

Definition F (x : E) (f : forall y : E, R y x -> E) :=
  match R_dec x with
  | inleft z => let (y0, r0) := z in f y0 r0
  | inright _ => x
  end.

Lemma F_eq :
 forall (x : E) (f1 f2 : forall y : E, R y x -> E),
 (forall (y : E) (r : R y x), f1 y r = f2 y r) -> F x f1 = F x f2.
Proof.
 intros; unfold F in |- *; case (R_dec x); intros.
 elim s; intros; auto.

 trivial.
Qed.

Definition root := Fix E (fun _ : E => E) R wf_R F.

Definition root_eq := fix_eq E (fun _ : E => E) R wf_R F F_eq.

Lemma root_no_R : forall x y : E, ~ R y (root x).
Proof.
 intros; elim (wf_R x).
 intros; rewrite root_eq.
 unfold F at 1 in |- *; case (R_dec x0); intros.
 elim s; intros.
 fold (root x1) in |- *; apply H0; trivial.

 trivial.
Qed.

Lemma prop_root :
 forall (P : E -> Prop) (x : E),
 P x -> (forall y z : E, P y -> R z y -> P z) -> P (root x).
Proof.
 intros; generalize H.
 elim (wf_R x).
 intros; unfold root in |- *; rewrite root_eq.
 unfold F at 1 in |- *; case (R_dec x0); intros.
 elim s; intros x1 y.
 apply (H2 x1 y).
 apply H0 with (y := x0); trivial.

 trivial.
Qed.

End WF_ROOT.