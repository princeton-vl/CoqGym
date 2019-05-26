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
(*                                  gram.v                                  *)
(****************************************************************************)
(*              Formal Language Theory                                      *)
(*                                                                          *)
(*              Judicael Courant - Jean-Christophe Filliatre                *)
(*                                                                          *)
(*              Developped in V5.8  June-July 1993                          *)
(*              Ported     to V5.10 October 1994                            *)
(****************************************************************************)

Require Import Ensf.
Require Import Words.
Require Import more_words.
Require Import need.
Require Import fonctions.
Require Import Relations.


Definition Mots (X : Ensf) :=
  forall a : Elt, dans a X -> exists w : Word, word w = a.


Definition Regles (X V R : Ensf) :=
  forall x : Elt,
  dans x R ->
  ex2 (fun A : Elt => dans A V)
    (fun A : Elt =>
     ex2 (fun B : Word => x = couple A (word B))
       (fun B : Word => inmonoid (union X V) B)).



Lemma Regles_inv1 :
 forall (X V R : Ensf) (x y : Elt),
 Regles X V R -> dans (couple x y) R -> dans x V.
intros X V R x y Regles_R dans_couple_R.
cut
 (ex2 (fun A : Elt => dans A V)
    (fun A : Elt =>
     ex2 (fun B : Word => couple x y = couple A (word B))
       (fun B : Word => inmonoid (union X V) B))).
intro temp; elim temp; clear temp.
intros x0 dans_x0_V temp; elim temp; clear temp.
intros u eg_couple inmonoid_u.
replace x with x0; prolog [ sym_equal couple_couple_inv1 ] 3.
	(*Assumption.
	Apply sym_equal.
	Apply couple_couple_inv1 with y (word u); Assumption.*)

auto.
Qed.

Lemma Regles_inv2 :
 forall (X V R : Ensf) (x : Elt) (u : Word),
 Regles X V R -> dans (couple x (word u)) R -> inmonoid (union X V) u.
intros X V R x u Regles_R dans_couple_R.
(**) cut
      (ex2 (fun A : Elt => dans A V)
         (fun A : Elt =>
          ex2 (fun B : Word => couple x (word u) = couple A (word B))
            (fun B : Word => inmonoid (union X V) B))).
intro temp; elim temp; clear temp.
intros x0 dans_x0_V temp; elim temp; clear temp.
intros u0 eg_couple inmonoid_u0.
replace u with u0; prolog [ sym_equal couple_couple_inv2 word_word_inv ] 4.
	(*Assumption.
	Apply word_word_inv.
	Apply couple_couple_inv2 with x0 x;Auto.*)
(**) auto.
Qed.


(* Definition d'une grammaire, *)
(*X : ensemble des terminaux, *)
(*V ensemble des non-terminaux, *)
(*R ensemble des productions A -> w, *)
(*S axiome *)

Definition isGram (X V R : Ensf) (S : Elt) : Prop :=
  Mots X /\ inter X V empty /\ dans S V /\ Regles X V R.

Section Easy_lemma_isGram.

Variable X V R : Ensf.
Variable S : Elt.
Let H := isGram X V R S.

Lemma isGram1 : H -> Mots X.
intro H1.
elim H1.
trivial.
Qed.

Lemma isGram2 : H -> inter X V empty.
intro H1.
elim H1.
intuition.
Qed.

Lemma isGram3 : H -> dans S V.
intro H1.
elim H1.
intuition.
Qed.


Lemma isGram4 : H -> Regles X V R.
intro H1.
elim H1.
intuition.
Qed.

Lemma isGram5 : Mots X -> inter X V empty -> dans S V -> Regles X V R -> H.
intros.
red in |- *; red in |- *.
auto.
Qed.


End Easy_lemma_isGram.
(*--------*)

Lemma Regles_R :
 forall X V R R' : Ensf, inclus R' R -> Regles X V R -> Regles X V R'.
unfold Regles in |- *.
auto.
Qed.

Lemma Regles_V :
 forall X V R V' : Ensf, inclus V V' -> Regles X V R -> Regles X V' R.
unfold Regles in |- *.
intros X V R V' inclus_V_V' Regles_X_V_R x dans_x_R.
elim (Regles_X_V_R x dans_x_R).
intros A dans_A_V temp; elim temp; clear temp.
intros B egal_B inmonoid_B.
exists A.
auto.
exists B.
assumption.
apply inmonoid_inclus with (union X V); auto.
Qed.



Lemma Regles_add :
 forall (X V R : Ensf) (a : Elt) (u : Word),
 Regles X V R ->
 dans a V -> inmonoid (union X V) u -> Regles X V (add (couple a (word u)) R).
intros X V R a u R_R dans_a_V inmonoid_u_X_V_u.
red in |- *.
intros x dans_x_R'.
cut (couple a (word u) = x :>Elt \/ dans x R). (**)
intuition.
(*	Intro egal_x_couple.*)
	exists a.
		assumption.
		exists u; auto.
(**)apply dans_add; assumption.
Qed.

Lemma Regles_add2 :
 forall (X V R : Ensf) (a : Elt), Regles X V R -> Regles X (add a V) R.
intros.
apply Regles_V with V; auto.
Qed.


Lemma Regles_union :
 forall X V R R' : Ensf,
 Regles X V R -> Regles X V R' -> Regles X V (union R R').

unfold Regles in |- *.
intros X V R R' R_R R_R' x dans_x_union.
cut (dans x R \/ dans x R'); auto.
intros [HR| HR']; auto.
Qed.

Lemma isGram_inclus2 :
 forall (X V R R' : Ensf) (S : Elt),
 inclus R' R -> isGram X V R S -> isGram X V R' S.
prolog [ isGram4 Regles_R isGram3 isGram2 isGram1 isGram5 ] 11.

(*Intros X V R R' S incl isGram_X_V_R_S.
Apply isGram5 .
	Apply isGram1 with V R S; Assumption.
	Apply isGram2 with R S; Assumption.
	Apply isGram3 with X R; Assumption.
	Apply Regles_R with R.
	     Assumption.
	     Apply isGram4 with S; Assumption.*)
Qed.

Lemma isGram_inclus3 :
 forall (X V R : Ensf) (S a : Elt), isGram X V (add a R) S -> isGram X V R S.
intros X V R S a isGram_X_V_a_R_S.
apply isGram_inclus2 with (add a R); auto.
Qed.


(*--------------------------*)



(* (Derive R u v) signifie "u se recrit en v par une production de R" *)
Inductive Derive (R : Ensf) : Word -> Word -> Prop :=
 
 (*si A -R-> u alors Av -G-> uv *)
  | Derive1 :
      forall (u v : Word) (A : Elt),
      dans (couple A (word u)) R ->
      Derive R (cons A v) (Append u v)
      
      (*si u -G-> v alors x::u -G-> x::v*)
  | Derive2 :
      forall (u v : Word) (x : Elt),
      Derive R u v -> Derive R (cons x u) (cons x v).

Hint Resolve Derive1.
Hint Resolve Derive2.


Lemma Derive_inclus :
 forall (R1 R2 : Ensf) (u v : Word),
 inclus R1 R2 -> Derive R1 u v -> Derive R2 u v.
intros R1 R2 u v inclus_R1_R2 Der_R1.
elim Der_R1; auto.
Qed.


Definition Derive_inv (R : Ensf) (x y : Word) :=
  match x return Prop with
  | nil =>
      (* nil  *)  False
      (* cons *) 
  | cons A w =>
      ex2 (fun u : Word => dans (couple A (word u)) R)
        (fun u : Word =>
         ex2 (fun v : Word => cons A v = x :>Word)
           (fun v : Word => Append u v = y :>Word)) \/
      ex2 (fun v : Word => Derive R w v)
        (fun v : Word => cons A v = y :>Word)
  end.


Lemma Derive_inv1 :
 forall (R : Ensf) (u v : Word), Derive R u v -> Derive_inv R u v.
intros R x y Der_x_y.
unfold Derive_inv in |- *.
elim Der_x_y; prolog [ ex_intro2 refl_equal or_intror or_introl ] 8.
(* Intros u v A dans_couple.
 Left.
 Exists u; [Assumption | Exists v; Apply refl_equal].

 Intros u v x0 Der_u_v Der_inv_u_v.
 Simpl; Right.
 Exists v; Trivial .*)
Qed.

Hint Resolve Derive_inv1.

Lemma Derive_inv2 :
 forall (R : Ensf) (x y : Word),
 Derive_inv R x y ->
 exists A : Elt,
   (exists2 w : Word,
      cons A w = x &
      (exists2 u : Word,
         dans (couple A (word u)) R &
         (exists2 v : Word, cons A v = x & Append u v = y)) \/
      (exists2 v : Word, Derive R w v & cons A v = y)).
intros R x y.
elim x.
unfold Derive_inv in |- *.

intuition.
(*Intro temp; Elim temp; Clear temp.*)

intros x0 w Hyp_rec.
unfold Derive_inv in |- *.
(*Simpl.*)
exists x0.
exists w; trivial.
Qed.


Lemma Derive_inv3 :
 forall (R : Ensf) (x y : Word),
 Derive R x y ->
 exists A : _,
   (exists2 w : _,
      cons A w = x &
      (exists2 u : _,
         dans (couple A (word u)) R &
         (exists2 v : _, cons A v = x & Append u v = y)) \/
      (exists2 v : _, Derive R w v & cons A v = y)).

(*
Proof [R:Ensf][x,y:Word][D : (Derive R x y)]
(Derive_inv2 R x y (Derive_inv1 R x y D)).
*)
prolog [ Derive_inv1 Derive Derive_inv2 ] 7.
Qed.

Lemma in_mon_X_Der_imp_inmon_X :
 forall (X V R : Ensf) (u v : Word),
 Regles X V R ->
 Derive R u v -> inmonoid (union X V) u -> inmonoid (union X V) v.

intros X V1 R1 u v Regles_R1 Der_R1.
elim Der_R1;
 prolog
  [ Regles_inv2 inmonoid_cons_inv inmonoid_cons_inv2 inmonoid_cons
   inmonoid_Append ] 10.
	(*Intros u0 v0 A dans_R1 inmonoid_cons_A_v0.
	Apply inmonoid_Append.
		Apply Regles_inv2 with R1 A;Assumption.
		Apply inmonoid_cons_inv with A; Assumption.

	Intros u0 v0 x Der_R1_u0 imp inmon_cons_x_u0.
	Apply inmonoid_cons.
		Apply imp.
		Apply inmonoid_cons_inv with x;Assumption.

		Apply inmonoid_cons_inv2 with u0;Assumption.*)

Qed.


(*  (Derivestar R u v) signifie "u se recrit en v par zero ou plusieurs productions de R" *)


Definition Derivestar (R : Ensf) := Rstar Word (Derive R).

Hint Unfold Derivestar.

Lemma Derivestar_refl : forall (R : Ensf) (u : Word), Derivestar R u u.
auto.
Qed.

Hint Resolve Derivestar_refl.

Lemma Derivestar_R :
 forall (R : Ensf) (u v w : Word),
 Derive R u v -> Derivestar R v w -> Derivestar R u w.
unfold Derivestar in |- *.
prolog [ Rstar_R ] 8.
(*Intros.
Apply Rstar_R with v;Assumption.*)
Qed.


Lemma Derivestar_inv :
 forall (R : Ensf) (u v : Word),
 Derivestar R u v ->
 u = v \/ (exists2 w : Word, Derive R u w & Derivestar R w v).
unfold Derivestar in |- *.
prolog [ Rstar_inv ] 6.
(*Intros R u v Der_R.
Apply Rstar_inv;Assumption.*)
Qed.

Hint Resolve Derivestar_inv.


Lemma Derivestar_inclus :
 forall (R1 R2 : Ensf) (u v : Word),
 inclus R1 R2 -> Derivestar R1 u v -> Derivestar R2 u v.
intros R1 R2 u v inclus_R1_R2 Der_R1.
unfold Derivestar, Rstar in Der_R1.
pattern u, v in |- *.
apply Der_R1.
	auto.
	intros; prolog [ Derive_inclus Derivestar_R ] 3.
	(*Intros a b c Der_a_b Der_b_c.
	Apply Derivestar_R with b.
		Apply Derive_inclus with R1;Assumption.
		Assumption.*)
Qed.


(* LG X V R S est l'ensemble de mots engendre par la grammaire (X V R S) *)

Definition LG (X V R : Ensf) (S : Elt) : wordset :=
  fun w : Word => Derivestar R (cons S nil) w /\ inmonoid X w.


Lemma LG_inv :
 forall (X V R : Ensf) (S : Elt) (w : Word), LG X V R S w -> inmonoid X w.
unfold LG in |- *.
intros.
elim H; auto.
Qed.

(*Pour toute grammaire (X,V,R,S), (LG X V R S) est un langage *)

Lemma LG_langage :
 forall (X V R : Ensf) (S : Elt), isGram X V R S -> islanguage X (LG X V R S).
intros; red in |- *; intros; elim H0; auto.
Qed.


(*Reunion de 2 grammaires *)

Definition Gunion (V1 R1 V2 R2 : Ensf) := (union V1 V2, union R1 R2).

(*------------------*)
Section injprod.

Let injproduc (f : Elt -> Elt) (V : Ensf) := extension V f.


Definition injproducg : Ensf -> Elt -> Elt := injproduc injgauche.

Definition injproducd : Ensf -> Elt -> Elt := injproduc injdroite.
					
(*prennent en arguments l'ensemble de non-terminaux V,*)
(*de productions R et rendent*)
(*les injections gauche et droite*)
(*utilisees ensuite pour la definition de G_union_disj_p.*)

End injprod.


Definition Gunion_disj_p (V1 R1 : Ensf) (S1 : Elt) 
  (V2 R2 : Ensf) (S2 S : Elt) :=
  (add S (fst (Gunion V1 R1 V2 R2)),
  (add (couple S (word (cons S1 nil)))
     (add (couple S (word (cons S2 nil))) (snd (Gunion V1 R1 V2 R2))), S)).


(* image par une fonction d'une grammaire *)

Definition imageGram (f : Elt -> Elt) (X V R : Ensf) 
  (S : Elt) :=
  (map f X,
  (map f V,
  (map
     (fun P : Elt =>
      couple (f (first P))
        ((fun w : Elt => word (Word_ext f (word_inv w))) (second P))) R, 
  f S))).

