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
(*                                 Words.v                                  *)
(****************************************************************************)
(*              Formal Language Theory                                      *)
(*                                                                          *)
(*              Judicael Courant - Jean-Christophe Filliatre                *)
(*                                                                          *)
(*              Developped in V5.8  June-July 1993                          *)
(*              Ported     to V5.10 October 1994                            *)
(****************************************************************************)

Require Import Ensf.

Parameter alph : Ensf.
Parameter epsilon : Elt.
  Axiom not_dans_epsilon_alph : ~ dans epsilon alph.

(*  On definit le predicat (inmonoid X w) qui signifie que le mot w	*)
(*  est dans le monoide libre engendre par X.				*)

Inductive inmonoid (X : Ensf) : Word -> Prop :=
  | inmonoid_nil : inmonoid X nil
  | inmonoid_cons :
      forall (w : Word) (e : Elt),
      inmonoid X w -> dans e X -> inmonoid X (cons e w).
Hint Resolve inmonoid_nil.
Hint Resolve inmonoid_cons.

(*  Inversion de la definition 						*)
(*
Fixpoint Inmonoid [X:Ensf; w:Word] : Prop :=
  (<Prop>Case w of
      (* nil  *) True
      (* cons *) [a:Elt][w':Word]( (dans a X) /\ (Inmonoid X w') )
  end ).
*)
Fixpoint Inmonoid (X : Ensf) (w : Word) {struct w} : Prop :=
  match w with
  | nil => True
  | cons a w' => dans a X /\ Inmonoid X w'
  end.

Lemma i_I : forall (X : Ensf) (w : Word), inmonoid X w -> Inmonoid X w.
intros X w H.
elim H.
red in |- *; simpl in |- *; exact I.
intros.
change (dans e X /\ Inmonoid X w0) in |- *.
auto.
Qed.
Hint Resolve i_I.

Lemma I_i : forall (X : Ensf) (w : Word), Inmonoid X w -> inmonoid X w.
intros X.
simple induction w.
auto.
intros x w0 H H0.
cut (dans x X /\ Inmonoid X w0); auto.
intro H1; elim H1; clear H1.
auto.
Qed.
Hint Resolve I_i.

Lemma inmonoid_cons_inv :
 forall (X : Ensf) (w : Word) (a : Elt),
 inmonoid X (cons a w) -> inmonoid X w.
intros.
cut (Inmonoid X w); auto.
cut (Inmonoid X (cons a w)); auto.
intro H0.
cut (dans a X /\ Inmonoid X w); auto.
intro H1; elim H1; clear H1.
auto.
Qed.

Lemma inmonoid_cons_inv2 :
 forall (X : Ensf) (a : Elt) (w : Word), inmonoid X (cons a w) -> dans a X.
intros.
cut (Inmonoid X (cons a w)); auto.
intro.
cut (dans a X /\ Inmonoid X w); auto.
intro H1; elim H1; clear H1.
auto.
Qed.

Lemma inmonoid_inclus :
 forall (E F : Ensf) (x : Word), inclus E F -> inmonoid E x -> inmonoid F x.
intros E F x inclus_E_F inmonoid_E_x.
elim inmonoid_E_x.
        trivial.
 
        intros w e inmonoid_E_w inmonoid_F_w dans_e_E.
        apply inmonoid_cons; [ assumption | apply inclus_E_F; assumption ].
Qed.


(*									*)
(*  Concatenation de 2 mots : 						*)
(*    (Append w1 w2) est la concatenation de w1 et w2			*)
(*    (append w1 w2 w3) est la proposition "w3 est la conc.de w1 et w2"	*)
(*									*)

(*
Fixpoint Append [w1:Word] : Word -> Word :=
  [w2:Word]
    (<Word>Case w1 of
	(* nil  *) w2
	(* cons *) [a:Elt][w3:Word](cons a (Append w3 w2))
    end ).
*)
Fixpoint Append (w1 : Word) : Word -> Word :=
  fun w2 : Word =>
  match w1 with
  | nil => w2
  | cons a w3 => cons a (Append w3 w2)
  end.

Lemma Append_w_nil : forall w : Word, Append w nil = w :>Word.
simple induction w.
auto.
intros x w0 H.
replace (Append (cons x w0) nil) with (cons x (Append w0 nil)); auto.
rewrite H; auto.
Qed.

Inductive append : Word -> Word -> Word -> Prop :=
  | append_nil : forall w : Word, append nil w w
  | append_cons :
      forall (w1 w2 w3 : Word) (a : Elt),
      append w1 w2 w3 -> append (cons a w1) w2 (cons a w3).


(*  Lemmes sur inmonoid et Append...					*)

Lemma Append_inmonoid_g :
 forall (X : Ensf) (w1 w2 : Word), inmonoid X (Append w1 w2) -> inmonoid X w1.
intros X.
simple induction w1.
auto.
intros x w H w2.
replace (Append (cons x w) w2) with (cons x (Append w w2)); auto.
intro.
apply inmonoid_cons.
apply (H w2).
apply inmonoid_cons_inv with x; auto.
apply inmonoid_cons_inv2 with (Append w w2); auto.
Qed.

Lemma Append_inmonoid_d :
 forall (X : Ensf) (w1 w2 : Word), inmonoid X (Append w1 w2) -> inmonoid X w2.
intros X.
simple induction w1.
auto.
intros x w H w2.
replace (Append (cons x w) w2) with (cons x (Append w w2)); auto.
intro.
apply (H w2).
apply inmonoid_cons_inv with x; auto.
Qed.

Lemma inmonoid_Append :
 forall (X : Ensf) (w1 w2 : Word),
 inmonoid X w1 -> inmonoid X w2 -> inmonoid X (Append w1 w2).
intros X.
simple induction w1.
auto.
intros x w H w2 H0 H1.
replace (Append (cons x w) w2) with (cons x (Append w w2)); auto.
apply inmonoid_cons.
apply (H w2); auto.
apply inmonoid_cons_inv with x; auto.
apply inmonoid_cons_inv2 with w; auto.
Qed.


(*									*)
(*  On definit tout d'abord le type wordset, qui est Word->Prop		*)
(*  et qui definit un ensemble de mots par sa fonction caracteristique.	*)
(*  									*)
(*  L'egalite de 2 wordset est definie comme la double implication.	*)
(*									*)


Definition wordset := Word -> Prop.

Definition eqwordset (l1 l2 : wordset) : Prop :=
  forall w : Word, (l1 w -> l2 w) /\ (l2 w -> l1 w).

Lemma eqwordset_refl : forall L : wordset, eqwordset L L.
red in |- *.
auto.
Qed.

Lemma eqwordset_sym :
 forall l1 l2 : wordset, eqwordset l1 l2 -> eqwordset l2 l1.
unfold eqwordset in |- *.
intros.
elim (H w); clear H; intros; auto.
Qed.

Lemma eqwordset_trans :
 forall l1 l2 l3 : wordset,
 eqwordset l1 l2 -> eqwordset l2 l3 -> eqwordset l1 l3.
unfold eqwordset in |- *.
intros.
elim (H0 w); clear H0; intros.
elim (H w); clear H; intros.
auto.
Qed.

(*									*)
(*  Le predicat islangage, defini sur les wordset, dit simplement	*)
(*  que les mots du wordset sont sur l'alphabet alph.			*)
(*									*)

Definition islanguage (X : Ensf) (L : wordset) : Prop :=
  forall w : Word, L w -> inmonoid X w.


(*									*)
(*  Extension aux mots d'une fonction definie sur les elements		*)
(*									*)

(*
Fixpoint Word_ext [f : Elt -> Elt; w:Word] : Word :=
  (<Word>Case w of
	(* nil  *) nil
	(* cons *) [a:Elt][w':Word](cons (f a) (Word_ext f w'))
   end ).
*)
Fixpoint Word_ext (f : Elt -> Elt) (w : Word) {struct w} : Word :=
  match w with
  | nil => nil
  | cons a w' => cons (f a) (Word_ext f w')
  end.

Lemma inmonoid_map :
 forall (f : Elt -> Elt) (a : Ensf) (w : Word),
 inmonoid a w -> inmonoid (map f a) (Word_ext f w).
intros.
elim H; [ unfold Word_ext in |- *; auto | idtac ].
intros; unfold Word_ext in |- *; simpl in |- *.
apply inmonoid_cons; try apply dans_map_inv; auto.
Qed.
Hint Resolve inmonoid_map.

(*  Un petit lemme bien utile par la suite...				*)

Lemma cons_cons :
 forall (x1 x2 : Elt) (w1 w2 : Word),
 x1 = x2 :>Elt -> w1 = w2 :>Word -> cons x1 w1 = cons x2 w2 :>Word.
intros.
rewrite H0.
rewrite H.
auto.
Qed.
Hint Resolve cons_cons.

Definition fun_consaw_a (w : Word) : Elt :=
  match w return Elt with
  | nil =>
      (* nil  *)  zero
      (* cons *) 
  | cons a w' => a
  end.

Definition fun_consaw_w (w : Word) : Word :=
  match w return Word with
  | nil =>
      (* nil  *)  nil
      (* cons *) 
  | cons a w' => w'
  end.

Lemma cons_cons_inv :
 forall (x1 x2 : Elt) (w1 w2 : Word),
 cons x1 w1 = cons x2 w2 -> x1 = x2 /\ w1 = w2.
intros.
split.
replace x1 with (fun_consaw_a (cons x1 w1)); auto.
replace x2 with (fun_consaw_a (cons x2 w2)); auto.
apply (f_equal (A:=Word) (B:=Elt)); auto.
replace w1 with (fun_consaw_w (cons x1 w1)); auto.
replace w2 with (fun_consaw_w (cons x2 w2)); auto.
apply (f_equal (A:=Word) (B:=Word)); auto.
Qed.

Hint Resolve cons_cons_inv.

Lemma cons_cons_inv1 :
 forall (x1 x2 : Elt) (w1 w2 : Word),
 cons x1 w1 = cons x2 w2 :>Word -> x1 = x2 :>Elt.
intros.
cut (x1 = x2 :>Elt /\ w1 = w2 :>Word); [ intuition | auto ].
Qed.


Lemma cons_cons_inv2 :
 forall (x1 x2 : Elt) (w1 w2 : Word), cons x1 w1 = cons x2 w2 -> w1 = w2.
intros.
cut (x1 = x2 /\ w1 = w2); [ intuition | auto ].
Qed.


(*									*)
(*  Un mot est soit nil, soit de la forme (cons x w0).			*)
(*									*)

Lemma nil_or_cons :
 forall w : Word,
 w = nil \/ (exists x : Elt, (exists w0 : Word, w = cons x w0)).
simple induction w.

left; auto.

intros x w0 H.
right.
exists x.
exists w0.
auto.
Qed.