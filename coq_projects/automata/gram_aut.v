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
(*                                gram_aut.v                                *)
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
Require Import Relations.

Require Import gram.
Require Import gram_g.
Require Import PushdownAutomata.


Section APD.

Variable X V R : Ensf.
Variable S' : Elt.

Hypothesis Gram : isGram X V R S'.

Lemma Regles_X_V_R : Regles X V R.
apply isGram4 with S'.
exact Gram.
Qed.

Let P := union X V.

Let f_R_d (a : Elt) :=
  couple (word (cons (first a) nil)) (couple (eps X) (second a)).

Let f_X_d (x : Elt) := couple (word (cons x nil)) (couple x (word nil)).

Let d := union (map f_R_d R) (map f_X_d X).

Let wd := cons S' nil.

Let wa := nil.

Lemma Trans : Transition X P d.
red in |- *.
intros x dans_x_d.
elimtype (dans x (map f_R_d R) \/ dans x (map f_X_d X)).
intros dans_x.

elimtype (exists y : Elt, dans y R /\ x = f_R_d y).
intros y temp; elim temp; clear temp.
unfold f_R_d in |- *.
intros dans_y_R eg_x_f_y.
exists (cons (first y) nil).
apply inmonoid_cons.
trivial.
elim (Regles_X_V_R y dans_y_R).
intros f_y dans_f_y_V temp; elim temp; clear temp.
intros u eg_y inmono_u.
rewrite eg_y.
unfold first in |- *.
unfold P in |- *.
auto.
exists (eps X).
auto.
exists (word_inv (second y)).
elim (Regles_X_V_R y dans_y_R).
intros f_y dans_f_y_V temp; elim temp; clear temp.
intros u eg_y inmono_u.
rewrite eg_y.
unfold second in |- *.
unfold word_inv in |- *.
assumption.

elim (Regles_X_V_R y dans_y_R).
intros f_y dans_f_y_V temp; elim temp; clear temp.
intros u eg_y inmono_u.

replace (word (word_inv (second y))) with (second y).
assumption.
replace (second y) with (word u).
apply refl_equal.
rewrite eg_y.
apply refl_equal.

apply dans_map.
assumption.

intros dans_x.
elimtype (exists y : Elt, dans y X /\ x = f_X_d y).
intros y temp; elim temp; clear temp.
unfold f_X_d in |- *.
intros dans_y_X eg_x_f_y.
exists (cons y nil).
apply inmonoid_cons.
trivial.
unfold P in |- *.
auto.

exists y.
auto.
exists nil.
trivial.
assumption.

apply dans_map.
assumption.

auto.
Qed.


Lemma X_P_wd_wa_d : P_automata X P wd wa d.
red in |- *.
split.
unfold wd in |- *.
apply inmonoid_cons.
trivial.
unfold P in |- *.
apply union_d.
apply isGram3 with X R.
exact Gram.
split.
apply inmonoid_nil.
exact Trans.
Qed.

Lemma cut_spec :
 forall u : Word,
 {a : Word & 
 {b : Word |
 inmonoid X a /\
 Append a b = u /\
 (b = nil \/
  ex2 (fun x : Elt => ~ dans x X)
    (fun x : Elt => exists w : Word, b = cons x w))}}.
intro u.
pattern u in |- *.
apply Word_rec.

exists nil.
exists nil.
auto.

intros x w Hyp.
elim Hyp.
intros a' spec; elim spec.
intros b' temp; elim temp; clear temp.
intros inmonoid_a' temp; elim temp; clear temp.
intros spec_App spec_or.
elimtype ({dans x X} + {~ dans x X}).
intro dans_x_X.
exists (cons x a').
exists b'.
split.
apply inmonoid_cons; assumption.
split.
unfold Append in |- *.
simpl in |- *.
auto.

elim spec_or; intro; assumption.
intro N_dans_x_X.
exists nil.
exists (cons x w).
split.
auto.
split.
auto.
apply or_intror.
exists x.
assumption.
exists w.
apply refl_equal.
exact (Dans_spec x X).
Qed.

Definition cut (u : Word) :=
  let (a, s) := cut_spec u in (a, let (b, s2) := s in b).




Definition cut1 (u : Word) := fst (cut u).
Definition cut2 (u : Word) := snd (cut u).

Lemma cut_unicite :
 forall u a b a' b' : Word,
 inmonoid X a /\
 Append a b = u /\
 (b = nil \/
  ex2 (fun x : Elt => ~ dans x X)
    (fun x : Elt => exists w : Word, b = cons x w)) ->
 inmonoid X a' /\
 Append a' b' = u /\
 (b' = nil \/
  ex2 (fun x : Elt => ~ dans x X)
    (fun x : Elt => exists w : Word, b' = cons x w)) -> 
 a = a'.
intros u a b a' b' temp1 temp2; elim temp1; elim temp2; clear temp1;
 clear temp2.
intros inmon temp inmon' temp'; elim temp; elim temp'; clear temp;
 clear temp'.
intros App spec_or App' spec_or'.
elimtype
 (exists w : Word,
    a = Append a' w /\ b' = Append w b \/ a' = Append a w /\ b = Append w b').
intros x temp; elim temp; clear temp.
pattern a' at 2 in |- *.
replace a' with (Append a' nil).
generalize x; clear x; simple induction x.

intro temp; elim temp.
auto.

intros x0 w Hyp temp; elim temp; clear temp.
intros a_eg b'_eg.
absurd (dans x0 X).
elim spec_or'.
rewrite b'_eg.
intro cons_nil.
absurd (cons x0 (Append w b) = nil).
discriminate.
assumption.
intro temp; elim temp; clear temp.
intros x1 N_dans_x1 temp; elim temp; clear temp.
intros w' b'_eg_2.
replace x0 with x1.
assumption.
apply cons_cons_inv1 with w' (Append w b).
rewrite <- b'_eg_2.
assumption.
apply inmonoid_cons_inv2 with w.
apply inmonoid_Append_inv2 with a'.
rewrite <- a_eg.
assumption.
apply Append_w_nil.

pattern a at 2 in |- *.
replace a with (Append a nil).
generalize x; clear x; simple induction x.

intro temp; elim temp.
auto.

intros x0 w Hyp temp; elim temp; clear temp.
intros a'_eg b_eg.
absurd (dans x0 X).
elim spec_or.
rewrite b_eg.
intro cons_nil.
absurd (cons x0 (Append w b') = nil).
discriminate.
assumption.
intro temp; elim temp; clear temp.
intros x1 N_dans_x1 temp; elim temp; clear temp.
intros w' b_eg_2.
replace x0 with x1.
assumption.
apply cons_cons_inv1 with w' (Append w b').
rewrite <- b_eg_2.
assumption.
apply inmonoid_cons_inv2 with w.
apply inmonoid_Append_inv2 with a.
rewrite <- a'_eg.
assumption.
apply Append_w_nil.
apply Append_Append.
rewrite App'; assumption.
Qed.


Lemma inmonoid_cut1 : forall w : Word, inmonoid X (cut1 w).
intro w.
unfold cut1, cut in |- *.
elim (cut_spec w).
intros a temp; elim temp; clear temp.
intros b temp; elim temp; clear temp.
simpl in |- *; auto.
Qed.

Lemma cut_Append : forall w : Word, w = Append (cut1 w) (cut2 w).
intro w.
unfold cut1, cut2, cut in |- *.
elim (cut_spec w).
intros a temp; elim temp; clear temp.
intros b temp; elim temp; clear temp.
intros inm temp; elim temp.
simpl in |- *; auto.
Qed.

Lemma cut1_cons :
 forall (a : Elt) (w : Word), dans a X -> cut1 (cons a w) = cons a (cut1 w).
intros a w dans_a_X.
unfold cut1, cut in |- *.
elim (cut_spec w).
intros x temp; elim temp; clear temp.
intros b temp; elim temp; clear temp.
intros inmon_X_x temp; elim temp; clear temp.

elim (cut_spec (cons a w)).
intros x' temp; elim temp; clear temp.
intros b' temp; elim temp; clear temp.
intros inmon_X_x' temp; elim temp; clear temp.

intros App_eg' spec' App_eg spec.
simpl in |- *.

cut (inmonoid X x').
cut (Append x' b' = cons a w).

clear inmon_X_x' App_eg'.
generalize x'; clear x'; simple induction x'.

intro App_nil_b'_eg_cons_a_w.
absurd (dans a X).
elim spec'.
intro b'_nil.
absurd (cons a w = nil).
discriminate.
rewrite <- b'_nil.
rewrite <- App_nil_b'_eg_cons_a_w.
trivial.
intro temp; elim temp; clear temp.
intros x0 N_dans_x0_X temp; elim temp; clear temp.
intros w1 eg_b'_cons.
replace a with x0.
assumption.
apply cons_cons_inv1 with w1 w.
rewrite <- eg_b'_cons.
assumption.
assumption.

intros x0 w0 Hyp App_eg_cons inmon_cons.
apply cons_cons.
apply cons_cons_inv1 with (Append w0 b') w.
assumption.
apply cut_unicite with w b' b.
split.
apply inmonoid_cons_inv with x0; assumption.

split.
apply cons_cons_inv2 with x0 a.
assumption.
assumption.

split; auto.
assumption.
assumption.
Qed.


Lemma cut1_Append :
 forall u v : Word, inmonoid X u -> cut1 (Append u v) = Append u (cut1 v).
intros u v.
generalize u; clear u; simple induction u.
auto.
intros x w Hyp inmon_x_w.
replace (cut1 (Append (cons x w) v)) with (cons x (cut1 (Append w v))).
replace (Append (cons x w) (cut1 v)) with (cons x (Append w (cut1 v))).
apply cons_cons.
trivial.

apply Hyp.
apply inmonoid_cons_inv with x; assumption.

trivial.

apply sym_equal.
unfold Append in |- *.
simpl in |- *.
apply cut1_cons.
apply inmonoid_cons_inv2 with w.
trivial.
Qed.


Axiom
  cut2_cons :
    forall (A : Elt) (v : Word), dans A X -> cut2 (cons A v) = cut2 v.


Lemma cut2_cons_N :
 forall (A : Elt) (v : Word), ~ dans A X -> cut2 (cons A v) = cons A v.
intros A v N_dans_A_X.
unfold cut2, cut in |- *.
elim (cut_spec (cons A v)).
intros a temp; elim temp; clear temp.
intros b temp; elim temp; clear temp.
intros inmon_a temp; elim temp; clear temp.
intros App_eg spec_or.
cut (inmonoid X a).
cut (Append a b = cons A v).
clear App_eg inmon_a.
generalize a; clear a; simple induction a.
	auto.

	intros x w Hyp App_eg_x_w inmon.
	absurd (dans A X).
		assumption.

		replace A with x.
		apply inmonoid_cons_inv2 with w.
		assumption.
		apply cons_cons_inv1 with (Append w b) v.
		assumption.
assumption.
assumption.
Qed.

Lemma Deriveg_imp_Deriveg_cut :
 forall x y : Word,
 Deriveg X R x y ->
 ex2 (fun w : Word => Append (cut1 x) w = y)
   (fun w : Word => Deriveg X R (cut2 x) w).
intros x y Der.
elim Der.
intros.
replace (cut1 (cons A v)) with nil.
exists (Append u v).
trivial.
replace (cut2 (cons A v)) with (cons A v).
apply Deriveg1.
assumption.
apply sym_equal.
apply cut2_cons_N.
apply inter_dans with V.
apply sym_inter.
apply isGram2 with R S'.
exact Gram.
apply Regles_inv1 with X R (word u).
apply isGram4 with S'.
exact Gram.
assumption.

unfold cut1, cut in |- *.
elim (cut_spec (cons A v)).
intros a p.
elim p.
intros b temp; elim temp; clear temp.
intros inmon_a temp; elim temp; clear temp.

intros App_eg spec_or.

cut (inmonoid X a). (**)(*pour l'induction*)
cut (Append a b = cons A v). (***)(*pour l'induction*)
clear App_eg inmon_a p.
generalize a; clear a; simple induction a.

auto.

intros x0 w Hyp App inmon.
absurd (dans A X).

intros.
apply inter_dans with V.
apply sym_inter.
apply isGram2 with R S'.
exact Gram.

apply Regles_inv1 with X R (word u).
apply isGram4 with S'.
exact Gram.
assumption.

apply inmonoid_cons_inv2 with w.
replace A with x0.
assumption.
apply cons_cons_inv1 with (Append w b) v.
assumption.

assumption. (**)
assumption. (***)


intros u v x0 dans_x0_X Deriveg_X_R_u_v temp.
elim temp; clear temp.
intros w eg_App_cut Der_g_cut2.
exists w.
replace (cut1 (cons x0 u)) with (cons x0 (cut1 u)).
unfold Append in |- *.
simpl in |- *.
apply cons_cons; trivial.

apply sym_equal.
apply cut1_cons.
assumption.

replace (cut2 (cons x0 u)) with (cut2 u).
assumption.
apply sym_equal.
apply cut2_cons.
assumption.
Qed.

Lemma Deriveg_imp_Deriveg_App :
 forall x y : Word,
 Deriveg X R x y ->
 forall u v : Word,
 Append u v = x ->
 inmonoid X u ->
 ex2 (fun w : Word => Append u w = y) (fun w : Word => Deriveg X R v w).
intros x y Derg.
elim Derg.

intros u0 v0 A dans_A_u0_R u v eg_App.
elimtype (u = nil \/ (exists w : Word, (exists x : Elt, u = cons x w))).
intros u_eg.
exists (Append u0 v0).
rewrite u_eg.
trivial.
replace v with (cons A v0).
apply Deriveg1; assumption.
replace v with (Append u v).
auto.
rewrite u_eg.
trivial.
intro temp; elim temp; clear temp.
intros w temp; elim temp; clear temp.
intros x0 u_eg inmon_u.
absurd (dans x0 V).
apply inter_dans with X.
apply isGram2 with R S'.
exact Gram.
apply inmonoid_cons_inv2 with w.
rewrite <- u_eg.
assumption.
replace x0 with A.
apply Regles_inv1 with X R (word u0).
exact Regles_X_V_R.
assumption.
apply cons_cons_inv1 with v0 (Append w v).
change (cons A v0 = Append (cons x0 w) v) in |- *.
rewrite <- u_eg.
auto.

clear eg_App.
generalize u; clear u; simple induction u.

auto.

intros x0 w hyp.
apply or_intror.
exists w.
exists x0.
trivial.

intros u0 v0 x0 dans_x0_X Derg_u_v Hyp u v.
elimtype (u = nil \/ (exists w : Word, (exists x : Elt, u = cons x w))).
intro eg_u. 
rewrite eg_u.
intros App_eg inmon_nil.
exists (cons x0 v0).
trivial.
replace v with (cons x0 u0).
apply Deriveg2.
assumption.
assumption.
intro temp; elim temp; clear temp.
intros w temp; elim temp; clear temp.
intros x1 u_eg.
rewrite u_eg.
intros App_cons_eg inmonoid_X_cons_x1_w.
elimtype
 (ex2 (fun w1 : Word => Append w w1 = v0) (fun w1 : Word => Deriveg X R v w1)).
intros w0 App_eg Der_v_w0.
exists w0.
change (cons x1 (Append w w0) = cons x0 v0) in |- *.
apply cons_cons.
apply cons_cons_inv1 with (Append w v) u0.
assumption.
assumption.
assumption.
apply Hyp.
apply cons_cons_inv2 with x1 x0.
assumption.
apply inmonoid_cons_inv with x1.
assumption.

generalize u; clear u; simple induction u.
auto.
intros x2 w hyp.
apply or_intror.
exists w.
exists x2.
trivial.

Qed.


Lemma Derivegstar_imp_Der_inmon :
 forall x y : Word,
 Derivegstar X R x y ->
 forall u v : Word,
 Append u v = x ->
 inmonoid X u ->
 ex2 (fun w : Word => Append u w = y) (fun w : Word => Derivegstar X R v w).
unfold Derivegstar in |- *.
intros x y Der_star.
unfold Rstar in Der_star.
pattern x, y in |- *.
apply Der_star.

intros; exists v.
assumption.
apply Rstar_reflexive.


intros u v w Der_u_v Hyp u0 v0 App_eg inmon_u0.
elimtype
 (ex2 (fun w1 : Word => Append u0 w1 = v)
    (fun w1 : Word => Deriveg X R v0 w1)).
intros w0 App_eg_u0_w0 Deriveg_v0_x0.
elimtype
 (ex2 (fun w1 : Word => Append u0 w1 = w)
    (fun w1 : Word => Rstar Word (Deriveg X R) w0 w1)).
intros w1 App_eg_u0_w1_w Rstar_Der.
exists w1.
assumption.
apply Rstar_R with w0.
assumption.
assumption.
apply Hyp; assumption.
apply Deriveg_imp_Deriveg_App with u; assumption.
Qed.



Inductive Derive_P_A_2 : Conf -> Conf -> Prop :=
  | Derive_X :
      forall (w u : Word) (x : Elt),
      dans x X -> Derive_P_A_2 (cons x w, cons x u) (w, u)
  | Derive_V :
      forall (v w u : Word) (x : Elt),
      dans (couple x (word u)) R ->
      Derive_P_A_2 (cons x w, v) (Append u w, v).



Definition Derive_P_A_2_nind (x y : Conf) :=
  ex2 (fun a : Elt => dans a X)
    (fun a : Elt => fst x = cons a (fst y) /\ snd x = cons a (snd y)) \/
  (exists a : Elt,
     ex2 (fun w : Word => cons a w = fst x)
       (fun w : Word =>
        ex2 (fun u : Word => dans (couple a (word u)) R)
          (fun u : Word => Append u w = fst y))).


Lemma Derive_P_A_2_inv :
 forall x y : Conf, Derive_P_A_2 x y -> Derive_P_A_2_nind x y.
intros x y Der.
unfold Derive_P_A_2_nind in |- *.
elim Der.
intros w u x0 dans_x0_X.
apply or_introl.
exists x0; auto.

intros v w u x0 dans_couple_Der.
apply or_intror.
exists x0.
exists w.
auto.
exists u; auto.
Qed.


Definition Derivestar_P_A_2 := Rstar Conf Derive_P_A_2.

Lemma Der_cons_inv :
 forall (x : Elt) (u v : Word),
 dans x X ->
 Derivestar_P_A_2 (cons x u, v) (nil, nil) ->
 ex2 (fun v2 : Word => v = cons x v2)
   (fun v2 : Word => Derivestar_P_A_2 (u, v2) (nil, nil)).
intros x u v dans_x_X Der_star.
elimtype
 ((cons x u, v) = (nil, nil) \/
  ex2 (fun z : Conf => Derive_P_A_2 (cons x u, v) z)
    (fun z : Conf => Rstar (Word * Word) Derive_P_A_2 z (nil, nil))).
intro eg.
absurd (cons x u = nil).
discriminate.

change (fst (cons x u, v) = fst (nil, nil)) in |- *.
apply (f_equal (fst (A:=Word) (B:=Word))).
assumption.
intro temp; elim temp; clear temp; intros z Der Der_star_2.
cut (Derive_P_A_2_nind (cons x u, v) z).
unfold Derive_P_A_2_nind in |- *.
intro temp; elim temp; clear temp; intro temp; elim temp; clear temp.
simpl in |- *.
intros x0 dans_x0_X temp; elim temp; clear temp.
intros eg_cons_x_x0 eg_v_cons.
exists (snd z).
replace x with x0.
trivial.
apply cons_cons_inv1 with (fst z) u.
auto.
unfold Derivestar_P_A_2 in |- *.
replace u with (fst z).
cut (Rstar (Word * Word) Derive_P_A_2 z (nil, nil)).
elim z.
auto.
assumption.
apply cons_cons_inv2 with x0 x.
auto.

simpl in |- *.
intros x0 temp; elim temp; clear temp; intros w eg temp; elim temp;
 clear temp.
intros u0 dans_couple.
absurd (dans x0 V).
apply inter_dans with X.
exact (isGram2 X V R S' Gram).
replace x0 with x.
trivial.
apply cons_cons_inv1 with u w.
auto.
apply Regles_inv1 with X R (word u0).
exact Regles_X_V_R.
assumption.
apply Derive_P_A_2_inv.
assumption.
apply Rstar_inv.
assumption.
Qed.


Lemma Derive_P_A_2_imp_Der_P_A_2_App :
 forall x y : Word,
 Derivestar_P_A_2 (x, y) (nil, nil) ->
 forall u v : Word,
 Append u v = x ->
 inmonoid X u ->
 ex2 (fun w : Word => Append u w = y)
   (fun w : Word => Derivestar_P_A_2 (v, w) (nil, nil)).
unfold Derivestar_P_A_2 in |- *.
simple induction x.
intros y Der_P_A_2 u v.
elimtype (u = nil \/ (exists w : Word, (exists x : Elt, u = cons x w))).
intros u_eg.
rewrite u_eg.
intros App_eg inmon_nil.
exists y; auto.
replace v with nil; trivial.

intro temp; elim temp; clear temp; intros w temp; elim temp; clear temp.
intros x0 eg_u.
rewrite eg_u.
intros cons_eg_nil.
absurd (cons x0 (Append w v) = nil).
discriminate.
trivial.

generalize u; clear u; simple induction u.
auto.
intros x1 w1 Hyp; apply or_intror; exists w1; exists x1; trivial.

intros x0 w Hyp y Der_star_cons u v App_eg inmon_X.
elimtype (u = nil \/ (exists w : Word, (exists x : Elt, u = cons x w))).
intros u_eg.
rewrite u_eg.
replace v with (cons x0 w).
exists y; trivial.
replace v with (Append u v).
auto.
rewrite u_eg.
trivial.

intro temp; elim temp; clear temp; intros w1 temp; elim temp; clear temp.
intros x1 eg_u.
rewrite eg_u.
elimtype
 (ex2 (fun v2 : Word => y = cons x0 v2)
    (fun v2 : Word => Derivestar_P_A_2 (w, v2) (nil, nil))).
intros v2 y_eg Der_w_v2.
elimtype
 (ex2 (fun w : Word => Append w1 w = v2)
    (fun w : Word => Rstar Conf Derive_P_A_2 (v, w) (nil, nil))).
intros we App_w1_we_eg_v2 Rstar_Der.
exists we.
rewrite y_eg.
replace (Append (cons x1 w1) we) with (cons x1 (Append w1 we)).
apply cons_cons.
apply cons_cons_inv1 with (Append w1 v) w.
rewrite <- App_eg.
rewrite eg_u.
trivial.
trivial.
trivial.
trivial.

apply Hyp.
trivial.
apply cons_cons_inv2 with x1 x0.
rewrite <- App_eg.
rewrite eg_u.
trivial.
apply inmonoid_cons_inv with x1.
rewrite <- eg_u.
trivial.
apply Der_cons_inv.
replace x0 with x1.
apply inmonoid_cons_inv2 with w1.
rewrite <- eg_u.
trivial.
apply cons_cons_inv1 with (Append w1 v) w.
rewrite <- App_eg.
rewrite eg_u.
trivial.
assumption.

clear inmon_X App_eg.
generalize u; clear u; simple induction u.
auto.
intros x1 w1 tmp; apply or_intror; exists w1; exists x1; trivial.

Qed.


Lemma Derive_P_A_2_imp_Der_P_A_2_cons :
 forall (u : Elt) (x y : Word),
 Derivestar_P_A_2 (cons u x, y) (nil, nil) ->
 dans u X ->
 ex2 (fun w : Word => cons u w = y)
   (fun w : Word => Derivestar_P_A_2 (x, w) (nil, nil)).
intros.
elimtype
 (ex2 (fun w : Word => Append (cons u nil) w = y)
    (fun w : Word => Derivestar_P_A_2 (x, w) (nil, nil))).
intros w eg_App Der.
exists w; trivial.

apply Derive_P_A_2_imp_Der_P_A_2_App with (cons u x); auto.
Qed.


Lemma Derivestar_P_A_2_x :
 forall x : Word, inmonoid X x -> Derivestar_P_A_2 (x, x) (nil, nil).
unfold Derivestar_P_A_2 in |- *.
simple induction x.
intro.
apply Rstar_reflexive.
intros x0 w Hyp inmon.
apply Rstar_R with (w, w).
apply Derive_X.
apply inmonoid_cons_inv2 with w; assumption.

apply Hyp.
apply inmonoid_cons_inv with x0; assumption.
Qed.
Hint Resolve Derivestar_P_A_2_x.


Lemma Derivegstar_imp_Derivestar_P_A_2 :
 forall x y : Word,
 Derivegstar X R x y -> inmonoid X y -> Derivestar_P_A_2 (x, y) (nil, nil).
unfold Derivegstar, Rstar in |- *.
intros x y Der_star.
pattern x, y in |- *.
apply Der_star.
auto.

intros u v w Derg_u_v.
generalize w.
elim Derg_u_v.
intros u0 v0 A dans_couple w0 Hyp inmon_w0.
unfold Derivestar_P_A_2 in |- *.
apply Rstar_R with (Append u0 v0, w0).
apply Derive_V.
assumption.
apply Hyp; assumption.

intros u0 v0 x0 dans_x0_v0 Der_u0_v0 Hyp1 w0 Hyp2 inmon_w0.

elimtype
 (ex2 (fun v2 : Word => w0 = cons x0 v2)
    (fun v2 : Word => Derivestar_P_A_2 (v0, v2) (nil, nil))).
intros x1 w0_eg_cons Derivestar_v0_x1.
rewrite w0_eg_cons.
unfold Derivestar_P_A_2 in |- *.
apply Rstar_R with (u0, x1).
apply Derive_X.
assumption.
apply Hyp1.
auto.
apply inmonoid_cons_inv with x0.
rewrite <- w0_eg_cons.
assumption.

apply Der_cons_inv.
assumption.
exact (Hyp2 inmon_w0).
Qed.
Hint Resolve Derivegstar_imp_Derivestar_P_A_2.


(*equivalence de Derive_P_A_2 et Derive_P_A*)
(*premiere implication*)

Lemma Derive_P_A_2_imp_Derive_P_A :
 forall x y : Word * Word, Derive_P_A_2 x y -> Derive_P_A X d x y.
intros x y Der.
elim Der.
intros w u x0 dans_x0_X.
replace (cons x0 w) with (Append (cons x0 nil) w).
pattern w at 2 in |- *.
replace w with (Append nil w).
apply Derive_cons.
assumption.
unfold d in |- *.
apply union_d.
change (dans (f_X_d x0) (map f_X_d X)) in |- *.
apply dans_map_inv.
assumption.
trivial.
trivial.

intros v w u x0 dans_couple.
replace (cons x0 w) with (Append (cons x0 nil) w).
apply Derive_eps.
unfold d in |- *.
apply union_g.
replace (couple (word (cons x0 nil)) (couple (eps X) (word u))) with
 (f_R_d (couple x0 (word u))).
apply dans_map_inv.
assumption.
unfold f_R_d in |- *.
trivial.
trivial.
Qed.
Hint Resolve Derive_P_A_2_imp_Derive_P_A.

Lemma Derivestar_P_A_2_imp_Derivestar_P_A :
 forall x y : Word * Word, Derivestar_P_A_2 x y -> Derivestar_P_A X d x y.
unfold Derivestar_P_A_2, Rstar, Derivestar_P_A in |- *.
intros x y Rstar_Der.
pattern x, y in |- *.
apply Rstar_Der.
intros.
apply Rstar_reflexive.
intros u v w Hyp1 Hyp2.
apply Rstar_R with v; auto.
Qed.
Hint Resolve Derivestar_P_A_2_imp_Derivestar_P_A.


(*seconde implication*)

Lemma Derive_P_A_imp_Derive_P_A_2 :
 forall x y : Word * Word, Derive_P_A X d x y -> Derive_P_A_2 x y.
unfold d in |- *.
intros x y Der.
elim Der.
intros w w1 w2 u x0 dans_x0_X dans_couple_d.
elimtype
 (dans (couple (word w1) (couple x0 (word w2))) (map f_R_d R) \/
  dans (couple (word w1) (couple x0 (word w2))) (map f_X_d X)).
intros dans_couple.
absurd (dans (eps X) X).
apply not_dans_X_eps.
replace (eps X) with x0.
assumption.
elimtype
 (exists r : Elt,
    dans r R /\ couple (word w1) (couple x0 (word w2)) = f_R_d r).
intros r temp; elim temp; clear temp; intros dans_r_R.
unfold f_R_d in |- *.
intro eg.
apply couple_couple_inv1 with (word w2) (second r).
apply couple_couple_inv2 with (word w1) (word (cons (first r) nil)).
assumption.
apply dans_map.
assumption.

intros dans_couple.
elimtype
 (exists r : Elt,
    dans r X /\ couple (word w1) (couple x0 (word w2)) = f_X_d r).
intros r temp; elim temp; clear temp; intros dans_r_X eg.

replace w1 with (cons x0 nil).
replace w2 with nil.
simpl in |- *.
replace (Append nil w) with w.
replace (Append (cons x0 nil) w) with (cons x0 w).
apply Derive_X.
assumption.
trivial.
trivial.
apply word_word_inv.
apply couple_couple_inv2 with r x0.
apply couple_couple_inv2 with (word (cons r nil)) (word w1).
auto.
replace x0 with r.
apply word_word_inv.
apply couple_couple_inv1 with (couple r (word nil)) (couple x0 (word w2)).
auto.
apply couple_couple_inv1 with (word nil) (word w2).
apply couple_couple_inv2 with (word (cons r nil)) (word w1).
auto.

apply dans_map.
assumption.
auto.

unfold d in |- *.
intros w w1 w2 u dans_couple_d.
elimtype
 (dans (couple (word w1) (couple (eps X) (word w2))) (map f_R_d R) \/
  dans (couple (word w1) (couple (eps X) (word w2))) (map f_X_d X)).
intros dans_couple.
(*   Apply Derive_V.*)
elimtype
 (exists r : Elt,
    dans r R /\ couple (word w1) (couple (eps X) (word w2)) = f_R_d r).
intros r temp; elim temp; clear temp; intros dans_r_R eg.
replace w1 with (cons (first r) nil).
replace (Append (cons (first r) nil) w) with (cons (first r) w).
apply Derive_V.
replace (word w2) with (second r).
elimtype
 (ex2 (fun A : Elt => dans A V)
    (fun A : Elt =>
     ex2 (fun B : Word => r = couple A (word B))
       (fun B : Word => inmonoid (union X V) B))).
intros A dans_A_V temp; elim temp; clear temp; intros B eg_r inmon_B.
rewrite eg_r.
replace (first (couple A (word B))) with A.
replace (second (couple A (word B))) with (word B).
rewrite <- eg_r.
assumption.
trivial.
trivial.

apply Regles_X_V_R.
assumption.
apply couple_couple_inv2 with (eps X) (eps X).
apply couple_couple_inv2 with (word (cons (first r) nil)) (word w1).
auto.
trivial.
apply word_word_inv.
apply
 couple_couple_inv1
  with (couple (eps X) (second r)) (couple (eps X) (word w2)).
auto.
apply dans_map.
assumption.

intro dans_couple.
elimtype
 (exists r : Elt,
    dans r X /\ couple (word w1) (couple (eps X) (word w2)) = f_X_d r).
intros r temp; elim temp; clear temp; intros dans_r_X eg.
absurd (dans (eps X) X).
apply not_dans_X_eps.
replace (eps X) with r.
assumption.
apply couple_couple_inv1 with (word nil) (word w2).
apply couple_couple_inv2 with (word (cons r nil)) (word w1).
auto.
apply dans_map.
assumption.
auto.
Qed.
Hint Resolve Derive_P_A_imp_Derive_P_A_2.


Lemma Derivestar_P_A_imp_Derivestar_P_A_2 :
 forall x y : Word * Word, Derivestar_P_A X d x y -> Derivestar_P_A_2 x y.
unfold Derivestar_P_A, Rstar, Derivestar_P_A_2 in |- *.
intros x y Der_star.
pattern x, y in |- *.
apply Der_star.
intros.
apply Rstar_reflexive.
intros u v w Deri_u_v Rstar_v_w.
apply Rstar_R with v; auto.
Qed.

Hint Resolve Derivestar_P_A_imp_Derivestar_P_A_2.



(**************************************************************)
(*Tout mot reconnu par la grammaire est reconnu par l'automate*)
(**************************************************************)

Theorem Derivestar_imp_Derivestar_P_A :
 forall x y : Word,
 Derivestar R x y -> inmonoid X y -> Derivestar_P_A X d (x, y) (nil, nil).

auto.
Qed.
(**************************************************************)




Inductive Derive_P_A_3 : Word * Conf -> Word * Conf -> Prop :=
  | Derive3_X :
      forall (w u s : Word) (x : Elt),
      dans x X ->
      Derive_P_A_3 (s, (cons x w, cons x u)) (Append s (cons x nil), (w, u))
  | Derive3_V :
      forall (v w u s : Word) (x : Elt),
      dans (couple x (word u)) R ->
      Derive_P_A_3 (s, (cons x w, v)) (s, (Append u w, v)).


Definition Derivestar_P_A_3 := Rstar (Word * Conf) Derive_P_A_3.


Lemma Conserve_App_s_u :
 forall s1 s2 u1 u2 v1 v2 : Word,
 Derive_P_A_3 (s1, (u1, v1)) (s2, (u2, v2)) -> Append s1 v1 = Append s2 v2.
intros s1 s2 u1 u2 v1 v2 Derive_P_A_3_s1_v1_s2_v2.
change
  ((fun a b : Word * Conf =>
    Append (fst a) (snd (snd a)) = Append (fst b) (snd (snd b)))
     (s1, (u1, v1)) (s2, (u2, v2))) in |- *.

elim Derive_P_A_3_s1_v1_s2_v2; simpl in |- *.
intros w u s x dans_x_X.
replace (cons x u) with (Append (cons x nil) u); trivial.
auto.
Qed.


Lemma Derisvestar_P_A_3_conserve :
 forall s1 s2 u1 u2 v1 v2 : Word,
 Derivestar_P_A_3 (s1, (u1, v1)) (s2, (u2, v2)) ->
 Append s1 v1 = Append s2 v2.
unfold Derivestar_P_A_3, Rstar in |- *.
intros s1 s2 u1 u2 v1 v2 Derivestar_P_A_3_s1_v1_s2_v2.
change
  ((fun a b : Word * Conf =>
    Append (fst a) (snd (snd a)) = Append (fst b) (snd (snd b)))
     (s1, (u1, v1)) (s2, (u2, v2))) in |- *.

apply Derivestar_P_A_3_s1_v1_s2_v2.
trivial.
intros u v w.
elim u. intros uu1 uuc. elim uuc. intros uu2 uu3.
elim v. intros vv1 vvc. elim vvc. intros vv2 vv3.
simpl in |- *.
intros Der eg1.
rewrite <- eg1.
apply Conserve_App_s_u with uu2 vv2.
assumption.
Qed.


Lemma Derive_P_A_2_imp_Derive_P_A_3 :
 forall (s : Word) (x y : Conf),
 Derive_P_A_2 x y -> exists s2 : Word, Derive_P_A_3 (s, x) (s2, y).
intros s x y Derive_P_A_2_x_y.
elim Derive_P_A_2_x_y.
intros w u x0 dans_x0_X.
exists (Append s (cons x0 nil)).
apply Derive3_X; assumption.

intros v w u x0 dans_couple.
intros; exists s.
apply Derive3_V; assumption.
Qed.


Lemma Derivestar_P_A_2_imp_Derivestar_P_A_3 :
 forall x y : Conf,
 Derivestar_P_A_2 x y ->
 forall s : Word, exists s2 : Word, Derivestar_P_A_3 (s, x) (s2, y).
unfold Derivestar_P_A_2, Rstar, Derivestar_P_A_3 in |- *.
intros x y Der_star.
pattern x, y in |- *.
apply Der_star.
intros; exists s.
apply Rstar_reflexive.

intros u v w Der_u_v Ex_v_w s.
elimtype (exists s2 : Word, Derive_P_A_3 (s, u) (s2, v)).
intros s1 Der_3_s_u_s1_v.
elim (Ex_v_w s1).
intros s2 Rstar_s1_v_s2_w.
exists s2.
apply Rstar_R with (s1, v); trivial.
apply Derive_P_A_2_imp_Derive_P_A_3; assumption.
Qed.


Lemma Deriveg_imp_Deriveg_App_2 :
 forall x y a : Word,
 inmonoid X a -> Deriveg X R x y -> Deriveg X R (Append a x) (Append a y).
intros x y.
simple induction a.
auto.

intros x0 w Hyp inmonoid_X_cons_x0_w Der_x_y.
change (Deriveg X R (cons x0 (Append w x)) (cons x0 (Append w y))) in |- *.
apply Deriveg2.
apply inmonoid_cons_inv2 with w; assumption.
apply Hyp.
apply inmonoid_cons_inv with x0; assumption.
assumption.
Qed.


Lemma Derive_P_A_3_imp_Derivegstar :
 forall x y x' y' s s' : Word,
 Derive_P_A_3 (s, (x, y)) (s', (x', y')) ->
 inmonoid X s -> Derivegstar X R (Append s x) (Append s' x').
intros x y x' y' s s' Der.
change
  ((fun a a' : Word * Conf =>
    inmonoid X (fst a) ->
    Derivegstar X R (Append (fst a) (fst (snd a)))
      (Append (fst a') (fst (snd a')))) (s, (x, y)) 
     (s', (x', y'))) in |- *.

unfold Derivegstar in |- *.
elim Der; simpl in |- *.
intros w u s0 x0 dans_x0_X inmon_s.
replace (Append (Append s0 (cons x0 nil)) w) with
 (Append s0 (Append (cons x0 nil) w)).
apply Rstar_reflexive.
auto.

intros v w u s0 x0 dans_couple_x0_u_R inmon_s.
apply Rstar_R with (Append s0 (Append u w)).
apply Deriveg_imp_Deriveg_App_2.
assumption.
apply Deriveg1.
assumption.
apply Rstar_reflexive.
Qed.


Lemma Derive_P_A_3_conserve_inmonoid_s :
 forall x y x' y' s s' : Word,
 Derive_P_A_3 (s, (x, y)) (s', (x', y')) -> inmonoid X s -> inmonoid X s'.
intros x y x' y' s s' Der.
change
  ((fun a a' : Word * Conf => inmonoid X (fst a) -> inmonoid X (fst a'))
     (s, (x, y)) (s', (x', y'))) in |- *.

elim Der; simpl in |- *.
intros.
apply inmonoid_Append; auto.
auto.
Qed.


Lemma Derivestar_P_A_3_imp_Derivegstar :
 forall x y x' y' s s' : Word,
 Derivestar_P_A_3 (s, (x, y)) (s', (x', y')) ->
 inmonoid X s -> Derivegstar X R (Append s x) (Append s' x').
unfold Derivestar_P_A_3, Rstar in |- *.
intros x y x' y' s s' Der_star.
change
  ((fun a a' : Word * Conf =>
    inmonoid X (fst a) ->
    Derivegstar X R (Append (fst a) (fst (snd a)))
      (Append (fst a') (fst (snd a')))) (s, (x, y)) 
     (s', (x', y'))) in |- *.

apply Der_star; unfold Derivegstar in |- *.

intros.
apply Rstar_reflexive.

intros u v w.
elim u. intros u1 uc. elim uc. intros u2 u3.
elim v. intros v1 vc. elim vc. intros v2 v3.
simpl in |- *.
intros Der_3_u_v Hyp inmon_u1.
apply Rstar_transitive with (Append v1 v2). 
change (Derivegstar X R (Append u1 u2) (Append v1 v2)) in |- *.
apply Derive_P_A_3_imp_Derivegstar with u3 v3.
assumption.
assumption.
apply Hyp.
apply Derive_P_A_3_conserve_inmonoid_s with u2 u3 v2 v3 u1.
assumption.
assumption.
Qed.


(*Tout mot reconnu par l'automate est reconnu par la grammaire*)

Theorem Derivestar_P_A_imp_Derivestar :
 forall x y : Word, Derivestar_P_A X d (x, y) (nil, nil) -> Derivestar R x y.
intros x y Derivestar_P_A_x_y_nil_nil.
elimtype (exists s2 : Word, Derivestar_P_A_3 (nil, (x, y)) (s2, (nil, nil))).
intros s2 Derivestar_P_A_3_x_y.
apply Derivegstar_Derivestar with X.
replace x with (Append nil x).
replace y with (Append s2 nil).
apply Derivestar_P_A_3_imp_Derivegstar with y nil.
assumption.
trivial.
replace y with (Append nil y).
apply sym_equal.
apply Derisvestar_P_A_3_conserve with x nil.
assumption.
trivial.
trivial.

apply Derivestar_P_A_2_imp_Derivestar_P_A_3.
auto.
Qed.

Hint Resolve Derivestar_P_A_imp_Derivestar.



(******************************************)
(*equivalence de G et de l'automate a pile*)
(******************************************)

Theorem equiv_APD_Gram : l_egal (LA X wd wa d) (LG X V R S').
red in |- *.
unfold l_inclus, LA, LG in |- *.
split.
intros w temp; elim temp; intros Der inmon.
auto.
intros w temp; elim temp; intros Der inmon.
auto.
Qed.


End APD.