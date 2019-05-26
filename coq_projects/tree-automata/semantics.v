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


Require Import Bool.
Require Import Arith.
Require Import Classical_Prop.
From IntMap Require Import Allmaps.
Require Import bases.
Require Import defs.

Unset Standard Proposition Elimination Names.

(* fonction définissant la sémantique : reconnaissance d'un terme par un automate *)

Fixpoint rec_term (d : preDTA) (a : ad) (t : term) 
 (n : nat) {struct n} : bool :=
  match n with
  | O => false
  | S k =>
      match t with
      | app c l =>
          match MapGet _ d a with
          | None => false
          | Some lts =>
              match MapGet _ lts c with
              | None => false
              | Some pre => rec_list_terms d pre l k
              end
          end
      end
  end
 
 with rec_list_terms (d : preDTA) (pre : prec_list) 
 (l : term_list) (n : nat) {struct n} : bool :=
  match n with
  | O => false
  | S k =>
      match pre with
      | prec_empty => match l with
                      | tnil => true
                      | _ => false
                      end
      | prec_cons st stp pre' =>
          match l with
          | tnil => false
          | tcons hd tl =>
              rec_list_terms d pre' l k
              || rec_term d st hd k && rec_list_terms d stp tl k
          end
      end
  end.

(* bornes sur l'entier décroissant (terminaison de la fonction reconnaissance *)

Lemma borne_0_0 :
 forall p : prec_list,
 prec_in_state (M0 prec_list) p -> taille_0 p <= taille_1 (M0 prec_list).
Proof.
	intros. elim (prec_in_state_M0_false p). assumption.
Qed.

Lemma borne_0_1 :
 forall (a : ad) (p' p : prec_list),
 prec_in_state (M1 prec_list a p') p ->
 taille_0 p <= taille_1 (M1 prec_list a p').
Proof.
	intros. cut (p = p'). intros. simpl in |- *. rewrite H0.
	exact (le_n_n (taille_0 p')).
	unfold prec_in_state in H.
	exact (in_M1_id prec_list p a p' H).
Qed.

Lemma borne_0_2 :
 forall (m0 m1 : Map prec_list) (p : prec_list),
 (prec_in_state m0 p -> taille_0 p <= taille_1 m0) ->
 (prec_in_state m1 p -> taille_0 p <= taille_1 m1) ->
 prec_in_state (M2 prec_list m0 m1) p ->
 taille_0 p <= taille_1 (M2 prec_list m0 m1).
Proof.
	intros. cut (prec_in_state m0 p \/ prec_in_state m1 p).
	intro. elim H2; intros. simpl in |- *. cut (taille_0 p <= taille_1 m0).
	intro. cut (taille_1 m0 <= max (taille_1 m0) (taille_1 m1)).
	intro. exact
  (le_trans (taille_0 p) (taille_1 m0) (max (taille_1 m0) (taille_1 m1)) H4
     H5).
	exact (le_max_l (taille_1 m0) (taille_1 m1)).
	exact (H H3).
	simpl in |- *. cut (taille_0 p <= taille_1 m1). 
	cut (taille_1 m1 <= max (taille_1 m0) (taille_1 m1)). intros.
	exact
  (le_trans (taille_0 p) (taille_1 m1) (max (taille_1 m0) (taille_1 m1)) H5
     H4).
	exact (le_max_r (taille_1 m0) (taille_1 m1)).
	exact (H0 H3).
	unfold prec_in_state in |- *. unfold prec_in_state in H1.
	exact (in_M2_disj prec_list p m0 m1 H1).
Qed.

Lemma borne_0 :
 forall (s : state) (p : prec_list),
 prec_in_state s p -> taille_0 p <= taille_1 s.
Proof.
	simple induction s. intros. exact (borne_0_0 p H).
	intros. exact (borne_0_1 a a0 p H).
	intros. exact (borne_0_2 m m0 p (H p) (H0 p) H1).
Qed.

Lemma borne_1_0 :
 forall s : state,
 state_in_dta (M0 state) s -> taille_1 s <= DTA_taille (M0 state).
Proof.
	intros. elim (state_in_dta_M0_false s). assumption.
Qed.

Lemma borne_1_1 :
 forall (a : ad) (s' s : state),
 state_in_dta (M1 state a s') s -> taille_1 s <= DTA_taille (M1 state a s').
Proof.
	intros. cut (s = s'). intros. simpl in |- *. rewrite H0.
	exact (le_n_n (taille_1 s')).
	unfold state_in_dta in H.
	exact (in_M1_id state s a s' H).
Qed.

Lemma borne_1_2 :
 forall (m0 m1 : Map state) (s : state),
 (state_in_dta m0 s -> taille_1 s <= DTA_taille m0) ->
 (state_in_dta m1 s -> taille_1 s <= DTA_taille m1) ->
 state_in_dta (M2 state m0 m1) s -> taille_1 s <= DTA_taille (M2 state m0 m1).
Proof.
	intros. cut (state_in_dta m0 s \/ state_in_dta m1 s).
	intro. elim H2; intros. simpl in |- *. cut (taille_1 s <= DTA_taille m0).
	intro. cut (DTA_taille m0 <= max (DTA_taille m0) (DTA_taille m1)).
	intro. exact
  (le_trans (taille_1 s) (DTA_taille m0)
     (max (DTA_taille m0) (DTA_taille m1)) H4 H5).
	exact (le_max_l (DTA_taille m0) (DTA_taille m1)).
	exact (H H3).
	simpl in |- *. cut (taille_1 s <= DTA_taille m1). 
	cut (DTA_taille m1 <= max (DTA_taille m0) (DTA_taille m1)). intros.
	exact
  (le_trans (taille_1 s) (DTA_taille m1)
     (max (DTA_taille m0) (DTA_taille m1)) H5 H4).
	exact (le_max_r (DTA_taille m0) (DTA_taille m1)).
	exact (H0 H3).
	unfold state_in_dta in |- *. unfold state_in_dta in H1.
	exact (in_M2_disj state s m0 m1 H1).
Qed.

Lemma borne_1 :
 forall (d : preDTA) (s : state),
 state_in_dta d s -> taille_1 s <= DTA_taille d.
Proof.
	simple induction d. intros. exact (borne_1_0 s H).
	intros. exact (borne_1_1 a a0 s H).
	intros. exact (borne_1_2 m m0 s (H s) (H0 s) H1).
Qed.

Lemma borne_2 :
 forall (d : preDTA) (p : prec_list),
 prec_in_dta d p -> taille_0 p <= DTA_taille d.
Proof.
	intros. unfold prec_in_dta in H. elim H. intros. elim H0.
	intros. elim H1. intros. elim H2. intros. 
	cut (taille_0 p <= taille_1 x).
	cut (taille_1 x <= DTA_taille d). intros.
	exact (le_trans (taille_0 p) (taille_1 x) (DTA_taille d) H6 H5).
	apply (borne_1 d x). unfold state_in_dta in |- *. split with x0.
	assumption.
	apply (borne_0 x p). unfold prec_in_state in |- *. split with x1.
	assumption.
Qed.

(* définition de la quantité d'essence (Astuce de Boyer, définition de *)
(* la reconnaissance par fixpoint...) *)

Definition essence (t : term) (d : preDTA) : nat :=
  S (term_high t) * S (DTA_taille d).

(* "hauteur" d'une liste : term_high_0 *)

Definition essence_list (l : term_list) (d : preDTA) 
  (pl : prec_list) : nat :=
  match l, pl with
  | tnil, _ => 1
  | _, prec_empty => 1
  | _, prec_cons a la ls =>
      taille_0 pl + S (term_high_0 l) * S (DTA_taille d)
  end.

(* lemmes concernant la gestion de la diminution de la quantité d'essence *)

Lemma conservation_0_0 : forall n n0 : nat, S n * S n0 = S (n0 + n * S n0).
Proof.
	simple induction n. simpl in |- *. trivial.
	intros. simpl in |- *. trivial.
Qed.

Lemma conservation_0 :
 forall (d : preDTA) (p : prec_list) (c : ad) (l : term_list),
 prec_in_dta d p -> S (essence_list l d p) <= essence (app c l) d.
Proof.
	intro. intro. intro. simple induction l. intros. unfold essence_list in |- *. unfold essence in |- *.
	case p. intros. cut (2 <= S (term_high (app c tnil))).
	cut (1 <= S (DTA_taille d)). intros.
	exact
  (le_mult_mult 2 (S (term_high (app c tnil))) 1 (S (DTA_taille d)) H1 H0).
	exact (le_n_S 0 (DTA_taille d) (le_O_n (DTA_taille d))).
	cut (1 <= term_high (app c tnil)). intro.
	exact (le_n_S 1 (term_high (app c tnil)) H0).
	simpl in |- *. exact (le_n_n 1).
	intros. cut (2 <= S (term_high (app c tnil))). cut (1 <= S (DTA_taille d)).
	intros. exact
  (le_mult_mult 2 (S (term_high (app c tnil))) 1 (S (DTA_taille d)) H1 H0).
	exact (le_n_S 0 (DTA_taille d) (le_O_n (DTA_taille d))).
	cut (1 <= term_high (app c tnil)). intro. exact (le_n_S 1 (term_high (app c tnil)) H0).
	simpl in |- *. exact (le_n_n 1).
	case p. intros. unfold essence in |- *. unfold essence_list in |- *.
	cut
  (S (term_high (app c (tcons t t0))) * S (DTA_taille d) =
   S (DTA_taille d + term_high (app c (tcons t t0)) * S (DTA_taille d))).
	intro. rewrite H1.
	cut
  (taille_0 (prec_cons a p0 p1) +
   S (term_high_0 (tcons t t0)) * S (DTA_taille d) <=
   DTA_taille d + term_high (app c (tcons t t0)) * S (DTA_taille d)).
	intro. exact (le_n_S _ _ H2).
	cut (taille_0 (prec_cons a p0 p1) <= DTA_taille d).
	cut
  (S (term_high_0 (tcons t t0)) * S (DTA_taille d) <=
   term_high (app c (tcons t t0)) * S (DTA_taille d)).
	intros. exact (plus_le_compat _ _ _ _ H3 H2).
	cut (S (term_high_0 (tcons t t0)) <= term_high (app c (tcons t t0))).
	intro. exact (le_mult_l _ _ _ H2).
	cut (S (term_high_0 (tcons t t0)) = term_high (app c (tcons t t0))). intro.
	exact (high_aux_0 c (tcons t t0)).
	exact (high_aux_1 c (tcons t t0)).
	exact (borne_2 d (prec_cons a p0 p1) H0).
	exact (conservation_0_0 (term_high (app c (tcons t t0))) (DTA_taille d)).
	intros. unfold essence_list in |- *. unfold essence in |- *. 
	cut (2 <= S (term_high (app c (tcons t t0)))).
	cut (1 <= S (DTA_taille d)). intros.
	exact
  (le_mult_mult 2 (S (term_high (app c (tcons t t0)))) 1 
     (S (DTA_taille d)) H2 H1).
	exact (le_n_S 0 (DTA_taille d) (le_O_n (DTA_taille d))).
	apply (le_n_S 1 (term_high (app c (tcons t t0)))).
	cut (1 <= S (term_high_0 (tcons t t0))).
	cut (S (term_high_0 (tcons t t0)) <= term_high (app c (tcons t t0))).
	intros. exact
  (le_trans 1 (S (term_high_0 (tcons t t0))) (term_high (app c (tcons t t0)))
     H2 H1).
	exact (high_aux_0 c (tcons t t0)). apply (le_n_S 0 (term_high_0 (tcons t t0))).
	exact (le_O_n _).
Qed.

Lemma conservation_1 :
 forall (d : preDTA) (l : term_list), 1 <= essence_list l d prec_empty.
Proof.
	intros. induction  l as [| t l Hrecl]. simpl in |- *. exact (le_n_n 1).
	simpl in |- *. exact (le_n_n 1).
Qed.

Lemma conservation_2 :
 forall (d : preDTA) (p : prec_list), 1 <= essence_list tnil d p.
Proof.
	intros. simpl in |- *. induction  p as [a p1 Hrecp1 p0 Hrecp0| ]; exact (le_n_n 1).
Qed.

Lemma conservation_3 :
 forall (d : preDTA) (hd : term) (tl : term_list) (a : ad)
   (la ls : prec_list),
 S (essence_list (tcons hd tl) d ls) <=
 essence_list (tcons hd tl) d (prec_cons a la ls).
Proof.
	unfold essence_list in |- *. intros. induction  ls as [a0 ls1 Hrecls1 ls0 Hrecls0| ].
	cut
  (S
     (taille_0 (prec_cons a0 ls1 ls0) +
      S (term_high_0 (tcons hd tl)) * S (DTA_taille d)) =
   S (taille_0 (prec_cons a0 ls1 ls0)) +
   S (term_high_0 (tcons hd tl)) * S (DTA_taille d)).
	intro. rewrite H.
	cut
  (S (taille_0 (prec_cons a0 ls1 ls0)) <=
   taille_0 (prec_cons a la (prec_cons a0 ls1 ls0))).
	intro.
	exact
  (plus_le_compat (S (taille_0 (prec_cons a0 ls1 ls0)))
     (taille_0 (prec_cons a la (prec_cons a0 ls1 ls0)))
     (S (term_high_0 (tcons hd tl)) * S (DTA_taille d))
     (S (term_high_0 (tcons hd tl)) * S (DTA_taille d)) H0
     (le_n_n (S (term_high_0 (tcons hd tl)) * S (DTA_taille d)))).
	exact (taille_aux_2 a la (prec_cons a0 ls1 ls0)).
	generalize (taille_0 (prec_cons a0 ls1 ls0)).
	generalize (S (term_high_0 (tcons hd tl)) * S (DTA_taille d)).
	simpl in |- *. trivial.
	cut (1 <= taille_0 (prec_cons a la prec_empty)).
	cut (1 <= S (term_high_0 (tcons hd tl)) * S (DTA_taille d)).
	intros. exact
  (plus_le_compat 1 (taille_0 (prec_cons a la prec_empty)) 1
     (S (term_high_0 (tcons hd tl)) * S (DTA_taille d)) H0 H).
	exact
  (le_mult_mult 1 (S (term_high_0 (tcons hd tl))) 1 
     (S (DTA_taille d))
     (le_n_S 0 (term_high_0 (tcons hd tl))
        (le_O_n (term_high_0 (tcons hd tl))))
     (le_n_S 0 (DTA_taille d) (le_O_n (DTA_taille d)))).
	exact (taille_aux_1 a la prec_empty).
Qed.

Lemma conservation_4 :
 forall (d : preDTA) (hd : term) (tl : term_list) (a : ad)
   (la ls : prec_list),
 S (essence_list tl d la) <= essence_list (tcons hd tl) d (prec_cons a la ls).
Proof.
	unfold essence_list in |- *. intro. intro. intro. intros.
	cut (1 <= taille_0 (prec_cons a la ls)).
	cut (1 <= S (term_high_0 (tcons hd tl)) * S (DTA_taille d)).
	intros. induction  tl as [| t tl Hrectl].
	cut
  (2 <=
   taille_0 (prec_cons a la ls) +
   S (term_high_0 (tcons hd tnil)) * S (DTA_taille d)).
	intros. induction  la as [a0 la1 Hrecla1 la0 Hrecla0| ]. assumption.
	assumption.
	exact
  (plus_le_compat 1 (taille_0 (prec_cons a la ls)) 1
     (S (term_high_0 (tcons hd tnil)) * S (DTA_taille d)) H0 H).
	induction  la as [a0 la1 Hrecla1 la0 Hrecla0| ].
	cut
  (S
     (taille_0 (prec_cons a0 la1 la0) +
      S (term_high_0 (tcons t tl)) * S (DTA_taille d)) =
   S (taille_0 (prec_cons a0 la1 la0)) +
   S (term_high_0 (tcons t tl)) * S (DTA_taille d)).
	intro. rewrite H1. cut
  (S (taille_0 (prec_cons a0 la1 la0)) <=
   taille_0 (prec_cons a (prec_cons a0 la1 la0) ls)).
	intro.
	apply
  (plus_le_compat (S (taille_0 (prec_cons a0 la1 la0)))
     (taille_0 (prec_cons a (prec_cons a0 la1 la0) ls))
     (S (term_high_0 (tcons t tl)) * S (DTA_taille d))
     (S (term_high_0 (tcons hd (tcons t tl))) * S (DTA_taille d)) H2).
	cut
  (S (term_high_0 (tcons t tl)) <= S (term_high_0 (tcons hd (tcons t tl)))).
	intro.
	exact
  (le_mult_mult (S (term_high_0 (tcons t tl)))
     (S (term_high_0 (tcons hd (tcons t tl)))) (S (DTA_taille d))
     (S (DTA_taille d)) H3 (le_n_n (S (DTA_taille d)))).
	exact
  (le_n_S (term_high_0 (tcons t tl)) (term_high_0 (tcons hd (tcons t tl)))
     (high_aux_4 hd (tcons t tl))).
	exact (taille_aux_0 a (prec_cons a0 la1 la0) ls).
	generalize (taille_0 (prec_cons a0 la1 la0)).
	generalize (S (term_high_0 (tcons t tl)) * S (DTA_taille d)).
	simpl in |- *. trivial.
	exact
  (plus_le_compat 1 (taille_0 (prec_cons a prec_empty ls)) 1
     (S (term_high_0 (tcons hd (tcons t tl))) * S (DTA_taille d)) H0 H).
	exact
  (le_mult_mult 1 (S (term_high_0 (tcons hd tl))) 1 
     (S (DTA_taille d))
     (le_n_S 0 (term_high_0 (tcons hd tl))
        (le_O_n (term_high_0 (tcons hd tl))))
     (le_n_S 0 (DTA_taille d) (le_O_n (DTA_taille d)))).
	exact (taille_aux_1 a la ls).
Qed.


Lemma conservation_5_0 :
 forall (a : ad) (la ls : prec_list), 1 <= taille_0 (prec_cons a la ls).
Proof.
	intros. simpl in |- *. apply (le_n_S 0 (taille_0 la + taille_0 ls)).
	exact (le_O_n (taille_0 la + taille_0 ls)).
Qed.

Lemma conservation_5 :
 forall (d : preDTA) (hd : term) (tl : term_list) (a : ad)
   (la ls : prec_list),
 S (essence hd d) <= essence_list (tcons hd tl) d (prec_cons a la ls).
Proof.
	intros. unfold essence in |- *. unfold essence_list in |- *.
	cut (term_high hd <= term_high_0 (tcons hd tl)).
	cut (1 <= taille_0 (prec_cons a la ls)).
	intros.
	cut
  (S (S (term_high hd) * S (DTA_taille d)) =
   1 + S (term_high hd) * S (DTA_taille d)).
	intros. rewrite H1.
	apply
  (plus_le_compat 1 (taille_0 (prec_cons a la ls))
     (S (term_high hd) * S (DTA_taille d))
     (S (term_high_0 (tcons hd tl)) * S (DTA_taille d)) H).
	apply
  (le_mult_mult (S (term_high hd)) (S (term_high_0 (tcons hd tl)))
     (S (DTA_taille d)) (S (DTA_taille d))
     (le_n_S (term_high hd) (term_high_0 (tcons hd tl)) H0)).
	exact (le_n_n (S (DTA_taille d))).
	unfold plus in |- *. trivial.
	exact (conservation_5_0 a la ls).
	exact (high_aux_3 hd tl).
Qed.

Definition dta_rec_term (d : DTA) (t : term) : bool :=
  match d with
  | dta p a => rec_term p a t (essence t p)
  end.

(* définitions inductives pour la reconnaissance d'un terme par un automate *)

Inductive reconnaissance : preDTA -> ad -> term -> Prop :=
    rec_dta :
      forall (d : preDTA) (a : ad) (t : term) (ladj : state),
      MapGet state d a = Some ladj ->
      state_reconnait d ladj t -> reconnaissance d a t
with state_reconnait : preDTA -> state -> term -> Prop :=
    rec_st :
      forall (d : preDTA) (s : state) (c : ad) (tl : term_list)
        (l : prec_list),
      MapGet prec_list s c = Some l ->
      liste_reconnait d l tl -> state_reconnait d s (app c tl)
with liste_reconnait : preDTA -> prec_list -> term_list -> Prop :=
  | rec_empty : forall d : preDTA, liste_reconnait d prec_empty tnil
  | rec_consi :
      forall (d : preDTA) (a : ad) (la ls : prec_list) 
        (hd : term) (tl : term_list),
      reconnaissance d a hd ->
      liste_reconnait d la tl ->
      liste_reconnait d (prec_cons a la ls) (tcons hd tl)
  | rec_consn :
      forall (d : preDTA) (a : ad) (la ls : prec_list) 
        (hd : term) (tl : term_list),
      liste_reconnait d ls (tcons hd tl) ->
      liste_reconnait d (prec_cons a la ls) (tcons hd tl).

Definition reconnait (d : DTA) (t : term) : Prop :=
  match d with
  | dta p a => reconnaissance p a t
  end.

(* principe d'induction commun *)

Scheme mreconnaissance_ind := Induction for reconnaissance
  Sort Prop
  with mstrec_ind := Induction for state_reconnait 
  Sort Prop
  with mlrec_ind := Induction for liste_reconnait Sort Prop.

(* lemmes de base sur la sémantique précédente (pour simplifier d'autres démos) *)

Lemma sem_listes_0 :
 forall (d : preDTA) (p : prec_list) (hd : term) (tl : term_list),
 liste_reconnait d p (tcons hd tl) -> p <> prec_empty.
Proof.
	intros. intro. inversion H. rewrite H0 in H4. discriminate H4.
	rewrite H0 in H3. inversion H3.
Qed.

Lemma sem_listes_1 :
 forall (d : preDTA) (hd : term) (tl : term_list),
 ~ liste_reconnait d prec_empty (tcons hd tl).
Proof.
	intros. intro. cut (prec_empty = prec_empty). intro.
	exact (sem_listes_0 d prec_empty hd tl H H0). trivial.
Qed.

Lemma sem_listes_2 :
 forall (d : preDTA) (pl : prec_list),
 liste_reconnait d pl tnil -> pl = prec_empty.
Proof.
	intros. inversion H. trivial.
Qed.

(* lemmes d'équivalence sémantique entre la fonction calculatoire (Fixpoint) *)
(* et la définition par Inductive *)

Definition sem_equiv_prop_t (t : term) :=
  forall (d : preDTA) (a : ad) (n : nat),
  rec_term d a t n = true -> reconnaissance d a t.
Definition sem_equiv_prop_l (l : term_list) :=
  forall (d : preDTA) (p : prec_list) (n : nat),
  rec_list_terms d p l n = true -> liste_reconnait d p l.

Lemma semantic_equiv_0_0 :
 forall (d : preDTA) (p : prec_list) (n : nat),
 rec_list_terms d p tnil n = true -> p = prec_empty.
Proof.
	intros. induction  p as [a p1 Hrecp1 p0 Hrecp0| ]. induction  n as [| n Hrecn]. simpl in H. discriminate H.
	simpl in H. discriminate H.
	trivial.
Qed.

Lemma semantic_equiv_0_1 : sem_equiv_prop_l tnil.
Proof.
	unfold sem_equiv_prop_l in |- *. intros. cut (p = prec_empty). intros. rewrite H0.
	exact (rec_empty d).
	exact (semantic_equiv_0_0 d p n H).
Qed.

Lemma semantic_equiv_0_2 :
 forall (d : preDTA) (a a' : ad) (l : term_list) (n : nat) 
   (s : state) (p : prec_list),
 rec_term d a (app a' l) (S n) = true ->
 MapGet state d a = Some s ->
 MapGet prec_list s a' = Some p -> rec_list_terms d p l n = true.
Proof.
	intro. intro. intro. intro. simple induction n. intros. simpl in H. 
	rewrite H0 in H. rewrite H1 in H. discriminate H.
	intros. elim (classic (rec_list_terms d p l (S n0) = true)).
	intro. assumption.
	intro. cut (rec_list_terms d p l (S n0) = false). intro. simpl in H0.
	rewrite H1 in H0. rewrite H2 in H0. simpl in H0. simpl in H4. 
	simpl in H4. (* Unfold rec_list_terms in H4. *) rewrite H4 in H0.
	discriminate H0.
	exact (not_true_is_false (rec_list_terms d p l (S n0)) H3).
Qed.

Lemma semantic_equiv_0_3 :
 forall (d : preDTA) (a a' : ad) (l : term_list) (n : nat),
 rec_term d a (app a' l) (S n) = true ->
 exists s : state, MapGet state d a = Some s.
Proof.
	intro. intro. intro. intro. simpl in |- *. intro.
	elim (MapGet state d a). Focus 2. intro H. discriminate H.
	intro. split with a0. trivial.
Qed.

Lemma semantic_equiv_0_4 :
 forall (d : preDTA) (a a' : ad) (l : term_list) (n : nat) (s : state),
 MapGet state d a = Some s ->
 rec_term d a (app a' l) (S n) = true ->
 exists p : prec_list, MapGet prec_list s a' = Some p.
Proof.
	intro. intro. intro. intro. intro. intro. intro. simpl in |- *.
	rewrite H. simpl in |- *. elim (MapGet prec_list s a'). Focus 2.
	intro H0. discriminate H0.
	intro. intro. split with a0. trivial.
Qed.

Lemma semantic_equiv_0_5 :
 forall (a : ad) (t : term_list),
 sem_equiv_prop_l t -> sem_equiv_prop_t (app a t).
Proof.
	unfold sem_equiv_prop_l in |- *. unfold sem_equiv_prop_t in |- *. intros.
	cut (exists s : state, MapGet state d a0 = Some s).
	intro. elim H1. intros.
	cut (exists p : prec_list, MapGet prec_list x a = Some p).
	intros. elim H3. intros. induction  n as [| n Hrecn]. simpl in H0. discriminate H0.
	exact
  (rec_dta d a0 (app a t) x H2
     (rec_st d x a t x0 H4
        (H d x0 n (semantic_equiv_0_2 d a0 a t n x x0 H0 H2 H4)))).
	induction  n as [| n Hrecn]. simpl in H0. discriminate.
	exact (semantic_equiv_0_4 d a0 a t n x H2 H0).
	induction  n as [| n Hrecn]. simpl in H0. discriminate H0.
	exact (semantic_equiv_0_3 d a0 a t n H0).
Qed.

Lemma semantic_equiv_0_6 :
 forall (n : nat) (t : term) (t0 : term_list),
 (forall (d : preDTA) (a : ad) (m : nat),
  rec_term d a t m = true -> reconnaissance d a t) ->
 (forall (d : preDTA) (p : prec_list) (m : nat),
  rec_list_terms d p t0 m = true -> liste_reconnait d p t0) ->
 forall (d : preDTA) (p : prec_list),
 rec_list_terms d p (tcons t t0) n = true -> liste_reconnait d p (tcons t t0).
Proof.
	simple induction n. intros. simpl in H1. inversion H1. intros.
	simpl in H2. elim (pl_sum p); intros. rewrite H3 in H2.
	inversion H2. elim H3. intros. elim H4. intros. elim H5.
	intros. rewrite H6 in H2. elim (bool_is_true_or_false (rec_list_terms d x1 (tcons t t0) n0)); intros;
  rewrite H7 in H2. rewrite H6. exact (rec_consn d x x0 x1 t t0 (H t t0 H0 H1 d x1 H7)). simpl in H2. fold rec_term in H2. elim (bool_is_true_or_false (rec_term d x t n0)); intros; rewrite H8 in H2. elim (bool_is_true_or_false (rec_list_terms d x0 t0 n0)). intros. rewrite H6. exact (rec_consi d x x0 x1 t t0 (H0 _ _ _ H8) (H1 _ _ _ H9)). intros. rewrite H9 in H2.
	inversion H2. inversion H2.
Qed.

Lemma semantic_equiv_0_7 :
 forall t : term,
 sem_equiv_prop_t t ->
 forall t0 : term_list, sem_equiv_prop_l t0 -> sem_equiv_prop_l (tcons t t0).
Proof.
	unfold sem_equiv_prop_t, sem_equiv_prop_l in |- *. intros.
	exact (semantic_equiv_0_6 n t t0 H H0 d p H1).
Qed.

Lemma semantic_equiv_0 :
 forall (d : preDTA) (a : ad) (t : term) (n : nat),
 rec_term d a t n = true -> reconnaissance d a t.
Proof.
	cut (forall t : term, sem_equiv_prop_t t). intros. 
	unfold sem_equiv_prop_t in H; intros.
	exact (H t d a n H0).
	exact
  (term_term_list_ind sem_equiv_prop_t sem_equiv_prop_l semantic_equiv_0_5
     semantic_equiv_0_1 semantic_equiv_0_7).
Qed.

(* conservation de la reconnaissance d'un terme si on met plus d'essence ... *)

Definition invar_term (t : term) : Prop :=
  forall (n m : nat) (d : preDTA) (a : ad),
  rec_term d a t n = true -> n <= m -> rec_term d a t m = true.

Definition invar_list (tl : term_list) : Prop :=
  forall (n m : nat) (d : preDTA) (p : prec_list),
  rec_list_terms d p tl n = true -> n <= m -> rec_list_terms d p tl m = true.

Lemma invar_0 : invar_list tnil.
Proof.
	unfold invar_list in |- *. simple induction n. intro. intro. simple induction p.
	intros. simpl in H1. discriminate H1.
	intros. simpl in H. discriminate H.
	intro. intro. simple induction m. intros. elim (le_Sn_O n0 H1).
	intro. intro. simple induction p. intros. simpl in |- *. simpl in H3. assumption.
	simpl in |- *. intros. assumption.
Qed.

Lemma invar_1_0 :
 forall (d : preDTA) (a c : ad) (t : term_list) (n : nat) 
   (s : state) (p : prec_list),
 MapGet state d a = Some s ->
 MapGet prec_list s c = Some p ->
 rec_list_terms d p t n = true -> rec_term d a (app c t) (S n) = true.
Proof.
	intro; intro; intro; simple induction n. intros. simpl in H1. discriminate H1.
	intros. simpl in |- *. rewrite H0. rewrite H1. simpl in H2. assumption.
Qed.

Lemma invar_1_1 :
 forall (d : preDTA) (a c : ad) (t : term_list) (n : nat),
 rec_term d a (app c t) (S n) = true ->
 exists p : prec_list, rec_list_terms d p t n = true.
Proof.
	intros. cut (exists s : state, MapGet state d a = Some s).
	intro. elim H0. intros.
	cut (exists p : prec_list, MapGet prec_list x c = Some p).
	intro. elim H2. intros. split with x0.
	exact (semantic_equiv_0_2 d a c t n x x0 H H1 H3).
	exact (semantic_equiv_0_4 d a c t n x H1 H).
	exact (semantic_equiv_0_3 d a c t n H).
Qed.

Lemma invar_1 :
 forall (a : ad) (t : term_list), invar_list t -> invar_term (app a t).
Proof.
	intro. intro. intro. unfold invar_list in H. unfold invar_term in |- *.
	simple induction n. intros. simpl in H0. discriminate H0.
	intro. intro. simple induction m; intros. elim (le_Sn_O n0 H2).
	cut (exists s : state, MapGet state d a0 = Some s).
	intro. elim H4. intros. 
	cut (exists p : prec_list, MapGet prec_list x a = Some p).
	intro. elim H6. intros. apply (invar_1_0 d a0 a t n1 x x0 H5 H7).
	cut (rec_list_terms d x0 t n0 = true). intro.
	exact (H n0 n1 d x0 H8 (le_S_n n0 n1 H3)).
	exact (semantic_equiv_0_2 d a0 a t n0 x x0 H2 H5 H7).
	exact (semantic_equiv_0_4 d a0 a t n0 x H5 H2).
	exact (semantic_equiv_0_3 d a0 a t n0 H2).
Qed.

Lemma invar_2_0 :
 forall (d : preDTA) (p : prec_list) (n : nat),
 rec_list_terms d p tnil n = true -> p = prec_empty.
Proof.
	intro. simple induction p; simple induction n. intro. simpl in H1. discriminate H1.
	intros. simpl in H2. discriminate H2.
	intro. simpl in H. trivial.
	intros. trivial.
Qed.

Lemma invar_2_1 :
 forall (d : preDTA) (a : ad) (la ls : prec_list) (hd : term)
   (tl : term_list) (n : nat),
 rec_list_terms d (prec_cons a la ls) (tcons hd tl) (S n) = true ->
 rec_list_terms d ls (tcons hd tl) n = true \/
 rec_term d a hd n = true /\ rec_list_terms d la tl n = true.
Proof.
	intro. intro. intro. intro. intro. intro. intro. induction  n as [| n Hrecn]. intro. simpl in H.
	discriminate H.
	intros.
	cut
  (rec_list_terms d ls (tcons hd tl) (S n) = true \/
   rec_list_terms d ls (tcons hd tl) (S n) = false).
	cut (rec_term d a hd (S n) = true \/ rec_term d a hd (S n) = false).
	cut
  (rec_list_terms d la tl (S n) = true \/
   rec_list_terms d la tl (S n) = false).
	intros. elim H2. left. assumption.
	elim H1. elim H0. intros. right. split; assumption. simpl in H. intros.
	simpl in H. simpl in H3. simpl in H4. simpl in H5. rewrite H3 in H.
	rewrite H4 in H. rewrite H5 in H. simpl in H. discriminate H.
	intros. simpl in H. simpl in H2. simpl in H3. simpl in H4. rewrite H3 in H.
	rewrite H4 in H. simpl in H. discriminate H.
	exact (bool_is_true_or_false (rec_list_terms d la tl (S n))).
	exact (bool_is_true_or_false (rec_term d a hd (S n))).
	exact (bool_is_true_or_false (rec_list_terms d ls (tcons hd tl) (S n))).
Qed.

Lemma invar_2_2 :
 forall (d : preDTA) (a : ad) (la ls : prec_list) (hd : term)
   (tl : term_list) (n : nat),
 rec_list_terms d ls (tcons hd tl) n = true \/
 rec_term d a hd n = true /\ rec_list_terms d la tl n = true ->
 rec_list_terms d (prec_cons a la ls) (tcons hd tl) (S n) = true.
Proof.
	intros. elim H. intro. simpl in |- *. simpl in H0. rewrite H0. simpl in |- *. trivial.
	intro. elim H0. intro. intro. simpl in |- *. simpl in H1. (*Unfold rec_term in H1.*)
	rewrite H1. rewrite H2. simpl in |- *. 
	exact (orb_b_true (rec_list_terms d ls (tcons hd tl) n)).
Qed.
 
Lemma invar_2 :
 forall t : term,
 invar_term t ->
 forall t0 : term_list, invar_list t0 -> invar_list (tcons t t0).
Proof.
	intros. unfold invar_list in H0. unfold invar_list in |- *. 
	simple induction n; simple induction m; intro. intros. simpl in H1. discriminate H1.
	intros. simpl in H2. discriminate H2.
	intros. elim (le_Sn_O n0 H3).
	simple induction p. intros.
	cut
  (rec_list_terms d p1 (tcons t t0) n1 = true \/
   rec_term d a t n1 = true /\ rec_list_terms d p0 t0 n1 = true).
	intro. elim H7. intros. exact (invar_2_2 d a p0 p1 t t0 n1 H7).
	intros. exact (invar_2_2 d a p0 p1 t t0 n1 H7).
	cut
  (rec_list_terms d p1 (tcons t t0) n0 = true \/
   rec_term d a t n0 = true /\ rec_list_terms d p0 t0 n0 = true).
	intro. elim H7; intros. left. exact (H1 n1 d p1 H8 (le_S_n n0 n1 H6)).
	right. elim H8. intros. split. unfold invar_term in H. 
	exact (H n0 n1 d a H9 (le_S_n n0 n1 H6)).
	exact (H0 n0 n1 d p0 H10 (le_S_n n0 n1 H6)).
	exact (invar_2_1 d a p0 p1 t t0 n0 H5).
	intros. simpl in H3. discriminate H3.
Qed.

Lemma invar : forall t : term, invar_term t.
Proof.
	exact (term_term_list_ind invar_term invar_list invar_1 invar_0 invar_2).
Qed.

Lemma invarl : forall tl : term_list, invar_list tl.
Proof.
	exact (term_list_term_ind invar_term invar_list invar_1 invar_0 invar_2).
Qed.

(* Second sens de l'équivalence sémantique *)

Definition dta_reconnait (d : preDTA) (a : ad) (t : term)
  (pr : reconnaissance d a t) := rec_term d a t (essence t d) = true.

Definition st_reconnait (d : preDTA) (s : state) (t : term)
  (pr : state_reconnait d s t) :=
  match t with
  | app c l =>
      exists p : prec_list,
        MapGet prec_list s c = Some p /\
        rec_list_terms d p l (essence_list l d p) = true
  end.

Definition pre_reconnait (d : preDTA) (p : prec_list) 
  (t : term_list) (pr : liste_reconnait d p t) :=
  rec_list_terms d p t (essence_list t d p) = true.

Lemma semantic_equiv_1_0 :
 forall (d : preDTA) (a : ad) (t : term) (ladj : state)
   (e : MapGet state d a = Some ladj) (s : state_reconnait d ladj t),
 st_reconnait d ladj t s -> dta_reconnait d a t (rec_dta d a t ladj e s).
Proof.
	intros. unfold dta_reconnait in |- *. unfold st_reconnait in H. induction  t as (a0, t).
	simpl in H. elim H. intros; intros. elim H0. intros.
	cut (rec_term d a (app a0 t) (S (essence_list t d x)) = true).
	cut (S (essence_list t d x) <= essence (app a0 t) d).
	intros. exact
  (invar (app a0 t) (S (essence_list t d x)) (essence (app a0 t) d) d a H4 H3).
	apply (conservation_0 d x a0 t). unfold prec_in_dta in |- *. split with ladj. split with a.
	split with a0. split. assumption.
	assumption.
	simpl in |- *. rewrite e. rewrite H1. simpl in H2. assumption.
Qed.

Lemma semantic_equiv_1_1 :
 forall (d : preDTA) (s : state) (c : ad) (tl : term_list) 
   (l : prec_list) (e : MapGet prec_list s c = Some l)
   (l0 : liste_reconnait d l tl),
 pre_reconnait d l tl l0 ->
 st_reconnait d s (app c tl) (rec_st d s c tl l e l0).
Proof.
	intros. unfold st_reconnait in |- *. unfold pre_reconnait in H. split with l. split; assumption.
Qed.

Lemma semantic_equiv_1_2 :
 forall d : preDTA, pre_reconnait d prec_empty tnil (rec_empty d).
Proof.
	intros. unfold pre_reconnait in |- *. simpl in |- *. trivial.
Qed.

Lemma semantic_equiv_1_3 :
 forall (d : preDTA) (a : ad) (la ls : prec_list) (hd : term)
   (tl : term_list) (r : reconnaissance d a hd),
 dta_reconnait d a hd r ->
 forall l : liste_reconnait d la tl,
 pre_reconnait d la tl l ->
 pre_reconnait d (prec_cons a la ls) (tcons hd tl)
   (rec_consi d a la ls hd tl r l).
Proof.
	intros. unfold dta_reconnait in H. unfold pre_reconnait in H0. unfold pre_reconnait in |- *.
	cut
  (rec_list_terms d (prec_cons a la ls) (tcons hd tl)
     (S (max (essence hd d) (essence_list tl d la))) = true).
	intro. cut
  (S (max (essence hd d) (essence_list tl d la)) <=
   essence_list (tcons hd tl) d (prec_cons a la ls)).
	intros. exact
  (invarl (tcons hd tl) (S (max (essence hd d) (essence_list tl d la)))
     (essence_list (tcons hd tl) d (prec_cons a la ls)) d 
     (prec_cons a la ls) H1 H2).
	cut
  (max (essence hd d) (essence_list tl d la) = essence hd d \/
   max (essence hd d) (essence_list tl d la) = essence_list tl d la).
	intro. elim H2. intros. rewrite H3. exact (conservation_5 d hd tl a la ls).
	intro. rewrite H3. exact (conservation_4 d hd tl a la ls).
	case (max_dec (essence hd d) (essence_list tl d la)); [ left | right ]; auto.
	cut (rec_term d a hd (max (essence hd d) (essence_list tl d la)) = true).
	cut
  (rec_list_terms d la tl (max (essence hd d) (essence_list tl d la)) = true).
	generalize (max (essence hd d) (essence_list tl d la)). intros. simpl in |- *. rewrite H1.
	(* Unfold rec_term in H2. *) rewrite H2. simpl in |- *.
	exact (orb_b_true (rec_list_terms d ls (tcons hd tl) n)).
	cut (essence_list tl d la <= max (essence hd d) (essence_list tl d la)).
	intro. exact
  (invarl tl (essence_list tl d la)
     (max (essence hd d) (essence_list tl d la)) d la H0 H1).
	exact (le_max_r (essence hd d) (essence_list tl d la)).
	cut (essence hd d <= max (essence hd d) (essence_list tl d la)). intro.
	exact
  (invar hd (essence hd d) (max (essence hd d) (essence_list tl d la)) d a H
     H1).
	exact (le_max_l (essence hd d) (essence_list tl d la)).
Qed.

Lemma semantic_equiv_1_4_0 :
 forall (d : preDTA) (a : ad) (la ls : prec_list) (l : term_list) (n : nat),
 l <> tnil ->
 rec_list_terms d ls l n = true ->
 rec_list_terms d (prec_cons a la ls) l (S n) = true.
Proof.
	intro. intro. intro. intro. simple induction l. intros. simpl in H. cut (tnil = tnil). intro. elim (H H1).
	trivial.
	intro. intro. simple induction n. intros. simpl in H1. discriminate H1.
	intros. simpl in |- *. simpl in H2. rewrite H2. simpl in |- *. trivial.
Qed.

Lemma semantic_equiv_1_4 :
 forall (d : preDTA) (a : ad) (la ls : prec_list) (hd : term)
   (tl : term_list) (l : liste_reconnait d ls (tcons hd tl)),
 pre_reconnait d ls (tcons hd tl) l ->
 pre_reconnait d (prec_cons a la ls) (tcons hd tl)
   (rec_consn d a la ls hd tl l).
Proof.
	intro. intro. intro. intro. unfold pre_reconnait in |- *. intros. induction  ls as [a0 ls1 Hrecls1 ls0 Hrecls0| ].
	cut
  (S (essence_list (tcons hd tl) d (prec_cons a0 ls1 ls0)) <=
   essence_list (tcons hd tl) d (prec_cons a la (prec_cons a0 ls1 ls0))).
	intro. cut
  (rec_list_terms d (prec_cons a la (prec_cons a0 ls1 ls0)) 
     (tcons hd tl) (S (essence_list (tcons hd tl) d (prec_cons a0 ls1 ls0))) =
   true).
	intro.
	exact
  (invarl (tcons hd tl)
     (S (essence_list (tcons hd tl) d (prec_cons a0 ls1 ls0)))
     (essence_list (tcons hd tl) d (prec_cons a la (prec_cons a0 ls1 ls0))) d
     (prec_cons a la (prec_cons a0 ls1 ls0)) H1 H0).
	cut (tcons hd tl <> tnil). intro. (* Unfold liste_reconnait in l.*)
	exact
  (semantic_equiv_1_4_0 d a la (prec_cons a0 ls1 ls0) 
     (tcons hd tl) (essence_list (tcons hd tl) d (prec_cons a0 ls1 ls0)) H1 H).
	intro. inversion H1.
	exact (conservation_3 d hd tl a la (prec_cons a0 ls1 ls0)).
	simpl in H. discriminate H.
Qed.

Lemma semantic_equiv_1 :
 forall (d : preDTA) (a : ad) (t : term),
 reconnaissance d a t -> rec_term d a t (essence t d) = true.
Proof.
	exact
  (mreconnaissance_ind dta_reconnait st_reconnait pre_reconnait
     semantic_equiv_1_0 semantic_equiv_1_1 semantic_equiv_1_2
     semantic_equiv_1_3 semantic_equiv_1_4).
Qed.