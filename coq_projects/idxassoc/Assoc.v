(*
 * This code was developped by IDEALX (http://IDEALX.org/) and
 * contributors (their names can be found in the CONTRIBUTORS file). It 
 * is released under the terms of the BSD license (see LICENCE file
 * for details). 
*)


(******************************************************************
 *          	      ASSOCIATIVE ARRAYS V0.1 (April 2001)
 *
 *
 ******************************************************************
 *
 *   We define the associative array (key -> value associations) 
 * datatype as list of couples, providing definitions of standards 
 * operations such as adding, deleting. 
 *   
 *   We introduce predicates for membership of a key and of couples. 
 *   
 *   Finally we define a search operator ("find") which returns the 
 * value associated with a key or the "none" option (see file 
 * Option.v which should be part of this contribution) on failure.
 * 
 *   Lemmas we prove about these concepts were motivated by our 
 * needs at the moment we created this file. We hope they'll suit 
 * your needs too but anyway, feel free to communicate any wish 
 *  or remark.
 *
 ******************************************************************)

Unset Standard Proposition Elimination Names.









Section associative_arrays.

Set Asymmetric Patterns.
Set Strict Implicit.
Unset Implicit Arguments.

Require Import List.
Require Import Option.

Variable K : Set. 
Variable V : Set. 

Hypothesis Keq_dec : forall x y : K, {x = y} + {x <> y}.


Record Tuple : Set := mkTuple {k : K; v : V}.




(**************************************************)
(* Definitions                                    *)
(**************************************************)



Definition assoc := list Tuple.  
(* <Warning> : Syntax is discontinued *) 


Definition assoc_empty := nil (A:=Tuple).


(* search function : locate a value by its key *)
Fixpoint assoc_find (l : assoc) : K -> option V :=
  fun k0 : K =>
  match l with
  | nil => none V
  | mkTuple k v :: l' =>
      match Keq_dec k k0 with
      | left _ => some V v
      | right _ => assoc_find l' k0
      end
  end.


(* function to add an entry in an array:  may replace an existing entry
  if the key is already present in the array *)
Fixpoint assoc_add (l : assoc) : K -> V -> assoc :=
  fun (k0 : K) (v0 : V) =>
  match l with
  | nil => mkTuple k0 v0 :: nil
  | mkTuple k v :: l' =>
      match Keq_dec k k0 with
      | left _ => mkTuple k0 v0 :: l'
      | _ => mkTuple k v :: assoc_add l' k0 v0
      end
  end.


(* remove an entry from an array or do nothing if the key isn't
    present in the array *) 
Fixpoint assoc_delete (l : assoc) : K -> assoc :=
  fun k0 : K =>
  match l with
  | nil => nil (A:=Tuple)
  | mkTuple k v :: l' =>
      match Keq_dec k k0 with
      | left _ => assoc_delete l' k0
      | _ => mkTuple k v :: assoc_delete l' k0
      end
  end.


(* tests the existence of a key in an array *)
Definition assoc_mem (l : assoc) (k : K) : Prop :=
  match assoc_find l k with
  | some _ => True
  | _ => False
  end.


(* tests the existence of the specified tuple in an array *)
Definition assoc_hasmem (l : assoc) (k : K) (v : V) : Prop :=
  match assoc_find l k with
  | some v' => v = v'
  | _ => False
  end.


(* definition of equal functions from keys to values option *)
Definition assoc_eqm (f1 f2 : K -> option V) := forall k : K, f1 k = f2 k.
 

(* definition of almost-everywhere-equal functions from keys 
  to values option *)
Definition assoc_almost_eqm (k0 : K) (f1 f2 : K -> option V) :=
  forall k : K, k <> k0 -> f1 k = f2 k.




(**************************************************)
(* Some properties about eqm functions            *)
(**************************************************)



Lemma assoc_almost_eqm_trans :
 forall (k : K) (f1 f2 f3 : K -> option V),
 assoc_almost_eqm k f1 f2 ->
 assoc_almost_eqm k f2 f3 -> assoc_almost_eqm k f1 f3.

Proof.
  intros k0 f1 f2 f3.
  unfold assoc_almost_eqm in |- *.
  intros H1 H2.
  intros k1 Kdiff.
  replace (f1 k1) with (f2 k1).
  apply H2.
  assumption.

  elim H1.
  trivial.

  trivial.
Qed.


Lemma assoc_almost_eqm_sym :
 forall (k : K) (f1 f2 : K -> option V),
 assoc_almost_eqm k f1 f2 -> assoc_almost_eqm k f2 f1.

Proof.
  intros k0 f1 f2.
  unfold assoc_almost_eqm in |- *.
  intro H.
  intros k1 kdiff.
  elim H.
  trivial.

  trivial.
Qed.


Lemma assoc_eqm_trans :
 forall f1 f2 f3 : K -> option V,
 assoc_eqm f1 f2 -> assoc_eqm f2 f3 -> assoc_eqm f1 f3.

Proof.
intros f1 f2 f3.
unfold assoc_eqm in |- *.
intros H1 H2 k0.
transitivity (f2 k0).
elim H1; trivial.
 
elim H2; trivial.
Qed.




(**************************************************)
(* assoc_find properties                          *)
(**************************************************)



Lemma assoc_semfind_nil :
 assoc_eqm (assoc_find assoc_empty) (fun k : K => none V).

Proof.
  simpl in |- *.
  unfold assoc_eqm in |- *.
  trivial.
Qed.


Lemma assoc_semfind_cons_1 :
 forall (k : K) (v : V) (l : assoc),
 assoc_almost_eqm k (assoc_find (mkTuple k v :: l)) (assoc_find l).

Proof.
intros.
unfold assoc_almost_eqm in |- *.
intros.
unfold assoc_find at 1 in |- *.
case (Keq_dec k0 k1).
intro.
elim H.
rewrite <- e.
trivial.
intros.
trivial.
Qed.


Lemma assoc_semfind_cons_2 :
 forall (k : K) (v : V) (l : assoc),
 assoc_find (mkTuple k v :: l) k = some V v.

Proof.
unfold assoc_find in |- *.
intros.
case (Keq_dec k0 k0).
auto.
intro.
elim n.
auto.
Qed.


Lemma assoc_semfind_change_valeur :
 forall (k : K) (v v' : V) (l : assoc),
 assoc_almost_eqm k (assoc_find (mkTuple k v :: l))
   (assoc_find (mkTuple k v' :: l)).

Proof.
intros.
cut (assoc_almost_eqm k0 (assoc_find l) (assoc_find (mkTuple k0 v' :: l))).
cut (assoc_almost_eqm k0 (assoc_find (mkTuple k0 v0 :: l)) (assoc_find l)).
intros.
apply assoc_almost_eqm_trans with (assoc_find l).
assumption.
 
assumption.
 
apply assoc_semfind_cons_1.
 
apply assoc_almost_eqm_sym.
apply assoc_semfind_cons_1.
Qed.


Lemma assoc_semfind_increase_1 :
 forall (a : Tuple) (l l' : assoc),
 assoc_eqm (assoc_find l) (assoc_find l') ->
 assoc_eqm (assoc_find (a :: l)) (assoc_find (a :: l')).

Proof.
unfold assoc_eqm in |- *.
intros.
induction  a as (k1, v0).
unfold assoc_find in |- *; case (Keq_dec k1 k0); fold assoc_find in |- *;
 auto.
Qed.


Lemma assoc_semfind_increase_2 :
 forall (k : K) (a : Tuple) (l l' : assoc),
 assoc_almost_eqm k (assoc_find l) (assoc_find l') ->
 assoc_almost_eqm k (assoc_find (a :: l)) (assoc_find (a :: l')).

Proof.
intros.
unfold assoc_almost_eqm in |- *.
intros.
unfold assoc_find in |- *.
induction  a as (k2, v0).
case (Keq_dec k2 k1).
trivial.
fold assoc_find in |- *.
intro.
elim H.
trivial.
trivial.
Qed.


Lemma assoc_semfind_commute :
 forall (k0 k1 : K) (v0 v1 : V) (l : assoc),
 k0 <> k1 ->
 assoc_eqm (assoc_find (mkTuple k1 v1 :: mkTuple k0 v0 :: l))
   (assoc_find (mkTuple k0 v0 :: mkTuple k1 v1 :: l)).

Proof.
  intros. unfold assoc_eqm in |- *. intros. unfold assoc_find in |- *.
  case (Keq_dec k1 k2).
  intro.
  replace k2 with k1.
  case (Keq_dec k0 k1).
  intro.
  elim H.
  trivial.

  trivial.
 
  intro.
  case (Keq_dec k0 k2).
  trivial.

  intro.
  trivial.
Qed.


Lemma assoc_hasmem_find :
 forall (l : assoc) (k : K) (v : V),
 assoc_hasmem l k v -> assoc_find l k = some V v.

Proof.
unfold assoc_hasmem in |- *.
intros l k0 v0.
case (assoc_find l k0).
auto.
intros.
contradiction.
intros.
rewrite H.
auto.
Qed.


Lemma assoc_find_hasmem :
 forall (l : assoc) (k : K) (v : V),
 assoc_find l k = some V v -> assoc_hasmem l k v.

Proof.
unfold assoc_hasmem in |- *; intros; rewrite H; auto.
Qed.


Lemma assoc_find_none_hasmem :
 forall (l : assoc) (k : K) (v : V),
 assoc_find l k = none V -> forall v : V, ~ assoc_hasmem l k v.

Proof.
unfold not in |- *; intros; absurd (assoc_find l k0 = some V v1).
rewrite H; discriminate.
apply assoc_hasmem_find; assumption.
Qed.


Lemma assoc_find_mem :
 forall (l : assoc) (k : K) (v : V),
 assoc_find l k = some V v -> assoc_mem l k.

Proof.
unfold assoc_mem in |- *; intros; rewrite H; simpl in |- *; auto.
Qed.




(**************************************************)
(* mem/hasmem connectivity                        *)
(**************************************************)



Lemma assoc_hasmem_mem :
 forall (l : assoc) (k : K) (v : V), assoc_hasmem l k v -> assoc_mem l k.

Proof.
intros.
cut (assoc_find l k0 = some V v0).
intro.
unfold assoc_mem in |- *.
rewrite H0.
auto.
apply assoc_hasmem_find.
auto.
Qed.


Lemma assoc_mem_hasmem :
 forall (l : assoc) (k : K),
 assoc_mem l k -> exists v : V, assoc_hasmem l k v.

Proof.
simple induction l.
simpl in |- *; unfold assoc_mem in |- *; simpl in |- *; auto.
intros; contradiction.
intros; unfold assoc_hasmem in |- *; simpl in |- *.
induction  a as (k1, v0).
case (Keq_dec k1 k0).
intros; split with v0; auto.
intros; unfold assoc_hasmem in H; apply H; auto.
generalize H0; unfold assoc_mem in |- *; simpl in |- *.
case (Keq_dec k1 k0); auto.
intro; absurd (k1 = k0); assumption.
Qed.




(**************************************************)
(* assoc_add properties                           *)
(**************************************************)



Lemma assoc_add_egale_cons :
 forall (t : assoc) (k : K) (v : V),
 assoc_eqm (assoc_find (mkTuple k v :: t)) (assoc_find (assoc_add t k v)).

Proof.
intro.
induction  t as [| a t Hrect].
unfold assoc_add, assoc_eqm in |- *.
trivial.
 
induction  a as (k0, v0).
unfold assoc_add in |- *.
intros.
case (Keq_dec k0 k1).
intro; replace k1 with k0.
unfold assoc_eqm in |- *.
intro.
unfold assoc_find in |- *; case (Keq_dec k0 k2); trivial.
 
fold assoc_add in |- *.
intro.
apply assoc_eqm_trans with (assoc_find (mkTuple k0 v0 :: mkTuple k1 v1 :: t)).
apply assoc_semfind_commute; auto.
 
apply assoc_semfind_increase_1; apply Hrect.
Qed.


Lemma assoc_add_correct_1 :
 forall (k : K) (v : V) (t : assoc),
 assoc_almost_eqm k (assoc_find (assoc_add t k v)) (assoc_find t).

Proof.
intros; unfold assoc_almost_eqm in |- *; intros.
replace (assoc_find (assoc_add t k0 v0) k1) with
 (assoc_find (mkTuple k0 v0 :: t) k1).
  simpl in |- *. case (Keq_dec k0 k1).
    intro; absurd (k1 = k0); auto.
    auto.
  cut
   (assoc_eqm (assoc_find (mkTuple k0 v0 :: t))
      (assoc_find (assoc_add t k0 v0))).
    unfold assoc_eqm in |- *; auto.
    apply assoc_add_egale_cons.
Qed.


Lemma assoc_add_correct_2 :
 forall (k : K) (v : V) (t : assoc),
 assoc_find (assoc_add t k v) k = some V v.

Proof.
intros.
transitivity (assoc_find (mkTuple k0 v0 :: t) k0).
elim assoc_add_egale_cons.
auto.
apply assoc_semfind_cons_2.
Qed.


Lemma assoc_add_correct_3 :
 forall (k : K) (v : V) (t : assoc), assoc_hasmem (assoc_add t k v) k v.

Proof.
intros.
unfold assoc_hasmem in |- *.
replace (assoc_find (assoc_add t k0 v0) k0) with (some V v0).
auto.
symmetry  in |- *.
apply assoc_add_correct_2.
Qed.


Lemma assoc_add_correct_4 :
 forall (k : K) (v : V) (t : assoc), assoc_mem (assoc_add t k v) k.

Proof.
intros.
apply assoc_hasmem_mem with v0.
apply assoc_add_correct_3.
Qed.




(**************************************************)
(* assoc_del properties                           *)
(**************************************************)



Lemma assoc_del_correct_1 :
 forall (l : assoc) (k : K), assoc_find (assoc_delete l k) k = none V.

Proof.
simple induction l; simpl in |- *; auto.
simple induction a; simpl in |- *.
intros.
case (Keq_dec k0 k1); auto.
intro; simpl in |- *.
case (Keq_dec k0 k1); auto.
intro; absurd (k0 = k1); assumption.
Qed.


Lemma assoc_del_correct_2 :
 forall (l : assoc) (k : K) (v : V), ~ assoc_hasmem (assoc_delete l k) k v.

Proof.
simple induction l; simpl in |- *; auto.
simple induction a; simpl in |- *; intros.
case (Keq_dec k0 k1).
intros; apply H.
unfold assoc_hasmem in |- *.
simpl in |- *.
case (Keq_dec k0 k1).
auto.
intros.
replace
 match assoc_find (assoc_delete l0 k1) k1 with
 | none => False
 | some v' => v1 = v'
 end with (assoc_hasmem (assoc_delete l0 k1) k1 v1).
apply H.
unfold assoc_hasmem in |- *; trivial.
Qed.


Lemma assoc_del_correct_3 :
 forall (l : assoc) (k : K), ~ assoc_mem (assoc_delete l k) k.

Proof.
simple induction l; auto.
intros; simpl in |- *; induction  a as (k1, v0).
  case (Keq_dec k1 k0).
    intros; apply H.
    intros; unfold assoc_mem in |- *; simpl in |- *; case (Keq_dec k1 k0).
       intros; absurd (k1 = k0); assumption.
       unfold assoc_mem in H; intros; apply H; auto.
Qed.


Lemma assoc_semfind_del :
 forall (l : assoc) (k : K),
 assoc_almost_eqm k (assoc_find l) (assoc_find (assoc_delete l k)).

Proof.
unfold assoc_almost_eqm in |- *; simple induction l; auto.
intros; induction  a as (k2, v0); simpl in |- *; case (Keq_dec k2 k1);
 case (Keq_dec k2 k0).
intros; absurd (k1 = k0); auto. transitivity k2; auto.
intros. simpl in |- *. case (Keq_dec k2 k1); auto.
   intros; absurd (k2 = k1); assumption.
intros; apply H; assumption.
intros; simpl in |- *. case (Keq_dec k2 k1).
   intros; absurd (k2 = k1); assumption.
   intro; apply H; auto.
Qed.


Lemma assoc_del_decrease_1 :
 forall (l : assoc) (k k' : K),
 assoc_find l k = none V -> assoc_find (assoc_delete l k') k = none V.

Proof.
simple induction l; simpl in |- *; auto.
simple induction a; simpl in |- *; intros.
generalize H0.
case (Keq_dec k0 k1); simpl in |- *.
intros.
discriminate H1.
intros; case (Keq_dec k0 k'); intros.
  apply H; assumption.
  simpl in |- *; case (Keq_dec k0 k1); intros.
    absurd (k0 = k1); assumption.
    apply H; assumption.
Qed.


Lemma assoc_del_decrease_2 :
 forall (l : assoc) (k k' : K) (v : V),
 assoc_find (assoc_delete l k') k = some V v -> assoc_find l k = some V v.

Proof.
intros.
induction  l as [| a l Hrecl]; simpl in |- *.
generalize H; simpl in |- *; intro myhyp; discriminate myhyp.
induction  a as (k1, v1).
case (Keq_dec k1 k0).
intro.
transitivity (assoc_find (assoc_delete (mkTuple k1 v1 :: l) k') k0); auto.
rewrite e.
simpl in |- *.
case (Keq_dec k0 k').
intro.
rewrite e in H.
rewrite e0 in H.
absurd (assoc_find (assoc_delete (mkTuple k' v1 :: l) k') k' = none V).
unfold not in |- *; rewrite H; intro myhyp; discriminate myhyp.
apply assoc_del_correct_1; auto.
intros; simpl in |- *. case (Keq_dec k0 k0); auto.
intro; absurd (k0 = k0); auto.
intro; apply Hrecl.
  transitivity (assoc_find (assoc_delete (mkTuple k1 v1 :: l) k') k0); auto.
simpl in |- *.
case (Keq_dec k1 k'); auto.
simpl in |- *.
intro.
case (Keq_dec k1 k0).
intro; absurd (k1 = k0); assumption.
auto.
Qed.


Lemma assoc_del_decrease_3 :
 forall (l : assoc) (k k' : K) (v v' : V),
 assoc_find l k = some V v ->
 assoc_find (assoc_delete l k') k = some V v' -> v = v'.

Proof.
intros.
cut (assoc_find l k0 = some V v').
rewrite H; auto.
intro INJ; injection INJ.
auto.
apply assoc_del_decrease_2 with k'; assumption.
Qed.


Lemma assoc_del_correct_4 :
 forall (l : assoc) (k k' : K) (v : V),
 ~ assoc_hasmem l k v -> ~ assoc_hasmem (assoc_delete l k') k v.

Proof.
intros; intro; absurd (assoc_hasmem l k0 v0); auto.
apply assoc_find_hasmem.
apply assoc_del_decrease_2 with k'.
apply assoc_hasmem_find.
auto.
Qed.


Lemma assoc_del_correct_5 :
 forall (l : assoc) (k k' : K),
 ~ assoc_mem l k -> ~ assoc_mem (assoc_delete l k') k.

Proof.
intros; intro; absurd (assoc_mem l k0); auto.
cut (exists v : V, assoc_hasmem (assoc_delete l k') k0 v).
intro EXISTS; elim EXISTS; intros; apply assoc_hasmem_mem with x; auto.
apply assoc_find_hasmem; apply assoc_del_decrease_2 with k';
 apply assoc_hasmem_find; assumption.
apply assoc_mem_hasmem; assumption.
Qed.




(**************************************************)
(*  some decidability properties                  *)
(**************************************************)



Lemma assoc_mem_dec :
 forall (l : assoc) (k : K), {assoc_mem l k} + {~ assoc_mem l k}.

Proof.
unfold assoc_mem in |- *; intros; case (assoc_find l k0).
right; auto.
left; auto.
Qed.


Lemma assoc_hasmem_dec :
 forall (Veq_dec : forall x y : V, {x = y} + {x <> y}) 
   (l : assoc) (k : K) (v : V), {assoc_hasmem l k v} + {~ assoc_hasmem l k v}.

Proof.
intros; unfold assoc_hasmem in |- *; case (assoc_find l k0).
right; auto.
intros; apply Veq_dec.
Qed.


Lemma assoc_hasmem_ex_dec :
 forall (Veq_dec : forall x y : V, {x = y} + {x <> y}) 
   (l : assoc) (k : K) (v : V),
 {(exists v : V, assoc_hasmem l k v)} +
 {~ (exists v : V, assoc_hasmem l k v)}.

Proof.
intros.
unfold assoc_hasmem in |- *.
case (assoc_find l k0).
right.
intro.
elim H; auto.
intro.
left.
split with v1.
auto.
Qed.


Lemma assoc_add_mem_choice :
 forall (b0 b : assoc) (k k0 : K) (v0 : V),
 b = assoc_add b0 k0 v0 -> assoc_mem b k -> assoc_mem b0 k \/ k = k0.

Proof.
intros until 1. rewrite H. unfold assoc_mem in |- *.
replace (assoc_find (assoc_add b0 k1 v0) k0) with
 (assoc_find (mkTuple k1 v0 :: b0) k0).
  simpl in |- *. case (Keq_dec k1 k0).
    intros; right; auto.
    intros; left; auto.
  cut
   (assoc_eqm (assoc_find (mkTuple k1 v0 :: b0))
      (assoc_find (assoc_add b0 k1 v0))).
    unfold assoc_eqm in |- *; auto.
    apply assoc_add_egale_cons; auto.
Qed.


Lemma assoc_add_hasmem_choice :
 forall (b0 b : assoc) (k k0 : K) (v v0 : V),
 b = assoc_add b0 k0 v0 ->
 assoc_hasmem b k v -> assoc_hasmem b0 k v \/ k = k0 /\ v = v0. 

Proof.
simple induction b0.
intros; right; rewrite H in H0; generalize H0; simpl in |- *;
 unfold assoc_hasmem in |- *; simpl in |- *.
case (Keq_dec k1 k0); auto.
intros; contradiction.

intros until 2; unfold assoc_hasmem in |- *; simpl in |- *.
induction  a as (k2, v2).
rewrite H0; simpl in |- *.
case (Keq_dec k2 k1).
case (Keq_dec k2 k0).
intros; right.
split.
transitivity k2; auto.

generalize H1; simpl in |- *.
case (Keq_dec k1 k0).
auto.

intro; absurd (k0 = k1); auto.
transitivity k2; auto.

intros until 2; rewrite <- e; simpl in |- *.
case (Keq_dec k2 k0).
  intro; absurd (k2 = k0); assumption.
  intros; left; assumption.

simpl in |- *.
case (Keq_dec k2 k0); simpl in |- *.
tauto.

intros; unfold assoc_hasmem in H; apply H with (assoc_add l k1 v1); auto.
Qed.




(**************************************************)
(* some invariant properties about add and delete *)
(**************************************************)



(* add/mem ******************************)
Lemma assoc_add_mem_invar :
 forall (l l' : assoc) (k k' : K) (v : V),
 l' = assoc_add l k' v -> k' <> k -> assoc_mem l k -> assoc_mem l' k.

Proof.
intros until 2.
cut (assoc_almost_eqm k' (assoc_find l) (assoc_find l')).
unfold assoc_almost_eqm, assoc_mem in |- *.
intro.
replace (assoc_find l' k0) with (assoc_find l k0).
auto.
apply H1; auto.
rewrite H.
apply assoc_almost_eqm_sym.
apply assoc_add_correct_1.
Qed.


Lemma assoc_add_mem_invar_contrap :
 forall (l l' : assoc) (k k' : K) (v : V),
 l' = assoc_add l k' v -> k' <> k -> assoc_mem l' k -> assoc_mem l k.

Proof.
intros until 2.
cut (assoc_almost_eqm k' (assoc_find l) (assoc_find l')).
unfold assoc_almost_eqm, assoc_mem in |- *.
intro.
replace (assoc_find l' k0) with (assoc_find l k0).
auto.

apply H1; auto.

rewrite H.
apply assoc_almost_eqm_sym.
apply assoc_add_correct_1.
Qed.


Lemma assoc_add_not_mem_invar :
 forall (l l' : assoc) (k k' : K) (v' : V),
 l' = assoc_add l k' v' -> k' <> k -> ~ assoc_mem l k -> ~ assoc_mem l' k.

Proof.
intros until 2.
cut (assoc_almost_eqm k' (assoc_find l') (assoc_find l)).
unfold assoc_mem, assoc_almost_eqm in |- *.
intros. replace (assoc_find l' k0) with (assoc_find l k0); auto.
  symmetry  in |- *; apply H1; auto.
rewrite H. apply assoc_add_correct_1.
Qed.


Lemma assoc_add_not_mem_invar_contrap :
 forall (l l' : assoc) (k k' : K) (v' : V),
 l' = assoc_add l k' v' -> k' <> k -> ~ assoc_mem l' k -> ~ assoc_mem l k.

Proof.
intros until 2.
cut (assoc_almost_eqm k' (assoc_find l') (assoc_find l)).
unfold assoc_mem, assoc_almost_eqm in |- *.
intros.
replace (assoc_find l k0) with (assoc_find l' k0); auto.

rewrite H.
apply assoc_add_correct_1.
Qed.


(* add/hasmem ******************************)

Lemma assoc_add_hasmem_invar :
 forall (l l' : assoc) (k k' : K) (v v' : V),
 l' = assoc_add l k' v' ->
 k' <> k -> assoc_hasmem l k v -> assoc_hasmem l' k v.

Proof.
intros until 2.
cut (assoc_almost_eqm k' (assoc_find l) (assoc_find l')).
  unfold assoc_almost_eqm, assoc_hasmem in |- *.
  intro. replace (assoc_find l' k0) with (assoc_find l k0).
     auto.
     apply H1; auto.
  rewrite H.
  apply assoc_almost_eqm_sym.
  apply assoc_add_correct_1.

Qed.


Lemma assoc_add_hasmem_invar_contrap :
 forall (l l' : assoc) (k k' : K) (v v' : V),
 l' = assoc_add l k' v' ->
 k' <> k -> assoc_hasmem l' k v -> assoc_hasmem l k v.

Proof.
intros until 2.
cut (assoc_almost_eqm k' (assoc_find l) (assoc_find l')).
unfold assoc_almost_eqm, assoc_hasmem in |- *.
intro.
replace (assoc_find l' k0) with (assoc_find l k0).
auto.

apply H1; auto.

rewrite H.
apply assoc_almost_eqm_sym.
apply assoc_add_correct_1.
Qed.


Lemma assoc_add_not_hasmem_invar :
 forall (l l' : assoc) (k k' : K) (v v' : V),
 l' = assoc_add l k' v' ->
 k' <> k -> ~ assoc_hasmem l k v -> ~ assoc_hasmem l' k v.

Proof.
intros until 2.
cut (assoc_almost_eqm k' (assoc_find l') (assoc_find l)).
unfold assoc_hasmem, assoc_almost_eqm in |- *; intros.
replace (assoc_find l' k0) with (assoc_find l k0).
auto.

symmetry  in |- *; apply H1; auto.

rewrite H.
apply assoc_add_correct_1.
Qed.


Lemma assoc_add_not_hasmem_invar_contrap :
 forall (l l' : assoc) (k k' : K) (v v' : V),
 l' = assoc_add l k' v' ->
 k' <> k -> ~ assoc_hasmem l' k v -> ~ assoc_hasmem l k v.

Proof.
intros until 2.
cut (assoc_almost_eqm k' (assoc_find l') (assoc_find l)).
unfold assoc_hasmem, assoc_almost_eqm in |- *; intros.
replace (assoc_find l k0) with (assoc_find l' k0).
auto.

apply H1; auto.

rewrite H.
apply assoc_add_correct_1.
Qed.


(* del/mem ******************************)

Lemma assoc_del_mem_invar :
 forall (l l' : assoc) (k k' : K),
 l' = assoc_delete l k' -> k' <> k -> assoc_mem l k -> assoc_mem l' k.

Proof.
intros until 2. rewrite H. unfold assoc_mem in |- *. intros.
replace (assoc_find (assoc_delete l k') k0) with (assoc_find l k0); auto.
cut (assoc_almost_eqm k' (assoc_find l) (assoc_find (assoc_delete l k'))).
  unfold assoc_almost_eqm in |- *; intros; apply H2; auto.
  apply assoc_semfind_del.
Qed.



Lemma assoc_del_mem_invar_contrap :
 forall (l l' : assoc) (k k' : K),
 l' = assoc_delete l k' -> k' <> k -> assoc_mem l' k -> assoc_mem l k.

Proof.
intros until 2. rewrite H. unfold assoc_mem in |- *. intros.
replace (assoc_find l k0) with (assoc_find (assoc_delete l k') k0); auto.
symmetry  in |- *.
cut (assoc_almost_eqm k' (assoc_find l) (assoc_find (assoc_delete l k'))).
  unfold assoc_almost_eqm in |- *; intros; apply H2; auto.
  apply assoc_semfind_del.
Qed.


Lemma assoc_del_not_mem_invar :
 forall (l l' : assoc) (k k' : K),
 l' = assoc_delete l k' -> k' <> k -> ~ assoc_mem l k -> ~ assoc_mem l' k.

Proof.
intros until 2.
cut (assoc_almost_eqm k' (assoc_find l') (assoc_find l)).
unfold assoc_mem, assoc_almost_eqm in |- *; intros.
replace (assoc_find l' k0) with (assoc_find l k0).
auto.
symmetry  in |- *; apply H1; auto.
apply assoc_almost_eqm_sym.
rewrite H; apply assoc_semfind_del.
Qed.


Lemma assoc_del_not_mem_invar_contrap :
 forall (l l' : assoc) (k k' : K),
 l' = assoc_delete l k' -> k' <> k -> ~ assoc_mem l' k -> ~ assoc_mem l k.

Proof.
intros until 2.
cut (assoc_almost_eqm k' (assoc_find l') (assoc_find l)).
unfold assoc_mem, assoc_almost_eqm in |- *; intros.
replace (assoc_find l k0) with (assoc_find l' k0).
auto.
apply H1; auto.
apply assoc_almost_eqm_sym.
rewrite H; apply assoc_semfind_del.
Qed.



(* del/hasmem ******************************)

Lemma assoc_del_hasmem_invar :
 forall (l l' : assoc) (k k' : K) (v : V),
 l' = assoc_delete l k' ->
 k' <> k -> assoc_hasmem l k v -> assoc_hasmem l' k v.

Proof.
intros until 2.
cut (assoc_almost_eqm k' (assoc_find l) (assoc_find l')).
  unfold assoc_almost_eqm, assoc_hasmem in |- *.
  intro. replace (assoc_find l' k0) with (assoc_find l k0).
     auto.
     apply H1; auto.
  rewrite H.
  apply assoc_semfind_del.
Qed.


Lemma assoc_del_hasmem_invar_contrap :
 forall (l l' : assoc) (k k' : K) (v : V),
 l' = assoc_delete l k' ->
 k' <> k -> assoc_hasmem l' k v -> assoc_hasmem l k v.

Proof.
intros until 2.
cut (assoc_almost_eqm k' (assoc_find l) (assoc_find l')).
unfold assoc_almost_eqm, assoc_hasmem in |- *.
intro.
replace (assoc_find l' k0) with (assoc_find l k0); auto.

rewrite H; apply assoc_semfind_del.
Qed.


Lemma assoc_del_not_hasmem_invar :
 forall (l l' : assoc) (k k' : K) (v : V),
 l' = assoc_delete l k' ->
 k' <> k -> ~ assoc_hasmem l k v -> ~ assoc_hasmem l' k v.

Proof.
intros until 2.
cut (assoc_almost_eqm k' (assoc_find l') (assoc_find l)).
unfold assoc_hasmem, assoc_almost_eqm in |- *; intros.
replace (assoc_find l' k0) with (assoc_find l k0); auto.
symmetry  in |- *; apply H1; auto.

apply assoc_almost_eqm_sym.
rewrite H; apply assoc_semfind_del.
Qed.


Lemma assoc_del_not_hasmem_invar_contrap :
 forall (l l' : assoc) (k k' : K) (v : V),
 l' = assoc_delete l k' ->
 k' <> k -> ~ assoc_hasmem l' k v -> ~ assoc_hasmem l k v.

Proof.
intros until 2.
cut (assoc_almost_eqm k' (assoc_find l') (assoc_find l)).
unfold assoc_hasmem, assoc_almost_eqm in |- *; intros.
replace (assoc_find l k0) with (assoc_find l' k0); auto.

apply assoc_almost_eqm_sym.
rewrite H; apply assoc_semfind_del.
Qed.




(**************************************************)
(* miscellanous                                   *)
(**************************************************)



Lemma assoc_unique_key :
 forall (l : assoc) (k : K) (v v' : V),
 assoc_hasmem l k v -> assoc_hasmem l k v' -> v' = v.

Proof.
unfold assoc_hasmem in |- *.
intros l k0 v0 v1.
case (assoc_find l k0); intros.
  contradiction.
  transitivity v2; auto.
Qed.


Lemma assoc_add_find_effect :
 forall (l0 l1 : assoc) (k k' : K) (v v' : V),
 none V = assoc_find l0 k ->
 some V v = assoc_find l1 k -> l1 = assoc_add l0 k' v' -> k' = k /\ v' = v.

Proof.
intros.
rewrite H1 in H0.
 cut (k' = k0).
 split; auto.
 cut (some V v0 = some V v').
 intros. injection H3. auto.
 rewrite H0. rewrite H2. apply assoc_add_correct_2.

generalize H0.
replace (assoc_find (assoc_add l0 k' v') k0) with
 (assoc_find (mkTuple k' v' :: l0) k0).
simpl in |- *. case (Keq_dec k' k0).
  auto.
  intros. absurd (none V = some V v0).
    unfold not in |- *; intro DISCR; discriminate DISCR.
    rewrite H2; rewrite H; trivial.

cut
 (assoc_eqm (assoc_find (mkTuple k' v' :: l0))
    (assoc_find (assoc_add l0 k' v'))).
unfold assoc_eqm in |- *.
  auto.
  apply assoc_add_egale_cons.
Qed.


Lemma assoc_add_mem_effect :
 forall (l0 l1 : assoc) (k k' : K) (v : V),
 ~ assoc_mem l0 k -> assoc_mem l1 k -> l1 = assoc_add l0 k' v -> k' = k.

Proof.
unfold assoc_mem in |- *; intros.
rewrite H1 in H0. generalize H0.
replace (assoc_find (assoc_add l0 k' v0) k0) with
 (assoc_find (mkTuple k' v0 :: l0) k0).
simpl in |- *. case (Keq_dec k' k0). auto.

intros; absurd (assoc_mem l0 k0); unfold assoc_mem in |- *; assumption.

cut
 (assoc_eqm (assoc_find (mkTuple k' v0 :: l0))
    (assoc_find (assoc_add l0 k' v0))).
unfold assoc_eqm in |- *; auto.

apply assoc_add_egale_cons.
Qed.


Lemma assoc_add_hasmem_effect :
 forall (l0 l1 : assoc) (k k' : K) (v v' : V),
 ~ assoc_hasmem l0 k v ->
 assoc_hasmem l1 k v -> l1 = assoc_add l0 k' v' -> k' = k /\ v' = v.

Proof.
unfold assoc_hasmem in |- *; intros.
cut (k' = k0).
  split; auto.
generalize H0; rewrite H1; rewrite H2;
 replace (assoc_find (assoc_add l0 k0 v') k0) with (some V v'); 
 auto.
symmetry  in |- *; apply assoc_add_correct_2.
generalize H0; rewrite H1.
replace (assoc_find (assoc_add l0 k' v') k0) with
 (assoc_find (mkTuple k' v' :: l0) k0).
simpl in |- *. case (Keq_dec k' k0). auto.

intros; absurd (assoc_hasmem l0 k0 v0); unfold assoc_hasmem in |- *;
 assumption.

cut
 (assoc_eqm (assoc_find (mkTuple k' v' :: l0))
    (assoc_find (assoc_add l0 k' v'))).
  unfold assoc_eqm in |- *; auto.
  apply assoc_add_egale_cons.

Qed.


Lemma assoc_del_mem_effect :
 forall (l : assoc) (k k' : K),
 assoc_mem l k -> ~ assoc_mem (assoc_delete l k') k -> k' = k.

Proof.
intros l k0 k1;
 cut (assoc_almost_eqm k1 (assoc_find l) (assoc_find (assoc_delete l k1))).
unfold assoc_almost_eqm in |- *; unfold assoc_mem in |- *.
case (Keq_dec k1 k0); auto.
  intros until 2;
   replace (assoc_find (assoc_delete l k1) k0) with (assoc_find l k0).
    case (assoc_find l k0).
      intros; contradiction.
      unfold not in |- *; tauto.
    apply H; auto.
  apply assoc_semfind_del.
Qed.


Lemma assoc_del_hasmem_effect :
 forall (l : assoc) (k k' : K) (v v' : V),
 assoc_hasmem l k v -> ~ assoc_hasmem (assoc_delete l k') k v -> k' = k.

Proof.
intros l k0 k1;
 cut (assoc_almost_eqm k1 (assoc_find l) (assoc_find (assoc_delete l k1))).
unfold assoc_almost_eqm in |- *; unfold assoc_hasmem in |- *.
case (Keq_dec k1 k0); auto.
intros until 2;
 replace (assoc_find (assoc_delete l k1) k0) with (assoc_find l k0).
case (assoc_find l k0).
intros; contradiction.

unfold not in |- *; tauto.

apply H; auto.

apply assoc_semfind_del.
Qed.




End associative_arrays.



















