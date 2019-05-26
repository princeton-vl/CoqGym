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
Require Import nat_trees.
Require Import search_trees.
Require Import Arith.

Inductive RMAX (t t' : nat_tree) (n : nat) : Prop :=
    rmax_intro :
      occ t n ->
      (forall p : nat, occ t p -> p <= n) ->
      (forall q : nat, occ t' q -> occ t q) ->
      (forall q : nat, occ t q -> occ t' q \/ n = q) ->
      ~ occ t' n -> search t' -> RMAX t t' n.

Hint Resolve rmax_intro: searchtrees.


(* base cases *)

Lemma rmax_nil_nil : forall n : nat, RMAX (bin n NIL NIL) NIL n.
(*******************************************************)
Proof.
 intro n; split; auto with searchtrees arith.
 intros p H; inversion_clear H; auto with searchtrees arith.
 absurd (occ NIL p); auto with searchtrees arith.
 absurd (occ NIL p); auto with searchtrees arith.
 intros q H; inversion_clear H; auto with searchtrees arith.
Defined.


Lemma rmax_t_NIL :
 forall (t : nat_tree) (n : nat),
 search (bin n t NIL) -> RMAX (bin n t NIL) t n.
(************************************************************)
Proof.
 intros t n H; split; auto with searchtrees arith. 
 intros p H0.
 elim (occ_inv n p t NIL H0); intro H1.
 elim H1; auto with searchtrees arith. 
 elim H1; intro H2.
 apply lt_le_weak. 
 elim (maj_l n t NIL H); auto with searchtrees arith.
 absurd (occ NIL p); auto with searchtrees arith.
 intros q H1; elim (occ_inv n q t NIL H1); intros; auto with searchtrees arith.
 elim H0.
 auto with searchtrees arith.
 intro H'; absurd (occ NIL q); auto with searchtrees arith.
 apply not_left with n NIL; auto with searchtrees arith.
 apply search_l with n NIL; auto with searchtrees arith.
Defined.

Hint Resolve rmax_t_NIL: searchtrees.


(* We study the case of a search tree (bin n t1 (bin p t2 t3))  *)

Section RMAX_np.
     Variable n p q : nat.
     Variable t1 t2 t3 t' : nat_tree.
     Hypothesis S1 : search (bin n t1 (bin p t2 t3)).
     Hypothesis R1 : RMAX (bin p t2 t3) t' q.
     Hint Resolve S1 R1: searchtrees.
     
     Remark rmax_1 : occ (bin n t1 (bin p t2 t3)) q.
     (**********************************************)
     Proof.
      elim R1; auto with searchtrees arith.
     Qed.

     Hint Resolve rmax_1: searchtrees.

     Remark rmax_2 : n < p.
     (**********************)
     Proof.
      elim (min_r _ _ _ S1); auto with searchtrees arith.
     Qed.

     Hint Resolve rmax_2: searchtrees.
     
     Remark rmax_3 : min n t'. 
     (************************)
     Proof.
      apply min_intro.
      intros q' H.
      elim R1; intros.
      elim (min_r _ _ _ S1); auto with searchtrees arith.
     Qed.
     Hint Resolve rmax_3: searchtrees.
     
     Remark rmax_4 : search (bin n t1 t').
     (************************************)
     Proof.
      apply bin_search.
      apply search_l with n (bin p t2 t3); auto with searchtrees arith. 
      elim R1; auto with searchtrees arith.
      apply maj_l with (bin p t2 t3); auto with searchtrees arith.
      auto with searchtrees arith.
     Qed. 

     Hint Resolve rmax_4: searchtrees.
     
     Remark rmax_5 : n < q.
     (**********************)
     Proof.
      elim R1; intros; apply lt_le_trans with p; auto with searchtrees arith.
     Qed.

     Hint Resolve rmax_5: searchtrees.

     Remark rmax_6 :
      forall p0 : nat, occ (bin n t1 (bin p t2 t3)) p0 -> p0 <= q.
     (******************************************************************)
     Proof.
      intros p0 H.
      elim R1.
      intros H0 H1 H2 H3 H4 H5.
      elim (occ_inv _ _ _ _ H); intro H6.
      elim H6; auto with searchtrees arith.
      elim H6; intro H7.
      elim (maj_l _ _ _ S1). 
      intro H8.
      cut (p0 < n); auto with searchtrees arith.
      intro; apply lt_le_weak.
      apply lt_trans with n; auto with searchtrees arith.
      elim (min_r _ _ _ S1); auto with searchtrees arith.
     Qed.

     Hint Resolve rmax_6: searchtrees.
     
     Remark rmax_7 :
      forall q' : nat,
      occ (bin n t1 t') q' -> occ (bin n t1 (bin p t2 t3)) q'.
     (*******************************************************)
     Proof.
      intros q' H; elim (occ_inv _ _ _ _ H); intro H0.
      elim H0; auto with searchtrees arith.
      elim H0; auto with searchtrees arith. 
      intro H1; elim R1; auto with searchtrees arith.
     Qed.

     Hint Resolve rmax_7: searchtrees.
     
     Remark rmax_8 : ~ occ (bin n t1 t') q.
     (************************************)
     Proof.
      unfold not in |- *; intro F.
      elim (occ_inv _ _ _ _ F).
      intro eg; absurd (n < q); auto with searchtrees arith.
      elim eg; auto with searchtrees arith.
      simple induction 1; intro H1.
      absurd (occ t1 q); auto with searchtrees arith. 
      apply not_left with n (bin p t2 t3); auto with searchtrees arith.
      elim R1; auto with searchtrees arith.
     Qed.

     Hint Resolve rmax_8: searchtrees.

     Remark rmax_9 :
      forall q0 : nat,
      occ (bin n t1 (bin p t2 t3)) q0 -> occ (bin n t1 t') q0 \/ q = q0.
     (****************************************)
     Proof.
      intros q0 H.
      elim (occ_inv _ _ _ _ H).
      simple induction 1; left; auto with searchtrees arith.
      simple induction 1; intro H'.
      left; auto with searchtrees arith.
      elim R1; intros H1 H2 H3 H4 H5 H6.
      elim (H4 _ H'); auto with searchtrees arith.
     Qed.

     Hint Resolve rmax_9: searchtrees.

     Lemma rmax_t1_t2t3 : RMAX (bin n t1 (bin p t2 t3)) (bin n t1 t') q.
     (*******************************************************************)
     Proof.
      apply rmax_intro; auto with searchtrees arith.
     Qed.

End RMAX_np.

Hint Resolve rmax_t1_t2t3: searchtrees.


Lemma rmax :
 forall t : nat_tree,
 search t -> binp t -> {q : nat &  {t' : nat_tree | RMAX t t' q}}.
(*********************************************)
Proof.

simple induction t;
 [ intros s b; exists 0; exists NIL
 | intros n t1 hr1 t2; case t2;
    [ intros hr2 s b; exists n; exists t1
    | intros n' t1' t2' hr2 s b; elim hr2;
       [ intros num ex; elim ex; intros tr htr; exists num;
          exists (bin n t1 tr)
       | idtac
       | idtac ] ] ]; auto with searchtrees arith.
absurd (binp NIL); auto with searchtrees arith.
eapply search_r; eauto with searchtrees arith.

(*
 Refine 
 Fix rmax{rmax/1 : (t:nat_tree)(search t)->(binp t)->
        {q:nat & {t':nat_tree | (RMAX t t' q)}} :=
  [t][ty:=[q]{t':nat_tree | (RMAX t t' q)}]
    <[t](search t)->(binp t)->{q :nat & (ty q)}>Cases t of 
       NIL => [s,b](existS ? ty O (exist ? ? NIL ?))
      |(bin n t1 NIL) => [s,b](existS ? ty n (exist ? ? t1 ?))
      |(bin n t1 t2) => [s,b]Cases (rmax t2 ? ?) of 
             (existS num (exist tr _)) => 
                (existS ? ty num (exist ? ? (bin n t1 tr) ?))
            end
      end}.
*)
(*
 Realizer Fix rmax{rmax/1 : nat_tree -> nat*nat_tree :=
                   [t:nat_tree]<nat*nat_tree>
                      Cases t of
                        NIL => (O,NIL)
                      | (bin n t1 NIL) => (n,t1)
                      | (bin n t1 t2) =>
         		    <nat*nat_tree>let (num,tr) =   (rmax t2) 
                             in (num,(bin n t1 tr)) end
                         }.
 Program_all. 
*)
Defined.
