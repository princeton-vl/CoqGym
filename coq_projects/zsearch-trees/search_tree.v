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

Global Set Asymmetric Patterns.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Standard Proposition Elimination Names.

Require Extraction.
Require Export ZArith_base.


Inductive Z_btree : Set :=
  | Z_leaf : Z_btree
  | Z_bnode : Z -> Z_btree -> Z_btree -> Z_btree.


Inductive Binp : Z_btree -> Prop :=
    Binp_intro : forall (n : Z) (t1 t2 : Z_btree), Binp (Z_bnode n t1 t2).

Hint Resolve Binp_intro: searchtrees.

Inductive occ (n : Z) : Z_btree -> Prop :=
  | occ_root : forall t1 t2 : Z_btree, occ n (Z_bnode n t1 t2)
  | occ_l :
      forall (p : Z) (t1 t2 : Z_btree), occ n t1 -> occ n (Z_bnode p t1 t2)
  | occ_r :
      forall (p : Z) (t1 t2 : Z_btree), occ n t2 -> occ n (Z_bnode p t1 t2).

Hint Resolve occ_root occ_l occ_r: searchtrees.


Derive Inversion_clear OCC_INV with
 (forall (z z' : Z) (t1 t2 : Z_btree), occ z' (Z_bnode z t1 t2)).



Lemma occ_inv :
 forall (z z' : Z) (t1 t2 : Z_btree),
 occ z' (Z_bnode z t1 t2) -> z = z' \/ occ z' t1 \/ occ z' t2.
Proof.
 intros z z' t1 t2 H.
 inversion H using OCC_INV; auto with searchtrees.
Qed.

Hint Resolve occ_inv: searchtrees.

Lemma not_occ_Leaf : forall z : Z, ~ occ z Z_leaf.
Proof.
 unfold not in |- *; intros z H.
 inversion_clear H.
Qed.

Hint Resolve not_occ_Leaf: searchtrees.

Definition naive_sch : forall (n : Z) (t : Z_btree), {occ n t} + {~ occ n t}.
 simple induction t.
 right; auto with searchtrees.
 intros z t0 H0 t1 H1.
 case (Z_eq_dec n z).
 simple induction 1; left; auto with searchtrees.
 case H0; case H1; intros; auto with searchtrees.
 right; intro H; elim (occ_inv H); auto with searchtrees.
 tauto.
Defined.


Extraction naive_sch.

(*
let rec naive_sch n = function
  Z_leaf -> right
| Z_bnode (z1, z0, z) ->
    (match Z_eq_dec n z1 with
       left -> left
     | right ->
         (match naive_sch n z0 with
            left -> left
          | right -> naive_sch n z))
*)




Inductive min (z : Z) (t : Z_btree) : Prop :=
    min_intro : (forall z' : Z, occ z' t -> (z < z')%Z) -> min z t.

Hint Resolve min_intro: searchtrees.

(* p is greater than every member of t *)

Inductive maj (z : Z) (t : Z_btree) : Prop :=
    maj_intro : (forall z' : Z, occ z' t -> (z' < z)%Z) -> maj z t.

Hint Resolve maj_intro: searchtrees.


Inductive search : Z_btree -> Prop :=
  | leaf_search : search Z_leaf
  | bnode_search :
      forall (z : Z) (t1 t2 : Z_btree),
      search t1 ->
      search t2 -> maj z t1 -> min z t2 -> search (Z_bnode z t1 t2).

Hint Resolve leaf_search bnode_search: searchtrees.

Lemma min_leaf : forall z : Z, min z Z_leaf.
Proof.
 intro z; apply min_intro.
 intros z' H; inversion_clear H.
Qed.

Hint Resolve min_leaf: searchtrees.

Lemma maj_leaf : forall z : Z, maj z Z_leaf.
Proof.
 intro z; apply maj_intro.
 intros z' H; inversion_clear H.
Qed.

Hint Resolve maj_leaf: searchtrees.

Lemma maj_not_occ : forall (z : Z) (t : Z_btree), maj z t -> ~ occ z t.
Proof.
 unfold not in |- *; intros z t H H'.
 elim H; intros; absurd (z < z)%Z; auto.
 apply Zlt_irrefl.
Qed.

Hint Resolve maj_not_occ: searchtrees.

Lemma min_not_occ : forall (z : Z) (t : Z_btree), min z t -> ~ occ z t.
Proof.
 unfold not in |- *; intros z t H H'.
 elim H; intros; absurd (z < z)%Z; auto.
 apply Zlt_irrefl.
Qed.


Hint Resolve min_not_occ: searchtrees.

Section search_tree_basic_properties.

 Variable n : Z.
 Variable t1 t2 : Z_btree.
 Hypothesis se : search (Z_bnode n t1 t2).

 Lemma search_l : search t1.
 Proof.
  inversion_clear se; auto with searchtrees.
 Qed.

 Hint Resolve search_l: searchtrees.

 Lemma search_r : search t2.
 Proof.
  inversion_clear se; auto with searchtrees.
 Qed.
 Hint Resolve search_r: searchtrees.

 Lemma maj_l : maj n t1.
 Proof.
  inversion_clear se; auto with searchtrees.
 Qed.
 Hint Resolve maj_l: searchtrees.

 Lemma min_r : min n t2.
 Proof.
  inversion_clear se; auto with searchtrees.
 Qed.
 Hint Resolve min_r: searchtrees.

 Lemma not_right : forall p : Z, (p <= n)%Z -> ~ occ p t2.
 Proof.
  intros p H; elim min_r.
  unfold not in |- *; intros; absurd (n < p)%Z; auto with searchtrees.
  apply Zle_not_lt; assumption.
 Qed.

 Hint Resolve not_right: searchtrees.
 
 Lemma not_left : forall p : Z, (p >= n)%Z -> ~ occ p t1.
 Proof.
  intros p H; elim maj_l.
  unfold not in |- *; intros; absurd (p < n)%Z; auto with searchtrees.
 Qed.

 Hint Resolve not_left: searchtrees.

 Lemma go_left :
  forall p : Z, occ p (Z_bnode n t1 t2) -> (p < n)%Z -> occ p t1.
 Proof.
  intros p H H0.    
  elim (occ_inv H).
  simple induction 1; absurd (p < n)%Z. 
  rewrite H1; apply Zle_not_lt; auto with zarith. 
  assumption.
  simple destruct 1; trivial.
  intro H2; absurd (occ p t2).
  apply not_right.
  apply Zlt_le_weak; assumption. 
  auto.
 Qed.

 Lemma go_right :
  forall p : Z, occ p (Z_bnode n t1 t2) -> (p > n)%Z -> occ p t2.
 Proof.
  intros p H H0.    
  elim (occ_inv H).
  simple induction 1; absurd (n < p)%Z. 
  rewrite H1; apply Zle_not_lt; auto with zarith. 
  apply Zgt_lt; assumption.
  simple destruct 1.    
  intro H2; absurd (occ p t1).
  apply not_left.
  unfold Zge in |- *; rewrite H0; discriminate. 
  auto.
  auto.
 Qed.

End search_tree_basic_properties.

Hint Resolve go_left go_right not_left not_right search_l search_r maj_l
  min_r: searchtrees.

Definition sch_spec (p : Z) (t : Z_btree) :=
  search t -> {occ p t} + {~ occ p t}.

Definition sch : forall (p : Z) (t : Z_btree), sch_spec p t.
 refine
  (fix sch (p : Z) (t : Z_btree) {struct t} : sch_spec p t :=
     match t as x return (sch_spec p x) with
     | Z_leaf => fun h => right _ _
     | Z_bnode n t1 t2 =>
         fun h =>
         match Z_le_gt_dec p n with
         | left h1 =>
             match Z_le_lt_eq_dec p n h1 with
             | left h'1 =>
                 match sch p t1 _ with
                 | left h''1 => left _ _
                 | right h''2 => right _ _
                 end
             | right h'2 => left _ _
             end
         | right h2 =>
             match sch p t2 _ with
             | left h''1 => left _ _
             | right h''2 => right _ _
             end
         end
     end); eauto with searchtrees.
 rewrite h'2; auto with searchtrees.
Defined.

Extraction sch.
(*
let rec sch p t x =
  match t with
    Z_leaf -> right
  | Z_bnode (n, t1, t2) ->
      (match Z_le_gt_dec p n with
         left ->
           (match match Zcompare p n with
                    EGAL -> right
                  | INFERIEUR -> left
                  | SUPERIEUR -> assert false  with
              left -> sch p t1 prop
            | right -> left)
       | right -> sch p t2 prop)
*)


(* 
 Definition of an INSERT predicate (a la  Prolog)
***************************************************

We begin with the definition of a predicate:

(INSERT n t t') if t' is a binary search tree containing exactly
  n and the elements of t *)

Inductive INSERT (n : Z) (t t' : Z_btree) : Prop :=
    insert_intro :
      (forall p : Z, occ p t -> occ p t') ->
      occ n t' ->
      (forall p : Z, occ p t' -> occ p t \/ n = p) ->
      search t' -> INSERT n t t'.

Hint Resolve insert_intro: searchtrees.


Definition insert_spec (n : Z) (t : Z_btree) :=
  search t -> {t' : Z_btree | INSERT n t t'}.

Lemma insert_leaf : forall n : Z, INSERT n Z_leaf (Z_bnode n Z_leaf Z_leaf).
Proof.
 intro n; split; auto with searchtrees.
 intros p H; inversion_clear H; auto with searchtrees. 
Defined.
Hint Resolve insert_leaf: searchtrees.



(* Inserting in the left son *)

Lemma insert_l :
 forall (n p : Z) (t1 t'1 t2 : Z_btree),
 (n < p)%Z ->
 search (Z_bnode p t1 t2) ->
 INSERT n t1 t'1 -> INSERT n (Z_bnode p t1 t2) (Z_bnode p t'1 t2).
Proof.
 intros n p t1 t'1 t2 H H0 H1; split.
 intros p0 H2; inversion_clear H2.
 auto with searchtrees.
 elim H1; auto with searchtrees.
 auto with searchtrees.
 constructor 2; elim H1; auto with searchtrees.
 intros p0 H2.
 inversion_clear H2.
 auto with searchtrees.
 elim H1; intros. 
 elim (H5 p0); auto with searchtrees.
 auto with searchtrees.
 elim H1; constructor 2; auto with searchtrees.
 eapply search_r; eauto with searchtrees.
 split; intros.
 elim (H4 z').
 intro; cut (maj p t1).
 simple induction 1; auto with searchtrees.
 eapply maj_l; eauto with searchtrees.
 simple induction 1; auto with searchtrees.
 auto with searchtrees.
 eapply min_r; eauto with searchtrees.
Defined.


Lemma insert_r :
 forall (n p : Z) (t1 t2 t'2 : Z_btree),
 (n > p)%Z ->
 search (Z_bnode p t1 t2) ->
 INSERT n t2 t'2 -> INSERT n (Z_bnode p t1 t2) (Z_bnode p t1 t'2).
(*******************************************************)
Proof.
 intros n p t1 t2 t'2 H H0 H1; split.
 intros p0 H2; inversion_clear H2; auto with searchtrees.
 elim H1; auto with searchtrees.
 constructor 3; elim H1; auto with searchtrees.
 intros p0 H2; inversion_clear H2; auto with searchtrees.
 elim H1; intros. 
 elim (H5 p0); auto with searchtrees.
 elim H1; constructor 2; auto with searchtrees.
 eapply search_l; eauto with searchtrees.
 split; intros.
 elim (maj_l H0); auto with searchtrees.
 split; intros q H6.
 elim (H4 q H6).
 intro.
 elim (min_r H0); auto with searchtrees.
 simple induction 1; auto with searchtrees.
 apply Zgt_lt.
 assumption.
Defined.



Lemma insert_eq :
 forall (n : Z) (t1 t2 : Z_btree),
 search (Z_bnode n t1 t2) -> INSERT n (Z_bnode n t1 t2) (Z_bnode n t1 t2).
Proof.
 auto with searchtrees.
Defined.

Hint Resolve insert_l insert_r insert_eq: searchtrees.



Lemma insert : forall (n : Z) (t : Z_btree), insert_spec n t.
Proof.
 refine
  (fix insert (n : Z) (t : Z_btree) {struct t} : insert_spec n t :=
     match t return (insert_spec n t) with
     | Z_leaf => fun s => exist _ (Z_bnode n Z_leaf Z_leaf) _
     | Z_bnode p t1 t2 =>
         fun s =>
         match Z_le_gt_dec n p with
         | left h =>
             match Z_le_lt_eq_dec n p h with
             | left _ =>
                 match insert n t1 _ with
                 | exist t3 _ => exist _ (Z_bnode p t3 t2) _
                 end
             | right e => exist _ (Z_bnode n t1 t2) _
             end
         | right _ =>
             match insert n t2 _ with
             | exist t3 _ => exist _ (Z_bnode p t1 t3) _
             end
         end
     end); eauto with searchtrees.
 rewrite e; eauto with searchtrees.
Defined.
Hint Resolve insert: searchtrees.

Extraction insert.

(*
let rec insert n t x =
  match t with
    Z_leaf -> Z_bnode (n, Z_leaf, Z_leaf)
  | Z_bnode (p, t1, t2) ->
      (match Z_le_gt_dec n p with
         left ->
           (match match Zcompare n p with
                    EGAL -> right
                  | INFERIEUR -> left
                  | SUPERIEUR -> assert false  with
              left -> Z_bnode (p, (insert n t1 prop), t2)
            | right -> Z_bnode (n, t1, t2))
       | right -> Z_bnode (p, t1, (insert n t2 prop)))

*)



Require Export List.

Hint Resolve in_nil: searchtrees.

Hint Resolve in_inv: searchtrees.


(* Construction of a binary search tree containing the elements of
  a list of integers *)


Definition list2trees_spec (l : list Z) :=
  {t : Z_btree | search t /\ (forall p : Z, In p l <-> occ p t)}.
   

Definition list2trees_aux_spec (l : list Z) (t : Z_btree) :=
  search t ->
  {t' : Z_btree |
  search t' /\ (forall p : Z, In p l \/ occ p t <-> occ p t')}.
   

Definition list2trees_aux :
  forall (l : list Z) (t : Z_btree), list2trees_aux_spec l t.

refine
 (fix list2trees_aux (l : list Z) (t : Z_btree) {struct l} :
    list2trees_aux_spec l t :=
    match l return (list2trees_aux_spec l t) with
    | nil => fun s => exist _ t _
    | p :: l' =>
        fun s =>
        match insert p (t:=t) s with
        | exist t' i =>
            match list2trees_aux l' t' _ with
            | exist t'' a => exist _ t'' _
            end
        end
    end).
 split; auto.
 split; auto.
 simple induction 1; auto.
 intro H0; inversion H0.
 case i; auto.
 case a; auto.
 intros; split; auto.
 intros.
 case a.
 intros.
 split; auto.
 simple induction 1; intro H4.
 simpl in H4.
 case H4.
 simple induction 1.
 case (H2 p); intros.
 apply H6.
 right.
 case i; auto.
 case (H2 p0); auto. 
 case (H2 p0); auto.
 intros.
 apply H5; right.
 elim i; auto.
 intros.
 case a; auto.
 intros.
 case (H5 p0).
 intros.
 case (H7 H3).
 left; auto.
 simpl in |- *; auto.
 case i.
 intros.
 case (H10 p0 H12).
 auto.
 simple induction 1; simpl in |- *; auto.
Defined.

Definition list2trees : forall l : list Z, list2trees_spec l.
 refine
  (fun l =>
   match list2trees_aux l (t:=Z_leaf) _ with
   | exist t a => exist _ t _
   end).
 eauto with searchtrees.
 case a; auto.
 split; auto.
 intro p; split; case (H0 p).
 auto.
 intros H1 H2 H3.
 case (H2 H3); auto.
 inversion 1.
Defined.

Extraction list2trees_aux. 


(*
let rec list2trees_aux l t x =
  match l with
    nil -> t
  | cons (p, l') -> list2trees_aux l' (insert p t prop) prop
*)




Extraction list2trees.

(*
let list2trees l =
  list2trees_aux l Z_leaf prop
*)



Inductive RMAX (t t' : Z_btree) (n : Z) : Prop :=
    rmax_intro :
      occ n t ->
      (forall p : Z, occ p t -> (p <= n)%Z) ->
      (forall q : Z, occ q t' -> occ q t) ->
      (forall q : Z, occ q t -> occ q t' \/ n = q) ->
      ~ occ n t' -> search t' -> RMAX t t' n.

Hint Resolve rmax_intro: searchtrees.


(* base cases *)

Lemma rmax_leaf_leaf : forall n : Z, RMAX (Z_bnode n Z_leaf Z_leaf) Z_leaf n.
Proof.
 intro n; split; auto with searchtrees.
 intros p H; inversion_clear H; auto with searchtrees.
 apply Zle_refl.
 absurd (occ p Z_leaf); auto with searchtrees.
 absurd (occ p Z_leaf); auto with searchtrees.
 intros q H; inversion_clear H; auto with searchtrees.
Qed.


Lemma rmax_t_Z_leaf :
 forall (t : Z_btree) (n : Z),
 search (Z_bnode n t Z_leaf) -> RMAX (Z_bnode n t Z_leaf) t n.

Proof.
 intros t n H; split; auto with searchtrees. 
 intros p H0.
 elim (occ_inv H0); intro H1.
 elim H1; auto with zarith.
 elim H1; intro H2.
 apply Zlt_le_weak.  
 elim (maj_l H). 
 auto. 
 absurd (occ p Z_leaf); auto with searchtrees.
 intros q H1. 
 elim (occ_inv H1); intros; auto with searchtrees.
 elim H0.
 auto. 
 intro H'; absurd (occ q Z_leaf); auto with searchtrees.  
 apply not_left with n Z_leaf; auto with searchtrees.
 auto with zarith.
 apply Zle_ge.
 auto with zarith.
 eauto with searchtrees. 
Qed. 

Hint Resolve rmax_t_Z_leaf: searchtrees.


(* We study the case of a search tree (Z_bnode n t1 (Z_bnode p t2 t3))  *)

Section RMAX_np.
     Variable n p q : Z.
     Variable t1 t2 t3 t' : Z_btree.
     Hypothesis S1 : search (Z_bnode n t1 (Z_bnode p t2 t3)).
     Hypothesis R1 : RMAX (Z_bnode p t2 t3) t' q.
     Hint Resolve S1 R1: searchtrees.
     
     Remark rmax_1 : occ q (Z_bnode n t1 (Z_bnode p t2 t3)).
     Proof.
      elim R1; auto with searchtrees.
     Qed.

     Hint Resolve rmax_1: searchtrees.

     Remark rmax_2 : (n < p)%Z.
     Proof.
      elim (min_r S1); auto with searchtrees.
     Qed.

     Hint Resolve rmax_2: searchtrees.
     
     Remark rmax_3 : min n t'. 
     Proof.
      apply min_intro.
      intros q' H.
      elim R1; intros.
      elim (min_r S1); auto with searchtrees.
     Qed.
     Hint Resolve rmax_3: searchtrees.
     
     Remark rmax_4 : search (Z_bnode n t1 t').
     Proof.
      right.
      apply search_l with n (Z_bnode p t2 t3); auto with searchtrees. 
      elim R1; auto with searchtrees.
      apply maj_l with (Z_bnode p t2 t3); auto with searchtrees.
      auto with searchtrees.
     Qed. 

     Hint Resolve rmax_4: searchtrees.
     
     Remark rmax_5 : (n < q)%Z.
     Proof.
      elim R1; intros; apply Zlt_le_trans with p; auto with searchtrees.
     Qed.

     Hint Resolve rmax_5: searchtrees.

     Remark rmax_6 :
      forall p0 : Z, occ p0 (Z_bnode n t1 (Z_bnode p t2 t3)) -> (p0 <= q)%Z.

     Proof.
      intros p0 H.
      elim R1.
      intros H0 H1 H2 H3 H4 H5.
      elim (occ_inv H); intro H6.
      elim H6; apply Zlt_le_weak; auto with searchtrees zarith.
      elim H6; intro H7.
      elim (maj_l S1). 
      intro H8.
      cut (p0 < n)%Z; auto with searchtrees.
      intro; apply Zlt_le_weak.
      apply Zlt_trans with n; auto with searchtrees.
      elim (min_r S1); auto with searchtrees.
     Qed.

     Hint Resolve rmax_6: searchtrees.
     
     Remark rmax_7 :
      forall q' : Z,
      occ q' (Z_bnode n t1 t') -> occ q' (Z_bnode n t1 (Z_bnode p t2 t3)).
     Proof.
      intros q' H; elim (occ_inv H); intro H0.
      elim H0; auto with searchtrees.
      elim H0; auto with searchtrees. 
      intro H1; elim R1; auto with searchtrees.
     Qed.

     Hint Resolve rmax_7: searchtrees.
     
     Remark rmax_8 : ~ occ q (Z_bnode n t1 t').
     Proof.
      unfold not in |- *; intro F.
      elim (occ_inv F).
      intro eg.
      absurd (n < q)%Z.
      rewrite eg.
      apply Zlt_irrefl.
      auto with searchtrees.
      simple induction 1; intro H1.
      absurd (occ q t1); auto with searchtrees. 
      apply not_left with n (Z_bnode p t2 t3); auto with searchtrees.
      apply Zle_ge; elim R1; auto with searchtrees.
      elim R1.
      intros.
      absurd (occ q t'); auto.
     Qed.

     Hint Resolve rmax_8: searchtrees.

     Remark rmax_9 :
      forall q0 : Z,
      occ q0 (Z_bnode n t1 (Z_bnode p t2 t3)) ->
      occ q0 (Z_bnode n t1 t') \/ q = q0.
     Proof.
      intros q0 H.
      elim (occ_inv H).
      simple induction 1; left; auto with searchtrees.
      simple induction 1; intro H'.
      left; auto with searchtrees.
      elim R1; intros H1 H2 H3 H4 H5 H6.
      elim (H4 _ H'); auto with searchtrees.
     Qed.

     Hint Resolve rmax_9: searchtrees.

     Lemma rmax_t1_t2t3 :
      RMAX (Z_bnode n t1 (Z_bnode p t2 t3)) (Z_bnode n t1 t') q.
     Proof.
      apply rmax_intro; auto with searchtrees.
     Qed.

End RMAX_np.

Hint Resolve rmax_t1_t2t3: searchtrees.

Definition rmax_sig (t : Z_btree) (q : Z) := {t' : Z_btree | RMAX t t' q}. 

Definition rmax_spec (t : Z_btree) :=
  search t -> Binp t -> {q : Z &  rmax_sig t q}.

Definition rmax : forall t : Z_btree, rmax_spec t.
 refine
  (fix rmax (t : Z_btree) : rmax_spec t :=
     match t as x return (rmax_spec x) with
     | Z_leaf => fun h h' => False_rec _ _
     | Z_bnode r t1 t2 =>
         match
           t2 as z
           return (rmax_spec z -> z = t2 -> rmax_spec (Z_bnode r t1 z))
         with
         | Z_leaf =>
             fun h h' h'' h''' =>
             existS (fun q : Z => rmax_sig (Z_bnode r t1 Z_leaf) q) r
               (exist _ t1 _)
         | Z_bnode n' t'1 t'2 =>
             fun h h' h'' h''' =>
             match rmax t2 _ _ with
             | existS num (exist t' _) =>
                 existS
                   (fun q : Z =>
                    rmax_sig (Z_bnode r t1 (Z_bnode n' t'1 t'2)) q) num
                   (exist _ (Z_bnode r t1 t') _)
             end
         end _ _
     end).
 inversion h'.
 auto with searchtrees.
 case h'; eauto with searchtrees.
 case h'; eauto with searchtrees.
 rewrite h'; eauto with searchtrees.
 case h'; apply rmax_t1_t2t3. 
 auto.
 rewrite h'; auto.
 auto.
 auto.
Defined.



(* VI    Deletion.
******************
*******************


  Deleting an element from a binary search tree is a little more
  complex than inserting or searching.
  The difficult case is the deletion of the root of a tree; we have
  to reconstruct a search tree. To solve this problem, we define
  an auxiliary operation: deleting the greatest element of a non-empty
  binary search tree.
*)

(* VI.2  Deletion in general
****************************

  We are now ready to study the remove operation in it's generality:
 (RM n t t') if t' is a search tree obtained by removing n from t *)


Inductive RM (n : Z) (t t' : Z_btree) : Prop :=
    rm_intro :
      ~ occ n t' ->
      (forall p : Z, occ p t' -> occ p t) ->
      (forall p : Z, occ p t -> occ p t' \/ n = p) -> search t' -> RM n t t'.

Definition RM_SPEC (n : Z) (t : Z_btree) := {t' : Z_btree | RM n t t'}.

Hint Resolve rm_intro: searchtrees.


(* base cases *)

Remark RM_0 : forall n : Z, RM n Z_leaf Z_leaf.
Proof.
 intro n; apply rm_intro; auto with searchtrees.
Qed.

Hint Resolve RM_0: searchtrees.


Remark RM_1 : forall n : Z, RM n (Z_bnode n Z_leaf Z_leaf) Z_leaf.
Proof.
 intros; apply rm_intro; auto with searchtrees.
 intros p H; elim (occ_inv H); auto with searchtrees.
 tauto.
Qed.

Hint Resolve RM_1: searchtrees.


(* deleting in the left son *)

Remark rm_left :
 forall (n p : Z) (t1 t2 t' : Z_btree),
 (p < n)%Z ->
 search (Z_bnode n t1 t2) ->
 RM p t1 t' -> RM p (Z_bnode n t1 t2) (Z_bnode n t' t2).
Proof.
 intros n p t1 t2 t' H H0 H1.
 apply rm_intro. unfold not in |- *; intro H2.
 elim (occ_inv H2).
 intro eg; apply Zlt_irrefl with n.
 pattern n at 1 in |- *; rewrite eg; auto.  
 intro D; elim D; intro H3. 
 elim H1; auto with searchtrees.
 absurd (occ p t2); auto with searchtrees.
 apply not_right with n t1; auto with searchtrees.
 apply Zlt_le_weak; auto with searchtrees.
 intros p0 H2.
 elim (occ_inv H2).
 simple induction 1; auto with searchtrees.
 simple induction 1; auto with searchtrees.
 intro; elim H1; auto with searchtrees.
 auto with searchtrees.
 intros p0 H2.
 elim (occ_inv H2).
 simple induction 1; auto with searchtrees.
 simple induction 1; intro H4.
 elim H1.
 intros H5 H6 H7 H8.
 elim (H7 p0 H4); auto with searchtrees.
 auto with searchtrees.
 auto with searchtrees.
 right. 
 elim H1; auto with searchtrees.
 apply search_r with n t1; auto with searchtrees.
 apply maj_intro; intros q H2.
 cut (occ q t1).
 intro; elim (maj_l H0); intros; auto with searchtrees.
 auto with searchtrees.
 elim H1; auto with searchtrees.
 apply min_r with t1; auto with searchtrees.
Qed.

Hint Resolve rm_left: searchtrees.


(* deleting in the right son *)

Remark rm_right :
 forall (n p : Z) (t1 t2 t' : Z_btree),
 (n < p)%Z ->
 search (Z_bnode n t1 t2) ->
 RM p t2 t' -> RM p (Z_bnode n t1 t2) (Z_bnode n t1 t').

Proof.
 intros n p t1 t2 t' H H0 H1.
 apply rm_intro.
 unfold not in |- *; intro H2.
 elim (occ_inv H2).
 intro eg; apply Zlt_irrefl with p; auto with searchtrees.
 pattern p at 1 in |- *; rewrite <- eg; auto with searchtrees.
 intro D; elim D; intro H3. 
 elim H1; auto with searchtrees.
 absurd (occ p t1).
 apply not_left with n t2; auto with searchtrees.
 auto with searchtrees.
 apply Zle_ge; apply Zlt_le_weak; auto.
 assumption.
 elim H1; intros; absurd (occ p t'); auto.
 intros p0 H2.
 elim (occ_inv H2).
 simple induction 1; auto with searchtrees.
 simple induction 1; auto with searchtrees.
 intro; elim H1; auto with searchtrees.
 intros p0 H2.
 elim (occ_inv H2).
 simple induction 1; auto with searchtrees.
 simple induction 1; auto with searchtrees.
 intro H4.
 elim H1; intros H5 H6 H7 H8.
 elim (H7 p0 H4); auto with searchtrees.
 right.
 eauto with searchtrees.
 elim H1; auto.
 eauto with searchtrees.
 eauto with searchtrees.
 eapply min_r.
 elim H1; intros H2 H3 H4 H5.
 inversion_clear H0.
 constructor 2.
 apply H6.
 auto.
 auto.
 elim H9.
 intros.
 split; intros.
 apply H0.
 elim H1; auto with searchtrees.
Qed.

Hint Resolve rm_right: searchtrees.


(* base case for deleting the root *)

Remark rm_root_base_case :
 forall (n : Z) (t : Z_btree),
 search (Z_bnode n Z_leaf t) -> RM n (Z_bnode n Z_leaf t) t.
Proof.
 intros; apply rm_intro.
 apply not_right with n Z_leaf; auto with searchtrees.
 auto with searchtrees.
 auto with zarith.
 auto with searchtrees.
 intros p H1; elim (occ_inv H1); intro H2.
 right; auto.
 elim H2; intro.
 absurd (occ p Z_leaf); auto.
 auto with searchtrees.
 auto.
 apply search_r with n Z_leaf; auto with searchtrees.
Qed.

Hint Resolve rm_root_base_case: searchtrees.


(* General case: we use the RMAX predicate *)

Section rm_root.
     Variable n p : Z.
     Variable t1 t2 t' : Z_btree.
     Hypothesis S : search (Z_bnode n (Z_bnode p t1 t2) t').
     Variable q : Z.
     Variable t0 : Z_btree.
     Hypothesis R : RMAX (Z_bnode p t1 t2) t0 q.
     Hint Resolve S: searchtrees.
     
     Remark rm_2 : (q < n)%Z.
     (********************)
     Proof.
      elim R.
      intros.
      elim (maj_l (n:=n) (t1:=Z_bnode p t1 t2) (t2:=t')).
      auto.
      auto with searchtrees.
     Qed.

     Hint Resolve rm_2: searchtrees.
     
     Remark rm_3 : ~ occ n (Z_bnode q t0 t').
     Proof.
      unfold not in |- *; intro H.
      elim (occ_inv H).
      intro eg; absurd (q < q)%Z; auto with searchtrees.
      apply Zlt_irrefl.
      pattern q at 2 in |- *; rewrite eg; auto with searchtrees.
      intro D; elim D; intro H'.
      elim R; intros H0 H1 H2 H3 H4 H5.
      absurd (occ n (Z_bnode p t1 t2)); auto with searchtrees.
      apply not_left with n t'; auto with searchtrees.
      apply Zle_ge; auto with zarith.
      absurd (occ n t'); auto with searchtrees.
      apply not_right with n (Z_bnode p t1 t2); auto with searchtrees.
      auto with zarith. 
     Qed.

     Hint Resolve rm_3: searchtrees.

     Remark rm_4 :
      forall p0 : Z,
      occ p0 (Z_bnode q t0 t') -> occ p0 (Z_bnode n (Z_bnode p t1 t2) t').
     Proof. 
      intros p0 H.
      elim (occ_inv H).  
      intro eg.
      elim R; rewrite eg; auto with searchtrees.
      simple induction 1; auto with searchtrees.
      intro H'. elim R; auto with searchtrees.
     Qed.

     Hint Resolve rm_4: searchtrees.

     Remark rm_5 :
      forall p0 : Z,
      occ p0 (Z_bnode n (Z_bnode p t1 t2) t') ->
      occ p0 (Z_bnode q t0 t') \/ n = p0.
     Proof.
      intros p0 H.
      elim (occ_inv H). 
      simple induction 1; auto with searchtrees.
      simple induction 1.
      intro H1.
      elim R; intros H2 H3 H4 H5 H6 H7.
      elim (H5 p0 H1). intro; left; auto with searchtrees.
      simple induction 1; left; auto with searchtrees.
      intro; left; auto with searchtrees.
     Qed.

     Hint Resolve rm_5: searchtrees.

     Remark rm_6 : search (Z_bnode q t0 t').
     Proof.
      right.
      elim R; auto with searchtrees.
      apply search_r with n (Z_bnode p t1 t2); auto with searchtrees.
      elim R; intros H H0 H1 H2 H3 H4.
      apply maj_intro.
      intros q0 H5; elim (Zle_lt_or_eq q0 q (H0 q0 (H1 q0 H5))).
      auto with searchtrees.
      intro eg; absurd (occ q0 t0).
      rewrite eg; auto with searchtrees.
      auto with searchtrees.
      apply min_intro.
      intros q0 H. 
      apply Zlt_trans with n. 
      elim R; auto with searchtrees.
      elim (min_r (n:=n) (t1:=Z_bnode p t1 t2) (t2:=t')). 
      auto with searchtrees. 
      auto with searchtrees.
     Qed.

     Hint Resolve rm_6: searchtrees.
     

     Lemma rm_root_lemma :
      RM n (Z_bnode n (Z_bnode p t1 t2) t') (Z_bnode q t0 t').
     (********************************************************************)
     Proof.
      apply rm_intro; auto with searchtrees.  
     Qed.
     
End rm_root.


(* The final algorithm *)

Definition rm : forall (n : Z) (t : Z_btree), search t -> RM_SPEC n t.
refine
 (fun n =>
  (fix rm (t : Z_btree) : search t -> RM_SPEC n t :=
     match t return (search t -> RM_SPEC n t) with
     | Z_leaf => fun h => exist _ Z_leaf _
     | Z_bnode p t1 t2 =>
         fun h =>
         match Z_le_gt_dec n p with
         | left _ =>
             match Z_le_lt_eq_dec n p _ with
             | left _ =>
                 match rm t1 _ with
                 | exist t'1 _ => exist _ (Z_bnode p t'1 t2) _
                 end
             | right e =>
                 match
                   t1 as t'
                   return
                     (t1 = t' -> RM_SPEC n t' -> RM_SPEC n (Z_bnode p t' t2))
                 with
                 | Z_leaf => fun h' h'' => exist _ t2 _
                 | Z_bnode p' t'1 t'2 =>
                     fun h' h'' =>
                     match rmax (t:=Z_bnode p' t'1 t'2) _ _ with
                     | existS q (exist t4 _) => exist _ (Z_bnode q t4 t2) _
                     end
                 end _ _
             end
         | right _ => let (t'2, _) := rm t2 _ in exist _ (Z_bnode p t1 t'2) _
         end
     end)).
 auto with searchtrees.
 auto.      
 eauto with searchtrees.
 eauto with searchtrees.
 rewrite e.
 rewrite h' in h.
 auto with searchtrees.
 case h'.
 eauto with searchtrees.
 split.
 rewrite e.
 apply rm_root_lemma.
 case h'; auto.
 auto.
 trivial.
 apply rm. 
 eauto with searchtrees.
 auto with searchtrees.
 eauto with searchtrees.
 apply rm_right; auto.
 apply Zgt_lt; auto.
Defined.



Extraction rm.
  
(*
let rec rm n t x =
  match t with
    Z_leaf -> Z_leaf
  | Z_bnode (p, t1, t2) ->
      (match Z_le_gt_dec n p with
         left ->
           (match match Zcompare n p with
                    EGAL -> right
                  | INFERIEUR -> left
                  | SUPERIEUR -> assert false  with
              left -> Z_bnode (p, (rm n t1 prop), t2)
            | right ->
                (match t1 with
                   Z_leaf -> t2
                 | Z_bnode (p', t'1, t'2) ->
                     (let existS (q, r) =
                     rmax (Z_bnode (p', t'1, t'2)) prop prop in Z_bnode
                     (q, r, t2))))
       | right -> Z_bnode (p, t1, (rm n t2 prop)))

*)
