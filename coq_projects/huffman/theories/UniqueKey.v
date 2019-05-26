(* This program is free software; you can redistribute it and/or      *)
(* modify it under the terms of the GNU Lesser General Public License *)
(* as published by the Free Software Foundation; either version 2.1   *)
(* of the License, or (at your option) any later version.             *)
(*                                                                    *)
(* This program is distributed in the hope that it will be useful,    *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of     *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the      *)
(* GNU Lesser General Public License for more details.                *)
(*                                                                    *)
(* You should have received a copy of the GNU Lesser General Public   *)
(* License along with this program; if not, write to the Free         *)
(* Software Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA *)
(* 02110-1301 USA                                                     *)

(***********************************************************************)
(*    Proof of Huffman algorithm: UniqueKey.v                          *)
(*                                                                     *)
(*    Definition: uniqueness of keys in association list               *)
(*                                                                     *)
(*                                    Laurent.Thery@inria.fr (2003)    *)
(***********************************************************************)

From Huffman Require Export Aux.
From Huffman Require Export Permutation.
From Huffman Require Export UList.
From Huffman Require Export sTactic.

Section UniqueKey.
Variables (A : Type) (B : Type).
 
(* An association list has unique keys if the keys appear only once *)
Inductive unique_key : list (A * B) -> Prop :=
  | unique_key_nil : unique_key nil
  | unique_key_cons :
      forall (a : A) (b : B) l,
      (forall b : B, ~ In (a, b) l) ->
      unique_key l -> unique_key ((a, b) :: l).
Hint Constructors unique_key : core.
 
(* Inversion theorem *)
Theorem unique_key_inv : forall a l, unique_key (a :: l) -> unique_key l.
Proof using.  
intros a l H; inversion H; auto.
Qed.

(* Inversion theorem *)
Theorem unique_key_in :
 forall (a : A) (b1 b2 : B) l, unique_key ((a, b1) :: l) -> ~ In (a, b2) l.
Proof using.
intros a b1 b2 l H; inversion H; auto.
Qed.

(* Inversion theorem *)
Theorem unique_key_in_inv :
 forall a l1 l2 l, unique_key l -> In (a, l1) l -> In (a, l2) l -> l1 = l2.
Proof using.
intros a l1 l2 l H; generalize a l1 l2; elim H; simpl in |- *; auto;
 clear H a l1 l2 l.
intros a l1 l2 H; case H.
intros a b l H H0 H1 a0 l1 l2 [H2| H2] [H3| H3].
injection H2; injection H3; intros; apply trans_equal with b; auto.
case (H l2); injection H2; intros H4 H5; rewrite H5; auto.
case (H l1); injection H3; intros H4 H5; rewrite H5; auto.
apply H1 with (1 := H2) (2 := H3); auto.
Qed.

(* Uniqueness is compatible with permutation *)
Theorem unique_key_perm :
 forall l1 l2, permutation l1 l2 -> unique_key l1 -> unique_key l2.
Proof using.
intros l1 l2 H; elim H; auto.
intros (a1, b1) L1 L2 H0 H1 H2; apply unique_key_cons.
intros b; red in |- *; intros H3; case (unique_key_in _ _ b _ H2).
apply permutation_in with (2 := H3); auto.
apply permutation_sym; auto.
apply H1; apply unique_key_inv with (1 := H2); auto.
intros (a1, b1) (a2, b2) L H0; apply unique_key_cons.
intros b; red in |- *; simpl in |- *; intros [H1| H1].
case (unique_key_in _ _ b2 _ H0); auto.
injection H1; intros H2 H3; rewrite H3; simpl in |- *; auto.
case (unique_key_in _ _ b _ (unique_key_inv _ _ H0)); auto.
apply unique_key_cons.
intros b; red in |- *; simpl in |- *; intros H1;
 case (unique_key_in _ _ b _ H0); simpl in |- *; auto.
apply unique_key_inv with (a := (a2, b2));
 apply unique_key_inv with (1 := H0).
Qed.

(* Uniqueness is compatible with append if the two list are distinct *)
Theorem unique_key_app :
 forall l1 l2,
 unique_key l1 ->
 unique_key l2 ->
 (forall a b c, In (a, b) l1 -> In (a, c) l2 -> False) ->
 unique_key (l1 ++ l2).
Proof using.
intros l1; elim l1; simpl in |- *; auto.
intros (a1, ll1) l H l2 H0 H1 H2; apply unique_key_cons; auto.
intros b; red in |- *; intros H3.
case in_app_or with (1 := H3).
change (~ In (a1, b) l) in |- *; apply unique_key_in with (1 := H0).
intros H4; apply (H2 a1 ll1 b); auto.
apply H; auto.
apply unique_key_inv with (1 := H0); auto.
intros a b c H3 H4; apply (H2 a b c); auto.
Qed.
 
(* The list of keys is unique *)
Theorem unique_key_ulist :
 forall l : list (A * B), unique_key l -> ulist (map (fst (B:=_)) l).
Proof using.
intros l; elim l; simpl in |- *; auto.
intros a l0 H H0; apply ulist_cons.
inversion H0.
red in |- *; intros H5; case in_map_inv with (1 := H5).
intros (b2, l2); simpl in |- *; intros (Hb1, Hb2); case (H3 l2); auto.
rewrite Hb2; auto.
apply H; apply unique_key_inv with (1 := H0); auto.
Qed.

(* A list of keys is unique gives a code with unique keys *)
Theorem ulist_unique_key :
 forall l : list (A * B), ulist (map (fst (B:=_)) l) -> unique_key l.
Proof using.
intros l; elim l; simpl in |- *; auto.
intros a; case a.
intros a0 b l0 H H0; apply unique_key_cons; auto.
intros b0; red in |- *; intros H1; absurd (In a0 (map (fst (B:=_)) l0)); auto.
inversion H0; auto.
change (In (fst (a0, b0)) (map (fst (B:=_)) l0)) in |- *; auto with datatypes.
apply in_map; auto.
apply H; apply ulist_inv with (1 := H0); auto.
Qed. 

End UniqueKey.
Hint Constructors unique_key : core.
Arguments unique_key [A B].
 
(* Uniqueness is compatible with map for injective functions *)
Theorem unique_key_map :
 forall (A B C D : Type) l (f : A * B -> C * D),
 unique_key l ->
 (forall a b, fst (f a) = fst (f b) -> fst a = fst b) -> unique_key (map f l).
Proof using.
intros A B C D l f H; elim H; simpl in |- *; auto.
intros a b l0 H0 H1 H2 H3.
CaseEq (f (a, b)); intros fa fb Hf; auto.
apply unique_key_cons; auto.
generalize H0; elim l0; simpl in |- *; auto.
intros (a0, b0) l1 H4 H5 b1; red in |- *; intros [H6| H6].
case (H5 b0); left; apply f_equal2 with (f := pair (A:=A) (B:=B)); auto.
change (fst (a0, b0) = fst (a, b)) in |- *.
apply H3; auto.
rewrite H6; rewrite Hf; simpl in |- *; auto.
generalize H6; change (~ In (fa, b1) (map f l1)) in |- *.
apply H4.
intros b2; red in |- *; intros H7.
case (H5 b2); auto.
Qed.
Hint Resolve unique_key_app unique_key_map : core.
