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


(**********************************************************************
    Proof of Huffman algorithm: Restrict.v                           
                                                                     
    Definition of a restriction of a code (only the keys of a        
    message appears                                                  
                                                                     
    Definition: restrict_code                                        
                                    Laurent.Thery@inria.fr (2003)    
 **********************************************************************)

From Huffman Require Export Code.
From Huffman Require Export Frequency.
From Huffman Require Export ISort.
From Huffman Require Export Permutation.
From Huffman Require Export UniqueKey.
From Huffman Require Export PBTree2BTree.

Section Restrict.
Variable A : Type.
Variable empty : A.
Variable eqA_dec : forall a b : A, {a = b} + {a <> b}.
Variable m : list A.

(* Restrict the code putting only codes of element in the frequency list *)
Definition restrict_code (m : list A) (c : code A) : 
  code A :=
  map (fun x => (fst x, find_code eqA_dec (fst x) c))
    (frequency_list eqA_dec m).

(* The restriction has unique keys *)
Theorem restrict_code_unique_key :
 forall c : code A, unique_key (restrict_code m c).
Proof using.
intros c; apply ulist_unique_key.
unfold restrict_code in |- *.
replace
 (map (fst (B:=_))
    (map (fun x : A * nat => (fst x, find_code eqA_dec (fst x) c))
       (frequency_list eqA_dec m))) with
 (map (fst (B:=_)) (frequency_list eqA_dec m)).
apply unique_key_ulist; auto.
elim (frequency_list eqA_dec m); simpl in |- *; auto with datatypes.
intros a l H; apply f_equal2 with (f := cons (A:=A)); auto.
Qed.

(* Doing the restriction does not change the codes *) 
Theorem restrict_code_in :
 forall (a : A) (c : code A),
 In a m -> find_code eqA_dec a c = find_code eqA_dec a (restrict_code m c).
Proof using.
intros a c H.
apply sym_equal; apply find_code_correct2; auto.
apply restrict_code_unique_key.
generalize (in_frequency_map _ eqA_dec m a H).
unfold restrict_code in |- *; elim (frequency_list eqA_dec m); simpl in |- *;
 auto with datatypes.
intros a0; case a0; simpl in |- *; auto with datatypes.
intros a1 n l H0 [H1| H1]; try rewrite H1; auto.
Qed.

(*
  The restriction does not change the encoding for messages in
  the same alphabet
*)
Theorem restrict_code_encode_incl :
 forall (m1 : list A) (c : code A),
 incl m1 m -> encode eqA_dec c m1 = encode eqA_dec (restrict_code m c) m1.
Proof using.
intros m1 c; elim m1; simpl in |- *; auto.
intros a l H H0.
apply f_equal2 with (f := app (A:=bool)); auto with datatypes.
apply restrict_code_in; auto with datatypes.
apply H; apply incl_tran with (2 := H0); auto with datatypes.
Qed.

(* The restriction does not change the encoding of the initial message *)
Theorem restrict_code_encode :
 forall c : code A, encode eqA_dec c m = encode eqA_dec (restrict_code m c) m.
Proof using.
intros c; apply restrict_code_encode_incl; auto with datatypes.
Qed.

(* 
  The restriction does not change the unique prefix property if
  the message is in the alphabet
*)
Theorem restrict_unique_prefix :
 forall c : code A,
 not_null c ->
 in_alphabet m c -> unique_prefix c -> unique_prefix (restrict_code m c).
Proof using.
intros c HH HH0 (HH1, HH2); split.
intros a1 a2 lb1 lb2 H0 H1 H2; apply HH1 with (lb1 := lb1) (lb2 := lb2); auto.
unfold restrict_code in H0.
case in_map_inv with (1 := H0).
intros x; case x; simpl in |- *.
intros a0 n (HP1, HP2).
rewrite HP2.
case (HH0 a0); auto.
apply frequency_list_in with (1 := HP1).
intros x0 H; rewrite find_code_correct2 with (2 := H); auto.
unfold restrict_code in H1.
case in_map_inv with (1 := H1).
intros x; case x; simpl in |- *.
intros a0 n (HP1, HP2).
rewrite HP2.
case (HH0 a0); auto.
apply frequency_list_in with (1 := HP1).
intros x0 H; rewrite find_code_correct2 with (2 := H); auto.
unfold restrict_code in |- *.
apply unique_key_map; auto.
Qed.

(* Restricting do not change the frequency list *)
Theorem frequency_list_restric_code_map :
 forall c,
 map (fst (B:=_)) (frequency_list eqA_dec m) =
 map (fst (B:=_)) (restrict_code m c).
Proof using.
intros c; unfold restrict_code in |- *; elim (frequency_list eqA_dec m);
 simpl in |- *; auto.
intros a0 l H; apply f_equal2 with (f := cons (A:=A)); auto.
Qed.

(* If the message is not null, so is the restriction *)
Theorem restrict_not_null : forall c, m <> nil -> restrict_code m c <> nil.
Proof using.
case m; simpl in |- *; auto.
unfold restrict_code in |- *.
intros a0 l c H H1.
absurd
 (In
    ((fun x : A * nat => (fst x, find_code eqA_dec (fst x) c))
       (a0, number_of_occurrences eqA_dec a0 (a0 :: l))) nil);
 auto with datatypes.
rewrite <- H1.
apply
 in_map with (f := fun x : A * nat => (fst x, find_code eqA_dec (fst x) c)).
apply frequency_number_of_occurrences; auto with datatypes.
Qed.

(* 
  The leaves of the build tree from the restrict code are the keys
  of the frequency list
*) 
Theorem restrict_code_pbbuild :
 forall c : code A,
 not_null c ->
 unique_prefix c ->
 in_alphabet m c ->
 m <> nil ->
 permutation (map fst (frequency_list eqA_dec m))
   (all_pbleaves (pbbuild empty (restrict_code m c))).
Proof using.
intros c H H0 H1 H2.
rewrite frequency_list_restric_code_map with (c := c).
apply all_pbleaves_pbbuild; auto.
apply restrict_not_null; auto.
apply restrict_unique_prefix; auto.
Qed.
 
End Restrict.
Arguments restrict_code [A].
