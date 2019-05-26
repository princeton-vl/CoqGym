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
    Proof of Huffman algorithm: Code.v                               
                                                                     
    Definitions of code as association lists and some properties     
                                                                     
    Definitions:                                                     
      code, encode, decode, find_code, find_val,                     
      in_alphabet, unique_prefix, not_null                           
                                                                     
                                    Laurent.Thery@inria.fr (2003)    
 **********************************************************************)

From Huffman Require Export Aux.
From Huffman Require Export Permutation.
From Huffman Require Export UniqueKey.
From Huffman Require Export Frequency.

Section Code.
(* Arbitrary set *)
Variable A : Type.
(* Equality is decidable *)
Variable eqA_dec : forall a b : A, {a = b} + {a <> b}.

(* A code is an association list *)
Definition code := list (A * list bool).

(* 
  Predicate that tells that a message (a list of message) is in the
  alphabet of the code
*)
Definition in_alphabet (m : list A) (c : code) :=
  forall a : A, In a m -> exists l : list bool, In (a, l) c.

(* Being in an alphabet is compatible with inclusion *)
Theorem in_alphabet_incl :
 forall m1 m2 c, incl m1 m2 -> in_alphabet m2 c -> in_alphabet m1 c.
Proof using.
intros m1 m2 c H H0; red in |- *.
intros a H1; case (H0 a); auto.
Qed.

(* Every code is in the alphabet of an empty message *)
Theorem in_alphabet_nil : forall c, in_alphabet nil c.
Proof using.
intros c a H; inversion H.
Qed.
Hint Resolve in_alphabet_nil : core.

(* An element can be added in the message if it is in the code *)
Theorem in_alphabet_cons :
 forall (m : list A) c a ca,
 In (a, ca) c -> in_alphabet m c -> in_alphabet (a :: m) c.
Proof using.
intros m c a ca H H0; red in |- *; simpl in |- *.
intros a1 [H1| H1].
exists ca; rewrite <- H1; auto.
case (H0 a1); auto.
Qed.
Hint Resolve in_alphabet_cons : core.

(* Inversion theorem *)
Theorem in_alphabet_inv :
 forall (c : code) (a : A) (l : list A),
 in_alphabet (a :: l) c -> in_alphabet l c.
Proof using.
intros c a l H; red in |- *.
intros a1 H1; apply H; simpl in |- *; auto.
Qed.
 
Definition code_dec :
  forall (c : code) a,
  {(exists l : list bool, In (a, l) c)} +
  {(forall l : list bool, ~ In (a, l) c)}.
intros c a; elim c; simpl in |- *; auto.
intros (a1, l1) l H; case (eqA_dec a1 a); intros H1.
left; exists l1; rewrite H1; auto.
case H.
intros e; left; case e; intros l2 H2; exists l2; auto.
intros n; right; intros l0; red in |- *; intros [H0| H0];
 [ case H1 | case (n l0) ]; auto.
injection H0; auto.
Defined.

(* Checking if a code is in an alphabet is decidable *)
Definition in_alphabet_dec :
  forall m c, {in_alphabet m c} + {~ in_alphabet m c}.
intros m; elim m; simpl in |- *; auto.
intros a l H c; case (H c); intros H1.
case (code_dec c a); intros H2.
left; red in |- *; simpl in |- *.
intros a1 [H3| H3];
 [ case H2; intros l1 Hl1; exists l1; rewrite <- H3 | idtac ]; 
 auto.
right; red in |- *; intros H3; case (H3 a); simpl in |- *; auto.
right; Contradict H1; auto; red in |- *.
intros a0 H0; case (H1 a0); simpl in |- *; auto.
intros x H2; exists x; auto.
Defined.

(* The empty list is associated to none of element of A in the code *)
Definition not_null (c : code) := forall a : A, ~ In (a, nil) c.

(* Inversion theorem *)
Theorem not_null_inv :
 forall (a : A * list bool) l, not_null (a :: l) -> not_null l.
Proof using.
intros a l H; red in |- *.
intros a0; red in |- *; intros H0; case (H a0); simpl in |- *; auto.
Qed.

(* Adding a non-empty element preserves the property of non-emptyness *)
Theorem not_null_cons :
 forall a b (l : list (A * list bool)),
 b <> nil -> not_null l -> not_null ((a, b) :: l).
Proof using.
intros a b l H H0; red in |- *.
intros a1; simpl in |- *; red in |- *; intros [H1| H1]; auto.
case H; injection H1; auto.
case (H0 a1); simpl in |- *; auto.
Qed.
Hint Resolve not_null_cons : core.

(* Non emptyness is compatible with append *) 
Theorem not_null_app :
 forall l1 l2 : list (A * list bool),
 not_null l1 -> not_null l2 -> not_null (l1 ++ l2).
Proof using.
intros l1; elim l1; simpl in |- *; auto.
intros (a2, l2); case l2; auto.
intros l H l0 H0 H1; case (H0 a2); simpl in |- *; auto.
intros b l l0 H l3 H0 H1; apply not_null_cons; auto.
red in |- *; intros H2; discriminate.
apply H; auto.
apply not_null_inv with (1 := H0).
Qed.
Hint Resolve not_null_app : core.

(* Adding an element in each component of a code makes it non-empty *)
Theorem not_null_map :
 forall (l : list (A * list bool)) b,
 not_null (map (fun v => match v with
                         | (a1, b1) => (a1, b :: b1)
                         end) l).
Proof using.
intros l; elim l; simpl in |- *; auto.
intros b; red in |- *; intros a; red in |- *; intros H; inversion H.
intros (a1, l1) l0 H b; apply not_null_cons; auto.
red in |- *; intros; discriminate.
Qed.
Hint Resolve not_null_map : core.

(* Define the property of list of booleans to be a prefix of another *)
Inductive is_prefix : list bool -> list bool -> Prop :=
  | prefixNull : forall l, is_prefix nil l
  | prefixCons :
      forall (b : bool) l1 l2,
      is_prefix l1 l2 -> is_prefix (b :: l1) (b :: l2).
Hint Constructors is_prefix : core.

(* A list is a prefix of itself *)
Theorem is_prefix_refl : forall l, is_prefix l l.
Proof using.
intros l; elim l; simpl in |- *; auto.
Qed.
Hint Resolve is_prefix_refl : core.

(* A code is unique_prefix, if there is no encoding that is prefix of another *)
Definition unique_prefix (l : code) :=
  (forall (a1 a2 : A) (lb1 lb2 : list bool),
   In (a1, lb1) l -> In (a2, lb2) l -> is_prefix lb1 lb2 -> a1 = a2) /\
  unique_key l.

(* The empty code is unique prefix *)
Theorem unique_prefix_nil : unique_prefix nil.
Proof using.
split; auto.
intros a1 a2 lb1 lb2 H; inversion H; auto.
Qed.
Hint Resolve unique_prefix_nil : core.

(* A unique prefix code can not have two elements prefix one from another *)
Theorem unique_prefix1 :
 forall (c : code) (a1 a2 : A) (lb1 lb2 : list bool),
 unique_prefix c ->
 In (a1, lb1) c -> In (a2, lb2) c -> is_prefix lb1 lb2 -> a1 = a2.
Proof using.
intros c a1 a2 lb1 lb2 (H1, H2); apply (H1 a1 a2 lb1 lb2); auto.
Qed.

(* A unique prefix code has unique keys *)
Theorem unique_prefix2 : forall c : code, unique_prefix c -> unique_key c.
Proof using.
intros c (H1, H2); auto.
Qed.

(* Inversion theorem *)
Theorem unique_prefix_inv :
 forall (c : code) (a : A) (l : list bool),
 unique_prefix ((a, l) :: c) -> unique_prefix c.
Proof using.
intros c a l (H1, H2); split.
intros a1 a2 lb1 lb2 H H0 H3; apply (H1 a1 a2 lb1 lb2); simpl in |- *; auto.
apply unique_key_inv with (1 := H2); auto.
Qed.

(* A prefix code with a  least two distinct elements is not_null *)
Theorem unique_prefix_not_null :
 forall (c : code) (a b : A),
 a <> b -> in_alphabet (a :: b :: nil) c -> unique_prefix c -> not_null c.
Proof using.
intros c a b H H0 H1.
unfold not_null in |- *; intros a1; red in |- *; intros Ha1.
case (H0 a); simpl in |- *; auto; intros l1 Hl1.
case (H0 b); simpl in |- *; auto; intros l2 Hl2.
case H; apply trans_equal with a1.
apply sym_equal; apply unique_prefix1 with (3 := Hl1) (2 := Ha1); auto.
apply unique_prefix1 with (3 := Hl2) (2 := Ha1); auto.
Qed.

(* Unique prefix is preserved by permutation *)
Theorem unique_prefix_permutation :
 forall c1 c2 : code,
 permutation c1 c2 -> unique_prefix c1 -> unique_prefix c2.
Proof using.
intros c1 c2 H (H1, H2).
cut (permutation c2 c1); [ intros HP; split | apply permutation_sym; auto ].
intros a1 a2 lb1 lb2 H0 H3 H4.
apply (H1 a1 a2 lb1 lb2); auto.
apply permutation_in with (2 := H0); auto.
apply permutation_in with (2 := H3); auto.
apply unique_key_perm with (2 := H2); auto.
Qed.

(* 
  Find the list of booleans associated with an element,
  return the empty list if the element does not exists
*)
Fixpoint find_code (a : A) (l : code) {struct l} : list bool :=
  match l with
  | nil => nil
  | (b, c) :: l1 =>
      match eqA_dec a b with
      | left _ => c
      | right _ => find_code a l1
      end
  end.

(* The result of find_code is in the code *)
Theorem find_code_correct1 :
 forall (c : code) (a : A) (b : bool) (l : list bool),
 find_code a c = b :: l -> In (a, b :: l) c.
Proof using.
intros c a b l; elim c; simpl in |- *; auto.
intros; discriminate.
intros a0; case a0.
intros a1; case (eqA_dec a a1); simpl in |- *; auto.
intros e l0 l1 H H0; left;
 apply f_equal2 with (f := pair (A:=A) (B:=list bool)); 
 auto.
Qed.

(* What is in the code can be found by find_code *)
Theorem find_code_correct2 :
 forall (c : code) (a : A) (l : list bool),
 unique_key c -> In (a, l) c -> find_code a c = l.
Proof using.
intros c a l; generalize a l; elim c; clear a l c; simpl in |- *; auto.
intros a l H H0; case H0.
intros a; case a.
intros a0 l l0 H a1 l1 H0 H1; case (eqA_dec a1 a0).
intros H2; case H1; intros H3.
injection H3; auto.
apply unique_key_in_inv with (l := (a0, l) :: l0) (a := a0); simpl in |- *;
 auto.
rewrite <- H2; auto.
intros H2; case H1; auto.
intros H3; case H2; injection H3; auto.
intros; apply H; auto.
apply unique_key_inv with (1 := H0); auto.
Qed.

(* There is not more than what is in the code *)
Theorem not_in_find_code :
 forall a l, (forall p, ~ In (a, p) l) -> find_code a l = nil.
Proof using.
intros a l; elim l; simpl in |- *; auto.
intros (a1, l1) l0 H H0.
case (eqA_dec a a1); auto.
intros H1; case (H0 l1); rewrite H1; auto.
intros H1; apply H; intros p; red in |- *; intros Hp; case (H0 p); auto.
Qed.

(* find_code is composed by append *)
Theorem find_code_app :
 forall a l1 l2,
 not_null l1 ->
 find_code a (l1 ++ l2) =
 match find_code a l1 with
 | nil => find_code a l2
 | b1 :: l3 => b1 :: l3
 end.
Proof using.
intros a l1; generalize a; elim l1; simpl in |- *; auto; clear a l1.
intros (a1, l1) l H a l2 H1; case (eqA_dec a a1); auto.
generalize H1; case l1; auto.
intros H0; case (H0 a1); simpl in |- *; auto.
cut (not_null l); simpl in |- *; auto.
apply not_null_inv with (1 := H1); auto.
Qed.

(* find_code is invariant under permutation *)
Theorem find_code_permutation :
 forall (a : A) (c1 c2 : code),
 permutation c1 c2 -> unique_prefix c1 -> find_code a c1 = find_code a c2.
Proof using.
intros a c1 c2 H; elim H; simpl in |- *; auto.
intros a0; case a0.
intros a1; case (eqA_dec a a1); auto.
intros n l L1 L2 H0 H1 H2; apply H1.
apply unique_prefix_inv with (1 := H2).
intros a0; case a0.
intros a1 l1.
case (eqA_dec a a1).
intros Ha1 b; case b; auto.
intros a2 l2 L HL; case (eqA_dec a a2); auto.
intros e.
case unique_key_in with (1 := unique_prefix2 _ HL) (b2 := l2); auto.
rewrite <- Ha1; rewrite e; simpl in |- *; auto.
intros Ha1 b; case b; auto.
intros L1 L2 L3 H0 H1 H2 H3 H4; apply trans_equal with (find_code a L2); auto.
apply H3.
apply (unique_prefix_permutation _ _ H0); auto.
Qed.

(* 
  Searching in a list with a common first element is equivalent
  to the search skipping the element
*)
Theorem in_find_map :
 forall p a l b,
 In (a, l) p ->
 find_code a
   (map
      (fun v : A * list bool => match v with
                          | (a1, b1) => (a1, b :: b1)
                          end) p) = b :: find_code a p.
Proof using.
intros p; elim p; simpl in |- *; auto.
intros a l b H; case H.
intros (a1, l1) l H a0 l0 b [H0| H0]; auto.
case (eqA_dec a0 a1); auto.
intros HH; case HH; injection H0; auto.
case (eqA_dec a0 a1); auto.
intros n; apply (H a0 l0 b); auto.
Qed.

(* 
  Searching in a list with a common first element is equivalent
  to the search skipping the element
*)
Theorem not_in_find_map :
 forall p a b,
 (forall l, ~ In (a, l) p) ->
 find_code a
   (map
      (fun v : A * list bool => match v with
                                | (a1, b1) => (a1, b :: b1)
                                end) p) = nil.
Proof using.
intros p; elim p; simpl in |- *; auto.
intros (a1, l1) l H a0 b H0; case (eqA_dec a0 a1); auto.
intros e; case (H0 l1); rewrite e; auto.
intros n; apply (H a0 b); auto.
intros l0; red in |- *; intros H1; case (H0 l0); auto.
Qed.

(* 
  Find the element associated with a list of booleans,
  return None if it does not exist in the code
*)
Fixpoint find_val (a : list bool) (l : code) {struct l} : option A :=
  match l with
  | nil => None
  | (b, c) :: l1 =>
      match list_eq_dec eq_bool_dec a c with
      | left _ => Some b
      | right _ => find_val a l1
      end
  end.

(* find_val returns an element of the code *)
Theorem find_val_correct1 :
 forall (c : code) (a : A) (l : list bool),
 find_val l c = Some a -> In (a, l) c.
Proof using.
intros c a l; elim c; simpl in |- *; auto.
intros; discriminate.
intros a0; case a0.
intros a1 l0 l1; case (list_eq_dec eq_bool_dec l l0); auto.
intros e H H0; injection H0.
intros e1; left; apply f_equal2 with (f := pair (A:=A) (B:=list bool)); auto.
Qed.

(* An element of the code can be found by find_val *)
Theorem find_val_correct2 :
 forall (c : code) (a : A) (l : list bool),
 unique_prefix c -> In (a, l) c -> find_val l c = Some a.
Proof using.
intros c a l; generalize a l; elim c; clear a l c; simpl in |- *; auto.
intros a l H H0; case H0.
intros a; case a.
intros a0 l l0 H a1 l1 H0 H1; case (list_eq_dec eq_bool_dec l1 l).
intros H2; apply f_equal with (f := Some (A:=A)).
case H1; intros H3.
injection H3; auto.
apply unique_prefix1 with (1 := H0) (lb1 := l) (lb2 := l1); simpl in |- *;
 auto.
rewrite H2; auto.
intros H2; case H1; auto.
intros H3; case H2; injection H3; auto.
intros; apply H; auto.
apply unique_prefix_inv with (1 := H0); auto.
Qed.

Opaque list_eq_dec.

(* The value of an empty list cannot be found in a non empty code *)
Theorem not_null_find_val :
 forall c : code, not_null c -> find_val nil c = None.
Proof using.
intros c; elim c; simpl; auto.
intros a; case a.
intros a1 l; case (list_eq_dec eq_bool_dec nil l); auto.
intros e l0 H H0; case (H0 a1); rewrite e; simpl in |- *; auto.
intros n l0 H H0; apply H.
unfold not_null in |- *; intros a2; red in |- *; intros H1.
case (H0 a2); simpl in |- *; auto.
Qed.

(* Encoding is done by iteratively applying find_code *)
Fixpoint encode (c : code) (m : list A) {struct m} : list bool :=
  match m with
  | nil => nil
  | a :: b => find_code a c ++ encode c b
  end.

(* Encoding can be splitted for appended lists *)
Theorem encode_app :
 forall l1 l2 c, encode c (l1 ++ l2) = encode c l1 ++ encode c l2.
Proof using.
intros l1; elim l1; simpl in |- *; auto.
intros a l H l2 c; rewrite H; auto.
rewrite app_ass; auto.
Qed.

(* Inversion theorem for encode *)
Theorem encode_cons_inv :
 forall a l1 l m1, ~ In a m1 -> encode ((a, l1) :: l) m1 = encode l m1.
Proof using.
intros a l1 l m1; generalize a l1 l; elim m1; simpl in |- *; auto;
 clear a l1 l m1.
intros a l H a0 l1 l0 H0; case (eqA_dec a a0); simpl in |- *; auto.
intros H1; case H0; auto.
intros e; rewrite H; auto.
Qed.

(* The encoding does not depend of permutation *)
Theorem encode_permutation :
 forall (m : list A) (c1 c2 : code),
 permutation c1 c2 -> unique_prefix c1 -> encode c1 m = encode c2 m.
Proof using.
intros m; elim m; simpl in |- *; auto.
intros a l H c1 c2 H0 H1.
apply f_equal2 with (f := app (A:=bool)); auto.
apply find_code_permutation; auto.
Qed.

(* Permuting the message permutes the encoding *)
Theorem encode_permutation_val :
 forall m1 m2 c, permutation m1 m2 -> permutation (encode c m1) (encode c m2).
Proof using.
intros m1 m2 c H; elim H; simpl in |- *; auto; clear H m1 m2.
intros; repeat rewrite <- app_ass; auto.
intros l1 l2 l3 H H0 H1 H2; apply permutation_trans with (1 := H0); auto.
Qed.

(* 
  To decode, first find the initial section of
  booleans that maps an encoding, this initial section is
  accumulated in the head
*)
Fixpoint decode_aux (c : code) (head m : list bool) {struct m} : list A :=
  match m with
  | nil => match find_val head c with
           | Some a => a :: nil
           | None => nil
           end
  | a :: m1 =>
      match find_val head c with
      | Some a1 => a1 :: decode_aux c (a :: nil) m1
      | None => decode_aux c (head ++ a :: nil) m1
      end
  end.

(* decode_aux is correct *)
Theorem decode_aux_correct :
 forall c : code,
 unique_prefix c ->
 not_null c ->
 forall (m1 m2 head : list bool) (a : A),
 find_val (head ++ m1) c = Some a ->
 decode_aux c head (m1 ++ m2) = a :: decode_aux c nil m2.
Proof using.
intros c Hc1 Hc2 m1; elim m1; simpl in |- *; auto.
intros m2; case m2; simpl in |- *; auto.
intros head a; rewrite <- app_nil_end.
intros H1; rewrite H1; auto.
rewrite not_null_find_val; auto.
intros b l head a; rewrite <- app_nil_end.
intros H1; rewrite H1; auto.
rewrite not_null_find_val; auto.
intros a l Rec m2 head a1 H2.
rewrite <- Rec with (head := head ++ a :: nil).
generalize (fun a => find_val_correct1 c a head).
case (find_val head c); auto.
intros a0 H; (cut (In (a0, head) c); [ intros Hin1 | auto ]).
cut (In (a1, head ++ a :: l) c);
 [ intros Hin2 | apply find_val_correct1; auto ].
cut (a1 = a0); [ intros Heq | idtac ].
absurd (head ++ a :: l = head); auto.
elim head; simpl in |- *; auto.
red in |- *; intros; discriminate.
intros a2 l0 H0; red in |- *; intros H1; case H0; auto.
injection H1; auto.
apply unique_key_in_inv with (l := c) (a := a1); auto.
apply unique_prefix2; auto.
rewrite Heq; auto.
apply sym_equal; apply (unique_prefix1 c a0 a1 head (head ++ a :: l)); auto.
elim head; simpl in |- *; auto.
rewrite app_ass; auto.
Qed.

(* Decode is just decode_aux with an empty head *)
Definition decode (c : list (A * list bool)) (m : list bool) :=
  decode_aux c nil m.

(* Decoding is correct *)
Theorem decode_correct :
 forall c : code,
 unique_prefix c ->
 not_null c ->
 forall (m1 m2 : list bool) (a : A),
 find_val m1 c = Some a -> decode c (m1 ++ m2) = a :: decode c m2.
Proof using.
intros c H H0 m1 m2 a H1; unfold decode in |- *; apply decode_aux_correct;
 auto.
Qed.

(* Encoding and decoding return the same message if the code is prefix *)
Theorem correct_encoding :
 forall c : code,
 unique_prefix c ->
 not_null c ->
 forall m : list A, in_alphabet m c -> decode c (encode c m) = m.
Proof using.
intros c H1 H2 m; elim m; simpl in |- *; auto.
intros H3; unfold decode in |- *; simpl in |- *.
rewrite not_null_find_val; auto.
intros a l H H0; rewrite decode_correct with (a := a); auto.
apply f_equal2 with (f := cons (A:=A)); auto.
apply H; apply in_alphabet_inv with (1 := H0); auto.
case (H0 a); simpl in |- *; auto.
intros l1 Hl1.
apply find_val_correct2; auto.
case (H0 a); simpl in |- *; auto.
intros x1; case x1.
intros H3; case (H2 a); auto.
intros b l0 H3; cut (find_code a c = b :: l0).
intros H4; rewrite H4; apply find_code_correct1; auto.
apply find_code_correct2 with (2 := H3); auto.
case H1; auto.
Qed.

(* A unique prefix code in an alphabet of at least 2 elements is non-empty *)
Theorem frequency_not_null :
 forall m (c : code),
 1 < length (frequency_list eqA_dec m) ->
 unique_prefix c -> in_alphabet m c -> not_null c.
Proof using.
intros m c H H0 H1.
CaseEq (frequency_list eqA_dec m); auto.
intros H2; rewrite H2 in H; Contradict H; simpl in |- *; auto with arith.
intros p l; case p; case l; simpl in |- *; auto.
intros a n H2; rewrite H2 in H; Contradict H; simpl in |- *; auto with arith.
intros p0 l0; case p0; intros b nb a na H2.
apply unique_prefix_not_null with a b; auto.
intros H3; absurd (In (fst (a, na)) (fst (b, nb) :: map (fst (B:=_)) l0)).
cut (ulist (map (fst (B:=_)) (frequency_list eqA_dec m))).
rewrite H2; simpl in |- *; intros H4; inversion H4.
case H7; rewrite H3; auto with datatypes.
apply unique_key_ulist.
apply frequency_list_unique.
simpl in |- *; rewrite H3; auto with datatypes.
case (H1 a); auto.
apply frequency_list_in with eqA_dec na; rewrite H2; auto with datatypes.
intros l1 Hl1; apply in_alphabet_cons with l1; auto.
case (H1 b); auto.
apply frequency_list_in with eqA_dec nb; rewrite H2; auto with datatypes.
intros l2 Hl2; apply in_alphabet_cons with l2; auto.
Qed.
 
End Code.
Arguments encode [A].
Arguments decode [A].
Arguments find_code [A].
Arguments find_val [A].
Arguments in_alphabet [A].
Arguments unique_prefix [A].
Arguments not_null [A].
Hint Constructors is_prefix : core.
Hint Resolve is_prefix_refl : core.
Hint Resolve not_null_map : core.
Hint Resolve unique_prefix_nil : core.
Hint Resolve in_alphabet_nil in_alphabet_cons : core.
Hint Resolve not_null_app : core.
