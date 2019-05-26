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


Section General_Order.
Variable S : Set.
Variable O : S -> S -> Prop.
Variable E : S -> S -> Prop.

(** merge_order is the order which is the disjuction of two other orders. *)

Definition is_order :=
  (forall x : S, ~ O x x) /\ (forall x y z : S, O x y -> O y z -> O x z).

Definition wf_ind :=
  forall P : S -> Prop,
  (forall q : S, (forall r : S, O r q -> P r) -> P q) -> forall q : S, P q.

Definition is_equality :=
  (forall x : S, E x x) /\
  (forall x y : S, E x y -> E y x) /\
  (forall x y z : S, E x y -> E y z -> E x z).

(* The well_definedness proof (of the merged order) does not seem to need the totality of the order with respect to the Leibniz equlqity, but rather with respect to an equality which is rewriteable in the order predicates, hence we consign to the following property *)

Definition is_well_def_rht :=
  forall x y : S, O x y -> forall z : S, E y z -> O x z.

Definition is_well_def_lft :=
  forall x y : S, O x y -> forall z : S, E x z -> O z y.

End General_Order.

Record well_ordering : Type := 
  {wfcrr :> Set;
   order : wfcrr -> wfcrr -> Prop;
   equality : wfcrr -> wfcrr -> Prop;
   is_ord : is_order wfcrr order;
   is_eq : is_equality wfcrr equality;
   ord_is_wf : wf_ind wfcrr order;
   ord_wd_rht : is_well_def_rht wfcrr order equality}.


Section Negation_Order.
Variable S : well_ordering.


Let O := order S.

Lemma order_lt_le_weak : forall n m : S, O m n -> ~ O n m.
Proof.
 intros.
 elim (is_ord S).
 intro.
 intro.
 intro.
 apply H0 with n. 
 apply H1 with m.
 assumption.
 assumption.
Defined.

End Negation_Order.

Section Merge_Order.

Variable S1 S2 : well_ordering.
Let O1 := order S1.
Let O2 := order S2.
Let E1 := equality S1.
Let E2 := equality S2.



Definition merge_lt (x1 : S1) (p1 : S2) (x2 : S1) (p2 : S2) :=
  O1 x1 x2 \/ E1 x1 x2 /\ O2 p1 p2.

Definition merge_le (x1 : S1) (p1 : S2) (x2 : S1) (p2 : S2) :=
  merge_lt x1 p1 x2 p2 \/ E1 x1 x2 /\ E2 p1 p2.


Let S1ind_wf := ord_is_wf S1.
Let S2ind_wf := ord_is_wf S2.



Lemma merge_lt_wf :
 forall P : S1 -> S2 -> Prop,
 (forall (q : S1) (t : S2),
  (forall (r : S1) (u : S2), merge_lt r u q t -> P r u) -> P q t) ->
 forall (x : S1) (p : S2), P x p.
Proof.
 intros.
 (* New Subgoal *)
 assert
  (forall r : S1,
   (forall r' : S1, O1 r' r -> forall t' : S2, P r' t') ->
   forall t : S2, P r t).
 clear x p.
 intros x.
 intros.
 set (x_aux := x) in *.
 assert (E1 x_aux x).
 unfold x_aux in |- *.
 elim (is_eq S1).
 intros.
 apply H1.
 generalize H1.
 generalize x_aux.
 apply (S2ind_wf (fun p : S2 => forall x_aux : S1, E1 x_aux x -> P x_aux p)).
 intros.
 apply H.
 intros.
 case H4.
 intro.
 apply H0.
 apply (ord_wd_rht S1) with x_aux0.
 assumption.
 assumption.
 intro a.
 elim a.
 intros.
 apply H2.
 assumption. 
 elim (is_eq S1).
 intros.
 elim H8.
 intros.
 apply H10 with x_aux0.
 assumption.
 assumption.
 (* End New SUBGOAL *)

 generalize x.
 clear x.
 apply (S2ind_wf (fun p : S2 => forall x : S1, P x p)).
 intros.
 apply H.
 clear p.
 intros x' p.
 intro.
 case H2.

 intro. 
 generalize p.
 assert
  (S1ind_wf_ :
   forall P : S1 -> Prop,
   (forall q : S1, (forall r : S1, O1 r q -> P r) -> P q) ->
   forall t : S1, P t).
 apply S1ind_wf.
 apply S1ind_wf_ with (P := fun x : S1 => forall p1 : S2, P x p1). 
 intros. 
 apply H0.
 intros.
 apply H4.
 assumption.

 intro a.
 elim a.
 intros.
 apply H1.
 assumption.
Defined.




End Merge_Order.
