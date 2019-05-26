(* Contribution to the Coq Library   V6.3 (July 1999)                    *)

(****************************************************************************)
(* This contribution was updated for Coq V5.10 by the COQ workgroup.        *)
(* January 1995                                                             *)
(****************************************************************************)
(*                                                                          *)
(*                                                                          *)
(*  utils.v                                                                 *)
(*                                                                          *)
(*  Contains miscellaneous useful definitions and theorems                  *)
(*  used in later proofs and definitions.                                   *)
(*                                                                          *)
(*                                                                          *)
(*  Jill Seaman                                                             *)
(*  Coq V5.8                                                                *)
(*  November  1993                                                          *)
(*                                                                          *)
(*                                                                          *)
(****************************************************************************)
(*                                 utils.v                                  *)
(****************************************************************************)

Require Import syntax.


(********************************************************)
(*							*)
(*   vari_nat:						*)
(*       (m,n:nat)  (x m) = (x n)  --> m = n		*)
(*							*)
(*   valu: a deconstructor for type vari 		*)
(*							*)
(********************************************************)

Definition valu (v : vari) :=
  match v return nat with
  | x n => (* x n *)  n
  end.

Goal forall m n : nat, x m = x n :>vari -> m = n :>nat.
intros m n Q.  
replace m with (valu (x m)).
rewrite Q.
simpl in |- *; reflexivity.
simpl in |- *; reflexivity.
Save vari_nat.


(********************************************************)
(*							*)
(*   subty_eq:						*)
(*	(s -> r) = (q -> t)  ---->  s = q /\ r = t	*)
(*							*)
(*   Rator_ty, Rand_ty:  Arrow type destructors giving  *)
(*   the types of the operator and operand respectively.*)
(*							*)
(********************************************************)

Definition Rator_ty (t : ty) :=
  match t with
  | nat_ty => t
  | bool_ty => t
  | arr t0 _ => t0
  end.
Definition Rand_ty (t : ty) :=
  match t with
  | nat_ty => t
  | bool_ty => t
  | arr _ t0 => t0
  end.
Goal
forall s1 t1 s2 t2 : ty,
arr s1 t1 = arr s2 t2 :>ty -> s1 = s2 :>ty /\ t1 = t2 :>ty.
intros s1 t1 s2 t2 Q.
split.
change (Rator_ty (arr s1 t1) = Rator_ty (arr s2 t2) :>ty) in |- *.
apply (f_equal Rator_ty). assumption.
change (Rand_ty (arr s1 t1) = Rand_ty (arr s2 t2) :>ty) in |- *.
apply (f_equal Rand_ty); assumption.
Save subty_eq.



(****************************************)
(* Type properties 			*)
(*     Proof that the type constructors	*) 
(*     nat_ty, bool_ty, and arr_ty are	*)
(*     distinct				*)
(****************************************)


Definition is_nat (t : ty) :=
  match t with
  | nat_ty => True
  | bool_ty => False
  | arr _ _ => False
  end.
Definition is_bool (t : ty) :=
  match t with
  | nat_ty => False
  | bool_ty => True
  | arr _ _ => False
  end.
Definition is_arr (t : ty) :=
  match t with
  | nat_ty => False
  | bool_ty => False
  | arr _ _ => True
  end.

Goal nat_ty <> bool_ty :>ty.
red in |- *; intro H; change (is_nat bool_ty) in |- *; elim H; exact I.
Save nat_not_bool.

Goal forall t s : ty, nat_ty <> arr t s :>ty.
red in |- *; intros t s H; change (is_nat (arr t s)) in |- *; elim H; exact I.
Save nat_not_arr.

Goal forall t s : ty, bool_ty <> arr t s :>ty.
red in |- *; intros t s H; change (is_bool (arr t s)) in |- *; elim H;
 exact I.
Save bool_not_arr.





(********************************)
(*         			*)
(*  Xmidvar: 			*)
(*      x=v \/ ~x=v		*)
(*          			*)
(*    	Uses Xmidnat		*)
(*          			*)
(********************************)


	(*************************)
	(* Xmidnat   		 *)
	(*     m=n \/ ~m=n       *)
	(*************************)

	Goal forall m n : nat, m = n \/ m <> n.

	simple induction m.
	simple induction n.
	left; reflexivity.
	intros; right; apply O_S.
	intros y H n; elim n.
	right; red in |- *; intro; apply (O_S y); symmetry  in |- *; assumption.
	intros y0 I.
	elim (H y0); intro E. 
	left; elim E; reflexivity.
	right; red in |- *; intro.
	apply E; apply eq_add_S; assumption.
	Save Xmidnat.


(****************)
(*   Xmidvar	*)
(****************)

Goal forall v w : vari, v = w \/ v <> w.

simple induction v.
simple induction w.
intro. 
specialize (Xmidnat n n0).
simple induction 1.
intro eq; left; elim eq; reflexivity.
intro neq; right; red in |- *; intro; apply neq.
apply vari_nat; assumption.
Save Xmidvar.



(*****************************************)
(*					 *)
(*  If Properties                        *)
(*				 	 *)
(*  If_T:  (IF A B C) /\ A -> B          *)
(*  If_F:  (IF A B C) /\ not A -> C      *)
(*  T_If:  A /\ B -> (IF A B C)          *)
(*  F_If:  not A /\ C -> (IF A B C)      *)
(*					 *)
(*****************************************)


(*** If_T ***)
Goal forall A B C : Prop, (IF A then B else C) -> A -> B.
unfold IF_then_else in |- *; simple induction 1.
simple induction 1; intros; assumption.
simple induction 1; intros; absurd A; assumption.
Save If_T.

(*** If_F ***)
Goal forall A B C : Prop, (IF A then B else C) -> ~ A -> C.
unfold IF_then_else in |- *; simple induction 1.
simple induction 1; intros; absurd A; assumption.
simple induction 1; intros; assumption.
Save If_F.

(*** T_If ***)
Goal forall A B C : Prop, A -> B -> IF A then B else C.
unfold IF_then_else in |- *; intros.
left; split; assumption.
Save T_If.

(*** F_If ***)
Goal forall A B C : Prop, ~ A -> C -> IF A then B else C.
unfold IF_then_else in |- *; intros.
right; split; assumption.
Save F_If.


(********************************)
(* IfA_IfAIfA:  		*)
(*  IF A then B			*)
(*         else C  ---->	*)
(*  IF A then B 		*)
(*       else IF A then D	*)
(*  		   else C.	*)
(********************************)

Goal
forall A B C D : Prop,
(IF A then B else C) -> IF A then B else (IF A then D else C).

unfold IF_then_else in |- *; simple induction 1.
intro T; left; assumption.
intro F; right; elim F; intros; split.
assumption.
right; split; assumption.
Save IfA_IfAIfA.

(********************************)
(*  AABC_ABC			*)
(*    A\/(D/\C) --> (D->(A\/B))	*)
(*       --> (A \/ (B/\C))	*)
(********************************)

Goal forall A B C D : Prop, A \/ D /\ C -> (D -> A \/ B) -> A \/ B /\ C.

intros A B C D A1 A2.
elim A1.
intro; left; assumption.
simple induction 1; intros DH CH.
specialize A2 with (1 := DH); induction A2.
left; assumption.
right; split; assumption.
Save AABC_ABC.
