(*********************************************)
(* This file is part of the 'Higman' contrib *)
(* file : tree.v                             *)
(* contains : tree definition and its        *)   
(*  associated induction principle           *)
(* author : W.Delobel                        *)
(*********************************************)

Set Implicit Arguments.
Require Export Arith.
Require Export List.
  
Section Wrap.

    Unset Elimination Schemes.

    Variable A : Set.
    Variable leA : A -> A -> Prop.

    Inductive tree : Set := 
      | node : A -> list tree -> tree.

Section definitions.


    Fixpoint tree_size (t : tree) : nat :=
      match t with 
	| node _ l => S ((fix l_size (l : list tree) : nat :=
			    match l with 
			      | nil => 0
			      | t' :: l' => (tree_size t') + (l_size l')
			    end) l)
      end.

   Definition root (t : tree) : A :=
	match t with 
	| node a l => a
	end.

   Definition subtrees (t : tree) : list tree :=
	match t with 
	| node _ l => l
	end.

   
Inductive tree_in_forest : tree -> list tree -> Prop :=
| tif0 : forall t t' l, In t' l -> subtree t t' -> tree_in_forest t l
with subtree : tree -> tree -> Prop :=
| sub0 : forall t, subtree t t
| sub1 : forall t l ts, tree_in_forest t ts -> subtree t (node l ts). 


End definitions.

Section tree_rect.

    Variables
      (P : tree -> Type)
      (Q : list tree -> Type).

    Hypotheses
      (H1 : forall x, P (node x nil))
      (H2 : forall f v, Q v -> P (node f v))
      (H3 : Q nil)
      (H4 : forall t v, P t -> Q v -> Q (t :: v)).

    Fixpoint tree_rect_aux t : P t :=
      match t as t return P t with
	| node f v => H2 f
	  ((fix vt_rect (v : list tree) : Q v :=
	    match v as v return Q v with
	      | nil => H3
	      | cons t' v' => H4 (tree_rect_aux t') (vt_rect v')
	    end) v)
      end.

End tree_rect.

Set Elimination Schemes.
			    
Inductive lforall (P : tree -> Type) : list tree -> Type :=
| lforall_nil : lforall P nil
| lforall_cons : forall a l, lforall P l -> P a -> lforall P (a::l).


Lemma tree_rect : forall P : tree -> Type, 
      (forall x, P (node x nil)) -> (forall f v, lforall P v -> P (node f v)) ->
      forall t, P t.
Proof.
	intros P H1 H2. 
	apply tree_rect_aux with (Q := fun l => lforall P l); trivial.
	constructor.
	intros; constructor; trivial.
Qed.

Lemma tree_ind : forall P : tree -> Prop, 
	(forall x, P (node x nil)) -> (forall f v, (forall u, In u v -> P u) -> P (node f v)) ->
	forall t, P t.
Proof.
	intros P H1 H2.
	apply tree_rect; trivial.
	intros f v H; apply H2.
	induction H; intros u Hu.
	inversion Hu.
	elim Hu; clear Hu; intro Hu.
	subst; trivial.
	apply IHlforall; trivial.
Qed.

Fact im_sub_tree_size : forall a l t, In t l -> (tree_size t) < (tree_size (node a l)).
Proof.
	intros a l; induction l as [| u l IHl]; intros t Hin.
	inversion Hin.
	elim Hin; clear Hin; intro Hin.
	subst; simpl in |- *.
	apply lt_le_trans with (S (tree_size t)); auto with arith.
	apply lt_le_trans with (tree_size (node a l)); auto with arith.
	simpl; auto with arith.
Qed.

Fact subtree_trans : forall t t' t'', subtree t t' -> subtree t' t'' -> subtree t t''.
Proof.
assert (H : forall t'' t', subtree t' t'' -> forall t, subtree t t' -> subtree t t'').
intro t; induction t as [a | a f IHt]; intros t' H1 t'' H2.
inversion H1; subst; trivial.
inversion H3; subst; trivial.
inversion H.
inversion H1; subst; trivial.
constructor 2.
inversion H3; subst.
constructor 1 with t'0; trivial.
apply IHt with t'; trivial.
intros t t' t'' H1 H2; apply H with t'; trivial.
Qed.

Fact eq_tree_dec : (forall (a a' : A), {a = a'} + {a <> a'}) -> 
forall (t t' : tree), {t = t'} + {t <> t'}.
Proof.
intro eq_A_dec; apply (tree_rect (P:=fun t => forall (t' : tree), {t = t'} + {t <> t'})).
intros a t'; destruct t' as [a' ts'].
destruct ts'; [idtac | right; intro HF; inversion HF].
elim (eq_A_dec a a'); intro case_a_a'; [left | right; intro HF; apply case_a_a']; subst; trivial.
inversion HF; trivial.
intros a ts IHt t'; destruct t' as [a' ts'].
elim (eq_A_dec a a'); intro case_a_a'; [subst a'|right;intro HF;inversion HF;apply case_a_a'; trivial].
assert (H : {ts = ts'} + {ts <> ts'}).
generalize ts'; clear ts'; induction IHt; intro ts'.
destruct ts' as [| t' ts']; [left | right]; trivial.
intro HF; inversion HF.
destruct ts' as [| t' ts']; [right | idtac]; trivial.
intro HF; inversion HF.
elim (IHIHt ts'); intro case_ts'.
subst; elim (p t'); intro case_t'; subst; [left | right]; trivial.
intro HF; inversion HF; apply case_t'; trivial.
right; intro HF; inversion HF; apply case_ts'; trivial.
elim H; clear H; intro H; [left; subst | right]; trivial.
intro HF; inversion HF; apply H; trivial.
Qed.

End Wrap.
