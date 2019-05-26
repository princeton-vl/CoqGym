Require Export List. 
Require Export ListSet. 
Set Implicit Arguments.
Unset Strict Implicit. 
 
(*********************************************************************) 
(*                  Some List Functions                              *) 
(*********************************************************************) 

Definition front (A : Set) (l : list A) : list A := rev (tail (rev l)). 
 
Definition last (A : Set) (l : list A) := head (rev l). 
 
Fixpoint take (A : Set) (n : nat) (l : list A) {struct l} : 
 list A :=
  match l with
  | nil => nil (A:=A)
  | a :: l' => match n with
               | O => nil (A:=A)
               | S m => a :: take m l'
               end
  end. 

Fixpoint allunique (A : Set) (l : list A) {struct l} : Prop :=
  match l with
  | nil => True
  | x :: l' => IF In x l' then False else allunique l'
  end. 
 
(*********************************************************************) 
(*                  Some Functions for ListSet                       *) 
(*********************************************************************) 
 
Definition IsEmpty (A : Set) (B : set A) := forall x : A, ~ set_In x B. 
 
Definition Included (A : Set) (B C : set A) :=
  forall x : A, set_In x B -> set_In x C. 
 
Lemma AllWaysIncluded : forall (A : Set) (B : set A), Included B B. 
intros. 
unfold Included in |- *. 
auto. 
 
Qed. 
 
(*********************************************************************) 
(*                  Some Results about ListSet                       *) 
(*********************************************************************) 
Section ListSetLemmas. 
 
Variable A : Set. 
 
Hypothesis Aeq_dec : forall x y : A, {x = y} + {x <> y}. 
 
Lemma Set_union1 :
 forall (B C : set A) (x : A),
 set_In x (set_union Aeq_dec B C) -> ~ set_In x B -> set_In x C. 
intros. 
cut (set_In x B \/ set_In x C). 
intro H1; elim H1. 
tauto. 
 
auto. 
 
eapply (set_union_elim (Aeq_dec:=Aeq_dec)); auto. 
 
Qed. 
 
Lemma Set_union2 :
 forall (B C : set A) (x : A),
 set_In x (set_union Aeq_dec B C) -> set_In x (set_union Aeq_dec C B). 
intros. 
cut (set_In x C \/ set_In x B). 
intro; apply set_union_intro. 
auto. 
 
cut (set_In x B \/ set_In x C). 
tauto. 
 
eapply (set_union_elim (Aeq_dec:=Aeq_dec)). 
auto. 
 
Qed. 
 
 
Lemma Set_remove2 :
 forall (B : set A) (x y : A),
 set_In x (set_remove Aeq_dec y B) -> set_In x B. 
intro; intro; intro. 
induction  B as [| a B HrecB]. 
auto. 
 
simpl in |- *. 
elim (Aeq_dec y a). 
intros. 
right. 
auto. 
 
simpl in |- *. 
intro. 
intro. 
elim H. 
intro. 
left; auto. 
 
intro. 
right. 
auto. 
Qed. 
 
 
Lemma Set_add1 :
 forall (B : set A) (x y : A),
 set_In x (set_add Aeq_dec y B) -> x <> y -> set_In x B. 
intros. 
cut (x = y \/ set_In x B). 
intro. 
elim H1. 
intro. 
absurd (x = y). 
auto. 
 
auto. 
 
intro. 
auto. 
 
eapply (set_add_elim (A:=A) (Aeq_dec:=Aeq_dec) (a:=x) (b:=y) (x:=B)). 
auto. 
 
Qed. 
 
 
Lemma Set_add2 :
 forall (B : set A) (x y : A),
 x <> y -> ~ set_In x B -> ~ set_In x (set_add Aeq_dec y B). 
intros. 
intro. 
apply H0. 
eapply (Set_add1 (B:=B) (x:=x) (y:=y)); auto. 
 
Qed. 
 
End ListSetLemmas. 
 
Hint Unfold IsEmpty Included. 
Hint Resolve Set_remove2 Set_add1 AllWaysIncluded Set_union1 Set_union2
  Set_add2. 
 
 
 
Lemma Listeq_dec :
 forall A : Set,
 (forall a b : A, {a = b} + {a <> b}) ->
 forall x y : list A, {x = y} + {x <> y}. 
simple induction x. 
simple induction y. 
auto. 
 
intros. 
right. 
unfold not in |- *; intro D; discriminate D. 
 
intros. 
induction  y as [| a0 y Hrecy]. 
right; unfold not in |- *; intro D; discriminate D. 
 
elim (H0 y). 
intro. 
rewrite a1. 
elim (H a a0). 
intro. 
rewrite a2. 
left; auto. 
 
intro. 
right. 
unfold not in |- *. 
unfold not in b. 
intro; apply b. 
injection H1. 
auto. 
 
unfold not in |- *; intro. 
right. 
intro; apply b. 
injection H1. 
auto. 
 
Qed. 
 
Hint Resolve Listeq_dec. 
 
 
Lemma Prodeq_dec :
 forall A B : Set,
 (forall x y : A, {x = y} + {x <> y}) ->
 (forall v w : B, {v = w} + {v <> w}) ->
 forall c d : A * B, {c = d} + {c <> d}. 
intros. 
elim c. 
elim d. 
intros. 
elim (H a a0); intro. 
rewrite a1. 
elim (H0 b b0); intro. 
rewrite a2. 
left; auto. 
 
right. 
intro. 
apply b1. 
injection H1; auto. 
 
right; intro; apply b1. 
injection H1; auto. 
 
Qed. 
 
Hint Resolve Prodeq_dec.