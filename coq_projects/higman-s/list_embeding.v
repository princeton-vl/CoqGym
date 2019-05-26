(*********************************************)
(* This file is part of the 'Higman' contrib *)
(* file : list_embeding.v                    *)
(* contains : definition  of the embeding    *)   
(*  relation on lists and basic lemmas       *)
(* author : W.Delobel                        *)
(*********************************************)

Set Implicit Arguments.
Require Export List.
Require Export inductive_wqo.

Section definitions.

Variable A : Set.
Variable leA : A -> A -> Prop.
Hypothesis leA_dec : forall a a', {leA a a'} + {~ leA a a'}.

Inductive Embeds : list A -> list A -> Prop :=
| emb0 : Embeds nil nil
| emb1 : forall v w a, Embeds v w -> Embeds v (a::w)
| emb2 : forall v w a b, Embeds v w -> leA a b -> Embeds (a::v) (b::w).

Inductive sorted : list A -> Prop :=
|srt0 : sorted nil
|srt1 : forall a, sorted (a::nil)
|srt2 : forall a a' l, leA a' a -> sorted (a'::l) -> sorted (a::(a'::l)).

End definitions.


Section list_embeding.

Variable A : Set.
Variable leA : A -> A -> Prop.
Hypothesis eqA_dec : forall a a' : A, {a = a'} + {a <> a'}.
Hypothesis leA_dec : forall a a', {leA a a'} + {~ leA a a'}.
Hypothesis leA_trans : forall a a' a'', leA a a' -> leA a' a'' -> leA a a''.

Definition embeds : list A -> list A -> Prop := Embeds leA.
Definition sublist : list (list A) -> list (list A) -> Prop := Embeds (eq (A:= list A)).

Lemma bad_cons : forall a l, bad embeds (a::l) -> bad embeds l.
Proof.
intros a l H H'.
apply H; constructor 2; trivial.
Qed.

Fact nil_embeds : forall w, embeds nil w.
Proof.
induction w; constructor; trivial.
Qed.

Lemma good_remove_letter : forall a w ws, 
good embeds (w::ws) -> good embeds ((a::w)::ws).
Proof.
intros a w ws.
assert (H : forall w', w' = w::ws -> good embeds w' -> good embeds ((a::w)::ws)).
2 : apply (H (w::ws)); trivial.
intros w' w'_is Hg; induction Hg.
inversion w'_is; subst.
constructor 1.
induction H.
constructor 1; constructor; trivial.
constructor 2; apply IHgreater; trivial.
inversion w'_is; subst.
constructor 2; trivial.
Qed.

Lemma bad_remove_letter : forall a w ws, 
bad embeds ((a::w)::ws) -> bad embeds (w::ws).
Proof.
intros a w ws Hb Hg; apply Hb; apply good_remove_letter; trivial.
Qed.

Fact sublist_refl : forall l, sublist l l.
Proof.
induction l; [constructor 1 | constructor 3; trivial; apply IHl]; trivial.
Qed.

Fact good_sublist : forall l l', sublist l l' -> good embeds l -> good embeds l'.
Proof.
intros l l' H; induction H; trivial.
intro H'; constructor 2; apply IHEmbeds; trivial.
subst.
intro H'; inversion H'; subst. 
constructor 1.
clear IHEmbeds H'; induction H; subst; trivial.
constructor 2; apply IHEmbeds; trivial.
inversion H1; subst.
constructor 1; trivial.
constructor 2; apply IHEmbeds; trivial.
constructor 2; apply IHEmbeds; trivial.
Qed.

Fact bad_sublist :  forall l l', sublist l' l -> bad embeds l -> bad embeds l'.
Proof.
intros l l' H Hb HF; apply Hb; apply (good_sublist H); trivial.
Qed.

Fact greater_add_letter : forall a w ws, greater embeds w ws ->
greater embeds (a :: w) ws.
Proof.
intros a w ws H; induction H.
constructor 1; constructor 2; trivial.
constructor 2; trivial.
Qed.

Fact greater_remove_letter : forall a w ws, 
greater embeds w ws -> greater embeds (a :: w) ws.
Proof.
intros a w ws H; induction H; simpl in |- *; trivial.
constructor; constructor; trivial.
constructor 2; trivial.
Qed.

Fact sorted_remove_head : forall a l, sorted leA (a::l) -> sorted leA l.
Proof.
intros a l H; inversion H; subst; trivial.
constructor.
Qed.

Lemma sorted_remove_inner : forall a a' l, sorted leA (a::a'::l) -> sorted leA (a::l).
Proof.
intros a a' l; assert (H : forall l', sorted leA l' -> forall l, l' = a::a'::l -> sorted leA (a::l)).
2 : intro Hl'; apply (H (a::a'::l) Hl' l); trivial.
clear l; intros l' H; induction H; intros t l'is; inversion l'is; subst.
inversion H0; subst.
constructor.
constructor 3; trivial.
apply leA_trans with a'; trivial.
Qed.


Fixpoint merge_label (ws : list (list A)) (l : list A) {struct l} : list (list A) :=
match ws,l with 
| w::ws', a::l' => (a::w)::(merge_label ws' l')
| ws', nil => ws'
| nil, _ => nil
end.

Lemma good_merge : forall vs, good embeds vs -> 
forall l, sorted leA l -> good embeds (merge_label vs l).
Proof.
intros vs H; induction H; intros l Hl.
destruct l as [|a' l]; simpl.
constructor 1; trivial.
constructor 1; generalize a' l Hl; clear Hl l a'.
induction H; intros a'' l Hl.
destruct l as [|a''' l]; simpl.
constructor 1.
constructor 2; trivial.
constructor 1.
constructor 3; trivial.
inversion Hl; subst; trivial.
destruct l as [|a''' l]; simpl.
constructor 2.
apply greater_add_letter; trivial.
constructor 2; trivial.
apply (IHgreater a'' l).
apply sorted_remove_inner with a'''; trivial.
destruct l as [|a' l].
simpl.
constructor 2; trivial.
simpl.
constructor 2; apply IHgood; trivial.
apply sorted_remove_head with a'; trivial.
Qed.

End list_embeding.

