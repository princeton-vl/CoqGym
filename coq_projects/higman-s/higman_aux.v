(*********************************************)
(* This file is part of the 'Higman' contrib *)
(* file : higman_aux.v                       *)
(* contains : auxiliary forest functions     *)   
(*  definitions and their main properties    *)
(* author : W.Delobel                        *)
(*********************************************)

Set Implicit Arguments.
Require Export inductive_wqo.
Require Export tree.
Require Export list_embeding.

Section higman_aux.

Variable A : Set.
Variable leA : A -> A -> Prop.
Hypothesis eqA_dec : forall a a' : A, {a = a'} + {a <> a'}.
Hypothesis leA_dec : forall a a', {leA a a'} + {~ leA a a'}.
Hypothesis leA_trans : forall a a' a'', leA a a' -> leA a' a'' -> leA a a''.

Definition embeds : list A -> list A -> Prop := Embeds leA.
Definition sublist : list (list A) -> list (list A) -> Prop := Embeds (eq (A:= list A)).

Fixpoint firsts (l : list (list A)) : list A :=
match l with 
| nil => nil
| w::ws => match w with 
		| nil => nil
		| a::w' => a :: (firsts ws)
	   end
end.

Definition Tree := tree (list (list A) * (list A)).

Fact eq_Tree_dec : forall t t' : Tree, {t = t'} + {t <> t'}.
Proof.
assert (H : forall l l' : (list (list A) * (list A)), {l = l'} + {l <> l'}).
intros l l'; destruct l as [vs l]; destruct l' as [vs' l'].
elim (list_eq_dec eqA_dec l l'); intro case_l.
subst; elim (list_eq_dec (list_eq_dec eqA_dec) vs vs'); intro case_vs.
subst; left; trivial.
right; intro HF; inversion HF; subst; apply case_vs; trivial.
right; intro HF; inversion HF; subst; apply case_l; trivial.
intros t t'; apply (eq_tree_dec H).
Qed.


Definition root_label (t : Tree) : option A := 
match (root t) with 
  | (l,r) => head r
end.

Fixpoint roots_labels (ts : list Tree) : option (list A) :=  
match ts with 
| nil => Some nil
| t :: ts' => match (root_label t) with 
                  | None => None
                  | Some a => match (roots_labels ts') with 
                                       | Some ts'' => Some (a :: ts'')
                                       | None => None
                                       end
                  end
end.

Inductive is_insert_forest : list Tree -> list A -> A -> list Tree -> Prop :=
| is_if0 : forall w a, is_insert_forest nil w a nil
| is_if2 : forall vs a' ts f w a f' l, 
             is_insert_forest f w a f' ->
             ~(leA a' a) -> 
             is_insert_forest ((node (vs,a'::l) ts) :: f) w a ((node (vs,a'::l) ts) :: f')
| is_if4 : forall vs a'  ts f w a t' l, 
             leA a' a -> 
             is_insert_tree (node (vs,a'::l) ts) w a t' -> 
             is_insert_forest ((node (vs,a'::l) ts):: f) w a (t' :: f) 
with is_insert_tree : Tree -> list A -> A -> Tree -> Prop :=
| is_it1 : forall vs l ts w a rrts, 
             roots_labels ts = Some rrts ->  
             ~ greater leA a rrts ->
             is_insert_tree (node (vs,l) ts) w a (node (vs,l) ((node (w::vs, a::l) ts) :: ts))
| is_it2 : forall l ts w a rrts f', 
             roots_labels ts = Some rrts ->  
             greater leA a rrts ->
             is_insert_forest ts w a f' ->
             is_insert_tree (node l ts) w a (node l f').

Inductive is_forest : list (list A) -> list Tree -> Prop :=
| is_f0 : is_forest nil nil
| is_f1 : forall a w ws f f',  is_forest ws f ->
            greater leA a (bad_subsequence leA leA_dec (firsts ws)) ->
            is_insert_forest f w a f' -> is_forest ((a::w)::ws) f' 
| is_f2 : forall a w ws f,  is_forest ws f ->
            ~ greater leA a (bad_subsequence leA leA_dec (firsts ws)) ->
            is_forest ((a::w)::ws) ((node (w::ws, a::nil) f)::f).

Section through_is_insert.

Variable P : list (list A) -> Tree -> Prop.

Definition P_on_tree (ws : list (list A)) (t : Tree) : Prop := forall t', subtree t' t -> P ws t'.
Definition P_on_forest (ws : list (list A)) (f : list Tree) : Prop := 
  forall t, tree_in_forest t f -> P ws t.

Fact P_on_node : forall a ts ws, P_on_tree ws (node a ts) -> 
forall t, In t ts -> P_on_tree ws t.
Proof.
intros a ts ws Hats t Ht t' Ht'.
apply Hats.
constructor 2.
constructor 1 with t; trivial.
Qed.

Definition from_insert_forest (t : Tree) (a : A) : Prop := 
forall a' l vs ts, t = node (vs, a'::l) ts -> leA a' a.

Hypothesis P_added_node : forall ws w vs a l ts, from_insert_forest (node (vs,l) ts) a ->
  P ws (node (vs,l) ts) -> 
  P ((a::w)::ws) (node (w::vs, a::l) ts).

Hypothesis P_added_node_base : forall ws w a f, P_on_forest ws f ->
P ((a::w)::ws) (node (w::ws,a::nil) f).

Hypothesis P_split : forall ws a t f, P ws (node a (t::f)) -> P ws t -> P ws (node a f).

Hypothesis P_merge : forall ws a t f, P ws (node a f) -> P ws t -> P ws (node a (t::f)).

Hypothesis P_add : forall w ws t, P ws t -> P (w::ws) t.

Lemma P_on_split : forall ws a t f, P_on_tree ws (node a (t::f)) -> P_on_tree ws t ->
P_on_tree ws (node a f).
Proof.
intros ws a t f Hatf Ht t' Ht'.
inversion Ht'; subst.
apply P_split with t.
apply (Hatf (node a (t::f))); constructor; trivial.
apply (Ht t); constructor; trivial.
apply (Hatf t').
constructor 2; inversion H1; subst.
constructor 1 with t'0; try right; trivial.
Qed.

Lemma P_on_merge : forall ws a t f, P_on_tree ws (node a f) -> P_on_tree ws t ->
P_on_tree ws (node a (t::f)).
Proof.
intros ws a t f Haf Ht t' Ht'.
inversion Ht'; subst.
apply P_merge.
apply (Haf (node a f)); constructor; trivial.
apply (Ht t); constructor; trivial.
inversion H1; subst.
elim H; clear H; intro H.
subst.
apply (Ht t'); trivial.
apply (Haf t'); constructor 2;  trivial.
constructor 1 with t'0; trivial.
Qed.

Lemma P_on_add : forall w ws t, P_on_tree ws t -> P_on_tree (w::ws) t.
Proof.
intros w ws t Ht t' Ht'; inversion Ht'; subst.
apply P_add; apply (Ht t); trivial.
apply P_add; apply (Ht t'); trivial.
Qed.

Lemma is_insert_tree_invariant : forall ws t w a t', 
from_insert_forest t a -> 
is_insert_tree t w a t' -> 
P_on_tree ws t -> P_on_tree ((a::w)::ws) t'.
Proof.
intros ws t; induction t as [a | a ts IHt]; intros w a' t' Hfrom Hinsert Ht.
inversion Hinsert; subst.
Focus 2.
simpl in H1; inversion H1; subst.
inversion H2.

apply P_on_merge; trivial.
apply P_on_add; trivial.
intros t'' Ht''; inversion Ht''; subst; trivial.
apply P_added_node; trivial.
apply (Ht (node (vs, l) nil)); constructor.
inversion H2; subst.
inversion H.

inversion Hinsert; subst.
(* not greater *) 
apply P_on_merge; trivial.
apply P_on_add; trivial.
intros t'' Ht''; inversion Ht''; subst; trivial.
apply P_added_node; trivial.
apply (Ht (node (vs, l) ts)); constructor.
inversion H2; subst.
apply P_add.
apply (Ht).
constructor 2.
constructor 1 with t';trivial.

(*greater *)
clear Hinsert H1 H2.
induction H6.
apply P_on_add; trivial.
assert (H7 : P_on_tree ws (node (vs, a' :: l) ts)).
apply (P_on_node Ht); left; trivial.

assert (IHinsert_forest_simpl : P_on_tree ((a0::w)::ws) (node a f')).
apply IHis_insert_forest; trivial.
intros u Hu; apply IHt; right; trivial.
intros a'' l' vs' ts' Heq.
inversion Heq; subst.
apply (Hfrom a'' l' vs' (node (vs, a' :: l) ts :: ts')); trivial.
apply P_on_split with (node (vs,a'::l) ts); trivial.

apply P_on_merge; trivial.
apply P_on_add; trivial.

assert (Hon : P_on_tree ws (node (vs, a' :: l) ts)).
apply (P_on_node Ht); left; trivial.
apply P_on_merge; trivial.
apply P_on_split with (node (vs, a' :: l) ts); trivial.
apply P_on_add; trivial.
apply P_on_add; trivial.

apply IHt with (node (vs, a' :: l) ts); try left; trivial.
intros a'' l' vs' ts' Heq.
inversion Heq; subst.
assumption.
Qed.

Lemma is_insert_forest_invariant : forall ws f w a f', is_insert_forest f w a f' -> 
P_on_forest ws f -> P_on_forest ((a::w)::ws) f'.
Proof.
intros ws f w a f' H; induction H; intros Hf t'' Ht''.
apply P_add; apply (Hf t''); trivial.
inversion Ht''; subst.
elim H1; clear H1; intro H1.
subst.
apply P_add; apply (Hf t''); trivial.
constructor 1 with (node (vs, a' :: l) ts); try left; trivial.
assert (H' : P_on_forest ((a::w)::ws) f').
apply IHis_insert_forest; intros t'0 Ht'0.
apply (Hf t'0).
inversion Ht'0; subst.
constructor 1 with t'1; try right; trivial.
apply (H' t''); constructor 1 with t'; trivial.
inversion Ht''; subst.
elim H1; clear H1; intro H1.
subst.
assert (Hfrom : from_insert_forest (node (vs, a' :: l) ts) a).
intros a'' l' vs' ts' Heq.
inversion Heq; subst; trivial.
generalize t'' H2; fold P_on_tree; apply (is_insert_tree_invariant (ws:=ws) Hfrom H0). 
intros t'1 Ht'1; apply (Hf t'1).
constructor 1 with (node (vs, a' :: l) ts); try left; trivial.
apply P_add.
apply (Hf t'').
constructor 1 with t'0; try right; trivial.
Qed.

Lemma P_on_is_forest : forall f ws, is_forest ws f -> 
 P_on_forest ws f.
Proof.
intros f ws H; induction H; intros t Ht.
inversion Ht; subst.
inversion H.
apply (is_insert_forest_invariant (ws:=ws) H1); trivial.
inversion Ht; subst.
elim H1; clear H1; intro H1; subst.
inversion H2; subst.
apply P_added_node_base; trivial.
apply P_add.
apply IHis_forest.
trivial.
apply P_add.
apply IHis_forest.
constructor 1 with t'; trivial.
Qed.

End through_is_insert.

Definition no_nil (t : Tree) : Prop := forall vs l ts, t = node (vs,l) ts -> l <> nil.

Fact in_is_forest_no_nil : forall f ws, is_forest ws f -> 
 forall t, tree_in_forest t f -> no_nil t.
Proof.
intros f ws Hf; assert (H : P_on_forest (fun (_ : list (list A)) => no_nil) ws f). 
apply P_on_is_forest; trivial; intros; intros ws' l' ts' H'; subst.
inversion H'; subst; intro HF.
inversion HF.
inversion H'; subst; intro HF.
inversion HF.
inversion H'; subst.
apply (H ws' l' (t::ts')); trivial.
inversion H'; subst.
apply (H ws' l' f0); trivial.
intros t Ht; apply (H t); trivial.
Qed.


Fact is_insert_tree_same_root : forall t t' w a, 
is_insert_tree t w a t' -> root_label t = root_label t'.
Proof.
intros t t' w a H; induction H; simpl; destruct l; simpl; trivial.
Qed.

Fact is_insert_forest_same_roots : forall f f' w a, 
is_insert_forest f w a f' -> roots_labels f = roots_labels f'.
Proof.
intros f f' w a H; induction H; simpl; trivial.
rewrite IHis_insert_forest; trivial.
destruct (roots_labels f); simpl.
2 : destruct (root_label t'); trivial.
rewrite <- (is_insert_tree_same_root H0); simpl; trivial.
Qed.
 
Fact roots_labels_exist : forall ts, (forall t, In t ts ->  no_nil t) -> 
  exists rrts, roots_labels ts = Some rrts.
Proof.
intro ts; induction ts as [|t ts IHts]; intro Hts; simpl.
exists (nil (A:=A)); trivial.
elim IHts.
2: intros t0 Ht0; apply Hts; right; trivial.
intros rrts Hrrts.
rewrite Hrrts; simpl.
destruct t as [l tf]; destruct l as [ws bs].
assert (Hts' : no_nil (node (ws, bs) tf)).
apply Hts; try left; trivial.
destruct bs as [ | b bs]; simpl.
elim (Hts' ws nil tf); trivial.
exists (b::rrts); trivial.
Qed.

Fact insert_forest_aux_get : forall f a w, 
  (forall t, In t f -> no_nil t /\ exists t', is_insert_tree t w a t') ->
  exists f', is_insert_forest f w a f'.
Proof.
intro f; induction f as [|t f IHf]; intros a w Hf.
exists (nil (A:=Tree)); constructor.
assert (H: exists f' : list Tree, is_insert_forest f w a f').
apply IHf; intros t' Ht'; apply Hf; try right; trivial.
clear IHf; destruct t as [l ts].
destruct l as [ws bs]; destruct bs as [|b bs].
assert (H' : In (node (ws, nil) ts) (node (ws, nil) ts :: f)).
left; trivial.
elim (Hf (node (ws, nil) ts) H'); intros HF dd; elim HF with ws (nil (A:=A)) ts; trivial.

elim (leA_dec b a); intro case_b_a.
assert (H' : In (node (ws, b::bs) ts) (node (ws, b::bs) ts :: f)).
left; trivial.
elim (Hf (node (ws, b::bs) ts) H'); intros H1 H2.
elim H2; clear H2; intros t' Ht'.
exists (t'::f); constructor 3; trivial.
elim H; clear H; intros f' Hf'.
exists ((node (ws, b :: bs) ts)::f'); constructor 2; trivial.
Qed.


Fact insert_tree_get : forall t w a, 
  (forall t', subtree t' t -> no_nil t') ->
  exists t', is_insert_tree t w a t'.
Proof.
intro t; induction t as [l | l ts IHt]; intros w a Ht.
destruct l as [ws bs].
exists (node (ws, bs) (node (w::ws, a::bs) nil :: nil)); 
constructor 1 with (nil (A := A)); trivial.
intro H; inversion H; subst.

destruct l as [ws bs].
destruct bs as [|b bs].
assert (Hnn : no_nil (node (ws, nil) ts)).
assert (Hd : subtree (node (ws,nil) ts) (node (ws,nil) ts)).
constructor 1; trivial.
apply (Ht (node (ws,nil) ts) Hd).
elim (Hnn ws nil ts); trivial.
assert (H' : forall t, In t ts -> no_nil t /\ exists t', is_insert_tree t w a t').
intros u Hu.
assert (H'' : subtree u (node (ws, b :: bs) ts)).
constructor 2; trivial.
constructor 1 with u; trivial.
constructor 1; trivial.
split.
apply (Ht u H'').
apply IHt; trivial.
intros t' Ht' ; assert (H' : subtree t' (node (ws, b :: bs) ts)).
apply subtree_trans with u; trivial.
apply (Ht t' H' ).
assert (H : forall t, In t ts -> no_nil t).
intros u Hu; elim (H' u Hu); trivial.

elim (roots_labels_exist ts H); intros rrts Hrrts.
elim (greater_dec leA leA_dec a rrts); intro case_greater.
elim (insert_forest_aux_get ts H'); intros f' Hf'.
exists (node (ws, b::bs) f'); constructor 2 with rrts; trivial.
exists (node (ws, b :: bs) (node (w::ws, a::b::bs) ts :: ts)); constructor 1 with rrts; trivial.
Qed.

Fact insert_forest_get : forall f a w ws, is_forest ws f -> exists f', is_insert_forest f w a f'.
Proof.
intros f a w ws Hisf; 
 generalize (in_is_forest_no_nil Hisf); clear Hisf ws.
induction f as [|t f IHf]; intro Hf.
exists (nil (A:=Tree)); constructor.
assert (H : forall t', subtree t' t -> no_nil t').
intros t' Ht'.
assert (H' : tree_in_forest t' (t :: f)).
constructor 1 with t; try left; trivial.
apply Hf; trivial.
destruct t as [l ts].
destruct l as [ws bs]; destruct bs as [|b bs].
assert (Ht : subtree (node (ws, nil) ts) (node (ws, nil) ts)).
constructor 1; trivial.
elim (H (node (ws,nil) ts) Ht ws nil ts); trivial.
assert (H' : exists f', is_insert_forest f w a f').
apply IHf.
intros t Ht; apply Hf.
inversion Ht; subst.
constructor 1 with t'; try right; trivial.
elim H'; clear H'; intros f' Hf'.
elim (leA_dec b a); intro case_b_a.
elim (insert_tree_get w a H); intros t' Ht'. 
exists (t'::f); constructor 3; trivial.
exists (node (ws, b :: bs) ts :: f'); constructor 2; trivial.
Qed.


Fact nil_forest : forall ws, is_forest ws nil -> ws = nil.
Proof.
intro ws; induction ws as [| w ws IHw]; intros H1; trivial.
inversion H1; subst.
inversion H5; subst.
generalize (IHw H2); intro; subst.
simpl in H3; inversion H3.
Qed.


Fact roots_labels_greater_get_tree : 
forall ts rrts, roots_labels ts = Some rrts ->
forall a, greater leA a rrts -> exists vs, exists b, exists bs, exists ts', 
leA b a /\ In (node (vs, b::bs) ts') ts.
Proof.
intro ts; induction ts as [|t ts IHts]; intros rrts Hrrts a Ha.
simpl in Hrrts; inversion Hrrts; subst.
inversion Ha.
generalize Hrrts; simpl.
destruct t as [l ts']; destruct l as [vs bs]; unfold root_label; simpl.

destruct bs as [|b bs]; simpl.
intro HF; inversion HF.
generalize (refl_equal (roots_labels ts)); pattern (roots_labels ts) at -1; case (roots_labels ts).
intros rrts' H1 H2; inversion H2; subst.
inversion Ha; subst.
exists vs; exists b; exists bs; exists ts'; split; try left; trivial.
elim (IHts rrts') with a; trivial.
intros vs' H; elim H; clear H; intros b' H; elim H; clear H; intros bs' H.
elim H; clear H; intros ts'' H; elim H; clear H; intros H H'.
exists vs'; exists b'; exists bs'; exists ts''; split; try right; trivial.
intros dd HF; inversion HF.
Qed.

Fact is_insert_tree_neq : forall t, 
forall w a t', is_insert_tree t w a t' -> t <> t'.
Proof.
intro t; induction t as [l | l ts IHl]; intros w a t' Ht.
inversion Ht; subst.
intro HF; inversion HF; subst.
inversion H1; subst.
inversion H2.
inversion Ht; subst.
intro HF; inversion HF.
generalize (node (w :: vs, a :: l0) ts) H0; clear H1 Ht HF IHl H0. 
induction ts as [|t ts IHts]; intros t' Ht; inversion Ht.
apply IHts with t'; trivial.
elim (roots_labels_greater_get_tree ts H1 H2); intros vs H'.
elim H'; clear H'; intros b H'; elim H'; clear H'; intros bs H'.
elim H'; clear H'; intros ts' H'; elim H'; clear H'; intros H3 H4.
generalize (IHl (node (vs, b :: bs) ts') H4); intro IHl'.
assert (IHl'' : forall u, In u ts -> forall (w : list A) (a : A) (t' : Tree),
        is_insert_tree u w a t' -> u <> t').
intros u Hu; apply IHl; trivial.
clear Ht H2 H1 IHl.
induction H6.
inversion H4.
elim H4; clear H4; intro H4.
inversion H4; subst.
elim H; trivial.
intro HF; inversion HF; subst.
apply (IHis_insert_forest); trivial.
intros u Hu; apply IHl''; try right; trivial.

elim H4; clear H4; intro H4.
inversion H4; subst.
intro HF; inversion HF; subst.
apply (IHl' w a (node (vs, b :: bs) ts')); trivial.
intro HF; inversion HF; subst.
assert (Hin : In (node (vs0, a' :: l0) ts) (node (vs0, a' :: l0) ts :: f)).
left; trivial.
apply (IHl'' (node (vs0, a' :: l0) ts) Hin w a (node (vs0, a' :: l0) ts)); trivial.
Qed.


Lemma is_insert_forest_neq_aux : forall f a w f', 
(exists vs, exists a', exists l, exists ts, In (node (vs,a'::l) ts) f /\ leA a' a) ->
is_insert_forest f w a f' -> f <> f'.
Proof.
intro f; induction f as [|t f IHf]; intros a w f' Hf Hf'.
elim Hf; clear Hf; intros vs Hf; elim Hf; clear  Hf; intros a' Hf.
elim Hf; clear Hf; intros l Hf; elim Hf; clear Hf; intros ts Hf; elim Hf; clear Hf; intros Hf1 Hf2.
inversion Hf1.
elim Hf; clear Hf; intros vs Hf; elim Hf; clear  Hf; intros a' Hf.
elim Hf; clear Hf; intros l Hf; elim Hf; clear Hf; intros ts Hf; elim Hf; clear Hf; intros Hf1 Hf2.
elim Hf1; clear Hf1; intro Hf1.
subst t; inversion Hf'; subst.
elim H8; trivial.
intro HF; inversion HF; subst.
generalize H8 (refl_equal (node (vs, a' :: l) ts)); apply is_insert_tree_neq.

inversion Hf'; subst.
intro HF; inversion HF; subst.
generalize H1 (refl_equal f'0); apply IHf.
exists vs; exists a'; exists l; exists ts; split; trivial.
intro HF; inversion HF; subst.
generalize H5 (refl_equal (node (vs0, a'0 :: l0) ts0)); apply is_insert_tree_neq.
Qed.


Fact is_insert_forest_neq : forall f ws, is_forest ws f ->
   forall a w f', greater leA a (bad_subsequence leA leA_dec (firsts ws)) ->
   is_insert_forest f w a f' -> f <> f'.
Proof.
intros f ws Hws a w f' Hg; apply is_insert_forest_neq_aux; trivial.
clear w f'.
generalize a Hg; clear a Hg.
induction Hws; intros a' Hg.
inversion Hg.
generalize Hg; clear Hg; simpl in |- *.
elim (greater_dec leA leA_dec a (bad_subsequence leA leA_dec (firsts ws)));
intros case_ws Hg.
elim (IHHws a' Hg); intros vs H'.
elim H'; clear H'; intros a'' H'.
elim H'; clear H'; intros l H'.
elim H'; clear H'; intros ts H'.
elim H'; clear H'; intros H1 H2.
clear IHHws Hws case_ws Hg.
induction H0.
inversion H1.
elim H1; clear H1; intro H1.
inversion H1; subst.
exists vs; exists a''; exists l; exists ts; split; try left; trivial.
elim (IHis_insert_forest H H1); intros vs' H4.
elim H4; clear H4; intros a''' H4.
elim H4; clear H4; intros l' H4.
elim H4; clear H4; intros ts' H4.
elim H4; clear H4; intros H4 H5.
exists vs'; exists a'''; exists l'; exists ts'.
split; try right; trivial.
elim H1; clear H1; intro H1.
inversion H1; subst.
generalize (is_insert_tree_same_root H3).
unfold root_label; simpl; intro H5.
destruct t' as [lbl t'ts].
simpl in H5. 
destruct lbl as [t'vs t'l].
destruct t'l; inversion H5; subst.
exists t'vs; exists a0; exists t'l; exists t'ts; split; try left; trivial.

exists vs; exists a''; exists l; exists ts; split; try right; trivial.
elim case_ws; trivial.
generalize Hg; clear Hg; simpl.
elim (greater_dec leA leA_dec a (bad_subsequence leA leA_dec (firsts ws))); intros case_ws Hg.
elim H; trivial.
inversion Hg; subst.
exists (w::ws); exists a; exists (nil (A:=A)); exists f; split; try left; trivial.
elim (IHHws a' H2); intros vs' H3.
elim H3; clear H3; intros a'' H3; elim H3; clear H3; intros l' H3.
elim H3; clear H3; intros ts' H3; elim H3; clear H3; intros H3 H4.
exists vs'; exists a''; exists l'; exists ts'; split; try right; trivial.
Qed.

End higman_aux.
