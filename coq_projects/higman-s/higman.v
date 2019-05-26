(*********************************************)
(* This file is part of the 'Higman' contrib *)
(* file : higman.v                           *)
(* contains : proof of higman's lemma        *)   
(*  based upon a proof by M.Seisenberger     *)
(* author : W.Delobel                        *)
(*********************************************)

Set Implicit Arguments.
Require Export inductive_wqo.
Require Export tree.
Require Export higman_aux.

Section higman.

Variable A : Set.
Variable leA : A -> A -> Prop.
Hypothesis eqA_dec : forall a a' : A, {a = a'} + {a <> a'}.
Hypothesis leA_dec : forall a a', {leA a a'} + {~ leA a a'}.
Hypothesis leA_trans : forall a a' a'', leA a a' -> leA a' a'' -> leA a a''.

Definition embeds : list A -> list A -> Prop := (higman_aux.embeds leA).
Definition sublist : list (list A) -> list (list A) -> Prop := (higman_aux.sublist (A:=A)).
Definition Tree := (higman_aux.Tree A).
Definition is_forest := (higman_aux.is_forest leA leA_dec).
Definition is_insert_forest := (higman_aux.is_insert_forest leA).
Definition is_insert_tree := (higman_aux.is_insert_tree leA).

Definition sub_seq_in_lbl (ws : list (list A)) (t : Tree) : Prop := 
forall vs l ts, t = node (vs,l) ts -> sublist (merge_label vs l) ws.

Lemma sub_seq_in_forest : forall ws f,
is_forest ws f -> P_on_forest sub_seq_in_lbl ws f.
Proof.
intros ws f Hws.
apply P_on_is_forest with leA leA_dec; intros.
(* P_added_node *)
unfold sub_seq_in_lbl; simpl; intros.
inversion H1; subst.
simpl.
constructor 3; trivial.
unfold sub_seq_in_lbl in H0; apply H0 with ts0; trivial.
(* P_added_node_base *)
unfold sub_seq_in_lbl; simpl; intros.
inversion H0; subst; destruct ws0; simpl; apply sublist_refl with (A:=A).
(* P_split *)
unfold sub_seq_in_lbl; simpl; intros.
inversion H1; subst.
unfold sub_seq_in_lbl in H; apply H with (t::ts); trivial.
(* P_merge *) 
unfold sub_seq_in_lbl; simpl; intros.
inversion H1; subst.
unfold sub_seq_in_lbl in H; apply H with f0; trivial.
(* P_add *)
unfold sub_seq_in_lbl in *; simpl in *.
intros ws' l ts Ht; constructor 2; apply (H ws' l ts Ht).
apply Hws.
Qed.

Definition sorted_in_label (t : Tree) : Prop := 
forall vs l ts, t = node (vs, l) ts -> sorted leA l.

Lemma sorted_in_forest : forall ws f, 
is_forest ws f -> forall t, tree_in_forest t f -> sorted_in_label t.
Proof.
intros ws f Hf.
assert (H : P_on_forest (fun (_:list (list A)) => sorted_in_label) ws f).
2 : intros t Ht; apply (H t Ht); trivial.
apply P_on_is_forest with leA leA_dec; intros; trivial.
(* P_added_node *)
destruct l as [|a' l].
	(* l = nil *)
intros vs' l' ts' H'; inversion H'; subst.
constructor 2.
	(* l <> nil *)
intros vs' l' ts' H'; inversion H'; subst.
constructor 3.
apply (H a' l vs ts'); trivial.
apply (H0 vs (a'::l) ts'); trivial.
(* P_added_node_base *)
intros vs' l' ts' H'; inversion H'; subst.
constructor 2.
(* P_split *)
intros vs' l' ts' H'; inversion H'; subst.
apply (H vs' l' (t::ts')); trivial.
(* P_merge *)
intros vs' l' ts' H'; inversion H'; subst.
apply (H vs' l' f0); trivial.
Qed.

Definition bad_seq_in_lbl (t : Tree) : Prop := 
forall vs l ts, t = node (vs,l) ts -> bad embeds vs.

Lemma bad_seqs_in_forest : forall ws, bad embeds ws -> 
  forall f, is_forest ws f ->  forall t, tree_in_forest t f -> bad_seq_in_lbl t.
Proof.
intros ws Hws f Hf t Ht vs l ts H.
generalize (sorted_in_forest Hf Ht H); intro H2.
assert (H' : bad embeds (merge_label vs l)).
apply (bad_sublist (leA:=leA) (sub_seq_in_forest Hf Ht H)); trivial.
intro HF; apply H'.
apply good_merge with (leA:=leA); trivial.
Qed.

Definition ltF : list Tree -> list Tree -> Prop := fun f' => fun f => exists w, exists a,
is_insert_forest f w a f'  /\ (forall t, tree_in_forest t f' -> bad_seq_in_lbl t) /\ f<>f'.

Fact acc_ltF_nil : Acc ltF nil.
constructor; intros f Hf.
elim Hf; clear Hf; intros w H; elim H; clear H; intros a H; 
elim H; clear H; intros H1 H; elim H; clear H; intros H2 H3.
inversion H1; subst.
elim H3; trivial.
Qed.

Fact acc_ltF_cons : forall f t, Acc ltF f -> Acc ltF (t::nil) -> Acc ltF (t::f).
Proof.
intros f t Acc_f; generalize t; clear t; induction Acc_f as [f acc_f IHf].
assert (H : forall f', Acc ltF f' -> forall t, f' = t::nil -> Acc ltF (t::f)).
2:intros; apply (H (t::nil)); trivial.
intros f' Hf'; induction Hf' as [f' acc_f' IHf'].
intros; constructor.
intros f'' H2.
elim H2; clear H2; intros w H2; elim H2; clear H2; intros a H2.
elim H2; clear H2; intros H2 H3; elim H3; clear H3; intros H3 H4.
inversion H2; subst.
(* case ~ leA a' a *)
apply IHf; trivial.
exists w; exists a; repeat split; trivial.
intros t Ht; apply (H3 t); trivial.
inversion Ht; subst.
constructor 1 with t'; trivial; try right; trivial.
intro; subst; apply H4; trivial.
constructor; apply acc_f'; trivial.
(* case leA a' a *)
apply IHf' with (t'::nil); trivial.
exists w; exists a; repeat split; trivial.
apply (is_if4 (leA := leA) (vs:=vs) (a':= a') (ts:=ts)); trivial.
intros u Hu; inversion Hu; subst.
apply (H3 u).
elim H; clear H; intro H.
subst t'0; constructor 1 with t'; try left; trivial.
inversion H.
intro H; subst; apply H4; inversion H; trivial.
Qed.

Lemma is_forest_roots_labels : forall ws f, is_forest ws f -> 
roots_labels f = Some (bad_subsequence leA leA_dec (firsts ws)).
Proof.
intros ws f Hws; induction Hws; simpl; trivial.
elim (greater_dec leA leA_dec a (bad_subsequence leA leA_dec (firsts ws))); intro case_ws.
rewrite <- IHHws.
symmetry; generalize H0; apply is_insert_forest_same_roots.
elim case_ws; trivial.
rewrite IHHws; simpl.
elim (greater_dec leA leA_dec a (bad_subsequence leA leA_dec (firsts ws))); intro case_ws.
elim H; trivial.
trivial.
Qed.

Lemma acc_ltF_single : forall ws, Acc (continues embeds) ws ->
  forall l a bs, Acc (continues leA) bs ->
  forall ts, Acc ltF ts -> 
  forall t, root t = (ws,a::l) /\ subtrees t = ts /\ Some bs = roots_labels ts -> 
  Acc ltF (t::nil).
Proof.
intros ws acc_ws; induction acc_ws as [ws acc_ws IHws]; intros l a.
intros bs acc_bs; induction acc_bs as [bs acc_bs IHbs].
intros ts acc_ts; induction acc_ts as [ts acc_ts IHts].
intros t Ht; elim Ht; clear Ht; intros H1 H2; elim H2; clear H2; intros H2 H3.
constructor; intros f Hf.
elim Hf; clear Hf; intros wf Hf.
elim Hf; clear Hf; intros af Hf.
elim Hf; clear Hf; intros Hf1 Hf2.
elim Hf2; clear Hf2; intros Hf2 Hf3.
destruct f as [|t' f].
(* case nil *)
inversion Hf1.
(* case t' f *)
cut (f = nil).
intro; subst f.
inversion Hf1.
(* case ~ leA a' af *)
subst f w a0 t' t f'; clear H7.
elim Hf3; trivial.
(* case leA a' af *)
subst w a0 t' t f.
inversion H8; subst.
	(* case ~ greater af rrts *)
apply IHbs with (y := af::bs) (ts := node (wf :: vs, af :: a' :: l) ts0 :: ts0); trivial.
constructor.
simpl in H3.
rewrite H10 in H3; inversion H3; trivial.
apply acc_ltF_cons; trivial.
constructor; simpl in acc_ts; trivial.
simpl in H1; inversion H1; subst.
apply (IHws (wf::ws)) with (ts:= ts0) (bs := bs) (a:=af) (l:=a::l); trivial.

constructor; trivial.
intro HF; assert (Hbil : bad_seq_in_lbl (node (wf :: ws, af :: a :: l) ts0)).
apply (Hf2 (node (wf :: ws, af :: a :: l) ts0)); simpl.
constructor 1 with (node (ws, a :: l) (node (wf :: ws, af :: a :: l) ts0 :: ts0)); try left; trivial.
constructor 2.
constructor 1 with (node (wf :: ws, af :: a :: l) ts0); constructor; trivial.
	(* Hbil prooved *)
apply (Hbil (wf::ws) (af::a::l) ts0); trivial.
constructor; trivial.
constructor; apply acc_bs.
constructor; apply acc_ts.
simpl in *; repeat split; trivial.
inversion H1; subst; trivial.
repeat split; simpl; trivial.
simpl in H3; rewrite <- H3; simpl; trivial.

	(* case greater af rrts *)
apply IHts with (y := f'); trivial.
exists wf; exists af.
repeat split; simpl; trivial.
intros u Hu; apply (Hf2 u); inversion Hu; subst.
constructor 1 with (node (vs, a' :: l0) f'); try left; trivial.
constructor 2.
constructor 1 with t'; trivial.
intro; subst; apply Hf3; trivial.
repeat split; simpl; trivial.
simpl in H3; rewrite H3.
generalize H11; apply is_insert_forest_same_roots.
(* proof f = nil *)
destruct f; trivial.
inversion Hf1; subst.
inversion H7.
Qed.



Lemma higman_aux : 
  forall bs, Acc (continues leA) bs -> 
  forall f, Acc ltF f -> 
  forall ws, bs = bad_subsequence leA leA_dec (firsts ws) /\ is_forest ws f -> 
  bad embeds ws -> Acc (continues embeds) ws.
Proof.
intros bs acc_bs; induction acc_bs as [bs acc_bs IHbs].
intros f acc_f; induction acc_f as [f acc_f IHf].
intros ws H; elim H; clear H; intros H1 H2 H3.
constructor; intros ws' Hws'.
Unset Regular Subst Tactic.
inversion Hws'; subst.
Set Regular Subst Tactic.
induction a as [| a w IHw].
(* case nil *)
constructor; intros y Hy; inversion Hy; subst.
elim H0; constructor 1. 
unfold embeds; apply (nil_embeds).
(* case <> nil *)
elim (greater_dec leA leA_dec a (bad_subsequence leA leA_dec (firsts ws))); intro case_a_bs.
(* case greater a badSub (Fsts ws) *)
elim (insert_forest_get a w H2); intros f' Hf'.
apply IHf with f'; trivial.
exists w; exists a; repeat split; trivial.
apply bad_seqs_in_forest with ((a::w)::ws); trivial.
intro HF; inversion HF; subst.
apply H; trivial.
apply H3; trivial.
constructor 2 with f; trivial.
apply (is_insert_forest_neq (leA:=leA) (leA_dec:=leA_dec)) with ws a w; trivial.
simpl; elim (greater_dec leA leA_dec a (bad_subsequence leA leA_dec (firsts ws))); intro c.
split; trivial.
constructor 2 with f; trivial.
elim c; trivial.
intro HF; inversion HF; subst.
apply H; trivial.
apply H3; trivial.

(* case ~ greater a badSub (Fsts ws) *)
apply IHbs with (y := a ::(bad_subsequence leA leA_dec (firsts ws)))
		(f := (node (w::ws, a::nil) f)::f); simpl; trivial.
constructor; trivial.
apply acc_ltF_cons.
constructor; apply acc_f.
apply acc_ltF_single with (w::ws) (nil (A:=A)) a (bad_subsequence leA leA_dec (firsts ws)) f; trivial.
apply IHw; trivial.
intros HF; apply H; generalize HF; apply (greater_remove_letter (leA:=leA)).
constructor.
intros HF; apply H; generalize HF; apply (greater_remove_letter (leA:=leA)).
constructor; apply acc_bs.
constructor; apply acc_f.
repeat split; trivial.
symmetry; apply is_forest_roots_labels; trivial.
elim (greater_dec leA leA_dec a (bad_subsequence leA leA_dec (firsts ws))); intro case'; 
	[elim case_a_bs | idtac]; trivial.
split; trivial.
constructor 3; trivial.
intro HF; inversion HF; subst.
apply H; trivial.
apply H3; trivial.
Qed.

Theorem Higman : 
  Acc (continues leA) nil -> Acc (continues embeds) nil.
Proof.
intro wqo_leA; apply (higman_aux wqo_leA) with (f:=nil (A := Tree)).
apply acc_ltF_nil.
split; simpl; trivial.
unfold is_forest; constructor 1 with (leA := leA) (leA_dec := leA_dec).
intro HF; inversion HF; trivial.
Qed.

End higman.
