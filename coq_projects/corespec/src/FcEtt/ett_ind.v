Require Import FcEtt.utils.
Require Import FcEtt.imports.


Require Export FcEtt.fset_facts.
Require Export FcEtt.ett_inf.
Require Export FcEtt.tactics.


(* This file contains:

   - Syntactic stuff that should be defined by lngen
     (and that we should get LNgen to generate in the future).

   - Induction principles for the relations.

   - Other tactics that are specialized to the relations.

 *)

Set Bullet Behavior "Strict Subproofs".
Set Implicit Arguments.


Lemma tm_subst_tm_tm_var : forall a x, tm_subst_tm_tm a x (a_Var_f x) = a.
Proof. intros. simpl. destruct (x == x). auto. done. Qed.

Lemma co_subst_co_co_var : forall a x, co_subst_co_co a x (g_Var_f x) = a.
Proof. intros. simpl. destruct (x == x). auto. done. Qed.

Lemma tm_subst_tm_tm_var_neq : forall a x y, x <> y ->
    tm_subst_tm_tm a y (a_Var_f x) = (a_Var_f x).
Proof. intros. simpl. destruct (x == y). contradiction. auto. Qed.

Lemma co_subst_co_co_var_neq : forall a x y, x <> y ->
    co_subst_co_co a y (g_Var_f x) = (g_Var_f x).
Proof. intros. simpl. destruct (x == y). contradiction. auto. Qed.

Hint Rewrite tm_subst_tm_tm_var co_subst_co_co_var.

(* ----------------------------------------------------- *)

(*
   Some rewriting hints so that we don't have to remember
   all of the various names of the functions/lemmas
   (and so that we can make the tactics more generic).

*)

Hint Rewrite tm_subst_tm_tm_open_tm_wrt_tm_var : subst_open_var.
Hint Rewrite tm_subst_tm_tm_open_tm_wrt_co_var : subst_open_var.
Hint Rewrite tm_subst_tm_co_open_co_wrt_tm_var : subst_open_var.
Hint Rewrite tm_subst_tm_co_open_co_wrt_co_var : subst_open_var.
Hint Rewrite co_subst_co_co_open_co_wrt_co_var : subst_open_var.
Hint Rewrite co_subst_co_co_open_co_wrt_tm_var : subst_open_var.
Hint Rewrite co_subst_co_tm_open_tm_wrt_co_var : subst_open_var.
Hint Rewrite co_subst_co_tm_open_tm_wrt_tm_var : subst_open_var.

Hint Rewrite <- tm_subst_tm_tm_open_tm_wrt_tm_var : open_subst_var.
Hint Rewrite <- co_subst_co_tm_open_tm_wrt_tm_var : open_subst_var.
Hint Rewrite <- tm_subst_tm_tm_open_tm_wrt_co_var : open_subst_var.
Hint Rewrite <- co_subst_co_co_open_co_wrt_co_var : open_subst_var.


Hint Rewrite tm_subst_tm_tm_open_tm_wrt_tm : subst_open.
Hint Rewrite tm_subst_tm_tm_open_tm_wrt_co : subst_open.
Hint Rewrite tm_subst_tm_co_open_co_wrt_tm : subst_open.
Hint Rewrite tm_subst_tm_co_open_co_wrt_co : subst_open.
Hint Rewrite co_subst_co_co_open_co_wrt_co : subst_open.
Hint Rewrite co_subst_co_co_open_co_wrt_tm : subst_open.
Hint Rewrite co_subst_co_tm_open_tm_wrt_co : subst_open.
Hint Rewrite co_subst_co_tm_open_tm_wrt_tm : subst_open.

Hint Rewrite <- tm_subst_tm_tm_open_tm_wrt_tm : open_subst.
Hint Rewrite <- tm_subst_tm_tm_open_tm_wrt_co : open_subst.
Hint Rewrite <- tm_subst_tm_co_open_co_wrt_tm : open_subst.
Hint Rewrite <- tm_subst_tm_co_open_co_wrt_co : open_subst.
Hint Rewrite <- co_subst_co_co_open_co_wrt_co : open_subst.
Hint Rewrite <- co_subst_co_co_open_co_wrt_tm : open_subst.
Hint Rewrite <- co_subst_co_tm_open_tm_wrt_co : open_subst.
Hint Rewrite <- co_subst_co_tm_open_tm_wrt_tm : open_subst.

(* ----------------------------------------------------- *)

(* lc support

   These are some general purpose tactics for solving local closure
   goals. The are used in the lc_mutual proofs, but may also
   be useful elsewhere in the development.

   These tactics generally support forward reasoning which is
   useful for exploratory proof development.

*)

(* apply a lc constructor for a term with binding. *)
Ltac apply_lc_exists x :=
  pick fresh x;
  ( apply lc_a_Abs_exists      with (x1 := x)
  || apply lc_a_Pi_exists       with (x1 := x)
  || apply lc_a_CPi_exists      with (c1 := x)
  || apply lc_a_CAbs_exists     with (c1 := x)
  || apply lc_a_UAbs_exists     with (x1:= x)
  || apply lc_a_UCAbs_exists    with (c1 := x)
  || apply lc_g_PiCong_exists   with (x1 := x)
  || apply lc_g_AbsCong_exists  with (x1 := x)
  || apply lc_g_CPiCong_exists  with (c1 := x)
  || apply lc_g_CAbsCong_exists with (c1 := x)
  || fail "invalid case for apply_lc_exists" );
  eauto 2.


(* This tactic assists local closure goals when
   we have a 'binds' assumption in the context. *)

(* TODO: replace basic_solve with something more primitive? *)
Ltac lc_solve_binds :=
  match goal with
  (* binds nil case *)
  | [ H : binds ?x ?s nil |- _ ] => inversion H; clear H
  (* binds cons case *)
  | [ H : binds _ ?s ([(_,_)] ++ _) |- _ ?s] =>
      destruct (binds_cons_1 _ _ _ _ _ _ H); basic_solve
  (* variable cases *)
  | [ b : binds ?x _ ?G, H : ∀ (x' : atom) _, binds x' _ ?G → _ |- _] =>
      by apply H in b; inversion b; try done;
          match goal with
            | [H' : lc_constraint _ |- _] => inversion H' ; clear H'
            | [H' : lc_tm         _ |- _] => inversion H' ; clear H'
          end
  end.

(* Invert all lc assumptions in the context, using the variable name
   "c" for any lc assumptions about the bodies of binders.  *)
(* TODO: remove split_hyp? *)
(* generalize first case to include context *)
Ltac lc_inversion c :=
  repeat match goal with
    (* inversion for binders *)
  | [ H : forall x, (x `in` ?L -> False) -> lc_tm _ /\ _ |- _ ] =>
    destruct (H c ltac:(auto)); split_hyp; clear H
  (* simple inversions *)
  | [ H : lc_constraint (_ _) |- _ ] =>
    inversion H; clear H
  | [ H : lc_tm (a_Abs _ _ _) |- _ ] =>
    inversion H; clear H
  | [ H : lc_tm (a_UAbs _ _) |- _ ] =>
    inversion H; clear H
  | [ H : lc_tm (a_App _ _ _) |- _ ] =>
    inversion H; clear H
  | [ H : lc_tm (a_Pi _ _ _) |- _ ] =>
    inversion H; clear H
  | [ H : lc_tm (a_Conv _ _) |- _ ] =>
    inversion H; clear H
  | [ H : lc_tm (a_CPi _ _) |- _ ] =>
    inversion H; clear H
  | [ H : lc_tm (a_CAbs _ _) |- _ ] =>
    inversion H; clear H
  | [ H : lc_tm (a_UCAbs _) |- _ ] =>
    inversion H; clear H
  | [ H : lc_tm (a_CApp _ _) |- _ ] =>
    inversion H; clear H
  | [ H : lc_tm (a_Case _ _) |- _ ] =>
    inversion H; clear H
 end.

Ltac apply_lc_body :=
  match goal with
  | |- lc_tm (open_tm_wrt_tm ?a ?b) => eapply lc_body_tm_wrt_tm; auto
  | |- lc_tm (open_tm_wrt_co ?a ?b) => eapply lc_body_tm_wrt_co; auto
  end.


(* --------------------------------------------------------------------- *)

(* This lemma is an inverse to

    co_subst_co_tm_lc_tm : ∀ (a1 : tm) (g1 : co) (c1 : covar),
       lc_tm a1 → lc_co g1 → lc_tm (co_subst_co_tm g1 c1 a1)

   It shows:

    co_subst_co_tm_lc_tm_inverse : ∀ (a1 : tm) (g1 : co) (c1 : covar),
       lc_co g1 -> lc_tm (co_subst_co_tm g1 c1 a1) -> tc_tm a1

    (Note, the other way around is not true because the variable c1
    may not actually appear in a1, so we cannot conclude anything
    about g1.)
 *)

Lemma co_subst_co_tm_lc_tm_inverse
  : ∀ (g1 : co) (c1 : covar),
      lc_co g1 ->
      (forall A,
          lc_tm A -> forall XX, A = (co_subst_co_tm g1 c1 XX) -> lc_tm XX)
      /\
      (forall b1,
          lc_brs b1 -> forall XX, b1 = (co_subst_co_brs g1 c1 XX) -> lc_brs XX)
      /\
      (forall co,
          lc_co co -> forall XX, co = (co_subst_co_co g1 c1 XX) -> lc_co XX)
      /\
      (forall phi,
          lc_constraint phi -> forall XX, phi = (co_subst_co_constraint g1 c1 XX) ->
          lc_constraint XX).
Proof.
  intros. 
  apply lc_tm_lc_brs_lc_co_lc_constraint_mutind.
  all: intros.
  (* simple destruct and inversion. *)
  all: match goal with
       | [H0 : _ = _ ?g1 ?c1 ?XX |- _] =>
         destruct XX; simpl in H0; inversion H0; clear H0; subst; auto
       end.
  all: try apply_lc_exists xc;
    try match goal with
    | [ H1 : ∀ x XX,
          _ (_ ?g1 ?c1 ?XX2) (_ x) = _ ?g1 ?c1 XX → _ XX |- _ ] =>
      eapply (H1 xc); autorewrite with subst_open; auto
    end.
  all: try rewrite co_subst_co_co_var_neq; auto.
Qed.


(* --------------------------------------------------------- *)

Ltac invert_syntactic_equality :=
  repeat match goal with
  | [ H : a_Var_f _  = a_Var_f _ |- _ ] =>
    inversion H; subst; clear H
  | [ H : a_Abs _ _ = a_Abs _ _ |- _ ] =>
    inversion H; subst; clear H
  | [ H : a_UAbs _ _ = a_UAbs _ _ |- _ ] =>
    inversion H; subst; clear H
  | [ H : a_Pi _ _ _ = a_Pi _ _ _ |- _ ] =>
    inversion H; subst; clear H
  | [ H : a_App _ _ _ = a_App _ _ _ |- _ ] =>
    inversion H; subst; clear H
  | [ H : a_Fam _  = a_Fam _ |- _ ] =>
    inversion H; subst; clear H
  | [ H : a_Const _  = a_Const _ |- _ ] =>
    inversion H; subst; clear H
  | [ H : a_Conv _ _ = a_Conv _ _ |- _ ] =>
    inversion H; subst; clear H
  | [ H : a_UCAbs _ = a_UCAbs _ |- _ ] =>
    inversion H; subst; clear H
  | [ H : a_CAbs + _ = a_CAbs _ _ |- _ ] =>
    inversion H; subst; clear H
  | [ H : a_CApp _ _  = a_CApp _ _ |- _ ] =>
    inversion H; subst; clear H
  | [ H : a_CPi _ _ = a_CPi _ _ |- _ ] =>
    inversion H; subst; clear H
  | [ H : Eq _ _ _ = Eq _ _ _ |- _ ] =>
    inversion H; subst; clear H
  end.

(* Invert an "interesting" assumption in the typing context *)
Ltac ann_invert_clear :=
  match goal with
  | H : AnnTyping _ a_Star _ |- _ => inversion H; subst; clear H
  | H : AnnTyping _ (_ _) _ |- _ =>  inversion H; subst; clear H
  | H : AnnPropWff _ _ |- _ => inversion H; subst; clear H
  | H : AnnIso _ _ (_ _) _ _ |- _ => inversion H; subst; clear H
  | H : AnnDefEq _ _ (_ _) _ _  |- _ => inversion H; subst; clear H
  | H : AnnCtx ([(_,_)] ++ _) |- _ => inversion H; subst; clear H
  | H : AnnCtx (_ :: _) |- _ => inversion H; subst; clear H
  end.


(* ----------------------------- *)

(* By default, swaps apply to tm variables. *)

Lemma lc_swap : forall x x0 a,
    x `notin` fv_tm_tm_tm a ->
    lc_tm (open_tm_wrt_tm a (a_Var_f x)) ->
    lc_tm (open_tm_wrt_tm a (a_Var_f x0)).
Proof.
  intros. rewrite (tm_subst_tm_tm_intro x); auto with lngen.
Qed.


Lemma fv_swap : forall x x0 a,
    x `notin` fv_tm_tm_tm a ->
    x0 `notin` fv_tm_tm_tm a ->
    x `notin` fv_tm_tm_tm (open_tm_wrt_tm a (a_Var_f x)) ->
    x0 `notin` fv_tm_tm_tm (open_tm_wrt_tm a (a_Var_f x0)).
Proof.
  intros.
  destruct (x == x0); subst; auto;
  rewrite (tm_subst_tm_tm_intro x); autorewrite with lngen; auto;
  rewrite fv_tm_tm_tm_open_tm_wrt_tm_upper;
  simpl; fsetdec.
Qed.


(* --------------------------------------------------- *)
(* --------------------------------------------------- *)

(* Induction schemes *)

Scheme typing_ind' := Induction for Typing Sort Prop
   with wff_ind'   := Induction for PropWff Sort Prop
   with iso_ind'   := Induction for Iso Sort Prop
   with defeq_ind' := Induction for DefEq Sort Prop
   with ctx_ind'   := Induction for Ctx Sort Prop.

Combined Scheme typing_wff_iso_defeq_mutual from typing_ind', wff_ind', iso_ind', defeq_ind', ctx_ind'.

Scheme ann_typing_ind' := Induction for AnnTyping Sort Prop
   with ann_wff_ind'   := Induction for AnnPropWff Sort Prop
   with ann_iso_ind'   := Induction for AnnIso Sort Prop
   with ann_defeq_ind' := Induction for AnnDefEq Sort Prop
   with ann_ctx_ind'   := Induction for AnnCtx Sort Prop.

Combined Scheme ann_typing_wff_iso_defeq_mutual
from ann_typing_ind', ann_wff_ind', ann_iso_ind',
     ann_defeq_ind', ann_ctx_ind'.

Scheme CoercedValue_ind' := Induction for CoercedValue Sort Prop
                            with Value_ind' := Induction for Value Sort Prop.
Combined Scheme CoercedValue_Value_mutual from CoercedValue_ind', Value_ind'.

(* --------------------------------------------------- *)

(* Apply the mutual induction hypothesis and add a marker to the
   context indicating the current case (and also making the associated
   data constructor for that case available) as the name 'CON'. *)

Ltac ext_induction CON :=
    apply typing_wff_iso_defeq_mutual;
    [ pose CON :=  E_Star       |
      pose CON :=  E_Var        |
      pose CON :=  E_Pi         |
      pose CON :=  E_Abs        |
      pose CON :=  E_App        |
      pose CON :=  E_IApp       |
      pose CON :=  E_Conv       |
      pose CON :=  E_CPi        |
      pose CON :=  E_CAbs       |
      pose CON :=  E_CApp       |
      pose CON :=  E_Const      |
      pose CON :=  E_Fam        |
      pose CON :=  E_Wff        |
      pose CON :=  E_PropCong   |
      pose CON :=  E_IsoConv    |
      pose CON :=  E_CPiFst     |
      pose CON :=  E_Assn       |
      pose CON :=  E_Refl       |
      pose CON :=  E_Sym        |
      pose CON :=  E_Trans      |
      pose CON :=  E_Beta       |
      pose CON :=  E_PiCong     |
      pose CON :=  E_AbsCong    |
      pose CON :=  E_AppCong    |
      pose CON :=  E_IAppCong   |
      pose CON :=  E_PiFst      |
      pose CON :=  E_PiSnd      |
      pose CON :=  E_CPiCong    |
      pose CON :=  E_CAbsCong   |
      pose CON :=  E_CAppCong   |
      pose CON :=  E_CPiSnd     |
      pose CON :=  E_Cast       |
      pose CON :=  E_EqConv     |
      pose CON :=  E_IsoSnd     |
      pose CON :=  E_EtaRel     |
      pose CON :=  E_EtaIrrel   |
      pose CON :=  E_EtaC       |
(*      pose CON :=  E_LeftRel    |
      pose CON :=  E_LeftIrrel  |
      pose CON :=  E_Right      |
      pose CON :=  E_CLeft      | *)
      pose CON :=  E_Empty      |
      pose CON :=  E_ConsTm     |
      pose CON :=  E_ConsCo     ].


Ltac ann_induction CON :=
    apply ann_typing_wff_iso_defeq_mutual;
    [ pose CON :=  An_Star       |
      pose CON :=  An_Var        |
      pose CON :=  An_Pi         |
      pose CON :=  An_Abs        |
      pose CON :=  An_App        |
      pose CON :=  An_Conv       |
      pose CON :=  An_CPi        |
      pose CON :=  An_CAbs       |
      pose CON :=  An_CApp       |
      pose CON :=  An_Const      |
      pose CON :=  An_Fam        |
      pose CON :=  An_Wff        |
      pose CON :=  An_PropCong   |
      pose CON :=  An_CPiFst     |
      pose CON :=  An_IsoSym     |
      pose CON :=  An_IsoConv    |
      pose CON :=  An_Assn       |
      pose CON :=  An_Refl       |
      pose CON :=  An_EraseEq      |
      pose CON :=  An_Sym        |
      pose CON :=  An_Trans      |
      pose CON :=  An_Beta       |
      pose CON :=  An_PiCong     |
      pose CON :=  An_AbsCong    |
      pose CON :=  An_AppCong    |
      pose CON :=  An_PiFst      |
      pose CON :=  An_PiSnd      |
      pose CON :=  An_CPiCong    |
      pose CON :=  An_CAbsCong   |
      pose CON :=  An_CAppCong   |
      pose CON :=  An_CPiSnd     |
      pose CON :=  An_Cast       |
      pose CON :=  An_IsoSnd     |
      pose CON :=  An_Eta        |
      pose CON :=  An_EtaC       |
(*      pose CON :=  An_Left       |
      pose CON :=  An_Right      |
      pose CON :=  An_CLeft      | *)
      pose CON :=  An_Empty      |
      pose CON :=  An_ConsTm     |
      pose CON :=  An_ConsCo     ].


Ltac ensure_case C :=
  match goal with [ CON := C : ?A |- _ ] => idtac end.


(* --------------------------------------------------- *)

(* Tactic support for freshness *)
(*  What does "fresh" mean for variables? *)

Ltac gather_atoms ::=
  let A := gather_atoms_with (fun x : vars => x) in
  let B := gather_atoms_with (fun x : var => {{ x }}) in
  let C1 := gather_atoms_with (fun x : context => dom x) in
  let D1 := gather_atoms_with (fun x => fv_tm_tm_tm x) in
  let D2 := gather_atoms_with (fun x => fv_tm_tm_co x) in
  let D3 := gather_atoms_with (fun x => fv_tm_tm_constraint x) in
  let D4 := gather_atoms_with (fun x => fv_tm_tm_sort x) in
  let D5 := gather_atoms_with (fun x => fv_tm_tm_brs x) in
  let D6 := gather_atoms_with (fun x => fv_co_co_tm x) in
  let D7 := gather_atoms_with (fun x => fv_co_co_co x) in
  let D8 := gather_atoms_with (fun x => fv_co_co_constraint x) in
  let D9 := gather_atoms_with (fun x => fv_co_co_sort x) in
  let D10 := gather_atoms_with (fun x => fv_co_co_brs x) in
  constr:(A \u B \u C1 \u D1 \u D2 \u D3 \u D4 \u D5 \u D6 \u D7 \u D8 \u D9 \u D10).


(* ----------------------------------------------------- *)

(* Rewrite the goal based on a equation in the context
   (i.e. using an equation from an eta-equivalence rule or from
   one of the Cong rules)
 *)

Ltac rewrite_body :=
  match goal with
  | [ e : ∀ x : atom, (x `in` ?L → False)
      → open_tm_wrt_tm _ (a_Var_f x) = open_tm_wrt_tm _ (_ (a_Var_f x) _) |- _ ] =>
     rewrite e; auto
  | [ e : ∀ x : atom, (x `notin` ?L)
      → open_tm_wrt_tm _ (a_Var_f x) = open_tm_wrt_tm _ (_ (a_Var_f x) _) |- _ ] =>
    rewrite e; auto
  | [ e : ∀ c : atom, (c `notin` ?L)
      → open_tm_wrt_co _ (g_Var_f c) =
        open_tm_wrt_co _ (g_Cast (g_Var_f c) (g_Sym _)) |- _ ] =>
    rewrite e; auto
  | [ e : ∀ x : atom, (x `in` ?L → False) →  _ _ (a_Var_f x) = _ _ _ (a_Var_f x) |- _ ] =>
    rewrite e; auto
  | [ e : ∀ x : atom, (x `in` ?L → False) →  _ _ (a_Var_f x) = _ _ _ (a_Bullet) |- _ ] =>
    rewrite e; auto
  | [ e : ∀ x : atom, (x `notin` ?L) →  _ _ (a_Var_f x) = _ _ _ (a_Var_f x) |- _ ] =>
    rewrite e; auto
  | [ e : ∀ x : atom, (x `notin` ?L) →  _ _ (a_Var_f x) = _ _ _ (a_Bullet) |- _ ] =>
    rewrite e; auto
  | [ e: ∀ c : atom,
    (c `in` ?L → False) → _ _ (g_Var_f c) = a_CApp _ _ |- _ ] =>
    rewrite e; auto
  | [ e: ∀ c : atom,
    (c `notin` ?L) → _ _ (g_Var_f c) = a_CApp _ _ |- _ ] =>
    rewrite e; auto

  end.



(* Solver for the two lc_mutual proofs. *)
Ltac lc_solve :=
  let c := fresh in
  try lc_solve_binds;
  try apply_lc_exists c;
  lc_inversion c; auto;
  try rewrite_body;
  try apply_lc_body;
  eauto with lc.

(* without these two lines, ext_consist.v fails. *)
Hint Resolve lc_a_Pi_exists
     lc_a_CPi_exists lc_a_Abs_exists lc_a_CAbs_exists lc_a_UAbs_exists.
(* This hint is restricted to lngen in ett_inf. *)
Hint Resolve lc_body_tm_wrt_tm lc_body_tm_wrt_co. (* binds_cons_1 *)




(* ---------------------------------------- *)

(*

Lemma fv_tm_tm_tm_open_wrt_tm_mutual:
  (forall a1 a2 x n, x `in` fv_tm_tm_tm a1 ->
      x `in` fv_tm_tm_tm (open_tm_wrt_tm_rec n a2 a1)) /\
  (forall brs a2 x n, x `in` fv_tm_tm_brs brs ->
      x `in` fv_tm_tm_brs (open_brs_wrt_tm_rec n a2 brs)) /\
  (forall g a2 x n, x `in` fv_tm_tm_co g ->
      x `in` fv_tm_tm_co (open_co_wrt_tm_rec n a2 g)) /\
  (forall phi1 a2 x n, x `in` fv_tm_tm_constraint phi1 ->
      x `in` fv_tm_tm_constraint (open_constraint_wrt_tm_rec n a2 phi1)).
Proof.
  apply tm_brs_co_constraint_mutind; simpl; try fsetdec; intros; eauto.
  all: try solve [apply AtomSetFacts.union_iff in H1; case: H1 => H1; eauto].
  all: try solve [apply AtomSetFacts.union_iff in H2; case: H2 => H2;
    eauto; apply AtomSetFacts.union_iff in H2; case: H2 => H2; eauto].
Qed.

Lemma fv_tm_tm_tm_open_wrt_co_mutual:
  (forall a1 a2 x n, x `in` fv_tm_tm_tm a1 ->
     x `in` fv_tm_tm_tm (open_tm_wrt_co_rec n a2 a1)) /\
  (forall brs a2 x n, x `in` fv_tm_tm_brs brs ->
     x `in` fv_tm_tm_brs (open_brs_wrt_co_rec n a2 brs)) /\
  (forall g a2 x n, x `in` fv_tm_tm_co g ->
     x `in` fv_tm_tm_co (open_co_wrt_co_rec n a2 g)) /\
  (forall phi1 a2 x n, x `in` fv_tm_tm_constraint phi1 ->
     x `in` fv_tm_tm_constraint (open_constraint_wrt_co_rec n a2 phi1)).
Proof.
  apply tm_brs_co_constraint_mutind; simpl; try fsetdec; intros; eauto.
  all: try solve [apply AtomSetFacts.union_iff in H1; case: H1 => H1; eauto].
  all: try solve [apply AtomSetFacts.union_iff in H2; case: H2 => H2; eauto; apply AtomSetFacts.union_iff in H2; case: H2 => H2; eauto].
Qed.

Lemma fv_tm_tm_tm_open_tm_wrt_tm:
  forall a1 a2 x, x `in` fv_tm_tm_tm a1 ->
               x `in` fv_tm_tm_tm (open_tm_wrt_tm a1 a2).
Proof.
  intros.
  apply fv_tm_tm_tm_open_tm_wrt_tm_lower.
  auto.
Qed.

Lemma fv_tm_tm_tm_open_tm_wrt_co:
  forall a1 a2 x, x `in` fv_tm_tm_tm a1 ->
               x `in` fv_tm_tm_tm (open_tm_wrt_co a1 a2).
Proof.
  intros.
  apply fv_tm_tm_tm_open_tm_wrt_co_lower.
  auto.
Qed.

*)

(* ----------------------------------------------------------------------- *)

(* TODO: These tactics may be a little loose when filtering the cases (to determine whether or not
         they should kick in). If the automation is too slow, this is something to keep an eye on *)
(* TODO: it may be possible to improve these tactics by matching on the production (return type) of
         the hyp in the context *)
(*
Ltac oh_c'mon :=
    let x := fresh in
    pick fresh x;
    multimatch goal with
      | [ H : forall _ : atom, _ |- _ ] => solve [destruct (H x); basic_solve]
    end.

Ltac invert_open_wrt :=
  subst;
  multimatch goal with
    | [ H : context [?A] |- _ ?A      ] => solve [inversion H; clear H; subst; basic_solve]
    | [ H : context [?A] |- lc_tm (_ ?A _)] => solve [inversion H; clear H; try solve_by_inv_hyp_about A; basic_solve]
  end.
*)
(*
Ltac des_bind_cons :=
  multimatch goal with
    (* So far, this hole ---↓ was only filled with lc_sort. *)
    | [ H : binds _ ?s _ |- _ ?s] => solve [destruct (binds_cons_1 _ _ _ _ _ _ H); basic_solve]
  end.
*)




(* ----------------------------- *)

Lemma rho_swap : forall rho x x0 a,
    x `notin` fv_tm_tm_tm a ->
    x0 `notin` fv_tm_tm_tm a ->
    RhoCheck rho x (open_tm_wrt_tm a (a_Var_f x)) ->
    RhoCheck rho x0 (open_tm_wrt_tm a (a_Var_f x0)).
Proof.
  intros rho x x0 a F1 F2 H0.
  inversion H0; subst; constructor.
  +  auto. (* eapply lc_swap with (x0 := x0) (x:= x); auto. *)
  +  eapply fv_swap with (x:=x); eauto.
Qed.

Lemma eta_swap: forall x y a' b rho,
    x `notin` fv_tm_tm_tm a' \u fv_tm_tm_tm b ->
    open_tm_wrt_tm a' (a_Var_f x) = a_App b rho (a_Var_f x) ->
    open_tm_wrt_tm a' (a_Var_f y) = a_App b rho (a_Var_f y).
Proof.
  intros.
  rewrite (tm_subst_tm_tm_intro x); auto.
  rewrite H0.
  simpl.
  rewrite tm_subst_tm_tm_fresh_eq; auto.
  destruct eq_dec. auto. done.
Qed.

Lemma eta_swap_irrel: forall x y a' b,
    x `notin` fv_tm_tm_tm a' \u fv_tm_tm_tm b ->
    open_tm_wrt_tm a' (a_Var_f x) = a_App b Irrel a_Bullet ->
    open_tm_wrt_tm a' (a_Var_f y) = a_App b Irrel a_Bullet.
Proof.
  intros.
  rewrite (tm_subst_tm_tm_intro x); auto.
  rewrite H0.
  simpl.
  rewrite tm_subst_tm_tm_fresh_eq; auto.
Qed.

Lemma eta_swap_c: forall x y a' b,
    x `notin` fv_co_co_tm a' \u fv_co_co_tm b ->
    open_tm_wrt_co a' (g_Var_f x) = a_CApp b g_Triv ->
    open_tm_wrt_co a' (g_Var_f y) = a_CApp b g_Triv.
Proof.
  intros.
  rewrite (co_subst_co_tm_intro x); auto.
  rewrite H0.
  simpl.
  rewrite co_subst_co_tm_fresh_eq; auto.
Qed.



(* ---------------------------------- *)

(*
Lemma close_tm_fresh :
  forall x a, x `notin` fv_tm_tm_tm (close_tm_wrt_tm x a).
Proof.
  intros.
  autorewrite with lngen.
  auto.
Qed.

Lemma close_co_fresh :
  forall x a, x `notin` fv_tm_tm_co (close_co_wrt_tm x a).
Proof.
  intros. autorewrite with lngen. auto.
Qed.

Lemma close_co_fresh_co :
  forall x a, x `notin` fv_co_co_co (close_co_wrt_co x a).
Proof.
  intros. autorewrite with lngen. auto.
Qed.
 *)

(* ----------------------------------------------------- *)

(* Tactics for working with context in weakening proof *)

Ltac auto_rew_env :=
  multimatch goal with
    | [ |- context [([(?x, ?T)] ++ ?G1 ++ ?G2 ++ ?G3)] ] => rewrite_env (((x ~ (T)) ++ G1) ++ G2 ++ G3)
  end.


(* -------------- Pick fresh and apply for judgements with binding ----- *)

Ltac E_pick_fresh x :=
  match goal with
    | [ |- Typing _ ?shape _ ] =>
      let v := match shape with
            | a_Pi _ _ _ => E_Pi
            | a_UAbs _ _ => E_Abs
            | a_CPi _ _  => E_CPi
            | a_CAbs _ _ => E_CAbs
            | a_UCAbs _  => E_CAbs
           end
      in pick fresh x and apply v
    | [ |- DefEq _ _ ?shape ?s2 _ ] =>
      let v := match shape with
               | a_Pi _ _ _ => E_PiCong
               | a_UAbs Rel _ => match s2 with
                                | a_UAbs _ _ => E_AbsCong
                                | _ => E_EtaRel
                                end
               | a_UAbs Irrel _ => match s2 with 
                                | a_UAbs _ _ =>  E_AbsCong
                                | _ => E_EtaIrrel
                                end
               | a_CPi _ _  => E_CPiCong
               | a_CAbs _ _ => E_CAbsCong
               | a_UCAbs _  => match s2 with 
                                | a_UCAbs _ =>  E_CAbsCong
                                | _ => E_EtaC
                                end
               end
      in pick fresh x and apply v
  end.

Ltac Par_pick_fresh x :=
  match goal with
    | [ |- Par _ _ ?shape ?s2 ] =>
      let v := match shape with
            | a_Pi _ _ _ => Par_Pi
            | a_UAbs Rel _ =>  match s2 with
                                | a_UAbs _ _ => Par_Abs
                                | _ => Par_Eta
                                end
            | a_UAbs Irrel _ =>  match s2 with
                                | a_UAbs _ _ => Par_Abs
                                | _ => Par_EtaIrrel
                                end
            | a_UAbs _ _ =>  Par_Abs
            | a_CPi _ _  => Par_CPi
            | a_CAbs _ _ => Par_CAbs
            | a_UCAbs _  => match s2 with
                                | a_UCAbs _ => Par_CAbs
                                | _ => Par_EtaC
                                end
           end
      in pick fresh x and apply v
  end.



Ltac An_pick_fresh x :=
  let shape := match goal with
                 | [ |- AnnTyping _   ?shape _    ] => shape
                 | [ |- AnnDefEq  _ _ ?shape _  _ ] => shape
               end in
  let ctor  := match shape with
    | a_Pi     _ _ _ => An_Pi
    | a_Abs    _ _ _ => An_Abs
    | a_CPi      _ _ => An_CPi
    | a_CAbs     _ _ => An_CAbs
    | g_PiCong _ _ _ => An_PiCong
    | g_AbsCong _ _ _  => An_AbsCong
    | g_CPiCong  _ _   => An_CPiCong
    | g_CAbsCong _ _ _ => An_CAbsCong
    | g_Eta _          => An_Eta
               end in
  pick fresh x and apply ctor.


(* --------------------------------------------------------- *)

Ltac RhoCheck_inversion y :=
  match goal with
  | [ K : ∀ x : atom, x `notin` ?L → RhoCheck ?rho x ?b |- _ ] =>
    move: (K y ltac:(auto)); inversion 1; subst; clear K
  | [ K : ∀ x : atom, (x `in` ?L -> False) → RhoCheck ?rho x ?b |- _ ] =>
    move: (K y ltac:(auto)); inversion 1; subst; clear K
  end.

(* --------------------------------------------------------- *)

Lemma lc_open_switch_co :
  forall g t, lc_co g ->
  lc_tm (open_tm_wrt_co t g_Triv) ->
  lc_tm (open_tm_wrt_co t g).
Proof.
  intros.
  pick fresh c.
  rewrite (co_subst_co_tm_intro c); auto.
  eapply co_subst_co_tm_lc_tm; auto.
  rewrite (co_subst_co_tm_intro c) in H0.
  eapply (@co_subst_co_tm_lc_tm_inverse g_Triv c); eauto 2. auto.
Qed.

Hint Resolve lc_open_switch_co.

(* Putting this here because it's annoying to move elsewhere. *)

Lemma tm_subst_cast : forall a x g,
    tm_subst_tm_tm a x (a_Conv (a_Var_f x) g) = a_Conv a (tm_subst_tm_co a x g).
Proof.
  intros. simpl.
  destruct (x == x). auto.
  done.
Qed.

Hint Rewrite tm_subst_cast.
