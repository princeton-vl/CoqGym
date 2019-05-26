(***************************************************************************
* Generic Environments                                                     *
*                                                                          *
* Emmanuel Polonowski, April 2011, Coq v8.3                                *
*                                                                          *
* (Inspired by the work of A. Chargueraud :                                *
*  http://www.chargueraud.org/softs/ln/index.php)                          *
***************************************************************************)

Require Import Utf8.
Set Implicit Arguments.

(* ********************************************************************** *)
(** * Module of the extension of an implementation of environments        *)

Require Import Equalities.
Require Import CoreGenericEnv.
Require List.
Require Sets.Image.

Module GenericEnvironmentType (VarType : UsualDecidableType)
  (CoreGE : CoreGenericEnvironmentType (VarType)).

Import List.

Import VarType CoreGE.
Definition eq_var_dec := VarType.eq_dec.

Local Open Scope gen_env_scope.

Section ExtendedDefinitions.

Variable A : Type.

(** Asserts the binding of a variable in an environment. *)
Definition binds (x : TVar) (v : A) (E : gen_env A) := get x E = Some v.

(** Asserts the inclusion of an environment in another. *)
Definition all_binds (E F : gen_env A) :=
  forall x v, binds x v E -> binds x v F.

(** Equivalence between environments *)
Definition eq (E F : gen_env A) := all_binds E F ∧ all_binds F E.

End ExtendedDefinitions.

(** [x '∹' v '⋲' E] to be read x is bound to v in E. *)

Notation "x '∹' v '⋲' E" := (binds x v E) 
  (at level 65) : gen_env_scope.

(** [E '⊏' F] to be read F all_binds E, i.e. E is included in F. *)

Notation "E '⊏' F" := (all_binds E F) 
  (at level 65) : gen_env_scope.

(** [E '≍' F] to be read F is equivalent to E, i.e. E binds as F. *)

Notation "E '≍' F" := (eq E F) 
  (at level 68) : gen_env_scope.

Bind Scope gen_env_scope with gen_env.
Delimit Scope gen_env_scope with gen_env.
Local Open Scope gen_env_scope.

(* ---------------------------------------------------------------------- *)
(** ** Properties *)

Section Properties.
Implicit Types x y : TVar.
Implicit Types xs ys : list TVar.

(* ---------------------------------------------------------------------- *)
(** **** Abstract properties of ok *)

(** Ok and dom *)
Theorem ok_dom : forall A (E : gen_env A),
  List.NoDup (dom E) -> ok E.
Proof.
  induction E using env_ind; intro H_NoDup.
  apply ok_empty.
  rewrite dom_concat in H_NoDup. rewrite dom_single in H_NoDup.
  simpl in H_NoDup. inversion H_NoDup.
  apply ok_cons; split; auto. apply notin_dom_inv; auto.
Qed.

Theorem ok_dom_inv : forall A (E : gen_env A),
  ok E -> List.NoDup (dom E).
Proof.
  induction E using env_ind; intro Hok.
  rewrite dom_empty. apply List.NoDup_nil.
  apply ok_concat_inv in Hok.
  destruct Hok as [ HokE Hok ] ; destruct Hok as [ Hokx Hdoms ].
  destruct Hdoms as [ Hdom1 Hdom2 ].
  rewrite dom_concat. rewrite dom_single in *. simpl.
  apply List.NoDup_cons; auto.
  apply all_notin_notin in Hdom2. destruct Hdom2. apply notin_dom; auto.
Qed.

(** Ok is equivalent to the non-duplication of the domain. *)
Theorem ok_NoDup_dom_eq : forall A (E : gen_env A),
  ok E <-> List.NoDup (dom E).
Proof.
  intro E; split; [ apply ok_dom_inv | apply ok_dom ]; auto.
Qed.


(* ---------------------------------------------------------------------- *)
(** **** Properties of binds *)

(** Binds and empty. *)
Theorem binds_empty : forall A x (v : A),
  x ∹ v ⋲ (@empty A) ->
  False.
Proof.
  intros A x v Hbind. inversion Hbind as [ Hget ].
  rewrite get_empty in Hget. inversion Hget.
Qed.

(** Binds on singular(s). *)
Theorem binds_single : forall A x y (v w : A),
  x = y -> v = w ->
  x ∹ v ⋲ (y ∶ w).
Proof.
  intros A x y v w Heq1 Heq2. rewrite Heq1, Heq2.
  unfold binds. rewrite get_single_eq; auto.
Qed.

Theorem binds_single_inv : forall A x y (v w: A),
  x ∹ v ⋲ (y ∶ w) ->
  x = y ∧ v = w.
Proof.
  intros A x y v w Hbind. inversion Hbind as [ Hget ].
  destruct (eq_var_dec x y) as [ Heq | Hneq ].
  rewrite Heq in *; clear x Heq.
  rewrite get_single_eq in Hget; auto. inversion Hget; auto.
  apply get_single_eq_inv in Hget. destruct Hget; contradiction.
Qed.

Theorem binds_singles : forall A x y (v w : A) ys (ws : list A),
  x = y -> v = w ->
  x ∹ v ⋲ (y :: ys ∷ w :: ws). 
Proof.
  intros A x y v w ys ws Heq1 Heq2. rewrite Heq1, Heq2.
  unfold binds. rewrite singles_cons. apply get_concat_r; auto.
Qed.

Theorem binds_singles_inv : forall A x y (v w : A) ys (ws : list A),
  x ∹ v ⋲ (y :: ys ∷ w :: ws) ->
  (x = y ∧ v = w) ∨ (x ∹ v ⋲ (ys ∷ ws)).
Proof.
  intros A x y v w ys ws Hbind. inversion Hbind as [ Hget ].
  rewrite singles_cons in Hget.
  apply get_concat_inv in Hget. destruct Hget as [ Heq | Hneq ].
  left. destruct Heq; split; auto.
  right. destruct Hneq. auto.
Qed.

(** Binds is functional. *)
Theorem binds_eq_inv : forall A x (v w : A) (E : gen_env A),
  x ∹ v ⋲ E -> x ∹ w ⋲ E ->
  v = w.
Proof.
  intros A x v w E Hbind1 Hbind2.
  inversion Hbind1 as [ Hget1 ]. inversion Hbind2 as [ Hget2 ].
  rewrite Hget1 in Hget2. inversion Hget2; auto.
Qed.

(** Binds and concatenation. *)
Theorem binds_concat_r : forall A x (v : A) (F G : gen_env A),
  x ∹ v ⋲ G ->
  x ∹ v ⋲ (F & G).
Proof.
  intros A x v F G Hbind. induction G as [ | G y w IHG ] using env_ind.
  apply binds_empty in Hbind. inversion Hbind.
  destruct (eq_keys_dec x y) as [ Heq | Hneq ].
  rewrite <- Heq in *; clear y Heq.
  unfold binds in *. apply get_concat_inv in Hbind.
  destruct Hbind as [ [ _ Heq ] | [ Hneq Hbind ] ].
  rewrite Heq in *. rewrite concat_assoc. apply get_concat_r; auto.
  elim Hneq; auto.
  unfold binds in *. rewrite concat_assoc.
  apply get_concat_inv in Hbind.
  destruct Hbind as [ [ Heq _ ] | [ _ Hget ] ]. contradiction.
  apply IHG in Hget.
  assert (get x (F & G & y ∶ w) = get x (F & G)) as Heq.
  apply get_concat_l; auto. rewrite Heq; auto.
Qed.

Theorem binds_concat_l : forall A x (v : A) (F G : gen_env A),
  x ∹ v ⋲ F ->
  x ∉ G ->
  x ∹ v ⋲ (F & G).
Proof.
  intros A x v F G Hbind Hnotin.
  induction G as [ | G y w IHG ] using env_ind.
  rewrite concat_empty_r; auto.
  apply notin_concat_inv in Hnotin. destruct Hnotin as [ HnotinG Hnotin_y ].
  apply IHG in HnotinG. apply notin_single_inv in Hnotin_y.
  unfold binds in *. rewrite concat_assoc.
  assert (get x (F & G & y ∶ w) = get x (F & G)) as Heq.
  apply get_concat_l; auto. rewrite Heq; auto.
Qed.

Theorem binds_concat_inv : forall A x (v : A) (F G : gen_env A),
  x ∹ v ⋲ (F & G) ->
  x ∹ v ⋲ G ∨ (x ∉ G ∧ x ∹ v ⋲ F).
Proof.
  induction G as [ | G y w IHG ] using env_ind; intro Hbind.
  rewrite concat_empty_r in *.
  right; split; [ apply notin_empty | ]; auto.

  unfold binds in *. rewrite concat_assoc in *.
  apply get_concat_inv in Hbind.
  destruct Hbind as [ [ Heq_xy Heq_wv ] | [ Hneq_xy Hget ] ].

  subst. left. apply get_concat_r; auto.

  apply IHG in Hget. destruct Hget as [ Hget | [ Hnotin Hget ] ].
  left.
  assert (get x (G & y ∶ w) = get x G) as Heq.
  apply get_concat_l; auto. rewrite Heq; auto.

  right. split; auto. apply notin_concat; auto. apply notin_single; auto.
Qed.

(** Binds and belongs. *)
Theorem binds_belongs : forall A x (v : A) (F : gen_env A),
  x ∹ v ⋲ F ->
  x ∈ F.
Proof.
  induction F using env_ind; intro Hbind.
  apply binds_empty in Hbind; inversion Hbind.
  apply binds_concat_inv in Hbind.
  destruct Hbind as [ Hbind | [ Hnotin Hbind ] ].

  apply belongs_concat_r. unfold binds in Hbind.
  apply get_single_eq_inv in Hbind. destruct Hbind.
  apply belongs_single; auto.

  apply IHF in Hbind. apply belongs_concat_l; auto.
Qed.

Theorem belongs_binds : forall A x (F : gen_env A),
  x ∈ F ->
  exists v, x ∹ v ⋲ F.
Proof.
  induction F as [ | F y w IHF ] using env_ind; intro Hbelong.
  apply belongs_empty in Hbelong. inversion Hbelong.

  destruct (eq_keys_dec x y) as [ Heq | Hneq ]. subst.
  exists w. apply binds_concat_r. apply binds_single; auto.

  apply belongs_concat_inv in Hbelong. destruct Hbelong as [ HinF | Hiny ].
  apply IHF in HinF. destruct HinF as [ w' Hbind ]. exists w'.
  apply binds_concat_l; auto. apply notin_single; auto.
  apply belongs_single_inv in Hiny. contradiction.
Qed.

(** Binds and map. *)
Theorem binds_map : forall A B x (v : A) (E : gen_env A) (f : A -> B),
  x ∹ v ⋲ E ->
  x ∹ (f v) ⋲ (map f E).
Proof.
  intros A B x v E f Hbind. induction E as [ | E y w IHE ] using env_ind.
  apply binds_empty in Hbind; inversion Hbind.

  rewrite map_concat, map_single.
  apply binds_concat_inv in Hbind.
  destruct Hbind as [ Hbind | [ Hnotin Hbind ] ].
  apply binds_single_inv in Hbind. destruct Hbind; subst.
  apply binds_concat_r. apply binds_single; auto.

  apply binds_concat_l; auto. apply notin_single.
  apply notin_single_inv in Hnotin; auto.
Qed.

Theorem binds_map_inv : forall A B x (w : B) (E : gen_env A) (f : A -> B),
  x ∹ w ⋲ (map f E) ->
  exists v, x ∹ v ⋲ E /\ w = f v.
Proof.
  intros A B x w E f Hbind. induction E as [ | E y u IHE ] using env_ind.
  rewrite map_empty in Hbind. apply binds_empty in Hbind. inversion Hbind.

  rewrite map_concat, map_single in Hbind. apply binds_concat_inv in Hbind.
  destruct Hbind as [ Hbind | [ Hnotin Hbind ] ].
  apply binds_single_inv in Hbind. destruct Hbind; subst.
  exists u. split; auto. apply binds_concat_r. apply binds_single; auto.

  apply IHE in Hbind. destruct Hbind as [ w' [ Hbind Heq ] ].
  exists w'. split; auto. apply binds_concat_l; auto.
  apply notin_single_inv in Hnotin. apply notin_single; auto.
Qed.

(** Binds and update_one. *)
Theorem binds_update_one_neq : forall A x y (v w : A) (F : gen_env A),
  x ∹ v ⋲ F ->
  x <> y ->
  x ∹ v ⋲ (F [y <- w]).
Proof.
  intros A x y v w F Hbind Hneq.
  induction F as [ | F z u ] using env_ind.
  apply binds_empty in Hbind. inversion Hbind.

  apply binds_concat_inv in Hbind. destruct Hbind as [ Hbind_r | Hbind_l ].
  apply binds_single_inv in Hbind_r. destruct Hbind_r as [ Heq1 Heq2 ].
  rewrite <- Heq1, <- Heq2 in *; clear z u Heq1 Heq2.
  rewrite update_one_concat_l.
  apply binds_concat_r. apply binds_single; auto.
  apply notin_single; auto.

  destruct Hbind_l as [ Hnotin Hbind ].
  destruct (eq_var_dec y z) as [ Heqz | Hneqz ].
  rewrite <- Heqz in *; clear z Heqz.
  rewrite update_one_concat_r. rewrite update_one_single; auto. 
  apply binds_concat_l; auto. apply notin_single; auto.
  apply belongs_single; auto.

  rewrite update_one_concat_l; [ | apply notin_single; auto ].
  apply binds_concat_l; auto.
Qed.

Theorem binds_update_one_eq : forall A x y (v w : A) (F : gen_env A),
  x ∈ F ->
  x = y -> v = w ->
  x ∹ v ⋲ (F [y <- w]).
Proof.
  intros A x y v w F Hbelongs Heq_xy Heq_vw.
  rewrite <- Heq_xy, <- Heq_vw in *; clear y w Heq_xy Heq_vw.
  induction F as [ | F z u ] using env_ind.
  apply belongs_empty in Hbelongs. inversion Hbelongs.

  destruct (eq_var_dec x z) as [ Heq | Hneq ].
  rewrite <- Heq in *; clear z Heq.
  rewrite update_one_concat_r; [ | apply belongs_single; auto ].
  rewrite update_one_single; auto.
  apply binds_concat_r. apply binds_single; auto.

  apply belongs_concat_inv in Hbelongs. destruct Hbelongs as [ HinF | Hinz].
  rewrite update_one_concat_l; [ | apply notin_single; auto ].
  apply binds_concat_l; [ | apply notin_single; auto ]; auto.

  apply belongs_single_inv in Hinz. contradiction.
Qed.

Theorem binds_update_one_inv : forall A x y (v w : A) (F : gen_env A),
  x ∹ v ⋲ (F [y <- w]) ->
  (x <> y ∧ x ∹ v ⋲ F) ∨ (x ∈ F ∧ x = y ∧ v = w).
Proof.
  intros A x y v w F Hbind.
  induction F as [ | F z u IHF ] using env_ind.

  rewrite update_one_empty in Hbind. apply binds_empty in Hbind.
  inversion Hbind.

  destruct (eq_var_dec y z) as [ Heqz | Hneqz ];
    destruct (eq_var_dec x y) as [ Heqy | Hneqy ]; subst.

  Focus.
  rewrite update_one_concat_r in Hbind; [ | apply belongs_single; auto ].
  rewrite update_one_single in Hbind; auto.
  apply binds_concat_inv in Hbind.
  destruct Hbind as [ Hin | Hnotin ].
  apply binds_single_inv in Hin. destruct Hin; subst.
  right. split; auto. apply belongs_concat_r. apply belongs_single; auto.
  destruct Hnotin as [ Hnotin _ ]. apply notin_single_inv in Hnotin.
  elim Hnotin; auto.

  Focus.
  rewrite update_one_concat_r in Hbind; [ | apply belongs_single; auto ].
  rewrite update_one_single in Hbind; auto.
  apply binds_concat_inv in Hbind.
  destruct Hbind as [ Hin | Hnotin ].
  apply binds_single_inv in Hin. destruct Hin; contradiction.
  left. split; auto.
  apply binds_concat_l. destruct Hnotin; auto.
  apply notin_single; auto.

  Focus.
  rewrite update_one_concat_l in Hbind; [ | apply notin_single; auto ].
  apply binds_concat_inv in Hbind.
  destruct Hbind as [ Hin | Hnotin ].
  apply binds_single_inv in Hin. destruct Hin; contradiction.
  destruct Hnotin as [ Hnotin Hbind ]. apply IHF in Hbind.
  destruct Hbind as [ Hneq | Heq ]. destruct Hneq as [ Hneq _ ].
  elim Hneq; auto. destruct Heq as [ HinF Heqs ]. destruct Heqs.
  right. split; auto. apply belongs_concat_l; auto.

  destruct (eq_var_dec x z) as [ Heq | Hneq ]; subst.
  rewrite update_one_concat_l in Hbind; [ | apply notin_single; auto ].
  apply binds_concat_inv in Hbind.
  destruct Hbind as [ Hin | Hnotin ].
  apply binds_single_inv in Hin. destruct Hin; subst.
  left. split; auto. apply binds_concat_r.
  apply binds_single; auto. destruct Hnotin as [ Hnotin _ ].
  apply notin_single_inv in Hnotin. elim Hnotin; auto.
  rewrite update_one_concat_l in Hbind; [ | apply notin_single; auto ].
  apply binds_concat_inv in Hbind.
  destruct Hbind as [ Hin | Hnotin ].
  apply binds_single_inv in Hin. destruct Hin; contradiction.
  destruct Hnotin as [ Hnotin Hbind ]. apply IHF in Hbind.
  destruct Hbind as [ Hneq2 | Heq ];
    [ | destruct Heq as [ _ Heq ]; destruct Heq; contradiction ].
  destruct Hneq2. left. split; auto.
  apply binds_concat_l; [ | apply notin_single; auto ]; auto.
Qed.

(** Binds and update. *)
Theorem binds_update_notin : forall A x (v : A) (F G : gen_env A),
  x ∹ v ⋲ F ->
  x ∉ G ->
  x ∹ v ⋲ (F ::= G).
Proof.
  intros A x v F G Hbind Hnotin.
  induction G as [ | G y w ] using env_ind.

  rewrite update_empty_r; auto.

  rewrite update_concat_r. rewrite update_update_one.
  apply notin_concat_inv in Hnotin. destruct Hnotin as [ HnotinG Hneq ].
  apply notin_single_inv in Hneq. apply binds_update_one_neq; auto.
Qed.

Theorem binds_update_in : forall A x (v : A) (F G : gen_env A),
  x ∈ F ->
  x ∹ v ⋲ G ->
  x ∹ v ⋲ (F ::= G).
Proof.
  intros A x v F G Hin Hbind.
  induction G as [ | G y w ] using env_ind.
  apply binds_empty in Hbind. inversion Hbind.
  apply binds_concat_inv in Hbind. destruct Hbind as [ Hbind | Hnotin ].
  apply binds_single_inv in Hbind. destruct Hbind; subst.
  apply (belongs_update G) in Hin.
  rewrite update_concat_r. rewrite update_update_one.
  apply binds_update_one_eq; auto.

  destruct Hnotin as [ Hnotin Hbind ]. apply notin_single_inv in Hnotin.
  rewrite update_concat_r. rewrite update_update_one.
  apply binds_update_one_neq; auto.
Qed.

Theorem binds_update_self : forall A x (v : A) (F : gen_env A),
  x ∈ F ->
  x ∹ v ⋲ (F ::= (x ∶ v)).
Proof.
  intros A x v F Hin.
  rewrite update_update_one. apply binds_update_one_eq; auto.
Qed.

Theorem binds_update_inv : forall A x (v : A) (F G : gen_env A),
  x ∹ v ⋲ (F ::= G) ->
  (x ∉ G ∧ x ∹ v ⋲ F) ∨ (x ∈ F ∧ x ∹ v ⋲ G).
Proof.
  intros A x v F G Hbind.
  induction G as [ | G y w IHG ] using env_ind.

  rewrite update_empty_r in Hbind. left; split; auto.
  apply notin_empty.

  rewrite update_concat_r in Hbind. rewrite update_update_one in Hbind.
  apply binds_update_one_inv in Hbind.
  destruct Hbind as [ Hneq | Heq ].

  destruct Hneq as [ Hneq Hbind].
  apply IHG in Hbind.
  destruct Hbind as [ HbindF | HbindG ].
  destruct HbindF as [ Hnotin Hbind ].
  left; split; auto. apply notin_concat; auto. apply notin_single; auto.

  destruct HbindG as [ HinF Hbind ].
  right; split; auto. apply binds_concat_l; auto. apply notin_single; auto.

  destruct Heq as [ Hin [ Heq1 Heq2 ] ]; subst.
  right. split. apply belongs_update_inv with G; auto.
  apply binds_concat_r. apply binds_single; auto.
Qed.

(** Binds and remove. *)
Theorem binds_remove : forall A x y (v : A) (E : gen_env A),
  x <> y -> x ∹ v ⋲ E ->
  x ∹ v ⋲ (E ∖ {y}).
Proof.
  intros A x y v E Hneq Hbind.
  induction E as [ | E z w IHE ] using env_ind.
  apply binds_empty in Hbind. inversion Hbind.

  apply binds_concat_inv in Hbind.
  destruct Hbind as [ Hbind | [ Hnotin Hbind ] ].

  destruct (eq_keys_dec y z) as [ Heq | Hneq_yz ]. subst.
  apply binds_single_inv in Hbind. destruct Hbind. contradiction.

  rewrite remove_belongs_concat_l.
  apply binds_concat_r; auto. apply notin_single; auto.

  apply notin_single_inv in Hnotin.
  destruct (eq_keys_dec y z); subst.
  rewrite remove_belongs_concat_r. rewrite remove_single_eq; auto.
  rewrite concat_empty_r; auto. apply belongs_single; auto.

  rewrite remove_belongs_concat_l.
  apply binds_concat_l; auto. apply notin_single; auto.
  apply notin_single; auto.
Qed.

Theorem binds_remove_inv : forall A x y (v : A) (E : gen_env A),
  x <> y -> x ∹ v ⋲ (E ∖ {y}) ->
  x ∹ v ⋲ E.
Proof.
  intros A x y v E Hneq Hbind.
  induction E as [ | E z w IHE ] using env_ind.
  rewrite remove_empty in Hbind.
  apply binds_empty in Hbind. inversion Hbind.

  destruct (eq_keys_dec y z); subst.
  rewrite remove_belongs_concat_r in Hbind.
  rewrite remove_single_eq in Hbind; auto. rewrite concat_empty_r in Hbind.
  apply binds_concat_l; auto. apply notin_single; auto.
  apply belongs_single; auto.

  destruct (eq_keys_dec x z); subst.
  rewrite remove_belongs_concat_l in Hbind.
  apply binds_concat_inv in Hbind.
  destruct Hbind as [ Hbind | [ Hnotin Hbind ] ].
  apply binds_concat_r; auto.

  apply notin_single_inv in Hnotin. elim Hnotin; auto.
  apply notin_single; auto.

  rewrite remove_belongs_concat_l in Hbind.
  apply binds_concat_inv in Hbind.
  destruct Hbind as [ Hbind | [ Hnotin Hbind ] ].
  apply binds_single_inv in Hbind. destruct Hbind; contradiction.
  apply binds_concat_l; auto. apply notin_single; auto.
Qed.

Theorem binds_all_remove : forall A x ys (v : A) (E : gen_env A),
  ¬ List.In x ys -> x ∹ v ⋲ E ->
  x ∹ v ⋲ (E ∖ ys).
Proof.
  induction ys as [ | y ys IHys ]; intros; simpl in *; auto.
  rewrite all_remove_nil; auto.
  rewrite all_remove_remove.
  assert (y <> x ∧ ¬ List.In x ys) as Hnot. split; auto. destruct Hnot.
  apply IHys; auto. apply binds_remove; auto.
Qed.

Theorem binds_all_remove_inv : forall A x ys (v : A) (E : gen_env A),
  ¬ List.In x ys -> x ∹ v ⋲ (E ∖ ys) ->
  x ∹ v ⋲ E.
Proof.
  induction ys as [ | y ys ]; intros v E Hnotin Hbind; simpl in *; auto.
  rewrite all_remove_nil in Hbind; auto.
  rewrite all_remove_remove in Hbind.
  assert (y <> x ∧ ¬ List.In x ys) as Hneq. split; auto. destruct Hneq.
  apply binds_remove_inv with y; auto.
Qed.

(** Binds and ok. *)
Theorem binds_concat_ok_comm : forall A x (v : A) (F G : gen_env A),
  binds x v (F & G) ->
  ok (F & G) ->
  binds x v (G & F).
Proof.
  intros A x v F G Hbind Hok. apply binds_concat_inv in Hbind.
  destruct Hbind as [ Hbind | [ Hnotin Hbind ] ].
  assert (x ∈ G) by (apply binds_belongs with v; auto).
  assert (x ∉ F) by (apply belongs_ok_concat_inv_r with G; auto).
  apply binds_concat_l; auto.
  apply binds_concat_r; auto.
Qed.

(** Decidability of binds. *)
Theorem binds_dec_exists : forall A x (E : gen_env A),
  { v | x ∹ v ⋲ E } + { forall v, ¬ x ∹ v ⋲ E }.
Proof.
  intros A x E. unfold binds.
  elim get_dec with A x E; intro Hget; [ left | right ]; auto.
  intro v. rewrite Hget. intro Heq. inversion Heq.
Qed.

Theorem binds_dec : forall A x (v : A) (E : gen_env A),
  (forall w w' : A, { w = w' } + { ¬ w = w' }) ->
  { x ∹ v ⋲ E } + { ¬ x ∹ v ⋲ E }.
Proof.
  intros A x v E Hdec. elim binds_dec_exists with A x E; intro Hdec2.
  destruct Hdec2 as [ w Hbind ]. elim (Hdec v w); intro Hneq; subst.
  left; auto.
  right. intro. assert (v = w) by (apply binds_eq_inv with x E; auto).
  auto.
  right; auto.
Qed.

(* ---------------------------------------------------------------------- *)
(** **** Properties of all_binds *)

(** All_Binds and binds. *)
Theorem all_binds_binds : forall A x (v : A) (E : gen_env A),
  (x ∶ v) ⊏ E ->
  x ∹ v ⋲ E.
Proof.
  unfold all_binds. intros A x v E Habind.
  apply (Habind x v). apply binds_single; auto.
Qed.

Theorem binds_all_binds : forall A x (v : A) (E : gen_env A),
  x ∹ v ⋲ E ->
  (x ∶ v) ⊏ E.
Proof.
  unfold all_binds. intros A x v E Hbind y w Hbind2.
  apply binds_single_inv in Hbind2. destruct Hbind2; subst; auto.
Qed.

(** All_Binds and empty. *)
Theorem all_binds_empty_l : forall A (E : gen_env A),
  (@empty A) ⊏ E.
Proof.
  unfold all_binds. intros A E x v Hbind.
  apply binds_empty in Hbind. inversion Hbind.
Qed.

Theorem all_binds_empty_r : forall A (E : gen_env A),
  E ⊏ (@empty A) ->
  E = (@empty A).
Proof.
  induction E as [ | E x v IHE ] using env_ind; intro Habind; auto.
  unfold all_binds in Habind.
  assert (x ∹ v ⋲ (@empty A)) as Hempty by
    (apply Habind; assert (x ∹ v ⋲ (E & (x ∶ v))) by
      (apply binds_concat_r; apply binds_single; auto); auto).
  apply binds_empty in Hempty. inversion Hempty.
Qed.

(** All_Binds on singular. *)
Theorem all_binds_single_empty : forall A x (v : A),
  (x ∶ v) ⊏ (@empty A) ->
  False.
Proof.
  intros A x v Habind. apply all_binds_binds in Habind.
  apply binds_empty in Habind; auto.
Qed.

Theorem all_binds_single_single : forall A x y (v w : A),
  x = y -> v = w ->
  (x ∶ v) ⊏ (y ∶ w).
Proof.
  intros; subst. apply binds_all_binds. apply binds_single; auto.
Qed.

Theorem all_binds_single_single_inv : forall A x y (v w : A),
  (x ∶ v) ⊏ (y ∶ w) ->
  x = y ∧ v = w.
Proof.
  intros A x y v w Habind. apply all_binds_binds in Habind.
  apply binds_single_inv; auto.
Qed.

Theorem all_binds_single_push_inv : forall A x y (v w : A) (E : gen_env A),
  (x ∶ v) ⊏ (E & (y ∶ w)) ->
  (x = y ∧ v = w) ∨ (x <> y ∧ (x ∶ v) ⊏ E).
Proof.
  intros A x y v w E Habind. apply all_binds_binds in Habind.
  apply binds_concat_inv in Habind.
  destruct Habind as [ Hbind | [ Hnotin Hbind ] ].
  apply binds_single_inv in Hbind. left; auto.
  apply notin_single_inv in Hnotin.
  apply binds_all_binds in Hbind. right; auto.
Qed.

Theorem all_binds_single_singles : forall A x y (v w : A) ys (ws : list A),
  x = y -> v = w ->
  (x ∶ v) ⊏ (y :: ys ∷ w :: ws).
Proof.
  intros. apply binds_all_binds. apply binds_singles; auto.
Qed.

Theorem all_binds_single_singles_inv :
  forall A x y (v w : A) ys (ws : list A),
    (x ∶ v) ⊏ (y :: ys ∷ w :: ws) ->
    (x = y ∧ v = w) ∨ ((x ∶ v) ⊏ (ys ∷ ws)).
Proof.
  intros A x y v w ys ws Habind.
  apply all_binds_binds in Habind. apply binds_singles_inv in Habind.
  destruct Habind; [ left | right ]; auto. apply binds_all_binds; auto.
Qed.

Theorem all_binds_single_eq_inv : forall A x (v w : A) (E : gen_env A),
  (x ∶ v) ⊏ E -> (x ∶ w) ⊏ E ->
  v = w.
Proof.
  intros A x v w E Habind1 Habind2.
  apply all_binds_binds in Habind1. apply all_binds_binds in Habind2.
  apply binds_eq_inv with x E; auto.
Qed.

(** All_Binds on singulars. *)
Theorem all_binds_singles_singles : forall A xs ys (vs ws : list A),
  xs = ys -> vs = ws ->
  (xs ∷ vs) ⊏ (ys ∷ ws).
Proof.
  intros; subst. unfold all_binds. intros; auto.
Qed.

(** All_Binds and concatenation. *)
Theorem all_binds_concat_r : forall A (E F G : gen_env A),
  E ⊏ G ->
  E ⊏ (F & G).
Proof.
  intros; unfold all_binds in *; intros. apply binds_concat_r; auto.
Qed.

Theorem all_binds_concat_l : forall A (E F G : gen_env A),
  E ⊏ F ->
  (dom E) ⊄ G ->
  E ⊏ (F & G).
Proof.
  intros A E F G Habind Hdom; unfold all_binds in *; intros x v Hbind.
  apply binds_concat_l; auto.
  apply binds_belongs in Hbind. auto.
  apply all_notin_def_inv with (dom E); auto.
  apply belongs_dom; auto.
Qed.

Theorem all_binds_l_concat : forall A (E F G : gen_env A),
  E ⊏ G -> F ⊏ G ->
  (E & F) ⊏ G.
Proof.
  intros. unfold all_binds in *. intros x v Hbind.
  apply binds_concat_inv in Hbind.
  destruct Hbind as [ Hbind | [ Hnotin Hbind] ]; auto.
Qed.

Theorem all_binds_l_concat_inv : forall A (E F G : gen_env A),
  ok (E & F) ->
  (E & F) ⊏ G ->
  E ⊏ G ∧ F ⊏ G.
Proof.
  intros A E F G Hok Habind. unfold all_binds in *.
  split; intros x v Hbind.
  apply Habind. apply binds_concat_l; auto.
  apply belongs_ok_concat_inv_l with E; auto.
  apply binds_belongs with v; auto.
  apply Habind. apply binds_concat_r; auto.
Qed.

Theorem all_binds_concat_compat : forall A (E F G : gen_env A),
  E ⊏ F ->
  (E & G) ⊏ (F & G).
Proof.
  intros A E F G Habind. induction G using env_ind.
  rewrite ?concat_empty_r; auto.
  unfold all_binds. intros y w Hbind.
  rewrite concat_assoc in *.
  apply binds_concat_inv in Hbind.
  destruct Hbind as [ Hbind | [ Hnotin Hbind ] ].
  apply binds_concat_r; auto.
  apply binds_concat_l; auto.
Qed.

(** All_Binds on singulars when ok. *)
Theorem all_binds_singles_eq_inv :
  forall A xs (vs vs' : list A) (F : gen_env A),
    List.NoDup xs ->
    length xs = length vs ->
    length xs = length vs' ->
    xs ∷ vs ⊏ F -> xs ∷ vs' ⊏ F ->
    vs = vs'.
Proof.
  induction xs as [ | x xs IHxs ]; induction vs as [ | v vs IHvs ];
    induction vs' as [ | v' vs' IHvs' ];
      intros F Hnodup Hleq1 Hleq2 Habind1 Habind2;
        simpl in *; try congruence.

  inversion Hnodup.
  assert (((xs ∷ vs) & (x ∶ v)) ⊏ F) as Habind_1
    by (rewrite <- singles_cons; auto); clear Habind1.
  assert (((xs ∷ vs') & (x ∶ v')) ⊏ F) as Habind_2
    by (rewrite <- singles_cons; auto); clear Habind2.
  apply all_binds_l_concat_inv in Habind_1.
  apply all_binds_l_concat_inv in Habind_2.
  destruct Habind_1; destruct Habind_2.
  assert (vs = vs') as Heq1 by (apply IHxs with F; auto).
  assert (v = v') as Heq2
    by (apply all_binds_single_eq_inv with x F; auto).
  rewrite Heq1, Heq2; auto.
  apply ok_concat. apply ok_singles; auto.
  apply ok_single. rewrite dom_singles.
  apply all_notin_single; auto. auto.
  rewrite dom_single. apply notin_all_notin.
  split. apply notin_singles; auto. apply all_notin_empty_l.
  apply ok_concat. apply ok_singles; auto.
  apply ok_single. rewrite dom_singles.
  apply all_notin_single; auto. auto.
  rewrite dom_single. apply notin_all_notin.
  split. apply notin_singles; auto. apply all_notin_empty_l.
Qed.

(** All_Binds and belongs. *)
Theorem all_binds_belongs : forall A (E F : gen_env A),
  E ⊏ F ->
  (dom E) ⊂ F.
Proof.
  unfold all_binds. intros A E F Hyp. apply all_belongs_def. intros x Hin.
  apply belongs_dom_inv in Hin.
  apply belongs_binds in Hin. destruct Hin as [ v Hbind ].
  apply Hyp in Hbind. apply binds_belongs with v; auto.
Qed.

Theorem belongs_all_binds : forall A x (F : gen_env A),
  x ∈ F ->
  exists v, (x ∶ v) ⊏ F.
Proof.
  intros A x F Hin. unfold all_binds. apply belongs_binds in Hin.
  destruct Hin as [ v Hbind ].
  exists v. intros y w Hbind2. apply binds_single_inv in Hbind2.
  destruct Hbind2; subst; auto.
Qed.

Theorem all_belongs_all_binds : forall A xs (F : gen_env A),
  xs ⊂ F ->
  exists vs, (xs ∷ vs) ⊏ F.
Proof.
  induction xs as [ | x xs IHxs ]; intros F Hin.
  exists nil; rewrite singles_empty; apply all_binds_empty_l; auto.
  apply all_belongs_belongs in Hin. destruct Hin as [ Hxin Hxsin ].
  apply IHxs in Hxsin. destruct Hxsin as [ vs Habind ].
  apply belongs_binds in Hxin. destruct Hxin as [ v Hbind ].
  exists (v :: vs). rewrite singles_cons. unfold all_binds.
  intros y w Hbind2.
  apply binds_concat_inv in Hbind2.
  destruct Hbind2 as [ Hbind2 | [ Hnotin Hbind2 ] ].
  apply binds_single_inv in Hbind2. destruct Hbind2; subst; auto.
  unfold all_binds in Habind; auto.
Qed.

(** All_Binds and map. *)
Theorem all_binds_map : forall A B (f : A -> B) (E F : gen_env A),
  E ⊏ F ->
  map f E ⊏ map f F.
Proof.
  intros A B f E F Habind. unfold all_binds in *. intros x v Hbind.
  apply binds_map_inv in Hbind. destruct Hbind as [ w [ Hbind Heq ] ].
  apply Habind in Hbind. subst. apply binds_map. auto.
Qed.

Theorem all_binds_map_inv : forall A B (f : A -> B) (E F : gen_env A),
  Image.injective A B f ->
  map f E ⊏ map f F ->
  E ⊏ F.
Proof.
  intros A B f E F Hinj Habind. unfold all_binds in *. intros x v Hbind.
  assert (x ∹ (f v) ⋲ map f E) as Hbind2 by (apply binds_map; auto).
  apply Habind in Hbind2. apply binds_map_inv in Hbind2.
  destruct Hbind2 as [ w [ Hbind2 Heq ] ].
  unfold Image.injective in *. apply Hinj in Heq. rewrite Heq; auto.
Qed.

(** All_Binds and update. *)
Theorem all_binds_update_self : forall A (E F : gen_env A),
  (dom E) ⊂ F ->
  E ⊏ (F ::= E).
Proof.
  intros A E F Hdom. unfold all_binds. intros x v Hbind.
  induction E as [ | E y w IHE ] using env_ind.
  apply binds_empty in Hbind. inversion Hbind.

  rewrite dom_concat in Hdom. rewrite dom_single in Hdom. simpl in Hdom.
  apply all_belongs_belongs in Hdom. destruct Hdom as [ Hin Hdom ].

  apply binds_concat_inv in Hbind. rewrite update_concat_r.
  destruct Hbind as [ Hbind | [ Hnotin Hbind ] ].
  apply binds_single_inv in Hbind. destruct Hbind; subst.
  apply binds_update_self. apply belongs_update; auto.

  apply notin_single_inv in Hnotin. rewrite update_update_one.
  apply binds_update_one_neq; auto.
Qed.

Theorem all_binds_update : forall A (E F G : gen_env A),
  E ⊏ F ->
  (E ::= G) ⊏ (F ::= G).
Proof.
  intros A E F G Habind. unfold all_binds in *. intros x v Hbind.
  apply binds_update_inv in Hbind.
  destruct Hbind as [ [ Hnotin Hbind ] | [ Hin Hbind ] ].
  apply binds_update_notin; auto.
  apply belongs_binds in Hin. destruct Hin as [ w Hbind2 ].
  apply Habind in Hbind2. apply binds_belongs in Hbind2.
  apply binds_update_in; auto.
Qed.

(** All_Binds and remove. *)
Theorem all_binds_remove : forall A y (E F : gen_env A),
  y ∉ E -> E ⊏ F ->
  E ⊏ (F ∖ {y}).
Proof.
  intros A y E F Hnotin Habind. unfold all_binds in *. intros x v Hbind.
  apply binds_remove; auto.
  apply binds_belongs in Hbind. apply notin_belongs_neq with A E; auto.
Qed.

Theorem all_binds_remove_inv : forall A y (E F : gen_env A),
  y ∉ E -> E ⊏ (F ∖ {y}) ->
  E ⊏ F.
Proof.
  intros A y E F Hnotin Habind. unfold all_binds in *. intros x v Hbind.
  apply binds_remove_inv with y; auto.
  apply binds_belongs in Hbind. apply notin_belongs_neq with A E; auto.
Qed.

Theorem all_binds_all_remove : forall A ys (E F : gen_env A),
  ys ⊄ E -> E ⊏ F ->
  E ⊏ (F ∖ ys).
Proof.
  intros A ys E F Hnotin Habind. unfold all_binds in *. intros x v Hbind.
  apply binds_all_remove; auto.
  apply binds_belongs in Hbind. apply all_notin_belongs_neq with A E; auto.
Qed.

Theorem all_binds_all_remove_inv : forall A ys (E F : gen_env A),
  ys ⊄ E -> E ⊏ (F ∖ ys) ->
  E ⊏ F.
Proof.
  intros A ys E F Hnotin Habind. unfold all_binds in *. intros x v Hbind.
  apply binds_all_remove_inv with ys; auto.
  apply binds_belongs in Hbind. apply all_notin_belongs_neq with A E; auto.
Qed.

Theorem all_binds_remove_compat : forall A x (E F : gen_env A),
  ok E -> ok F ->
  E ⊏ F ->
  E ∖ {x} ⊏ F ∖ {x}.
Proof.
  intros A x E F Hok1 Hok2 Habind. unfold all_binds in *. intros y v Hbind.
  assert (y <> x) by
    (apply belongs_remove_inv with A E; auto;
      apply binds_belongs with v; auto).
  apply binds_remove; auto. apply Habind.
  apply binds_remove_inv with x; auto.
Qed.

Theorem all_binds_all_remove_compat : forall A xs (E F : gen_env A),
  ok E -> ok F ->
  E ⊏ F ->
  E ∖ xs ⊏ F ∖ xs.
Proof.
  induction xs as [ | x xs IHxs ]; intros E F Hok1 Hok2 Habind;
    simpl in *; auto.
  rewrite ?all_remove_nil; auto.
  assert (E ∖ {x} ⊏ F ∖ {x}) by (apply all_binds_remove_compat; auto).
  rewrite ?all_remove_remove.
  apply IHxs; auto; apply ok_remove; auto.
Qed.

(** All_Binds and ok *)
Theorem all_binds_ok_concat_inv : forall A (E F G : gen_env A),
  ok (E & F) ->
  (E & F) ⊏ G ->
  E ⊏ G ∧ F ⊏ G.
Proof.
  intros A E F G Hok Habind; unfold all_binds in *.
  split; intros x v Hbind; apply Habind.
  apply binds_concat_l; auto. apply binds_belongs in Hbind.
  apply belongs_ok_concat_inv_l with E; auto.
  apply binds_concat_r; auto.
Qed.

Theorem all_binds_concat_ok_comm : forall A (E F G : gen_env A),
  E ⊏ (F & G) ->
  ok (F & G) ->
  E ⊏ (G & F).
Proof.
  intros. unfold all_binds in *. intros.
  apply binds_concat_ok_comm; auto.
Qed.

(** All_Binds is reflexive, anti-symmetric and transitive *)
Theorem all_binds_refl : forall A (E F : gen_env A),
  E = F ->
  E ⊏ F.
Proof. intros; subst; unfold all_binds; auto. Qed.

Theorem all_binds_anti_sym : forall A (E F : gen_env A),
  E ⊏ F -> F ⊏ E ->
  E ≍ F.
Proof. unfold eq; auto. Qed.

Theorem all_binds_trans : forall A (E F G : gen_env A),
  E ⊏ F -> F ⊏ G ->
  E ⊏ G.
Proof. unfold all_binds; intros; auto. Qed.

(** Decidability of all_binds. *)

(**************************************************************************)
(* This lemma should appear in a List module...                           *)
Lemma list_length_S : forall A (l : list A) n,
  length l = S n -> exists x:A, exists l', l = x :: l'.
Proof.
  induction l as [ | a ]; intros n Hlen; simpl in *; inversion Hlen;
    exists a; exists l; auto.
Qed.
(**************************************************************************)

Theorem all_binds_dec_exists : forall A xs (F : gen_env A),
  List.NoDup xs ->
  { vs : list A | length xs = length vs ∧ (xs ∷ vs) ⊏ F }
  + { forall vs : list A, length xs = length vs -> ¬ (xs ∷ vs) ⊏ F }.
Proof.
  intros A xs F Hnodup. unfold all_binds. induction xs as [ | x xs IHxs ].

  (* case nil *)
  Focus.
  left. exists nil. split; auto. rewrite singles_empty. intros x v Hbind.
  apply binds_empty in Hbind. inversion Hbind.

  (* case cons *)
  assert (~ List.In x xs ∧ List.NoDup xs) as Hnodup2 by
    (inversion Hnodup; auto). clear Hnodup.
  destruct Hnodup2 as [ Hnotin Hnodup2 ].
  destruct IHxs as [ IH | IH ]; auto.

  (* case exists *)
  Focus.
  destruct IH as [ vs [ Hlen Hbind ] ].
  elim binds_dec_exists with A x F; intro Hex. destruct Hex as [ v Hbind2 ].
  left. exists (v :: vs). split; simpl; auto. intros y w Hbind3.
  assert (y ∹ w ⋲ ((xs ∷ vs) & (x ∶ v))) as Hbind4
    by (rewrite <- singles_cons; auto). clear Hbind3.
  apply binds_concat_inv in Hbind4.
  destruct Hbind4 as [ Hbind4 | [ Hnotin2 Hbind4 ] ]; auto.
  apply binds_single_inv in Hbind4. destruct Hbind4; subst; auto.

  right. intros ws Hlen2. inversion Hlen2 as [ Hlen3 ].
  apply eq_sym in Hlen3. apply list_length_S in Hlen3.
  destruct Hlen3 as [ w [ ws' Heq ] ]; subst; simpl in *.
  intro Hyp. apply (Hex w). apply (Hyp x w).
  assert (x ∹ w ⋲ ((xs ∷ ws') & (x ∶ w))). apply binds_concat_r.
  apply binds_single; auto. rewrite singles_cons; auto.

  (* case not exists *)
  Focus.
  right. intros vs Hlen. inversion Hlen as [ Hlen2 ].
  apply eq_sym in Hlen2. apply list_length_S in Hlen2.
  destruct Hlen2 as [ v [ vs' Heq ] ]. subst; simpl in *.
  intro Hyp. apply (IH vs'); auto. intros y w Hbind. apply Hyp.
  assert (y ∹ w ⋲ ((xs ∷ vs') & (x ∶ v))); auto.
  apply binds_concat_l; auto.
  apply binds_belongs in Hbind. inversion Hlen.
  apply belongs_singles_inv in Hbind; auto.
  apply notin_single. intro Heq; subst; auto.
  rewrite singles_cons; auto.
Qed.

Theorem all_binds_dec : forall A (E F : gen_env A),
  ok E ->
  (forall w w' : A, { w = w' } + { ¬ w = w' }) ->
  {E ⊏ F} + {¬ E ⊏ F}.
Proof.
  assert (forall A, (forall w w' : A, { w = w' } + { ¬ w = w' }) ->
    forall ws ws' : list A, { ws = ws' } + { ¬ ws = ws' }) as Hdec.
  intros A Hyp.
  induction ws as [ | w ws IHws ]; induction ws' as [ | w' ws' IHws' ];
    simpl in *; auto.
  right; intro Heq; inversion Heq.
  right; intro Heq; inversion Heq. destruct (Hyp w w'); destruct (IHws ws').
  left; subst; auto.
  right; intro Heq; inversion Heq; auto.
  right; intro Heq; inversion Heq; auto.
  right; intro Heq; inversion Heq; auto.

  intros A E F Hok Hdec2.
  assert (forall ws ws' : list A, { ws = ws' } + { ¬ ws = ws' })
    as Hdec3 by auto.

  assert (List.NoDup (dom E)) as Hdom by (apply ok_dom_inv; auto).
  elim all_binds_dec_exists with A (dom E) F; auto; intro Hyp.
  destruct Hyp as [ vs [ Hlen Habind ] ].
  elim (Hdec3 vs (img E)); intro Hyp; subst.
  left. rewrite dom_img_id in *; auto.
  right. intro Habind2. rewrite <- (dom_img_id E) in Habind2.
  assert (vs = img E).
  apply all_binds_singles_eq_inv with (dom E) F; auto.
  apply length_dom_img_eq. auto.
  right. intro Habind. apply (Hyp (img E)). 
  apply length_dom_img_eq. rewrite dom_img_id; auto.
Qed.

(* ---------------------------------------------------------------------- *)
(** **** Properties of eq *)

(** Eq is reflexive, symmetric and transitive *)
Theorem eq_refl : forall A (E F : gen_env A),
  E = F ->
  E ≍ F.
Proof. unfold eq. intro. split; apply all_binds_refl; auto. Qed.

Theorem eq_sym : forall A (E F : gen_env A),
  E ≍ F ->
  F ≍ E.
Proof. unfold eq; intros A E F Heq; destruct Heq; split; auto. Qed.

Theorem eq_trans : forall A (E F G : gen_env A),
  E ≍ F -> F ≍ G ->
  E ≍ G.
Proof.
  unfold eq; intros A E F G Heq1 Heq2. destruct Heq1, Heq2.
  split; apply all_binds_trans with F; auto.
Qed.

(** Eq implements equivalence over bindings. *)
Theorem eq_binds : forall A x (v : A) (E F : gen_env A),
  E ≍ F ->
  binds x v E ->
  binds x v F.
Proof. intros A x v E F Heq Hbind. unfold eq in *. destruct Heq. auto. Qed.

(** Concat to the right. *)
Theorem eq_concat : forall A (E F G : gen_env A),
  E ≍ F ->
  (E & G) ≍ (F & G).
Proof.
  unfold eq; intros A E F G Heq. destruct Heq.
  split; apply all_binds_concat_compat; auto.
Qed.

(** Concat is commutative with eq when ok. *)
Theorem eq_concat_comm : forall A (E F : gen_env A),
  ok (E & F) ->
  (E & F) ≍ (F & E).
Proof.
  intros. unfold eq.
  split; apply all_binds_concat_ok_comm; auto.
  auto; apply all_binds_refl; auto.
  apply all_binds_refl; auto. apply ok_concat_comm; auto.
Qed.

(** Eq commutes with other operations on environments. *)
Theorem eq_get : forall A (E F : gen_env A),
  E ≍ F ->
  forall x, get x E = get x F.
Proof.
  intros A E F Heq x. unfold eq in Heq. destruct Heq as [ Habind1 Habind2 ].
  unfold all_binds in *. unfold binds in *.
  elim get_dec with A x E; elim get_dec with A x F; intros Hyp1 Hyp2.
  destruct Hyp1 as [ v Hget1 ]; destruct Hyp2 as [ w Hget2 ].
  rewrite Hget1, Hget2. apply Habind1 in Hget2.
  rewrite Hget1 in Hget2; auto.
  destruct Hyp2 as [ v Hget2 ]. apply Habind1 in Hget2.
  rewrite Hyp1 in Hget2. inversion Hget2.
  destruct Hyp1 as [ v Hget1 ]. apply Habind2 in Hget1.
  rewrite Hyp2 in Hget1. inversion Hget1.
  rewrite Hyp1, Hyp2; auto.
Qed.

Theorem eq_get_inv : forall A (E F : gen_env A),
  (forall x, get x E = get x F) ->
  E ≍ F.
Proof.
  intros A E F Hyp. unfold eq, all_binds, binds.
  split; intros x v Hbind. rewrite <- Hbind; auto. rewrite Hyp; auto.
Qed.

Theorem eq_map : forall A B (f : A -> B) (E F : gen_env A),
  E ≍ F ->
  map f E ≍ map f F.
Proof.
  intros A B f E F Heq. unfold eq in *. destruct Heq.
  split; apply all_binds_map; auto.
Qed.

Theorem eq_map_inv : forall A B (f : A -> B) (E F : gen_env A),
  Image.injective A B f ->
  map f E ≍ map f F ->
  E ≍ F.
Proof.
  intros A B f E F Hinj Heq. unfold eq in *. destruct Heq.
  split; apply (all_binds_map_inv Hinj); auto.
Qed.

Theorem eq_remove : forall A x (E F : gen_env A),
  ok E -> ok F ->
  E ≍ F ->
  E ∖ {x} ≍ F ∖ {x}.
Proof.
  intros A x E F Hok1 Hok2 Heq. unfold eq in *. destruct Heq.
  split; apply all_binds_remove_compat; auto.
Qed.

Theorem eq_all_remove : forall A xs (E F : gen_env A),
  ok E -> ok F ->
  E ≍ F ->
  E ∖ xs ≍ F ∖ xs.
Proof.
  intros A xs E F Hok1 Hok2 Heq. unfold eq in *. destruct Heq.
  split; apply all_binds_all_remove_compat; auto.
Qed.

Theorem eq_update : forall A (E F G : gen_env A),
  E ≍ F ->
  (E ::= G) ≍ (F ::= G).
Proof.
  intros A E F G Heq. unfold eq in *. destruct Heq.
  split; apply all_binds_update; auto.
Qed.

Theorem eq_belongs : forall A x (E F : gen_env A),
  E ≍ F ->
  x ∈ E ->
  x ∈ F.
Proof.
  intros A x E F Heq Hin. unfold eq in *.
  destruct Heq as [ Habind1 Habind2 ]. unfold all_binds in *.
  apply belongs_binds in Hin. destruct Hin as [ v Hbind ].
  apply Habind1 in Hbind. apply binds_belongs with v; auto.
Qed.

Theorem eq_all_belongs : forall A xs (E F : gen_env A),
  E ≍ F ->
  xs ⊂ E ->
  xs ⊂ F.
Proof.
  intros A xs E F Heq Hin. unfold eq in *.
  destruct Heq as [ Habind1 Habind2 ].
  apply all_binds_belongs in Habind1.
  apply all_belongs_def. intros.
  apply all_belongs_def_inv with (dom E); auto.
  apply belongs_dom.
  apply all_belongs_def_inv with xs; auto.
Qed.

Theorem eq_notin : forall A x (E F : gen_env A),
  E ≍ F ->
  x ∉ E ->
  x ∉ F.
Proof.
  intros A x E F Heq Hnotin. unfold eq in *.
  destruct Heq as [ Habind1 Habind2 ]. unfold all_binds in *.
  apply not_belongs_notin. intro Hin.
  apply belongs_binds in Hin. destruct Hin as [ v Hbind ].
  apply Habind2 in Hbind. apply binds_belongs in Hbind.
  apply notin_belongs in Hnotin. contradiction.
Qed.

Theorem eq_all_notin : forall A xs (E F : gen_env A),
  E ≍ F ->
  xs ⊄ E ->
  xs ⊄ F.
Proof.
  intros A xs E F Heq Hnotin. apply all_notin_def. intros.
  apply eq_notin with E; auto.
  apply all_notin_def_inv with xs; auto.
Qed.

(** Decidability of eq. *)
Theorem eq_dec : forall A (E F : gen_env A),
  (forall w w' : A, { w = w' } + { ¬ w = w' }) ->
  ok E -> ok F ->
  { E ≍ F } + { ¬ E ≍ F }.
Proof.
  intros A E F Hdec Hok1 Hok2; unfold eq.
  elim all_binds_dec with A E F; elim all_binds_dec with A F E; intros;
    auto; right; intro Heq; destruct Heq; contradiction.
Qed.

(* ---------------------------------------------------------------------- *)
(** **** Additional principal properties *)

Theorem update_is_remove_concat : forall A x (v : A) (E : gen_env A),
  x ∈ E ->
  E ::= (x ∶ v) ≍ (E ∖ {x}) & (x ∶ v).
Proof.
  intros A x v E Hin. unfold eq. split; unfold all_binds; intros y w Hbind.
  apply binds_update_inv in Hbind.
  destruct Hbind as [ [ Hnotin Hbind ] | [ Hin2 Hbind ] ].
  apply binds_concat_l; auto. apply notin_single_inv in Hnotin.
  apply binds_remove; auto.
  apply binds_concat_r; auto.
  apply binds_concat_inv in Hbind.
  destruct Hbind as [ Hbind | [ Hnotin Hbind ] ].
  apply binds_single_inv in Hbind. destruct Hbind; subst.
  apply binds_update_self; auto.
  apply binds_update_notin; auto.
  apply binds_remove_inv with x; auto.
  apply notin_single_inv with A v; auto.
Qed.

End Properties.

End GenericEnvironmentType.
