(***************************************************************************
* Generic Environments implemented as lists                                *
*                                                                          *
* Emmanuel Polonowski, April 2011, Coq v8.3                                *
*                                                                          *
* (Inspired by the work of A. Chargueraud :                                *
*  http://www.chargueraud.org/softs/ln/index.php)                          *
***************************************************************************)

Require Import Utf8.
Require List Bool.
Set Implicit Arguments.

(* ********************************************************************** *)
(** * Module of an implementation of environments with lists              *)

Require Import Equalities.

Module CoreGenericEnvListDef (VarType : UsualDecidableType).

Import List Bool.

Import VarType.

Definition TVar := VarType.t.

(* ---------------------------------------------------------------------- *)
(** ** Definitions *)

Definition gen_env A := list (TVar * A).

Section CoreDefinitions.

Variable A B : Type.
Implicit Types x y : TVar.
Implicit Types xs ys : list TVar.
Implicit Types v w : A.
Implicit Types vs ws : list A.
Implicit Types E F G : gen_env A.
Implicit Types f g : A -> B.

Definition eq_keys_dec := VarType.eq_dec.

(** Preliminary properties of eq_keys_dec. *)

Lemma eq_keys_true : forall A x (a b : A),
  (if eq_keys_dec x x then a else b) = a.
Proof. intros. case (eq_keys_dec x x); congruence. Qed.

Lemma eq_keys_false : forall A x y (a b : A),
  x <> y -> (if eq_keys_dec x y then a else b) = b.
Proof. intros. case (eq_keys_dec x y); congruence. Qed.

Definition empty : gen_env A := nil.

Definition single x v := (x, v) :: nil.

Fixpoint singles xs vs : gen_env A :=
  match xs, vs with
    | x :: xs, v :: vs => (x, v) :: (singles xs vs)
    | _, _ => nil
  end.

Definition concat E F := F ++ E.

Fixpoint get x E : option A :=
  match E with
    | nil => None
    | (y, v) :: E' => if eq_keys_dec x y then Some v else get x E'
  end.

Fixpoint dom E : list TVar :=
  match E with
    | nil => nil
    | (x, _) :: E' => x :: (dom E')
  end.

Fixpoint img E : list A :=
  match E with
    | nil => nil
    | (_, v) :: E' => v :: (img E')
  end.

Definition belongs x E :=
  List.In x (dom E).

Definition all_belongs xs E :=
  forall x, List.In x xs -> belongs x E.

Definition notin x E := 
  ~ belongs x E.

Definition all_notin xs E :=
  forall x, List.In x xs -> notin x E.

Fixpoint map f E : gen_env B :=
  match E with
    | nil => nil
    | (x, v) :: E' => (x, f v) :: map f E'
  end.

Fixpoint update_one E x v : gen_env A :=
  match E with
    | nil => nil
    | (y, v') :: E' =>
      if eq_keys_dec x y then (y, v) :: E'
        else (y, v') :: (update_one E' x v)
  end.

Fixpoint update E F : gen_env A :=
  match F with
    | nil => E
    | (x, v) :: F' => update_one (update E F') x v
  end.

Fixpoint remove x E : gen_env A :=
  match E with
    | nil => nil
    | (y, v) :: E => if eq_keys_dec x y then E else (y, v) :: (remove x E)
  end.

Fixpoint all_remove xs E : gen_env A :=
  match xs with
    | nil => E
    | x :: xs => all_remove xs (remove x E)
  end.

Inductive ok : gen_env A -> Prop :=
| ok_nil : ok nil
| ok_cons : forall x v F, ok F ∧ notin x F -> ok (concat F (single x v))
.

End CoreDefinitions.

(** [x ∶ v] is the notation for a singleton environment mapping x to v. *)

Notation "x '∶' v" := (single x v)
  (at level 63) : gen_env_scope.

(** [xs ∷ vs] is the notation for an environment mapping xs to vs. *)

Notation "xs '∷' vs" := (singles xs vs)
  (at level 63) : gen_env_scope.

(** [E & F] is the notation for concatenation of E and F. *)

Notation "E '&' F" := (concat E F) 
  (at level 65, left associativity) : gen_env_scope.

(** [E ∖ { x } ] is the notation for removing x from E. *)

Notation "E '∖' '{' x '}'" := (remove x E) 
  (at level 64, left associativity) : gen_env_scope.

(** [E ∖ xs ] is the notation for removing xs from E. *)

Notation "E '∖' xs" := (all_remove xs E) 
  (at level 64, left associativity) : gen_env_scope.

(** [E '[' x '<-' v ']' ] is the notation for updating x in E with v. *)

Notation "E '[' x '<-' v ']'" := (update_one E x v) 
  (at level 65, left associativity) : gen_env_scope.

(** [E ::= F] is the notation for updating of E with F. *)

Notation "E '::=' F" := (update E F) 
  (at level 65, left associativity) : gen_env_scope.

(** [x ∈ E] to be read x is bound in E. *)

Notation "x '∈' E" := (belongs x E)
  (at level 67) : gen_env_scope.

(** [xs ⊂ E] to be read xs are bound in E. *)

Notation "xs '⊂' E" := (all_belongs xs E)
  (at level 67) : gen_env_scope.

(** [x '∉' E] to be read x is unbound in E. *)

Notation "x '∉' E" := (notin x E)
  (at level 67) : gen_env_scope.

(** [xs '⊄' E] to be read xs are unbound in E. *)

Notation "xs '⊄' E" := (all_notin xs E)
  (at level 67) : gen_env_scope.

Bind Scope gen_env_scope with gen_env.
Delimit Scope gen_env_scope with gen_env.
Local Open Scope gen_env_scope.

(* ---------------------------------------------------------------------- *)
(** ** Properties *)

Section Properties.
Variable A B : Type.
Implicit Types x y : TVar.
Implicit Types xs ys : list TVar.
Implicit Types v w : A.
Implicit Types vs ws : list A.
Implicit Types E F G : gen_env A.
Implicit Types f g : A -> B.

(* ---------------------------------------------------------------------- *)
(** *** Primary properties *)

(** Induction scheme over environments. *)
Lemma env_ind : forall (P : gen_env A -> Prop),
  (P (@empty A)) ->
  (forall E x v, P E -> P (E & (x ∶ v))) ->
  (forall E, P E).
Proof.
  unfold concat, single, singles.
  induction E as [ | (x, v) ]; simpl in *; auto.
Qed.

(* ---------------------------------------------------------------------- *)
(** **** Properties of singulars *)

Lemma singles_empty :
  nil ∷ nil = (@empty A).
Proof. auto. Qed.

Lemma singles_cons : forall x xs v vs,
  (x :: xs) ∷ (v :: vs) = (xs ∷ vs) & (x ∶ v).
Proof. auto. Qed.

Lemma singles_empty_r : forall xs,
  xs ∷ nil = (@empty A).
Proof. induction xs as [ | x ]; auto. Qed.

Lemma singles_empty_l : forall vs,
  nil ∷ vs = (@empty A).
Proof. induction vs as [ | v ]; auto. Qed.

(* ---------------------------------------------------------------------- *)
(** **** Properties of concatenation *)

Lemma concat_empty_r : forall E,
  E & (@empty A) = E.
Proof. auto. Qed.

Lemma concat_empty_l : forall E,
  (@empty A) & E = E.
Proof.
  induction E as [ | (x, v) E IHE ]; unfold concat in *;
    simpl in *; [ | rewrite IHE ]; auto.
Qed.

Lemma concat_assoc : forall E F G,
  E & (F & G) = (E & F) & G.
Proof.
  intros. unfold concat. rewrite app_assoc. auto.
Qed.

(* ---------------------------------------------------------------------- *)
(** **** Properties of get *)

Lemma get_empty : forall x,
  get x (@empty A) = None.
Proof. auto. Qed.

Lemma get_single_eq : forall x y v,
  x = y ->
  get x (y ∶ v) = Some v.
Proof. intros; subst. simpl. apply eq_keys_true. Qed.

Lemma get_single_eq_inv : forall x y v w,
  get x (y ∶ w) = Some v ->
  x = y /\ v = w.
Proof.
  intros x y v w Hget. simpl in Hget.
  destruct (eq_keys_dec x y) as [ Heq | Hneq ];
    subst; inversion Hget; auto.
Qed.

Lemma get_dec : forall x E,
  { v : A | get x E = Some v } + { get x E = None }.
Proof.
  intros. induction E as [ | (y, w) ].
  right; auto. simpl. destruct (eq_keys_dec x y).
  left; exists w; auto. auto.
Qed.

Lemma get_concat_r : forall x y v E,
  x = y ->
  get x (E & (y ∶ v)) = Some v.
Proof.
  intros x y v E Heq; subst. simpl. assert (y = y) by auto.
  destruct (eq_keys_dec y y); auto; try contradiction.
Qed.

Lemma get_concat_l : forall x y v E,
  x <> y ->
  get x (E & (y ∶ v)) = get x E.
Proof.
  intros x y v E Hneq. simpl.
  destruct (eq_keys_dec x y); auto; try contradiction.
Qed.

Lemma get_concat_inv : forall x y v w E,
  get x (E & (y ∶ v)) = Some w ->
  (x = y /\ v = w) \/ (x <> y /\ get x E = Some w).
Proof.
  intros x y v w E Hget. simpl in *.
  destruct (eq_keys_dec x y); [ left | right ]; inversion Hget; auto.
Qed.

(* ---------------------------------------------------------------------- *)
(** **** Properties of dom *)

Lemma dom_empty :
  dom (@empty A) = nil.
Proof. auto. Qed.

Lemma dom_empty_inv : forall E,
  dom (E) = nil ->
  E = (@empty A).
Proof. induction E as [ | (x, v) ]; intro Heq; auto. inversion Heq. Qed.

Lemma dom_single : forall x v,
  dom (x ∶ v) = x :: nil.
Proof. auto. Qed.

Lemma dom_singles : forall xs vs,
  length xs = length vs ->
  dom (xs ∷ vs) = xs.
Proof.
  induction xs as [ | x xs IHxs ]; induction vs;
    intro Hlen; inversion Hlen as [ Hlen2 ]; auto.
  simpl. rewrite (IHxs vs Hlen2); auto.
Qed.

Lemma dom_singles_incl : forall xs vs,
  List.incl (dom (xs ∷ vs)) xs.
Proof.
  induction xs; induction vs; intros; simpl; auto.
  apply incl_refl.
  unfold List.incl; intros x Hin; inversion Hin.
  apply List.incl_cons. simpl; auto.
  apply List.incl_tl. auto.
Qed.

Lemma dom_concat : forall E F,
  dom (E & F) = List.app (dom F) (dom E).
Proof.
  intros E F; generalize E; induction F as [ | (x, v) F IHF ];
    intros; simpl in *; auto.
  rewrite IHF. reflexivity.
Qed.

(* ---------------------------------------------------------------------- *)
(** **** Properties of img *)

Lemma img_empty :
  img (@empty A) = nil.
Proof. auto. Qed.

Lemma img_empty_inv : forall E,
  img (E) = nil ->
  E = (@empty A).
Proof. induction E as [ | (x, v) ]; intro Heq; auto. inversion Heq. Qed.

Lemma img_single : forall x v,
  img (x ∶ v) = v :: nil.
Proof. auto. Qed.

Lemma img_singles : forall xs vs,
  length xs = length vs ->
  img (xs ∷ vs) = vs.
Proof.
  induction xs as [ | x xs IHxs ]; induction vs;
    intro Hlen; inversion Hlen as [ Hlen2 ]; auto.
  simpl. rewrite (IHxs vs Hlen2); auto.
Qed.

Lemma img_singles_incl : forall xs vs,
  List.incl (img (xs ∷ vs)) vs.
Proof.
  induction xs; induction vs; intros; simpl; auto.
  apply incl_refl.
  unfold List.incl; intros x Hin; inversion Hin.
  apply incl_refl.
  apply List.incl_cons. simpl; auto.
  apply List.incl_tl. auto.
Qed.

Lemma img_concat : forall E F,
  img (E & F) = List.app (img F) (img E).
Proof.
  intros E F; generalize E; induction F as [ | (x, v) F IHF ];
    intros; simpl in *; auto.
  rewrite IHF. reflexivity.
Qed.

Lemma dom_img_id : forall E,
  (dom E) ∷ (img E) = E.
Proof.
  induction E as [ | (x, v) E IHE ]; simpl in *; auto. rewrite IHE; auto.
Qed.

Lemma length_dom_img_eq : forall E,
  length (dom E) = length (img E).
Proof. induction E as [ | (x, v) ]; simpl in *; auto. Qed.

(* ---------------------------------------------------------------------- *)
(** **** Properties of belongs *)

Lemma belongs_empty : forall x,
  x ∈ (@empty A) ->
  False.
Proof. auto. Qed.

Lemma belongs_single : forall x y v,
  x = y ->
  x ∈ (y ∶ v).
Proof. unfold belongs; simpl; auto. Qed.

Lemma belongs_single_inv : forall x y v,
  x ∈ (y ∶ v) ->
  x = y.
Proof.
  unfold belongs; simpl; intros x y v Hor;
    inversion Hor as [ Heq | Hfalse ]; auto; inversion Hfalse.
Qed.

Lemma belongs_singles : forall x xs vs,
  length xs = length vs ->
  List.In x xs ->
  x ∈ (xs ∷ vs).
Proof.
  intros; unfold belongs; simpl; auto.
  rewrite dom_singles; auto.
Qed.

Lemma belongs_singles_inv : forall x xs vs,
  length xs = length vs ->
  x ∈ (xs ∷ vs) ->
  List.In x xs.
Proof.
  intros x xs vs Hlen Hin; unfold belongs in *; simpl in *; auto.
  rewrite dom_singles in Hin; auto.
Qed.

Lemma belongs_concat_l : forall x F G,
  x ∈ F ->
  x ∈ (F & G).
Proof.
  unfold belongs. intros. rewrite dom_concat.
  apply List.in_or_app. right; auto.
Qed.

Lemma belongs_concat_r : forall x F G,
  x ∈ F ->
  x ∈ (G & F).
Proof.
  unfold belongs. intros. rewrite dom_concat.
  apply List.in_or_app. left; auto.
Qed.

Lemma belongs_concat_inv : forall x F G,
  x ∈ (F & G) ->
  x ∈ F ∨ x ∈ G.
Proof.
  unfold belongs. intros. rewrite dom_concat in * |-.
  apply or_comm. apply List.in_app_or; auto.
Qed.

Lemma belongs_dom : forall x E,
  x ∈ E ->
  List.In x (dom E).
Proof. auto. Qed.

Lemma belongs_dom_inv : forall x E,
  List.In x (dom E) ->
  x ∈ E.
Proof. auto. Qed.

(* ---------------------------------------------------------------------- *)
(** **** Properties of all_belongs *)

Lemma all_belongs_def : forall xs E,
  (forall x, List.In x xs -> x ∈ E) ->
  xs ⊂ E.
Proof. auto. Qed.

Lemma all_belongs_def_inv : forall xs E,
  xs ⊂ E ->
  (forall x, List.In x xs -> x ∈ E).
Proof. auto. Qed.

Lemma all_belongs_belongs : forall x xs E,
  (x :: xs) ⊂ E ->
  x ∈ E ∧ xs ⊂ E.
Proof.
  unfold all_belongs. intros x xs E Hyp. simpl in *.
  split; [ | intros ]; apply Hyp; auto.
Qed.

Lemma belongs_all_belongs : forall x xs E,
  x ∈ E ∧ xs ⊂ E ->
  (x :: xs) ⊂ E.
Proof.
  unfold all_belongs. intros x xs E Hyp y Hin. simpl in *.
  destruct Hyp. destruct Hin; subst; auto.
Qed.

Lemma all_belongs_empty : forall xs,
  xs ⊂ (@empty A) ->
  xs = nil.
Proof.
  induction xs as [ | x ]; intro Hin; simpl in *; auto.
  unfold all_belongs, belongs in Hin.
  rewrite dom_empty in Hin. simpl in Hin.
  elim Hin with x. left; auto.
Qed.

Lemma all_belongs_nil : forall E,
  nil ⊂ E.
Proof. unfold all_belongs; simpl; intros E x Hfalse; inversion Hfalse. Qed.

Lemma all_belongs_single : forall xs y v,
  xs = y :: nil ->
  xs ⊂ (y ∶ v).
Proof.
  intros; subst. unfold all_belongs. intros. auto.
Qed.

Lemma all_belongs_single_inv : forall xs y v,
  length xs = 1 ->
  xs ⊂ (y ∶ v) ->
  xs = y :: nil.
Proof.
  induction xs as [ | x xs IHxs ]; intros y v Hlen Hin; simpl in *; auto;
    inversion Hlen as [ Hlen2 ].
  assert (xs = nil) as Hxsnil by
    (induction xs; simpl in *; auto; inversion Hlen2).
  rewrite Hxsnil; f_equal.
  unfold all_belongs in Hin; simpl in Hin.
  assert (x ∈ (y ∶ v)) as Hin2 by 
    (apply Hin; left; auto).
  inversion Hin2 as [ | Hfalse ]; auto. inversion Hfalse.
Qed.

Lemma all_belongs_singles : forall xs ys vs,
  length ys = length vs ->
  List.incl xs ys ->
  xs ⊂ (ys ∷ vs).
Proof.
  unfold all_belongs. intros. apply belongs_singles; auto.
Qed.

Lemma all_belongs_singles_inv : forall xs ys vs,
  xs ⊂ (ys ∷ vs) ->
  List.incl xs ys.
Proof.
  unfold all_belongs. intros xs ys vs Hincl. unfold belongs in Hincl.
  unfold List.incl. intros x Hin. apply Hincl in Hin.
  assert (forall x l l', List.In x l -> List.incl l l' -> List.In x l')
    as Hincl2 by auto.
  apply Hincl2 with (dom (ys ∷ vs)); auto.
  apply dom_singles_incl.
Qed.

Lemma all_belongs_concat_l : forall xs F G,
  xs ⊂ F ->
  xs ⊂ (F & G).
Proof.
  intros xs F G Hincl. unfold all_belongs in *. intros x Hin.
  apply Hincl in Hin. apply belongs_concat_l; auto.
Qed.

Lemma all_belongs_concat_r : forall xs F G,
  xs ⊂ F ->
  xs ⊂ (G & F).
Proof.
  intros xs F G Hincl. unfold all_belongs in *. intros x Hin.
  apply Hincl in Hin. apply belongs_concat_r; auto.
Qed.

Lemma all_belongs_dom : forall xs E,
  xs ⊂ E ->
  List.incl xs (dom E).
Proof. auto. Qed.

Lemma all_belongs_dom_inv : forall xs E F,
  List.incl xs (dom E) ->
  xs ⊂ E.
Proof. auto. Qed.

(* ---------------------------------------------------------------------- *)
(** **** Properties of notin *)

Lemma notin_belongs : forall x E,
  x ∉ E ->
  ¬ x ∈ E.
Proof. auto. Qed.

Lemma belongs_notin : forall x E,
  x ∈ E ->
  ¬ x ∉ E.
Proof. auto. Qed.

Lemma not_belongs_notin : forall A x (E : gen_env A),
  ¬ x ∈ E ->
  x ∉ E.
Proof. auto. Qed.

Lemma notin_belongs_neq : forall x y E,
  x ∈ E -> y ∉ E ->
  x <> y.
Proof. intros x y E Hin Hnotin. intro Heq; subst. contradiction. Qed.

Lemma notin_empty : forall x,
  x ∉ (@empty A).
Proof. unfold notin. auto. Qed.

Lemma notin_single : forall x y v,
  x <> y ->
  x ∉ (y ∶ v).
Proof.
  intros x y v Hneq Hin. elim Hneq.
  apply belongs_single_inv with v; auto.
Qed.

Lemma notin_single_inv : forall x y v,
  x ∉ (y ∶ v) ->
  x <> y.
Proof.
  intros x y v Hnotin Heq. elim Hnotin.
  apply belongs_single; auto.
Qed.

Lemma notin_singles : forall x xs vs,
  ¬ List.In x xs ->
  x ∉ (xs ∷ vs).
Proof.
  intros x xs vs Hnotin Hin. elim Hnotin.
  unfold belongs in Hin.
  assert (forall x l l', List.In x l -> List.incl l l' -> List.In x l')
    as Hincl by auto.
  apply Hincl with (dom (xs ∷ vs)); auto. apply dom_singles_incl.
Qed.

Lemma notin_singles_inv : forall x xs vs,
  length xs = length vs ->
  x ∉ (xs ∷ vs) ->
  ¬ List.In x xs.
Proof.
  intros x xs vs Heq Hnotin Hin. elim Hnotin.
  unfold belongs. rewrite dom_singles; auto.
Qed.

Lemma notin_concat : forall x F G,
  x ∉ F -> x ∉ G ->
  x ∉ (F & G).
Proof.
  intros x F G HnotinF HnotinG HinFG. apply belongs_concat_inv in HinFG.
  destruct HinFG; [ elim HnotinF | elim HnotinG ]; auto.
Qed.

Lemma notin_concat_inv : forall x F G,
  x ∉ (F & G) ->
  x ∉ F ∧ x ∉ G.
Proof.
  intros x F G Hnotin.
  split; intro Hin; elim Hnotin;
    [ apply belongs_concat_l | apply belongs_concat_r ]; auto.
Qed.

Lemma notin_dom : forall x E,
  x ∉ E ->
  ¬ List.In x (dom E).
Proof. auto. Qed.

Lemma notin_dom_inv : forall x E F,
  ¬ List.In x (dom E) ->
  x ∉ E.
Proof. auto. Qed.

(* ---------------------------------------------------------------------- *)
(** **** Properties of all_notin *)

Lemma all_notin_empty_l : forall E,
  nil ⊄ E.
Proof. unfold all_notin; intros E x Hin. inversion Hin. Qed.

Lemma all_notin_def : forall xs E,
  (forall x, List.In x xs -> x ∉ E) ->
  xs ⊄ E.
Proof. auto. Qed.

Lemma all_notin_def_inv : forall xs E,
  xs ⊄ E ->
  (forall x, List.In x xs -> x ∉ E).
Proof. auto. Qed.

Lemma all_notin_notin : forall x xs E,
  (x :: xs) ⊄ E ->
  x ∉ E ∧ xs ⊄ E.
Proof.
  unfold all_notin; simpl. intros. auto.
Qed.

Lemma notin_all_notin : forall x xs E,
  x ∉ E ∧ xs ⊄ E ->
  (x :: xs) ⊄ E.
Proof.
  unfold all_notin; simpl. intros x xs E Hyp y Hyp2.
  destruct Hyp. destruct Hyp2; subst; auto.
Qed.

Lemma all_notin_belongs_neq : forall x ys E,
  x ∈ E -> ys ⊄ E ->
  ¬ List.In x ys.
Proof.
  intros x ys E Hin Hnotincl. unfold all_notin in *. intro Hin2.
  apply Hnotincl in Hin2. contradiction.
Qed.

Lemma all_notin_empty_r : forall xs,
  xs ⊄ (@empty A).
Proof.
  unfold all_notin. intros. apply notin_empty.
Qed.

Lemma all_notin_nil : forall E,
  nil ⊄ E.
Proof. unfold all_notin. intros E x Hin. inversion Hin. Qed.

Lemma all_notin_single : forall xs y v,
  ¬ List.In y xs ->
  xs ⊄ (y ∶ v).
Proof.
  intros xs y v Hnotin. unfold all_notin. intros x Hin.
  apply notin_single. intro; subst. contradiction.
Qed.

Lemma all_notin_single_inv : forall xs y v,
  xs ⊄ (y ∶ v) ->
  ¬ List.In y xs.
Proof.
  unfold all_notin. intros xs y v Hnotincl. intro Hin.
  apply Hnotincl in Hin. apply Hin. apply belongs_single; auto.
Qed.


Lemma all_notin_singles : forall xs ys vs,
  List.Forall (fun x => ¬ List.In x ys) xs ->
  xs ⊄ (ys ∷ vs).
Proof.
  intros xs ys vs Hforall.
  unfold all_notin; intros x Hin.
  apply notin_singles.
  apply (List.Forall_forall (fun x => ¬ In x ys) xs); intros; auto.
Qed.

Lemma all_notin_singles_inv : forall xs ys vs,
  length ys = length vs ->
  xs ⊄ (ys ∷ vs) ->
  List.Forall (fun x => ¬ List.In x ys) xs.
Proof.
  intros xs ys vs Heq Hnotin. unfold all_notin in Hnotin.
  elim (List.Forall_forall (fun x => ¬ In x ys) xs); intros Hyp1 Hyp2.
  apply Hyp2. intros x Hin. apply Hnotin in Hin.
  apply notin_singles_inv with vs; auto.
Qed.

Lemma all_notin_concat : forall xs F G,
  xs ⊄ F -> xs ⊄ G ->
  xs ⊄ (F & G).
Proof.
  intros. unfold all_notin in *. intros.
  apply notin_concat; auto.
Qed.

Lemma all_notin_concat_inv : forall xs F G,
  xs ⊄ (F & G) ->
  xs ⊄ F ∧ xs ⊄ G.
Proof.
  intros xs F G Hnotincl. unfold all_notin in *.
  split; intros x Hin; apply Hnotincl in Hin;
    apply notin_concat_inv in Hin; destruct Hin; auto.
Qed.

Lemma all_notin_dom : forall xs E,
  xs ⊄ E ->
  List.Forall (fun x => ¬ List.In x (dom E)) xs.
Proof.
  intros. unfold all_notin, notin, belongs in *.
  apply List.Forall_forall; auto.
Qed.

Lemma all_notin_dom_inv : forall xs E,
  List.Forall (fun x => ¬ List.In x (dom E)) xs ->
  xs ⊄ E.
Proof.
  intros. unfold all_notin, notin, belongs.
  apply List.Forall_forall; auto.
Qed.

(* ---------------------------------------------------------------------- *)
(** **** Properties of map *)

Lemma map_empty : forall f,
  map f (@empty A) = (@empty B).
Proof. auto. Qed.

Lemma map_single : forall f x v,
  map f (x ∶ v) = x ∶ (f v).
Proof. auto. Qed.

Lemma map_singles : forall f xs vs,
  map f (xs ∷ vs) = xs ∷ (List.map f vs).
Proof.
  induction xs as [ | x xs IHxs ]; induction vs; simpl in *; auto.
  f_equal. apply IHxs.
Qed.

Lemma map_concat : forall f E F,
  map f (E & F) = (map f E) & (map f F).
Proof.
  intros. induction F as [ | (x, v) F IHF ]; simpl; auto.
  rewrite IHF. reflexivity.
Qed.

Lemma dom_map : forall E f,
  dom (map f E) = dom E.
Proof.
  intros; induction E as [ | (x, v) E IHE ]; simpl; auto.
  rewrite IHE; auto.
Qed.

Lemma belongs_map : forall x E f,
  x ∈ E ->
  x ∈ (map f E).
Proof.
  unfold belongs. intros; rewrite dom_map; auto.
Qed.

Lemma belongs_map_inv : forall x E f,
  x ∈ (map f E) ->
  x ∈ E.
Proof.
  unfold belongs. intros; rewrite dom_map in * |-; auto.
Qed.

Lemma all_belongs_map : forall xs E f,
  xs ⊂ E ->
  xs ⊂ (map f E).
Proof.
  unfold all_belongs; intros xs E f Hincl x Hin.
  apply Hincl in Hin. apply belongs_map; auto.
Qed.

Lemma all_belongs_map_inv : forall xs E f,
  xs ⊂ (map f E) ->
  xs ⊂ E.
Proof.
  unfold all_belongs; intros xs E f Hincl x Hin. apply Hincl in Hin.
  apply belongs_map_inv with f; auto.
Qed.

Lemma notin_map : forall x E f,
  x ∉ E ->
  x ∉ (map f E).
Proof.
  intros x E f Hnotin Hin. elim Hnotin.
  apply belongs_map_inv with f; auto.
Qed.

Lemma notin_map_inv : forall x E f,
  x ∉ (map f E) ->
  x ∉ E.
Proof.
  intros x E f Hnotin Hin. elim Hnotin.
  apply belongs_map; auto.
Qed.

Lemma all_notin_map : forall xs E f,
  xs ⊄ E ->
  xs ⊄ (map f E).
Proof.
  intros xs E f Hnotincl. unfold all_notin in *. intros x Hin.
  apply Hnotincl in Hin. apply notin_map; auto.
Qed.

Lemma all_notin_map_inv : forall xs E f,
  xs ⊄ (map f E) ->
  xs ⊄ E.
Proof.
  intros xs E f Hnotincl. unfold all_notin in *; intros x Hin.
  apply Hnotincl in Hin. apply notin_map_inv with f; auto.
Qed.

Lemma ok_map : forall E f,
  ok E ->
  ok (map f E).
Proof.
  intros E f Hok. induction E using env_ind. rewrite map_empty.
  apply ok_nil.
  rewrite map_concat. rewrite map_single. apply ok_cons.
  inversion Hok as [ | y w F Hok2 ]; subst.
  destruct Hok2 as [ Hok2 Hnotin ]. split; auto.
  intro Hin. elim Hnotin. apply belongs_map_inv with f; auto.
Qed.

Lemma ok_map_inv : forall E f,
  ok (map f E) ->
  ok E.
Proof.
  intros E f Hok. induction E using env_ind.
  apply ok_nil.
  rewrite map_concat in Hok. rewrite map_single in Hok. apply ok_cons.
  inversion Hok as [ | y w F Hok2 ]; subst.
  destruct Hok2 as [ Hok2 Hnotin ]. split; auto.
  intro Hin. elim Hnotin. apply belongs_map; auto.
Qed.

(* ---------------------------------------------------------------------- *)
(** **** Properties of update_one *)

Lemma update_one_empty : forall x v,
  (@empty A) [x <- v] = (@empty A).
Proof. auto. Qed.

Lemma update_one_single : forall x y v w,
  x = y ->
  (x ∶ v) [y <- w] = (x ∶ w).
Proof.
  intros x y v w Heq. subst. simpl.
  destruct (eq_keys_dec y y) as [ Heq | Hneq ]; auto; elim Hneq; auto.
Qed.

Lemma update_one_single_neq : forall x y v w,
  x <> y ->
  (x ∶ v) [y <- w] = (x ∶ v).
Proof.
  intros x y v w Hneq. simpl.
  destruct (eq_keys_dec y x) as [ Heq | Hneq2 ]; auto. elim Hneq; auto.
Qed.

Lemma update_one_concat_r : forall x v E F,
  x ∈ F ->
  (E & F) [x <- v] = E & (F [x <- v]).
Proof.
  intros x v E F Hin.
  induction F as [ | (y, w) F IHF ]; simpl in *; auto. inversion Hin.
  destruct (eq_keys_dec x y) as [ Heq | Hneq ]; simpl in *; auto.
  unfold belongs in Hin. simpl in Hin. destruct Hin as [ Heq | Hin ].
  elim Hneq; auto. f_equal; auto.
Qed.

Lemma update_one_concat_l : forall x v E F,
  x ∉ F ->
  (E & F) [x <- v] = (E [x <- v]) & F.
Proof.
  intros x v E F Hnotin.
  induction F as [ | (y, w) F IHF ]; simpl in *; auto.
  unfold notin, belongs in Hnotin. simpl in Hnotin.
  destruct (eq_keys_dec x y) as [ Heq | Hneq ]; simpl in *; auto.
  elim Hnotin; auto. f_equal. apply IHF. unfold notin. intro.
  elim Hnotin; auto.
Qed.

Lemma dom_update_one : forall x v E,
  dom (E [x <- v]) = dom E.
Proof.
  intros x v. induction E as [ | (y, w) E IHE ]; simpl in *; auto.
  destruct (eq_keys_dec x y) as [ Heq | Hneq ]; simpl in *; auto.
  f_equal; auto.
Qed.

Lemma belongs_update_one : forall x y v E,
  y ∈ E ->
  y ∈ (E [x <- v]).
Proof.
  intros x y v.
  induction E as [ | (z, w) E IHE ]; intro Hin; simpl in *; auto.
  destruct (eq_keys_dec x z) as [ Heq | Hneq ]; simpl in *; auto.
  unfold belongs in Hin |- *. simpl in *.
  destruct Hin; [ left | right ]; auto. apply IHE; auto.
Qed.

Lemma belongs_update_one_inv : forall x y v E,
  y ∈ (E [x <- v]) ->
  y ∈ E.
Proof.
  intros x y v.
  induction E as [ | (z, w) E IHE ]; intro Hin; simpl in *; auto.
  destruct (eq_keys_dec x z) as [ Heq | Hneq ]; simpl in *; auto.
  unfold belongs in Hin |- *. simpl in *.
  destruct Hin; [ left | right ]; auto. apply IHE; auto.
Qed.

Lemma all_belongs_update_one : forall x xs v E,
  xs ⊂ E ->
  xs ⊂ (E [x <- v]).
Proof.
  intros x xs v E Hin.
  unfold all_belongs in Hin |- *. intros y Hin2.
  apply Hin in Hin2. apply belongs_update_one; auto.
Qed.

Lemma all_belongs_update_one_inv : forall x xs v E,
  xs ⊂ (E [x <- v]) ->
  xs ⊂ E.
Proof.
  intros x xs v E Hin.
  unfold all_belongs in Hin |- *. intros y Hin2.
  apply Hin in Hin2. apply belongs_update_one_inv with x v; auto.
Qed.

Lemma notin_update_one : forall x y v E,
  y ∉ E ->
  y ∉ (E [x <- v]).
Proof.
  intros x y v E Hnotin. unfold notin in *.
  intro Hin. elim Hnotin. apply belongs_update_one_inv with x v; auto.
Qed.

Lemma notin_update_one_inv : forall x y v E,
  y ∉ (E [x <- v]) ->
  y ∉ E.
Proof.
  intros x y v E Hnotin. unfold notin in *.
  intros Hin. elim Hnotin. apply belongs_update_one; auto.
Qed.

Lemma all_notin_update_one : forall x xs v E,
  xs ⊄ E ->
  xs ⊄ (E [x <- v]).
Proof.
  intros x xs v E Hnotin. unfold all_notin in *. intros y Hin.
  apply Hnotin in Hin. apply notin_update_one; auto.
Qed.

Lemma all_notin_update_one_inv : forall x xs v E,
  xs ⊄ (E [x <- v]) ->
  xs ⊄ E.
Proof.
  intros x xs v E Hnotin. unfold all_notin in *. intros y Hin.
  apply Hnotin in Hin. apply notin_update_one_inv with x v; auto.
Qed.

Lemma update_one_notin : forall x v E,
  x ∉ E ->
  E [x <- v] = E.
Proof.
  intros x v E Hnotin. induction E as [ | (y, w) E IHE ]; simpl in *; auto.
  destruct (eq_keys_dec x y) as [ Heq | Hneq ]; subst; simpl in *; auto.
  unfold notin in Hnotin. unfold belongs in Hnotin. simpl in Hnotin.
  elim Hnotin; auto. f_equal; apply IHE.
  assert (x ∉ (E & (y ∶ w))) as Hnotin2 by auto.
  apply notin_concat_inv in Hnotin2. destruct Hnotin2; auto.
Qed.

Lemma map_update_one : forall f x v E,
  map f (E [x <- v]) = (map f E) [x <- f v].
Proof.
  intros f x v E. induction E as [ | (y, w) E IHE ]; simpl in *; auto.
  destruct (eq_keys_dec x y) as [ Heq | Hneq ]; subst; simpl in *; auto.
  f_equal; auto.
Qed.

Lemma ok_update_one : forall x v E,
  ok E ->
  ok (E [x <- v]).
Proof.
  intros x v E Hok. induction E as [ | E y w ] using env_ind.
  rewrite update_one_empty. apply ok_nil.
  inversion Hok as [ | z u F Hok2 ]; subst. destruct Hok2.
  destruct (eq_keys_dec x y) as [ Heq | Hneq ]; subst.
  rewrite update_one_concat_r; [ | apply belongs_single; auto ].
  rewrite update_one_single; auto. apply ok_cons; auto.
  rewrite update_one_concat_l; [ | apply notin_single; auto ].
  apply ok_cons. split; auto. apply notin_update_one; auto.
Qed.

Lemma ok_update_one_inv : forall x v E,
  ok (E [x <- v]) ->
  ok E.
Proof.
  intros x v E Hok. induction E as [ | E y w ] using env_ind.
  apply ok_nil. apply ok_cons.
  destruct (eq_keys_dec x y) as [ Heq | Hneq ]; subst.
  rewrite update_one_concat_r in Hok; [ | apply belongs_single; auto ].
  rewrite update_one_single in Hok; auto.
  inversion Hok as [ | z u F Hok2 ]; subst; auto.
  rewrite update_one_concat_l in Hok; [ | apply notin_single; auto ].
  inversion Hok as [ | z u F Hok2 ]; subst; auto. destruct Hok2.
  split; auto. apply notin_update_one_inv with x v; auto.
Qed.

(* ---------------------------------------------------------------------- *)
(** **** Properties of update *)

Lemma update_empty_r : forall E,
  E ::= (@empty A) = E.
Proof. auto. Qed.

Lemma update_empty_l : forall E,
  (@empty A) ::= E = (@empty A).
Proof.
  induction E as [ | (x, v) E IHE ]; simpl; auto.
  rewrite IHE. auto.
Qed.

Lemma update_update_one : forall x v E,
  E ::= (x ∶ v) = E [x <- v].
Proof. auto. Qed.  

Lemma update_single_single : forall x y v w,
  x = y ->
  (x ∶ v) ::= (y ∶ w) = (x ∶ w). 
Proof. intros; subst. simpl. apply eq_keys_true. Qed.

Lemma update_single_single_neq : forall x y v w,
  x <> y ->
  (x ∶ v) ::= (y ∶ w) = (x ∶ v). 
Proof. intros. simpl. apply eq_keys_false; auto. Qed.

Lemma update_concat_r : forall E F G,
  E ::= (F & G) = (E ::= F) ::= G.
Proof.
  induction G as [ | (x, v) G IHG ]; simpl; auto.
  rewrite IHG. auto.
Qed.

Lemma dom_update : forall E F,
  dom (E ::= F) = dom E.
Proof.
  induction F as [ | (x, v) F IHF ]; simpl in *; auto.
  rewrite dom_update_one, IHF; auto.
Qed.

Lemma belongs_update : forall x E F,
  x ∈ E ->
  x ∈ (E ::= F).
Proof.
  unfold belongs. intros; rewrite dom_update; auto.
Qed.

Lemma belongs_update_inv : forall x E F,
  x ∈ (E ::= F) ->
  x ∈ E.
Proof.
  unfold belongs. intros; rewrite dom_update in * |-; auto.
Qed.

Lemma all_belongs_update : forall xs E F,
  xs ⊂ E ->
  xs ⊂ (E ::= F).
Proof.
  unfold all_belongs; intros xs E F Hincl x Hin.
  apply Hincl in Hin. apply belongs_update; auto.
Qed.

Lemma all_belongs_update_inv : forall xs E F,
  xs ⊂ (E ::= F) ->
  xs ⊂ E.
Proof.
  unfold all_belongs; intros xs E F Hincl x Hin. apply Hincl in Hin.
  apply belongs_update_inv with F; auto.
Qed.

Lemma notin_update : forall x E F,
  x ∉ E ->
  x ∉ (E ::= F).
Proof.
  intros x E F Hnotin Hin. elim Hnotin.
  apply belongs_update_inv with F; auto.
Qed.

Lemma notin_update_inv : forall x E F,
  x ∉ (E ::= F) ->
  x ∉ E.
Proof.
  intros x E F Hnotin Hin. elim Hnotin.
  apply belongs_update; auto.
Qed.

Lemma all_notin_update : forall xs E F,
  xs ⊄ E ->
  xs ⊄ (E ::= F).
Proof.
  intros xs E F Hnotincl. unfold all_notin in *. intros x Hin.
  apply Hnotincl in Hin. apply notin_update; auto.
Qed.

Lemma all_notin_update_inv : forall xs E F,
  xs ⊄ (E ::= F) ->
  xs ⊄ E.
Proof.
  intros xs E F Hnotincl. unfold all_notin in *. intros x Hin.
  apply Hnotincl in Hin. apply notin_update_inv with F; auto.
Qed.

Lemma update_notin : forall E F,
  (dom F) ⊄ E ->
  E ::= F = E.
Proof.
  induction F as [ | (x, v) F IHF ]; unfold all_belongs;
    intro Hdom; simpl in *; auto.
  apply all_notin_notin in Hdom.
  destruct Hdom as [ Hnotin Hdom ].
  apply IHF in Hdom. rewrite Hdom.
  apply update_one_notin; auto.
Qed.

Lemma map_update : forall f E F,
  map f (E ::= F) = (map f E) ::= (map f F).
Proof.
  intros. induction F as [ | (x, v) F IHF ]; simpl; auto.
  rewrite <- IHF. apply map_update_one.
Qed.

Lemma ok_update : forall E F,
  ok E ->
  ok (E ::= F).
Proof.
  intros. induction F as [ | (x, v) F IHF ]; simpl in *; auto. 
  apply ok_update_one; auto.
Qed.

Lemma ok_update_inv : forall E F,
  ok (E ::= F) ->
  ok E.
Proof.
  intros E F Hok. induction F as [ | (x, v) F IHF ]; simpl in *; auto. 
  apply ok_update_one_inv in Hok; auto.
Qed.

(* ---------------------------------------------------------------------- *)
(** **** Properties of remove *)

Lemma remove_empty : forall x,
  (@empty A) ∖ {x} = (@empty A).
Proof. auto. Qed.

Lemma remove_single_eq : forall x y v,
  x = y ->
  (x ∶ v) ∖ {y} = (@empty A).
Proof. intros; subst. simpl. apply eq_keys_true. Qed.

Lemma remove_single_neq : forall x y v,
  x <> y ->
  (x ∶ v) ∖ {y} = (x ∶ v).
Proof. intros. simpl. apply eq_keys_false; auto. Qed.

Lemma remove_notin : forall x E,
  x ∉ E ->
  E ∖ {x} = E.
Proof.
  intros x E Hnotin. induction E as [ | (y, v) E IHE ]; simpl; auto.
  assert (x ∉ E & (y ∶ v)) as Hnotin2 by auto. clear Hnotin.
  apply notin_concat_inv in Hnotin2.
  destruct Hnotin2 as [ Hnotin Hnotin2 ]. apply IHE in Hnotin.
  rewrite Hnotin. apply notin_single_inv in Hnotin2.
  apply eq_keys_false; auto.
Qed.

Lemma notin_remove_notin : forall x y E,
  x ∉ E ->
  x ∉ (E ∖ {y}).
Proof.
  intros x y E Hnotin. induction E as [ | (z, v) E IHE ]; simpl; auto.
  assert (x ∉ E & (z ∶ v)) as Hnotin2 by auto. clear Hnotin.
  apply notin_concat_inv in Hnotin2. destruct Hnotin2 as [ Hnotin Hnotin2 ].
  apply notin_single_inv in Hnotin2.
  destruct (eq_keys_dec y z) as [ Heq | Hneq ]; auto.
  apply IHE in Hnotin.
  assert (x ∉ (E ∖ {y}) & (z ∶ v)); auto.
  apply notin_concat; auto. apply notin_single; auto.
Qed.

Lemma all_notin_remove_notin : forall xs y E,
  xs ⊄ E ->
  xs ⊄ (E ∖ {y}).
Proof.
  intros xs y E Hnotincl. induction xs as [ | x xs IHxs ].
  unfold all_notin. intros x Hin. inversion Hin.
  apply all_notin_notin in Hnotincl.
  destruct Hnotincl as [ Hnotin Hnotincl ].
  apply IHxs in Hnotincl.
  apply notin_all_notin. split; auto.
  apply notin_remove_notin; auto.
Qed.

Lemma belongs_remove : forall x y E,
  x <> y -> x ∈ E ->
  x ∈ (E ∖ {y}).
Proof.
  induction E as [ | (z, v) E IHE ]; intros Hneq Hin; simpl in *; auto.
  assert (x ∈ E & (z ∶ v)) as Hin2 by auto; clear Hin.
  apply belongs_concat_inv in Hin2.
  destruct Hin2 as [ Hin | Hin ];
    destruct (eq_keys_dec y z) as [ Heq | Hneq2 ]; subst; auto.
  assert (x ∈ (E ∖ {y}) & (z ∶ v)) as Hin2; auto.
  apply belongs_concat_l; auto.
  apply belongs_single_inv in Hin. contradiction.
  assert (x ∈ (E ∖ {y}) & (z ∶ v)); auto.
  apply belongs_concat_r; auto.
Qed.

Lemma belongs_remove_inv : forall x y E,
  ok E ->
  x ∈ (E ∖ {y}) -> x <> y.
Proof.
  intros x y E Hok Hbelongs Heq; subst.
  induction E as [ | (x, v) E IHE ]; simpl in *; auto. 
  inversion Hok as [ | z w F Hok2 ]; subst.
  destruct Hok2 as [ Hok2 Hnotin ].
  destruct (eq_keys_dec y x) as [ Heq | Hneq ]; subst. contradiction.
  assert (y ∈ ((E ∖ {y}) & (x ∶ v))) as Hin by auto. clear Hbelongs.
  apply belongs_concat_inv in Hin. destruct Hin as [ | Hin ]; auto.
  apply belongs_single_inv in Hin; auto.
Qed.

Lemma remove_belongs_concat_r : forall x E F,
  x ∈ F ->
  (E & F) ∖ {x} = E & (F ∖ {x}).
Proof.
  intros x E F Hin. induction F as [ | (y, v) F IHF ]; simpl; auto.
  inversion Hin.
  assert (x ∈ F & (y ∶ v)) as Hin2 by auto. clear Hin.
  apply belongs_concat_inv in Hin2. destruct Hin2 as [ Hin | Hin ].
  apply IHF in Hin. rewrite Hin.
  destruct (eq_keys_dec x y); subst; auto.
  apply belongs_single_inv in Hin; subst.
  rewrite ?eq_keys_true; auto.
Qed.

Lemma remove_belongs_concat_l : forall x E F,
  x ∉ F ->
  (E & F) ∖ {x} = (E ∖ {x}) & F.
Proof.
  intros x E F Hnotin. induction F as [ | (y, v) F IHF ]; simpl; auto.
  assert (x ∉ F & (y ∶ v)) as Hnotin2 by auto. clear Hnotin.
  apply notin_concat_inv in Hnotin2. destruct Hnotin2 as [ Hnotin Hnotin2 ].
  apply IHF in Hnotin. rewrite Hnotin.
  destruct (eq_keys_dec x y); subst; auto.
  apply notin_single_inv in Hnotin2. elim Hnotin2; auto.
Qed.  

Lemma remove_ok_notin : forall x E,
  ok E ->
  x ∉ (E ∖ {x}).
Proof.
  intros x E Hok. induction E as [ | (y, v) E IHE]; simpl.
  apply notin_empty. inversion Hok as [ | z w F Hok2 ]; subst.
  destruct Hok2 as [ Hok2 Hnotin ].
  apply IHE in Hok2. destruct (eq_keys_dec x y); subst; auto.
  assert (x ∉ (E ∖ {x}) & y ∶ v); auto.
  apply notin_concat; auto. apply notin_single; auto.
Qed.

Lemma remove_all_belongs : forall x xs F,
  ¬ List.In x xs -> (x :: xs) ⊂ F ->
  xs ⊂ (F ∖ {x}).
Proof.
  intros x xs F Hnotin Hincl. unfold all_belongs in *. intros y Hin.
  simpl in *. apply belongs_remove; auto. intro; subst. contradiction.
Qed.

Lemma remove_map : forall f E x,
  (map f E) ∖ {x} = map f (E ∖ {x}).
Proof.
  intros. induction E as [ | (y, v) E IHE ]; simpl; auto. rewrite IHE.
  destruct (eq_keys_dec x y); auto.
Qed.

Lemma remove_update_one : forall x y v E,
  ok E ->
  (update_one E y v) ∖ {x} = update_one (E ∖ {x}) y v.
Proof.
  intros x y v E Hok. induction E as [ | (z, w) E IHE]; simpl in *; auto.
  inversion Hok as [ | z' w' F Hok2 ]; subst.
  destruct Hok2 as [ Hok2 Hnotin ]. apply IHE in Hok2.

  destruct (eq_keys_dec x z); subst.

  destruct (eq_keys_dec y z); simpl;
    destruct (eq_keys_dec y z); simpl;
      rewrite ?eq_keys_true; subst; try congruence.

  rewrite update_one_notin in *; auto.

  destruct (eq_keys_dec y z); simpl;
    destruct (eq_keys_dec y z); simpl;
      destruct (eq_keys_dec x z); subst; simpl; try congruence.
Qed.

Lemma remove_update : forall x E F,
  ok E ->
  (E ::= F) ∖ {x} = (E ∖ {x}) ::= F.
Proof.
  intros. induction F as [ | (y, v) F IHF ]; simpl; auto.
  rewrite <- IHF. apply remove_update_one.
  apply ok_update; auto.
Qed.

Lemma remove_update_eq : forall x y v E,
  x = y ->
  (E ::= (y ∶ v)) ∖ {x} = E ∖ {x}.
Proof.
  intros; subst. induction E as [ | (y', v') ]; simpl; auto.
  destruct (eq_keys_dec y y'); subst; simpl.
  rewrite eq_keys_true; auto. rewrite eq_keys_false; auto.
  f_equal; auto.
Qed.

Lemma ok_remove : forall x E,
  ok E ->
  ok (E ∖ {x}).
Proof.
  intros x E Hok. induction E as [ | (y, v) E IHE ]; simpl; auto.
  inversion Hok as [ | z w F Hok2 ]; subst.
  destruct Hok2 as [ Hok2 Hnotin ].
  destruct (eq_keys_dec x y); auto.
  apply IHE in Hok2.
  assert (ok ((E ∖ {x}) & (y ∶ v))); auto.
  apply ok_cons. split; auto.
  apply notin_remove_notin; auto.
Qed.

(* ---------------------------------------------------------------------- *)
(** **** Properties of all_remove *)

Lemma all_remove_remove : forall x xs E,
  E ∖ (x :: xs) = (E ∖ {x}) ∖ xs.
Proof. auto. Qed.

Lemma all_remove_empty : forall xs,
  (@empty A) ∖ xs = (@empty A).
Proof. induction xs as [ | x ]; simpl; auto. Qed.

Lemma all_remove_nil : forall E,
  E ∖ nil = E.
Proof. auto. Qed.

Lemma all_remove_single_in : forall x xs v,
  List.In x xs ->
  (x ∶ v) ∖ xs = (@empty A).
Proof.
  intros x xs v; induction xs as [ | y ]; intros Hin;
    simpl in *; auto; inversion Hin; subst.
  rewrite eq_keys_true. apply all_remove_empty.
  destruct (eq_keys_dec y x). apply all_remove_empty. auto.
Qed.

Lemma all_remove_single_not_in : forall x xs v,
  ¬ List.In x xs ->
  (x ∶ v) ∖ xs = (x ∶ v).
Proof.
  intros x xs v Hnotin. induction xs as [ | y xs IHxs ]; simpl; auto.
  assert (x ≠ y ∧ ¬In x xs) as Hyp by
    (split; intro Hyp; apply Hnotin;
      [ rewrite Hyp; apply in_eq | apply in_cons; auto ]).
  destruct Hyp as [ Hneq Hnotin2 ]. apply IHxs in Hnotin2.
  rewrite <- Hnotin2. f_equal.
  apply eq_keys_false; auto.
Qed.

Lemma all_remove_singles_in : forall xs ys vs,
  xs = ys -> length xs = length vs ->
  (xs ∷ vs) ∖ ys = (@empty A).
Proof.
  intros xs vs ys Heq; subst.
  generalize vs. clear vs.
  induction ys as [ | y ]; induction vs as [ | v ];
    intro Hlen; simpl in *; auto.
  inversion Hlen. rewrite eq_keys_true; auto.
Qed.

Lemma all_remove_singles_not_in : forall xs ys vs,
  List.Forall (fun x => ¬ List.In x xs) ys ->
  (xs ∷ vs) ∖ ys = (xs ∷ vs).
Proof.
  intros xs ys vs Hyp. induction ys as [ | y ]; simpl; auto. inversion Hyp.
  rewrite remove_notin; auto. apply notin_singles; auto.
Qed.

Lemma all_remove_notin : forall xs E,
  xs ⊄ E ->
  E ∖ xs = E.
Proof.
  intros xs E Hnotincl. induction xs as [ | x ]; simpl; auto.
  apply all_notin_notin in Hnotincl. destruct Hnotincl.
  rewrite remove_notin; auto.
Qed.

Lemma notin_all_remove_notin : forall x ys E,
  x ∉ E ->
  x ∉ (E ∖ ys).
Proof.
  induction ys as [ | y ]; simpl; auto.
  intros.
  assert (x ∉ E ∖ {y}) by (apply notin_remove_notin; auto).
  auto.
Qed.

Lemma all_notin_all_remove_notin : forall xs ys E,
  xs ⊄ E ->
  xs ⊄ (E ∖ ys).
Proof.
  induction ys as [ | y ]; simpl; auto.
  intros.
  assert (xs ⊄ E ∖ {y}) by (apply all_notin_remove_notin; auto).
  auto.
Qed.

Lemma all_remove_ok_notin : forall xs E,
  ok E ->
  xs ⊄ (E ∖ xs).
Proof.
  induction xs as [ | x xs IHxs ]; intros E Hok; simpl.
  unfold all_notin. intros x Hin. inversion Hin.
  apply notin_all_notin. split.
  apply notin_all_remove_notin. apply remove_ok_notin; auto.
  apply IHxs. apply ok_remove; auto.
Qed.

Lemma all_remove_belongs_concat_r : forall xs E F,
  List.NoDup xs ->
  xs ⊂ F ->
  (E & F) ∖ xs = E & (F ∖ xs).
Proof.
  induction xs as [ | x xs IHxs ]; intros E F Hnodup Hincl; simpl; auto.
  inversion Hnodup.
  rewrite remove_belongs_concat_r; auto.
  rewrite IHxs; auto.
  apply remove_all_belongs; auto.
  apply all_belongs_belongs in Hincl. destruct Hincl; auto.
Qed.

Lemma all_remove_belongs_concat_l : forall xs E F,
  xs ⊄ F ->
  (E & F) ∖ xs = (E ∖ xs) & F.
Proof.
  induction xs as [ | x ]; intros E F Hnotincl; simpl; auto.
  apply all_notin_notin in Hnotincl. destruct Hnotincl.
  rewrite remove_belongs_concat_l; auto.
Qed.

Lemma all_remove_map : forall f E xs,
  (map f E) ∖ xs = map f (E ∖ xs).
Proof.
  intros f E xs. generalize E.
  induction xs as [ | x ]; intros; simpl; auto.
  rewrite remove_map. auto.
Qed.

Lemma all_remove_update : forall xs E F,
  ok E ->
  (E ::= F) ∖ xs = (E ∖ xs) ::= F.
Proof.
  intros xs E F. generalize E. clear E.
  induction xs as [ | x xs IHxs ]; intros; simpl; auto.
  rewrite remove_update; auto. apply IHxs. apply ok_remove; auto.
Qed.

Lemma ok_all_remove : forall xs E,
  ok E ->
  ok (E ∖ xs).
Proof.
  induction xs as [ | x ]; intros E Hok; simpl in *; auto.
  assert (ok (E ∖ {x})). apply ok_remove; auto. auto.
Qed.

(* ---------------------------------------------------------------------- *)
(** **** Properties of ok *)

Lemma ok_empty :
  ok (@empty A).
Proof. apply ok_nil. Qed.

Lemma ok_single : forall x v,
  ok (x ∶ v).
Proof.
  intros. rewrite <- concat_empty_l. apply ok_cons.
  split; [ apply ok_nil | ]; auto. apply notin_empty.
Qed.

Lemma ok_singles : forall xs vs,
  List.NoDup xs ->
  ok (xs ∷ vs).
Proof.
  induction xs as [ | x xs IHxs ]; induction vs as [ | v vs IHvs ];
    intro Hnodup; simpl in *; auto.
  apply ok_nil. apply ok_nil.
  assert (ok ((xs ∷ vs) & (x ∶ v))); auto.
  apply ok_cons.
  assert (List.NoDup xs ∧ ¬ List.In x xs) as Hdup by
    (rewrite <- List.app_nil_l in Hnodup; split;
      [ apply List.NoDup_remove_1 in Hnodup
        | apply List.NoDup_remove_2 in Hnodup ];
      auto). destruct Hdup as [ Hnodup2 Hnotin ].
  apply IHxs with vs in Hnodup2.
  split; auto.
  unfold belongs. 
  assert (forall x l l', ¬ List.In x l' -> List.incl l l' -> ¬ List.In x l)
    as Hincl by auto.
  apply Hincl with xs; auto.
  apply dom_singles_incl.
Qed.

Lemma ok_singles_inv : forall xs vs,
  length xs = length vs ->
  ok (xs ∷ vs) ->
  List.NoDup xs.
Proof.
  induction xs as [ | x xs IHxs ]; induction vs as [ | v vs IHvs ];
    intros Hlen Hok; auto.
  apply List.NoDup_nil. apply List.NoDup_nil. inversion Hlen.
  inversion Hlen as [ Hlen2 ]. inversion Hok as [ | y w F Hok2 ]; subst.
  destruct Hok2 as [ Hok3 Hnotin ].
  apply (IHxs vs) in Hok3; auto.
  unfold notin, belongs in Hnotin. rewrite dom_singles in Hnotin; auto.
  apply List.NoDup_cons; auto.
Qed.

Lemma ok_concat : forall E F,
  ok E -> ok F ->
  (dom E) ⊄ F -> (dom F) ⊄ E ->
  ok (E & F).
Proof.
  intros E F HokE HokF HdomE HdomF.
  induction F as [ | (x, v) F IHF ]; simpl in *; auto.
  apply all_notin_notin in HdomF. destruct HdomF as [ HnotinE HdomF ].
  inversion HokF as [ | y w G HokF2 ]; subst.
  destruct HokF2 as [ HokF2 HnotinF ].
  assert (dom E ⊄ F & x ∶ v) as HdomE2 by auto. clear HdomE.
  apply all_notin_concat_inv in HdomE2. destruct HdomE2 as [ HdomE HdomE2 ].
  apply all_notin_single_inv in HdomE2.
  assert (ok ((E & F) & (x ∶ v))); auto.
  apply ok_cons.
  split. apply IHF; auto. apply notin_concat; auto.
Qed.

Lemma ok_concat_inv : forall E F,
  ok (E & F) ->
  ok E ∧ ok F ∧ (dom E) ⊄ F ∧ (dom F) ⊄ E.
Proof.
  intros E F Hok.
  induction F as [ | (x, v) F IHF ]; simpl in *.
  split; auto. split. apply ok_empty.
  split. apply all_notin_empty_r.
  unfold all_notin; intros; contradiction.
  inversion Hok as [ | y w G Hok2]; subst. destruct Hok2 as [ Hok2 Hnotin ].  apply IHF in Hok2. destruct Hok2 as [ HokE [ HokF [ HdomE HdomF ] ] ].
  apply notin_concat_inv in Hnotin. destruct Hnotin as [ HnotinE HnotinF ].
  split; auto. split. assert (ok (F & x ∶ v)); auto.
  apply ok_cons. split; auto.

  split. assert (dom E ⊄ F & x ∶ v); auto. apply all_notin_concat; auto.
  unfold all_notin. intros. apply notin_single. intro; subst.
  contradiction.

  unfold all_notin in *. intros y Hin. simpl in Hin.
  destruct Hin; subst; auto.
Qed.

Lemma ok_concat_comm : forall E F,
  ok (E & F) ->
  ok (F & E).
Proof.
  intros E F Hok. apply ok_concat_inv in Hok.
  destruct Hok as [ HokE [ HokF [ HdomE HdomF ] ] ].
  apply ok_concat; auto.
Qed.

Lemma belongs_ok_concat_inv_l : forall x F G,
  ok (F & G) ->
  x ∈ F ->
  x ∉ G.
Proof.
  intros x F G Hok HinF. apply ok_concat_inv in Hok.
  destruct Hok as [ HokE [ HokF [ HdomE HdomF ] ] ].
  unfold all_notin, notin, belongs in *; auto.
Qed.

Lemma belongs_ok_concat_inv_r : forall x F G,
  ok (F & G) ->
  x ∈ G ->
  x ∉ F.
Proof.
  intros x F G Hok HinG. apply ok_concat_inv in Hok.
  destruct Hok as [ HokE [ HokF [ HdomE HdomF ] ] ].
  unfold all_notin, notin, belongs in *; auto.
Qed.

Lemma concat_not_ok : forall x F G,
  x ∈ F -> x ∈ G ->
  ¬ ok (F & G).
Proof.
  intros x F G HinF HinG Hok.
  apply (belongs_ok_concat_inv_r x F G) in Hok; auto.
Qed.

(** Additional properties when ok stands. *)

(** Update commutes with concatenation on the left. *)
Lemma update_one_concat_ok : forall E F x v,
  ok (E & F) ->
  (E & F) [x <- v] =
  (E [x <- v]) & (F [x <- v]).
Proof.
  intros E F x v Hok. induction F as [ | (y, w) F IHF ]; simpl in *; auto.
  inversion Hok as [ | z w' G Hok2 ]; subst.
  destruct Hok2 as [ Hok2 Hnotin ]. rewrite IHF; auto.
  destruct (eq_keys_dec x y); subst; simpl; auto.
  rewrite update_one_notin; auto.
  apply notin_concat_inv in Hnotin. destruct Hnotin; auto.
Qed.

Lemma update_concat_l : forall E F G,
  ok (E & F) ->
  (E & F) ::= G = (E ::= G) & (F ::= G).
Proof.
  intros E F G Hok. induction G as [ | (x, v) G IHG ]; simpl in *; auto.
  rewrite IHG. apply update_one_concat_ok.
  apply ok_concat_inv in Hok.
  destruct Hok as [ HokE [ HokF [ HdomE HdomF ] ] ].
  assert (ok (E ::= G)) by (apply ok_update; auto).
  assert (ok (F ::= G)) by (apply ok_update; auto).
  apply ok_concat; auto; rewrite dom_update; apply all_notin_update; auto.
Qed.

End Properties.

End CoreGenericEnvListDef.

(** * Instantiation of Generic_Env with this implementation. *)
Require Import CoreGenericEnv GenericEnv.

(** Application of Core functor. *)
Module CoreGenericEnvList (VarType : UsualDecidableType)
  : CoreGenericEnvironmentType VarType
  := CoreGenericEnvListDef VarType.

(** Extension of core implementation with the Extension functor. *)
Module GenericEnvironmentAsList (VarType : UsualDecidableType).
  Module Core := CoreGenericEnvList VarType.
  Module Ext := GenericEnvironmentType VarType Core.
  Import Ext.
End GenericEnvironmentAsList.
