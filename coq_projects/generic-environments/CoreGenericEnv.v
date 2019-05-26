(***************************************************************************
* Core Generic Environments                                                *
*                                                                          *
* Emmanuel Polonowski, April 2011, Coq v8.3                                *
*                                                                          *
* (Inspired by the work of A. Chargueraud :                                *
*  http://www.chargueraud.org/softs/ln/index.php)                          *
***************************************************************************)

Require Import Utf8.
Set Implicit Arguments.

(* ********************************************************************** *)
(** * Module Type of an implementation of environments                    *)

Require Import Equalities.
Require Import List.

Module Type CoreGenericEnvironmentType (VarType : UsualDecidableType).

Import VarType.

Definition TVar := VarType.t.

(* ---------------------------------------------------------------------- *)
(** ** Definitions and Notations *)

(** gen_env A is an environment that binds variables to values of type A. *)
Parameter gen_env : Type -> Type.

Section CoreDefinitions.

Variable A B : Type.

(** The decidability of equality on keys (variables) is imported from Var.*)
Definition eq_keys_dec := VarType.eq_dec.

(** Empty environment. *)
Parameter empty : gen_env A.

(** Environment build upon explicit associations. *)
Parameter single : TVar -> A -> gen_env A.
Parameter singles : list TVar -> list A -> gen_env A.

(** Concatenation of environment (the second one binds first). *)
Parameter concat : gen_env A -> gen_env A -> gen_env A.

(** The main operation on environment, get the type of a variable. *)
Parameter get : TVar -> gen_env A -> option A.

(** Domain and image of an environment. *)
Parameter dom : gen_env A -> list TVar.
Parameter img : gen_env A -> list A.

(** Check the occurence of variable(s) in an environment. *)
Axiom belongs : TVar -> gen_env A -> Prop.
Axiom all_belongs : list TVar -> gen_env A -> Prop.

(** Check the non-occurence of variable(s) in an environment. *)
Axiom notin  : TVar -> gen_env A -> Prop.
Axiom all_notin : list TVar -> gen_env A -> Prop.

(** Map function on types. *)
Parameter map : (A -> B) -> gen_env A -> gen_env B.

(** Updating of types with bindings of another environment. *)
Parameter update_one : gen_env A -> TVar -> A -> gen_env A.
Parameter update : gen_env A -> gen_env A -> gen_env A.

(** Remove a binding from an environment. *)
Parameter remove : TVar -> gen_env A -> gen_env A.
Parameter all_remove : list TVar -> gen_env A -> gen_env A.

(** The ok predicate states that the bindings are pairwise distinct,
   i.e. each variable appears only once. *)
Inductive ok : gen_env A -> Prop :=
| ok_nil : ok empty
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
Implicit Types x y : TVar.
Implicit Types xs ys : list TVar.

(* ---------------------------------------------------------------------- *)
(** *** Primary properties *)

(** Induction scheme over environments. *)
Axiom env_ind : forall A, forall P : gen_env A -> Prop,
  (P (@empty A)) ->
  (forall (E : gen_env A) x (v : A), P E -> P (E & (x ∶ v))) ->
  (forall (E : gen_env A), P E).

(* ---------------------------------------------------------------------- *)
(** **** Properties of singulars *)

(** Environment built from lists. *)
Axiom singles_empty : forall A,
  nil ∷ nil = (@empty A).
Axiom singles_cons : forall A x xs (v : A) (vs : list A),
  (x :: xs) ∷ (v :: vs) = (xs ∷ vs) & (x ∶ v).

(* ---------------------------------------------------------------------- *)
(** **** Properties of concatenation *)

(** Concatenation admits empty as neutral element, and is associative. *)
Axiom concat_empty_r : forall A (E : gen_env A),
  E & (@empty A) = E.
Axiom concat_empty_l : forall A (E : gen_env A),
  (@empty A) & E = E.
Axiom concat_assoc : forall A (E F G : gen_env A),
  E & (F & G) = (E & F) & G.

(* ---------------------------------------------------------------------- *)
(** **** Properties of get *)

(** Get is None on empty. *)
Axiom get_empty : forall A x,
  get x (@empty A) = None.

(** Get is Some when it binds. *)
Axiom get_single_eq : forall A x y (v : A),
  x = y ->
  get x (y ∶ v) = Some v.
Axiom get_single_eq_inv : forall A x y (v w : A),
  get x (y ∶ w) = Some v ->
  x = y /\ v = w.

(** Get is decidable. *)
Axiom get_dec : forall A x (E : gen_env A),
   { v : A | get x E = Some v } + { get x E = None }.

(** Get and concatenation. *)
Axiom get_concat_r : forall A x y (v : A) (E : gen_env A),
  x = y ->
  get x (E & (y ∶ v)) = Some v.
Axiom get_concat_l : forall A x y (v : A) (E : gen_env A),
  x <> y ->
  get x (E & (y ∶ v)) = get x E.
Axiom get_concat_inv : forall A x y (v w : A) (E : gen_env A),
  get x (E & (y ∶ v)) = Some w ->
  (x = y /\ v = w) \/ (x <> y /\ get x E = Some w).

(* ---------------------------------------------------------------------- *)
(** **** Properties of dom *)

(** Dom builds a list. *)
Axiom dom_empty : forall A,
  dom (@empty A) = nil.
Axiom dom_empty_inv : forall A (E : gen_env A),
  dom (E) = nil ->
  E = (@empty A).
Axiom dom_single : forall A x (v : A),
  dom (x ∶ v) = (x :: nil).
Axiom dom_singles : forall A xs (vs : list A),
  length xs = length vs ->
  dom (xs ∷ vs) = xs.
Axiom dom_singles_incl : forall A xs (vs : list A),
  List.incl (dom (xs ∷ vs)) xs.
Axiom dom_concat : forall A (E F : gen_env A),
  dom (E & F) = List.app (dom F) (dom E).

(* ---------------------------------------------------------------------- *)
(** **** Properties of img *)

(** Img builds a list. *)
Axiom img_empty : forall A,
  img (@empty A) = nil.
Axiom img_empty_inv : forall A (E : gen_env A),
  img (E) = nil ->
  E = (@empty A).
Axiom img_single : forall A x (v : A),
  img (x ∶ v) = v :: nil.
Axiom img_singles : forall A xs (vs : list A),
  length xs = length vs ->
  img (xs ∷ vs) = vs.
Axiom img_singles_incl : forall A xs (vs : list A),
  List.incl (img (xs ∷ vs)) vs.
Axiom img_concat : forall A (E F : gen_env A),
  img (E & F) = List.app (img F) (img E).

(** Dom and img builds identity. *)
Axiom dom_img_id : forall A (E : gen_env A),
  (dom E) ∷ (img E) = E.
Axiom length_dom_img_eq : forall A (E : gen_env A),
  length (dom E) = length (img E).

(* ---------------------------------------------------------------------- *)
(** **** Properties of belongs *)

(** Belongs is false on empty environments. *)
Axiom belongs_empty : forall A x,
  x ∈ (@empty A) ->
  False.

(** Belongs in singular(s). *)
Axiom belongs_single : forall A x y (v : A),
  x = y ->
  x ∈ (y ∶ v).
Axiom belongs_single_inv : forall A x y (v : A),
  x ∈ (y ∶ v) ->
  x = y.
Axiom belongs_singles : forall A x xs (vs : list A),
  length xs = length vs ->
  List.In x xs ->
  x ∈ (xs ∷ vs).
Axiom belongs_singles_inv : forall A x xs (vs : list A),
  length xs = length vs ->
  x ∈ (xs ∷ vs) ->
  List.In x xs.

(** Belongs and concatenation. *)
Axiom belongs_concat_l : forall A x (F G : gen_env A),
  x ∈ F ->
  x ∈ (F & G).
Axiom belongs_concat_r : forall A x (F G : gen_env A),
  x ∈ F ->
  x ∈ (G & F).
Axiom belongs_concat_inv : forall A x (F G : gen_env A),
  x ∈ (F & G) ->
  x ∈ F ∨ x ∈ G.

(** Belongs and dom. *)
Axiom belongs_dom : forall A x (E : gen_env A),
  x ∈ E ->
  List.In x (dom E).
Axiom belongs_dom_inv : forall A x (E : gen_env A),
  List.In x (dom E) ->
  x ∈ E.

(* ---------------------------------------------------------------------- *)
(** **** Properties of all_belongs *)

(** All_belongs and belongs. *)
Axiom all_belongs_def : forall A xs (E : gen_env A),
  (forall x, List.In x xs -> x ∈ E) ->
  xs ⊂ E.
Axiom all_belongs_def_inv : forall A xs (E : gen_env A),
  xs ⊂ E ->
  (forall x, List.In x xs -> x ∈ E).
Axiom all_belongs_belongs : forall A x xs (E : gen_env A),
  (x :: xs) ⊂ E ->
  x ∈ E ∧ xs ⊂ E.
Axiom belongs_all_belongs : forall A x xs (E : gen_env A),
  x ∈ E ∧ xs ⊂ E ->
  (x :: xs) ⊂ E.

(** All_belongs is false on empty environments. *)
Axiom all_belongs_empty : forall A xs,
  xs ⊂ (@empty A) ->
  xs = nil.
Axiom all_belongs_nil : forall A (E : gen_env A),
  nil ⊂ E.

(** All_belongs in singular(s). *)
Axiom all_belongs_single : forall A xs y (v : A),
  xs = y :: nil ->
  xs ⊂ (y ∶ v).
Axiom all_belongs_single_inv : forall A xs y (v : A),
  length xs = 1 ->
  xs ⊂ (y ∶ v) ->
  xs = y :: nil.
Axiom all_belongs_singles : forall A xs ys (vs : list A),
  length ys = length vs ->
  List.incl xs ys ->
  xs ⊂ (ys ∷ vs).
Axiom all_belongs_singles_inv : forall A xs ys (vs : list A),
  xs ⊂ (ys ∷ vs) ->
  List.incl xs ys.

(** All_belongs and concatenation. *)
Axiom all_belongs_concat_l : forall A xs (F G : gen_env A),
  xs ⊂ F ->
  xs ⊂ (F & G).
Axiom all_belongs_concat_r : forall A xs (F G : gen_env A),
  xs ⊂ F ->
  xs ⊂ (G & F).

(** All_belongs and dom. *)
Axiom all_belongs_dom : forall A xs (E : gen_env A),
  xs ⊂ E ->
  List.incl xs (dom E).
Axiom all_belongs_dom_inv : forall A xs (E F : gen_env A),
  List.incl xs (dom E) ->
  xs ⊂ E.

(* ---------------------------------------------------------------------- *)
(** **** Properties of notin *)

(** Notin and belongs. *)
Axiom notin_belongs : forall A x (E : gen_env A),
  x ∉ E ->
  ¬ x ∈ E.
Axiom belongs_notin : forall A x (E : gen_env A),
  x ∈ E ->
  ¬ x ∉ E.
Axiom not_belongs_notin : forall A x (E : gen_env A),
  ¬ x ∈ E ->
  x ∉ E.
Axiom notin_belongs_neq : forall A x y (E : gen_env A),
  x ∈ E -> y ∉ E ->
  x <> y.

(** Notin is true on empty environments. *)
Axiom notin_empty : forall A x,
  x ∉ (@empty A).

(** Notin in singular(s). *)
Axiom notin_single : forall A x y (v : A),
  x <> y ->
  x ∉ (y ∶ v).
Axiom notin_single_inv : forall A x y (v : A),
  x ∉ (y ∶ v) ->
  x <> y.
Axiom notin_singles : forall A x xs (vs : list A),
  ¬ List.In x xs ->
  x ∉ (xs ∷ vs).
Axiom notin_singles_inv : forall A x xs (vs : list A),
  length xs = length vs ->
  x ∉ (xs ∷ vs) ->
  ¬ List.In x xs.

(** Notin and concatenation. *)
Axiom notin_concat : forall A x (F G : gen_env A),
  x ∉ F -> x ∉ G ->
  x ∉ (F & G).
Axiom notin_concat_inv : forall A x (F G : gen_env A),
  x ∉ (F & G) ->
  x ∉ F ∧ x ∉ G.

(** Notin and dom. *)
Axiom notin_dom : forall A x (E : gen_env A),
  x ∉ E ->
  ¬ List.In x (dom E).
Axiom notin_dom_inv : forall A x (E F : gen_env A),
  ¬ List.In x (dom E) ->
  x ∉ E.

(* ---------------------------------------------------------------------- *)
(** **** Properties of all_notin *)

(** All_notin is true on empty lists. *)
Axiom all_notin_empty_l : forall A (E : gen_env A),
  nil ⊄ E.

(** All_notin and notin. *)
Axiom all_notin_def : forall A xs (E : gen_env A),
  (forall x, List.In x xs -> x ∉ E) ->
  xs ⊄ E.
Axiom all_notin_def_inv : forall A xs (E : gen_env A),
  xs ⊄ E ->
  (forall x, List.In x xs -> x ∉ E).
Axiom all_notin_notin : forall A x xs (E : gen_env A),
  (x :: xs) ⊄ E ->
  x ∉ E ∧ xs ⊄ E.
Axiom notin_all_notin : forall A x xs (E : gen_env A),
  x ∉ E ∧ xs ⊄ E ->
  (x :: xs) ⊄ E.

(** All_notin and belongs. *)
Axiom all_notin_belongs_neq : forall A x ys (E : gen_env A),
  x ∈ E -> ys ⊄ E ->
  ¬ List.In x ys.

(** All_notin is true on empty environments. *)
Axiom all_notin_empty_r : forall A xs,
  xs ⊄ (@empty A).

(** All_notin in singular(s). *)
Axiom all_notin_single : forall A xs y (v : A),
  ¬ List.In y xs ->
  xs ⊄ (y ∶ v).
Axiom all_notin_single_inv : forall A xs y (v : A),
  xs ⊄ (y ∶ v) ->
  ¬ List.In y xs.
Axiom all_notin_singles : forall A xs ys (vs : list A),
  List.Forall (fun x => ¬ List.In x ys) xs ->
  xs ⊄ (ys ∷ vs).
Axiom all_notin_singles_inv : forall A xs ys (vs : list A),
  length ys = length vs ->
  xs ⊄ (ys ∷ vs) ->
  List.Forall (fun x => ¬ List.In x ys) xs.

(** All_notin and concatenation. *)
Axiom all_notin_concat : forall A xs (F G : gen_env A),
  xs ⊄ F -> xs ⊄ G ->
  xs ⊄ (F & G).
Axiom all_notin_concat_inv : forall A xs (F G : gen_env A),
  xs ⊄ (F & G) ->
  xs ⊄ F ∧ xs ⊄ G.

(** All_notin and dom. *)
Axiom all_notin_dom : forall A xs (E : gen_env A),
  xs ⊄ E ->
  List.Forall (fun x => ¬ List.In x (dom E)) xs.
Axiom all_notin_dom_inv : forall A xs (E : gen_env A),
  List.Forall (fun x => ¬ List.In x (dom E)) xs ->
  xs ⊄ E.

(* ---------------------------------------------------------------------- *)
(** **** Properties of map *)

(** Map is applied on type(s). *)
Axiom map_empty : forall A B (f : A -> B),
  map f (@empty A) = (@empty B).
Axiom map_single : forall A B (f : A -> B) x (v : A),
  map f (x ∶ v) = x ∶ (f v).
Axiom map_singles : forall A B (f : A -> B) xs (vs : list A),
  map f (xs ∷ vs) = xs ∷ (List.map f vs).

(** Map commutes with concatenation. *)
Axiom map_concat : forall A B (f : A -> B) (E F : gen_env A),
  map f (E & F) = (map f E) & (map f F).

(** Dom is unchanged by map. *)
Axiom dom_map : forall A B (E : gen_env A) (f : A -> B),
  dom (map f E) = dom E.

(** Belongs commutes with map. *)
Axiom belongs_map : forall A B x (E : gen_env A) (f : A -> B),
  x ∈ E ->
  x ∈ (map f E).
Axiom belongs_map_inv : forall A B x (E : gen_env A) (f : A -> B),
  x ∈ (map f E) ->
  x ∈ E.

(** All_belongs commutes with map. *)
Axiom all_belongs_map : forall A B xs (E : gen_env A) (f : A -> B),
  xs ⊂ E ->
  xs ⊂ (map f E).
Axiom all_belongs_map_inv : forall A B xs (E : gen_env A) (f : A -> B),
  xs ⊂ (map f E) ->
  xs ⊂ E.

(** Notin commutes with map. *)
Axiom notin_map : forall A B x (E : gen_env A) (f : A -> B),
  x ∉ E ->
  x ∉ (map f E).
Axiom notin_map_inv : forall A B x (E : gen_env A) (f : A -> B),
  x ∉ (map f E) ->
  x ∉ E.

(** All_notin commutes with map. *)
Axiom all_notin_map : forall A B xs (E : gen_env A) (f : A -> B),
  xs ⊄ E ->
  xs ⊄ (map f E).
Axiom all_notin_map_inv : forall A B xs (E : gen_env A) (f : A -> B),
  xs ⊄ (map f E) ->
  xs ⊄ E.

(** Ok commutes with map. *)
Axiom ok_map : forall A B (E : gen_env A) (f : A -> B),
  ok E ->
  ok (map f E).
Axiom ok_map_inv : forall A B (E : gen_env A) (f : A -> B),
  ok (map f E) ->
  ok E.

(* ---------------------------------------------------------------------- *)
(** **** Properties of update_one *)

(** Update_one is identity on empty environments. *)
Axiom update_one_empty : forall A x (v : A),
  (@empty A) [x <- v] = (@empty A).

(** Update_one with single. *)
Axiom update_one_single : forall A x y (v w : A),
  x = y ->
  (x ∶ v) [y <- w] = (x ∶ w).
Axiom update_one_single_neq : forall A x y (v w : A),
  x <> y ->
  (x ∶ v) [y <- w] = (x ∶ v).

(** Update_one and  concatenation. *)
Axiom update_one_concat_r : forall A x (v : A) (E F : gen_env A),
  x ∈ F ->
  (E & F) [x <- v] = E & (F [x <- v]).
Axiom update_one_concat_l : forall A x (v : A) (E F : gen_env A),
  x ∉ F ->
  (E & F) [x <- v] = (E [x <- v]) & F.

(** Dom is unchanged by updating. *)
Axiom dom_update_one : forall A x (v : A) (E : gen_env A),
  dom (E [x <- v]) = dom E.

(** Belongs commutes with update. *)
Axiom belongs_update_one : forall A x y (v : A) (E : gen_env A),
  y ∈ E ->
  y ∈ (E [x <- v]).
Axiom belongs_update_one_inv : forall A x y (v : A) (E : gen_env A),
  y ∈ (E [x <- v]) ->
  y ∈ E.

(** All_belongs commutes with update. *)
Axiom all_belongs_update_one : forall A x xs (v : A) (E : gen_env A),
  xs ⊂ E ->
  xs ⊂ (E [x <- v]).
Axiom all_belongs_update_one_inv : forall A x xs (v : A) (E : gen_env A),
  xs ⊂ (E [x <- v]) ->
  xs ⊂ E.

(** Notin commutes with update. *)
Axiom notin_update_one : forall A x y (v : A) (E : gen_env A),
  y ∉ E ->
  y ∉ (E [x <- v]).
Axiom notin_update_one_inv : forall A x y (v : A) (E : gen_env A),
  y ∉ (E [x <- v]) ->
  y ∉ E.

(** All_notin commutes with update. *)
Axiom all_notin_update_one : forall A x xs (v : A) (E : gen_env A),
  xs ⊄ E ->
  xs ⊄ (E [x <- v]).
Axiom all_notin_update_one_inv : forall A x xs (v : A) (E : gen_env A),
  xs ⊄ (E [x <- v]) ->
  xs ⊄ E.

(** Update is identity when the domains are disjoints. *)
Axiom update_one_notin : forall A x (v : A) (E : gen_env A),
  x ∉ E ->
  E [x <- v] = E.

(** Update commutes with map. *)
Axiom map_update_one : forall A B (f : A -> B) x (v : A) (E : gen_env A),
  map f (E [x <- v]) = (map f E) [x <- f v].

(** Ok commutes with update. *)
Axiom ok_update_one : forall A x (v : A) (E : gen_env A),
  ok E ->
  ok (E [x <- v]).
Axiom ok_update_one_inv : forall A x (v : A) (E : gen_env A),
  ok (E [x <- v]) ->
  ok E.

(* ---------------------------------------------------------------------- *)
(** **** Properties of update *)

(** Update is identity in presence of empty environments. *)
Axiom update_empty_r : forall A (E : gen_env A),
  E ::= (@empty A) = E.
Axiom update_empty_l : forall A (E : gen_env A),
  (@empty A) ::= E = (@empty A).

(** Update with single. *)
Axiom update_update_one : forall A x (v : A) (E : gen_env A),
  E ::= (x ∶ v) = E [x <- v].
Axiom update_single_single : forall A x y (v w : A),
  x = y ->
  (x ∶ v) ::= (y ∶ w) = (x ∶ w).
Axiom update_single_single_neq : forall A x y (v w : A),
  x <> y ->
  (x ∶ v) ::= (y ∶ w) = (x ∶ v).

(** Update commutes with concatenation on the right. *)
Axiom update_concat_r : forall A (E F G : gen_env A),
  E ::= (F & G) = (E ::= F) ::= G.

(** Dom is unchanged by updating. *)
Axiom dom_update : forall A (E F : gen_env A),
  dom (E ::= F) = dom E.

(** Belongs commutes with update. *)
Axiom belongs_update : forall A x (E F : gen_env A),
  x ∈ E ->
  x ∈ (E ::= F).
Axiom belongs_update_inv : forall A x (E F : gen_env A),
  x ∈ (E ::= F) ->
  x ∈ E.

(** All_belongs commutes with update. *)
Axiom all_belongs_update : forall A xs (E F : gen_env A),
  xs ⊂ E ->
  xs ⊂ (E ::= F).
Axiom all_belongs_update_inv : forall A xs (E F : gen_env A),
  xs ⊂ (E ::= F) ->
  xs ⊂ E.

(** Notin commutes with update. *)
Axiom notin_update : forall A x (E F : gen_env A),
  x ∉ E ->
  x ∉ (E ::= F).
Axiom notin_update_inv : forall A x (E F : gen_env A),
  x ∉ (E ::= F) ->
  x ∉ E.

(** All_notin commutes with update. *)
Axiom all_notin_update : forall A xs (E F : gen_env A),
  xs ⊄ E ->
  xs ⊄ (E ::= F).
Axiom all_notin_update_inv : forall A xs (E F : gen_env A),
  xs ⊄ (E ::= F) ->
  xs ⊄ E.

(** Update is identity when the domains are disjoints. *)
Axiom update_notin : forall A (E F : gen_env A),
  (dom F) ⊄ E ->
  E ::= F = E.

(** Update commutes with map. *)
Axiom map_update : forall A B (f : A -> B) (E F : gen_env A),
  map f (E ::= F) = (map f E) ::= (map f F).

(** Ok commutes with update. *)
Axiom ok_update : forall A (E F : gen_env A),
  ok E ->
  ok (E ::= F).
Axiom ok_update_inv : forall A (E F : gen_env A),
  ok (E ::= F) ->
  ok E.

(* ---------------------------------------------------------------------- *)
(** **** Properties of remove *)

(** Remove is identity on empty environments. *)
Axiom remove_empty : forall A x,
  (@empty A) ∖ {x} = (@empty A).

(** Remove on singular. *)
Axiom remove_single_eq : forall A x y (v : A),
  x = y ->
  (x ∶ v) ∖ {y} = (@empty A).
Axiom remove_single_neq : forall A x y (v : A),
  x <> y ->
  (x ∶ v) ∖ {y} = (x ∶ v).

(** Remove and notin and belongs. *)
Axiom remove_notin : forall A x (E : gen_env A),
  x ∉ E ->
  E ∖ {x} = E.
Axiom notin_remove_notin : forall A x y (E : gen_env A),
  x ∉ E ->
  x ∉ (E ∖ {y}).
Axiom all_notin_remove_notin : forall A xs y (E : gen_env A),
  xs ⊄ E ->
  xs ⊄ (E ∖ {y}).
Axiom belongs_remove : forall A x y (E : gen_env A),
  x <> y -> x ∈ E ->
  x ∈ (E ∖ {y}).
Axiom belongs_remove_inv : forall A x y (E : gen_env A),
  ok E ->
  x ∈ (E ∖ {y}) -> x <> y.

(** Remove and concatenation. *)
Axiom remove_belongs_concat_r : forall A x (E F : gen_env A),
  x ∈ F ->
  (E & F) ∖ {x} = E & (F ∖ {x}).
Axiom remove_belongs_concat_l : forall A x (E F : gen_env A),
  x ∉ F ->
  (E & F) ∖ {x} = (E ∖ {x}) & F.

(** Remove and belongs and all_belongs. *)
Axiom remove_ok_notin : forall A x (E : gen_env A),
  ok E ->
  x ∉ (E ∖ {x}).
Axiom remove_all_belongs : forall A x xs (F : gen_env A),
  ¬ List.In x xs -> (x :: xs) ⊂ F ->
  xs ⊂ (F ∖ {x}).

(** Remove commutes with map and updating. *)
Axiom remove_map : forall A B (f : A -> B) (E : gen_env A) x,
  (map f E) ∖ {x} = map f (E ∖ {x}).
Axiom remove_update : forall A x (E F : gen_env A),
  ok E ->
  (E ::= F) ∖ {x} = (E ∖ {x}) ::= F.
Axiom remove_update_eq : forall A x y (v : A) (E : gen_env A),
  x = y ->
  (E ::= (y ∶ v)) ∖ {x} = E ∖ {x}.

(** Ok and remove. *)
Axiom ok_remove : forall A x (E : gen_env A),
  ok E ->
  ok (E ∖ {x}).

(* ---------------------------------------------------------------------- *)
(** **** Properties of all_remove *)

(** All_remove and remove. *)
Axiom all_remove_remove : forall A x xs (E : gen_env A),
  E ∖ (x :: xs) = (E ∖ {x}) ∖ xs.

(** All_remove is identity on empty environments. *)
Axiom all_remove_empty : forall A xs,
  (@empty A) ∖ xs = (@empty A).
Axiom all_remove_nil : forall A (E : gen_env A),
  E ∖ nil = E.

(** All_remove on singular. *)
Axiom all_remove_single_in : forall A x xs (v : A),
  List.In x xs ->
  (x ∶ v) ∖ xs = (@empty A).
Axiom all_remove_single_not_in : forall A x xs (v : A),
  ¬ List.In x xs ->
  (x ∶ v) ∖ xs = (x ∶ v).

(** All_remove on singulars. *)
Axiom all_remove_singles_in : forall A xs ys (vs : list A),
  xs = ys -> length xs = length vs ->
  (xs ∷ vs) ∖ ys = (@empty A).
Axiom all_remove_singles_not_in : forall A xs ys (vs : list A),
  List.Forall (fun x => ¬ List.In x xs) ys ->
  (xs ∷ vs) ∖ ys = (xs ∷ vs).

(** All_remove and notin. *)
Axiom all_remove_notin : forall A xs (E : gen_env A),
  xs ⊄ E ->
  E ∖ xs = E.
Axiom notin_all_remove_notin : forall A x ys (E : gen_env A),
  x ∉ E ->
  x ∉ (E ∖ ys).
Axiom all_notin_all_remove_notin : forall A xs ys (E : gen_env A),
  xs ⊄ E ->
  xs ⊄ (E ∖ ys).

(** Remove and all_notin. *)
Axiom all_remove_ok_notin : forall A xs (E : gen_env A),
  ok E ->
  xs ⊄ (E ∖ xs).

(** All_remove and concatenation. *)
Axiom all_remove_belongs_concat_r : forall A xs (E F : gen_env A),
  List.NoDup xs ->
  xs ⊂ F ->
  (E & F) ∖ xs = E & (F ∖ xs).
Axiom all_remove_belongs_concat_l : forall A xs (E F : gen_env A),
  xs ⊄ F ->
  (E & F) ∖ xs = (E ∖ xs) & F.

(** All_remove commutes with map and updating. *)
Axiom all_remove_map : forall A B (f : A -> B) (E : gen_env A) xs,
  (map f E) ∖ xs = map f (E ∖ xs).
Axiom all_remove_update : forall A xs (E F : gen_env A),
  ok E ->
  (E ::= F) ∖ xs = (E ∖ xs) ::= F.

(** Ok and all_remove. *)
Axiom ok_all_remove : forall A xs (E : gen_env A),
  ok E ->
  ok (E ∖ xs).

(* ---------------------------------------------------------------------- *)
(** **** Properties of ok *)

(** Ok stands for empty and singular environments. *)
Axiom ok_empty : forall A,
  ok (@empty A).
Axiom ok_single : forall A x (v : A),
  ok (x ∶ v).

(** Ok stands if there is no variable duplication. *)
Axiom ok_singles : forall A xs (vs : list A),
  List.NoDup xs ->
  ok (xs ∷ vs).
Axiom ok_singles_inv : forall A xs (vs : list A),
  length xs = length vs ->
  ok (xs ∷ vs) ->
  List.NoDup xs.

(** Ok stands on concatenation when domains are disjoints. *)
Axiom ok_concat : forall A (E F : gen_env A),
  ok E -> ok F ->
  (dom E) ⊄ F -> (dom F) ⊄ E ->
  ok (E & F).
Axiom ok_concat_inv : forall A (E F : gen_env A),
  ok (E & F) ->
  ok E ∧ ok F ∧ (dom E) ⊄ F ∧ (dom F) ⊄ E.
Axiom ok_concat_comm : forall A (E F : gen_env A),
  ok (E & F) ->
  ok (F & E).

(** Belongs and concat with ok. *)
Axiom belongs_ok_concat_inv_l : forall A x (F G : gen_env A),
  ok (F & G) ->
  x ∈ F ->
  x ∉ G.
Axiom belongs_ok_concat_inv_r : forall A x (F G : gen_env A),
  ok (F & G) ->
  x ∈ G ->
  x ∉ F.
Axiom concat_not_ok : forall A x (F G : gen_env A),
  x ∈ F -> x ∈ G ->
  ¬ ok (F & G).

(** Additional properties when ok stands. *)

(** Update commutes with concatenation on the left. *)
Axiom update_concat_l : forall A (E F G : gen_env A),
  ok (E & F) ->
  (E & F) ::= G = (E ::= G) & (F ::= G).

End Properties.

End CoreGenericEnvironmentType.
