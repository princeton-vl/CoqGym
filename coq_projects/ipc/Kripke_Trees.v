(* File: Kripke_Trees.v  (last edited on 25/10/2000) (c) Klaus Weich  *)


Require Export AvlTrees.
Require Export Trees.
Require Export Derivations.

(*******   Kripke_Model    ****************************************)


Inductive Kripke_Model (A : Set) (World : A -> Type) 
(le : A -> A -> Type) (forces0 : A -> Int -> Prop) : Type :=
    kripke_model :
      (forall k : A, World k -> le k k) ->
      (forall k0 k1 k2 : A,
       World k0 -> World k1 -> World k2 -> le k0 k1 -> le k1 k2 -> le k0 k2) ->
      (forall k0 k1 : A,
       World k0 ->
       World k1 -> le k0 k1 -> forall i : Int, forces0 k0 i -> forces0 k1 i) ->
      Kripke_Model A World le forces0.



Fixpoint forces (A : Set) (World : A -> Type) 
 (le : A -> A -> Type) (forces0 : A -> Int -> Prop) 
 (k : A) (a : form) {struct a} : Prop :=
  match a with
  | Falsum => False
  | Atom i => forces0 k i
  | AndF a0 a1 =>
      forces A World le forces0 k a0 /\ forces A World le forces0 k a1
  | OrF a0 a1 =>
      forces A World le forces0 k a0 \/ forces A World le forces0 k a1
  | Imp a0 a1 =>
      forall k' : A,
      World k' ->
      le k k' ->
      forces A World le forces0 k' a0 -> forces A World le forces0 k' a1
  end.


Lemma forces_mon :
 forall (A : Set) (World : A -> Type) (le : A -> A -> Type)
   (forces0 : A -> Int -> Prop),
 Kripke_Model A World le forces0 ->
 forall (k : A) (a : form),
 World k ->
 forces A World le forces0 k a ->
 forall k' : A, World k' -> le k k' -> forces A World le forces0 k' a.
intros A World le forces0 kripke k a w; elim a; clear a.

simpl in |- *.
trivial.

intros.
elim kripke.
intros refl trans mon.
simpl in |- *; apply (mon k k'); assumption.

intros a ih_a b ih_b.
simpl in |- *.
intros u0; elim u0; clear u0; intros u0 u1.
intros; split.
apply ih_a; assumption.
apply ih_b; assumption.

intros a ih_a b ih_b.
simpl in |- *.
intros u0; elim u0; clear u0; intros u0.
intros; left.
apply ih_a; assumption.
intros; right.
apply ih_b; assumption.

intros a ih_a b ih_b.
simpl in |- *.
intros.
apply H.
assumption.
elim kripke.
intros refl trans mon.
apply (trans k k' k'0); assumption.
assumption.
Qed.



Lemma soundness :
 forall (t : proof_term) (context : flist) (a : form),
 derives context t a ->
 forall (A : Set) (World : A -> Type) (le : A -> A -> Type)
   (forces0 : A -> Int -> Prop),
 Kripke_Model A World le forces0 ->
 forall k : A,
 World k ->
 (forall c : form, In c context -> forces A World le forces0 k c) ->
 forces A World le forces0 k a.
intros t context a der_t A World le forces0 kripke_model0.
elim der_t; clear der_t t a context.

(* t=(Var n) *)
intros context n a nth k world forces_context.
apply forces_context.
apply nth_in with n; assumption.

(* t=(Efq r b) *)
intros context r a der_t ih k world forces_context.
elimtype False.
apply (ih k world forces_context).

(* t=(Abs a0 r) *)
intros context a r b der_t ih k world forces_context.
simpl in |- *.
intros k' world_k' le_k' forces_a0.
apply (ih k' world_k').
intros c in_c.
inversion_clear in_c.
 rewrite <- H.
assumption.
apply forces_mon with k; try assumption.
apply forces_context; assumption.

(* t=(App r s) *)
intros context r s a b der_r ih_r der_s ih_s k world forces_context.
apply (ih_r k world forces_context k).
assumption.
elim kripke_model0; auto.
apply (ih_s k world forces_context).

(* t=(Pair r s) *)
intros context r s a b der_r ih_r der_s ih_s k world forces_context.
split.
apply (ih_r k world forces_context).
apply (ih_s k world forces_context).

(* t=(PrL r) *)
intros context r a b der_r ih k world forces_context.
generalize (ih k world forces_context).
intros u0; elim u0; intros; assumption.

(* t=(PrR r) *)
intros context r a b der_r ih k world forces_context.
generalize (ih k world forces_context).
intros u0; elim u0; intros; assumption.

(* t=(OrFL r b) *)
intros context r a b der_r ih k world forces_context.
left.
apply (ih k world forces_context).

(* t=(OrFR r b) *)
intros context r a b der_r ih k world forces_context.
right.
apply ih; assumption.

(* t=(Cas r s t) *)
intros context r s t a b c der_r ih_r der_s ih_s der_t ih_t k world
 forces_context.
generalize (ih_r k world forces_context); clear ih_r.
intro u0; elim u0; clear u0.
intro forces_a0.
apply ih_s; clear ih_s ih_t.
assumption.
intros c0 in_c0.
inversion_clear in_c0.
 rewrite <- H; assumption.
apply forces_context; assumption.
intros forces_b.
apply ih_t; clear ih_s ih_t.
assumption.
intros c0 in_c0; inversion_clear in_c0.
 rewrite <- H; assumption.
apply forces_context; assumption.

(* t=(Shift r) *)
intros context r a b der_r ih k world forces_context.
apply ih.
assumption.
intros c in_c.
apply forces_context.
right; assumption.
Qed.



Lemma forces_b__forces_a_imp_b :
 forall (A : Set) (World : A -> Type) (le : A -> A -> Type)
   (forces0 : A -> Int -> Prop),
 Kripke_Model A World le forces0 ->
 forall k : A,
 World k ->
 forall b : form,
 forces A World le forces0 k b ->
 forall a : form, forces A World le forces0 k (Imp a b).
intros A World le forces0 kripke k w b forces_b.
intros a.
simpl in |- *.
intros k' w' le_k_k' forces_a.
apply forces_mon with (k := k); assumption.
Qed.


Lemma forces_a0_imp_a1_imp_b__forces_a0_and_a1_imp_b :
 forall (A : Set) (World : A -> Type) (le : A -> A -> Type)
   (forces0 : A -> Int -> Prop),
 Kripke_Model A World le forces0 ->
 forall k : A,
 World k ->
 forall a0 a1 b : form,
 forces A World le forces0 k (Imp a0 (Imp a1 b)) ->
 forces A World le forces0 k (Imp (AndF a0 a1) b).
intros A World le forces0 kripke k world a0 a1 b forces_a0_a1_b.
simpl in |- *.
intros k' u0 u1 forces_a0_and_a1.
elim forces_a0_and_a1; clear forces_a0_and_a1.
intros forces_a0 forces_a1.
apply (forces_a0_a1_b k' u0 u1).
apply forces_a0.
apply u0.
elim kripke.
intros refl trans mon.
apply refl.
apply u0.
apply forces_a1.
Qed.


Lemma forces_a0_imp_c_and_a1_imp_c_and_c_imp_b__forces_a0_or_a1_imp_b :
 forall (A : Set) (World : A -> Type) (le : A -> A -> Type)
   (forces0 : A -> Int -> Prop) (k : A) (a0 a1 c b : form),
 forces A World le forces0 k (Imp a0 c) ->
 forces A World le forces0 k (Imp a1 c) ->
 forces A World le forces0 k (Imp c b) ->
 forces A World le forces0 k (Imp (OrF a0 a1) b).
intros A World le forces0 k a0 a1 c b forces_a0_c forces_a1_c forces_c_b.
simpl in |- *.
intros k' u0 u1 forces_a0_or_a1.
elim forces_a0_or_a1; clear forces_a0_or_a1.
intro forces_a0.
apply (forces_c_b k' u0 u1).
apply (forces_a0_c k' u0 u1 forces_a0).
intro forces_a1.
apply (forces_c_b k' u0 u1).
apply (forces_a1_c k' u0 u1 forces_a1).
Qed.


Lemma forces_a0_imp_b_and_a1_imp_b__forces_a0_or_a1_imp_b :
 forall (A : Set) (World : A -> Type) (le : A -> A -> Type)
   (forces0 : A -> Int -> Prop) (k : A) (a0 a1 b : form),
 forces A World le forces0 k (Imp a0 b) ->
 forces A World le forces0 k (Imp a1 b) ->
 forces A World le forces0 k (Imp (OrF a0 a1) b).
intros A World le forces0 k a0 a1 b forces_a0_b forces_a1_b.
simpl in |- *.
intros k' u0 u1 forces_a0_or_a1.
elim forces_a0_or_a1; clear forces_a0_or_a1.
intro forces_a0.
apply (forces_a0_b k' u0 u1 forces_a0).
intro forces_a1.
apply (forces_a1_b k' u0 u1 forces_a1).
Qed.



Lemma forces_a1_imp_b__forces_a0_imp_a1_imp_b :
 forall (A : Set) (World : A -> Type) (le : A -> A -> Type)
   (forces0 : A -> Int -> Prop),
 Kripke_Model A World le forces0 ->
 forall k : A,
 World k ->
 forall a0 : form,
 forces A World le forces0 k a0 ->
 forall a1 b : form,
 forces A World le forces0 k (Imp a1 b) ->
 forces A World le forces0 k (Imp (Imp a0 a1) b).
intros A World le forces0 kripke k w a0 forces_a0 a1 b forces_a1_b.
simpl in |- *.
intros k' w' le_k_k' forces_a0_a1.
apply (forces_a1_b k').
assumption.
assumption.
change (forces A World le forces0 k' a1) in |- *.
apply (forces_a0_a1 k').
assumption.
elim kripke.
intros refl trans mon.
apply refl.
assumption.
apply forces_mon with (k := k); assumption.
Qed.

Lemma forces_a0_imp_a1_imp_b__forces_a1_imp_b :
 forall (A : Set) (World : A -> Type) (le : A -> A -> Type)
   (forces0 : A -> Int -> Prop),
 Kripke_Model A World le forces0 ->
 forall k : A,
 World k ->
 forall a0 : form,
 forces A World le forces0 k a0 ->
 forall a1 b : form,
 forces A World le forces0 k (Imp (Imp a0 a1) b) ->
 forces A World le forces0 k (Imp a1 b).
intros A World le forces0 kripke k w a0 forces_a0 a1 b forces_a0a1_b.
simpl in |- *.
intros k' w' le_k_k' forces_a1.
apply (forces_a0a1_b k').
assumption.
assumption.
change (forces A World le forces0 k' (Imp a0 a1)) in |- *.
simpl in |- *.
intros k'' w'' le'' forces_a0''.
elim kripke.
intros refl trans mon.
apply forces_mon with (k := k'); assumption.
Qed.

Lemma forces_a0_imp_b__forces_a0_and_a1_imp_b :
 forall (A : Set) (World : A -> Type) (le : A -> A -> Type)
   (forces0 : A -> Int -> Prop) (k : A) (a0 b : form),
 forces A World le forces0 k (Imp a0 b) ->
 forall a1 : form, forces A World le forces0 k (Imp (AndF a0 a1) b).
intros A World le forces0 k a0 b forces_a0_b a1.
simpl in |- *.
intros k' w' le_k_k' forces_a0_a1.
apply (forces_a0_b k').
assumption.
assumption.
change (forces A World le forces0 k' a0) in |- *.
elim forces_a0_a1; trivial.
Qed.



Lemma forces_a1_imp_b__forces_a0_and_a1_imp_b :
 forall (A : Set) (World : A -> Type) (le : A -> A -> Type)
   (forces0 : A -> Int -> Prop) (k : A) (a1 b : form),
 forces A World le forces0 k (Imp a1 b) ->
 forall a0 : form, forces A World le forces0 k (Imp (AndF a0 a1) b).
intros A World le forces0 k a1 b forces_a1_b a0.
simpl in |- *.
intros k' w' le_k_k' forces_a0_a1.
apply (forces_a1_b k').
assumption.
assumption.
change (forces A World le forces0 k' a1) in |- *.
elim forces_a0_a1; trivial.
Qed.


(*******   kripke_trees    ****************************************)



Definition atoms := AVL unit.
Definition ANil := AVL_NIL unit.

Definition kripke_tree := Tree atoms.
Definition Kripke_Forest := Forest atoms.
Definition forces0_t (A : atoms) (i : Int) := LOOKUP unit i A tt.

Definition Is_Monotone_kripke_tree := Is_Monotone_Tree atoms Int forces0_t.
Definition Is_Monotone_Kripke_Forest :=
  Is_Monotone_Forest atoms Int forces0_t.

Definition Suc (k0 k1 : kripke_tree) := Successor atoms k0 k1.
Definition Atms (k : kripke_tree) := root atoms k.
Definition Succs (k0 : kripke_tree) := successors atoms k0.


Lemma kripke_tree_kripke_model :
 forall k : kripke_tree,
 Is_Monotone_kripke_tree k ->
 Kripke_Model kripke_tree (fun k0 : kripke_tree => Suc k0 k)
   (fun k0 k1 : kripke_tree => Suc k1 k0)
   (fun (k0 : kripke_tree) (i : Int) => forces0_t (Atms k0) i).
intros.
apply kripke_model.

unfold Suc in |- *.
intros.
apply succs_refl.

unfold Suc in |- *.
intros.
apply succs_trans with (t1 := k1); assumption.

unfold Suc in |- *.
unfold Atms in |- *.
intros k0 k1 suc0 suc1 suc1' i forces_k1.
cut (Is_Monotone atoms Int forces0_t k).
intro is_mon_k.
inversion_clear is_mon_k.
apply H0 with (t0 := k0); assumption.
apply is_monotone_tree_is_monotone.
assumption.
Qed.



Lemma kripke_tree_succ :
 forall K : kripke_tree,
 Is_Monotone_kripke_tree K ->
 forall k : kripke_tree, Suc k K -> Is_Monotone_kripke_tree k.
unfold Is_Monotone_kripke_tree in |- *.
intros K mon k suc.
apply is_monotone_tree_successor with K; assumption.
Qed.


Definition forces_t2 (K k : kripke_tree) (a : form) :=
  forces kripke_tree (fun k0 : kripke_tree => Suc k0 K)
    (fun k0 k1 : kripke_tree => Suc k1 k0)
    (fun (k0 : kripke_tree) (i : Int) => forces0_t (Atms k0) i) k a.



Lemma forces_t2_is_local :
 forall (a : form) (k : kripke_tree),
 Is_Monotone_kripke_tree k ->
 forall k' : kripke_tree,
 Suc k' k ->
 forces_t2 k k' a ->
 forall K : kripke_tree,
 Is_Monotone_kripke_tree K -> Suc k' K -> forces_t2 K k' a.
intros a; elim a; clear a.

unfold forces_t2 in |- *.
simpl in |- *; trivial.

unfold forces_t2 in |- *; simpl in |- *.
trivial.

intros a ih_a b ih_b k mon_k k' suc_k'_k forces_k_k'_ab K mon_K suc_k'_K.
elim forces_k_k'_ab.
fold (forces_t2 k k' a) in |- *.
fold (forces_t2 k k' b) in |- *.
clear forces_k_k'_ab.
intros u0 u1.
split.
change (forces_t2 K k' a) in |- *.
apply ih_a with (k := k); assumption.
change (forces_t2 K k' b) in |- *.
apply ih_b with (k := k); assumption.

intros a ih_a b ih_b k mon_k k' suc_k'_k forces_k_k'_ab K mon_K suc_k'_K.
elim forces_k_k'_ab; clear forces_k_k'_ab.
fold (forces_t2 k k' a) in |- *.
intro u0.
left.
change (forces_t2 K k' a) in |- *.
apply ih_a with (k := k); assumption.
fold (forces_t2 k k' b) in |- *.
intros u0.
right.
change (forces_t2 K k' b) in |- *.
apply ih_b with (k := k); assumption.

intros a ih_a b ih_b.
intros k mon_k k' suc_k'_k forces_k_k'_ab K mon_K suc_k_K. 
unfold forces_t2 in |- *; simpl in |- *.
intros k''.
fold (forces_t2 K k'' a) in |- *.
fold (forces_t2 K k'' b) in |- *.
intros.
apply ih_b with (k := k); clear ih_b.
assumption.
unfold Suc in |- *; apply succs_trans with k'; assumption.
apply (forces_k_k'_ab k''); clear forces_k_k'_ab.
unfold Suc in |- *; apply succs_trans with k'; assumption.
assumption.
change (forces_t2 k k'' a) in |- *.
apply ih_a with (k := K); clear ih_a.
assumption.
assumption.
assumption.
assumption.
unfold Suc in |- *; apply succs_trans with k'; assumption.
assumption.
assumption.
Qed.



Definition forces_t (k : kripke_tree) := forces_t2 k k.


Lemma forces_t_imp :
 forall k : kripke_tree,
 Is_Monotone_kripke_tree k ->
 forall a b : form,
 (forces_t k a -> forces_t k b) ->
 (forall k' : kripke_tree,
  In_Forest atoms k' (Succs k) -> forces_t k' (Imp a b)) ->
 forces_t k (Imp a b).
intros k mon a b forces_a_b foreach_succs.
unfold forces_t in |- *.
unfold forces_t2 in |- *.
simpl in |- *.
intro k'.
fold (forces_t2 k k' a) in |- *.
fold (forces_t2 k k' b) in |- *.
intros suc_k'_k; clear suc_k'_k.
intros suc_k'_k.
inversion_clear suc_k'_k.
assumption.
intro forces_a.
apply forces_t2_is_local with (k := t1).
unfold Is_Monotone_kripke_tree in |- *.
apply is_monotone_tree_successor with k. 
assumption.
apply successor_trans with t1.
assumption.
apply succs_refl.
assumption.
apply (foreach_succs t1 H k').
assumption.
assumption.
change (forces_t2 t1 k' a) in |- *.
apply forces_t2_is_local with (k := k).
assumption.
unfold Suc in |- *; apply successor_trans with t1.
assumption.
assumption.
assumption.
unfold Is_Monotone_kripke_tree in |- *.
apply is_monotone_tree_successor with k.
assumption.
apply successor_trans with t1.
assumption.
apply succs_refl.
assumption.
assumption.
unfold Suc in |- *; apply successor_trans with t1.
assumption.
assumption.
Qed.


Lemma forces_t_mon :
 forall k : kripke_tree,
 Is_Monotone_kripke_tree k ->
 forall a : form,
 forces_t k a -> forall k' : kripke_tree, Suc k' k -> forces_t k' a.
intros k mon a forces_a k' suc.
unfold forces_t in |- *.
apply forces_t2_is_local with (k := k).
assumption.
assumption.
unfold forces_t2 in |- *.
apply forces_mon with (k := k).
apply (kripke_tree_kripke_model k mon).
unfold Suc in |- *; apply succs_refl.
assumption.
assumption.
assumption.
unfold Is_Monotone_kripke_tree in |- *.
apply is_monotone_tree_successor with k.
assumption.
assumption.
unfold Suc in |- *; apply succs_refl.
Qed.



Lemma soundness_t :
 forall (t : proof_term) (context : flist) (a : form),
 derives context t a ->
 forall k : kripke_tree,
 Is_Monotone_kripke_tree k ->
 (forall c : form, In c context -> forces_t k c) -> forces_t k a.
intros t context a der_t k mon forces_context.
unfold forces_t in |- *.
unfold forces_t2 in |- *.
apply soundness with t context.
assumption.
apply (kripke_tree_kripke_model k mon).
unfold Suc in |- *; apply succs_refl.
exact forces_context.
Qed.



Lemma forces_b__forces_a_imp_b_t :
 forall k : kripke_tree,
 Is_Monotone_kripke_tree k ->
 forall b : form, forces_t k b -> forall a : form, forces_t k (Imp a b).
intros k mon b forces_b a.
unfold forces_t in |- *.
unfold forces_t2 in |- *.
apply forces_b__forces_a_imp_b.
apply (kripke_tree_kripke_model k mon).
unfold Suc in |- *; apply succs_refl.
assumption.
Qed.


Lemma forces_a0_imp_a1_imp_b__forces_a0_and_a1_imp_b_t :
 forall k : kripke_tree,
 Is_Monotone_kripke_tree k ->
 forall a0 a1 b : form,
 forces_t k (Imp a0 (Imp a1 b)) -> forces_t k (Imp (AndF a0 a1) b).
intros k mon a0 a1 b forces_a0_a1_b.
unfold forces_t in |- *.
unfold forces_t2 in |- *.
apply forces_a0_imp_a1_imp_b__forces_a0_and_a1_imp_b.
apply (kripke_tree_kripke_model k mon).
unfold Suc in |- *; apply succs_refl.
assumption.
Qed.


Lemma forces_a0_imp_c_and_a1_imp_c_and_c_imp_b__forces_a0_or_a1_imp_b_t :
 forall (k : kripke_tree) (a0 a1 c b : form),
 forces_t k (Imp a0 c) ->
 forces_t k (Imp a1 c) ->
 forces_t k (Imp c b) -> forces_t k (Imp (OrF a0 a1) b).
intros k a0 a1 c b forces_a0_c forces_a1_c forces_c_b.
unfold forces_t in |- *.
unfold forces_t2 in |- *.
apply forces_a0_imp_c_and_a1_imp_c_and_c_imp_b__forces_a0_or_a1_imp_b with c;
 assumption.
Qed.


Lemma forces_a1_imp_b__forces_a0_imp_a1_imp_b_t :
 forall k : kripke_tree,
 Is_Monotone_kripke_tree k ->
 forall a0 : form,
 forces_t k a0 ->
 forall a1 b : form, forces_t k (Imp a1 b) -> forces_t k (Imp (Imp a0 a1) b).
intros k mon a0 forces_a0 a1 b forces_a1_b.
unfold forces_t in |- *.
unfold forces_t2 in |- *.
apply forces_a1_imp_b__forces_a0_imp_a1_imp_b.
apply (kripke_tree_kripke_model k mon).
unfold Suc in |- *; apply succs_refl.
assumption.
assumption.
Qed.



Lemma forces_a0_imp_a1_imp_b__forces_a1_imp_b_t :
 forall k : kripke_tree,
 Is_Monotone_kripke_tree k ->
 forall a0 : form,
 forces_t k a0 ->
 forall a1 b : form, forces_t k (Imp (Imp a0 a1) b) -> forces_t k (Imp a1 b).
intros k mon a0 forces_a0 a1 b forces_a0a1_b.
unfold forces_t in |- *.
unfold forces_t2 in |- *.
apply forces_a0_imp_a1_imp_b__forces_a1_imp_b with a0.
apply (kripke_tree_kripke_model k mon).
unfold Suc in |- *; apply succs_refl.
assumption.
assumption.
Qed.


Lemma forces_a0_imp_b__forces_a0_and_a1_imp_b_t :
 forall (k : kripke_tree) (a0 b : form),
 forces_t k (Imp a0 b) -> forall a1 : form, forces_t k (Imp (AndF a0 a1) b).
intros k a0 b forces_a0_b a1.
unfold forces_t in |- *.
unfold forces_t2 in |- *.
apply forces_a0_imp_b__forces_a0_and_a1_imp_b.
assumption.
Qed.



Lemma forces_a1_imp_b__forces_a0_and_a1_imp_b_t :
 forall (k : kripke_tree) (a1 b : form),
 forces_t k (Imp a1 b) -> forall a0 : form, forces_t k (Imp (AndF a0 a1) b).
intros k a1 b forces_a1_b a0.
unfold forces_t in |- *.
unfold forces_t2 in |- *.
apply forces_a1_imp_b__forces_a0_and_a1_imp_b.
assumption.
Qed.


(*****************************************************************)

Lemma forces_a_a_imp_b__forces_b_t :
 forall (k : kripke_tree) (a b : form),
 forces_t k a -> forces_t k (Imp a b) -> forces_t k b.
intros k a b forces_a forces_ab.
apply (forces_ab k).
unfold Suc in |- *; apply successor_refl.
unfold Suc in |- *; apply successor_refl.
assumption.
Qed.


Lemma forces_a_imp_b0_a_imp_b1__forces_a_imp_a0_and_a1 :
 forall (a b0 b1 : form) (k : kripke_tree),
 forces_t k (Imp a b0) ->
 forces_t k (Imp a b1) -> forces_t k (Imp a (AndF b0 b1)).
intros a b0 b1 k forces_ab0 forces_ab1.
unfold forces_t in |- *; unfold forces_t2 in |- *; simpl in |- *.
intros k' suc_k' suc_k''.
change (forces_t2 k k' a -> forces_t2 k k' b0 /\ forces_t2 k k' b1) in |- *.
intros forces_a.
split.
apply (forces_ab0 k'); assumption.
apply (forces_ab1 k'); assumption.
Qed.


Lemma forces_a_imp_b__forces_a_imp_falsum_or_b :
 forall (k : kripke_tree) (a b : form),
 forces_t k (Imp a b) -> forces_t k (Imp a (OrF Falsum b)).
intros k a b forces_ab.
unfold forces_t in |- *; unfold forces_t2 in |- *; simpl in |- *.
intros k' suc_k' suc_k''.
change (forces_t2 k k' a -> False \/ forces_t2 k k' b) in |- *.
intros forces_a; right.
apply (forces_ab k'); assumption.
Qed.


Lemma forces_a_imp_b__forces_a_imp_b_or_falsum :
 forall (k : kripke_tree) (a b : form),
 forces_t k (Imp a b) -> forces_t k (Imp a (OrF b Falsum)).
intros k a b forces_ab.
unfold forces_t in |- *; unfold forces_t2 in |- *; simpl in |- *.
intros k' suc_k' suc_k''.
change (forces_t2 k k' a -> forces_t2 k k' b \/ False) in |- *.
intros forces_a; left.
apply (forces_ab k'); assumption.
Qed.


Lemma forces_a_imp_falsum_imp_b1_t :
 forall (k : kripke_tree) (a b1 : form), forces_t k (Imp a (Imp Falsum b1)).
unfold forces_t in |- *; unfold forces_t2 in |- *; simpl in |- *.
intros; elimtype False; assumption.
Qed.



Lemma forces_a_imp_b_imp_c__forces_a_imp_falsum_imp_c :
 forall (k : kripke_tree) (a b c : form),
 forces_t k (Imp (Imp a b) c) -> forces_t k (Imp (Imp a Falsum) c).
intros k a b c forces_abc.
unfold forces_t in |- *; unfold forces_t2 in |- *; simpl in |- *.
intros k' suc_k' suc_k''.
change (forces_t2 k k' (Imp a Falsum) -> forces_t2 k k' c) in |- *.
intros forces1.
apply (forces_abc k'); try assumption.
intros k'' suc3 suc4 forces_a.
elimtype False.
apply (forces1 k''); assumption.
Qed.


Lemma forces_vimp :
 forall (k : kripke_tree) (l : list Int) (a b : form),
 (forall k' : kripke_tree, Suc k' k -> forces_t2 k k' a -> forces_t2 k k' b) ->
 forces_t k (vimp l a) -> forces_t k (vimp l b).
intros k l.
elim l; clear l.
intros a b forces_ab forces_a.
apply forces_ab with (k' := k); try assumption.
unfold Suc in |- *; apply successor_refl.
simpl in |- *; intros i l ih a b forces_ab forces_a.
apply ih with (a := Imp (Atom i) a); try assumption.
intros k' suc1 forces_ia.
unfold forces_t in |- *; unfold forces_t2 in |- *; simpl in |- *.
intros k'' suc2 suc3 forces_i.
change (forces_t2 k k'' b) in |- *.
apply forces_ab.
assumption.
apply (forces_ia k''); assumption.
Qed.


Lemma forces_vimp2 :
 forall (k : kripke_tree) (l : list Int) (a b c : form),
 (forall k' : kripke_tree,
  Suc k' k -> forces_t2 k k' a -> forces_t2 k k' b -> forces_t2 k k' c) ->
 forces_t k (vimp l a) -> forces_t k (vimp l b) -> forces_t k (vimp l c).
intros k l.
elim l; clear l.
intros a b c forces_abc forces_a forces_b.
apply forces_abc with (k' := k); try assumption.
unfold Suc in |- *; apply successor_refl.
simpl in |- *; intros i l ih a b c forces_abc forces_a forces_b.
apply ih with (a := Imp (Atom i) a) (b := Imp (Atom i) b); try assumption.
intros k' suc1 forces_ia forces_ib.
unfold forces_t in |- *; unfold forces_t2 in |- *; simpl in |- *.
intros k'' suc2 suc3 forces_i.
change (forces_t2 k k'' c) in |- *.
apply forces_abc.
assumption.
apply (forces_ia k''); assumption.
apply (forces_ib k''); assumption.
Qed.




Lemma forces_vimp0 :
 forall (k : kripke_tree) (l : list Int) (b : form),
 (forall k' : kripke_tree, Suc k' k -> forces_t2 k k' b) ->
 forces_t k (vimp l b).
intros k l.
elim l; clear l.
intros b forces_ab.
apply forces_ab with (k' := k); try assumption.
unfold Suc in |- *; apply successor_refl.
simpl in |- *; intros i l ih b forces_ab.
apply ih.
intros k' suc1.
unfold forces_t in |- *; unfold forces_t2 in |- *; simpl in |- *.
intros k'' suc2 suc3 forces_i.
change (forces_t2 k k'' b) in |- *.
apply forces_ab.
assumption.
Qed.



Lemma forces_a_imp_b_imp_c__forces_a_imp_falsum_imp_c_t2 :
 forall (k k' : kripke_tree) (a b c : form),
 Suc k' k ->
 forces_t2 k k' (Imp (Imp a b) c) -> forces_t2 k k' (Imp (Imp a Falsum) c).
intros k k' a b c suc1 forces_abc.
unfold forces_t in |- *; unfold forces_t2 in |- *; simpl in |- *.
intros k'' suc_k' suc_k''.
change (forces_t2 k k'' (Imp a Falsum) -> forces_t2 k k'' c) in |- *.
intros forces1.
apply (forces_abc k''); try assumption.
intros k''' suc3 suc4 forces_a.
elimtype False.
apply (forces1 k'''); assumption.
Qed.
