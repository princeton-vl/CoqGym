Class Var_env : Type := {
  Var : Type;
  var_eq: forall v1 v2: Var, {v1 = v2} + {v1 <> v2}
}.

Section Logic.

Context {venv: Var_env}.

Inductive Term: Type :=
  | andp : Term -> Term -> Term
  | orp : Term -> Term -> Term
  | impp : Term -> Term -> Term
  | falsep : Term
  | varp : Var -> Term.

Notation "x && y" := (andp x y) (at level 40, left associativity) : IPC_scope.
Notation "x || y" := (orp x y) (at level 50, left associativity) : IPC_scope.
Notation "x --> y" := (impp x y) (at level 55, right associativity) : IPC_scope.
Notation "'FF'" := falsep : IPC_scope.

Local Open Scope IPC_scope.

Definition term_eq: forall t1 t2: Term, {t1 = t2} + {t1 <> t2}.
Proof.
  induction t1; intros.
  + destruct t2; try solve [right; congruence].
    destruct (IHt1_1 t2_1), (IHt1_2 t2_2); [left | right | right | right]; congruence.
  + destruct t2; try solve [right; congruence].
    destruct (IHt1_1 t2_1), (IHt1_2 t2_2); [left | right | right | right]; congruence.
  + destruct t2; try solve [right; congruence].
    destruct (IHt1_1 t2_1), (IHt1_2 t2_2); [left | right | right | right]; congruence.
  + destruct t2; try solve [right; congruence].
    left; auto.
  + destruct t2; try solve [right; congruence].
    destruct (var_eq v v0); [left | right]; congruence.
Defined.

Definition Context := Term -> bool.

Definition EmptyContext : Context := fun _ => false.

Definition ExtendContext (ctx: Context) (t: Term) : Context :=
  fun t0 => if term_eq t0 t then true else ctx t0.

Notation "ctx ;; t" := (ExtendContext ctx t) (at level 65, left associativity) : IPC_scope.

Class Semantic : Type := mk_sem {
  ModelType : Type;
  satisfy : ModelType -> Term -> Prop
}.

Definition valid {sem: Semantic} (t: Term) : Prop :=
  forall M, @satisfy sem M t.

Definition sem_conseq {sem: Semantic} (ctx : Context) (t: Term) : Prop :=
  forall M, (forall t0, ctx t0 = true -> @satisfy sem M t0) -> @satisfy sem M t.

Notation "M  |=  t" := (satisfy M t) (at level 60, no associativity) : IPC_scope.

Notation "|==  t" := (valid t) (at level 61, no associativity) : IPC_scope.

Notation "ctx  |==  t" := (sem_conseq ctx t) (at level 60, no associativity) : IPC_scope.

Class ProofTheory : Type := mk_pt {
  derivable : Context -> Term -> Prop
}.

Notation "ctx  |--  t" := (derivable ctx t) (at level 60, no associativity) : IPC_scope.

Definition provable {pt: ProofTheory} t := EmptyContext |-- t.

Notation "|--  t" := (provable t) (at level 61, no associativity) : IPC_scope.

Definition sound (sem: Semantic) (pt: ProofTheory) : Prop :=
  forall ctx t, ctx |-- t -> ctx |== t.
  
Definition weak_complete (sem: Semantic) (pt: ProofTheory) : Prop :=
  forall t, |== t -> |-- t.

Definition strong_complete (sem: Semantic) (pt: ProofTheory) : Prop :=
  forall ctx t, ctx |== t -> ctx |-- t.

End Logic.

Module IPC_Notation.
Notation "x && y" := (andp x y) (at level 40, left associativity) : IPC_scope.
Notation "x || y" := (orp x y) (at level 50, left associativity) : IPC_scope.
Notation "x --> y" := (impp x y) (at level 55, right associativity) : IPC_scope.
Notation "'FF'" := falsep : IPC_scope.
End IPC_Notation.

Module LogicNotation.
Notation "ctx ;; t" := (ExtendContext ctx t) (at level 65, left associativity) : IPC_scope.
Notation "M  |=  t" := (satisfy M t) (at level 60, no associativity) : IPC_scope.
Notation "|==  t" := (valid t) (at level 61, no associativity) : IPC_scope.
Notation "ctx  |==  t" := (sem_conseq ctx t) (at level 60, no associativity) : IPC_scope.
Notation "ctx  |--  t" := (derivable ctx t) (at level 60, no associativity) : IPC_scope.
Notation "|--  t" := (provable t) (at level 61, no associativity) : IPC_scope.
End LogicNotation.