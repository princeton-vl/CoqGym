Global Set Automatic Coercions Import.
Set Implicit Arguments.

Require Import List.
Require Import list_utils.
Require Import util.

Record Monad: Type :=
  { mon:> Set -> Set
  ; bind: forall a b, mon a -> (a -> mon b) -> mon b
  ; ret: forall (a: Set), a -> mon a
  (* Laws: *)
  ; mon_lunit: forall (a b: Set) (x: a) (f: a -> mon b), bind (ret x) f = f x
      (* (return x >>= f) = (f x) *)
  ; mon_runit: forall (a: Set) (f: mon a), bind f (@ret a) = f
      (* (f >>= return) = f *)
  ; mon_assoc: forall a b c (n: mon a) (f: a -> mon b) (g: b -> mon c),
      bind (bind n f) g =
      bind n (fun x => bind (f x) g)
      (* ((n >>= f) >>= g) = n >>= (\x -> f x >>= g) *)
  }.

  (* Todo: I vaguely recall someone mentioning that there was a way to use notation and/or implicit arguments inside a record definition. That would make the above a lot cleaner. *)

Arguments bind [m a b].
Arguments ret {m a}.

Notation "x >>= y" := (bind x y) (at level 55).
Notation "x >> y" := (bind x (fun _ => y)) (at level 30, right associativity).
Notation "x <- y ; z" := (bind y (fun x : _ => z)) (at level 30, right associativity).

Record Functor: Type :=
  { func: Set -> Set
  ; func_map: forall (a b: Set) (f: a -> b), func a -> func b
  (* Laws: *)
  ; func_id: forall (X: Set), func_map (fun (x: X) => x) = (fun (x: func X) => x)
        (* (id .) = id *)
  ; func_assoc: forall (a b c: Set) (x: func a) (f: b -> c) (g: a -> b),
      func_map (f ∘ g) x = func_map f (func_map g x)
        (* (f . g) . x = f . (g . x) *)
  }.

Arguments func_map [f a b].

Definition extMonad (M: Monad): Prop := forall (A B: Set) (f g: A -> M B), ext_eq f g -> forall x, bind x f = bind x g.

Lemma bind_eqq (M: Monad) (e: extMonad M) (A B: Set) (m n: M A) (f g: A -> M B):
  m = n -> ext_eq f g -> (m >>= f) = (n >>= g).
Proof. intros. subst. apply e. assumption. Qed.

Definition extFlipped (M: Monad): extMonad M -> forall A (x: M A) (B: Set) (f g: A -> M B), ext_eq f g -> bind x f = bind x g.
Proof. auto. Defined.

Lemma mon_lunit_under_bind (M: Monad) (A B C: Set) (a: M A) (b: A -> B) (f: A -> B -> M C):
  extMonad M -> (x <- a ; (ret (b x) >>= f x)) = (x <- a ; f x (b x)).
Proof with auto.
  intros.
  apply H.
  intro.
  apply mon_lunit.
Qed.

Section MonadFunctor. (* Every Monad is a Functor. *)

  Variable M: Monad.

  Definition bind_map (a b: Set) (f: a -> b) (x: M a): M b :=
    xv <- x ;
    ret (f xv).

  Hypothesis f_ext_eq: forall A B (f g: A -> B), (forall x, f x = g x) -> f = g.

  Lemma eta A B (f: A -> B): (fun x => f x) = f.
    intros.
    apply f_ext_eq.
    auto.
  Qed.

  Definition MonadFunctor: Functor.
  Proof with auto.
    apply (Build_Functor M bind_map).
      intros.
      apply f_ext_eq.
      intro.
      unfold bind_map.
      rewrite (eta (@ret M X)).
      apply mon_runit.
    intros.
    unfold bind_map.
    unfold compose.
    rewrite mon_assoc.
    replace (fun xv: a => ret (m:=M) (f (g xv))) with (fun x0: a =>
         bind (m:=M) (b:=c) (ret (m:=M) (g x0))
           (fun xv: b => ret (m:=M) (f xv)))...
    apply f_ext_eq.
    intros.
    rewrite mon_lunit...
  Defined.

  Definition a_monad_isa_functor T (x: M T): func MonadFunctor T := x.
    (* can't make this a coercion:
          User error: a_monad_isa_functor does not respect the inheritance uniform condition *)

End MonadFunctor.

Module IdMonad.

  Definition C (s: Set): Set := s. (* type ctor *)

  Definition bind A B (x: C A) (y: A -> C B): C B := y x.
  Definition ret (A: Set) (x: A): C A := x.

  Definition M: Monad.
  Proof. apply (Build_Monad C bind ret); auto. Defined.

  Coercion id_isa_monad A (a: C A): M A := a.
(*  Coercion id_isa_functor A (a: C A): func (MonadFunctor M) A := a.*)

  Lemma ext: extMonad M.
  Proof. compute. auto. Qed.

End IdMonad.

Unset Elimination Schemes.

Inductive Tree (A: Set): Set :=
  | Leaf: A -> Tree A
  | Node: list (Tree A) -> Tree A.

Set Elimination Schemes.

Definition Tree_ind
  : forall (A: Set) (P : Tree A -> Prop),
    (forall n : A, P (Leaf n)) ->
    (forall l : list (Tree A), (forall t, In t l -> P t) -> P (Node l)) ->
  forall t, P t.
Proof with auto.
  intros A P Hbase Hrcd.
  refine (fix IH (t:Tree A) {struct t} : P t := _).
  case t; intros.
    apply Hbase.
  apply Hrcd.
  induction l.
    simpl.
    intros.
    contradiction.
  simpl.
  intros.
  destruct H.
    subst t0.
    apply IH.
  apply IHl.
  assumption.
Qed.

Section MonadToys.

  Definition liftM (A B: Set) (f: A -> B) (M: Monad) (x: M A): M B :=
    xv <- x ; ret (f xv).

  Definition liftM2 (A B C: Set) (f: A -> B -> C) (M: Monad) (x: M A) (y: M B): M C :=
    xv <- x ; yv <- y ; ret (f xv yv).

  Fixpoint foldlM {A B: Set} {M: Monad} (f: A -> B -> M A) (x: A) (l: list B) {struct l}: M A :=
    match l with
    | nil => ret x
    | h :: t => fax <- f x h ; foldlM f fax t
    end. (* Haskell's foldM *)

  Fixpoint foldrM {A B: Set} {M: Monad} (f: B -> A -> M A) (x: A) (l: list B) {struct l}: M A :=
    match l with
    | nil => ret x
    | h :: t => t' <- foldrM f x t; f h t'
    end. (* missing in Haskell.. *)

  Lemma foldlM_cons (A B: Set) (M: Monad) (f: A -> B -> M A) (x: A) (h: B) (t: list B):
    foldlM f x (h :: t) = fax <- f x h ; foldlM f fax t.
  Proof. auto. Qed.

  Fixpoint filterM {A: Set} {M: Monad} (p: A -> M bool) (l: list A): M (list A) :=
    match l with
    | nil => ret nil
    | h :: t =>
      b <- p h ;
      t' <- filterM p t ;
      ret (if b then h :: t' else t')
    end. (* as in Haskell *)

  Lemma filterM_id (A: Set) (p: A -> IdMonad.M bool) (l: list A): filter p l = filterM p l.
  Proof with auto.
    induction l...
    simpl.
    rewrite IHl...
  Qed.

End MonadToys.

Arguments liftM [A B] _ [M].

Record MonadTrans: Type :=
  { transMonad: forall (m: Monad), extMonad m -> Monad
  ; lift: forall (m: Monad) (e: extMonad m) (A: Set), m A -> transMonad e A
  }.
