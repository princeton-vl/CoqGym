From mathcomp Require Import ssreflect ssrbool eqtype.
Require Import Arith List String Omega.
Require Import Program Relations Wellfounded Lexicographic_Product.
From QuickChick Require Import QuickChick.
From QuickChick.stlc Require Import monad.

Import ListNotations.

Definition tvar := nat.
Definition var := nat.

Inductive type : Type :=
| N : type
| Arrow : type -> type -> type.

Definition type_eq_dec (t1 t2 : type) : {t1 = t2} + {t1 <> t2}.
Proof. do 2 decide equality. Defined.

Fixpoint type_size (tau : type) : nat :=
  match tau with
    | N => 0
    | Arrow tau1 tau2 =>
      1 + (type_size tau1 + type_size tau2)
  end.

Definition lt_type (tau1 tau2 : type) : Prop :=
  type_size tau1 < type_size tau2.

Lemma wf_lt_type : well_founded lt_type.
Proof.
  unfold lt_type. apply wf_inverse_image. apply lt_wf.
Qed.

Inductive term : Type :=
| Const : nat -> term
| Id : var -> term
| App : term -> term -> term
| Abs : term -> term.

(* Terms that do not have applications *)
Inductive app_free : term -> Prop :=
| ConsNoApp : forall n, app_free (Const n)
| IdNoApp : forall x, app_free (Id x)
| AbsNoApp : forall (t : term),
               app_free t -> app_free (Abs t).

(* Number of applications in a term *)
Fixpoint app_no (t : term) : nat :=
  match t with
    | Const _ | Id _ => 0
    | Abs t => app_no t
    | App t1 t2 => 1 + (app_no t1 + app_no t2)
  end.

Definition env := list type.

Inductive bind : env -> nat -> type -> Prop :=
| BindNow   : forall tau env, bind (tau :: env) 0 tau
| BindLater : forall tau tau' x env,
    bind env x tau -> bind (tau' :: env) (S x) tau.

Inductive typing (e : env) : term -> type -> Prop :=
| TId :
    forall x tau,
      nth_error e x = Some tau ->
      typing e (Id x) tau
| TConst :
    forall n,
      typing e (Const n) N
| TAbs :
    forall t tau1 tau2,
      typing (tau1 :: e) t tau2 ->
      typing e (Abs t) (Arrow tau1 tau2)
| TApp :
    forall t1 t2 tau1 tau2,
      typing e t1 (Arrow tau1 tau2) ->
      typing e t2 tau1 ->
      typing e (App t1 t2) tau2.

Inductive typing' (e : env) : term -> type -> Prop :=
| TId' :
    forall x tau,
      bind e x tau ->
      typing' e (Id x) tau
| TConst' :
    forall n,
      typing' e (Const n) N
| TAbs' :
    forall t tau1 tau2,
      typing' (tau1 :: e) t tau2 ->
      typing' e (Abs t) (Arrow tau1 tau2)
| TApp' :
    forall t1 t2 tau1 tau2,
      typing' e t1 (Arrow tau1 tau2) ->
      typing' e t2 tau1 ->
      typing' e (App t1 t2) tau2.

Derive Arbitrary for type.
Instance dec_type (t1 t2 : type) : Dec (t1 = t2).
Proof. dec_eq. Defined.
Derive ArbitrarySizedSuchThat for (fun x => bind env x tau).
Derive ArbitrarySizedSuchThat for (fun t => typing' env t tau).

Inductive option_le : option nat -> option nat -> Prop :=
    | opt_le_1 : option_le None None
    | opt_le_2 : forall n, option_le None (Some n)
    | opt_le_3 : forall n m : nat,
                   n <= m -> option_le (Some n) (Some m).

(* The following keeps track of the size of largest type that appears in a cut
   in the derivation tree. Needed for verification purposes *)
Inductive typing_max_tau (e : env) : term -> type -> nat -> Prop :=
| TIdMax :
    forall x tau,
      nth_error e x = Some tau ->
      typing_max_tau e (Id x) tau 0
| TConstMax :
    forall n,
      typing_max_tau e (Const n) N 0
| TAbsMax :
    forall t tau1 tau2 m,
      typing_max_tau (tau1 :: e) t tau2 m ->
      typing_max_tau e (Abs t) (Arrow tau1 tau2) m
| TAppMax :
    forall t1 t2 tau1 tau2 m1 m2,
      typing_max_tau e t1 (Arrow tau1 tau2) m1 ->
      typing_max_tau e t2 tau1 m2 ->
      typing_max_tau e (App t1 t2) tau2 (max (type_size tau1) (max m1 m2)).

Lemma typing_max_tau_correct :
  forall e t tau,
    (exists m, typing_max_tau e t tau m) <->
    typing e t tau.
Proof.
  intros. split.
  - move => [maxt H]. induction H; econstructor; eauto.
  - move => H.
    induction H; (try now eexists; econstructor; eauto).
    destruct IHtyping as [m H']. exists m. constructor; auto.
    destruct IHtyping1 as [m1 H1];
    destruct IHtyping2 as [m2 H2]. eexists. econstructor; eauto.
Qed.

Lemma typing_max_no_app :
  forall e t tau,
    app_free t ->
    typing e t tau ->
    typing_max_tau e t tau 0.
Proof.
  intros e t tau H. generalize e tau. clear e tau.
  induction H; intros e tau H1; inversion H1; subst; constructor; auto.
Qed.

(* Small step CBV semantics *)
Fixpoint is_value (t : term) : bool :=
  match t with
    | Const _ | Abs _ => true
    | _ => false
  end.

Fixpoint subst (y : var) (t1 : term) (t2 : term) : term :=
  match t2 with
    | Const n => Const n
    | Id x =>
      if eq_nat_dec x y then t1 else t2
    | App t t' =>
      App (subst y t1 t) (subst y t1 t')
    | Abs t =>
      subst (S y) t1 t
  end.

Fixpoint step (t : term) : option term :=
  match t with
    | Const _ | Id _ => None | Abs x => None
    | App t1 t2 =>
      if is_value t1 then
        match t1 with
          | Abs t =>
            if is_value t2 then ret (subst 0 t1 t)
            else
              t2' <- step t2;;
              ret (App t1 t2')
          | _ => None
        end
      else
        t1' <- step t1;;
        ret (App t1' t2)
  end.

(* Generators *)
Module DoNotation.
Notation "'do!' X <- A ; B" :=
  (bindGen A (fun X => B))
    (at level 200, X ident, A at level 100, B at level 200).
End DoNotation.
Import DoNotation.

(* Sized generator of simple types *)
Fixpoint gen_type_size (n : nat) : G type :=
  match n with
    | 0 => returnGen N
    | S n' =>
      do! m <- choose (0, n');
          liftGen2 Arrow (gen_type_size (n' - m)) (gen_type_size (n' - (n' - m)))
  end.

(* Generator of simple types *)
Definition gen_type : G type := bindGen arbitrary gen_type_size.

(* Returns the list of bindings that have type tau in e *)
Definition vars_with_type (e : env) (tau : type) : list term :=
  map (fun p => Id (snd p))
      (filter (fun p => proj1_sig (Sumbool.bool_of_sumbool (type_eq_dec tau (fst p))))
              (combine e (seq 0 (List.length e)))).

Definition sigT_of_prod {A B : Type} (p : A * B) : {_ : A & B} :=
  let (a, b) := p in existT (fun _ : A => B) a b.

Definition lt_pair (c1 c2 : (nat * type)) : Prop :=
  lexprod nat (fun _ => type) lt (fun _ => lt_type) (sigT_of_prod c1) (sigT_of_prod c2).

Lemma wf_lt_pair : well_founded lt_pair.
Proof.
  unfold lt_pair. apply wf_inverse_image.
  apply wf_lexprod. now apply Wf_nat.lt_wf. intros _; now apply wf_lt_type.
Qed.


(* Generator of app-free well-typed terms of type tau *)
Fixpoint gen_term_no_app (tau : type)  (e : env) : G term :=
  match vars_with_type e tau with
    | [] =>
      match tau with
        | N => liftGen Const arbitrary
        | Arrow tau1 tau2 =>
          liftGen Abs (gen_term_no_app tau2 (tau1 :: e))
      end
    | def :: vars =>
      oneOf_ (returnGen def)
            [ match tau with
                | N => liftGen Const arbitrary
                | Arrow tau1 tau2 =>
                   liftGen Abs (gen_term_no_app tau2 (tau1 :: e))
              end;
              elems_ def (def :: vars)]
  end.

(* Generator of well-typed terms of type tau. [fst p] is the maximum number of applications *)
Program Fixpoint gen_term_size (p : nat * type) {wf lt_pair p} : env -> G term :=
  fun (e : env) => (* apparently with this trick we get a more manageable term *)
  match p with
    | (0, tau) => gen_term_no_app tau e
    | (S n', tau) =>
      match vars_with_type e tau with
        | [] =>
            oneOf_ (gen_term_no_app tau e)
            [ (do! tau' <- gen_type;
               do! m <- choose (0, n');
               do! m' <- choose (n' -  m, n');
               liftGen2 App (@gen_term_size (n' - m, (Arrow tau' tau)) _ e)
                        (@gen_term_size (n' - m', tau') _ e));
              (match tau with
                 | N => liftGen Const arbitrary
                 | Arrow tau1 tau2 =>
                   liftGen Abs (@gen_term_size (S n', tau2) _ (tau1 :: e))
               end)]
        | def :: vars =>
            oneOf_ (gen_term_no_app tau e)
            [ (do! tau' <- gen_type;
               do! m <- choose (0, n');
               do! m' <- choose (n' - m, n');
               liftGen2 App (@gen_term_size (n' - m, (Arrow tau' tau)) _ e)
                        (@gen_term_size (n' - m', tau') _ e));
              (match tau with
                 | N => liftGen Const arbitrary
                 | Arrow tau1 tau2 =>
                   liftGen Abs (@gen_term_size (S n', tau2) _ (tau1 :: e))
               end);
              elems_ def (def :: vars) ]
      end
  end.
Solve Obligations with
  program_simpl; unfold lt_pair; apply left_lex; omega.
Solve Obligations with
  program_simpl; unfold lt_pair; apply right_lex; unfold lt_type; simpl; omega.
Next Obligation.
  unfold MR. apply wf_inverse_image. apply wf_lt_pair.
Defined.


Definition gen_term_size_unfold (p : nat * type) (e : env) : G term :=
  match p with
    | (0, tau) => gen_term_no_app tau e
    | (S n', tau) =>
      match vars_with_type e tau with
        | [] =>
            oneOf_ (gen_term_no_app tau e)
            [ (do! tau' <- gen_type;
               do! m <- choose (0, n');
               do! m' <- choose (n' - m, n');
               liftGen2 App (gen_term_size (n' - m, (Arrow tau' tau)) e)
                        (gen_term_size (n' - m', tau') e));
              (match tau with
                 | N => liftGen Const arbitrary
                 | Arrow tau1 tau2 =>
                   liftGen Abs (@gen_term_size (S n', tau2) (tau1 :: e))
               end)]
        | def :: vars =>
            oneOf_ (gen_term_no_app tau e)
            [ (do! tau' <- gen_type;
               do! m <- choose (0, n');
               do! m' <- choose (n' - m, n');
               liftGen2 App (gen_term_size (n' - m, (Arrow tau' tau)) e)
                        (@gen_term_size (n' - m', tau') e));
              (match tau with
                 | N => liftGen Const arbitrary
                 | Arrow tau1 tau2 =>
                   liftGen Abs (gen_term_size (S n', tau2) (tau1 :: e))
               end);
              elems_ def (def :: vars) ]
      end
  end.

Import WfExtensionality.

Lemma gen_term_size_eq (e : env) (p : nat * type) :
  gen_term_size p e =
  gen_term_size_unfold p e.
Proof.
  unfold_sub gen_term_size (gen_term_size p e); simpl.
  destruct p as [[|n] [|]]; try reflexivity;
  destruct (vars_with_type e _) eqn:Heq; simpl;
  repeat (rewrite !Heq /=; apply f_equal; try reflexivity).
Qed.

Global Opaque gen_term_size.

Definition gen_term (tau : type) :=
  sized (fun s => gen_term_size (s, tau) []).


Open Scope string.

Fixpoint show_type (tau : type) :=
  match tau with
    | N => "Nat"
    | Arrow tau1 tau2 =>
      "(" ++ show_type tau1 ++ " -> " ++ show_type tau2 ++ ")"
  end.

Instance showType : Show type := { show := show_type }.

Fixpoint show_term (t : term) :=
  match t with
    | Const n => show n
    | Id x => "Id" ++ show x
    | App t1 t2 => "(" ++ show_term t1 ++ " " ++ show_term t2 ++ ")"
    | Abs t => "λ.(" ++ show_term t ++ ")"
  end.

Close Scope string.

Instance showTerm : Show term := { show := show_term }.
