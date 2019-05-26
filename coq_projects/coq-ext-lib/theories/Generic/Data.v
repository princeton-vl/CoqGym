Require Import Coq.Lists.List.
Require Import ExtLib.Data.Member.
Require Import ExtLib.Data.HList.
Require Import ExtLib.Generic.Func.
(** This module gives a representation of inductive types **)

Set Implicit Arguments.
Set Strict Implicit.

Fixpoint hlist_to_tuple ps (h : hlist (fun x : Type => x) ps) : asTuple ps :=
  match h in hlist _ ps return asTuple ps with
    | Hnil => tt
    | Hcons x h => (x,hlist_to_tuple h)
  end.

Inductive itype (ps : list Type) : Type :=
| Inj : Type -> itype ps
| Rec : hlist (fun x => x) ps -> itype ps
| Sum : itype ps -> itype ps -> itype ps
| Prod : itype ps -> itype ps -> itype ps
| Sig : forall T : Type, (T -> itype ps) -> itype ps
| Pi : forall T : Type, (T -> itype ps) -> itype ps
| Get : forall T : Type, member T ps -> (T -> itype ps) -> itype ps
| Unf : forall T : Type, member T ps -> T -> itype ps -> itype ps.

Definition Unit {ps} := @Inj ps unit.

Section denote.
  Variable (ps : list Type).

  Fixpoint itypeD (i : itype ps) {struct i}
  : asFunc ps Type -> asFunc ps Type :=
    match i return asFunc ps Type -> asFunc ps Type with
      | Get pf f => fun F => @get ps _ _ pf (fun x => itypeD (f x) F)
      | Inj _ T => fun _ => const T
      | Rec h => fun F => const (applyF F (hlist_to_tuple h))
      | @Sig _ t f => fun F =>
                     @under _ _ (fun App => @sigT t (fun x' => App _ (itypeD (f x') F)))
      | @Pi _ t f => fun F =>
                     @under _ _ (fun App => forall x' : t, App _ (itypeD (f x') F))
      | Sum a b => fun F => combine sum ps (itypeD a F) (itypeD b F)
      | Prod a b => fun F => combine prod ps (itypeD a F) (itypeD b F)
      | @Unf _ T pf v i => fun F =>
                          @get ps _ _ pf (fun x => combine prod _ (const (x = v : Type)) (replace pf v (itypeD i F)))
    end%type.
End denote.

Section _match.
  Variable ps : list Type.
  Variable RecT : asFunc ps Type.

  (** NOTE: Non-dependent **)
  Fixpoint cases (i : itype ps) (k : asFunc ps Type -> asFunc ps Type)
           {struct i} : asFunc ps Type :=
    match i with
      | Inj _ T => k (const T)
      | Sum a b => combine prod ps (cases a k) (cases b k)
      | Prod a b =>
        cases a (fun A => cases b (fun B =>
                                       under _ _ (fun App => App _ A -> App _ (k B))))
      | Rec ps => k (const (applyF RecT (hlist_to_tuple ps)))
      | @Get _ T m f => @get _ _ _ m (fun x => cases (f x) k)
      | @Sig _ t f => @under _ _ (fun App => forall x' : t, (App _ (cases (f x') k)))
      | @Pi _ t f => @under _ _ (fun App => @sigT t (fun x' => App _ (cases (f x') k)))
      | @Unf _ T pf v i => replace pf v (cases i k)
    end.

End _match.

Fixpoint asPiE ps {struct ps}
: forall (F : _)
         (G : forall x : (forall U, asFunc ps U -> U), F x),
         asPi ps F :=
  match ps as ps
        return forall F : (forall U : Type, asFunc ps U -> U) -> Type,
                 (forall x : forall U : Type, asFunc ps U -> U, F x) -> asPi ps F
  with
    | nil => fun _ G => G _
    | p :: ps => fun _ G => fun x => asPiE _ _ (fun x' => G _)
  end.

Fixpoint asPi_combine ps {struct ps}
: forall (F G : _),
    asPi ps (fun App => F App -> G App) ->
    asPi ps F -> asPi ps G :=
  match ps as ps
        return forall F G : (forall U : Type, asFunc ps U -> U) -> Type,
                 asPi ps (fun App : forall U : Type, asFunc ps U -> U => F App -> G App) ->
                 asPi ps F -> asPi ps G
  with
    | nil => fun _ _ a b => a b
    | p :: ps => fun _ _ a b x => asPi_combine _ _ _ (a x) (b x)
  end.

(*

Section _mmatch.
  Variable ps : list Type.
  Variable RecT : asFunc ps Type.

  Fixpoint Fmatch (i : itype ps) (Ret : asFunc ps Type)
    (brs : asPi ps (fun App => App _ (cases RecT i (fun x => combine (fun x y => x -> y) _ x Ret))))
    {struct i}
  : asPi ps (fun App => App _ (itypeD i RecT) -> App _ Ret).
  destruct i.
  { simpl in *. revert brs.
    unfold combine.
    apply asPi_combine.
    apply asPiE.
  intro. intro.
  destruct i.
  { simpl in *.
  Abort.
*)

(** Some Examples **)
(** Vectors **)
(*
Definition rfvec T : itype ((nat : Type) :: nil) :=
  @Get ((nat : Type) :: @nil Type) nat (MZ _ _)
       (fun x =>
          match x with
            | 0 => Inj _ unit
            | S n => Prod (Inj _ T) (Rec (Hcons n Hnil))
          end).

Definition rfvec' T : itype ((nat : Type) :: nil) :=
  Sum (@Get ((nat : Type) :: @nil Type) nat (MZ _ _)
            (fun x => Inj _ (x = 0)))
      (@Get ((nat : Type) :: @nil Type) nat (MZ _ _)
            (fun x => Sig (fun n : nat => Prod (Inj _ T) (Prod (Rec (Hcons n Hnil)) (Inj _ (x = S n)))))).

Definition rfvec'' T : itype ((nat : Type) :: nil) :=
  Sum (Unf (MZ _ _) 0 Unit)
      (Sig (fun n : nat =>
              (Unf (MZ _ _) (S n) (Prod (Inj _ T) (Rec (Hcons n Hnil)))))).

Eval simpl in fun T => itypeD (rfvec T).
Eval simpl in fun T => itypeD (rfvec' T).
Eval simpl in fun T => itypeD (rfvec'' T).
Eval simpl in fun T Result Rec =>
                @cases _ Rec (rfvec T) (fun x => combine (fun x y => x -> y) _ x Result).

Eval simpl in fun T Result Rec =>
                @cases _ Rec (rfvec' T) (fun x => combine (fun x y => x -> y) _ x Result).

Eval simpl in fun T Result Rec =>
                @cases _ Rec (rfvec'' T) (fun x => combine (fun x y => x -> y) _ x Result).


(** Nats **)
Definition rfnat := Sum (Inj nil unit) (Rec Hnil).

Eval simpl in fun Result Rec =>
                @Tmatch _ Rec rfnat (fun x => combine (fun x y => x -> y) _ x Result).

Definition inat :=
  Eval simpl in itypeD rfnat.

Definition i0 : inat :=
  @existT bool (fun x' => itypeD nil (if x' then Inj nil unit else Rec nil Hnil)
  nat) true tt.

Definition iS : nat -> inat :=
  @existT bool (fun x' => itypeD nil (if x' then Inj nil unit else Rec nil Hnil)
  nat) false.

Definition fold (i : nat) : inat :=
  match i with
    | 0 => i0
    | S n => iS n
  end.

Definition unfold (i : inat) : nat :=
  match i with
    | existT true _ => 0
    | existT false x => S x
  end.

Theorem fold_unfold : forall x, fold (unfold x) = x.
Proof.
  destruct x; simpl.
  destruct x; simpl.
  { simpl in *. destruct i. reflexivity. }
  { simpl in *. reflexivity. }
Qed.

Theorem unfold_fold : forall x, unfold (fold x) = x.
Proof.
  destruct x; simpl; reflexivity.
Qed.
*)