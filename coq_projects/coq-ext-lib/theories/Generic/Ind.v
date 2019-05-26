Require Import List String.
Require Import ExtLib.Structures.CoMonad.

Set Implicit Arguments.
Set Strict Implicit.

Inductive type : Type :=
| Self : type
| Inj : Type -> type.

Definition product := list type.
Definition variant := list product.

Section denote.
  Variable M : Type.

  Definition typeD (t : type) : Type :=
    match t with
      | Self => M
      | Inj t => t
    end.

  Definition func (T : Type) (v : product) : Type :=
    fold_right (fun x acc => typeD x -> acc) T v.

  Definition data (v : product) : Type :=
    fold_right (fun x acc => typeD x * acc)%type unit v.

  Definition matchD (T : Type) (v : variant) : Type :=
    fold_right (fun x acc => func T x -> acc)%type T v.

  Definition dataD (v : variant) : Type :=
    fold_right (fun x acc => data x + acc)%type Empty_set v.

  Definition recD (T : Type) (c : Type -> Type) (v : variant) : Type :=
    fold_right (fun x acc =>
      fold_right (fun x acc =>
        match x with
          | Inj t => t
          | Self => c T
        end -> acc) (c T) x -> acc) (M -> T) v.

End denote.

Class Data (T : Type) : Type :=
{ repr  : variant
; into  : dataD T repr -> T
; outof : T -> forall A, matchD T A repr
; rec   : forall c {_ : CoMonad c}, forall A, recD T A c repr
}.

Local Open Scope string_scope.

Global Instance Data_nat : Data nat :=
{ repr := nil :: (Self :: nil) :: nil
; outof := fun x _ z s =>
  match x with
    | 0 => z
    | S n => s n
  end
; into := fun d =>
  match d with
    | inl tt => 0
    | inr (inl (n, tt)) => n
    | inr (inr x) => match x with end
  end
; rec := fun c _ A z s d =>
  coret ((fix recur (d : nat) {struct d} : c A :=
    match d with
      | 0 => z
      | S n => s (recur n)
    end) d)
}.

Global Instance Data_list {A} : Data (list A) :=
{ repr := (nil) :: (Inj A :: Self :: nil) :: nil
; outof := fun x _ n c =>
  match x with
    | nil => n
    | x :: xs => c x xs
  end
; into := fun d =>
  match d with
    | inl tt => nil
    | inr (inl (x, (xs, tt))) => x :: xs
    | inr (inr x) => match x with end
  end
; rec := fun c _ T n co d =>
  coret ((fix recur (ds : list A) {struct ds} : c T :=
    match ds with
      | nil => n
      | d :: ds => co d (recur ds)
    end) d)
}.

(** Example of deriving Show from Data **)
Require Import ExtLib.Programming.Show.
Require Import ExtLib.Data.Monads.IdentityMonad.
Require Import ExtLib.Structures.Monads.

Global Instance Comoand_Id : CoMonad id :=
{ coret := fun _ x => x
; cobind := fun _ _ f x => x f
}.

(*
Inductive AllResolve (C : Type -> Type) : list type -> Type :=
| AllResolve_nil  : AllResolve C nil
| AllResolve_Self : forall ls, AllResolve C ls -> AllResolve C (Self :: ls)
| AllResolve_Inj  : forall t ls, C t -> AllResolve C ls -> AllResolve C (Inj t :: ls).

Existing Class AllResolve.
*)

Definition ProductResolve (C : Type -> Type) (r : product) : Type :=
  fold_right (fun t acc =>
    match t with
      | Inj t => C t * acc
      | Self => acc
    end)%type unit r.

Definition VariantResolve (C : Type -> Type) (r : variant) : Type :=
  fold_right (fun p acc => ProductResolve C p * acc)%type unit r.

Existing Class VariantResolve.
Ltac all_resolve :=
  simpl VariantResolve; simpl ProductResolve;
    repeat match goal with
             | |- unit => apply tt
             | |- (unit * _)%type => constructor; [ apply tt | ]
             | |- (_ * _)%type => constructor
             | |- _ => solve [ eauto with typeclass_instances ]
           end.

Hint Extern 0 (ProductResolve _ _) => all_resolve : typeclass_instances.
Hint Extern 0 (VariantResolve _ _) => all_resolve : typeclass_instances.

Definition comma_before (b : bool) (s : showM) : showM :=
  if b then
    cat (show_exact ",") s
  else
    s.

Fixpoint show_product (first : bool) (r : list type) {struct r} :
  ProductResolve Show r ->
  (showM -> showM) ->
  (fold_right
     (fun (x : type) (acc : Type) =>
      match x with
      | Self => showM
      | Inj t => t
      end -> acc) (showM) r).
refine (
     match r as r
       return
       ProductResolve Show r ->
       (showM -> showM) ->
       (fold_right
         (fun (x : type) (acc : Type) =>
           match x with
             | Self => showM
             | Inj t => t
           end -> acc) (showM) r)
       with
       | nil => fun _ f => f empty
       | Self :: rs => fun a f s =>
         @show_product false rs a (fun s' => f (cat s (comma_before first s')))
       | Inj t :: rs => fun a f x => @show_product false rs (snd a) (fun s' => f (cat ((fst a) x) (comma_before first s')))
     end); simpl in *.
Defined.

Global Instance Show_data (T : Type) (d : Data T) (AS : VariantResolve Show repr) : Show T :=
{ show :=
  (fix recur (repr : variant) : VariantResolve Show repr -> recD T showM id repr -> T -> showM :=
    match repr as repr return
      VariantResolve Show repr -> recD T showM id repr -> T -> showM
      with
      | nil => fun _ x => x
      | r :: rs => fun a k' =>
        recur rs (snd a) (k' (show_product true _ (fst a)
          (fun s' => cat (show_exact "-") (cat (show_exact "(") (cat s' (show_exact ")"))))))
    end) repr AS (rec (c := id) showM)
}.

Eval compute in
  to_string (M := Show_data _ _) (5 :: 6 :: 7 :: nil).
