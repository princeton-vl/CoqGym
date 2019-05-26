Require Import ExtLib.Structures.Functor.
Require Import ExtLib.Structures.Applicative.
Require Import ExtLib.Tactics.Injection.

Set Printing Universes.

Section poption.
  Polymorphic Universe i.
  Polymorphic Variable T : Type@{i}.

  Polymorphic Inductive poption : Type@{i} :=
  | pSome : T -> poption
  | pNone.

  Global Polymorphic Instance Injective_pSome a b
  : Injective (pSome a = pSome b) :=
  { result := a = b
  ; injection := fun pf =>
                   match pf in _ = X
                         return a = match X with
                                    | pSome y => y
                                    | _ => a
                                    end
                   with
                   | eq_refl => eq_refl
                   end }.

  Global Polymorphic Instance Injective_pSome_pNone a
  : Injective (pSome a = pNone) :=
  { result := False
  ; injection := fun pf =>
                   match pf in _ = X
                         return match X with
                                | pSome y => True
                                | _ => False
                                end
                   with
                   | eq_refl => I
                   end }.

  Global Polymorphic Instance Injective_pNone_pSome a
  : Injective (pNone = pSome a) :=
  { result := False
  ; injection := fun pf =>
                   match pf in _ = X
                         return match X with
                                | pNone => True
                                | _ => False
                                end
                   with
                   | eq_refl => I
                   end }.

End poption.

Arguments pSome {_} _.
Arguments pNone {_}.

Section poption_map.
  Polymorphic Universes i j.
  Polymorphic Context {T : Type@{i}} {U : Type@{j}}.
  Polymorphic Variable f : T -> U.

  Polymorphic Definition fmap_poption (x : poption@{i} T) : poption@{j} U :=
    match x with
    | pNone => pNone@{j}
    | pSome x => pSome@{j} (f x)
    end.

  Polymorphic Definition ap_poption
              (f : poption@{i} (T -> U)) (x : poption@{i} T)
  : poption@{j} U :=
    match f , x with
    | pSome f , pSome x => pSome (f x)
    | _ , _ => pNone
    end.

End poption_map.

Polymorphic Definition Functor_poption@{i} : Functor@{i i} poption@{i} :=
{| fmap := @fmap_poption@{i i} |}.
Existing Instance Functor_poption.


Polymorphic Definition Applicative_poption@{i} : Applicative@{i i} poption@{i} :=
{| pure := @pSome@{i}
 ; ap   := @ap_poption |}.
Existing Instance Applicative_poption.