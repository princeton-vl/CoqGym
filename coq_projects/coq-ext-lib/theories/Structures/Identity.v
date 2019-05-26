Require Import ExtLib.Core.Type.

Set Implicit Arguments.
Set Strict Implicit.

Polymorphic Class IsIdent@{t}
            {A : Type@{t}}
            {tA : type A}
            {tokA : typeOk tA} (f : A -> A) : Prop :=
  isId : forall x, proper x -> equal (f x) x.

Polymorphic Definition IsIdent_id@{t}
            {A : Type@{t}}
            {tA : type A}
            {tokA : typeOk tA} : IsIdent id.
Proof.
  unfold id. eapply equiv_prefl; auto.
Qed.
Global Existing Instance IsIdent_id.


Polymorphic Definition IsIdent_id'@{t}
            {A : Type@{t}}
            {tA : type A}
            {tokA : typeOk tA} : IsIdent (fun x => x) := IsIdent_id.
Global Existing Instance IsIdent_id'.
