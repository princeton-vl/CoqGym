Set Implicit Arguments.
Set Strict Implicit.

Section ClassReify.
  Variable P Q : Type.
  Variable D : P -> Q.

  Class ClassReify (v : Q) : Type :=
  { reify : P
  ; reify_sound : D reify = v
  }.
End ClassReify.

Require Import Lists.List.

Section ListReify.
  Variables (T U : Type) (f : T -> U).

  Global Instance  Reflect_nil : ClassReify (map f) nil :=
  { reify := nil 
  ; reify_sound := refl_equal
  }.

  Global Instance  Reflect_cons a b (Ra : ClassReify f a) (Rb : ClassReify (map f) b) 
  : ClassReify (map f) (a :: b).
  refine {| reify := cons (@reify _ _ _ _ Ra) (@reify _ _ _ _ Rb) |}.
  simpl; f_equal; eapply reify_sound.
  Defined.
End ListReify.
