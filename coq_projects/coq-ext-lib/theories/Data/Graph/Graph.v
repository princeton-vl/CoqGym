Set Implicit Arguments.
Set Strict Implicit.

Section Graph.
  Variable V : Type.
  Variable G : Type.

  Class Graph : Type :=
  { verticies  : G -> list V
  ; successors : G -> V -> list V
  }.
End Graph.

Arguments verticies {V} {G} {Graph} _.
Arguments successors {V} {G} {Graph} _ _.