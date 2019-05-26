Section compose.
  Variable T : Type.
  Variable R1 R2 : T -> T -> Prop.

  Definition compose (x z : T) : Prop :=
    exists y, R1 x y /\ R2 y z.
End compose.
