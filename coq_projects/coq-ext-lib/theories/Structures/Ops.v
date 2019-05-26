Section unit_op.
  Context {T : Type}.
  Variable op : T -> T -> T.
  Variable u : T.
  Variable equ : T -> T -> Prop.

  Class Ident : Type :=
    lunit : forall a, equ (op u a) a.

  Class RightUnit : Type :=
    runit : forall a, equ (op a u) a.

End unit_op.