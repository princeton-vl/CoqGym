Section unit_op.
  Context {T : Type}.
  Variable op : T -> T -> T.
  Variable u : T.
  Variable equ : T -> T -> Prop.
 
  Class LeftUnit : Type :=
    lunit : forall a, equ (op u a) a.

  Class RightUnit : Type :=
    runit : forall a, equ (op a u) a.
  
End unit_op.

Section comm_op.
  Context {T U : Type}.
  Variable op : T -> T -> U.
  Variable equ : U -> U -> Prop.
 
  Class Commutative : Type :=
    commut : forall a b, equ (op a b) (op b a).
  
End comm_op.

Section assoc_op.
  Context {T : Type}.
  Variable op : T -> T -> T.
  Variable equ : T -> T -> Prop.

  Class Associative : Type :=
    assoc : forall a b c, equ (op (op a b) c) (op a (op b c)).
  
End assoc_op.
