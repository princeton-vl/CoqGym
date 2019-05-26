Set Implicit Arguments.
Set Strict Implicit.
Set Asymmetric Patterns.

Section checked.
  Context {T : Type}.
  Variable F : T -> Type.

  Inductive Checked : option T -> Type :=
  | Success : forall {v}, F v -> Checked (Some v)
  | Failure : Checked None.

  Definition succeeded (o : option T) (d : Checked o) : bool :=
    match d with
      | Success _ _ => true
      | Failure => false
    end.

  Definition failed (o : option T) (d : Checked o) : bool :=
    match d with
      | Success _ _ => false
      | Failure => true
    end.

  Definition asOption (o : option T) (d : Checked o) : option (match o with
                                                                 | None => False
                                                                 | Some x => F x
                                                               end) :=
    match d in Checked o return option match o with
                                         | None => False
                                         | Some x => F x
                                       end
    with
      | Success _ x => Some x
      | Failure => None
    end.

End checked.