

Section lazy_list.
  Variable T : Type.

  Inductive llist : Type :=
  | lnil : llist
  | lcons : T -> (unit -> llist) -> llist.

  Fixpoint force (l : llist) : list T :=
    match l with
      | lnil => nil
      | lcons a b => cons a (force (b tt))
    end.

End lazy_list.

Arguments lnil {T}.
Arguments lcons {T} _ _.