(** We circumvent a limitation of type class definition by defining a polymorphic type
    for a triple of elements which will be used to define an angle by instantiating
    A with Point *)

Record Triple {A:Type} : Type := build_triple {V1 : A ; V : A ; V2 : A ; Pred : V1 <> V /\ V2 <> V}.

Record Couple {A:Type} : Type := build_couple {P1: A ; P2 : A ; Cond: P1 <> P2}.
