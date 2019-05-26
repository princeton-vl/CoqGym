Class Join (worlds: Type): Type := join: worlds -> worlds -> worlds -> Prop.

Class SeparationAlgebra (worlds: Type) {SA: Join worlds}: Type :=
{
  join_comm: forall m1 m2 m: worlds,
    join m1 m2 m ->
    join m2 m1 m;
  join_assoc: forall mx my mz mxy mxyz: worlds,
    join mx my mxy ->
    join mxy mz mxyz ->
    exists myz, join my mz myz /\ join mx myz mxyz
}.

Definition unit_element {worlds: Type} {J: Join worlds}: worlds -> Prop :=
  fun e => forall n n', join e n n' -> n = n'.
