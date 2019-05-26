(* Directions for replace *)

Inductive Dir : Set := L | R.

Definition pol_dir_opp dir := match dir with L => R | R => L end.
