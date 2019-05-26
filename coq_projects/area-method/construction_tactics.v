(***************************************************************************)
(* Formalization of the Chou, Gao and Zhang's decision procedure.          *)
(* Julien Narboux (Julien@narboux.fr)                                      *)
(* LIX/INRIA FUTURS 2004-2006                                              *)
(* University of Strasbourg 2008                                           *)
(***************************************************************************)

Require  Export construction_lemmas_2.

Ltac point_on_line I A B :=
let id1 := fresh in ((assert (id1:{Y : Point | Col Y A B});
[apply (on_lineex A B)|DecompEx id1 ipattern:(I)])).

Ltac point_on_line_d I A B d :=
let id1 := fresh in ((assert (id1:{Y : Point | Col Y A B /\ A ** Y = d * A ** B});
[apply (on_line_dex A B d)|DecompExAnd id1 ipattern:(I)])).

Ltac midpoint I A B := point_on_line_d I A B (1/2).

Ltac point_on_parallel_line I P A B :=
let id1 := fresh in ((assert (id1:{Y : Point | (parallel Y P A B)});
[apply (on_parallelex A B P)|DecompEx id1 ipattern:(I)])).

Ltac point_on_intersection_lines I A B C D :=
let id1 := fresh in ((assert (id1:{Y : Point | Col Y A B /\ Col Y C D});
[apply (inter_llex A B C D)|DecompExAnd id1 ipattern:(I)])).
