(***************************************************************************)
(* Formalization of the Chou, Gao and Zhang's decision procedure.          *)
(* Julien Narboux (Julien@narboux.fr)                                      *)
(* LIX/INRIA FUTURS 2004-2006                                              *)
(* University of Strasbourg 2008                                           *)
(***************************************************************************)

Require  Export parallel_lemmas.

(*********************************************************************)
(*  Construction statements                                                         *)
(*********************************************************************)

Definition on_line (A B C : Point) : Prop := Col A B C /\ B <> C.
Definition on_line_d (A B C : Point) (lambda : F) : Prop :=
  Col A B C /\ B <> C /\ B ** A = lambda * B ** C.
Definition inter_ll (I A B C D : Point) : Prop :=
  Col I A B /\ Col I C D /\ ~ parallel A B C D.
Definition on_parallel (A' A B C : Point) : Prop := B <> C  /\ parallel A A' B C.
Definition on_parallel_d (Y R P Q : Point) (lambda : F) : Prop :=
  P <> Q  /\ parallel Y R P Q /\ R ** Y = lambda * P ** Q.
Definition on_inter_line_parallel (Y R U V P Q : Point) : Prop :=
  ~Col R P Q /\ Col Y U V /\ parallel Y R P Q /\ ~ parallel P Q U V.
Definition on_inter_parallel_parallel (Y R U V W P Q : Point) : Prop :=
  ~Col R P Q /\ parallel Y R U V /\ parallel Y W P Q /\ ~ parallel P Q U V.
Definition is_midpoint (I A B : Point) := on_line_d I A B (1 / 2).
Definition mratio (Y U V : Point) (r : F) :=
  on_parallel_d Y U U V (r / (1 + r)) /\ 1 + r  <> 0. 

(** Lemma to go from point at some distance to point on a line *)

Lemma on_line_to_on_line_d : forall A B C,
 on_line A B C -> on_line_d A B C (B**A / B**C). 
Proof.
intros.
unfold on_line, on_line_d in *.
intuition.
field.
Geometry.
Qed.

Lemma on_parallel_to_on_parallel_d : forall  Y T A B,
 on_parallel Y T A B -> on_parallel_d Y T A B (T**Y / A**B). 
Proof.
intros.
unfold on_parallel, on_parallel_d in *.
intuition.
field.
Geometry.
Qed.

Theorem on_lineex : forall P Q : Point, P <> Q -> {Y : Point | Col Y P Q}.
Proof with Geometry.
intros.
assert (T := A2a P Q 1)...
DecompExAnd T X.
exists X...
Qed.

Theorem on_line_ex : forall P Q : Point, P<>Q -> exists Y, on_line Y P Q.
Proof with Geometry.
intros.
assert {Y : Point | Col Y P Q}.
apply on_lineex...
DecompEx H0 Y.
exists Y.
unfold on_line...
Qed.


Theorem on_line_dex :
 forall (P Q : Point) (lambda : F),
 P <> Q -> {Y : Point | Col Y P Q /\ P ** Y = lambda * P ** Q}.
Proof with Geometry.
intros.
assert (T := A2a P Q lambda).
DecompExAnd T X.
exists X...
Qed.

Theorem inter_llex :
 forall P Q U V : Point,
 ~ parallel P Q U V -> {Y : Point | Col Y P Q /\ Col Y U V}.
Proof with Geometry.
intros.
assert (P <> Q).
eapply par_aux_1.
apply H...
assert (T := A2a P Q (S P U V / S4 P U Q V))...
elim T; intro O; intros...
decompose [and] p...
clear T p...

cut (O ** Q / P ** Q = - (S Q U V / S4 P U Q V))...
intro...

assert (S O U V = P ** O / P ** Q * S Q U V + O ** Q / P ** Q * S P U V)...
apply l2_9...

assert (P ** O / P ** Q = S P U V / S4 P U Q V)...
rewrite H2...
field...
clear H2; rename H5 into H2...

rewrite H2 in H4...
rewrite H3 in H4...
assert (S O U V = 0)...
rewrite H4; field...

exists O...
assert (P ** O / P ** Q = S P U V / S4 P U Q V)...
rewrite H2; field...
clear H2; rename H3 into H2...

assert (P ** Q + Q ** O = P ** O)...
rewrite <- H3 in H2...
assert (O ** Q / P ** Q = 1 - S P U V / S4 P U Q V)...
rewrite <- H2...
assert (O ** Q = - Q ** O)...
rewrite H4...
field...

assert (1 - S P U V / S4 P U Q V = (S4 P U Q V - S P U V) / S4 P U Q V)...
field...
rewrite H5 in H4...
clear H5...
unfold S4 in H4...
assert (S P U Q + S P Q V - S P U V = - S Q U V)... 
assert (S P Q V = S P Q U + S P U V + S U Q V)...
rewrite H5...
assert (S P Q U = - S P U Q)...
rewrite H6...
assert (S U Q V = - S Q U V)...
rewrite H7...
ring...
rewrite H5 in H4...
rewrite H4...
unfold S4 in |- *...
field...
Qed.

Lemma inter_ll_ex :  forall P Q U V : Point,
 ~ parallel P Q U V -> exists Y, inter_ll Y P Q U V.
Proof with intuition.
intros.
assert  {Y : Point | Col Y P Q /\ Col Y U V}.
apply inter_llex...
DecompExAnd H0 Y.
exists Y.
unfold inter_ll...
Qed.




Theorem on_parallelex : forall P Q R : Point, 
  Q<>R -> 
  ~ Col P Q R ->
  exists Y, parallel Q R P Y.
Proof.
intros.
assert ({Y : Point | parallel Q R P Y}).
apply euclid_parallel_existence.
DecompEx H1 Y.
exists Y.
intuition.
Qed.

Theorem on_parallel_ex : forall P Q R : Point, 
  Q<>R -> 
  ~ Col P Q R ->
  exists Y, on_parallel Y P Q R.
Proof.
intros.
assert ({Y : Point | parallel Q R P Y}).
apply euclid_parallel_existence.
elim H1;intros.
exists x.
unfold on_parallel.
intuition.
Qed.


Lemma  on_parallel_d_ex :
    forall (P Q R : Point) (lambda : F),
   P<>Q -> 
   ~ Col P Q R ->
   exists Y, on_parallel_d Y R P Q lambda.
Proof with Geometry.
intros.

assert ({Y':Point | (parallel P Q R Y') /\ R<>Y'}).
apply euclid_parallel_existence_strong...
DecompExAnd H1 Y'.
assert {Y : Point | Col Y R Y' /\ R ** Y =  (lambda * P**Q/R**Y') * R ** Y'}.
apply on_line_dex...
DecompExAnd H1 Y.
exists Y.
unfold on_parallel_d.
repeat split...
cut (parallel P Q R Y).
Geometry.
eapply col_par_par.
apply H4.
Geometry.
Geometry.
rewrite H6.
field.
Geometry.
Qed.


