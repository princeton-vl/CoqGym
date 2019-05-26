(* Contribution to the Coq Library   V6.3 (July 1999)                    *)

(****************************************************************************)
(* This contribution was updated for Coq V5.10 by the COQ workgroup.        *)
(* January 1995                                                             *)
(****************************************************************************)
(*                                drinker.v                                 *)
(****************************************************************************)


Theorem drinker's_theorem :
 (forall P : Prop, P \/ ~ P) ->
 forall (U : Set) (x : U) (Q : U -> Prop),
 exists x : U, Q x -> forall x : U, Q x.
intros Excluded_middle U x Q.
generalize (Excluded_middle (exists x : U, ~ Q x)); intro h; elim h; intro H';
 clear h.
elim H'; intros z E; clear H'.
exists z; intro H'0.
elim E; assumption.

exists x; intros H'0 x0.
generalize (Excluded_middle (Q x0)); intro h; elim h; intro H'1; clear h;
 auto.
elim H'; exists x0; assumption.
Qed.