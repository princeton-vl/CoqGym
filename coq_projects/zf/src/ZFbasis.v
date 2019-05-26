(* Contribution to the Coq Library   V6.3 (July 1999)                    *)

(***************************************************************************)
(* File: ZFbasis.v                                                         *)
(* auteur: alex@sysal.ibp.fr                                               *)
(* date: 19/10/95                                                          *)
(***************************************************************************)

Require Export useful.

Parameter E : Set.
Parameter In : E -> E -> Prop. (* x \in y ==> In x y *)

Lemma lem_eq_or : forall a b c : E, a = c \/ b = c <-> c = a \/ c = b.
(* Proof of lem_eq_or                                                      *)
intros; unfold iff in |- *; split; intros.
elim H; clear H; intros.
left; symmetry  in |- *; assumption.

right; symmetry  in |- *; assumption.

elim H; clear H; intros.
left; symmetry  in |- *; assumption.

right; symmetry  in |- *; assumption.

Qed.
(* End of proof of lem_eq_or                                               *)

(***************************************************************************)
(* Definition de l'inclusion                                               *)
(***************************************************************************)
Definition inc (a b : E) := forall v0 : E, In v0 a -> In v0 b.

(***************************************************************************)
(*                    Next : axs_extensionnalite.v                         *)
(***************************************************************************)