(* Contribution to the Coq Library   V6.3 (July 1999)                    *)

(***************************************************************************)
(* File: axs_parties.v                                                     *)
(* auteur: alex@sysal.ibp.fr                                               *)
(* date: 19/10/95                                                          *)
(***************************************************************************)
Require Export axs_reunion.

(***************************************************************************)
(* Axiome des parties                                                      *)
(***************************************************************************)
Parameter parties : E -> E.
Axiom
  axs_parties :
    forall v0 v2 : E,
    In v2 (parties v0) <-> (forall v3 : E, In v3 v2 -> In v3 v0).

(***************************************************************************)
(* La reunion des parties de x est x                                       *)
(***************************************************************************)
Lemma lem_reunion_parties : forall x : E, reunion (parties x) = x.
(* Proof of lem_reunion_parties                                            *)
intros; apply axs_extensionnalite; intros; unfold iff in |- *; split; intros.
elim (axs_reunion (parties x) v2); intros; generalize (H0 H); clear H H0 H1;
 intros.
elim H; clear H; intros; elim H; clear H; intros.
elim (axs_parties x x0); intros; generalize (H1 H); clear H1 H2; intros.
exact (H1 v2 H0).

elim (axs_reunion (parties x) v2); intros; apply H1; clear H0 H1; intros.
exists (singleton v2); split; [ idtac | apply lem_x_in_sing_x ].
elim (axs_parties x (singleton v2)); intros; apply H1; clear H0 H1; intros.
unfold singleton in H0.
elim (axs_paire v2 v2 v3); intros; generalize (H1 H0); clear H1 H2; intros.
elim H1; clear H1; intros; rewrite H1; auto with zfc.

Qed.
(* End of proof of lem_reunion_parties                                     *)
(***************************************************************************)
(*                   Next : axs_comprehension.v                            *)
(***************************************************************************)